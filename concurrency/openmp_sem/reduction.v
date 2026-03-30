From Coq Require Import String ZArith.
From compcert Require Import Clight Cop Clightdefs AST Integers Ctypes Values Memory Globalenvs.
From compcert Require Import -(notations) lib.Maps.
From VST.concurrency.openmp_sem Require Import notations clight_fun event_semantics.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From stdpp Require Import base list.

(* This is not used directly, only serves as a reference.
   Mathematical value of a privatized reduction variable
   We need the initial value to be injected in compcert val type, and we obtain that by
   evaluating an initializer expression in the executing environment and memory.
   
   [Standard 6.0, Table 7.1: (Initializer for) Implicitly Declared C/C++ Reduction Identifiers]  *)
    Definition reduction_var_init_val (i: reduction_identifier_type) : option nat :=
        match i with
        | RedIdIdent id =>
            if (ident_eq id __max) then
                (* TODO the minimal number representable in the type *) None
            else if (ident_eq id __min) then
                (* TODO the maximal number representable in the type *) None    
            else None
        | RedIdPlus => Some 0
        | RedIdTimes => Some 1
        | RedIdAnd => None (* ~ 0 *)
        | RedIdOr => Some 0
        | RedIdXor => Some 0
        | RedIdLogicalAnd => Some 1
        | RedIdLogicalOr => Some 0
        end.

    Definition initializer_expr (red_id: reduction_identifier_type) (ty: type) : option expr :=
        match red_id with
        | RedIdPlus =>  Some $ Ecast (Econst_int (Int.repr 0%Z) tint) ty
        | RedIdTimes => Some $ Ecast (Econst_int (Int.repr 1%Z) tint) ty
        (*  all bits set to 1 *)
        | RedIdAnd => Some $ Eunop Onotint (Ecast (Econst_int (Int.repr 0%Z) tint) ty) ty 
        | RedIdOr => Some $ Ecast (Econst_int (Int.repr 0%Z) tint) ty
        | RedIdXor => Some $ Ecast (Econst_int (Int.repr 0%Z) tint) ty
        | RedIdLogicalAnd => Some $ Ecast (Econst_int (Int.repr 1%Z) tint) ty
        | RedIdLogicalOr => Some $ Ecast (Econst_int (Int.repr 0%Z) tint) ty
        (* TODO | (RedIdIdent __max) minimal value representable in ty *)
        | _ => None
        end
    .

    Section PRIVATIZATION.

        Fixpoint alloc_variables_fun (ge:genv) (e: env) (m: mem) (vs: list (ident * type)) : env * mem :=
        match vs with
        | nil => (e, m)
        |  (id, ty) :: vs' =>
            let (m1, b1) := Mem.alloc m 0 (sizeof ge ty) in
            alloc_variables_fun ge (PTree.set id (b1, ty) e) m1 vs'
        end.

        Lemma alloc_variables_fun_equiv : forall ge e m vs e' m',
            alloc_variables_fun ge e m vs = (e', m') -> alloc_variables ge e m vs e' m'.
        Proof.
        intros ge e m vs. revert ge e m. induction vs; intros.
        - inversion H. subst. apply alloc_variables_nil.
        - simpl in H. destruct a. destruct (Mem.alloc m 0 (sizeof ge t)) eqn:Heq.
        eapply alloc_variables_cons. done.
        eapply IHvs. done.
        Qed.
        

        (* add entries in e1 to e2 *)
        Definition merge (e1 e2: env) : env :=
            PTree.fold (λ e id b, PTree.set id b e) e1 e2.

        (*  alloc_pvs allocate 
            all privatization happens when a thread is spawned by a parallel construct.
            for each variable that comes from local env, for each spawned thread, allocate a new variable with the same ident and type in memory,
            overwrite the original local env. *)
        Definition alloc_pvs (ge: genv) (le: env) (m: mem) (pvs: list (ident * type)) : env * mem :=
                let (pve, m') := @alloc_variables_fun ge empty_env m pvs in
                (merge pve le, m').

    End PRIVATIZATION.
    
    Section REDUCTION.
        Implicit Types (ge: genv) (ce: composite_env) (op: Cop.binary_operation) (le: env) (m: mem)
                       (b: Values.block) (ty: type).
        (* combine the reduction contributions in the reduction clause *)
        Definition combine_vals ce op v1 ty1 v2 ty2 m: option val :=
            sem_binary_operation ce op v1 ty1 v2 ty2 m.

        Definition c_true := Econst_int (Int.repr 1%Z) tint.
        Definition c_false := Econst_int (Int.repr 0%Z) tint.

        (* the expression corresponding to `reduction_function omp_in omp_out` that combines
            omp_in and omp_out (v1 and v2 below). ty is the type v1 (the values being combined).
            v2 is the output of a single combine, and the type of v2 is: 
                - ty, if red_id specifies a non-logical operation
                - tint (represents _Bool), if red_id specifies a logical operation (&&, ||)

        [Standard 6.0, Table 7.1: (Initializer for) Implicitly Declared C/C++ Reduction Identifiers]
        assume omp_in, omp_out and the output (new omp_out) have the same type *)
        Definition combiner_sem ce m v1 v2 ty (red_id: reduction_identifier_type) : option val :=
            match red_id with
            | RedIdPlus => combine_vals ce Oadd v1 ty v2 ty m
            | RedIdTimes => combine_vals ce Omul v1 ty v2 ty m
            | RedIdAnd => combine_vals ce Oand v1 ty v2 ty m
            | RedIdOr => combine_vals ce Oor v1 ty v2 ty m
            | RedIdXor => combine_vals ce Oxor v1 ty v2 ty m
            | RedIdLogicalAnd =>
                b1 ← bool_val v1 tint m;
                b2 ← bool_val v2 tint m;
                (* && returns Vtrue or Vfalse *)
                Some $ if (b1:bool) && (b2:bool) then Vtrue else Vfalse
            | RedIdLogicalOr =>
                b1 ← bool_val v1 tint m;
                b2 ← bool_val v2 tint m;
                Some $ if (b1:bool) || (b2:bool) then Vtrue else Vfalse
            (* Standard 7.6.6: For a max or min reduction, the type of the list item must be an allowed arithmetic data type:
            char, int, float, double, or _Bool, possibly modified with long, short, signed,
            or unsigned. *)
            | RedIdIdent i =>
                if (ident_eq i __max) then
                    (* vb should be either Vtrue or Vfalse, so has type Tint *)
                    vb ← sem_binary_operation ce Olt v1 ty v2 ty m;
                    b ← bool_val vb tint m;
                    Some $ if (b:bool) then v2 else v1
                else if (ident_eq i __min) then
                    vb ← sem_binary_operation ce Ogt v1 ty v2 ty m;
                    b ← bool_val v1 tint m;
                    Some $ if (b:bool) then v2 else v1
                else
                    None
            end.

    (* Standard 6.0, 7.6.2.1: "The number of times that the combiner expression is executed and the
    order of these executions for any reduction clause are unspecified."
    *)

        (* information about a variable being reduced *)
        Record red_var :=
        {
            red_op: reduction_identifier_type; (* reduction operator *)
            b_ty: Values.block * type; (* block and type of the original copy *)
        }.
        #[export] Instance settable_red_var : Settable _ := settable! Build_red_var <red_op; b_ty>.

        Definition red_vars : Type := PTree.t red_var.

        Definition rv_empty : red_vars := @PTree.empty red_var.

        (* the initial value for the implicitly privatized reduction variable,
           of some reduction operation `red_id_type` and ctype `ty` is `v` *)
        Definition init_val ge le te m red_id_type ty : option val :=   
            exp ← initializer_expr red_id_type ty;
            @eval_expr_fun ge le te m exp.

        (* initialize values for idents in rc.
           The address of the idents are decided by ge and le, so this operation should be done after
           private copies are allocated.  *)
        Definition init_rvs_for_one_rc (rc : reduction_clause_type) ge le te maybe_m : option mem :=
            match rc with
            | RedClause red_op red_var_names =>
                foldr (λ i maybe_m,
                        m ← maybe_m;
                        b_ty ← get_b_ty ge le i;
                        let '(b, ty) := b_ty in
                        init_v ← init_val ge le te m red_op ty;
                        write_v ge b ty m init_v)
                      maybe_m red_var_names
            end.
        
        (* initialize values for idents in rcs. *)
        Definition init_rvs (rcs : list reduction_clause_type) ge le te m : option mem :=
            foldr (λ rc maybe_m, init_rvs_for_one_rc rc ge le te maybe_m) (Some m) rcs.

        (* requires private copies for pc_first are allocated.
           read their original values (with the old envs ge_0, le_0),
           copy over to new address  *)
        Definition init_firstprivate (pc_first : privatization_clause_type)
                                    ge_0 le_0 ge le m : option mem :=
            match pc_first with
            | PrivClause pvs =>
                foldr (λ i maybe_m,
                        m ← maybe_m;
                        orig_v ← deref ge_0 le_0 i m;
                        b_ty ← get_b_ty ge le i;
                        let '(b, ty) := b_ty in
                        write_v ge b ty m orig_v)
                      (Some m) pvs
            end.

        (* go through the local envs of kids, combine reduction contributions for i.*)
        Definition combine_one_var (i:ident) red_op (orig_val: val) ty ce le_lst m : option val :=
            foldr (λ le maybe_v, v ← maybe_v;
                                 v' ← deref_le le i m;
                                 combiner_sem ce m v v' ty red_op) (Some orig_val) le_lst.

          (* for reduction variables recorded in the top stack of red_vars in t, combine their contributions
            and write back to memory according to the original environments.
            ge_0 and le_0 stores the mapping from idents to (block, type) of the original copies..
            because the OMPRed label cannot store a genv, ge_0 is stored as an env instead. *)
        Definition reduction_one_clause (rc: reduction_clause_type) ce (le_lst: list env) (rvs_env :env) m : option mem :=
            match rc with
            | RedClause red_op rvs =>
                foldr (λ i maybe_m,
                    m ← maybe_m;
                    b_ty ← rvs_env!i;
                    let '(b, ty) := b_ty in
                    orig_val ← deref_loc_fun ty m b Ptrofs.zero Full;
                    final_v ← combine_one_var i red_op orig_val ty ce le_lst m;
                    write_v ce b ty m final_v) (Some m) rvs
            end.

        Definition reduction (rcs: list reduction_clause_type) ce (le_lst: list env)
                       (rvs_env:env) m : option mem :=
            foldr (λ rc maybe_m,
                m ← maybe_m;
                reduction_one_clause rc ce le_lst rvs_env m) (Some m) rcs.

    End REDUCTION.
    
    Section PR_MAP.

        (* origical location of privatized variables. Only need to record it if it comes from lenv. *)
        Variant orig_entry :=
            (* the original var is in le *)
            | OrigEnv (b_ty: Values.block * type)
            (* the original var is in ge *)
            | OrigGenv.

        (* a map of privatized variables and where they came from.
        ident -> (original address, reduction information) *)
        Definition pv_map := PTree.t orig_entry.

        Implicit Types (pvm : pv_map) (rvl: val) 
                       (i: ident) (ge: genv) (le orig_le: env) (m: mem) (b:Values.block) (ty:type).

        Definition pvm_init : pv_map := PTree.empty orig_entry.

        Definition pvm_get pvm (i: ident) :=
            pvm ! i.

        Definition pvm_register_p pvm (priv_clause : privatization_clause_type) ge le: option pv_map :=
            let pvs := match priv_clause with
            | PrivClause pvs => pvs
            end in
            foldr (λ i maybe_pvm, 
                        pvm ← maybe_pvm;
                        match le!i with
                        (* if i\in le *)
                        | Some b_ty => Some $ PTree.set i (OrigEnv b_ty) pvm
                        | None => match Genv.find_symbol ge i with
                                  (* if i\in ge *)
                                  | Some _ => Some $ PTree.set i OrigGenv pvm
                                  | None => None
                                  end
                        end)
                   (Some pvm) pvs.

        Definition alloc_priv_copies ge_0 le_0 m (pvs: list ident) : option (env * mem) :=
            foldr (λ i accu,
                    accu ← accu;
                    let '(le', m') := accu in
                    alloc_variable_fun ge_0 le_0 i m') (Some (le_0, m)) pvs.

        Definition rcs_priv_idents (rcs: list reduction_clause_type) : list ident :=
            foldr (λ rc accu,
                        let rvs := match rc with
                        | RedClause _ pvs => pvs
                        end in
                        rvs ++ accu)
                    [] rcs.

        Definition priv_idents (pc pc_first: privatization_clause_type)
                       (rcs: list reduction_clause_type) : list ident :=
            let pc_pvs := match pc with
            | PrivClause pvs => pvs
            end in
            let pc_first_pvs := match pc_first with
            | PrivClause pvs => pvs
            end in
            let rcs_pvs := rcs_priv_idents rcs in
            pc_pvs ++ pc_first_pvs ++ rcs_pvs.

        (* allocate private copies for idents in the private, firstprivate and reduction clause,
           initialize private copies in the first private clause to be their original values,
           and initialize private copies from the reduction clause with specific rules.
           Returns the new le and mem; the global and temperal envs are not changed. *)
        Definition privatization (pc pc_first: privatization_clause_type)
                                  (rcs: list reduction_clause_type)
                                 m ge_0 le_0 te_0 : option (env * mem) :=
            let pvs := priv_idents pc pc_first rcs in
            le'_m' ← alloc_priv_copies ge_0 le_0 m pvs;
            let (le', m') := (le'_m': env * mem) in
            (* ge is not changed *)
            m'' ← init_firstprivate pc_first ge_0 le_0 ge_0 le' m';
            m''' ← init_rvs rcs ge_0 le' te_0 m'';
            Some (le', m''').

        (* free memory for private copies in pvs. *)
        Definition free_private pvs ce le m : option mem :=
            foldr (λ i maybe_m,
                    m ← maybe_m;
                    b_ty ← le!i;
                    let '(b, ty) := b_ty in
                    Mem.free m b 0 (sizeof ce ty))
                (Some m) pvs
        .

        (* For privatized idents in pc::pc_first::rcs, restore entries in le.
            if the ident i came from le_0, restore le[i] to le_0[i];
            otherwise it must came from ge, so we simply remove the key from le and so lookup of i will resolve in ge. *)
        Definition restore_le pvs le le_0 : env :=
            foldr (λ i maybe_le,
                match PTree.get i le_0 with
                | Some b_ty => PTree.set i b_ty le
                | None => PTree.remove i le
                end)
                le pvs
        .

        Definition end_privatization (pvs: list ident) ce le le_0 m : option (env * mem) :=
            m' ← free_private pvs ce le m;
            let le' := restore_le pvs le le_0 in
            Some (le', m')
        .

    End PR_MAP.
