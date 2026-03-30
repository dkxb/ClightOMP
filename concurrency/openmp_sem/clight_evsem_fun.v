(* function version of a part of clight_evsem semantics, a version of Clight that carries a trace of memory events *)

From compcert Require Import Clight Cop Clightdefs AST Integers Ctypes Values Memory Events Globalenvs.

From VST.concurrency.openmp_sem Require Import notations clight_fun event_semantics Clight_evsem Clight_core.

From stdpp Require Import base list.

Section MemOpsT.
    Open Scope Z.
    #[export] Instance Z_divide_dec : RelDecision (Z.divide).
    Proof. unfold RelDecision. apply Znumtheory.Zdivide_dec. Defined.

    Definition load_bitfieldT_fun (ty:type) (sz: intsize) (sg: signedness) pos width m b ofs : option (val * list memval) :=
        match ty with
        | Tint sz' sg1 attr =>
            if (decide $ ((sz = sz' ∧ 0 <= pos ∧ 0 < width <= bitsize_intsize sz ∧ pos + width <= bitsize_carrier sz)%Z ∧
                          (sg1 = (if Coqlib.zlt width (bitsize_intsize sz) then Signed else sg)) ∧
                          (align_chunk (chunk_for_carrier sz) | (Ptrofs.unsigned ofs))))
            then 
            match Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk (chunk_for_carrier sz)) with
            | Some bytes =>
                match decode_val (chunk_for_carrier sz) bytes with
                | Vint c => Some ((Vint (bitfield_extract sz sg pos width c)), bytes)
                | _ => None
                end
            | None => None end
            else None
        | _ => None
        end.

    Lemma load_bitfieldT_fun_correct1:
        ∀ ty sz sg pos width m b ofs v bytes, load_bitfieldT_fun ty sz sg pos width m b ofs = Some (v, bytes) ->
            load_bitfieldT ty sz sg pos width m b ofs v bytes.
    Proof.
        intros; unfold load_bitfield_fun in *.
        destruct ty eqn:?; try done.
        simpl in H.
        destruct (decide _) eqn:?; try done.
        destruct (Mem.loadbytes _ _ _ _) eqn:?; try done.
        destruct (decode_val _ _) eqn:?; try done.
        inv H.
        destruct a0 as [[->[?[??]]][??]].
        eapply load_bitfield_intro; eauto.
    Qed.

    Definition deref_locT_fun (ty: type) (m: Memory.mem) (b: Values.block) (ofs: ptrofs) (bf: bitfield) : option (val * list mem_event) :=
        match bf with
        | Full =>
            match access_mode ty with
            (* deref_locT_value *)
            | By_value chunk => 
                if decide $ (align_chunk chunk | Ptrofs.unsigned ofs)%Z then
                bytes ← Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk chunk);
                Some (decode_val chunk bytes, Read b (Ptrofs.unsigned ofs) (size_chunk chunk) bytes :: nil)
                else None
            (* deref_locT_reference *)
            | By_reference => Some (Vptr b ofs, [])
            (* deref_locT_copy *) 
            | By_copy => Some (Vptr b ofs, [])
            | _ => None
            end
        (* deref_locT_bitfield *)
        | Bits sz sg pos width =>
            v_bytes ← load_bitfieldT_fun ty sz sg pos width m b ofs;
            let '(v, bytes) := v_bytes in
            Some (v, (Read b (Ptrofs.unsigned ofs) (size_chunk (chunk_for_carrier sz)) bytes)::nil)
        end.

    Lemma deref_locT_fun_correct1:
        ∀ ty m b ofs bf v bytes, deref_locT_fun ty m b ofs bf = Some (v, bytes) -> deref_locT ty m b ofs bf v bytes.
    Proof.
        intros; unfold deref_loc_fun in *. destruct bf; try constructor.
        - destruct (access_mode ty) eqn:?.
            + unfold deref_locT_fun in H. unfold_mbind_in_hyp. repeat destruct_match in H eqn:?. inv H. eapply deref_locT_value; eauto.
            + inv H. repeat destruct_match!. inv H1. eapply deref_locT_reference; eauto.
            + inv H. repeat destruct_match!. inv H1. eapply deref_locT_copy; eauto.
            + inv H. rewrite Heqm0 in H1. done.
        - simpl in H. unfold_mbind_in_hyp. destruct_match!. destruct p. inv H.
          by apply deref_locT_bitfield, load_bitfieldT_fun_correct1.
    Qed.

    (* TODO only the assign_loc_value is defined, so struct/union/array not supported yet. *)
    Definition assign_locT_fun (ce: composite_env) (ty: type) m b (ofs: ptrofs) (bf: bitfield) v : option (mem * list mem_event) :=
        match bf with
        (* assign_locT_bitfield *)
        | Bits _ _ _ _ => None (* if by value, bf=Full*)
        | Full =>
            match access_mode ty with
            (* assign_locT_value *)
            | By_value chunk =>
                m' ← Mem.storev chunk m (Vptr b ofs) v;
                Some (m', (Write b (Ptrofs.unsigned ofs) (encode_val chunk v) ::nil))
            (* assign_locT_copy *)
            | By_copy => None
            | _ => None
            end
        end.

    Lemma assign_locT_fun_correct1:
        ∀ ce ty m b ofs bf v m' T, assign_locT_fun ce ty m b ofs bf v = Some (m', T)-> assign_locT ce ty m b ofs bf v m' T.
    Proof.
        intros; unfold assign_loc_fun in *.
        unfold assign_locT_fun in H.
        unfold_mbind_in_hyp.
        repeat destruct_match in H eqn:?.
        inv H.
        eapply assign_locT_value; done.
    Qed.

    Fixpoint alloc_variablesT_fun ge le m (l: list (ident * type)) : option (env * mem * list mem_event) :=
        match l with
        | nil => Some (le, m, nil)
        | (i, ty) :: vars =>
            let '(m1, b1) := Mem.alloc m 0 (@sizeof ge ty) in
            let le1 := (PTree.set i (b1, ty) le) in
            le2_m2_T ← alloc_variablesT_fun ge le1 m1 vars;
            let '(le', m', T) := le2_m2_T in
            Some (le', m', (Alloc b1 0 (@sizeof ge ty) :: T))
        end.
    
    Lemma alloc_variablesT_fun_correct1:
        ∀ ge le m l le' m' T,
            alloc_variablesT_fun ge.(genv_cenv) le m l = Some (le', m', T) -> 
            alloc_variablesT ge le m l le' m' T.
    Proof.
        intros until l. generalize ge le m. induction l; intros; simpl in H.
        - inv H. apply alloc_variablesT_nil.
        - unfold_mbind_in_hyp. repeat destruct_match in H eqn:?.
          inv H. econstructor 2; last apply IHl; done.
    Qed.
End MemOpsT.

Section EvalExprTFun.
    Context (ge: genv).
    Context (le: env).
    Context (te: temp_env).
    Context (m: Memory.mem).

    Definition eval_lvalueT_fun' eval_exprT_fun (exp:expr) : option (Values.block * ptrofs * bitfield * list mem_event) :=
        match exp with
        | Evar id ty =>
            match le ! id with
            | Some (l, ty') => if decide (ty'=ty) then Some (l, Ptrofs.zero, Full, nil) else None (* eval_Evar_local *)
            | None => (* eval_Evar_global *)
                    l ← Globalenvs.Genv.find_symbol ge id;
                    Some (l, Ptrofs.zero, Full, nil)
            end
        | Ederef a ty => 
            v_T ← eval_exprT_fun a;
            let '(v, T) := v_T in
            match v with
            | Vptr l ofs => Some (l, ofs, Full, T)
            | _ => None
            end
        | Efield a i ty => 
            v_T ← eval_exprT_fun a;
            let '(v, T) := v_T in
            match v with
            | Vptr l ofs => 
                match typeof a with
                | Tstruct id att => 
                    (* eval_Efield_struct *)
                    co ← ge.(genv_cenv) ! id;
                    match field_offset ge i (co_members co) with
                    | Errors.OK (delta, bf) => Some (l, (Ptrofs.add ofs (Ptrofs.repr delta)), bf, T)
                    | _ => None
                    end
                | Tunion id att => 
                    (* eval_Efield_union *)
                    co ← ge.(genv_cenv) ! id;
                    match union_field_offset ge i (co_members co) with
                    | Errors.OK (delta, bf) => Some (l, (Ptrofs.add ofs (Ptrofs.repr delta)), bf, T)
                    | _ => None
                    end
                | _ => None
                end
            | _ => None
            end
        | _ => None 
        end.

    Fixpoint eval_exprT_fun (exp: expr) : option (val * list mem_event) :=
    match exp with
    | Econst_int i ty => Some (Vint i, nil)
    | Econst_float f ty => Some (Vfloat f, nil)
    | Econst_single f ty => Some (Vsingle f, nil)
    | Econst_long i ty => Some (Vlong i, nil)
    | Etempvar id ty => v ← te ! id; Some (v, nil)
    | Eaddrof a ty => match eval_lvalueT_fun' eval_exprT_fun a  with
                    | Some (loc, ofs, Full, T) => Some (Vptr loc ofs, T)
                    | _ => None
                    end
    | Eunop op a ty => v1_T ← eval_exprT_fun a; 
                         let '(v1, T) := v1_T in
                         v ← sem_unary_operation op v1 (typeof a) m;
                         Some (v, T)
    | Ebinop op a1 a2 ty => v1_T1 ← eval_exprT_fun a1;
                              let '(v1, T1) := v1_T1 in
                              v2_T2 ← eval_exprT_fun a2;
                              let '(v2, T2) := v2_T2 in
                              v ← sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) m;
                              Some (v, T1 ++ T2)
    | Ecast a ty => v1_T ← eval_exprT_fun  a;
                      let '(v1, T) := v1_T in
                      v ← sem_cast v1 (typeof a) ty m;
                      Some (v, T)
    | Esizeof ty1 ty => Some (Vptrofs (Ptrofs.repr (@sizeof ge ty1)), nil)
    | Ealignof ty1 ty => Some (Vptrofs (Ptrofs.repr (@alignof ge ty1)), nil)
    (* otherwise, an lvalue; eval_Elvalue *)
    | a => res ← eval_lvalueT_fun' eval_exprT_fun a;
        let '(loc, ofs, bf, T1) := res in
        v_T2 ← deref_locT_fun (typeof a) m loc ofs bf;
        let '(v, T2) := v_T2 in
        Some (v, T1 ++ T2)
    end.

    Definition eval_lvalueT_fun := eval_lvalueT_fun' eval_exprT_fun.
End EvalExprTFun.

Ltac fun_correct_tac :=
    lazymatch goal with
    | [ H: deref_locT_fun _ _ _ _ _ = Some _ |- _ ] => apply deref_locT_fun_correct1 in H
    | [ H: load_bitfieldT_fun _ _ _ _ _ _ _ _ = Some _ |- _ ] => apply load_bitfieldT_fun_correct1 in H
    | [ H: assign_locT_fun _ _ _ _ _ _ _ _ = Some _ |- _ ] => apply assign_locT_fun_correct1 in H
    | [ H: alloc_variablesT_fun _ _ _ _ = Some _ |- _ ] => apply alloc_variablesT_fun_correct1 in H
    end.

Section EvalExprFun.
    Context (ge: genv).
    Context (e: env). (* local env *)
    Context (le: temp_env).
    Context (m: Memory.mem).

    Notation eval_lvalueT_fun := (eval_lvalueT_fun ge e le m).
    Notation eval_exprT_fun := (eval_exprT_fun ge e le m).

    Lemma eval_exprT_fun_correct1 :
        ∀  exp, (∀ v T, @eval_exprT_fun exp = Some (v, T) -> eval_exprT ge e le m exp v T) ∧
                ∀ bl ofs bt T, eval_lvalueT_fun exp = Some (bl, ofs, bt, T) -> eval_lvalueT ge e le m exp bl ofs bt T.
    Proof.
    intro exp; induction exp; intros; split; intros; inv H; try (by constructor);
    try unfold_mbind_in_hyp; repeat destruct_match!; inv H1.
    - (* local *)
    fun_correct_tac.
    eapply evalT_Elvalue; eauto.
    eapply evalT_Evar_local; eauto.
    done.
    - (* global *)
    fun_correct_tac.
    eapply evalT_Elvalue; eauto.
    eapply evalT_Evar_global; eauto.
    done.
    - (* evalT_Evar_local *)
    constructor. done.
    - (* evalT_Evar_global *)
    apply evalT_Evar_global; done.
    - constructor; done.
    - 
    destruct IHexp as [IHexp1 IHexp2].
    eapply evalT_Elvalue; last done.
    + constructor. eapply IHexp1; done.
    + fun_correct_tac. done.
    - 
    destruct IHexp as [IHexp1 IHexp2].
    eapply evalT_Ederef.
    by eapply IHexp1.
    - destruct IHexp as [IHexp1 IHexp2].
      econstructor. by apply IHexp2.
    - destruct IHexp as [IHexp1 IHexp2].
    econstructor; eauto.
    - destruct IHexp1 as [IHexp1 _].
     destruct IHexp2 as [IHexp2 _].
    econstructor; eauto.
    - destruct IHexp as [IHexp1 IHexp2].
    econstructor; eauto.
    - (* evalT_Efield_struct *)
     subst. destruct IHexp as [IHexp1 IHexp2].
    econstructor. 
    * eapply evalT_Efield_struct; eauto.
    * by fun_correct_tac.
    * done.
    - (* evalT_Efield_union *)
    subst. destruct IHexp as [IHexp1 IHexp2].
    econstructor. 
    * eapply evalT_Efield_union; eauto.
    * by fun_correct_tac.
    * done.
    - (* evalT_Efield_struct *)
    subst. destruct IHexp as [IHexp1 IHexp2].
    eapply evalT_Efield_struct; eauto.
    - (* evalT_Efield_union *)
     subst. destruct IHexp as [IHexp1 IHexp2].
    eapply evalT_Efield_union; eauto.
    Qed.


    Fixpoint eval_exprTlist_fun (elist:list expr) (t: typelist) : option (list val * list mem_event) := 
        match elist, t with
        | nil, Ctypes.Tnil => Some ([], [])
        | a::bl, Ctypes.Tcons ty ty1 =>
                 v1_T ← eval_exprT_fun a;
                 let '(v1, T) := v1_T in
                 v2 ← sem_cast v1 (typeof a) ty m;
                 vl_Tl ← eval_exprTlist_fun bl ty1;
                 let '(vl, Tl) := vl_Tl in
                 Some (v2::vl, T ++ Tl)
        | _, _ => None
        end
    .

    Lemma evalT_exprlist_fun_correct1:
        ∀ elist t vl Tl, eval_exprTlist_fun elist t = Some (vl, Tl) -> eval_exprTlist ge e le m elist t vl Tl.
    Proof.
    Admitted.

End EvalExprFun.

Ltac fun_correct_tac ::=
    lazymatch goal with
    | [ H: deref_locT_fun _ _ _ _ _ = Some _ |- _ ] => apply deref_locT_fun_correct1 in H
    | [ H: load_bitfieldT_fun _ _ _ _ _ _ _ _ = Some _ |- _ ] => apply load_bitfieldT_fun_correct1 in H
    | [ H: assign_locT_fun _ _ _ _ _ _ _ = Some _ |- _ ] => apply assign_locT_fun_correct1 in H
    | [ H: alloc_variablesT_fun _ _ _ _ = Some _ |- _ ] => apply alloc_variablesT_fun_correct1 in H
    | [ H: eval_exprT_fun _ _ _ _ _ = Some _ |- _ ] => apply eval_exprT_fun_correct1 in H
    | [ H: eval_lvalueT_fun _ _ _ _ _ = Some _ |- _ ] => apply eval_exprT_fun_correct1 in H
    | [ H: eval_exprTlist_fun _ _ _ _ _ _ = Some _ |- _ ] => apply evalT_exprlist_fun_correct1 in H
    end.

Section EVStepFun.
    Context {ge: genv}.
    Context {e: env}. (* local env *)
    Context {le: temp_env}.
    Context {m: Memory.mem}.

    #[export] Instance list_norepet_dec_inst  (A: Type) (l:list A) :
        RelDecision (@eq A) -> Decision (Coqlib.list_norepet l).
    Proof. intros. unfold Decision. apply Coqlib.list_norepet_dec. done. Defined. 

    #[export] Instance list_disjoint_dec_inst  (A: Type) (l1 l2:list A) :
        RelDecision (@eq A) -> Decision (Coqlib.list_disjoint l1 l2).
    Proof. intros. unfold Decision. apply Coqlib.list_disjoint_dec. done. Defined.

    Definition cl_evstep_fun (s: CC_core) m : option (CC_core * mem * list mem_event) :=
    match s with 
    | State f (Sassign a1 a2) k e le =>  
        loc_ofs_bf_T1 ← eval_lvalueT_fun ge e le m a1;
        let '(loc, ofs, bf, T1) := loc_ofs_bf_T1 in
        v2_T2 ← eval_exprT_fun ge e le m a2;
        let '(v2, T2) := v2_T2 in
        v ← sem_cast v2 (typeof a2) (typeof a1) m; 
        m'_T3 ← assign_locT_fun ge (typeof a1) m loc ofs bf v;
        let '(m', T3) := m'_T3 in
        Some (State f Sskip k e le, m', T1++T2++T3)
    | State f (Sset id a) k e le =>
        v_T ← eval_exprT_fun ge e le m a;
        let '(v, T) := v_T in
        Some (State f Sskip k e (PTree.set id v le), m, T) 
    | State f (Scall optid a al) k e le =>
        vf_T1 ← eval_exprT_fun ge e le m a;
        let '(vf, T1) := vf_T1 in
        fd ← Genv.find_funct ge vf;
        match classify_fun (typeof a) with 
        | fun_case_f tyargs tyres cconv =>
            match type_of_fundef fd with
            | Tfunction tyargs' tyres' cconv' =>
                if decide ((tyargs = tyargs') ∧ (tyres = tyres') ∧ (cconv = cconv'))
                then         
                    vargs_T2 ← eval_exprTlist_fun ge e le m al tyargs;
                    let '(vargs, T2) := vargs_T2 in
                    Some (Callstate fd vargs (Kcall optid f e le k), m, T1++T2)
                else None
            | _ => None
            end
        | _ => None
        end
    | State f (Ssequence s1 s2) k e le =>
        Some (State f s1 (Kseq s2 k) e le, m, nil)
    | State f Sskip (Kseq s k) e le =>
        Some (State f s k e le, m, nil)
    | State f Scontinue (Kseq s k) e le =>
        Some (State f Scontinue k e le, m, nil)
    | State f Sbreak (Kseq s k) e le =>
        Some (State f Sbreak k e le, m, nil)
    | State f (Sifthenelse a s1 s2) k e le =>
        v1_T ← eval_exprT_fun ge e le m a;
        let '(v1, T) := v1_T in
        b ← bool_val v1 (typeof a) m;
        Some (State f (if b:bool then s1 else s2) k e le, m, T)
    | State f (Sloop s1 s2) k e le =>
        Some (State f s1 (Kloop1 s1 s2 k) e le, m, nil)
    | State f Sbreak (Kloop1 s1 s2 k) e le =>
        Some (State f Sskip k e le, m, nil)
    | State f x (Kloop1 s1 s2 k) e le => 
        match x with 
        | Sskip => Some (State f s2 (Kloop2 s1 s2 k) e le, m, nil) 
        | Scontinue => Some (State f s2 (Kloop2 s1 s2 k) e le, m, nil) 
        | _ => None
        end
    | State f Sskip (Kloop2 s1 s2 k) e le =>
        Some (State f (Sloop s1 s2) k e le, m, nil)
    | State f Sbreak (Kloop2 s1 s2 k) e le =>
        Some (State f Sskip k e le, m, nil)
    | State f (Sreturn None) k e le =>
        m' ← Mem.free_list m (blocks_of_env ge e); 
        Some (Returnstate Vundef (call_cont k), m', Free (Clight.blocks_of_env ge e)::nil)                               
    | State f (Sreturn (Some a)) k e le => 
        v_T ← eval_exprT_fun ge e le m a;
        let '(v, T) := v_T in
        v' ← sem_cast v (typeof a) f.(fn_return) m;
        m' ← Mem.free_list m (blocks_of_env ge e); 
        Some (Returnstate v' (call_cont k), m', T ++ Free (Clight.blocks_of_env ge e)::nil)
    | State f Sskip k e le =>
        m' ← Mem.free_list m (blocks_of_env ge e) ;
        if is_call_cont_bool k 
        then Some (Returnstate Vundef k, m', Free (Clight.blocks_of_env ge e)::nil)
        else None
    | State f (Sswitch a sl) k e le =>
        v_T ← eval_exprT_fun ge e le m a;
        let '(v, T) := v_T in
        n ← sem_switch_arg v (typeof a);
        Some (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le, m, T)
    | State f Scontinue (Kswitch k) e le =>
        Some (State f Scontinue k e le, m, nil)
    | State f x (Kswitch k) e le =>
        match x with 
        | Sskip | Sbreak => Some (State f Sskip k e le, m, nil)
        | _ => None
        end
    | State f (Slabel lbl s) k e le =>
        Some (State f s k e le, m, nil)
    | State f (Sgoto lbl) k e le =>
        s'_k' ← find_label lbl f.(fn_body) (call_cont k);
        let '(s', k') := s'_k' in
        Some (State f s' k' e le, m, nil)
    | Callstate (Internal f) vargs k => 
        if decide $ (Coqlib.list_norepet (var_names (fn_params f)) ∧ 
                     Coqlib.list_disjoint (var_names (fn_params f)) (var_names (fn_temps f)) ∧
                     Coqlib.list_norepet (var_names f.(fn_vars)))
        then e_m1_T ← alloc_variablesT_fun ge empty_env m (f.(fn_vars));
             let '(e, m1, T) := e_m1_T in
             le ← bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps));
             Some (State f f.(fn_body) k e le, m1, T)
        else None
    | Returnstate v (Kcall optid f e le k) => Some (State f Sskip k e (set_opttemp optid v le), m, nil)
    (*TODO: step_builtin, step_external_function, step_to_metastate, step_from_metastate*)
    (* | State f (Sbuiltin optid ef tyargs al) k e le m) => vargs ← eval_exprlist_fun ge e le m al tyargs; external_call ef ge vargs m *)
    (* | Callstate (External ef targs tres cconv) vargs k m) => Some (Returnstate vres k m') *)
    | State f (Spragma n ml s) k e le => Some (Pragmastate n ml (f, s, k, e, le), m, nil)
    | _ => None
        (* |(State f (Sbuiltin optid ef tyargs al) k e le m) => (State f Sskip k e (set_opttemp optid vres le) m') *)
    end .

    Ltac unfold_cl_evstep_fun :=
        match goal with
        | [ H: cl_evstep_fun _ _ = Some _ |- _ ] =>
            unfold cl_evstep_fun in H;
            try unfold_mbind_in_hyp;
            repeat destruct_match!;
            inv H
        end.

    Lemma evstep_fun_correct: 
        ∀ s m T s' m', cl_evstep_fun s m = Some (s', m', T) -> cl_evstep ge s m T s' m'.
    Proof.  intro s. destruct s; intros.
    (* State case *)
    - induction s eqn:Hs; try by (unfold_cl_evstep_fun; econstructor; eauto; repeat fun_correct_tac).
        + (* evstep_call *)
            unfold_cl_evstep_fun.
            econstructor; try by (repeat fun_correct_tac).
            { rewrite Heqt0. repeat destruct a; subst; done. }
        + (* evstep_ifthenelse *)
            unfold cl_evstep_fun in H.
            unfold_mbind_in_hyp; do 3 destruct_match in H eqn:?.
            inv H.
            eapply evstep_ifthenelse; by fun_correct_tac.
        +(* Sreturn *) 
            (* proof goes by destructing return value and current continuation *)
            unfold_cl_evstep_fun;
            try match goal with
            |  |- cl_evstep _ (State _ _ ?k1 _ _) _ _ (Returnstate _ (call_cont ?k2)) _ =>
            replace (call_cont k2) with (call_cont $ k1) by done
            end;
            econstructor; repeat fun_correct_tac; eauto.
    - unfold_cl_evstep_fun.
      repeat destruct a.
      econstructor; (repeat fun_correct_tac; eauto).
    - unfold_cl_evstep_fun.  constructor. 
    - inv H.
    Qed.
End EVStepFun.

Ltac fun_correct_tac ::=
    lazymatch goal with
    | [ H: deref_locT_fun _ _ _ _ _ = Some _ |- _ ] => apply deref_locT_fun_correct1 in H
    | [ H: load_bitfieldT_fun _ _ _ _ _ _ _ _ = Some _ |- _ ] => apply load_bitfieldT_fun_correct1 in H
    | [ H: assign_locT_fun _ _ _ _ _ _ _ = Some _ |- _ ] => apply assign_locT_fun_correct1 in H
    | [ H: alloc_variablesT_fun _ _ _ _ = Some _ |- _ ] => apply alloc_variablesT_fun_correct1 in H
    | [ H: eval_exprT_fun _ _ _ _ _ = Some _ |- _ ] => apply eval_exprT_fun_correct1 in H
    | [ H: eval_lvalueT_fun _ _ _ _ _ = Some _ |- _ ] => apply eval_exprT_fun_correct1 in H
    | [ H: eval_exprTlist_fun _ _ _ _ _ _ = Some _ |- _ ] => apply evalT_exprlist_fun_correct1 in H
    | [ H: cl_evstep_fun _ _ = Some _ |- _ ] => apply step_fun_correct in H
    end.