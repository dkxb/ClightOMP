(* adapted from concurrency/common/HybridMachione.v *)
From mathcomp.ssreflect Require Import ssreflect seq ssrbool ssrfun.
Require Import Coq.Classes.Morphisms.

Require Import compcert.common.Memory.
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Clight.
Require Import compcert.lib.Integers.

Require Import VST.msl.Axioms.
Require Import Coq.ZArith.ZArith.
(*Require Import VST.concurrency.common.core_semantics.*)
Require Import VST.concurrency.openmp_sem.event_semantics.
Require Export VST.concurrency.openmp_sem.semantics.
Require Export VST.concurrency.common.lksize.
Require Import VST.concurrency.openmp_sem.finThreadPool.

Require Import VST.concurrency.common.machine_semantics.
Require Import VST.concurrency.openmp_sem.permissions.
Require Import VST.concurrency.openmp_sem.mem_equiv.

Require Import VST.concurrency.openmp_sem.bounded_maps.
Require Import VST.concurrency.openmp_sem.addressFiniteMap.

Require Import VST.concurrency.common.scheduler.
Require Import Coq.Program.Program.

From VST.concurrency.openmp_sem Require Import HybridMachineSig team_dyn notations reduction canonical_loop_nest for_construct Clight_evsem Clight_core.
From stdpp Require Import base.
(* Require Import VST.concurrency.CoreSemantics_sum. *)
Import -(notations) Maps.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import Coq.Relations.Relation_Operators.

Lemma at_external_SEM_eq:
  forall ge c m, memory_semantics.at_external (csem (msem (CLC_evsem ge))) c m =
  match c with
  | Callstate (Ctypes.External ef _ _ _) args _ => 
      if ef_inline ef then None else Some (ef, args)
  | _ => None
  end.
Proof. auto. Qed.

Lemma at_pragma_SEM_eq:
   forall ge c, memory_semantics.at_pragma (csem (msem (CLC_evsem ge))) c =
  match c with
  | Pragmastate n pl _ => Some (n, pl)
  | _ => None
  end.
Proof. auto. Qed.

#[export] Instance ClightSem ge : Semantics :=
  { semG := G; semC := C; semSem := CLC_evsem ge; the_ge := ge }.

Module DryHybridMachine.
  Import Events ThreadPool.

  #[export] Instance dryResources: Resources:=
    {| res := access_map * access_map;
       lock_info := access_map * access_map |}.

  Section DryHybridMachine.
        
    Context {ge:genv}.
    (** Unlike the original CPM work, the OpenMP semantics is only defined on C,
        so we don't quantify over semantics (while we probably could). *)
    Instance Sem : Semantics := ClightSem ge.
    
    Context {tpool : @ThreadPool.ThreadPool dryResources Sem}.
    (* define this as clightSem in clightSemanticsForMachines*)
    Notation C:= (@semC Sem).
    Notation G:= (@semG Sem).

    Notation semSem:= (@semSem Sem).

    Notation thread_pool := (@t dryResources Sem).
    Local Open Scope stdpp_scope.
    (** Memories*)
    Definition richMem: Type:= mem.
    Definition dryMem: richMem -> mem:= fun x => x.
    
    (** The state respects the memory*)
    
    Record mem_compatible (tp: thread_pool) m : Prop :=
      { compat_th :> forall {tid} (cnt: containsThread tp tid),
            permMapLt (getThreadR cnt).1 (getMaxPerm m) /\
            permMapLt (getThreadR cnt).2 (getMaxPerm m);
        compat_lp : forall l pmaps, lockRes tp l = Some pmaps ->
                               permMapLt pmaps.1 (getMaxPerm m) /\
                               permMapLt pmaps.2 (getMaxPerm m);
        lockRes_blocks: forall l rmap, lockRes tp l = Some rmap ->
                                  Mem.valid_block m l.1}.

      Lemma  mem_compat_restrPermMap:
        forall m perms st
          (permMapLt: permMapLt perms (getMaxPerm m)),
          (mem_compatible st m) ->
          (mem_compatible st (restrPermMap permMapLt)).
      Proof.
        intros.
        inversion H; econstructor.
        - intros; unfold permissions.permMapLt.
          split; intros;
            erewrite getMax_restr; 
            eapply compat_th0.
        - intros; unfold permissions.permMapLt.
          split; intros;
            erewrite getMax_restr; 
            eapply compat_lp0; eauto.
        - intros. eapply restrPermMap_valid; eauto.
      Qed.

    (* should there be something that says that if something is a lock then
     someone has at least readable permission on it?*)
    Record invariant (tp: thread_pool) :=
      { no_race_thr :
          forall i j (cnti: containsThread tp i) (cntj: containsThread tp j)
            (Hneq: i <> j),
            permMapsDisjoint2 (getThreadR cnti)
                              (getThreadR cntj); (*thread's resources are disjoint *)
        no_race_lr:
          forall laddr1 laddr2 rmap1 rmap2
            (Hneq: laddr1 <> laddr2)
            (Hres1: lockRes tp laddr1 = Some rmap1)
            (Hres2: lockRes tp laddr2 = Some rmap2),
            permMapsDisjoint2 rmap1 rmap2; (*lock's resources are disjoint *)
        no_race:
          forall i laddr (cnti: containsThread tp i) rmap
            (Hres: lockRes tp laddr = Some rmap),
            permMapsDisjoint2 (getThreadR cnti) rmap; (*resources are disjoint
             between threads and locks*)

        (* if an address is a lock then there can be no data
             permission above non-empty for this address*)
        thread_data_lock_coh:
          forall i (cnti: containsThread tp i),
            (forall j (cntj: containsThread tp j),
                permMapCoherence (getThreadR cntj).1 (getThreadR cnti).2) /\
            (forall laddr rmap,
                lockRes tp laddr = Some rmap ->
                permMapCoherence rmap.1 (getThreadR cnti).2);
        locks_data_lock_coh:
          forall laddr rmap
            (Hres: lockRes tp laddr = Some rmap),
            (forall j (cntj: containsThread tp j),
                permMapCoherence (getThreadR cntj).1 rmap.2) /\
            (forall laddr' rmap',
                lockRes tp laddr' = Some rmap' ->
                permMapCoherence rmap'.1 rmap.2);
        lockRes_valid: lr_valid (lockRes tp) (*well-formed locks*)
      }.


    (** Steps*)
    Inductive dry_step {tid0 tp m} (cnt: containsThread tp tid0)
              (Hcompatible: mem_compatible tp m) :
      thread_pool -> mem -> seq.seq mem_event -> Prop :=
    | step_dry :
        forall (tp':thread_pool) c m1 m' (c' : C) ev
          (** Instal the permission's of the thread on non-lock locations*)
          (Hrestrict_pmap: restrPermMap (Hcompatible tid0 cnt).1 = m1)
          (Hinv: invariant tp)
          (Hcode: getThreadC cnt = Krun c)
          (Hcorestep: ev_step semSem c m1 ev c' m')
          (** the new data resources of the thread are the ones on the
           memory, the lock ones are unchanged by internal steps*)
          (Htp': tp' = updThread cnt (Krun c') (getCurPerm m', (getThreadR cnt).2)),
          dry_step cnt Hcompatible tp' m' ev.

    Definition option_function {A B} (opt_f: option (A -> B)) (x:A): option B:=
      match opt_f with
        Some f => Some (f x)
      | None => None
      end.
    Infix "??" := option_function (at level 80, right associativity).

    Definition build_delta_content (dm: delta_map) (m:mem): delta_content :=
      PTree.map (fun b dm_f =>
                   fun ofs =>
                     match dm_f ofs with
                     | None | Some (None) 
                     | Some (Some Nonempty) => None
                     | Some _ => Some (ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)))
                     end) dm.

    (* get the index of the pragma *)
    Definition get_idx (c: Clight_core.state) : option nat :=
      match c with
      | Clight_core.Pragmastate n _ _ => Some n
      | _ => None
      end.
  
    (* Notation "'SBarrier' idx b ck" := *)
    Definition Sbarrier idx b ck :=
      Spragma idx (OMPBarrier b ck) Sskip.

    (* ge, le stores reduction vars' original copies' addresses *)
    Definition Sred idx rcs rcs_env :=
      Spragma idx (OMPRed rcs rcs_env) Sskip.

    Definition Spriv idx pc pc_first rcs s :=
      Spragma idx (OMPPriv pc pc_first rcs) s.

    Definition SBRB idx ck rcs rcs_env : statement :=
      let SBR :=
        match rcs with
        | [] => Sskip
        | _ => Ssequence (Sbarrier idx false ck) (Sred idx rcs rcs_env)
        end in
      Ssequence SBR (Sbarrier idx true ck).

    Definition SprivEnd idx pvs le_0 :=
      Spragma idx (OMPPrivEnd pvs le_0) Sskip.

    (* ge is genv_symb *)
    Definition transform_state_parallel (c: state) (rcs_env: env) (is_leader:bool) : option state :=
      match c with
      | Clight_core.Pragmastate idx (OMPParallel tn pc pc_first rcs) (f,s,k,le,te) =>
        let s' := Ssequence s (SBRB idx ParallelConstruct rcs rcs_env) in
        let s'' := Spriv idx pc pc_first rcs s' in
        let k' := if is_leader then k else Kstop in
        Some (Clight_core.State f s'' k' le te)
      | _ => None
      end.

    Definition transform_state_for (c: state) (rcs_env: env) (my_workload: list chunk) (cln: CanonicalLoopNest) : option state :=
      match c with
      | Clight_core.Pragmastate idx (OMPFor pc pc_first rcs) (f,s,k,le,te) =>
         let s' := Ssequence (transform_chunks my_workload cln)
                             (SBRB idx ForConstruct rcs rcs_env) in
         let s'' := Spriv idx pc pc_first rcs s' in
        Some (Clight_core.State f s'' k le te)
      | _ => None
      end.

    Definition transform_state_single (c: state) (is_chosen:bool) : option state :=
      match c with
      | Clight_core.Pragmastate idx (OMPSingle pc pc_first) (f,s,k,le,te) =>
        let s' := if is_chosen then s else Sskip in
        let s'' := Ssequence s' (Sbarrier idx true SingleConstruct) in
        let s''' := Spriv idx pc pc_first [] s'' in
        Some (Clight_core.State f s''' k le te)
      | _ => None
      end.

    Definition update_le (c: state) (le': env) : option state :=
      match c with
      | State f s k le te => Some $ State f s k le' te
      | Pragmastate n ml (f,s,k,le,te) => Some $ Pragmastate n ml (f,s,k,le',te)
      | _ => None
      end.

    Definition update_stmt (c: state) (s': statement) : option state :=
      match c with
      | State f _ k le te => Some $ State f s' k le te
      | Pragmastate n ml (f,s',k,le,te) => Some $ Pragmastate n ml (f,s',k,le,te)
      | _ => None
      end.

    Definition update_stmt_le (c: state) (s': statement) (le': env) : option state :=
      match c with
      | State f _ k _ te => Some $ State f s' k le' te
      | Pragmastate n ml (f,s',k,_,te) => Some $ Pragmastate n ml (f,s',k,le',te)
      | _ => None
      end.

    Definition get_stmt (c: state) : option statement :=
      match c with
      | State _ s _ _ _ => Some s
      | Pragmastate _ _ (_,s,_,_,_) => Some s
      | _ => None
      end.

    Definition get_le (c: state) : option env :=
      match c with
      | State _ _ _ le _ => Some le
      | Pragmastate _ _ (_,_,_,le,_) => Some le
      | _ => None
      end.

    Definition get_te (c: state) : option temp_env :=
      match c with
      | State _ _ _ _ te => Some te
      | Pragmastate _ _ (_,_,_,_,te) => Some te
      | _ => None
      end.

    Definition get_f (c: state) : option function :=
      match c with
      | State f _ _ _ _ => Some f
      | Pragmastate _ _ (f,_,_,_,_) => Some f
      | _ => None
      end.

    Definition ce := ge.(genv_cenv).

    Definition Kblocked_at (ct:ctl) : option C :=
       match ct with
      | Kblocked c => Some c
      | _ => None
      end.

    Definition Krun_at (ct: ctl) : option C :=
      match ct with
      | Krun c => Some c
      | _ => None
      end.

    Definition get_state (ct:ctl) :option C :=
      match ct with
      | Kblocked c => Some c
      | Krun c => Some c
      | _ => None
      end.
  
    Definition permMapJoinPair (pmap1 pmap2 pmap3: res) : Prop :=
      permMapJoin pmap1.1 pmap2.1 pmap3.1 ∧
      permMapJoin pmap1.2 pmap2.2 pmap3.2.

    Definition emptyPerm: res := (empty_map, empty_map).
    Definition permMapJoin_list pmaps pmap : Prop :=
      sepalg_list.fold_rel permMapJoinPair emptyPerm pmaps pmap.

    (** Setoid instances for rewriting with [access_map_equiv] inside
        [permMapJoin_list]. *)

    #[export] Instance permMapJoin_proper :
      Proper (access_map_equiv ==> access_map_equiv ==> access_map_equiv ==> iff)
             permMapJoin.
    Proof.
      intros a1 a2 Ha b1 b2 Hb c1 c2 Hc.
      unfold permMapJoin, access_map_equiv in *.
      split; intros H b ofs; specialize (H b ofs).
      - rewrite -(Ha b) -(Hb b) -(Hc b); exact H.
      - rewrite (Ha b) (Hb b) (Hc b); exact H.
    Qed.

    Definition res_equiv (r1 r2 : res) : Prop :=
      access_map_equiv r1.1 r2.1 /\ access_map_equiv r1.2 r2.2.

    #[export] Instance res_equiv_Equivalence : Equivalence res_equiv.
    Proof.
      constructor.
      - intros [? ?]; split; reflexivity.
      - intros [? ?] [? ?] [H1 H2]; split; symmetry; assumption.
      - intros [? ?] [? ?] [? ?] [H1 H2] [H3 H4]; split; etransitivity; eassumption.
    Qed.

    #[export] Instance permMapJoinPair_proper :
      Proper (res_equiv ==> res_equiv ==> res_equiv ==> iff) permMapJoinPair.
    Proof.
      intros r1 s1 [H11 H12] r2 s2 [H21 H22] r3 s3 [H31 H32].
      unfold permMapJoinPair.
      split; intros [A B]; split.
      - exact (proj1 (permMapJoin_proper H11 H21 H31) A).
      - exact (proj1 (permMapJoin_proper H12 H22 H32) B).
      - exact (proj2 (permMapJoin_proper H11 H21 H31) A).
      - exact (proj2 (permMapJoin_proper H12 H22 H32) B).
    Qed.

    Lemma fold_rel_permMapJoinPair_Forall2 :
      forall pmaps pmaps' (e : res) pmap,
        List.Forall2 res_equiv pmaps pmaps' ->
        sepalg_list.fold_rel permMapJoinPair e pmaps pmap <->
        sepalg_list.fold_rel permMapJoinPair e pmaps' pmap.
    Proof.
      intros pmaps pmaps' e0 pmap0 HF. revert e0 pmap0.
      induction HF as [| r r' rs rs' Hr _ IH]; intros e pmap.
      - tauto.
      - split; intro H; inversion H; subst.
        + eapply sepalg_list.fold_rel_cons.
          * setoid_rewrite <- Hr; eassumption.
          * apply (proj1 (IH _ _)); eassumption.
        + eapply sepalg_list.fold_rel_cons.
          * setoid_rewrite Hr; eassumption.
          * apply (proj2 (IH _ _)); eassumption.
    Qed.

    #[export] Instance permMapJoin_list_proper :
      Proper (List.Forall2 res_equiv ==> eq ==> iff) permMapJoin_list.
    Proof.
      intros pmaps pmaps' HF pmap pmap' <-.
      exact (fold_rel_permMapJoinPair_Forall2 pmaps pmaps' emptyPerm pmap HF).
    Qed.

    Program Fixpoint fold_siblings {B:Type} (f: stree -> B -> B) (b:B) tz {measure (tree_pos_measure tz)} : (team_zipper * B) :=
      let b' := f tz.this b in
      match go_right tz with
      | None => (tz, b')
      | Some tz' => fold_siblings f b' tz'
      end.
    Next Obligation. intros. destruct tz. destruct a; try done.
        subst filtered_var.
        Coqlib.inv Heq_anonymous.
      simpl. rewrite /fmap. destruct tis; simpl. Lia.lia. Defined.
    Next Obligation. apply measure_wf. apply lt_wf. Defined.

    (* check that all threads in mates_tids are at pragma_label `pl` and pragma index idx,
       and collect their local env *)
    Definition all_at_pragma tp mates_tids (pl:pragma_label) idx : option $ list env :=
      foldr (λ tid maybe_le_lst,
            le_lst ← maybe_le_lst;
            cnt_i ← maybeContainsThread tp tid;
            (* every thread is blocked at pragma_label *)
            c ← Kblocked_at $ getThreadC cnt_i;
            match at_pragma semSem c with
            | Some (idx', pl) =>
              if decide (idx' = idx) then
              (* appends the local environment *)
              le ← get_le c;
              Some $ le::le_lst
              else None
            | _ => None
            end)
            (Some []) mates_tids.

    Definition id_ty_of_fun (f: function) (var: ident) : option Ctypes.type :=
      id_ty ← find (λ p, if ident_eq p.1 var then true else false)
                   $ f.(fn_params) ++ f.(fn_vars) ++ f.(fn_temps);
      Some id_ty.2.

    Definition getThreadRs (tp: thread_pool) (tids: list nat) : list res :=
      map (λ tid,
            match maybeContainsThread tp tid with
            | Some cnt => getThreadR cnt
            | None => emptyPerm
            end) tids.

    Definition make_rvs_env_i (i: ident) ge le rvs_env : option env :=
      b_ty ← clight_fun.get_b_ty ge le i;
      Some (PTree.set i b_ty rvs_env).
    
    Definition make_rvs_env (rcs: list reduction_clause_type) ge le : option env :=
      foldr (λ i maybe_rvs_env,
          rvs_env ← maybe_rvs_env;
          make_rvs_env_i i ge le rvs_env) (Some empty_env) (rcs_priv_idents rcs).

    Inductive pragma_step {tid0 tp m} {ttree: team_tree}
              (cnt0:containsThread tp tid0)(Hcompat:mem_compatible tp m):
      thread_pool -> mem -> team_tree -> list machine_event -> Prop :=
    | step_parallel :
        forall (tp' tp'' tp''':thread_pool) c c'_l c'_nl le rvs_env m'
          ttree' (num_threads:nat) pc pc_first rcs (new_tids: list nat) idx
          perm (perms:list res),
          forall
            (* TODO num_thread at least 2? *)
            (Hinv : invariant tp)
            (* To check if the machine is at an external step and load its arguments install the thread data permissions*)
            (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).1 = m')
            (Hc: Kblocked_at (getThreadC cnt0) = Some c)
            (Hat_pragma: at_pragma semSem c = Some (idx, OMPParallel num_threads pc pc_first rcs))
            (* 1. spawn new threads as fork, add them to team, and split permissions angelically*)
            (Hnum_threads: num_threads > 0)
            (Hperm: perm = getThreadR cnt0)
            (* perms is an angelic split of the original permission perm *)
            (HangleSplit: permMapJoin_list perms perm)
            (Hperms_length: length perms = num_threads)
            (* rvs_env stores the mapping from idents to (block, type) of the original copies of a reduction var. *)
            (Hle: Some le = get_le c)
            (Hrvs_env: Some rvs_env = make_rvs_env rcs ge le)
            (Hc': Some c'_l = transform_state_parallel c rvs_env true)
            (Hc': Some c'_nl = transform_state_parallel c rvs_env false)
            (Htp': tp' = updThread cnt0 (Krun c'_l) (nth 0 perms emptyPerm))
            (Htp'': (new_tids, tp'') = addThreads tp' c'_nl (tl perms))
            (* 2. add new team to team_tree, sets info about parallel construct as a team context *)
            (Htree': Some ttree' = spawn_team tid0 new_tids idx ttree),
            pragma_step cnt0 Hcompat tp'' m' ttree' []
    | step_for :
      forall c c' le te rvs_env stmt cln lb incr iter_num mates_tids team_size
       chunks (team_workloads : list $ list chunk) (my_workload: list chunk)
       (ttree' : team_tree)
       tp' tnum pc pc_first rcs m' idx tm_exec_ctx
      (Hcode: getThreadC cnt0 = Kblocked c)
      (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).1 = m')
      (Hat_pragma: at_pragma semSem c = Some (idx, OMPFor pc pc_first rcs))
      (* next statement is a canonical loop nest *)
      (Hstmt: Some stmt = get_stmt c)
      (Hle: Some le = get_le c)
      (Hte: Some te = get_te c)
      (* exists a chunk split of the iterations *)
      (His_cln: make_canonical_loop_nest stmt = Some cln)
      (Hlb_of_loop: lb_of_loop cln ge le te m = Some lb)
      (Hincr_of_loop: incr_of_loop cln ge le te m = Some incr)
      (Hiter_num_of_loop: iter_num_of_loop cln ge le te m = Some iter_num)
      (Hmates_tids: Some mates_tids = team_mates_tids tid0 ttree)
      (Hteam_size: team_size = length mates_tids)
      (chunkSplit: ChunkSplit lb incr iter_num team_size chunks team_workloads),
      forall
      (* 1. first thread encountering the for-construct adds the team_exec_ctx
            for the for-construct, including reduction info and a partition of
            iterations. *)
      (Htm_exec_ctx: tm_exec_ctx = (idx, team_ctx_for team_workloads) )
      (Httree': Some ttree' = tz' ← mate_maybe_add_team_exec_ctx (from_stree ttree) tid0 tm_exec_ctx;
                              to_stree tz')
      (* 2. update current statement to be my workload *)
      (Htnum: Some tnum = get_thread_num tid0 (from_stree ttree'))
      (Hchunks: Some my_workload = nth_error team_workloads tnum)
      (Hrvs_env: Some rvs_env = make_rvs_env rcs ge le)
      (Hc'': Some c' = transform_state_for c rvs_env my_workload cln)
      (* 4. update tp with the new c' *)
      (Htp': tp' = updThreadC cnt0 (Krun c')),
      pragma_step cnt0 Hcompat tp' m' ttree' []
    | step_single :
      forall c c' pc pc_first m' idx tm_exec_ctx tnum chosen_tnum tp' ttree' 
      (Hcode: getThreadC cnt0 = Kblocked c)
      (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).1 = m')
      (Hat_pragma: at_pragma semSem c = Some (idx, OMPSingle pc pc_first))
      (* check ectx, see if I am the chosen team mate *)
      (Htm_exec_ctx: tm_exec_ctx = (idx, team_ctx_single chosen_tnum) )
      (Htnum: Some tnum = get_thread_num tid0 (from_stree ttree))
      (Httree': Some ttree' = tz' ← mate_maybe_add_team_exec_ctx (from_stree ttree) tid0 tm_exec_ctx;
                              to_stree tz')
      (* update state *)
      (Hc': Some c' = transform_state_single c (chosen_tnum =? tnum))
      (Htp': tp' = updThreadC cnt0 (Krun c')),
      pragma_step cnt0 Hcompat tp' m' ttree' []
    | step_barrier :
      (* if all teammates are at barrier, move them across the barrier. *)
      forall m' idx (is_ending_region:bool) (s_tag: construct_kind) mates_tids 
      ttree' tp' tp'' perms1 perms2 perm_sum
      (Hinv : invariant tp)
      (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).1 = m')
      (* 1. check all threads are at the same barrier, and then move them accross barrier *)
      (Hmates_tids: Some mates_tids = team_mates_tids tid0 ttree)
      (Hstep_barrier: Some tp' = foldr (λ tid maybe_tp,
          tp ← maybe_tp;
          cnt_i ← maybeContainsThread tp tid;
          c ← Kblocked_at $ getThreadC cnt_i;
          match at_pragma semSem c with
          (* all at the same barrier *)
          | Some (idx, OMPBarrier is_ending_region s_tag) =>
            c' ← update_stmt c Sskip;
            Some $ updThreadC cnt_i (Krun c')
          | _ => None
          end)
        (Some tp) mates_tids)
      (* 2. check constraints on ectx, and end a region if required *)
      (Hcheck_ectx: has_ectx_iff_team_executed (from_stree ttree) tid0 s_tag)
      (Httree': Some ttree' =
                  if is_ending_region
                  then tz ← tz_end_ctx (from_stree ttree) tid0 s_tag idx;
                       to_stree tz
                  else Some ttree)
      (* 3. sync permissions *)
      (Hperms1: perms1 = getThreadRs tp' mates_tids)
      (Hperms2: perms2 = getThreadRs tp'' mates_tids)
      (Hperms1_eq: permMapJoin_list perms1 perm_sum)
      (Hperms2_eq: permMapJoin_list perms2 perm_sum),
      pragma_step cnt0 Hcompat tp'' m ttree' []
    | step_priv :
      forall c c' c'' le le' te s pc pc_first rcs pvs m' idx tp'
      (Hinv : invariant tp)
      (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).1 = m')
      (Hcode: getThreadC cnt0 = Kblocked c)
      (Hat_pragma: at_pragma semSem c = Some (idx, OMPPriv pc pc_first rcs))
      (Hs: Some s = get_stmt c)
      (Hle: Some le = get_le c)
      (Hte: Some te = get_te c)
      (* do privatization *)
      (Hpriv: Some (le', m') = privatization pc pc_first rcs m ge le te)
      (Hc': Some c' = update_le c le')
      (* update current statement *)
      (Hpvs: pvs = priv_idents pc pc_first rcs)
      (Hc'': Some c'' = update_stmt c' (Ssequence s (SprivEnd idx pvs le)))
      (* update tp with the new state and permissions from m', similar to dry_step (i.e. a Clight step) *)
      (Htp': tp' = updThread cnt0 (Krun c'') (getCurPerm m', (getThreadR cnt0).2)),
      pragma_step cnt0 Hcompat tp' m' ttree []
    | step_priv_end :
      forall c c' c'' le le' le_0 pvs m' idx tp'
        (Hinv : invariant tp)
        (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).1 = m')
        (Hcode: getThreadC cnt0 = Kblocked c)
        (Hat_pragma: at_pragma semSem c = Some (idx, OMPPrivEnd pvs le_0))
        (Hle: Some le = get_le c)
        (* end privatization *)
        (Hpriv_end: Some (le', m') = end_privatization pvs ge le le_0 m)
        (Hc': Some c' = update_le c le')
        (* forward statement *)
        (Hc': Some c'' = update_stmt c' Sskip)
        (* update tp with the new state and permissions from m', similar to dry_step (i.e. a Clight step) *)
        (Htp': tp' = updThread cnt0 (Krun c'') (getCurPerm m', (getThreadR cnt0).2)),
        pragma_step cnt0 Hcompat tp' m' ttree []
    (* semantics for Sred: the leader does the redution, other threads treat it as no-op. *)
    | step_red_leader :
      forall c c' rcs rvs_env m' idx tp' (le_lst : list env)
      mates_tids
      (Hinv : invariant tp)
      (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).1 = m')
      (Hcode: getThreadC cnt0 = Kblocked c)
      (Hat_pragma: at_pragma semSem c = Some (idx, OMPRed rcs rvs_env))
      (* 1. the leader does reduction *)
      (His_leader: is_leader tid0 (from_stree ttree) = true)
      (* 2. find teammmates' local envs (including tid0's), do reduction.
         it is safe to lookup other thread's le and compile them into le_lst,
         but reading values in memorywith le_lst during reduction requires permissions of these reduction locations.
         This should be ensured by the previous barrier. *)
      (Hmates_tids: Some mates_tids = team_mates_tids tid0 ttree)
      (Hle_lst: Some le_lst = foldr (λ i maybe_le_lst,
            le_lst ← maybe_le_lst;
            cnt_i ← maybeContainsThread tp i;
            c_i ← get_state (getThreadC cnt_i);
            le_i ← get_le c_i;
            Some $ le_i::le_lst)
            (Some []) mates_tids)
      (Hreduce: Some m' = reduction rcs ge le_lst rvs_env m)
      (* forward statement *)
      (Hc': Some c' = update_stmt c Sskip)
      (* update tp with the new state and permissions from m', similar to dry_step (i.e. a Clight step) *)
      (Htp': tp' = updThread cnt0 (Krun c') (getCurPerm m', (getThreadR cnt0).2)),
      pragma_step cnt0 Hcompat tp' m' ttree []
    | step_red_not_leader :
      forall c c' rcs rvs_env m' idx tp'
      (Hinv : invariant tp)
      (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).1 = m')
      (Hcode: getThreadC cnt0 = Kblocked c)
      (Hat_pragma: at_pragma semSem c = Some (idx, OMPRed rcs rvs_env))
      (* 1. the leader does reduction *)
      (His_leader: is_leader tid0 (from_stree ttree) = false)
      (* forward statement *)
      (Hc': Some c' = update_stmt c Sskip)
      (* update tp with the new state and permissions from m', similar to dry_step (i.e. a Clight step) *)
      (Htp': tp' = updThreadC cnt0 (Krun c')),
      pragma_step cnt0 Hcompat tp' m ttree []
    .

    Definition threadStep: forall {tid0 ms m},
        containsThread ms tid0 -> mem_compatible ms m ->
        thread_pool -> mem -> seq.seq mem_event -> Prop:=
      @dry_step.

    Lemma threadStep_at_Krun:
      forall i tp m cnt cmpt tp' m' tr,
        @threadStep i tp m cnt cmpt tp' m' tr ->
        (exists q, @getThreadC _ _ _ i tp cnt = Krun q).
    Proof.
      intros.
      inversion H; subst;
        now eauto.
    Qed.
    
    Lemma threadStep_equal_run:
      forall i tp m cnt cmpt tp' m' tr,
        @threadStep i tp m cnt cmpt tp' m' tr ->
        forall j,
          (exists cntj q, @getThreadC _ _ _ j tp cntj = Krun q) <->
          (exists cntj' q', @getThreadC _ _ _ j tp' cntj' = Krun q').
    Proof.
      intros. split.
      - intros [cntj [ q running]].
        inversion H; subst.
        assert (cntj':=cntj).
        (* XXX: eapply does not work here. report? *)
        pose proof (cntUpdate (Krun c') (getCurPerm m', (getThreadR cnt)#2) cnt cntj') as cntj''.
        exists cntj''.
        destruct (NatTID.eq_tid_dec i j).
        + subst j; exists c'.
          rewrite gssThreadCode; reflexivity.
        + exists q.
          erewrite gsoThreadCode;
            now eauto.
      - intros [cntj' [ q' running]].
        inversion H; subst.
        assert (cntj:=cntj').
        eapply cntUpdate' with(c:=Krun c')(p:=(getCurPerm m', (getThreadR cnt)#2)) in cntj; eauto.
        exists cntj.
        destruct (NatTID.eq_tid_dec i j).
        + subst j; exists c.
          rewrite <- Hcode.
          f_equal.
          apply cnt_irr.
        + exists q'.
          rewrite gsoThreadCode in running; auto.
    Qed.

    Definition pragmaStep:
      forall {tid0 ms m ttree},
        containsThread ms tid0 -> mem_compatible ms m ->
        thread_pool -> mem -> team_tree -> list machine_event -> Prop:=
      @pragma_step.

    Inductive ext_step {isCoarse:bool} {tid0 tp m}
              (cnt0:containsThread tp tid0)(Hcompat:mem_compatible tp m):
      thread_pool -> mem -> sync_event -> Prop :=
    | step_acquire :
        forall (tp' tp'':thread_pool) marg m0 m1 c m' b ofs
          (pmap : lock_info)
          (pmap_tid' : access_map)
          (virtueThread : delta_map * delta_map)
          (Hbounded: if isCoarse then
                       ( sub_map virtueThread.1 (getMaxPerm m).2 /\
                         sub_map virtueThread.2 (getMaxPerm m).2)
                     else
                       True ),
          let newThreadPerm := (computeMap (getThreadR cnt0).1 virtueThread.1,
                                computeMap (getThreadR cnt0).2 virtueThread.2) in
          forall
            (Hinv : invariant tp)
            (Hcode: getThreadC cnt0 = Kblocked c)
            (* To check if the machine is at an external step and load its arguments install the thread data permissions*)
            (Hrestrict_pmap_arg: restrPermMap (Hcompat tid0 cnt0).1 = marg)
            (Hat_external: memory_semantics.at_external semSem c marg = Some (LOCK, Vptr b ofs::nil))
            (** install the thread's permissions on lock locations*)
            (Hrestrict_pmap0: restrPermMap (Hcompat tid0 cnt0).2 = m0)
            (** To acquire the lock the thread must have [Readable] permission on it*)
            (Haccess: Mem.range_perm m0 b (Ptrofs.intval ofs) ((Ptrofs.intval ofs) + LKSIZE) Cur Readable)
            (** check if the lock is free*)
            (Hload: Mem.load Mptr m0 b (Ptrofs.intval ofs) = Some (Vptrofs Ptrofs.one))
            (** set the permissions on the lock location equal to the max permissions on the memory*)
            (Hset_perm: setPermBlock (Some Writable)
                                     b (Ptrofs.intval ofs) ((getThreadR cnt0).2) LKSIZE_nat = pmap_tid')
            (Hlt': permMapLt pmap_tid' (getMaxPerm m))
            (Hlt_new: if isCoarse then
                       ( permMapLt (fst newThreadPerm) (getMaxPerm m) /\
                         permMapLt (snd newThreadPerm) (getMaxPerm m))
                     else True )
            (Hrestrict_pmap: restrPermMap Hlt' = m1)
            (** acquire the lock*)
            (Hstore: Mem.store Mptr m1 b (Ptrofs.intval ofs) (Vptrofs Ptrofs.zero) = Some m')
            (HisLock: lockRes tp (b, Ptrofs.intval ofs) = Some pmap)
            (Hangel1: permMapJoin pmap.1 (getThreadR cnt0).1 newThreadPerm.1)
            (Hangel2: permMapJoin pmap.2 (getThreadR cnt0).2 newThreadPerm.2)
            (Htp': tp' = updThread cnt0 (Kresume c Vundef) newThreadPerm)
            (** acquiring the lock leaves empty permissions at the resource pool*)
            (Htp'': tp'' = updLockSet tp' (b, Ptrofs.intval ofs) (empty_map, empty_map)),
            ext_step cnt0 Hcompat tp'' m'
                     (acquire (b, Ptrofs.intval ofs)
                              (Some (build_delta_content (fst virtueThread) m')))

    | step_release :
        forall (tp' tp'':thread_pool) marg m0 m1 c m' b ofs virtueThread virtueLP pmap_tid' rmap
          (Hbounded: if isCoarse then
                       ( sub_map virtueThread.1 (getMaxPerm m).2 /\
                         sub_map virtueThread.2 (getMaxPerm m).2)
                     else
                       True )
          (HboundedLP: if isCoarse then
                         ( map_empty_def virtueLP.1 /\
                           map_empty_def virtueLP.2 /\
                           sub_map virtueLP.1.2 (getMaxPerm m).2 /\
                           sub_map virtueLP.2.2 (getMaxPerm m).2)
                       else
                         True ),
          let newThreadPerm := (computeMap (getThreadR cnt0).1 virtueThread.1,
                                computeMap (getThreadR cnt0).2 virtueThread.2) in
          forall
            (Hinv : invariant tp)
            (Hcode: getThreadC cnt0 = Kblocked c)
            (* To check if the machine is at an external step and load its arguments install the thread data permissions*)
            (Hrestrict_pmap_arg: restrPermMap (Hcompat tid0 cnt0).1 = marg)
            (Hat_external: memory_semantics.at_external semSem c marg =
                           Some (UNLOCK, Vptr b ofs::nil))
            (** install the thread's permissions on lock locations *)
            (Hrestrict_pmap0: restrPermMap (Hcompat tid0 cnt0).2 = m0)
            (** To release the lock the thread must have [Readable] permission on it*)
            (Haccess: Mem.range_perm m0 b (Ptrofs.intval ofs) ((Ptrofs.intval ofs) + LKSIZE) Cur Readable)
            (Hload: Mem.load Mptr m0 b (Ptrofs.intval ofs) = Some (Vptrofs Ptrofs.zero))
            (** set the permissions on the lock location equal to [Writable]*)
            (Hset_perm: setPermBlock (Some Writable)
                                     b (Ptrofs.intval ofs) ((getThreadR cnt0).2) LKSIZE_nat = pmap_tid')
            (Hlt': permMapLt pmap_tid' (getMaxPerm m))
            (Hrestrict_pmap: restrPermMap Hlt' = m1)
            (** release the lock *)
            (Hstore: Mem.store Mptr m1 b (Ptrofs.intval ofs) (Vptrofs Ptrofs.one) = Some m')
            (HisLock: lockRes tp (b, Ptrofs.intval ofs) = Some rmap)
            (Hrmap: forall b ofs, rmap.1 !!!! b ofs = None /\ rmap.2 !!!! b ofs = None)
            (Hangel1: permMapJoin newThreadPerm.1 virtueLP.1 (getThreadR cnt0).1)
            (Hangel2: permMapJoin newThreadPerm.2 virtueLP.2 (getThreadR cnt0).2)
            (Htp': tp' = updThread cnt0 (Kresume c Vundef)
                                   (computeMap (getThreadR cnt0).1 virtueThread.1,
                                    computeMap (getThreadR cnt0).2 virtueThread.2))
            (Htp'': tp'' = updLockSet tp' (b, Ptrofs.intval ofs) virtueLP),
            ext_step cnt0 Hcompat tp'' m'
                     (release (b, Ptrofs.intval ofs)
                              (Some (build_delta_content (fst virtueThread) m')))
    (* | step_create :
        forall (tp_upd tp':thread_pool) c marg b ofs arg virtue1 virtue2
          (Hbounded: if isCoarse then
                       ( sub_map virtue1.1 (getMaxPerm m).2 /\
                         sub_map virtue1.2 (getMaxPerm m).2)
                     else
                       True )
          (Hbounded_new: if isCoarse then
                           ( sub_map virtue2.1 (getMaxPerm m).2 /\
                             sub_map virtue2.2 (getMaxPerm m).2)
                         else
                           True ),
          let threadPerm' := (computeMap (getThreadR cnt0).1 virtue1.1,
                              computeMap (getThreadR cnt0).2 virtue1.2) in
          let newThreadPerm := (computeMap empty_map virtue2.1,
                                computeMap empty_map virtue2.2) in
          forall
            (Hinv : invariant tp)
            (Hcode: getThreadC cnt0 = Kblocked c)
            (* To check if the machine is at an external step and load its arguments install the thread data permissions*)
            (Hrestrict_pmap_arg: restrPermMap (Hcompat tid0 cnt0).1 = marg)
            (Hat_external: memory_semantics.at_external semSem c marg = Some (CREATE, Vptr b ofs::arg::nil))
(*            (Harg: Val.inject (Mem.flat_inj (Mem.nextblock m)) arg arg) *)
            (** we do not need to enforce the almost empty predicate on thread
           spawn as long as it's considered a synchronizing operation *)
            (Hangel1: permMapJoin newThreadPerm.1 threadPerm'.1 (getThreadR cnt0).1)
            (Hangel2: permMapJoin newThreadPerm.2 threadPerm'.2 (getThreadR cnt0).2)
            (Htp_upd: tp_upd = updThread cnt0 (Kresume c Vundef) threadPerm')
            (Htp': tp' = addThread tp_upd (Vptr b ofs) arg newThreadPerm),
            ext_step cnt0 Hcompat tp' m
                     (spawn (b, Ptrofs.intval ofs)
                            (Some (build_delta_content (fst virtue1) m))
                            (Some (build_delta_content (fst virtue2) m))) *)


    | step_mklock :
        forall  (tp' tp'': thread_pool) marg m1 c m' b ofs pmap_tid',
          let: pmap_tid := getThreadR cnt0 in
          forall
            (Hinv : invariant tp)
            (Hcode: getThreadC cnt0 = Kblocked c)
            (* To check if the machine is at an external step and load its arguments install the thread data permissions*)
            (Hrestrict_pmap_arg: restrPermMap (Hcompat tid0 cnt0).1 = marg)
            (Hat_external: memory_semantics.at_external semSem c marg = Some (MKLOCK, Vptr b ofs::nil))
            (** install the thread's data permissions*)
            (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).1 = m1)
            (** To create the lock the thread must have [Writable] permission on it*)
            (Hfreeable: Mem.range_perm m1 b (Ptrofs.intval ofs) ((Ptrofs.intval ofs) + LKSIZE) Cur Writable)
            (** lock is created in acquired state*)
            (Hstore: Mem.store Mptr m1 b (Ptrofs.intval ofs) (Vptrofs Ptrofs.zero) = Some m')
            (** The thread's data permissions are set to Nonempty*)
            (Hdata_perm: setPermBlock
                           (Some Nonempty)
                           b
                           (Ptrofs.intval ofs)
                           pmap_tid.1
                           LKSIZE_nat = pmap_tid'.1)
            (** thread lock permission is increased *)
            (Hlock_perm: setPermBlock
                           (Some Writable)
                           b
                           (Ptrofs.intval ofs)
                           pmap_tid.2
                           LKSIZE_nat = pmap_tid'.2)
            (** Require that [(b, Ptrofs.intval ofs)] was not a lock*)
            (HlockRes: lockRes tp (b, Ptrofs.intval ofs) = None)
            (Htp': tp' = updThread cnt0 (Kresume c Vundef) pmap_tid')
            (** the lock has no resources initially *)
            (Htp'': tp'' = updLockSet tp' (b, Ptrofs.intval ofs) (empty_map, empty_map)),
            ext_step cnt0 Hcompat tp'' m' (mklock (b, Ptrofs.intval ofs))

    | step_freelock :
        forall  (tp' tp'': thread_pool) c marg b ofs pmap_tid' m1 pdata rmap
           (Hbounded: if isCoarse then
                        ( bounded_maps.bounded_nat_func' pdata LKSIZE_nat)
                      else
                        True ),
          let: pmap_tid := getThreadR cnt0 in
          forall
            (Hinv: invariant tp)
            (Hcode: getThreadC cnt0 = Kblocked c)
            (* To check if the machine is at an external step and load its arguments install the thread data permissions*)
            (Hrestrict_pmap_arg: restrPermMap (Hcompat tid0 cnt0).1 = marg)
            (Hat_external: memory_semantics.at_external semSem c marg = Some (FREE_LOCK, Vptr b ofs::nil))
            (** If this address is a lock*)
            (His_lock: lockRes tp (b, (Ptrofs.intval ofs)) = Some rmap)
            (** And the lock is taken *)
            (Hrmap: forall b ofs, rmap.1 !!!! b ofs = None /\ rmap.2 !!!! b ofs = None)
            (** Install the thread's lock permissions*)
            (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).2 = m1)
            (** To free the lock the thread must have at least Writable on it*)
            (Hfreeable: Mem.range_perm m1 b (Ptrofs.intval ofs) ((Ptrofs.intval ofs) + LKSIZE) Cur Writable)
            (** lock permissions of the thread are dropped to empty *)
            (Hlock_perm: setPermBlock
                           None
                           b
                           (Ptrofs.intval ofs)
                           pmap_tid.2
                           LKSIZE_nat = pmap_tid'.2)
            (** data permissions are computed in a non-deterministic way *)
            (Hneq_perms: forall i,
                (0 <= Z.of_nat i < LKSIZE)%Z ->
                Mem.perm_order'' (pdata (S i)) (Some Writable)
            )
            (*Hpdata: perm_order pdata Writable*)
            (Hdata_perm: setPermBlock_var (*=setPermBlockfunc*)
                           pdata
                           b
                           (Ptrofs.intval ofs)
                           pmap_tid.1
                           LKSIZE_nat = pmap_tid'.1)
            (Htp': tp' = updThread cnt0 (Kresume c Vundef) pmap_tid')
            (Htp'': tp'' = remLockSet tp' (b, Ptrofs.intval ofs)),
            ext_step cnt0 Hcompat  tp'' m (freelock (b, Ptrofs.intval ofs))
    | step_acqfail :
        forall  c b ofs marg m1
           (Hinv : invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (* To check if the machine is at an external step and load its arguments install the thread data permissions*)
           (Hrestrict_pmap_arg: restrPermMap (Hcompat tid0 cnt0).1 = marg)
           (Hat_external: memory_semantics.at_external semSem c marg = Some (LOCK, Vptr b ofs::nil))
           (** Install the thread's lock permissions*)
           (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).2 = m1)
           (** To acquire the lock the thread must have [Readable] permission on it*)
           (Haccess: Mem.range_perm m1 b (Ptrofs.intval ofs) ((Ptrofs.intval ofs) + LKSIZE) Cur Readable)
           (** Lock is already acquired.*)
           (Hload: Mem.load Mptr m1 b (Ptrofs.intval ofs) = Some (Vptrofs Ptrofs.zero)),
          ext_step cnt0 Hcompat tp m (failacq (b, Ptrofs.intval ofs)).

    Definition syncStep (isCoarse:bool) :
      forall {tid0 ms m},
        containsThread ms tid0 -> mem_compatible ms m ->
        thread_pool -> mem -> sync_event -> Prop:=
      @ext_step isCoarse.

    Lemma syncstep_equal_run:
      forall b i tp m cnt cmpt tp' m' tr,
        @syncStep b i tp m cnt cmpt tp' m' tr ->
        forall j,
          (exists cntj q, @getThreadC _ _ _ j tp cntj = Krun q) <->
          (exists cntj' q', @getThreadC _ _ _ j tp' cntj' = Krun q').
    Proof.
      intros b i tp m cnt cmpt tp' m' tr H j; split.
      - intros [cntj [ q running]].
        destruct (NatTID.eq_tid_dec i j).
        + subst j. generalize running; clear running.
          inversion H; subst;
            match goal with
            | [ H: getThreadC ?cnt = Kblocked ?c |- _ ] =>
              replace cnt with cntj in H by apply cnt_irr;
                intros HH; rewrite HH in H; inversion H
            end.
        + (*this should be easy to automate or shorten*)
          inversion H; subst.
          * exists (cntUpdateL _ _
                          (cntUpdate (Kresume c Vundef) _
                                     _ cntj)), q.
            rewrite gLockSetCode.
            apply cntUpdate;
              now auto.
            intros.
            rewrite gsoThreadCode; assumption.
          * exists ( (cntUpdateL _ _
                            (cntUpdate (Kresume c Vundef) _ _ cntj))), q.
            rewrite gLockSetCode.
            apply cntUpdate;
              now auto.
            intros.
            rewrite gsoThreadCode; assumption.
          (* * exists (cntAdd _ _ _
                      (cntUpdate (Kresume c Vundef) _ _ cntj)), q.
            erewrite gsoAddCode .
            rewrite gsoThreadCode; assumption. *)
          * exists ( (cntUpdateL _ _
                            (cntUpdate (Kresume c Vundef) _ _ cntj))), q.
            rewrite gLockSetCode.
            apply cntUpdate;
              now auto.
            intros.
            rewrite gsoThreadCode; assumption.
          * exists ( (cntRemoveL _
                            (cntUpdate (Kresume c Vundef) _ _ cntj))), q.
            rewrite gRemLockSetCode.
            apply cntUpdate;
              now auto.
            intros.
            rewrite gsoThreadCode; assumption.
          * exists cntj, q; assumption.
      - intros [cntj [ q running]].
        destruct (NatTID.eq_tid_dec i j).
        + subst j. generalize running; clear running;
          inversion H; subst; intros;
            try (exfalso;
                 erewrite gLockSetCode with (cnti := cntUpdateL' _ _ cntj) in running;
                 rewrite gssThreadCode in running;
                 discriminate).
          
          { (*remove lock*)
            pose proof (cntUpdate' _ _ cnt (cntRemoveL' _ cntj)) as cnti.
            erewrite  gRemLockSetCode with (cnti := cntRemoveL' _ cntj) in running.
            rewrite gssThreadCode in running.
            discriminate. }
          { (*acquire lock*)
            do 2 eexists; eauto.
          }           
        + generalize running; clear running.
          inversion H; subst;
          intros.
          - exists (cntUpdate' _ _ cnt (cntUpdateL' _ _ cntj)), q.
            rewrite <- running.
            rewrite gLockSetCode.
            eapply cntUpdateL'; eauto.
            intros.
            rewrite gsoThreadCode; eauto.
            eapply cntUpdate'; eapply cntUpdateL'; eauto.
            intros.
            erewrite cnt_irr with (cnt1 := Hyp1).
            reflexivity.
          - exists (cntUpdate' _ _ cnt (cntUpdateL' _ _ cntj)), q.
            rewrite <- running.
            rewrite gLockSetCode.
            eapply cntUpdateL'; eauto.
            intros.
            rewrite gsoThreadCode; eauto.
            eapply cntUpdate'; eapply cntUpdateL'; eauto.
            intros.
            erewrite cnt_irr with (cnt1 := Hyp1).
            reflexivity.
          - exists (cntUpdate' _ _ cnt (cntUpdateL' _ _ cntj)), q.
            rewrite <- running.
            rewrite gLockSetCode.
            eapply cntUpdateL'; eauto.
            intros.
            rewrite gsoThreadCode; eauto.
            eapply cntUpdate'; eapply cntUpdateL'; eauto.
            intros.
            erewrite cnt_irr with (cnt1 := Hyp1).
            reflexivity.
          -  exists (cntUpdate' _ _ cnt (cntRemoveL' _ cntj)), q.
             rewrite <- running.
             rewrite gRemLockSetCode.
             eapply cntRemoveL'; eauto.
             intros.
             rewrite gsoThreadCode; eauto.
             eapply cntUpdate'; eapply cntRemoveL'; eauto.
             intros.
             erewrite cnt_irr with (cnt1 := Hyp1).
             reflexivity.
          - do 2 eexists;
              now eauto.
    Qed.

    Lemma syncstep_not_running:
      forall b i tp m cnt cmpt tp' m' tr,
        @syncStep b i tp m cnt cmpt tp' m' tr ->
        forall cntj q, ~ @getThreadC _ _ _ i tp cntj = Krun q.
    Proof.
      intros.
      inversion H;
        match goal with
        | [ H: getThreadC ?cnt = _ |- _ ] =>
          erewrite (cnt_irr _ _ _ cnt);
            rewrite H; intros AA; inversion AA
        end.
    Qed.

    Definition initial_machine pmap c := mkPool (Krun c) (pmap, empty_map) (* (empty_map, empty_map) *).

    Definition init_mach (pmap : option res) (m: mem)
               (ms:thread_pool) (m' : mem) (v:val) (args:list val) : Prop :=
      exists c, initial_core semSem 0 m c m' v args /\
           ms = mkPool (Krun c) (getCurPerm m', empty_map) (* (empty_map, empty_map) *).

    Definition install_perm tp m tid (Hcmpt: mem_compatible tp m) (Hcnt: containsThread tp tid) m' :=
      m' = restrPermMap (Hcmpt tid Hcnt).1.

    Definition add_block tp m tid (Hcmpt: mem_compatible tp m) (Hcnt: containsThread tp tid) m' :=
      (getCurPerm m', (getThreadR Hcnt).2).

    (** The signature of a Dry HybridMachine *)
    (** This can be used to instantiate a Dry CoarseHybridMachine or a Dry
    FineHybridMachine *)
    
    Instance DryHybridMachineSig: @HybridMachineSig.MachineSig dryResources Sem tpool :=
      (@HybridMachineSig.Build_MachineSig dryResources Sem tpool
                             richMem
                             dryMem
                             mem_compatible
                             invariant
                             install_perm
                             add_block
                             (@threadStep)
                             threadStep_at_Krun
                             threadStep_equal_run
                             (@syncStep)
                             (@pragmaStep)
                             syncstep_equal_run
                             syncstep_not_running
                             init_mach
      ).

    
    Definition Ostate : Type := (@HybridMachineSig.MachState dryResources Sem tpool * mem).

    Definition Ostep (os os': Ostate) := @HybridMachineSig.MachStep _ _ _ HybridMachineSig.HybridCoarseMachine.DilMem DryHybridMachineSig
                                          HybridMachineSig.HybridCoarseMachine.scheduler os.1 os.2 os'.1 os'.2.
    Definition Ostep_refl_trans_closure := @clos_refl_trans_1n Ostate Ostep.

  End DryHybridMachine.
  
  Section HybDryMachineLemmas.

    (* Lemmas that don't need semantics/threadpool*)
    
      Lemma build_delta_content_restr: forall d m p Hlt,
        build_delta_content d (@restrPermMap p m Hlt) = build_delta_content d m.
      Proof.
        reflexivity.
      Qed.

      (** Assume some threadwise semantics *)
        Context {ge:genv}.
        (** Assume some threadwise semantics *)
        Context {tpool : @ThreadPool.ThreadPool dryResources (@Sem ge)}.
    
      
      (*TODO: This lemma should probably be moved. *)
      Lemma threads_canonical:
        forall ds m i (cnt:containsThread ds i),
          mem_compatible ds m ->
          isCanonical (getThreadR cnt).1 /\
          isCanonical (getThreadR cnt).2.
        intros.
        destruct (compat_th _ _ H cnt);
          eauto using canonical_lt.
      Qed.
      (** most of these lemmas are in DryMachinLemmas*)

      (** *Invariant Lemmas*)

      (** ** Updating the machine state**)
      (* Many invariant lemmas were removed from here. *)


    Notation thread_perms st i cnt:= (fst (@getThreadR _ (@Sem ge) _ st i cnt)).
    Notation lock_perms st i cnt:= (snd (@getThreadR  _ (@Sem ge) _ st i cnt)).
    Record thread_compat st i
           (cnt:containsThread st i) m:=
      { th_comp: permMapLt (thread_perms _ _ cnt) (getMaxPerm m);
        lock_comp: permMapLt (lock_perms _ _ cnt) (getMaxPerm m)}.
    #[export] Instance thread_compat_proper st i:
        Proper (Logic.eq ==> Max_equiv ==> iff) (@thread_compat st i).
      Proof.
        intros ?? <- ???.
        split; intros [H0 H1]; constructor;
          try (eapply permMapLt_equiv; last apply H0; done);
          try (eapply permMapLt_equiv; last apply H1; done).
      Qed.
    Lemma mem_compatible_thread_compat:
      forall (st1 : ThreadPool.t) (m1 : mem) (tid : nat)
        (cnt1 : containsThread st1 tid),
        mem_compatible st1 m1 -> thread_compat _ _ cnt1 m1.
    Proof. intros * H; constructor; apply H. Qed.
    Lemma mem_compat_Max:
        forall Sem Tp st m m',
          Max_equiv m m' ->
          Mem.nextblock m = Mem.nextblock m' ->
          @mem_compatible Sem Tp st m ->
          @mem_compatible Sem Tp st m'.
      Proof.
        intros * Hmax Hnb H.
        assert (Hmax':access_map_equiv (getMaxPerm m) (getMaxPerm m'))
          by eapply Hmax.
        constructor; intros;
          repeat rewrite <- Hmax';
          try eapply H; eauto.
        unfold Mem.valid_block; rewrite <- Hnb;
          eapply H; eauto.
      Qed.

  End HybDryMachineLemmas.
    
End DryHybridMachine.

Export DryHybridMachine.
