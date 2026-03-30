(* adapted from concurrency/common/threadPool.v *)
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.

Require Import Lia.
Require Import compcert.common.Memory.
Require Import compcert.common.Values. (*for val*)
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.openmp_sem.permissions.
Require Import VST.concurrency.openmp_sem.semantics.
Require Import VST.concurrency.common.pos.
Require Import VST.concurrency.common.threads_lemmas.
Require Import compcert.lib.Axioms.
Require Import VST.concurrency.openmp_sem.addressFiniteMap.

(* Require Import compcert.lib.Maps. *)
Require Import Coq.ZArith.ZArith.
Require Import VST.msl.Coqlib2.

Require Import VST.concurrency.common.lksize.

Import Address.

Set Implicit Arguments.
Require Import List. Import List.ListNotations.

Require Import VST.concurrency.openmp_sem.notations stdpp.base stdpp.vector stdpp.fin.
Notation block := Values.block.

Inductive ctl {cT:Type} : Type :=
| Krun : cT -> ctl
| Kblocked : cT -> ctl
| Kresume : cT -> val -> ctl (* Carries the return value. Probably a unit.*)
| Kinit : val -> val -> ctl. (* vals correspond to vf and arg respectively. *)

Definition EqDec: Type -> Type :=
  fun A : Type => forall a a' : A, {a = a'} + {a <> a'}.

(* Nth_error for lists*)
(** * Definition of threadpool*)

Module ThreadPool.
  Section ThreadPool.

    Context {resources: Resources}.
    Context {Sem: Semantics}.
    
    Local Notation ctl := (@ctl semC).

    Notation tid:= nat.

    (* !! TODO: remove extraRes? remove lockGuts, lockSet? *)
    Class ThreadPool :=
      { t : Type;
        mkPool : ctl -> res -> (*res ->*) t;
        containsThread : t -> tid -> Prop;
        getThreadC : forall {tid tp}, containsThread tp tid -> ctl;
        getThreadR : forall {tid tp}, containsThread tp tid -> res;
        (* resourceList : t -> list res; *)
        lockGuts : t -> AMap.t lock_info;  (* Gets the set of locks + their info    *)
        lockSet : t -> access_map;         (* Gets the permissions for the lock set *)
        lockRes : t -> address -> option lock_info;
(*         extraRes : t -> res; (* extra resources not held by any thread or lock *) *)
        (* addThread : t -> val -> val -> res -> t; *)
        addThread : t -> semC -> res -> t;
        addThreads : t -> semC -> list res -> list nat (* new threads' tids *) * t;
        updThreadC : forall {tid tp}, containsThread tp tid -> ctl -> t;
        updThreadR : forall {tid tp}, containsThread tp tid -> res -> t;
        updThread : forall {tid tp}, containsThread tp tid -> ctl -> res -> t;
        updLockSet : t -> address -> lock_info -> t;
        remLockSet : t -> address -> t;
(*         updExtraRes : t -> res -> t; *)
        latestThread : t -> tid;
        lr_valid : (address -> option lock_info) -> Prop;
        (*Find the first thread i that satisfies (filter i) *)
        (* find_thread_: t -> (ctl -> bool) -> option tid
        ; resourceList_spec: forall i tp
            (cnti: containsThread tp i),
            List.nth_error (resourceList tp) i = Some (getThreadR cnti)          
        ;   *)
        containsThread_dec:
             forall i tp, {containsThread tp i} + { ~ containsThread tp i}
        ; maybeContainsThread tp tid : option (containsThread tp tid) 
        (*Proof Irrelevance of contains*)
        ;  cnt_irr: forall t tid
                      (cnt1 cnt2: containsThread t tid),
            cnt1 = cnt2

        (* Add Thread properties*)
        ;  cntAdd:
             forall {j tp} c p,
               containsThread tp j ->
               containsThread (addThread tp c p) j

        ;  cntAddLatest:
             forall {tp} c p,
               containsThread (addThread tp c p) (latestThread tp)

        ;  cntAdd':
             forall {j tp} c p,
               containsThread (addThread tp c p) j ->
               (containsThread tp j /\ j <> latestThread tp) \/ j = latestThread tp

        (* Update properties*)
        ;  cntUpdateC:
             forall {tid tid0 tp} c
               (cnt: containsThread tp tid),
               containsThread tp tid0->
               containsThread (updThreadC cnt c) tid0
        ;  cntUpdateC':
             forall {tid tid0 tp} c
               (cnt: containsThread tp tid),
               containsThread (updThreadC cnt c) tid0 ->
               containsThread tp tid0

        ;  cntUpdateR:
             forall {i j tp} r
               (cnti: containsThread tp i),
               containsThread tp j->
               containsThread (updThreadR cnti r) j
        ;  cntUpdateR':
             forall {i j tp} r
               (cnti: containsThread tp i),
               containsThread (updThreadR cnti r) j ->
               containsThread tp j

        ;  cntUpdate:
             forall {i j tp} c p
               (cnti: containsThread tp i),
               containsThread tp j ->
               containsThread (updThread cnti c p) j
        ;  cntUpdate':
             forall {i j tp} c p
               (cnti: containsThread tp i),
               containsThread (updThread cnti c p) j ->
               containsThread tp j

        ;  cntUpdateL:
             forall {j tp} add lf,
               containsThread tp j ->
               containsThread (updLockSet tp add lf) j
        ;  cntRemoveL:
             forall {j tp} add,
               containsThread tp j ->
               containsThread (remLockSet tp add) j

        ;  cntUpdateL':
             forall {j tp} add lf,
               containsThread (updLockSet tp add lf) j ->
               containsThread tp j
        ;  cntRemoveL':
             forall {j tp} add,
               containsThread (remLockSet tp add) j ->
               containsThread tp j
(*         ;  cntUpdateExtra:
             forall {j tp} res,
               containsThread tp j ->
               containsThread (updExtraRes tp res) j *)

        (*;  gssLockPool:
    forall tp ls,
      lockSet (updLockSet tp ls) = ls*) (*Will change*)

        ;  gsoThreadLock:
             forall {i tp} c p (cnti: containsThread tp i),
               lockSet (updThread cnti c p) = lockSet tp

        ;  gsoThreadCLock :
             forall {i tp} c (cnti: containsThread tp i),
               lockSet (updThreadC cnti c) = lockSet tp

        ;  gsoThreadRLock :
             forall {i tp} p (cnti: containsThread tp i),
               lockSet (updThreadR cnti p) = lockSet tp

        ;  gsoAddLock :
             forall tp c p,
               lockSet (addThread tp c p) = lockSet tp

        ;  gssAddRes :
             forall {tp} c pmap j
               (Heq: j = latestThread tp)
               (cnt': containsThread (addThread tp c pmap) j),
               getThreadR cnt' = pmap

        (*Get thread Properties*)
        ;  gssThreadCode :
             forall {tid tp} (cnt: containsThread tp tid) c' p'
               (cnt': containsThread (updThread cnt c' p') tid),
               getThreadC cnt' = c'

        ;  gsoThreadCode :
             forall {i j tp} (Hneq: i <> j) (cnti: containsThread tp i)
               (cntj: containsThread tp j) c' p'
               (cntj': containsThread (updThread cnti c' p') j),
               getThreadC cntj' = getThreadC cntj

        ;  gssThreadRes :
             forall {tid tp} (cnt: containsThread tp tid) c' p'
               (cnt': containsThread (updThread cnt c' p') tid),
               getThreadR cnt' = p'

        ;  gsoThreadRes :
             forall {i j tp} (cnti: containsThread tp i)
               (cntj: containsThread tp j) (Hneq: i <> j) c' p'
               (cntj': containsThread (updThread cnti c' p') j),
               getThreadR cntj' = getThreadR cntj

        ;  gssThreadCC :
             forall {tid tp} (cnt: containsThread tp tid) c'
               (cnt': containsThread (updThreadC cnt c') tid),
               getThreadC cnt' = c'

        ;  gsoThreadCC :
             forall {i j tp} (Hneq: i <> j) (cnti: containsThread tp i)
               (cntj: containsThread tp j) c'
               (cntj': containsThread (updThreadC cnti c') j),
               getThreadC cntj = getThreadC cntj'

        ;  getThreadCC :
             forall {tp} i j
               (cnti : containsThread tp i) (cntj : containsThread tp j)
               c' (cntj' : containsThread (updThreadC cnti c') j),
               getThreadC cntj' = if Nat.eq_dec i j then c' else getThreadC cntj

        ;  gssThreadRR :
             forall {tid tp} (cnt: containsThread tp tid) p'
               (cnt': containsThread (updThreadR cnt p') tid),
               getThreadR cnt' = p'

        ;  gsoThreadRR :
             forall {i j tp} (Hneq: i <> j) (cnti: containsThread tp i)
               (cntj: containsThread tp j) p'
               (cntj': containsThread (updThreadR cnti p') j),
               getThreadR cntj = getThreadR cntj'

        ;  gThreadCR :
             forall {i j tp} (cnti: containsThread tp i)
               (cntj: containsThread tp j) c'
               (cntj': containsThread (updThreadC cnti c') j),
               getThreadR cntj' = getThreadR cntj

        ;  gThreadRC :
             forall {i j tp} (cnti: containsThread tp i)
               (cntj: containsThread tp j) p
               (cntj': containsThread (updThreadR cnti p) j),
               getThreadC cntj' = getThreadC cntj

        ;  gsoThreadCLPool :
             forall {i tp} c (cnti: containsThread tp i) addr,
               lockRes (updThreadC cnti c) addr = lockRes tp addr

        ;  gsoThreadLPool :
             forall {i tp} c p (cnti: containsThread tp i) addr,
               lockRes (updThread cnti c p) addr = lockRes tp addr

        ;  gsoAddLPool :
             forall tp c p (addr : address),
               lockRes (addThread tp c p) addr = lockRes tp addr

        ;  gLockSetRes :
             forall {i tp} addr (res : lock_info) (cnti: containsThread tp i)
               (cnti': containsThread (updLockSet tp addr res) i),
               getThreadR cnti' = getThreadR cnti

        ;  gLockSetCode :
             forall {i tp} addr (res : lock_info) (cnti: containsThread tp i)
               (cnti': containsThread (updLockSet tp addr res) i),
               getThreadC cnti' = getThreadC cnti

        ;  gssLockRes :
             forall tp addr pmap,
               lockRes (updLockSet tp addr pmap) addr = Some pmap

        ;  gsoLockRes:
             forall tp addr addr' pmap
               (Hneq: addr <> addr'),
               lockRes (updLockSet tp addr pmap) addr' =
               lockRes tp addr'

        ;  gssLockSet :
             forall tp b ofs rmap ofs',
               (ofs <= ofs' < ofs + Z.of_nat lksize.LKSIZE_nat)%Z ->
               (Maps.PMap.get b (lockSet (updLockSet tp (b, ofs) rmap)) ofs') = Some Writable

        ;  gsoLockSet_1 :
             forall tp b ofs ofs'  pmap
               (Hofs: (ofs' < ofs)%Z \/ (ofs' >= ofs + (Z.of_nat lksize.LKSIZE_nat))%Z),
               (Maps.PMap.get b (lockSet (updLockSet tp (b,ofs) pmap))) ofs' =
               (Maps.PMap.get b (lockSet tp)) ofs'
        ;  gsoLockSet_2 :
             forall tp b b' ofs ofs' pmap,
               b <> b' ->
               (Maps.PMap.get b' (lockSet (updLockSet tp (b,ofs) pmap))) ofs' =
               (Maps.PMap.get b' (lockSet tp)) ofs'

        ;  lockSet__updLockSet:
             forall tp i (pf: containsThread tp i) c pmap addr rmap,
               lockSet (updLockSet tp addr rmap) =
               lockSet (updLockSet (updThread pf c pmap) addr rmap)

        ;  updThread_updThreadC__comm :
             forall tp i j c pmap' c'
               (Hneq: i <> j)
               (cnti : containsThread tp i)
               (cntj : containsThread tp j)
               (cnti': containsThread (updThread cntj c' pmap') i)
               (cntj': containsThread (updThreadC cnti c) j),
               updThreadC cnti' c = updThread cntj' c' pmap'

        ;  updThread_comm :
             forall tp i j c pmap c' pmap'
               (Hneq: i <> j)
               (cnti : containsThread tp i)
               (cntj : containsThread tp j)
               (cnti': containsThread (updThread cntj c' pmap') i)
               (cntj': containsThread (updThread cnti c pmap) j),
               updThread cnti' c pmap = updThread cntj' c' pmap'

        ;  add_updateC_comm :
             forall tp i c pmap c'
               (cnti: containsThread tp i)
               (cnti': containsThread (addThread tp c pmap) i),
               addThread (updThreadC cnti c') c pmap =
               updThreadC cnti' c'

        ;  add_update_comm :
             forall tp i c pmap c' pmap'
               (cnti: containsThread tp i)
               (cnti': containsThread (addThread tp c pmap) i),
               addThread (updThread cnti c' pmap') c pmap =
               updThread cnti' c' pmap'

        ;  updThread_lr_valid :
             forall tp i (cnti: containsThread tp i) c' m',
               lr_valid (lockRes tp) ->
               lr_valid (lockRes (updThread cnti c' m'))

(*        (* extraRes properties *)

        ; gssExtraRes : forall tp res, extraRes (updExtraRes tp res) = res

        ; gsoAddExtra : forall tp vf arg p, extraRes (addThread tp vf arg p) = extraRes tp

        ; gsoThreadCExtra : forall {i tp} c (cnti: containsThread tp i), extraRes (updThreadC cnti c) = extraRes tp

        ; gsoThreadRExtra : forall {i tp} r (cnti: containsThread tp i), extraRes (updThreadR cnti r) = extraRes tp

        ; gsoThreadExtra : forall {i tp} c r (cnti: containsThread tp i), extraRes (updThread cnti c r) = extraRes tp

        ; gsoLockSetExtra : forall tp addr res, extraRes (updLockSet tp addr res) = extraRes tp

        ; gsoRemLockExtra : forall tp addr, extraRes (remLockSet tp addr) = extraRes tp

        ; gExtraResCode : forall {i tp} res (cnti: containsThread tp i)
               (cnti': containsThread (updExtraRes tp res) i),
               getThreadC cnti' = getThreadC cnti

        ; gExtraResRes : forall {i tp} res (cnti: containsThread tp i)
               (cnti': containsThread (updExtraRes tp res) i),
               getThreadR cnti' = getThreadR cnti

        ; gsoExtraLPool : forall tp res addr,
               lockRes (updExtraRes tp res) addr = lockRes tp addr

        ; gsoExtraLock : forall tp res,
               lockSet (updExtraRes tp res) = lockSet tp *)

        (*New axioms, to avoid breaking the modularity *)
        ; lockSet_spec_2 :
            forall (js : t) (b : block) (ofs ofs' : Z),
              Intv.In ofs' (ofs, (ofs + Z.of_nat lksize.LKSIZE_nat)%Z) ->
              lockRes js (b, ofs) -> (lockSet js) !!!! b ofs' = Some Memtype.Writable

        ;  lockSet_spec_3 :
             forall ds b ofs,
               (forall z, z <= ofs < z+LKSIZE -> lockRes ds (b,z) = None)%Z ->
               (lockSet ds) !!!! b ofs = None

        ;  gsslockSet_rem : forall ds b ofs ofs0,
            lr_valid (lockRes ds) ->
            Intv.In ofs0 (ofs, ofs + lksize.LKSIZE)%Z ->
            isSome ((lockRes ds) (b,ofs)) ->  (*New hypothesis needed. Shouldn't be a problem *)
            (lockSet (remLockSet ds (b, ofs))) !!!! b ofs0 =
            None

        ;  gsolockSet_rem1 : forall ds b ofs b' ofs',
            b  <> b' ->
            (lockSet (remLockSet ds (b, ofs))) !!!! b' ofs' =
            (lockSet ds)  !!!! b' ofs'

        ;  gsolockSet_rem2 : forall ds b ofs ofs',
            lr_valid (lockRes ds) ->
            ~ Intv.In ofs' (ofs, ofs + lksize.LKSIZE)%Z ->
            (lockSet (remLockSet ds (b, ofs))) !!!! b ofs' =
            (lockSet ds) !!!! b ofs'
        ;  gsslockResUpdLock: forall js a res,
            lockRes (updLockSet js a res) a =
            Some res
        ;  gsolockResUpdLock : forall js loc a res,
            loc <> a ->
            lockRes (updLockSet js loc res) a =
            lockRes js a

        ;  gsslockResRemLock : forall js a,
            lockRes (remLockSet js a) a =
            None
        ;  gsolockResRemLock : forall js loc a,
            loc <> a ->
            lockRes (remLockSet js loc) a =
            lockRes js a

        ;  gRemLockSetCode :
             forall {i tp} addr (cnti: containsThread tp i)
               (cnti': containsThread (remLockSet tp addr) i),
               getThreadC cnti' = getThreadC cnti

        ;  gRemLockSetRes :
             forall {i tp} addr (cnti: containsThread tp i)
               (cnti': containsThread (remLockSet tp addr) i),
               getThreadR cnti' = getThreadR cnti

        ;  gsoAddCode :
             forall {tp} c pmap j
               (cntj: containsThread tp j)
               (cntj': containsThread (addThread tp c pmap) j),
               getThreadC cntj' = getThreadC cntj

        ;  gssAddCode :
             forall {tp} c pmap j
               (Heq: j = latestThread tp)
               (cnt': containsThread (addThread tp c pmap) j),
               getThreadC cnt' = Kblocked c

        ;  gsoAddRes :
             forall {tp} c pmap j
               (cntj: containsThread tp j) (cntj': containsThread (addThread tp c pmap) j),
               getThreadR cntj' = getThreadR cntj

        ;  updLock_updThread_comm :
             forall ds,
             forall i (cnti: containsThread ds i) c map l lmap,
             forall (cnti': containsThread (updLockSet ds l lmap) i),
               updLockSet
                 (@updThread _ ds cnti c map) l lmap =
               @updThread  _ (updLockSet ds l lmap) cnti' c map

        ;  remLock_updThread_comm :
             forall ds,
             forall i (cnti: containsThread ds i) c map l,
             forall (cnti': containsThread (remLockSet ds l) i),
               remLockSet
                 (updThread cnti c map)
                 l =
               updThread cnti' c map
        ;  remLock_updThreadC_comm :
             forall ds,
             forall i (cnti: containsThread ds i) c l,
             forall (cnti': containsThread (remLockSet ds l) i),
               remLockSet (updThreadC cnti c) l = updThreadC cnti' c
      }.

  End ThreadPool.
End ThreadPool.

Module FinPool.

  Definition empty_lset {lock_info}:AMap.t lock_info:=
    AMap.empty lock_info.

  Lemma find_empty:
    forall a l,
      @AMap.find a l empty_lset = None.
    unfold empty_lset.
    unfold AMap.empty, AMap.find; reflexivity.
  Qed.

  
  Section FinThreadPool.

  
  Context {resources: Resources}.
    Context {Sem: Semantics}.
    
    Local Notation ctl := (@ctl semC).

    Notation tid:= nat.
    
    Record t := mk
                  { num_threads : nat
                    ; pool :> vec ctl num_threads
                    ; perm_maps : vec res num_threads
                    ; lset : AMap.t lock_info
(*                     ; extra : res *)
                  }.

    Arguments mk _ _ _ _ : clear implicits.

    Definition mkPool c res (* extra *) :=
      mk 1
        [#c]
        [#res]
        empty_lset (* initially there are no locks *)
        (* extra *). (* no obvious initial value for extra *)
    
    Definition lockGuts := lset.
    Definition lockSet (tp:t) := A2PMap (lset tp).

    Definition lockRes t : address -> option lock_info:=
      AMap.find (elt:=lock_info)^~ (lockGuts t).

(*     Definition extraRes := extra. *)

    Definition lr_valid (lr: address -> option lock_info):=
      forall b ofs,
        match lr (b,ofs) with
        | Some r => forall ofs0:Z, (ofs < ofs0 < ofs+LKSIZE)%Z -> lr (b, ofs0) = None
        | _ => True
        end.

    Lemma is_pos: forall n, (0 < S n)%coq_nat.
    Proof. move=> n; lia. Qed.
    Definition mk_pos_S (n:nat):= mkPos (is_pos n).
    Lemma lt_decr: forall n m: nat, S n < m -> n < m.
    Proof. intros. lia. Qed.

    Import Coqlib.

    Lemma lockSet_WorNE: forall js b ofs,
        (lockSet js) !!!! b ofs = Some Memtype.Writable \/
        (lockSet js) !!!! b ofs = None.
    Proof.
      intros. unfold lockSet.
      unfold A2PMap.
      rewrite <- List.fold_left_rev_right.
      match goal with |- context [List.fold_right ?F ?Z ?A] =>
                      set (f := F); set (z:=Z); induction A end.
      right. simpl. rewrite PMap.gi. auto.
      change (List.fold_right f z (a::l)) with (f a (List.fold_right f z l)).
      unfold f at 1 3.
      destruct a. destruct a.
      destruct (peq b0 b).
      - subst b0.
        pose proof permissions.setPermBlock_or (Some Memtype.Writable) b z0 LKSIZE_nat (fold_right f z l) b ofs as H.
        destruct H as [-> | ->]; auto.
      - rewrite permissions.setPermBlock_other_2; auto.
    Qed.

    Lemma lockSet_spec_2 :
      forall (js : t) (b : block) (ofs ofs' : Z),
        Intv.In ofs' (ofs, (ofs + Z.of_nat lksize.LKSIZE_nat)%Z) ->
        lockRes js (b, ofs) -> (lockSet js) !!!! b ofs' = Some Memtype.Writable.
    Proof.
      intros.
      hnf in H0.
      hnf in H. simpl in H.
      unfold lockSet. unfold A2PMap.
      rewrite <- List.fold_left_rev_right.
      unfold lockRes in H0. unfold lockGuts in H0.
      match type of H0 with isSome ?A = true=> destruct A eqn:?H; inv H0 end.
      apply AMap.find_2 in H1.
      apply AMap.elements_1 in H1.
      apply SetoidList.InA_rev in H1.
      unfold AMap.key in H1.
      forget (@rev (address * lock_info) (AMap.elements (elt:=lock_info) (lset js))) as el.
      match goal with |- context [List.fold_right ?F ?Z ?A] =>
                      set (f := F); set (z:=Z) end.
      revert H1; induction el; intros.
      inv H1.
      apply SetoidList.InA_cons in H1.
      destruct H1.
      hnf in H0. destruct a; simpl in H0. destruct H0; subst a l0.
      simpl. rewrite setPermBlock_lookup; if_tac; auto.
      contradiction H0; split; auto.
      apply IHel in H0; clear IHel.
      simpl.
      unfold f at 1. destruct a. destruct a.
      rewrite setPermBlock_lookup; if_tac; auto.
    Qed.

    Lemma lockSet_spec_1: forall js b ofs,
        lockRes js (b,ofs) ->
        (lockSet js) !!!! b ofs = Some Memtype.Writable.
    Proof.
      intros.
      eapply lockSet_spec_2; eauto.
      unfold Intv.In.
      simpl. pose proof LKSIZE_pos; rewrite Z2Nat.id; lia.
    Qed.

    Open Scope nat_scope.

    (* Definition containsThread_dec (tp : t) (i : NatTID.tid) : bool:=
  Compare.Pcompare i (num_threads tp). *)
    Definition containsThread (tp : t) (i : NatTID.tid) : Prop :=
      i < tp.(num_threads).

    #[export] Instance containsThread_dec:
      forall i tp, Decision (containsThread tp i).
    Proof.
      intros.
      unfold containsThread.
      apply _.
    Defined.

    Definition getThreadC {i} (tp:t) (cnt: containsThread tp i) : ctl :=
      tp.(pool) !!! (nat_to_fin cnt).

    Definition unique_Krun' tp i :=
      ( forall j cnti q,
          @getThreadC j tp cnti = Krun q ->
          eq_nat_dec i j ).

    Definition is_running tp i:=
      exists cnti q, @getThreadC i tp cnti = Krun q.

    Lemma unique_runing_not_running:
      forall tp i,
        unique_Krun' tp i ->
        ~ is_running tp i ->
        forall j, unique_Krun' tp j.
    Proof.
      unfold unique_Krun', is_running.
      intros.
      specialize (H  _ _ _ H1);
        destruct (eq_nat_dec i j0); inversion H; subst.

      exfalso; apply H0 .
      exists cnti, q; assumption.
    Qed.


    Definition getThreadR {i tp} (cnt: containsThread tp i) : res :=
      (perm_maps tp) !!! (nat_to_fin cnt).

    Definition latestThread tp := (num_threads tp).

    Definition addThread' (tp : t) (c : semC) (pmap : res) :=
      let: new_num_threads := (num_threads tp)+1 in
      let tp' := mk new_num_threads
         (pool tp +++ [#Kblocked c])
         (perm_maps tp +++ [#pmap])
         (lset tp) (* (extra tp) *) in
      (* (num_threads tp) is the pos version of the new tid *)
      ((num_threads tp), tp').

    Definition addThread (tp : t) (c : semC) (pmap : res) : t :=
      (addThread' tp c pmap).2.

    (* spawn threads, each has a different permission in pmaps, return the new tids and the new tp *)
    Definition addThreads (tp : t) (c : semC) (pmaps : list res) : list nat * t :=
      fold_right (fun perm_i x =>
        let tp := x.2 in
        let tids := x.1 in
        let (new_tid, tp') := addThread' tp c perm_i in
        (new_tid::tids, tp')) ([], tp) pmaps.

    Definition updLockSet tp (add:address) (lf:lock_info) : t :=
      mk (num_threads tp)
         (pool tp)
         (perm_maps tp)
         (AMap.add add lf (lockGuts tp))
         (* (extra tp) *).

    Definition remLockSet tp  (add:address) : t :=
      mk (num_threads tp)
         (pool tp)
         (perm_maps tp)
         (AMap.remove add (lockGuts tp))
         (* (extra tp) *).

    Definition updThreadC {tid tp} (cnt: containsThread tp tid) (c' : ctl) : t :=
      mk (num_threads tp)
         (vinsert (nat_to_fin cnt) c' tp )
         (perm_maps tp)
         (lset tp)
         (* (extra tp) *).

    Definition updThreadR {tid tp} (cnt: containsThread tp tid)
               (pmap' : res) : t :=
      mk (num_threads tp)
        (pool tp)
         (vinsert (nat_to_fin cnt) pmap' (perm_maps tp))
         (lset tp)
         (* (extra tp) *).

    Definition updThread {tid tp} (cnt: containsThread tp tid) (c' : ctl)
               (pmap : res) : t :=
      mk (num_threads tp)
         (vinsert (nat_to_fin cnt) c' tp )
         (vinsert (nat_to_fin cnt) pmap (perm_maps tp))
         (lset tp)
         (* (extra tp) *).

(*     Definition updExtraRes tp res : t :=
      mk (num_threads tp)
         (pool tp)
         (perm_maps tp)
         (lset tp)
         res. *)

    (*TODO: see if typeclasses can automate these proofs, probably not thanks dep types*)

        Lemma nat_to_fin_inj i j m cnti cntj: 
      @nat_to_fin i m cnti = @nat_to_fin j m cntj -> i = j.
    Proof.
      intros H.
      rewrite -(fin_to_nat_to_fin _ _ cnti) -(fin_to_nat_to_fin _ _ cntj) H //.
    Qed.

    (* Ltac nat_to_fin_eq_tac := 
      lazymatch goal with
      | |- nat_to_fin ?cnti = nat_to_fin ?cntj =>
        lazymatch type of cnti with
        | ?i < _ =>
          lazymatch type of cntj with
          | ?j < _ =>
            match goal with
            | Hneq : i ≠ j |- _ => contradict Hneq; by eapply nat_to_fin_inj
            | Hneq : j ≠ i |- _ => contradict Hneq; by eapply nat_to_fin_inj
            end
          end
        end
      end. *)

    Ltac nat_to_fin_neq_tac :=
      lazymatch goal with
      | |- nat_to_fin ?cnti ≠ nat_to_fin ?cntj =>
        lazymatch type of cnti with
        | ?i < _ =>
          lazymatch type of cntj with
          | ?j < _ =>
            match goal with
            | Hneq : i ≠ j |- _ => contradict Hneq; by eapply nat_to_fin_inj
            | Hneq : j ≠ i |- _ => contradict Hneq; by eapply nat_to_fin_inj
            end
          end
        end
      end.

    Ltac vlookup_insert_same_tac cnt cnt' :=
      (tryif unify cnt' cnt then idtac else 
      assert (nat_to_fin cnt = nat_to_fin cnt') as <- by (by rewrite (Fin.of_nat_ext cnt' cnt)));
      rewrite vlookup_insert //.
    
    Ltac vlookup_insert_neq_tac :=
      rewrite vlookup_insert_ne //; nat_to_fin_neq_tac.

    Ltac unfold_tp_defs :=
      unfold getThreadR, getThreadC, latestThread,
        updThread, updThreadC, containsThread, addThread in *; simpl in *.

    Ltac vlookup_insert_tac :=
      lazymatch goal with
      | |- context [vinsert (nat_to_fin ?cnt) _ _ !!! nat_to_fin ?cnt' ] =>
        first [vlookup_insert_same_tac cnt cnt'| 
               vlookup_insert_neq_tac] end.

    Ltac vlookup_lookup_eq_tac :=
      lazymatch goal with
      | |- ?tp !!! (nat_to_fin ?cnt) = ?tp !!! (nat_to_fin ?cnt') =>
        f_equal; by apply Fin.of_nat_ext end.

    Lemma vlookup_middle_2 {A: Type} {i j:nat}
    (v : vec A i) (w : vec A j) (x : A) (cnt : i < (i+j.+1)) :
    (v +++ x ::: w) !!! (nat_to_fin cnt) = x.
    Proof.
      rewrite vlookup_lookup.
      rewrite vec_to_list_app vec_to_list_cons.
      rewrite list_lookup_middle //.
      rewrite vec_to_list_length fin_to_nat_to_fin //.
    Qed.

    Ltac vlookup_middle_tac :=
      (* lookup in the middle of vec *)
      match goal with
      | |- context [(?v +++ ?x ::: ?w) !!! (nat_to_fin ?cnt)] =>
        match type of v with
        | vec _ ?i =>
          match type of cnt with
          | ?j < _ =>  unify i j; rewrite (vlookup_middle_2 v w x cnt)
          end
        end
      end.

    Lemma vlookup_app_l {A: Type} {k i j:nat}
      (v : vec A i) (w : vec A j) (cnt : k < (i+j)) (cnt' : k < i) :
        (v +++ w) !!! nat_to_fin cnt = v !!! nat_to_fin cnt'.
    Proof.
      rewrite vlookup_lookup.
      rewrite vec_to_list_app.
      rewrite lookup_app_l fin_to_nat_to_fin  //.
      - rewrite -vlookup_lookup'. eexists. done.
      - rewrite vec_to_list_length //.
    Qed.

    Ltac vlookup_app_l_tac :=
      rewrite vlookup_app_l.

    Lemma vinsert_app_l {A: Type} {k i j:nat}
      (v : vec A i) (w : vec A j) (x : A) (cnt : k < i+j) (cnt' : k < i) :
        vinsert (nat_to_fin cnt) x (v +++ w) =
        vinsert (nat_to_fin cnt') x v +++ w.
    Proof.
      apply vec_to_list_inj2.
      rewrite vec_to_list_app 2!vec_to_list_insert vec_to_list_app 2!fin_to_nat_to_fin.
      rewrite insert_app_l //.
      rewrite vec_to_list_length //.
    Qed.

    Ltac vinsert_app_l_tac := rewrite vinsert_app_l.

    Lemma vinsert_commute {A: Type} {k l i:nat}
      (v : vec A i) (x y: A) (cnt : k < i) (cnt' : l < i) (Hkl: k ≠ l) :
        vinsert (nat_to_fin cnt)  x $ vinsert (nat_to_fin cnt') y $ v =
        vinsert (nat_to_fin cnt') y $ vinsert (nat_to_fin cnt)  x $ v.
    Proof.
      apply vec_to_list_inj2.
      rewrite !vec_to_list_insert list_insert_commute //.
      rewrite !fin_to_nat_to_fin //.
    Qed.

    (* NOTE direction of the rewrite relies on the assumption (Hkl: k ≠ l) of vinsert_commute,
       i.e. can't have (k ≠ l) and (l ≠ k) at the same time *)
    Ltac vinsert_commute_tac :=
      match goal with
      | |- context[vinsert (nat_to_fin ?cnt) _ $ vinsert (nat_to_fin ?cnt') _ $ _] =>
        match type of cnt with
        | ?k < _ =>
          match type of cnt' with
          | ?l < _ =>
            (* triggers rewrite if 
               1. there is an explicit assumption k ≠ l
               2. k > l *)
            match goal with
            | _ : k ≠ l |- _ => rewrite (vinsert_commute(k:=k)(l:=l))
            | |- _ => let H := fresh in assert (H : k > l) by lia;
                      clear H;
                      rewrite (vinsert_commute(k:=k)(l:=l))
            end
          end
        end
      end.

    Lemma vinsert_insert {A: Type} {k i:nat}
      (v : vec A i) (x y: A) (cnt : k < i) :
        vinsert (nat_to_fin cnt)  x $ vinsert (nat_to_fin cnt) y $ v =
        vinsert (nat_to_fin cnt)  x $ v.
    Proof.
      apply vec_to_list_inj2.
      rewrite !vec_to_list_insert list_insert_insert //.
    Qed.


    (*Proof Irrelevance of contains*)
    Lemma cnt_irr: forall t tid
                     (cnt1 cnt2: containsThread t tid),
        cnt1 = cnt2.
    Proof. intros. apply proof_irr. Qed.

    Ltac normalize_cnt :=
      match goal with
      | cnt : ?i < ?n, cnt' : ?i' < ?n' |- _ =>
        unify i i'; unify n n';
        rewrite ?(Fin.of_nat_ext cnt' cnt);
        clear cnt'
      end.

    Ltac tp_tac :=
      intros;
      unfold_tp_defs;
      repeat first [
         done
        | normalize_cnt
        | rewrite vlookup_insert_self
        | rewrite vinsert_insert
        | vlookup_insert_tac
        | vlookup_lookup_eq_tac
        | vlookup_middle_tac
        | vlookup_app_l_tac
        | vinsert_app_l_tac
        | vinsert_commute_tac
        | lia
      ].

    (* Update properties*)
    Lemma numUpdateC :
      forall {tid tp} (cnt: containsThread tp tid) c,
        num_threads tp =  num_threads (updThreadC cnt c).
    Proof. tp_tac. Qed.

    Lemma cntUpdateC :
      forall {tid tid0 tp} c
        (cnt: containsThread tp tid),
        containsThread tp tid0 ->
        containsThread (updThreadC cnt c) tid0.
    Proof. tp_tac. Qed.

    Lemma cntUpdateC':
      forall {tid tid0 tp} c
        (cnt: containsThread tp tid),
        containsThread (updThreadC cnt c) tid0 ->
        containsThread tp tid0.
    Proof. tp_tac. Qed.

    Lemma cntUpdateR:
      forall {i j tp} r
        (cnti: containsThread tp i),
        containsThread tp j->
        containsThread (updThreadR cnti r) j.
    Proof. tp_tac. Qed.

    Lemma cntUpdateR':
      forall {i j tp} r
        (cnti: containsThread tp i),
        containsThread (updThreadR cnti r) j ->
        containsThread tp j.
    Proof. tp_tac. Qed.

    Lemma cntUpdate :
      forall {i j tp} c p
        (cnti: containsThread tp i),
        containsThread tp j ->
        containsThread (updThread cnti c p) j.
    Proof. tp_tac. Qed.

    Lemma cntUpdate':
      forall {i j tp} c p
        (cnti: containsThread tp i),
        containsThread (updThread cnti c p) j ->
        containsThread tp j.
    Proof. tp_tac. Qed.

    Lemma cntUpdateL:
      forall {j tp} add lf,
        containsThread tp j ->
        containsThread (updLockSet tp add lf) j.
    Proof. tp_tac. Qed.

    Lemma cntRemoveL:
      forall {j tp} add,
        containsThread tp j ->
        containsThread (remLockSet tp add) j.
    Proof. tp_tac. Qed.

    Lemma cntUpdateL':
      forall {j tp} add lf,
        containsThread (updLockSet tp add lf) j ->
        containsThread tp j.
    Proof. tp_tac. Qed.

    Lemma cntRemoveL':
      forall {j tp} add,
        containsThread (remLockSet tp add) j ->
        containsThread tp j.
    Proof. tp_tac. Qed.

(*     Lemma cntUpdateExtra:
             forall {j tp} res,
               containsThread tp j ->
               containsThread (updExtraRes tp res) j.
    Proof.
      intros. unfold containsThread in *; simpl in *; by assumption.
    Qed. *)

    Lemma cntAdd:
      forall {j tp} c p,
        containsThread tp j ->
        containsThread (addThread tp c p) j.
    Proof. tp_tac. Qed.

    Lemma cntAddLatest:
      forall {tp} c p,
        containsThread (addThread tp c p) (latestThread tp).
    Proof. tp_tac. Qed.

    Lemma cntAdd':
      forall {j tp} c p,
        containsThread (addThread tp c p) j ->
        (containsThread tp j /\ j <> num_threads tp) \/ j = num_threads tp.
    Proof. tp_tac. Qed.

    Lemma contains_add_latest: forall ds c r,
        containsThread (addThread ds c r)
                       (latestThread ds).
    Proof. tp_tac. Qed.

    Lemma updLock_updThread_comm:
      forall ds,
      forall i (cnti: containsThread ds i) c map l lmap,
      forall (cnti': containsThread (updLockSet ds l lmap) i),
        updLockSet
          (@updThread _ ds cnti c map) l lmap =
        @updThread _ (updLockSet ds l lmap) cnti' c map.
    Proof. unfold updLockSet, updThread; simpl; intros.
      rewrite Fin.of_nat_ext //.
    Qed.

    Lemma remLock_updThread_comm:
      forall ds,
      forall i (cnti: containsThread ds i) c map l,
      forall (cnti': containsThread (remLockSet ds l) i),
        remLockSet
          (updThread cnti c map)
          l =
        updThread cnti' c map.
    Proof.
      unfold remLockSet, updThread; simpl; intros.
      rewrite Fin.of_nat_ext //.
    Qed.

    Lemma remLock_updThreadC_comm :
      forall ds i (cnti: containsThread ds i) c l
        (cnti': containsThread (remLockSet ds l) i),
        remLockSet (updThreadC cnti c) l = updThreadC cnti' c.
    Proof.
      unfold remLockSet, updThreadC; simpl; intros.
      rewrite Fin.of_nat_ext //.
    Qed.

    (* TODO: most of these proofs are similar, automate them*)
    (** Getters and Setters Properties*)

    Lemma gsslockResUpdLock: forall js a res,
        lockRes (updLockSet js a res) a =
        Some res.
    Proof.
      intros.
      unfold lockRes, updLockSet. simpl.
      unfold AMap.find; simpl.
      forget (AMap.this (lockGuts js)) as el.
      unfold AMap.find; simpl.
      induction el.
      * simpl.
        destruct (@AMap.Raw.PX.MO.elim_compare_eq a a); auto. rewrite H. auto.
      * simpl.
        destruct a0.
        destruct (AddressOrdered.compare a a0).
        simpl.
        destruct (@AMap.Raw.PX.MO.elim_compare_eq a a); auto. rewrite H. auto.
        simpl.
        destruct (@AMap.Raw.PX.MO.elim_compare_eq a a); auto. rewrite H. auto.
        simpl.
        destruct (AddressOrdered.compare a a0).
        pose proof (AddressOrdered.lt_trans l1 l0).
        apply AddressOrdered.lt_not_eq in H. contradiction H.
        reflexivity.
        apply AddressOrdered.lt_not_eq in l0.
        hnf in e. subst. contradiction l0; reflexivity.
        auto.
    Qed.


    Ltac address_ordered_auto :=
      auto; repeat match goal with
                   | H: AddressOrdered.eq ?A ?A |- _ => clear H
                   | H: AddressOrdered.eq ?A ?B |- _ => hnf in H; subst A
                   | H: ?A <> ?A |- _ => contradiction H; reflexivity
                   | H: AddressOrdered.lt ?A ?A |- _ =>
                     apply AddressOrdered.lt_not_eq in H; contradiction H; reflexivity
                   | H: AddressOrdered.lt ?A ?B, H': AddressOrdered.lt ?B ?A |- _ =>
                     contradiction (AddressOrdered.lt_not_eq (AddressOrdered.lt_trans H H')); reflexivity
                   end.

    Lemma gsolockResUpdLock: forall js loc a res,
        loc <> a ->
        lockRes (updLockSet js loc res) a =
        lockRes js a.
    Proof.
      intros.
      unfold lockRes, updLockSet. simpl.
      unfold AMap.find; simpl.
      forget (AMap.this (lockGuts js)) as el.
      unfold AMap.find; simpl.
      induction el; simpl.
      destruct (AddressOrdered.compare a loc); auto.
      address_ordered_auto.
      destruct a0.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare loc a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a loc); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare loc a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a0 a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a0 loc); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a0 a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare loc a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
      pose proof (AddressOrdered.lt_trans l1 l0).
      destruct (AddressOrdered.compare a loc); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
    Qed.

    Lemma gsslockResRemLock: forall js a,
        lockRes (remLockSet js a) a =
        None.
    Proof.
      intros.
      unfold lockRes, remLockSet; simpl. unfold AMap.find, AMap.remove; simpl.
      destruct js; simpl. destruct lset0; simpl.
      assert (SetoidList.NoDupA (@AMap.Raw.PX.eqk _) this).
      apply SetoidList.SortA_NoDupA with (@AMap.Raw.PX.ltk _); auto with typeclass_instances.
      rename this into el.
      revert H; clear; induction el; simpl; intros; auto.
      destruct a0.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
      inv H.
      clear - H2.
      revert H2; induction el; intros; auto.
      simpl. destruct a.
      destruct (AddressOrdered.compare a0 a); simpl; address_ordered_auto.
      contradiction H2. left. reflexivity.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
      apply IHel.
      inv H; auto.
    Qed.

    Lemma gsolockResRemLock: forall js loc a,
        loc <> a ->
        lockRes (remLockSet js loc) a =
        lockRes js a.
    Proof.
      intros.
      unfold lockRes, remLockSet; simpl.
      rewrite AMap_find_remove if_false; auto.
    Qed.


    Lemma gsoThreadLock:
      forall {i tp} c p (cnti: containsThread tp i),
        lockSet (updThread cnti c p) = lockSet tp.
    Proof.
        by auto.
    Qed.

    Lemma gsoThreadCLock:
      forall {i tp} c (cnti: containsThread tp i),
        lockSet (updThreadC cnti c) = lockSet tp.
    Proof.
        by auto.
    Qed.

    Lemma gsoThreadRLock:
      forall {i tp} p (cnti: containsThread tp i),
        lockSet (updThreadR cnti p) = lockSet tp.
    Proof.
      auto.
    Qed.

    Lemma gsoAddLock:
      forall tp c p,
        lockSet (addThread tp c p) = lockSet tp.
    Proof.
      auto.
    Qed.

    Lemma PX_in_rev:
      forall elt a m, AMap.Raw.PX.In (elt:=elt) a m <-> AMap.Raw.PX.In a (rev m).
    Proof.
      intros.
      unfold AMap.Raw.PX.In.
      unfold AMap.Raw.PX.MapsTo.
      split; intros [e ?]; exists e.
      rewrite SetoidList.InA_rev; auto.
      rewrite <- SetoidList.InA_rev; auto.
    Qed.

    Import SetoidList.
    Arguments InA {A}{eqA} x _.
    Arguments AMap.In {elt} x m.

    Lemma lockRes_range_dec: forall tp b ofs,
        { (exists z, z <= ofs < z+LKSIZE /\ lockRes tp (b,z) )%Z  } + {(forall z, z <= ofs < z+LKSIZE -> lockRes tp (b,z) = None)%Z }.
    Proof.
      intros tp b ofs.
      assert (H : (0 <= LKSIZE)%Z) by (pose proof LKSIZE_pos; lia).
      destruct (@RiemannInt_SF.IZN_var _ H) as (n, ->).
      induction n.
      - right. simpl. intros. lia.
      - destruct IHn as [IHn | IHn].
        + left; destruct IHn as (z & r & Hz).
          exists z; split; auto. zify. lia.
        + destruct (lockRes tp (b, (ofs - Z.of_nat n)%Z)) eqn:Ez.
          * left. exists (ofs - Z.of_nat n)%Z; split. 2:rewrite Ez; auto.
            zify; lia.
          * right; intros z r.
            destruct (zeq ofs (z + Z.of_nat n)%Z).
            -- subst; auto. rewrite <-Ez; do 2 f_equal. lia.
            -- apply IHn. zify. lia.
    Qed.

    Lemma lockSet_spec_3:
      forall ds b ofs,
        (forall z, z <= ofs < z+LKSIZE -> lockRes ds (b,z) = None)%Z ->
        (lockSet ds) !!!! b ofs = None.
    Proof.
      intros.
      unfold lockSet. unfold A2PMap.
      rewrite <- !List.fold_left_rev_right.
      match goal with |- context [fold_right ?F ?I] => set (f:=F); set (init:=I)end.
      unfold lockRes in H.
      assert (H': forall z,  (z <= ofs < z + LKSIZE)%Z ->
                        ~ AMap.In (b,z) (lockGuts ds)). {
        intros. intro. destruct H1; apply AMap.find_1 in H1.
        rewrite H in H1. inv H1. auto.
      } clear H.
      unfold lockGuts in *.
      assert (H7 : forall (x : AMap.key) (e : lock_info),
                 @InA _ (@AMap.eq_key_elt lock_info) (x, e) (rev (AMap.elements (lset ds))) ->
                 AMap.MapsTo x e (lset ds)). {
        intros. apply AMap.elements_2. rewrite -> InA_rev in H. apply H.
      }
      change address with AMap.key.
      forget (rev (AMap.elements (lset ds))) as al.
      revert H7; induction al; intros.
      simpl. rewrite PMap.gi. auto.
      change ((f a (fold_right f init al)) !!!! b ofs = None).
      unfold f at 1. destruct a as [[? ?] ?].
      simpl.
      rewrite setPermBlock_lookup; if_tac; auto.
      destruct H as [Heq H]; subst.
      apply H' in H. contradiction H.
      specialize (H7 (b,z) l). spec H7; [left; reflexivity |].
      exists l; auto.
    Qed.

    Lemma gsslockSet_rem: forall ds b ofs ofs0,
        lr_valid (lockRes ds) ->
        Intv.In ofs0 (ofs, ofs + lksize.LKSIZE)%Z ->
        isSome ((lockRes ds) (b,ofs)) ->  (*New hypothesis needed. Shouldn't be a problem *)
        (lockSet (remLockSet ds (b, ofs))) !!!! b ofs0 =
        None.
    Proof.
      intros.
      hnf in H0; simpl in H0.
      apply lockSet_spec_3.
      unfold LKSIZE in H0.
      unfold LKSIZE.
      intros.
      destruct (zeq ofs z).
      * subst ofs.
        unfold lockRes. unfold lockGuts. unfold remLockSet. simpl.
        assert (H8 := @AMap.remove_1 _ (lockGuts ds) (b,z) (b,z) (refl_equal _)).
        destruct (AMap.find (b, z) (AMap.remove (b, z) (lockGuts ds))) eqn:?; auto.
        apply  AMap.find_2 in Heqo.
        contradiction H8; eexists; eassumption.
      * hnf in H.
        destruct (lockRes ds (b,z)) eqn:?; inv H1.
      + destruct (lockRes ds (b,ofs)) eqn:?; inv H4.
        assert (z <= ofs < z+2 * size_chunk AST.Mptr \/ ofs <= z <= ofs+2 * size_chunk AST.Mptr)%Z by lia.
        destruct H1.
      - specialize (H b z). rewrite Heqo in H. unfold LKSIZE in H.
        specialize (H ofs). spec H; [lia|]. congruence.
      - specialize (H b ofs). rewrite Heqo0 in H. specialize (H z).
        unfold LKSIZE in H.
        spec H; [lia|]. congruence.
        + unfold lockRes, remLockSet.  simpl.
          assert (H8 := @AMap.remove_3 _ (lockGuts ds) (b,ofs) (b,z)).
          destruct (AMap.find (b, z) (AMap.remove (b, ofs) (lockGuts ds))) eqn:?; auto.
          apply  AMap.find_2 in Heqo0. apply H8 in Heqo0.
          unfold lockRes in Heqo.
          apply AMap.find_1 in Heqo0. congruence.
    Qed.



    Lemma gsolockSet_rem1: forall ds b ofs b' ofs',
        b  <> b' ->
        (lockSet (remLockSet ds (b, ofs))) !!!! b' ofs' =
        (lockSet ds)  !!!! b' ofs'.
    Proof.

      intros.
      destruct (lockRes_range_dec ds b' ofs').
      - destruct e as [z [ineq HH]]. unfold LKSIZE in ineq.
        erewrite lockSet_spec_2.
        erewrite lockSet_spec_2; auto.
        + hnf; simpl; eauto.
        + auto.
        + hnf; simpl; eauto.
        + rewrite gsolockResRemLock; auto.
          intros AA. inversion AA; subst. congruence.
      - erewrite lockSet_spec_3.
        erewrite lockSet_spec_3; auto.
        intros.
        rewrite gsolockResRemLock; auto.
        intros AA. inversion AA; congruence.
    Qed.

    Lemma gsolockSet_rem2: forall ds b ofs ofs',
        lr_valid (lockRes ds) ->
        ~ Intv.In ofs' (ofs, ofs + lksize.LKSIZE)%Z ->
        (lockSet (remLockSet ds (b, ofs))) !!!! b ofs' =
        (lockSet ds)  !!!! b ofs'.
    Proof.
      intros.
      destruct (lockRes_range_dec ds b ofs').
      - destruct e as [z [ineq HH]].
        assert (ofs <> z).
        { intros AA. inversion AA.
          apply H0. hnf.
          simpl; lia. }
        erewrite lockSet_spec_2.
        erewrite lockSet_spec_2; auto.
        + hnf; simpl; eauto.
        + auto.
        + hnf; simpl; eauto.
        + rewrite gsolockResRemLock; auto.
          intros AA. inversion AA. congruence.
      - erewrite lockSet_spec_3.
        erewrite lockSet_spec_3; auto.
        intros.
        destruct (zeq ofs z).
        subst ofs; rewrite gsslockResRemLock; auto.
        rewrite gsolockResRemLock; auto.
        intros AA. inversion AA; congruence.
    Qed.

    Lemma gssThreadCode {tid tp} (cnt: containsThread tp tid) c' p'
          (cnt': containsThread (updThread cnt c' p') tid) :
      @getThreadC _ (updThread cnt c' p') cnt' = c'.
    Proof.
      rewrite /getThreadC /updThread /=.
      rewrite (Fin.of_nat_ext cnt cnt') vlookup_insert //.
    Qed.

    Lemma eq_op_false: forall A i j, i <>j -> @eq_op A i j = false.
    Proof.
      intros.
      apply (@negbRL _ true).
      eapply contraFneq; last done.
      intros. easy.
    Qed.

    Lemma gsoThreadCode:
      forall {i j tp} (Hneq: i <> j) (cnti: containsThread tp i)
        (cntj: containsThread tp j) c' p'
        (cntj': containsThread (updThread cnti c' p') j),
        @getThreadC _ (updThread cnti c' p') cntj' = @getThreadC _ tp cntj.
    Proof. 
     tp_tac. 
     Qed.

    Lemma gssThreadRes {tid tp} (cnt: containsThread tp tid) c' p'
          (cnt': containsThread (updThread cnt c' p') tid) :
      getThreadR cnt' = p'.
    Proof. tp_tac. Qed.

    Lemma gsoThreadRes {i j tp} (cnti: containsThread tp i)
          (cntj: containsThread tp j) (Hneq: i <> j) c' p'
          (cntj': containsThread (updThread cnti c' p') j) :
      getThreadR cntj' = getThreadR cntj.
    Proof. tp_tac. Qed.

    Lemma gssThreadCC {tid tp} (cnt: containsThread tp tid) c'
          (cnt': containsThread (updThreadC cnt c') tid) :
      getThreadC cnt' = c'.
    Proof. tp_tac. Qed.

    Lemma gsoThreadCC {i j tp} (Hneq: i <> j) (cnti: containsThread tp i)
          (cntj: containsThread tp j) c'
          (cntj': containsThread (updThreadC cnti c') j) :
      getThreadC cntj = getThreadC cntj'.
    Proof. tp_tac. Qed.

    Lemma getThreadCC
          {tp} i j
          (cnti : containsThread tp i) (cntj : containsThread tp j)
          c' (cntj' : containsThread (updThreadC cnti c') j):
      getThreadC cntj' = if eq_nat_dec i j then c' else getThreadC cntj.
    Proof.
      destruct (eq_nat_dec i j); subst;
        [rewrite gssThreadCC |
         erewrite <- @gsoThreadCC with (cntj := cntj)];
        now eauto.
    Qed.

    Lemma gssThreadRR {tid tp} (cnt: containsThread tp tid) p'
          (cnt': containsThread (updThreadR cnt p') tid) :
      getThreadR cnt' = p'.
    Proof. tp_tac. Qed.

    Lemma gsoThreadRR {i j tp} (Hneq: i <> j) (cnti: containsThread tp i)
          (cntj: containsThread tp j) p'
          (cntj': containsThread (updThreadR cnti p') j) :
      getThreadR cntj = getThreadR cntj'.
    Proof. tp_tac. Qed.

    Lemma gThreadCR {i j tp} (cnti: containsThread tp i)
          (cntj: containsThread tp j) c'
          (cntj': containsThread (updThreadC cnti c') j) :
      getThreadR cntj' = getThreadR cntj.
    Proof. tp_tac. Qed.

    Lemma gThreadRC {i j tp} (cnti: containsThread tp i)
          (cntj: containsThread tp j) p
          (cntj': containsThread (updThreadR cnti p) j) :
      getThreadC cntj' = getThreadC cntj.
    Proof. tp_tac. Qed.

    (* Lemma unlift_m_inv :
      forall tp i (Htid : i < (num_threads tp).+1) ord
        (Hunlift: unlift (ordinal_pos_incr (num_threads tp))
                         (Ordinal (n:=(num_threads tp).+1)
                                  (m:=i) Htid)=Some ord),
        nat_of_ord ord = i.
    Proof.
      intros.
      assert (Hcontra: unlift_spec (ordinal_pos_incr (num_threads tp))
                                   (Ordinal (n:=(num_threads tp).+1)
                                            (m:=i) Htid) (Some ord)).
      rewrite <- Hunlift.
      apply/unliftP.
      inversion Hcontra; subst.
      inversion H0.
      unfold bump.
      assert (pf: ord < (num_threads tp))
        by (by rewrite ltn_ord).
      assert (H: (num_threads tp) <= ord = false).
      rewrite ltnNge in pf.
      rewrite <- Bool.negb_true_iff. auto.
      rewrite H. simpl. rewrite add0n. reflexivity.
    Defined. *)


    Lemma gssAddRes:
      forall {tp} c pmap j
        (Heq: j = latestThread tp)
        (cnt': containsThread (addThread tp c pmap) j),
        getThreadR cnt' = pmap.
    Proof. intros; subst. tp_tac. Qed.


    Lemma gsoAddRes:
      forall {tp} c pmap j
        (cntj: containsThread tp j) (cntj': containsThread (addThread tp c pmap) j),
        getThreadR cntj' = getThreadR cntj.
    Proof. intros; subst. tp_tac. Qed.

    Lemma gssAddCode:
      forall {tp} c pmap j
        (Heq: j = latestThread tp)
        (cnt': containsThread (addThread tp c pmap) j),
        getThreadC cnt' = Kblocked c.
    Proof. intros. subst. tp_tac. Qed.

    Lemma gsoAddCode:
      forall {tp} c pmap j
        (cntj: containsThread tp j)
        (cntj': containsThread (addThread tp c pmap) j),
        getThreadC cntj' = getThreadC cntj.
    Proof. tp_tac. Qed.

    (* Ke: now addThread is a fork, add and update are not commutative any more *)
    Lemma add_update_comm:
      forall tp i c pmap c' pmap'
        (cnti: containsThread tp i)
        (cnti': containsThread (addThread tp c pmap) i),
        addThread (updThread cnti c' pmap') c pmap =
        updThread cnti' c' pmap'.
    Proof. tp_tac. Qed.

    Lemma add_updateC_comm:
      forall tp i c pmap c'
        (cnti: containsThread tp i)
        (cnti': containsThread (addThread tp c pmap) i),
        addThread (updThreadC cnti c') c pmap =
        updThreadC cnti' c'.
    Proof. tp_tac. Qed.

    Lemma updThread_comm :
      forall tp  i j c pmap c' pmap'
        (Hneq: i <> j)
        (cnti : containsThread tp i)
        (cntj : containsThread tp j)
        (cnti': containsThread (updThread cntj c' pmap') i)
        (cntj': containsThread (updThread cnti c pmap) j),
        updThread cnti' c pmap = updThread cntj' c' pmap'.
    Proof. tp_tac. Qed.

    Lemma updThread_updThreadC_comm :
      forall tp i j c pmap' c'
        (Hneq: i <> j)
        (cnti : containsThread tp i)
        (cntj : containsThread tp j)
        (cnti': containsThread (updThread cntj c' pmap') i)
        (cntj': containsThread (updThreadC cnti c) j),
        updThreadC cnti' c = updThread cntj' c' pmap'.
    Proof. tp_tac. Qed.

    Lemma updThread_same :
      forall tp i (cnti : containsThread tp i),
      updThread cnti (getThreadC cnti) (getThreadR cnti) = tp.
    Proof.
      tp_tac. by destruct tp.
    Qed.

    Lemma updThread_twice :
      forall tp i (cnti : containsThread tp i) c c' r r'
        (cnti' : containsThread (updThread cnti c r) i),
      updThread cnti' c' r' = updThread cnti c' r'.
    Proof. tp_tac. Qed.

    Lemma updThreadRC : forall tp i (cnti : containsThread tp i) c,
      updThread cnti c (getThreadR cnti) = updThreadC cnti c.
    Proof. tp_tac. Qed.

    Lemma gsoThreadCLPool:
      forall {i tp} c (cnti: containsThread tp i) addr,
        lockRes (updThreadC cnti c) addr = lockRes tp addr.
    Proof. tp_tac. Qed.

    Lemma gsoThreadLPool:
      forall {i tp} c p (cnti: containsThread tp i) addr,
        lockRes (updThread cnti c p) addr = lockRes tp addr.
    Proof. tp_tac. Qed.

    Lemma gsoAddLPool:
      forall tp c p (addr : address),
        lockRes (addThread tp c p) addr = lockRes tp addr.
    Proof. tp_tac. Qed.

    Lemma gLockSetRes:
      forall {i tp} addr (res : lock_info) (cnti: containsThread tp i)
        (cnti': containsThread (updLockSet tp addr res) i),
        getThreadR cnti' = getThreadR cnti.
    Proof. tp_tac. Qed.

    Lemma gLockSetCode:
      forall {i tp} addr (res : lock_info) (cnti: containsThread tp i)
        (cnti': containsThread (updLockSet tp addr res) i),
        getThreadC cnti' = getThreadC cnti.
    Proof. tp_tac. Qed.

    Lemma gRemLockSetCode:
      forall {i tp} addr (cnti: containsThread tp i)
        (cnti': containsThread (remLockSet tp addr) i),
        getThreadC cnti' = getThreadC cnti.
    Proof. tp_tac. Qed.

    Lemma gRemLockSetRes:
      forall {i tp} addr (cnti: containsThread tp i)
        (cnti': containsThread (remLockSet tp addr) i),
        getThreadR cnti' = getThreadR cnti.
    Proof. tp_tac. Qed.

    Lemma gssLockRes:
      forall tp addr pmap,
        lockRes (updLockSet tp addr pmap) addr = Some pmap.
    Proof.
      intros.
      unfold lockRes, updLockSet. simpl.
      unfold AMap.find, AMap.add; simpl.
      forget (AMap.this (lockGuts tp)) as el.
      clear. induction el; simpl.
      destruct (AddressOrdered.compare addr addr); address_ordered_auto.
      destruct a.
      destruct (AddressOrdered.compare addr a); address_ordered_auto.
      simpl.
      destruct (AddressOrdered.compare addr addr); address_ordered_auto.
      simpl.
      destruct (AddressOrdered.compare a a); address_ordered_auto.
      simpl.
      destruct (AddressOrdered.compare addr a); address_ordered_auto.
    Qed.

    Lemma gsoLockRes:
      forall tp addr addr' pmap
        (Hneq: addr <> addr'),
        lockRes (updLockSet tp addr pmap) addr' =
        lockRes tp addr'.
    Proof.
      intros.
      rename addr into a; rename addr' into b.
      unfold lockRes, updLockSet. simpl. destruct tp; simpl. destruct lset0; simpl.
      unfold AMap.find, AMap.add; simpl.
      rename this into el.
      induction el as [ | [c ?]].
      simpl.
      destruct (AddressOrdered.compare b a); address_ordered_auto.
      simpl.
      destruct (AddressOrdered.compare a c); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare b c); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare b a); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare c a); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare b a); simpl; address_ordered_auto.
      pose proof (AddressOrdered.lt_trans l0 l1); address_ordered_auto.
      destruct (AddressOrdered.compare b c); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare b c); simpl; address_ordered_auto.
      apply IHel.
      inv sorted; auto.
    Qed.

    Lemma gssLockSet:
      forall tp b ofs rmap ofs',
        (ofs <= ofs' < ofs + Z.of_nat lksize.LKSIZE_nat)%Z ->
        (Maps.PMap.get b (lockSet (updLockSet tp (b, ofs) rmap)) ofs') =
        Some Memtype.Writable.
    Proof.
      intros.
      apply lockSet_spec_2 with ofs; auto.
      red.
      rewrite gssLockRes. reflexivity.
    Qed.

    Lemma gsoLockSet_12 :
      forall tp b b' ofs ofs' pmap,
        ~ adr_range (b,ofs) LKSIZE (b',ofs') ->
        (Maps.PMap.get b' (lockSet (updLockSet tp (b,ofs) pmap))) ofs' =
        (Maps.PMap.get b' (lockSet tp)) ofs'.
    Proof.

      intros.
      destruct (lockRes_range_dec tp b' ofs').
      - destruct e as [z [ineq HH]]. unfold LKSIZE in ineq.
        erewrite lockSet_spec_2.
        erewrite lockSet_spec_2; auto.
        + hnf; simpl; eauto.
        + auto.
        + hnf; simpl; eauto.
        + rewrite gsolockResUpdLock; auto.
          intros AA. inversion AA.
          eapply H. unfold adr_range. subst; split; auto.
      - erewrite lockSet_spec_3.
        erewrite lockSet_spec_3; auto.
        intros.
        rewrite gsolockResUpdLock; auto.
        intros AA. inversion AA.
        eapply H. unfold adr_range. subst; split; auto.
    Qed.

    Lemma gsoLockSet_1:
      forall tp b ofs ofs'  pmap
        (Hofs: (ofs' < ofs)%Z \/ (ofs' >= ofs + (Z.of_nat lksize.LKSIZE_nat))%Z),
        (Maps.PMap.get b (lockSet (updLockSet tp (b,ofs) pmap))) ofs' =
        (Maps.PMap.get b (lockSet tp)) ofs'.
    Proof.
      intros.
      apply gsoLockSet_12. intros [? ?]. unfold LKSIZE_nat in *; rewrite Z2Nat.id in Hofs; simpl in *; lia.
    Qed.

    Lemma gsoLockSet_2 :
      forall tp b b' ofs ofs' pmap,
        b <> b' ->
        (Maps.PMap.get b' (lockSet (updLockSet tp (b,ofs) pmap))) ofs' =
        (Maps.PMap.get b' (lockSet tp)) ofs'.
    Proof.
      intros.
      apply gsoLockSet_12. intros [? ?]. contradiction.
    Qed.

    Lemma lockSet_updLockSet:
      forall tp i (pf: containsThread tp i) c pmap addr rmap,
        lockSet (updLockSet tp addr rmap) =
        lockSet (updLockSet (updThread pf c pmap) addr rmap).
    Proof.
      intros.
      unfold lockSet, updLockSet, updThread.
      simpl;
        by reflexivity.
    Qed.

    Lemma updThread_lr_valid:
      forall tp i (cnti: containsThread tp i) c' m',
        lr_valid (lockRes tp) ->
        lr_valid (lockRes (updThread cnti c' m')).
    Proof.
      repeat intro.
      rewrite gsoThreadLPool; apply H.
    Qed.

(*     Lemma gssExtraRes : forall tp res, extraRes (updExtraRes tp res) = res.
    Proof.
      reflexivity.
    Qed.

    Lemma gsoAddExtra : forall tp vf arg p, extraRes (addThread tp vf arg p) = extraRes tp.
    Proof.
      reflexivity.
    Qed.

    Lemma gsoThreadCExtra : forall {i tp} c (cnti: containsThread tp i), extraRes (updThreadC cnti c) = extraRes tp.
    Proof.
      reflexivity.
    Qed.

    Lemma gsoThreadRExtra : forall {i tp} r (cnti: containsThread tp i), extraRes (updThreadR cnti r) = extraRes tp.
    Proof.
      reflexivity.
    Qed.

    Lemma gsoThreadExtra : forall {i tp} c r (cnti: containsThread tp i), extraRes (updThread cnti c r) = extraRes tp.
    Proof.
      reflexivity.
    Qed.

    Lemma gsoLockSetExtra : forall tp addr res, extraRes (updLockSet tp addr res) = extraRes tp.
    Proof.
      reflexivity.
    Qed.

    Lemma gsoRemLockExtra : forall tp addr, extraRes (remLockSet tp addr) = extraRes tp.
    Proof.
      reflexivity.
    Qed.

    Lemma gExtraResCode : forall {i tp} res (cnti: containsThread tp i)
               (cnti': containsThread (updExtraRes tp res) i),
               getThreadC cnti' = getThreadC cnti.
    Proof.
      destruct tp; simpl.
      intros; do 2 f_equal.
      apply cnt_irr.
    Qed.

    Lemma gExtraResRes : forall {i tp} res (cnti: containsThread tp i)
               (cnti': containsThread (updExtraRes tp res) i),
               getThreadR cnti' = getThreadR cnti.
    Proof.
      destruct tp; simpl.
      intros; do 2 f_equal.
      apply cnt_irr.
    Qed.

    Lemma gsoExtraLPool : forall tp res addr,
               lockRes (updExtraRes tp res) addr = lockRes tp addr.
    Proof.
      reflexivity.
    Qed.

    Lemma gsoExtraLock : forall tp res,
               lockSet (updExtraRes tp res) = lockSet tp.
    Proof.
      reflexivity.
    Qed. *)

    Lemma contains_iff_num:
      forall tp tp'
        (Hcnt: forall i, containsThread tp i <-> containsThread tp' i),
        num_threads tp = num_threads tp'.
    Proof.
      tp_tac.
      forget (num_threads tp) as n.
      forget (num_threads tp') as n'.
      destruct (decide (n < n')).
      1 :{ destruct (Hcnt n) as [_ ?]. lia. }
      destruct (decide (n' < n)).
      1: { destruct (Hcnt n') as [? _]. lia. }
      lia.
    Qed.

    (* looks like the following are not used: *)
    (*
    Lemma leq_stepdown:
      forall {m n},
        S n <= m -> n <= m.
    Proof. intros; ssrlia. Qed.
    
    Lemma lt_sub:
      forall {m n},
        S n <= m ->
        m - (S n) <  m.
    Proof. intros; ssrlia. Qed.

    
    Fixpoint containsList_upto_n (n m:nat): n <= m -> seq.seq (sigT (fun i => i < m)):=
      match n with
      | O => fun _ => nil
      | S n' => fun (H: S n' <= m) =>
                 (existT (P := fun i => i < m) (m-(S n')) (lt_sub H)) ::
                 (containsList_upto_n n' m) (leq_stepdown H)
      end.

    Lemma containsList_upto_n_spec:
      forall m n (H: n <= m)
        i (cnti:  (fun i => i < m) (m - n + i)),
        i < n ->
        nth_error (containsList_upto_n n m H) i = Some (existT (m - n + i) (cnti)). 
    Proof.
      intros.
      remember (n - i) as k.
      assert (HH: n = i + k) by ssrlia.
      clear Heqk.
      revert m n H cnti H0 HH.
      induction i.
      intros.
      - destruct n; try (exfalso; ssrlia).
        simpl. f_equal.
        eapply ProofIrrelevance.ProofIrrelevanceTheory.subsetT_eq_compat.
        ssrlia.
      - intros.
        assert (n = (n - 1).+1) by ssrlia.
        revert H cnti .
        dependent rewrite H1.
        intros H cnti.
        simpl.
        rewrite IHi.
        + ssrlia.
        + intros. f_equal.
          eapply ProofIrrelevance.ProofIrrelevanceTheory.subsetT_eq_compat.
          clear - H.
          ssrlia.
        + ssrlia.
        + ssrlia.
    Qed.
      
    Lemma leq_refl: forall n, n <= n. Proof. intros; ssrlia. Qed.
    
    Definition containsList' (n:nat): seq.seq (sigT (fun i => i < n)):=
      containsList_upto_n n n (leq_refl n).

    Definition contains_from_ineq (tp:t):
        {i : tid & i < num_threads tp } -> {i : tid & containsThread tp i}:=
       fun (H : {i : tid & i < num_threads tp}) =>
         let (x, i) := H in existT x i.

    Definition containsList (tp:t): seq.seq (sigT (containsThread tp)):=
      map (contains_from_ineq tp) (containsList' (num_threads tp)).

    Lemma containsList'_spec: forall i n
            (cnti: (fun i => i < n) i),
            List.nth_error (containsList' n) i = Some (existT i (cnti)).
    Proof.
      intros.
      unfold containsList'.
      - rewrite containsList_upto_n_spec.
        + simpl in cnti; ssrlia.
        + intros. f_equal.
          eapply ProofIrrelevance.ProofIrrelevanceTheory.subsetT_eq_compat.
          simpl in cnti; ssrlia.
        + assumption.
    Qed.

      
    Lemma containsList_spec: forall i tp
            (cnti: containsThread tp i),
            List.nth_error (containsList tp) i = Some (existT i cnti).
    Proof.
      intros.
      unfold containsList. 
      rewrite list_map_nth containsList'_spec; simpl.
      reflexivity.
    Qed.
      
    Definition indexed_contains tp:= (fun Ncontained: (sigT (containsThread tp)) =>
             let (i, cnti) := Ncontained in getThreadR cnti).
    
    Definition resourceList (tp:t): seq.seq res:=
      map (@indexed_contains tp)
          (containsList tp).

    Lemma resourceList_spec: forall i tp
            (cnti: containsThread tp i),
            List.nth_error (resourceList tp) i = Some (getThreadR cnti).
    Proof.
      intros.
      unfold containsThread in cnti.
      destruct tp.
      destruct num_threads0 as [n ?].
      unfold getThreadR; simpl.
      simpl in *.
      induction n.
      - exfalso. ssrlia.
      - unfold resourceList.
        rewrite list_map_nth.
        rewrite containsList_spec.
        reflexivity.
    Qed.
    *)

    Definition maybeContainsThread tp tid : option (containsThread tp tid) :=
      match containsThread_dec tid tp with
      | left cnt => Some cnt
      | right _ => None
      end.

    Definition FinThreadPool: ThreadPool.ThreadPool :=
      (@ThreadPool.Build_ThreadPool _ _
                                    t
                                    mkPool
                                    containsThread
                                    (@getThreadC)
                                    (@getThreadR)
                                    (* resourceList *)
                                    lockGuts
                                    lockSet
                                    (@lockRes)
                                    (* extraRes *)
                                    addThread
                                    addThreads
                                    (@updThreadC)
                                    (@updThreadR)
                                    (@updThread)
                                    updLockSet
                                    remLockSet
                                    (* updExtraRes *)
                                    latestThread
                                    lr_valid 
                                    (*Find the first thread i, that satisfies (filter i) *)
                                    (* find_thread *)
                                    (* resourceList_spec *)
                                    containsThread_dec
                                    maybeContainsThread
                                    (*Proof Irrelevance of contains*)
                                    cnt_irr
                                    (@cntAdd)
                                    (@cntAddLatest)
                                    (@cntAdd')
                                    (@cntUpdateC)
                                    (@cntUpdateC')
                                    (@cntUpdateR)
                                    (@cntUpdateR')
                                    (@cntUpdate)
                                    (@cntUpdate')
                                    (@cntUpdateL)
                                    (@cntRemoveL)
                                    (@cntUpdateL')
                                    (@cntRemoveL')
                                    (* (@cntUpdateExtra) *)
                                    (@gsoThreadLock)
                                    (@gsoThreadCLock)
                                    (@gsoThreadRLock)
                                    (@gsoAddLock)
                                    (@gssAddRes)
                                    (@gssThreadCode)
                                    (@gsoThreadCode)
                                    (@gssThreadRes)
                                    (@gsoThreadRes)
                                    (@gssThreadCC)
                                    (@gsoThreadCC)
                                    (@getThreadCC)
                                    (@gssThreadRR)
                                    (@gsoThreadRR)
                                    (@gThreadCR)
                                    (@gThreadRC)
                                    (@gsoThreadCLPool)
                                    (@gsoThreadLPool)
                                    (@gsoAddLPool)
                                    (@gLockSetRes)
                                    (@gLockSetCode)
                                    (@gssLockRes)
                                    (@gsoLockRes)
                                    (@gssLockSet)
                                    (@gsoLockSet_1)
                                    gsoLockSet_2
                                    lockSet_updLockSet
                                    updThread_updThreadC_comm
                                    updThread_comm
                                    add_updateC_comm
                                    add_update_comm
                                    updThread_lr_valid
(*                                     gssExtraRes
                                    gsoAddExtra
                                    (@gsoThreadCExtra)
                                    (@gsoThreadRExtra)
                                    (@gsoThreadExtra)
                                    gsoLockSetExtra
                                    gsoRemLockExtra
                                    (@gExtraResCode)
                                    (@gExtraResRes)
                                    gsoExtraLPool
                                    gsoExtraLock *)
                                    lockSet_spec_2
                                    lockSet_spec_3
                                    gsslockSet_rem
                                    gsolockSet_rem1
                                    gsolockSet_rem2
                                    gsslockResUpdLock
                                    gsolockResUpdLock
                                    gsslockResRemLock
                                    gsolockResRemLock
                                    (@gRemLockSetCode)
                                    (@gRemLockSetRes)
                                    (@gsoAddCode)
                                    (@gssAddCode)
                                    (@gsoAddRes)
                                    updLock_updThread_comm
                                    remLock_updThread_comm
                                    remLock_updThreadC_comm
      ).

  End FinThreadPool.
End FinPool.
