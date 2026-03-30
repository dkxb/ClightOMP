From mathcomp.ssreflect Require Import ssreflect ssrbool.
Require Import Coq.Program.Wf FunInd Recdef.
From compcert Require Import Values Clight Memory Ctypes AST Globalenvs.
From VST.concurrency.openmp_sem Require Import reduction notations for_construct clight_fun.
From stdpp Require Import base list.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From Coq Require Import Nat.
From Equations Require Import Equations.

Section SiblingTree.

  Context {B:Type}.
  (* a tree that can have multiple children *)
  Inductive stree : Type :=
  | SNode : B -> list stree -> stree.

  Definition data (st: stree) : B :=
    match st with | SNode b _ => b end.

  Definition kids (st: stree) : list stree :=
    match st with | SNode _ kids => kids end.

  #[export] Instance stree_settable : Settable stree := settable! SNode < data; kids >.

  (* stree eliminator, with the ability of knowing a node's parent
     f (parent: option B) (current_node_info: B) (previously accumulated results: A) *)
  (* Fixpoint fold_tree_p {A: Type} (st: stree) (f: option B -> B -> A -> A) (accu: A) (parent: option B) : A :=
    match st with | SNode b kids =>
    let accu' := f parent b accu in
       foldr (λ st accu, fold_tree_p st f accu $ Some b) accu' kids
    end. *)

  Fixpoint fold_stree {A: Type} (f: B -> A -> A) (s: stree) (base: A) :=
    f (data s) (foldr (fold_stree f) base (kids s)).
  
  Fixpoint stree_measure s :=
    1 + (foldr add 0 $ (stree_measure <$> kids s)).

  Lemma stree_measure_pos s : stree_measure s > 0.
    rewrite /stree_measure /=.
    induction s. destruct l; simpl; lia.
  Qed.

End SiblingTree.

Notation " x '.data' " := (data x) (at level 3).
Notation " x '.kids' " := (kids x) (at level 3).

(*
Example of a list zipper (not shown here):
  l:=[a;b;c;d]
look l c
  [] a [b;c;d]
  [a] b [c;d]
  [a;b] c [d]

We can define operations such as:
  go_left
  go_right
*)

Section SiblingTreeZipper.
  Context {B:Type}.

  Notation stree := (@stree B).
  Definition sforest := list stree.

  (* from haskell tree zipper `tree_pos`, 
    https://hackage.haskell.org/package/rosezipper-0.2/docs/src/Data-Tree-Zipper.html*)
  Inductive tree_zipper : Type :=
  (* this : the focused stree
    before : the list of siblings to the left, in reverse order
     after : the list of siblings to the right (in normal order)
    parents : each item in the list is the parent node and its left and right siblings.

            []        parents[n].2     []
                       ...
    parents[1].1   parents[1].2      parents[1].3
                  /    |         \
                /      |          \
    parents[0].1   parents[0].2    parents[0].3
                  /    |    \
  [b_k;...;b_1;b_0]   b_(k+1)    [b_((k+2);b_(k+3)...]

            GO LEFT->
    [...;b_1;b_0]   b_k;    [b_((k+1);b_(k+2)...]
    *)
  | TreeZip (tis: stree) (b a: sforest) (p: list (sforest * B * sforest))
  .

  Implicit Type (tz: tree_zipper).

  Definition this tz : stree :=
    match tz with
    | TreeZip tis _ _ _ => tis
    end.

  Definition before tz : sforest :=
    match tz with
    | TreeZip _ b _ _ => b end.

  Definition after tz : sforest :=
    match tz with
    | TreeZip _ _ a _ => a
    end.

  Definition parents tz : list (sforest * B * sforest) :=
    match tz with
    | TreeZip _ _ _ p => p
    end.

  #[export] Instance tree_zipper_settable : Settable tree_zipper := settable! TreeZip < this; before; after; parents >.

  Definition from_stree (st: stree) : tree_zipper :=
    TreeZip st [] [] [].

  (* all siblings and itself *)
  Definition forest tz : sforest :=
    (rev (before tz)) ++ [this tz] ++ after tz.

  Definition go_left tz : option tree_zipper :=
    match tz with
    | TreeZip this (h::b) a p =>
      Some (TreeZip h b (this::a) p)
    | _ => None
    end.

  Definition go_right tz : option tree_zipper :=
    match tz with
    | TreeZip this b (h::a) p =>
      Some (TreeZip h (this::b) a p)
    | _ => None
    end.

  (* go to the parent *)
  Definition go_up tz : option tree_zipper :=
    match tz with
    | TreeZip this b a ((l, p, r)::ps) =>
      Some (TreeZip (SNode p $ forest tz) l r ps)
    | _ => None
    end.

  (* go to the left most child *)
  Definition go_down tz : option tree_zipper :=
    match tz with
    | TreeZip (SNode d (k::ks)) b a ps =>
      Some (TreeZip k [] ks ((b, d, a)::ps))
    | _ => None
    end.

  Lemma left_right_idem:
    ∀ tz tz'',
      (tz' ← go_left tz; go_right tz') = Some tz''
      -> tz = tz''.
  Proof.
    intros. destruct tz. destruct b; first done.
    unfold_mbind_in_hyp. inv H. done.
  Qed.
  
  Lemma right_left_idem:
    ∀ tz tz'',
      (tz' ← go_right tz; go_left tz') = Some tz''
      -> tz = tz''.
  Proof.
    intros. destruct tz. destruct a; first done.
    unfold_mbind_in_hyp. inv H. done.
  Qed.

  Definition tree_pos_iter tz : option tree_zipper :=
    match go_right tz with
    | Some tz' => Some tz'
    | None =>
      match go_down tz with
      | Some tz' => Some tz'
      | None => None
      end
    end.

  (* measured in size of right siblings and children *)
  Definition tree_pos_measure tz : nat :=
    match tz with
    | TreeZip this _ a _ => stree_measure this + foldr add 0 (stree_measure <$> a)
    end.

  Lemma tree_pos_iter_wf tz tz':
    tree_pos_iter tz = Some tz'
    → tree_pos_measure tz' < tree_pos_measure tz.
  Proof.
    intros H.
    rewrite /tree_pos_iter in H.
    destruct_match!.
    { rewrite /go_right in Heqo.
      destruct tz => //.
      destruct a => //. inv Heqo.
      rewrite /tree_pos_measure /fmap /= -/fmap.
      assert (stree_measure tis > 0) by apply stree_measure_pos.
      lia. }
    destruct_match!.
    rewrite /go_down in Heqo0.
    destruct_match!.
    destruct_match!.
    destruct_match!.
    inv Heqo0.
    rewrite /tree_pos_measure.
    rewrite  /stree_measure /= -/stree_measure /fmap. lia.
  Defined.

  (* the equation for the case when we go down *)
  Definition tree_zipper_iter_rel : relation tree_zipper.
  Proof. rewrite /relation. intros tz tz'. 
    refine (tree_pos_iter tz' = Some tz). Defined.

  #[export] Instance tree_zipper_iter_wf : WellFounded tree_zipper_iter_rel.
  Proof. rewrite /WellFounded.  eapply (well_founded_lt_compat _  (tree_pos_measure)).
    intros. apply tree_pos_iter_wf. rewrite H //. Defined.

  (* not used for now *)
  Section TreeZipperIter.

    Program Fixpoint fold_tree_zipper' {A: Type} tz (f: tree_zipper -> A -> A) (base: A) {measure (tree_pos_measure tz) } : A :=
      let rest:A :=
        match tree_pos_iter tz with
        | Some tz' => fold_tree_zipper' tz' f base
        | None => base
        end in
      f tz rest
      .
    Next Obligation. intros. by apply tree_pos_iter_wf. Defined.
    Next Obligation. apply measure_wf. apply lt_wf. Defined.

    Equations fold_tree_zipper {A: Type} tz (f: tree_zipper -> A -> A) (base: A) : A by wf tz tree_zipper_iter_rel :=
      (* go right if possible *)
      fold_tree_zipper (TreeZip this b (h::a) p) f base :=
        let tz := (TreeZip this b (h::a) p) in
          f tz (fold_tree_zipper (TreeZip h (this::b) a p) f base);
      fold_tree_zipper (TreeZip (SNode d (h::kids)) b [] p) f base :=
        let tz := (TreeZip (SNode d (h::kids)) b [] p) in
          f tz (fold_tree_zipper (TreeZip h [] kids ((b,d,[])::p)) f base);
      fold_tree_zipper tz f base := base.
    Next Obligation. rewrite /tree_zipper_iter_rel. rewrite /tree_pos_iter //. Defined.
    Next Obligation. rewrite /tree_zipper_iter_rel. rewrite /tree_pos_iter //. Defined.
  End TreeZipperIter.

  (* TODO maybe rewrite tz_lookup with fold_tree_zipper *)
  Program Fixpoint _tz_lookup (f: stree -> bool) tz {measure (tree_pos_measure tz)} : option tree_zipper :=
  if f (this tz) then Some tz else
  let right_res :=
      match go_right tz with
    | Some tz_r => _tz_lookup f tz_r
    | None => None 
    end in
  match right_res with
  | Some res => Some res
  | None => 
    match go_down tz with
    | Some tz_d => _tz_lookup f tz_d
    | None => None
    end
  end.
  Next Obligation. destruct tz. destruct a; try done. inv Heq_anonymous.
    simpl. rewrite /fmap. destruct tis; simpl. lia. Defined.
  Next Obligation. destruct tz. destruct tis. destruct l; try done. inv Heq_anonymous.
    simpl. rewrite /fmap. lia. Defined.
  Next Obligation. apply measure_wf. apply lt_wf. Defined.

  Definition _stree_lookup (f: stree -> bool) s := _tz_lookup f (from_stree s).

  (* This is the one we actually use! *)
  Equations tz_lookup (f: stree -> bool) tz : option tree_zipper by wf tz tree_zipper_iter_rel :=
    tz_lookup f (TreeZip this b (h::a) p) :=
      let tz := (TreeZip this b (h::a) p) in
      if (f this) then Some tz else
      (* look right if possible *)
        tz_lookup f (TreeZip h (this::b) a p);
    tz_lookup f (TreeZip (SNode d (h::kids)) b [] p) :=
      let tz := (TreeZip (SNode d (h::kids)) b [] p) in
      if (f $ this tz) then Some tz else
      (* look down if possible *)
        tz_lookup f (TreeZip h [] kids ((b,d,[])::p));
    tz_lookup f tz :=
      if (f $ this tz) then Some tz else None.
  Next Obligation. rewrite /tree_zipper_iter_rel. rewrite /tree_pos_iter //. Defined.
  Next Obligation. rewrite /tree_zipper_iter_rel. rewrite /tree_pos_iter //. Defined.

  (* go_up is well-founded *)
  Definition tree_pos_measure_up tz : nat :=
    match tz with
    | TreeZip _ _ _ p => length p 
    end.

  Lemma go_up_wf tz tz':
    go_up tz = Some tz'
    → tree_pos_measure_up tz' < tree_pos_measure_up tz.
  Proof.
    intros H.
    rewrite /go_up in H.
    destruct tz => //.
    destruct p; first done.
    repeat destruct_match!. inv H. simpl. lia.
  Defined.

  (* Using Equations would generate the rewrite lemmas automatically,
     but the definition would be a bit hard to read (it has to be defined on patterns of tz) and may not compute. *)
  Program Fixpoint root tz {measure (tree_pos_measure_up tz)}: tree_zipper :=
    match go_up tz with
    | Some tz' => root tz'
    | None => tz
    end.
  Next Obligation. apply go_up_wf. rewrite Heq_anonymous //. Defined.
  Next Obligation. apply measure_wf. apply lt_wf. Defined.

  Lemma root_eq_1 this b a l d r p :
    root $ TreeZip this b a ((l,d,r)::p) = root $ TreeZip (SNode d ((rev b)++[this]++a)) l r p.
  Proof.
    rewrite /root.
    rewrite WfExtensionality.fix_sub_eq_ext /=.
    rewrite /forest //.
  Qed.

 Lemma root_eq_2 tz : 
     (go_up tz = None) → root tz = tz.
  Proof. intros. rewrite /root.
    rewrite WfExtensionality.fix_sub_eq_ext /= H //.
  Qed.

  Definition to_stree (tz: tree_zipper) : option stree :=
    match (root tz) with
    | TreeZip this [] [] _ => Some this
    | _ => None
    end.

  Lemma from_to_stree_idem (st: stree) :
    to_stree (from_stree st) = Some st.
  Proof. rewrite /to_stree /from_stree //. Qed.

  Lemma go_right_same_tree (tz tz': tree_zipper) :
    go_right tz = Some tz' → to_stree tz = to_stree tz'.
  Proof.
    intros H.
    induction tz. destruct a; first done.
    rewrite /root.
    inv H. 
    destruct p; rewrite /to_stree.
    - rewrite !root_eq_2 //. destruct b; done.
    - destruct p as [[? ?] ?]. rewrite !root_eq_1 //.
      rewrite app_assoc //.
  Qed.

  Definition stree_lookup (is_target: stree -> bool) s := 
    tz_lookup is_target (from_stree s).

  (* NOTE if we write stree_update directly on stree, then there are 2 bad things:
     1. update is not modular with lookup;
     2. have to induct on the tree structure, during which we have to induct on the list of children, 
        mixing 2 inductive principles, whereas in tree_zipper we have a unified one. *)
  (* lookup with is_target, if found, update the data of the subtree to b' *)
  Definition tz_update (is_target: stree -> bool) (f: stree -> stree) (tz: tree_zipper) : option tree_zipper :=
    tz' ← tz_lookup is_target tz;
    Some (tz' <| this := f (this tz') |>).

  Definition stree_update (is_target: stree -> bool) (f: stree -> stree) (s: stree) : option stree :=
    tz ← tz_update is_target f (from_stree s);
    to_stree tz.

  (* so original field of k does not matter *)
  Definition tz_comp (k: tree_zipper) (s' s: stree) : Prop :=
    to_stree $ k <| this:=s' |> = Some s.

  (* s' ⊂ s *)
  Definition sub_tree s' s : Prop :=
    ∃ k, tz_comp k s' s.

  Lemma stree_update_correct is_target f s1 s2 :
    stree_update is_target f s1 = Some s2 →
    ∃ k s', tz_comp k s' s1 ∧ tz_comp k (f s') s2.
  Proof.
    intros. rewrite /stree_update in H.
    unfold_mbind_in_hyp; destruct_match!.
    rewrite /tz_update in Heqo.
    unfold_mbind_in_hyp; destruct_match!.
    exists t0, (this t0).
    destruct (tz_lookup_correct _ _ _ Heqo0).
    rewrite /tz_comp; split.
    - destruct t0; rewrite /this // .  
    - inversion Heqo. rewrite H3 //.
  Qed.

End SiblingTreeZipper.

Section TreeZipperTests.
  Example test_stree_lookup :
    tz_lookup (λ x, data x =? 3) 
      (TreeZip (SNode 0 []) [] [(SNode 1 []);(SNode 2 [SNode 3 []])] []) = Some (TreeZip (SNode 3 []) [] [] [([SNode 1 []; SNode 0 []], 2, [])]).
  Proof. 
    (* match goal with
    | |- ?x = _ => let a := eval vm_compute in x in idtac a end. *)
  done. Qed.
End TreeZipperTests.

Notation " x '.this' " := (this x) (at level 3).
Notation " x '.before' " := (before x) (at level 3).
Notation " x '.after' " := (after x) (at level 3).
Notation " x '.parents' " := (parents x) (at level 3).
Notation " x '.forest' " := (forest x) (at level 3).

Definition parallel_construct_context : Type := nat.
            

(* the context for the current team executing region.
  Note that the parallel construct is not a team-executing construct.
  Every team_executing_context carries a nat, it is the corresponding pragma's index.
  The team would have to check  *)
Variant team_executing_context' :=
| team_ctx_for :
            (* The team workload split. Is A partition of iterations.
               A thread works on a chunk of iterations. *)
           (list $ list chunk) ->
           team_executing_context'
| team_ctx_single :
  (* the OpenMP thread number that identifies the thread that
     executes the single construct *)
  nat -> 
  team_executing_context'
| team_ctx_barrier : team_executing_context'
.
Definition team_executing_context : Type := (nat * team_executing_context').

(* we assume each pragma in the program have distinct index, and two teamcontexts
  come from the same pragma if they have the same index. *)
Definition matching_par_ctx (c1 c2: parallel_construct_context) : bool :=
  c1 =? c2.

(* two team executing contexts are the same if they have the same index and
   their corresponding team_executing_context' are the same. *)
Definition matching_tm_exec_ctx (c1 c2: team_executing_context) : bool :=
  c1.1 =? c2.1.

(* TODO fix variable convention: tz should always be the first or last argument *)
Section OpenMPThreads.

    (* OpenMP context for a thread in a parallel region *)
    Record o_ctx := {
      t_tid : nat; (* thread id *)
      (* every time we run a cothe th privatized variables and their original values *)
      (* o_thread_ctxs : list thread_context; *)
      (* o_team_ctxs fields exists iff this node has a team of children.
         o_team_ctxs.1 is for the parallel region enclosing the team;
         o_team_ctxs.2 exists iff some threads in the team are working in some team executing region.
      *)
      o_team_ctxs : option (parallel_construct_context * option team_executing_context);
    }.

    #[export] Instance settable_o_ctx : Settable _ :=
      settable! Build_o_ctx <t_tid; o_team_ctxs>.

    Section OpenMPTeam.

    (* team id -> team_tree *) 

    (**   (0)

           parallel(3)-> 

           [0]
        /  |  \   
      [(0), (1), (2)]]

            parallel(2) ->

           [0]
        /    |    \   
      [(0), [1], (2)]]
            / \
    [(0),[(0),(1)], (2)]]      
            
    *)

      (* model of the dynamics of a team. 
         Each node is either a thread with no children, which we call a leaf node, that represents an executing thread;
         or a thread that has children, which are the team that it spawned. This team includes the thread itself, and
         the parent node data contains bookkeeping info about this team. When the team is done, we can fire the team,
         and the parent thread recovers its previous state as a leaf node.
         The bookkeeping data of a team contains `Some privatized_vars` if the parallel region of the team (i.e. the lifetime
         span of the team) also contains a reduction clause. *)
      Definition team_tree := @stree (o_ctx).
      Definition team_zipper := @tree_zipper (o_ctx).

      Implicit Types (pvm : pv_map) (ot: o_ctx) (tree: team_tree) (tz ptz:team_zipper)
        (i: ident) (ge orig_ge: genv) (le orig_le: env)
        (ce:composite_env) (m: mem) (b:Values.block) (ty:type)
        (tm_exec_ctx: team_executing_context) (par_ctx: parallel_construct_context)
        (tid:nat).

      (* the first thread in the program *)
      Definition ot_init (tid: nat) : o_ctx := Build_o_ctx tid None.

      (* a team starts with just the main thread *)
      Definition team_tree_init (tid: nat) : team_tree := SNode (ot_init tid) [].

      Definition is_tid (tid: nat) (ot: o_ctx) : Prop :=
        ot.(t_tid) = tid.
      #[global] Instance is_tid_dec (tid: nat) (ot: o_ctx) : Decision (is_tid tid ot).
      Proof. apply Nat.eq_dec. Qed.

      Definition has_tid (tid: nat) (tz: team_zipper) : bool :=
        isSome $ tz_lookup (λ st, bool_decide $ is_tid tid $ st.data) tz.

      (* the list of all leaf threads *)
      Fixpoint tree_to_list (tree: team_tree) : (list o_ctx) :=
        match tree with
        | SNode ot ts =>
          match ts with
          | [] => [ot] (* leaf node*)
          | _ => concat (tree_to_list <$> ts)
          end
        end.

      Definition leaf_tids (t: team_tree) : list nat :=
        t_tid <$> tree_to_list t.

      Definition has_tid_spec (tid: nat) (tree: team_tree) : Prop :=
        In tid $ leaf_tids tree.

      Definition tid_unique (tree: team_tree) : Prop :=
        NoDup $ t_tid <$> tree_to_list tree.

      Record team_tree_inv (tree: team_tree) : Prop :=
        { inv_tid_unique : tid_unique tree }.

      (** folloing opeartions assume that tids in the trees are NoDup, and the indexing tid exists as a leaf
           node in the tree. *)
      (** spawns a team at every TeamLeaf that contains tid.
       * should require that tid is unique in tree.
       *)

      (* t is a leaf node and represents tid *)
      Definition is_leaf_tid' (tid: nat) (t: team_tree) : bool :=
        match t with
        | SNode ot [] => bool_decide (is_tid tid ot)
        | _ => false
        end.

      Definition is_leaf_tid (tid: nat) (tz: stree) : bool :=
        is_leaf_tid' tid tz.

      (* find the leaf node that represents tid *)
      Definition lookup_tid (tid: nat) (t: team_tree) : option team_zipper :=
        tz_lookup (is_leaf_tid tid) (from_stree t).

      Definition update_tid (tid: nat) t f : option team_tree :=
        stree_update (is_leaf_tid tid) f t.

      Definition parent_tree_of tid tz : option team_zipper :=
        tz ← tz_lookup (is_leaf_tid tid) tz;
        go_up tz.

      (* the parallel pragma spawns a team of threads, each gets initialized thread contexts;
         sets team_ctxs.1. *)
      Definition spawn_team (tid: nat) (team_mates: list nat) (spar_index:nat) t : option team_tree :=
        update_tid tid t (λ leaf, leaf <| kids := map team_tree_init (tid::team_mates) |>
                                       <| data; o_team_ctxs := Some (spar_index, None) |>).

      (* Maintenance of the team context when tid enters a team executing construct.
          if it is the first thread in the team that enters this construct <-> data.o_team_ctxs.2 is None,
          it sets data.o_team_ctxs.2 according to (idx, pragma);
          otherwise, someone else in the team has already entered a team executing construct, 
          and it must enter the same construct, so it checks whether (idx, pragma) corresponds to data.o_team_ctxs.2. *)
      Definition mate_maybe_add_team_exec_ctx tz tid tm_exec_ctx : option team_zipper :=
        parent ← parent_tree_of tid tz;
        tm_ctx ← parent.this.data.(o_team_ctxs);
        match tm_ctx.2 with
        | Some tm_exec_ctx' =>
          if matching_tm_exec_ctx tm_exec_ctx tm_exec_ctx'
          then Some tz
          else None
        | None => Some $ parent <| this; data; o_team_ctxs := Some (tm_ctx.1, Some tm_exec_ctx) |>
        end
      .

      (* find tid's teammates' thread ids, including tid.
         If tid is root, return itself. *)
      Definition team_mates_tids tid (t:team_tree) : option $ list nat :=
        ref ← lookup_tid tid t;
        Some $ map (λ x, x.data.(t_tid)) (forest ref).
      
      Lemma in_team_mates_tids tid ttree mates_tids :
        Some mates_tids = team_mates_tids tid ttree ->
        In tid mates_tids.
      Proof.
        intros. rewrite /team_mates_tids in H.
        destruct (lookup_tid tid ttree) eqn:?; last done.
        simpl in H. injection H; intros; subst.
        apply stree_lookup_correct in Heqo as [? ?].
        rewrite /is_leaf_tid /is_leaf_tid' in H0.
        rewrite map_app map_cons.
        apply in_or_app. right.
        destruct (t .this) eqn:?; try done.
        destruct l; try done.
        simpl. left.
        destruct (is_tid_dec tid o); done.
      Qed.

      (* pop the team executing context for the team that tid is in *)
      Definition team_pop_team_exec_context tz tid : option (team_zipper * team_executing_context) :=
        ptz ← parent_tree_of tid tz;
        tm_ctxs ← ptz.this.data.(o_team_ctxs);
        tm_exec_ctx ← tm_ctxs.2;
        let ptz' := ptz <| this; data; o_team_ctxs := Some (tm_ctxs.1, None) |> in
        Some (ptz', tm_exec_ctx).

      (*** ending a parallel construct ***)
      (* pop the parallel context for the team that tid is in *)
      Definition team_pop_parallel_context tz tid : option (team_zipper * parallel_construct_context) :=
        pref ← parent_tree_of tid tz;
        tm_ctxs ← pref.this.data.(o_team_ctxs);
        (* must not have any other team context (i.e. team_executing context) *)
        match tm_ctxs.2 with
        | Some _ => None
        | None => Some ( pref <| this; data; o_team_ctxs := None |>, tm_ctxs.1) end.

      (* there is no team context for the team of tid *)
      Definition team_context_resolved tz tid : bool :=
        match parent_tree_of tid tz with
        | Some pref => bool_decide (pref.this.data.(o_team_ctxs) = None)
        | None => false
        end.

      (* finish a team when there is no team or thread context left to resolve *)
      Definition team_fire tid tz : option team_zipper :=
        if team_context_resolved tz tid
        then pref ← parent_tree_of tid tz;
             Some $ (pref <| this; kids := [] |>)
        else None.

      (* returns the first i if f(l[i])=true. *)
      Fixpoint find_index {A:Type} (f: A->bool) (l:list A) : option nat :=
        match l with
        | [] => None
        | x::xs => if f x then Some 0 else
                   match find_index f xs with
                   | None => None
                   | Some n => Some (S n)
                   end
        end.
      
      (* thread num is the index to tid of parent tree's kids list. *)
      Definition get_thread_num tid tz : option nat :=
        ref ← parent_tree_of tid tz;
        find_index (is_leaf_tid' tid) ref.this.kids.

      (* tid is a leader of its current team if it's parent node has the same tid. *)
      Definition is_leader tid tz : bool :=
        match parent_tree_of tid tz with
        | None => true
        | Some pref => pref.this.data.(t_tid) =? tid
        end.

      Definition has_ectx_iff_team_executed tz tid (s_tag: construct_kind) : Prop :=
        ∃ tz_p: team_zipper, Some tz_p = parent_tree_of tid tz ∧
        ∃ pctx maybe_ectx, Some (pctx, maybe_ectx) = tz.this.data.(o_team_ctxs) ∧
        ((s_tag = ForConstruct ∨ s_tag = SingleConstruct) <-> isSome maybe_ectx).
      
      Definition tz_end_ctx tz tid (s_tag: construct_kind) idx : option team_zipper :=
        (* pref ← parent_tree_of tid tz;
        tm_ctxs ← ref.this.data.(o_team_ctxs); *)
        match s_tag with
        | ForConstruct =>
          tz_ectx ← team_pop_team_exec_context tz tid;
          let (tz, ectx) := (tz_ectx: (team_zipper * team_executing_context)) in
          match ectx with
          | (idx', team_ctx_for _) => if idx' =? idx then Some tz else None
          | _ => None
          end
        | SingleConstruct =>
          tz_ectx ← team_pop_team_exec_context tz tid;
          let (tz, ectx) := (tz_ectx: (team_zipper * team_executing_context)) in
          match ectx with
          | (idx', team_ctx_single _) => if idx' =? idx then Some tz else None
          | _ => None
          end
        | ParallelConstruct =>
          tz_pctx ← team_pop_parallel_context tz tid;
          let (tz, pctx) := (tz_pctx: (team_zipper * parallel_construct_context)) in
          if pctx =? idx then team_fire tid tz else None
        (* if executing an explicit barrier construct, the team cannot have an ectx *)
        | BarrierConstruct => None
        end.

    End OpenMPTeam.
End OpenMPThreads.