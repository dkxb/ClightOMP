
From compcert Require Import Clight Cop Clightdefs AST Integers Ctypes Values Memory Events Globalenvs.
From VST.concurrency.openmp_sem Require Import notations permissions.
From stdpp Require Import base list.
From mathcomp Require Import ssreflect.

Section PermissionFun.
#[export] Instance perm_order''_dec_inst : RelDecision Mem.perm_order''.
Proof. unfold RelDecision. apply perm_order''_dec. Defined.

Definition block_perm_lt  :    (t1 t2: PTree.t (Z → option permission)): .

Lemma simple_permMapLt (p1 p2 : access_map) :
    p1.1 = (λ z, None) →
    p2.1 = (λ z, None) →
    p1.2 < p2.2 →
    permMapLt p1 p2.

#[export] Instance permMapLt_dec : p1=(λ , None) Decision permMapLt p1 p2.
Proof.
    unfold RelDecision. intros.
    unfold permMapLt.
    unfold Mem.perm_order''.
    destruct x as [x1 x2] eqn:Hx, y as [y1 y2] eqn:Hy.
    (* i∈x2,y2 -> x2[i]<y2[i] *)
    (* i∈x2, i∉y2 -> x2[i]< *)
 
    (* lookup in PTree is finite *)
    rewrite /PMap.get /=.
 
    unfold Decision.
    Search (_ -> (Decision (∀ _, _))).
    apply .
    destruct (x !!!! b ofs), (y !!!! b ofs).
    
    destruct x as [o t] eqn:?.
