(* "small" memory that ignores properties of compcert mem *)
From Coq Require Import List. Import ListNotations.
From stdpp Require Import -(notations) base.
From VST.concurrency Require Import notations.
From compcert Require Import Memory Coqlib Values.


Record smem' : Type := mksmem {
  smem_contents: list (list memval * list memval);  (**r [block -> (non-negative part of a block * negative part of a block)] *)
  smem_access: list (list (option permission * option permission) *
                     list (option permission * option permission));
    (**r [block -> 
      [(current * max permission) for the non-neg * negative part of a block].
      Undef Permissions are none here *)
  smem_nextblock: block;
  smem_max_offset_index : positive ; (* keep track of the max (ZIndexed.index offset) used for any block. This ensures to_mem is deterministic. *)
}.

Definition smem := smem'.

Definition empty: smem :=
  mksmem []
         []
         1%positive
         (ZIndexed.index 0%Z).

Definition idx : Type := nat.

(* foldr, but also has access to the index *)
Definition foldr {A B} (f: idx -> B -> A -> A) (a: A) (l: list B) : A :=
  fold_right (λ b_i, f (b_i).1 (b_i).2) a (combine (seq 0 (length l)) l).

(* encode block offset, Z, in idx with a bijection *)
Definition ofs_to_idx (ofs: Z) : idx :=
  ((Z.to_nat (ofs * 2)) - (if (ofs <? 0)%Z then 1 else 0))%nat.

(* decode block offset from block offset *)
Definition idx_to_ofs (i: idx) : Z :=
  

  (* Zindex_to_Z is the inverse of ZIndexed.index *)
Definition Zindex_to_Z (i: positive) : Z :=
  match i with
  | xH => Z0
  | xO p => Zpos p
  | xI p => Zneg p
  end.
  
Lemma Zindex_to_Z_spec (z: Z) : Zindex_to_Z (ZIndexed.index z) = z.
Proof. by destruct z. Qed.


Definition smem_block_mem_block (sb: list memval) : ZMap.t memval :=
  foldr (λ i sb_i b, ZMap.set (Z.of_nat i) sb_i b) (ZMap.init Undef) sb.

Definition smem_contents_mem_contents (sc: list (list memval)) : PMap.t (ZMap.t memval) :=
  foldr (λ i (sb:list memval) c,
    PMap.set (Pos.of_nat i) (smem_block_mem_block sb) c
  ) (PMap.init (ZMap.init Undef)) sc.


Definition smem_block_access_mem_block_access (sb: list (option permission * option permission)) : ZMap.t (option permission * option permission) :=
  foldr (λ i sb_i f, (λ ofs k,
    if (ofs =? (Z.of_nat i)) then
    match k with | Cur => sb_i.1 | Max => sb_i.2 end
    else f ofs k)) (λ ofs k, None) sb.

Definition smem_access_mem_access (sa: list (list (option permission * option permission))) : PMap.t (ZMap.t (option permission * option permission)) :=
  foldr (λ i sa_i a,
    PMap.set (Pos.of_nat i) (foldr (λ j sa_ij a, ZMap.set (Z.of_nat j) sa_ij a) (ZMap.init None) sa_i) a
  ) (PMap.init (ZMap.init None)) sa.

Definition to_mem (m: smem) : mem :=
  let contents := smem_contents m in
  let access := smem_access m in
  let nextblock := smem_nextblock m in
  let max_offset := smem_max_offset m in
  {|
    Mem.mem_contents := contents;
    Mem.mem_access := access;
    Mem.nextblock := nextblock;
    Mem.max_offset := max_offset;

  |}.

