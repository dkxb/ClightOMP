(* "small" memory that ignores properties of compcert mem *)
From Coq Require Import List. Import ListNotations.
From compcert Require Import Memory Coqlib Values.
From VST.concurrency.openmp_sem Require Import notations.

Record smem' : Type := mksmem {
  smem_contents: list (list memval);  (**r [block -> ZIndexed.index offset -> memval] *)
  smem_access: list (list (option permission * option permission));
                                         (**r [block -> offset -> (current * max permission)]. undef Permissions are none here *)
  smem_nextblock: block;
  smem_max_offset_index : positive ; (* keep track of the max (ZIndexed.index offset) used for any block. This ensures to_mem is deterministic. *)
}.

Definition smem := smem'.

Definition empty: smem :=
  mksmem []
         []
         1%positive
         (ZIndexed.index 0%Z).

Definition foldr {A B} (f: nat -> B -> A -> A) (a: A) (l: list B) : A :=
  fold_right (λ b_i, f (fst b_i) (snd b_i) ) a (combine (seq 0 (length l)) l).

Definition smem_contents_mem_contents (sc: list (list memval)) : PMap.t (ZMap.t memval) :=
  fold_right (λ (b:list memval) c,
    
  ) PMap.empty sc.

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

