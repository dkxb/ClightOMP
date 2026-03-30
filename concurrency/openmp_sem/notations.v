From Coq Require Import String ZArith.
From compcert Require Import Clightdefs AST.
From compcert Require Export -(notations) lib.Maps.
From stdpp Require Export base tactics.
Local Open Scope string_scope.
Local Open Scope clight_scope.
(* same as in Clightdefs, just redefine notation *)
Notation "$$ s" := (ltac:(ClightNotations.ident_of_string s))
                  (at level 1, only parsing) : clight_scope.

                  Definition __max : ident := $$"max".
                  Definition __min : ident := $$"min".

(* redefine compcert map notations since they conflict with stdpp *)
Notation "a ! b" := (PTree.get b a) (at level 1).
Notation "a !!!! b" := (PMap.get b a) (at level 1).

Ltac unfold_mbind_in_hyp := 
    lazymatch goal with
    | [ H : context[@mbind _ ?instance _ _ _] |- _] => unfold mbind in H; unfold instance in H
    end.

Ltac unfold_mbind :=
    lazymatch goal with
    | |- context[@mbind _ ?instance _ _ _] => unfold mbind; unfold instance
    end.

(* Helpers: find the first match/decide and apply do_destruct to the scrutinee.
   The decide case always uses [->|] regardless of the do_destruct continuation. *)
Ltac with_first_match_in_goal do_destruct :=
    lazymatch goal with
    | |- context[if (decide (?x = ?y)) then _ else _] => destruct (decide (x = y)) as [->|]; try done
    | |- context[match (match ?x with _ => _ end) with _ => _ end] => do_destruct x
    | |- context[match ?x with _ => _ end] => do_destruct x
    end.

Ltac with_first_match_in H do_destruct :=
    lazymatch type of H with
    | context[if (decide (?x = ?y)) then _ else _] => destruct (decide (x = y)) as [->|]; try done
    | context[match (match ?x with _ => _ end) with _ => _ end] => do_destruct x
    | context[match ?x with _ => _ end] => do_destruct x
    end.

Ltac with_first_match_in_hyps do_destruct :=
    lazymatch goal with
    | [ _ : context[if (decide (?x = ?y)) then _ else _] |- _] => destruct (decide (x = y)) as [->|]; try done
    | [ _ : context[match (match ?x with _ => _ end) with _ => _ end] |- _] => do_destruct x
    | [ _ : context[match ?x with _ => _ end] |- _] => do_destruct x
    end.

(* TODO rename these;
   destruct the first pattern matching in goal *)
Tactic Notation "destruct_match" :=
  with_first_match_in_goal ltac:(fun x => destruct x; try done).
Tactic Notation "destruct_match"                "eqn" ":" ident(H2) :=
  with_first_match_in_goal ltac:(fun x => destruct x eqn:H2; try done).
Tactic Notation "destruct_match"                "eqn" ":" "?" :=
  with_first_match_in_goal ltac:(fun x => destruct x eqn:?; try done).

Tactic Notation "destruct_match" "in" ident(H1) :=
  with_first_match_in H1   ltac:(fun x => destruct x; try done).
Tactic Notation "destruct_match" "in" ident(H1) "eqn" ":" ident(H2) :=
  with_first_match_in H1   ltac:(fun x => destruct x eqn:H2; try done).
Tactic Notation "destruct_match" "in" ident(H1) "eqn" ":" "?" :=
  with_first_match_in H1   ltac:(fun x => destruct x eqn:?; try done).

Tactic Notation "destruct_match" "in" "*" :=
  with_first_match_in_hyps ltac:(fun x => destruct x; try done).
Tactic Notation "destruct_match" "in" "*" "eqn" ":" ident(H2) :=
  with_first_match_in_hyps ltac:(fun x => destruct x eqn:H2; try done).
Tactic Notation "destruct_match" "in" "*" "eqn" ":" "?" :=
  with_first_match_in_hyps ltac:(fun x => destruct x eqn:?; try done).

(* look for a match in both goal and hyps, and destruct the first one *)
Tactic Notation "destruct_match!" :=
  progress (
    destruct_match in * eqn:? ||
    destruct_match eqn:?
  ).

(* mbind but allows filling in the MBind typeclass instance explicitly *)
Notation "m '≫=@{' M '}' f" := (@mbind _ M _ _ f m) (at level 60, right associativity) : stdpp_scope.
