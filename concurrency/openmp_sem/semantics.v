(* a fork of concurrency/common/semantics.v *)
From mathcomp.ssreflect Require Import ssreflect seq ssrbool.
Require Import VST.concurrency.openmp_sem.event_semantics.

(** *The typeclass version*)
Class Semantics:=
  {
    (* semF: Type ;
  semV: Type; *)
    semG: Type;
    semC: Type;
    semSem: @EvSem semC;
    (* getEnv : semG -> Genv.t semF semV *)
    the_ge: semG
  }.

Class Resources:=
  {
    res: Type;
    lock_info : Type
  }.

(** The Module version *)

Module Type SEMANTICS.
  Parameter G : Type.
  Parameter C : Type.
  Parameter SEM : @EvSem C.
End SEMANTICS.
