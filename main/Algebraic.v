(* attempt to define algebraic numbers *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List ListNotations Init.Nat.

Require Import Misc RingLike.
Require Import Polynomial Matrix.

(* Sylvester matrix *)

Section a.

Context {A : Type}.
Context {ro : ring_like_op A}.

Definition rlap_sylvester_list_list (rp rq : list A) : list (list A) :=
  let m := length rp in
  let n := length rq in
  repeat (repeat 0%L (m + n)) (m + n). 

End a.

About rlap_sylvester_list_list.

Require Import RnglAlg.Qrl.
Require Import RnglAlg.Rational.
Import Q.Notations.
Open Scope Q_scope.

Compute (rlap_sylvester_list_list [1;2;3;4] [5;6;7]).
