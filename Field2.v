(* fields *)

Set Implicit Arguments.

Require Import Utf8.
Require Import Semiring.

Class field_op T :=
  { fld_inv : T → T }.

Definition fld_div T {fo : field_op T} {so : semiring_op T} a b :=
  srng_mul a (fld_inv b).

Declare Scope field_scope.

Delimit Scope field_scope with F.
Notation "0" := srng_zero : field_scope.
Notation "1" := srng_one : field_scope.
Notation "- a" := (rng_opp a) : field_scope.
Notation "/ a" := (fld_inv a) : field_scope.
Notation "a + b" := (srng_add a b) : field_scope.
Notation "a - b" := (rng_sub a b) : field_scope.
Notation "a * b" := (srng_mul a b) : field_scope.
Notation "a / b" := (fld_div a b) : field_scope.
