(* fields *)

(*
Set Implicit Arguments.
*)

Require Import Utf8.
Require Import Semiring.

Class field_op T :=
  { fld_inv : T → T }.

Definition fld_div T {fo : field_op T} {so : semiring_op T} a b :=
  srng_mul a (fld_inv b).

Declare Scope field_scope.

Delimit Scope field_scope with F.
Notation "0" := (@srng_zero _ _) : field_scope.
Notation "1" := (@srng_one _ _) : field_scope.
Notation "- a" := (@rng_opp _ _ a) : field_scope.
Notation "/ a" := (@fld_inv _ _ a) : field_scope.
Notation "a + b" := (@srng_add _ _ a b) : field_scope.
Notation "a - b" := (@rng_sub _ _ _ a b) : field_scope.
Notation "a * b" := (@srng_mul _ _ a b) : field_scope.
Notation "a / b" := (@fld_div _ _ _ a b) : field_scope.

Class field_prop A {so : semiring_op A} {fo : field_op A} :=
  { fld_mul_inv_l : ∀ a : A, a ≠ 0%F → (/ a * a = 1)%F }.
