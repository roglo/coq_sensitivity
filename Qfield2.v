(* field of rationals *)

Set Implicit Arguments.

Require Import Utf8.

Require Import Semiring Field2 Rational.
Import Q.Notations.

Definition Q_semiring_op : semiring_op Q :=
  {| srng_zero := 0%Q;
     srng_one := 1%Q;
     srng_add := Q.add;
     srng_mul := Q.mul |}.

Definition Q_ring_op : ring_op Q := {| rng_opp := Q.opp |}.

Canonical Structure Q_semiring_op.
Canonical Structure Q_ring_op.

Theorem Q_1_neq_0 : 1%Q ≠ 0%Q.
Proof. easy. Qed.

Definition Q_sring_dec_prop : sring_dec_prop Q :=
  {| srng_eq_dec := Q.eq_dec; srng_1_neq_0 := Q_1_neq_0 |}.

Definition Q_field_op : field_op Q :=
  {| fld_inv := Q.inv |}.
