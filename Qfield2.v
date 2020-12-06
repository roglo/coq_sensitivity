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

Definition Q_semiring_prop :=
  {| srng_is_comm := true;
     srng_add_comm := Q.add_comm;
     srng_add_assoc := Q.add_assoc;
     srng_add_0_l := Q.add_0_l;
(*
     srng_mul_comm := Q.mul_comm;
*)
     srng_mul_assoc := Q.mul_assoc;
     srng_mul_1_l := Q.mul_1_l;
     srng_mul_add_distr_l := Q.mul_add_distr_l;
     srng_mul_0_l := Q.mul_0_l |}.

Definition Q_ring_prop := {| rng_add_opp_l := Q.add_opp_diag_l |}.

Theorem Q_1_neq_0 : 1%Q ≠ 0%Q.
Proof. easy. Qed.

Definition Q_sring_dec_prop : sring_dec_prop Q :=
  {| srng_eq_dec := Q.eq_dec; srng_1_neq_0 := Q_1_neq_0 |}.

Definition Q_field_op : field_op Q :=
  {| fld_inv := Q.inv |}.

Canonical Structure Q_field_op.

Definition Q_field_prop : field_prop Q :=
  {| fld_mul_inv_l := Q.mul_inv_l |}.
