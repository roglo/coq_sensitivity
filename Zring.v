(* Ring of integers *)

Require Import Utf8 ZArith.

Require Import Semiring.

Definition Z_semiring_op : semiring_op Z :=
  {| srng_zero := 0%Z;
     srng_one := 1%Z;
     srng_add := Z.add;
     srng_mul := Z.mul |}.

Definition Z_ring_op : ring_op Z :=
  {| rng_opp := Z.opp |}.

Canonical Structure Z_semiring_op.
Canonical Structure Z_ring_op.

Definition Z_semiring_prop : semiring_prop Z :=
  {| srng_add_comm := Z.add_comm;
     srng_add_assoc := Z.add_assoc;
     srng_add_0_l := Z.add_0_l;
(*
     srng_mul_comm := Z.mul_comm;
*)
     srng_mul_assoc := Z.mul_assoc;
     srng_mul_1_l := Z.mul_1_l;
     srng_mul_add_distr_l := Z.mul_add_distr_l;
     srng_mul_0_l := Z.mul_0_l |}.

Definition Z_ring_prop : ring_prop Z :=
  {| rng_add_opp_l := Z.add_opp_diag_l |}.

Theorem Z_1_neq_0 : 1%Z ≠ 0%Z.
Proof. easy. Qed.

Definition Z_sring_dec_prop : sring_dec_prop Z :=
  {| srng_eq_dec := Z.eq_dec; srng_1_neq_0 := Z_1_neq_0 |}.
