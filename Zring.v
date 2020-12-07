(* Ring of integers *)

Require Import Utf8 ZArith.

Require Import Semiring.

Definition phony_Z_inv (x : Z) := 0%Z.

Definition Z_ring_like_op : ring_like_op Z :=
  {| rngl_zero := 0%Z;
     rngl_one := 1%Z;
     rngl_add := Z.add;
     rngl_mul := Z.mul;
     rngl_opp := Z.opp;
     rngl_inv := phony_Z_inv |}.

Canonical Structure Z_ring_like_op.

Definition Z_ring_like_prop : ring_like_prop Z :=
  {| rngl_is_comm := true;
     rngl_has_opp := true;
     rngl_has_inv := false;
     rngl_add_comm := Z.add_comm;
     rngl_add_assoc := Z.add_assoc;
     rngl_add_0_l := Z.add_0_l;
     rngl_mul_assoc := Z.mul_assoc;
     rngl_mul_1_l := Z.mul_1_l;
     rngl_mul_add_distr_l := Z.mul_add_distr_l;
     rngl_c_mul_comm := Z.mul_comm;
     rngl_nc_mul_1_r := I;
     rngl_nc_mul_add_distr_r := I;
     rngl_o_add_opp_l := Z.add_opp_diag_l;
     rngl_no_mul_0_l := I;
     rngl_no_mul_0_r := I;
     rngl_i_mul_inv_l := I |}.

Theorem Z_1_neq_0 : 1%Z ≠ 0%Z.
Proof. easy. Qed.

Definition Z_ring_like_dec_prop : ring_like_dec_prop Z :=
  {| rngl_eq_dec := Z.eq_dec; rngl_1_neq_0 := Z_1_neq_0 |}.
