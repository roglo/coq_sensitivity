(* Ring of integers *)

Require Import Utf8 ZArith.

Require Import RingLike.

Definition phony_Z_inv (x : Z) := 0%Z.

Canonical Structure Z_ring_like_op : ring_like_op Z :=
  {| rngl_zero := 0%Z;
     rngl_one := 1%Z;
     rngl_add := Z.add;
     rngl_mul := Z.mul;
     rngl_opp := Z.opp;
     rngl_inv := phony_Z_inv |}.

Theorem Z_mul_eq_0 :  ∀ n m, (n * m)%Z = 0%Z → n = 0%Z ∨ m = 0%Z.
Proof. now apply Z.mul_eq_0. Qed.

Definition Z_ring_like_prop : ring_like_prop Z :=
  {| rngl_is_comm := true;
     rngl_has_opp := true;
     rngl_has_inv := false;
     rngl_eq_is_dec := true;
     rngl_is_integral := true;
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
     rngl_i_mul_inv_l := I;
     rngl_d_eq_dec := Z.eq_dec;
     rngl_i_is_integral := Z_mul_eq_0 |}.

Theorem Z_1_neq_0 : 1%Z ≠ 0%Z.
Proof. easy. Qed.

Definition Z_ring_like_one_neq_zero_prop : ring_like_one_neq_zero Z :=
  {| rngl_1_neq_0 := Z_1_neq_0 |}.
