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

Theorem Z_eq_mul_0 :  ∀ n m, (n * m)%Z = 0%Z → n = 0%Z ∨ m = 0%Z.
Proof. now apply Z.eq_mul_0. Qed.

Definition Z_ring_like_prop : ring_like_prop Z :=
  {| rngl_is_comm := true;
     rngl_has_opp := true;
     rngl_has_inv := false;
     rngl_has_dec_eq := true;
     rngl_is_integral_not_provable := true;
     rngl_add_comm := Z.add_comm;
     rngl_add_assoc := Z.add_assoc;
     rngl_add_0_l := Z.add_0_l;
     rngl_mul_assoc := Z.mul_assoc;
     rngl_mul_1_l := Z.mul_1_l;
     rngl_mul_add_distr_l := Z.mul_add_distr_l;
     rngl_opt_mul_comm := Z.mul_comm;
     rngl_opt_mul_1_r := I;
     rngl_opt_mul_add_distr_r := I;
     rngl_opt_add_opp_l := Z.add_opp_diag_l;
     rngl_opt_mul_0_l := I;
     rngl_opt_mul_0_r := I;
     rngl_opt_mul_inv_l := I;
     rngl_opt_eq_dec := Z.eq_dec;
     rngl_opt_is_integral := Z_eq_mul_0 |}.
