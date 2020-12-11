(* field of rationals *)

Set Implicit Arguments.
Require Import Utf8.

Require Import RingLike Rational.
Import Q.Notations.

Canonical Structure Q_ring_like_op : ring_like_op Q :=
  {| rngl_zero := 0%Q;
     rngl_one := 1%Q;
     rngl_add := Q.add;
     rngl_mul := Q.mul;
     rngl_opp := Q.opp;
     rngl_inv := Q.inv |}.

Theorem Q_1_neq_0 : (1 ≠ 0)%Q.
Proof. easy. Qed.

Definition Q_ring_like_prop :=
  {| rngl_is_comm := true;
     rngl_has_opp := true;
     rngl_has_inv := true;
     rngl_has_dec_eq := true;
     rngl_is_domain := false;
     rngl_add_comm := Q.add_comm;
     rngl_add_assoc := Q.add_assoc;
     rngl_add_0_l := Q.add_0_l;
     rngl_mul_assoc := Q.mul_assoc;
     rngl_mul_1_l := Q.mul_1_l;
     rngl_mul_add_distr_l := Q.mul_add_distr_l;
     rngl_1_neq_0 := Q_1_neq_0;
     rngl_opt_mul_comm := Q.mul_comm;
     rngl_opt_mul_1_r := I;
     rngl_opt_mul_add_distr_r := I;
     rngl_opt_add_opp_l := Q.add_opp_diag_l;
     rngl_opt_mul_0_l := I;
     rngl_opt_mul_0_r := I;
     rngl_opt_mul_inv_l := Q.mul_inv_l;
     rngl_opt_mul_inv_r := I;
     rngl_opt_eq_dec := Q.eq_dec;
     rngl_opt_is_integral := I |}.
