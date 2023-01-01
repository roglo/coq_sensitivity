Set Nested Proofs Allowed.
Require Import Utf8 Reals.
Require Import Main.RingLike.

Canonical Structure reals_ring_like_op : ring_like_op R :=
  {| rngl_zero := R0;
     rngl_one := R1;
     rngl_add := Rplus;
     rngl_mul := Rmult;
     rngl_opt_opp_or_sous := Some (inl Ropp);
     rngl_opt_inv_or_quot := Some (inl Rinv);
     rngl_opt_eqb := None;
     rngl_opt_le := Some Rle |}.

Canonical Structure reals_ring_like_prop : ring_like_prop R :=
  {| rngl_mul_is_comm := true;
     rngl_has_dec_le := false;
     rngl_is_integral := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := Rplus_comm;
     rngl_add_assoc := ?rngl_add_assoc;
     rngl_add_0_l := ?rngl_add_0_l;
     rngl_mul_assoc := ?rngl_mul_assoc;
     rngl_mul_1_l := ?rngl_mul_1_l;
     rngl_mul_add_distr_l := ?rngl_mul_add_distr_l;
     rngl_opt_mul_comm := ?rngl_opt_mul_comm;
     rngl_opt_mul_1_r := ?rngl_opt_mul_1_r;
     rngl_opt_mul_add_distr_r := ?rngl_opt_mul_add_distr_r;
     rngl_opt_add_opp_l := ?rngl_opt_add_opp_l;
     rngl_opt_add_sub := ?rngl_opt_add_sub;
     rngl_opt_sub_sub_sub_add := ?rngl_opt_sub_sub_sub_add;
     rngl_opt_mul_sub_distr_l := ?rngl_opt_mul_sub_distr_l;
     rngl_opt_mul_sub_distr_r := ?rngl_opt_mul_sub_distr_r;
     rngl_opt_mul_inv_l := ?rngl_opt_mul_inv_l;
     rngl_opt_mul_inv_r := ?rngl_opt_mul_inv_r;
     rngl_opt_mul_div := ?rngl_opt_mul_div;
     rngl_opt_mul_quot_r := ?rngl_opt_mul_quot_r;
     rngl_opt_eqb_eq := ?rngl_opt_eqb_eq;
     rngl_opt_le_dec := ?rngl_opt_le_dec;
     rngl_opt_integral := ?rngl_opt_integral;
     rngl_opt_alg_closed := ?rngl_opt_alg_closed;
     rngl_characteristic_prop := ?rngl_characteristic_prop;
     rngl_opt_le_refl := ?rngl_opt_le_refl;
     rngl_opt_le_antisymm := ?rngl_opt_le_antisymm;
     rngl_opt_le_trans := ?rngl_opt_le_trans;
     rngl_opt_add_le_compat := ?rngl_opt_add_le_compat;
     rngl_opt_mul_le_compat_nonneg := ?rngl_opt_mul_le_compat_nonneg;
     rngl_opt_mul_le_compat_nonpos := ?rngl_opt_mul_le_compat_nonpos;
     rngl_opt_mul_le_compat := ?rngl_opt_mul_le_compat;
     rngl_opt_not_le := ?rngl_opt_not_le |}.
