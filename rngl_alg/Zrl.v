(* ℤ is a ring-like, i.e. a ring *)

Require Import Utf8.
Require Import ZArith.

Require Import Main.RingLike.

Notation "x ≤ y" := (x <= y)%Z (at level 70, y at next level) : Z_scope.
Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%Z (at level 70, y at next level) :
  Z_scope.

Canonical Structure Z_ring_like_op : ring_like_op Z :=
  {| rngl_zero := 0%Z;
     rngl_one := 1%Z;
     rngl_add := Z.add;
     rngl_mul := Z.mul;
     rngl_opt_opp_or_subt := Some (inl Z.opp);
     rngl_opt_inv_or_quot := Some (inr Z.quot);
     rngl_opt_eqb := Some Z.eqb;
     rngl_opt_le := Some Z.le |}.

(*
Global Existing Instance Z_ring_like_op.
*)

Theorem Z_eq_mul_0 :  ∀ n m, (n * m)%Z = 0%Z → n = 0%Z ∨ m = 0%Z.
Proof. now apply Z.eq_mul_0. Qed.

Theorem Z_characteristic_prop :
  let roz := Z_ring_like_op in
  ∀ i, rngl_of_nat (S i) ≠ 0%Z.
Proof.
intros.
cbn - [ Z.add ].
assert (Hz : ∀ i, (0 <= rngl_of_nat i)%Z). {
  clear i; intros.
  cbn - [ Z.add ].
  induction i; [ easy | ].
  cbn - [ Z.add ].
  now destruct (rngl_of_nat i).
}
intros H.
specialize (Hz i).
apply Z.nlt_ge in Hz; apply Hz.
rewrite <- H.
apply Z.lt_sub_lt_add_r.
now rewrite Z.sub_diag.
Qed.

Theorem Z_mul_le_compat_nonneg : ∀ a b c d,
  (0 ≤ a ≤ c → 0 ≤ b ≤ d → a * b ≤ c * d)%Z.
Proof.
intros * Hac Hbd.
now apply Z.mul_le_mono_nonneg.
Qed.

Theorem Z_mul_le_compat_nonpos :
  let roz := Z_ring_like_op in
  ∀ a b c d, (c ≤ a ≤ 0 → d ≤ b ≤ 0 → a * b ≤ c * d)%L.
Proof.
intros * Hac Hbd.
now apply Z.mul_le_mono_nonpos.
Qed.

Theorem Z_not_le : ∀ a b, ¬ (a ≤ b)%Z → a = b ∨ (b ≤ a)%Z.
Proof.
intros * Hab.
destruct (Z.eq_dec a b) as [Heab| Heab]; [ now left | right ].
apply Z.nle_gt in Hab.
apply Z.nlt_ge; intros Hba.
apply Heab.
now apply Z.le_antisymm; apply Z.lt_le_incl.
Qed.

Definition Z_ring_like_prop : ring_like_prop Z :=
  {| rngl_mul_is_comm := true;
     rngl_has_dec_le := true;
     rngl_is_integral := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := Z.add_comm;
     rngl_add_assoc := Z.add_assoc;
     rngl_add_0_l := Z.add_0_l;
     rngl_mul_assoc := Z.mul_assoc;
     rngl_mul_1_l := Z.mul_1_l;
     rngl_mul_add_distr_l := Z.mul_add_distr_l;
     rngl_opt_mul_comm := Z.mul_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_l := Z.add_opp_diag_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_mul_sub_distr_l := NA;
     rngl_opt_mul_sub_distr_r := NA;
     rngl_opt_mul_inv_l := NA;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_mul_div := Z.quot_mul;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_eqb_eq := Z.eqb_eq;
     rngl_opt_le_dec := Z_le_dec;
     rngl_opt_integral := Z_eq_mul_0;
     rngl_opt_alg_closed := NA;
     rngl_characteristic_prop := Z_characteristic_prop;
     rngl_opt_le_refl := Z.le_refl;
     rngl_opt_le_antisymm := Z.le_antisymm;
     rngl_opt_le_trans := Z.le_trans;
     rngl_opt_add_le_compat := Z.add_le_mono;
     rngl_opt_mul_le_compat_nonneg := Z_mul_le_compat_nonneg;
     rngl_opt_mul_le_compat_nonpos := Z_mul_le_compat_nonpos;
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := Z_not_le |}.
