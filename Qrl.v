(* ℚ is a ring-like with inverse *)
(* i.e. it is a field *)

Set Implicit Arguments.
Require Import Utf8.

Require Import RingLike Rational.
Import Q.Notations.

Definition phony_Q_sub (a b : Q) := a.
Definition phony_Q_div (a b : Q) := a.

Canonical Structure Q_ring_like_op : ring_like_op Q :=
  {| rngl_has_opp := true;
     rngl_has_inv := true;
     rngl_has_no_inv_but_div := false;
     rngl_is_ordered := true;
     rngl_zero := 0%Q;
     rngl_one := 1%Q;
     rngl_add := Q.add;
     rngl_mul := Q.mul;
     rngl_opp := Q.opp;
     rngl_inv := Q.inv;
     rngl_le := Q.le;
     rngl_opt_sub := phony_Q_sub;
     rngl_opt_div := phony_Q_div |}.

Existing Instance Q_ring_like_op.

Theorem Q_1_neq_0 : (1 ≠ 0)%Q.
Proof. easy. Qed.

Theorem Q_characteristic_prop : ∀ i, rngl_of_nat (S i) ≠ 0%Q.
Proof.
intros.
cbn - [ Q.add ].
assert (Hz : ∀ i, (0 ≤ rngl_of_nat i)%Q). {
  clear i; intros.
  cbn - [ Q.add ].
  induction i; [ easy | ].
  cbn - [ Q.add ].
  now destruct (rngl_of_nat i).
}
intros H.
specialize (Hz i).
apply Q.nlt_ge in Hz; apply Hz.
rewrite <- H.
apply Q.lt_sub_lt_add_r.
now rewrite Q.sub_diag.
Qed.

Theorem Q_mul_le_compat_nonneg : ∀ a b c d,
  (0 ≤ a ≤ c → 0 ≤ b ≤ d → a * b ≤ c * d)%Q.
Proof.
intros * Hac Hbd.
now apply Q.mul_le_mono_nonneg.
Qed.

Theorem Q_mul_le_compat_nonpos : ∀ a b c d,
  (c ≤ a ≤ 0 → d ≤ b ≤ 0 → a * b ≤ c * d)%F.
Proof.
intros * Hac Hbd.
now apply Q.mul_le_mono_nonpos.
Qed.

Theorem Q_not_le : ∀ a b, ¬ (a ≤ b)%Q → a = b ∨ (b ≤ a)%Q.
Proof.
intros * Hab.
destruct (Q.eq_dec a b) as [Heab| Heab]; [ now left | right ].
apply Q.nle_gt in Hab.
apply Q.nlt_ge; intros Hba.
apply Heab.
now apply Q.le_antisymm; apply Q.lt_le_incl.
Qed.

Theorem Q_consistent : rngl_has_inv = false ∨ rngl_has_no_inv_but_div = false.
Proof. now right. Qed.

Definition Q_ring_like_prop :=
  {| rngl_is_comm := true;
     rngl_has_dec_eq := true;
     rngl_has_dec_le := true;
     rngl_has_1_neq_0 := true;
     rngl_is_integral := false;
     rngl_characteristic := 0;
     rngl_add_comm := Q.add_comm;
     rngl_add_assoc := Q.add_assoc;
     rngl_add_0_l := Q.add_0_l;
     rngl_mul_assoc := Q.mul_assoc;
     rngl_mul_1_l := Q.mul_1_l;
     rngl_mul_add_distr_l := Q.mul_add_distr_l;
     rngl_opt_1_neq_0 := Q_1_neq_0;
     rngl_opt_mul_comm := Q.mul_comm;
     rngl_opt_mul_1_r := I;
     rngl_opt_mul_add_distr_r := I;
     rngl_opt_add_opp_l := Q.add_opp_diag_l;
     rngl_opt_add_sub := I;
     rngl_opt_mul_0_l := I;
     rngl_opt_mul_0_r := I;
     rngl_opt_mul_inv_l := Q.mul_inv_l;
     rngl_opt_mul_inv_r := I;
     rngl_opt_mul_div_l := I;
     rngl_opt_mul_div_r := I;
     rngl_opt_eq_dec := Q.eq_dec;
     rngl_opt_le_dec := Q.le_dec;
     rngl_opt_integral := I;
     rngl_characteristic_prop := Q_characteristic_prop;
     rngl_opt_le_refl := Q.le_refl;
     rngl_opt_le_antisymm := Q.le_antisymm;
     rngl_opt_le_trans := Q.le_trans;
     rngl_opt_add_le_compat := Q.add_le_mono;
     rngl_opt_mul_le_compat_nonneg := Q_mul_le_compat_nonneg;
     rngl_opt_mul_le_compat_nonpos := Q_mul_le_compat_nonpos;
     rngl_opt_mul_le_compat := I;
     rngl_opt_not_le := Q_not_le;
     rngl_consistent := Q_consistent |}.
