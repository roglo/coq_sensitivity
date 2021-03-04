(* ℤ is a ring-like, i.e. a ring *)

Require Import Utf8 ZArith.

Require Import RingLike.

Notation "x ≤ y" := (x <= y)%Z (at level 70, y at next level) : Z_scope.
Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%Z (at level 70, y at next level) :
  Z_scope.

Canonical Structure Z_ring_like_op : ring_like_op Z :=
  {| rngl_zero := 0%Z;
     rngl_one := 1%Z;
     rngl_add := Z.add;
     rngl_mul := Z.mul;
     rngl_opt_opp := Some Z.opp;
     rngl_opt_inv := None;
     rngl_opt_monus := None;
     rngl_opt_eucl_div := Some (Z.div_eucl, Z.abs_nat);
     rngl_le := Z.le |}.

Existing Instance Z_ring_like_op.

Theorem Z_eq_mul_0 :  ∀ n m, (n * m)%Z = 0%Z → n = 0%Z ∨ m = 0%Z.
Proof. now apply Z.eq_mul_0. Qed.

Theorem Z_1_neq_0 : (1 ≠ 0)%Z.
Proof. easy. Qed.

Theorem Z_characteristic_prop : ∀ i, rngl_of_nat (S i) ≠ 0%Z.
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

Theorem Z_mul_div_l : ∀ a b : Z, a ≠ 0%F → (a * b / a)%F = b.
Proof.
intros * Haz.
rewrite Z.mul_comm.
now apply Z.div_mul.
Qed.

Theorem Z_eucl_div_prop : ∀ a b q r : Z,
  b ≠ 0%Z
  → rngl_eucl_div a b = (q, r)
  → a = (b * q + r)%F ∧ Z.abs_nat r < Z.abs_nat b.
Proof.
intros * Hbz Hab.
cbn in Hab.
specialize (Z_div_mod_full a b Hbz) as H1.
rewrite Hab in H1.
destruct H1 as (H1, H2).
split; [ easy | ].
unfold Remainder in H2.
destruct H2 as [H2| H2]; [ now apply Zabs_nat_lt | ].
destruct b as [| b| b]; [ easy | | ]. {
  destruct H2 as (H2, H3).
  apply Z.nle_gt in H2.
  exfalso; apply H2; clear H2.
  transitivity 0%Z; [ easy | ].
  apply Zle_0_pos.
}
destruct r as [| r| r]. {
  apply Pos2Nat.is_pos.
} {
  destruct H2 as (H2, H3).
  apply Z.nlt_ge in H3.
  exfalso; apply H3; clear H3.
  apply Pos2Z.pos_is_pos.
}
cbn.
destruct H2 as (H2, H3).
apply Pos2Nat.inj_lt.
apply Pos.lt_nle.
intros H.
apply Pos2Z.neg_le_neg in H.
now apply Z.nlt_ge in H.
Qed.

Theorem Z_gauge_prop : ∀ a b : Z,
  a ≠ 0%F
  → b ≠ 0%F
  → rngl_gauge a ≤ rngl_gauge (a * b)%F ∧ rngl_gauge b ≤ rngl_gauge (a * b)%F.
Proof.
intros * Haz Hbz; cbn.
assert (∀ a b, a ≠ 0%F → b ≠ 0%F → Z.abs_nat a ≤ Z.abs_nat (a * b)). {
  clear a b Haz Hbz; intros * Haz Hbz.
  destruct a as [| a| a]; [ apply Nat.le_0_l | | ]. {
    destruct b as [| b| b]; cbn; [ easy | | ]. {
      apply Pos2Nat.inj_le.
      remember (a * b)%positive as x.
      rewrite <- (Pos.mul_1_r a); subst x.
      apply Pos.mul_le_mono_l.
      apply Pos.le_1_l.
    } {
      apply Pos2Nat.inj_le.
      remember (a * b)%positive as x.
      rewrite <- (Pos.mul_1_r a); subst x.
      apply Pos.mul_le_mono_l.
      apply Pos.le_1_l.
    }
  } {
    destruct b as [| b| b]; cbn; [ easy | | ]. {
      apply Pos2Nat.inj_le.
      remember (a * b)%positive as x.
      rewrite <- (Pos.mul_1_r a); subst x.
      apply Pos.mul_le_mono_l.
      apply Pos.le_1_l.
    } {
      apply Pos2Nat.inj_le.
      remember (a * b)%positive as x.
      rewrite <- (Pos.mul_1_r a); subst x.
      apply Pos.mul_le_mono_l.
      apply Pos.le_1_l.
    }
  }
}
split; [ now apply H | ].
rewrite Z.mul_comm.
now apply H.
Qed.

Theorem Z_mul_le_compat_nonneg : ∀ a b c d,
  (0 ≤ a ≤ c → 0 ≤ b ≤ d → a * b ≤ c * d)%Z.
Proof.
intros * Hac Hbd.
now apply Z.mul_le_mono_nonneg.
Qed.

Theorem Z_mul_le_compat_nonpos : ∀ a b c d,
  (c ≤ a ≤ 0 → d ≤ b ≤ 0 → a * b ≤ c * d)%F.
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

Theorem Z_consistent :
  rngl_has_inv = false ∨ rngl_has_eucl_div = false.
Proof. now left. Qed.

Definition Z_ring_like_prop : ring_like_prop Z :=
  {| rngl_is_comm := true;
     rngl_has_dec_eq := true;
     rngl_has_dec_le := true;
     rngl_has_1_neq_0 := true;
     rngl_is_ordered := true;
     rngl_is_integral := true;
     rngl_characteristic := 0;
     rngl_add_comm := Z.add_comm;
     rngl_add_assoc := Z.add_assoc;
     rngl_add_0_l := Z.add_0_l;
     rngl_mul_assoc := Z.mul_assoc;
     rngl_mul_1_l := Z.mul_1_l;
     rngl_mul_add_distr_l := Z.mul_add_distr_l;
     rngl_opt_1_neq_0 := Z_1_neq_0;
     rngl_opt_mul_comm := Z.mul_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_l := Z.add_opp_diag_l;
     rngl_opt_add_sub_add_sub := NA;
     rngl_opt_sub_sub_sub_add := NA;
     rngl_opt_sub_diag := NA;
     rngl_opt_sub_0_l := NA;
     rngl_opt_add_cancel_l := NA;
     rngl_opt_mul_sub_distr_l := NA;
     rngl_opt_mul_sub_distr_r := NA;
     rngl_opt_mul_inv_l := NA;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_eucl_div_prop := Z_eucl_div_prop;
     rngl_opt_gauge_prop := Z_gauge_prop;
     rngl_opt_eq_dec := Z.eq_dec;
     rngl_opt_le_dec := Z_le_dec;
     rngl_opt_integral := Z_eq_mul_0;
     rngl_characteristic_prop := Z_characteristic_prop;
     rngl_opt_le_refl := Z.le_refl;
     rngl_opt_le_antisymm := Z.le_antisymm;
     rngl_opt_le_trans := Z.le_trans;
     rngl_opt_add_le_compat := Z.add_le_mono;
     rngl_opt_mul_le_compat_nonneg := Z_mul_le_compat_nonneg;
     rngl_opt_mul_le_compat_nonpos := Z_mul_le_compat_nonpos;
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := Z_not_le;
     rngl_consistent := Z_consistent |}.
