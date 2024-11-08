Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.Misc1 Main.RingLike.
Require Import RealLike.
Require Import TrigoWithoutPi TrigoWithoutPiExt.
Require Import Angle_order.
Require Import AngleDiv2.
Require Import AngleAddLeMonoL.
Require Import AngleTypeIsComplete.
Require Import SeqAngleIsCauchy.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Definition angle_div_nat θ n θ' :=
  angle_lim (seq_angle_to_div_nat θ n) θ'.

Theorem angle_lim_eq_compat :
  ∀ a b f g θ,
  (∀ i, f (i + a) = g (i + b))
  → angle_lim f θ
  → angle_lim g θ.
Proof.
intros * Hfg Hf.
eapply is_limit_when_tending_to_inf_eq_compat; [ apply Hfg | easy ].
Qed.

Theorem angle_lim_opp :
  ∀ f θ, angle_lim f θ → angle_lim (λ i, (- f i)%A) (- θ).
Proof.
intros * Hft.
intros ε Hε.
specialize (Hft ε Hε).
destruct Hft as (N, HN).
exists N.
intros n Hn.
rewrite angle_eucl_dist_opp_opp.
now apply HN.
Qed.

Theorem angle_lim_move_0_r :
  ∀ f θ, angle_lim f θ ↔ angle_lim (λ i, (f i - θ)%A) 0%A.
Proof.
intros.
split; intros Hlim. {
  intros ε Hε.
  specialize (Hlim ε Hε).
  destruct Hlim as (N, HN).
  exists N.
  intros n Hn.
  specialize (HN n Hn).
  now rewrite angle_eucl_dist_move_0_r in HN.
} {
  intros ε Hε.
  specialize (Hlim ε Hε).
  destruct Hlim as (N, HN).
  exists N.
  intros n Hn.
  specialize (HN n Hn).
  now rewrite angle_eucl_dist_move_0_r.
}
Qed.

Theorem angle_le_angle_eucl_dist_le :
  ∀ θ1 θ2,
  (θ1 ≤ angle_straight)%A
  → (θ2 ≤ angle_straight)%A
  → (θ1 ≤ θ2)%A ↔ (angle_eucl_dist θ1 0 ≤ angle_eucl_dist θ2 0)%L.
Proof.
intros * Ht1 Ht2.
progress unfold angle_leb.
apply rngl_sin_nonneg_angle_le_straight in Ht1, Ht2.
apply rngl_leb_le in Ht1, Ht2.
rewrite Ht1, Ht2.
split; intros H12. {
  apply rngl_leb_le in H12.
  now apply rngl_cos_le_iff_angle_eucl_le.
} {
  apply rngl_leb_le.
  now apply rngl_cos_le_iff_angle_eucl_le in H12.
}
Qed.

Theorem angle_div_nat_prop :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  rngl_is_complete T →
  ∀ θ n θ',
  angle_div_nat θ n θ'
  → (n = 0 ∧ θ' = 0%A) ∨ (n * θ')%A = θ.
Proof.
destruct_ac.
intros Hcz Har Hco.
intros * Hdn.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  left; split; [ easy | subst n ].
  progress unfold angle_div_nat in Hdn.
  progress unfold seq_angle_to_div_nat in Hdn.
  cbn in Hdn.
  now apply angle_lim_const in Hdn.
}
right.
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]. {
  subst n; rewrite angle_mul_1_l.
  progress unfold angle_div_nat in Hdn.
  progress unfold seq_angle_to_div_nat in Hdn.
  eapply (angle_lim_eq_compat 0 0) in Hdn. 2: {
    intros i.
    rewrite Nat.add_0_r.
    rewrite Nat.div_1_r.
    rewrite angle_div_2_pow_mul_2_pow.
    easy.
  }
  now apply angle_lim_const in Hdn.
}
progress unfold angle_div_nat in Hdn.
rename Hdn into Hlim.
specialize (angle_lim_mul n _ _ Hlim) as H1.
enough (H2 : angle_lim (λ i, (n * seq_angle_to_div_nat θ n i)%A) θ). {
  apply (limit_unique Hon Hop Hiv Hor) with (lim1 := (n * θ')%A) in H2. {
    easy.
  } {
    apply angle_eucl_dist_is_dist.
  } {
    easy.
  }
}
clear θ' Hlim H1.
destruct (angle_eq_dec θ 0) as [Htz| Htz]. {
  subst θ.
  eapply (angle_lim_eq_compat 0 0). {
    intros i.
    rewrite Nat.add_0_r; symmetry.
    progress unfold seq_angle_to_div_nat.
    rewrite angle_0_div_2_pow.
    do 2 rewrite angle_mul_0_r.
    easy.
  }
  intros ε Hε.
  exists 0.
  intros m _.
  now rewrite angle_eucl_dist_diag.
}
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H2.
  intros ε Hε.
  rewrite (H2 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
move Hc1 before Hcz.
move Hii before Hco.
eapply (angle_lim_eq_compat 0 0). {
  intros i.
  rewrite Nat.add_0_r; symmetry.
  progress unfold seq_angle_to_div_nat.
  rewrite angle_mul_nat_assoc.
  specialize (Nat.div_mod (2 ^ i) n Hnz) as H1.
  symmetry in H1.
  apply Nat.add_sub_eq_r in H1.
  rewrite <- H1.
  rewrite angle_mul_sub_distr_r; [ | now apply Nat.Div0.mod_le ].
  rewrite angle_div_2_pow_mul_2_pow.
  easy.
}
apply angle_lim_move_0_r.
eapply (angle_lim_eq_compat 0 0). {
  intros i.
  rewrite Nat.add_0_r; symmetry.
  rewrite angle_sub_sub_swap.
  rewrite angle_sub_diag.
  rewrite angle_sub_0_l.
  easy.
}
rewrite <- angle_opp_0.
apply angle_lim_opp.
enough (H : angle_lim (λ i, (n * (θ /₂^i))%A) 0). {
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists (Nat.max N (Nat.log2_up (2 * n))).
  intros m Hm.
  specialize (HN m).
  assert (H : N ≤ m). {
    eapply Nat.le_trans; [ | apply Hm ].
    apply Nat.le_max_l.
  }
  specialize (HN H); clear H.
  eapply (rngl_le_lt_trans Hor); [ | apply HN ].
  assert (Hnm : Nat.log2_up (2 * n) ≤ m). {
    eapply Nat.le_trans; [ | apply Hm ].
    apply Nat.le_max_r.
  }
  apply (Nat.pow_le_mono_r 2) in Hnm; [ | easy ].
  apply angle_le_angle_eucl_dist_le. {
    eapply angle_le_trans. {
      apply angle_mul_le_mono_r. 2: {
        apply Nat.lt_le_incl.
        apply Nat.mod_upper_bound.
        apply Hnz.
      }
      apply angle_mul_nat_overflow_div_pow2.
      eapply Nat.le_trans; [ | apply Hnm ].
      apply (Nat.le_trans _ (2 * n)). {
        flia Hnz Hn1.
      }
      apply Nat.log2_log2_up_spec.
      apply Nat.neq_0_lt_0.
      flia Hnz Hn1.
    }
    apply angle_mul_div_pow2_le_straight.
    eapply Nat.le_trans; [ | apply Hnm ].
    apply Nat.log2_log2_up_spec.
    apply Nat.neq_0_lt_0.
    flia Hnz Hn1.
  } {
    apply angle_mul_div_pow2_le_straight.
    eapply Nat.le_trans; [ | apply Hnm ].
    apply Nat.log2_log2_up_spec.
    apply Nat.neq_0_lt_0.
    flia Hnz Hn1.
  }
  apply angle_mul_le_mono_r. 2: {
    apply Nat.lt_le_incl.
    now apply Nat.mod_upper_bound.
  }
  apply angle_mul_nat_overflow_div_pow2.
  eapply Nat.le_trans; [ | apply Hnm ].
  apply (Nat.le_trans _ (2 * n)). {
    flia Hnz Hn1.
  }
  apply Nat.log2_log2_up_spec.
  apply Nat.neq_0_lt_0.
  flia Hnz Hn1.
}
rewrite <- (angle_mul_0_r n).
apply angle_lim_mul.
(* lemma : angle_lim (angle_div_2_pow θ) 0 *)
intros ε Hε.
enough (H : ∃ N, ∀ m, N ≤ m → (1 - ε² / 2 < rngl_cos (θ /₂^m))%L). {
  destruct H as (N, HN).
  exists N.
  intros m Hm.
  specialize (HN m Hm).
  apply rngl_cos_lt_angle_eucl_dist_lt. {
    now apply (rngl_lt_le_incl Hor) in Hε.
  }
  now rewrite angle_sub_0_l.
}
now apply (exists_nat_such_that_rngl_cos_close_to_1 Har).
Qed.

Theorem exists_angle_div_nat :
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  rngl_is_complete T →
  ∀ θ n,
  n ≠ 0
  → ∃ θ', (n * θ')%A = θ.
Proof.
destruct_ac.
intros Hcz Har Hco * Hnz.
specialize (seq_angle_to_div_nat_is_Cauchy Har n θ) as H1.
specialize (rngl_is_complete_angle_is_complete Hco) as H2.
specialize (H2 _ H1).
destruct H2 as (θ', Ht).
exists θ'.
specialize (angle_div_nat_prop Hcz Har Hco _ _ _ Ht) as H2.
now destruct H2.
Qed.

Inspect 1.

End a.
