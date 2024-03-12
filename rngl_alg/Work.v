(* File created because Complex.v became too big, but
   without any topic found for the moment *)

Set Nested Proofs Allowed.
Require Import Utf8 ZArith.
Require Import Init.Nat.
Import List List.ListNotations.
Require Import Main.Misc Main.RingLike Main.IterAdd.
Require Import Misc.
Require Import RealLike TrigoWithoutPi.
Require Import AngleAddOverflowLe AngleAddLeMonoL.
Require Import AngleLeSubAdd AngleDiv2Add.
Require Import TacChangeAngle.
Require Import Complex NewtonBinomial.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem rngl_pow_1_l : rngl_has_1 T = true → ∀ n, (1 ^ n = 1)%L.
Proof.
intros Hon *.
induction n; [ easy | cbn ].
rewrite IHn.
apply (rngl_mul_1_l Hon).
Qed.

Theorem rngl_pow_mul_l :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  ∀ a b n, ((a * b) ^ n = a ^ n * b ^ n)%L.
Proof.
intros Hic Hon *.
induction n; cbn. {
  symmetry; apply (rngl_mul_1_l Hon).
}
do 2 rewrite <- rngl_mul_assoc.
f_equal.
rewrite IHn.
rewrite (rngl_mul_comm Hic).
rewrite <- rngl_mul_assoc.
f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem rngl_pow_mul_r :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  ∀ a m n, (a ^ (m * n) = (a ^ m) ^ n)%L.
Proof.
intros Hic Hon *.
revert n.
induction m; intros. {
  symmetry; apply (rngl_pow_1_l Hon).
}
rewrite rngl_pow_succ_r.
cbn.
rewrite (rngl_pow_add_r Hon).
rewrite IHm.
symmetry.
apply (rngl_pow_mul_l Hic Hon).
Qed.

Context {rl : real_like_prop T}.

Theorem gc_power_im_0 :
  rngl_has_opp_or_subt T = true →
  ∀ n x, (mk_gc x 0%L ^ n)%C = (mk_gc (x ^ n) 0)%C.
Proof.
intros Hos *.
progress unfold gc_power_nat.
induction n. {
  cbn; progress unfold rngl_one.
  cbn; progress unfold gc_opt_one.
  now destruct (rngl_opt_one T).
}
rewrite rngl_pow_succ_r; cbn.
rewrite IHn.
apply eq_gc_eq; cbn.
do 2 rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_r Hos), rngl_add_0_r.
now rewrite (rngl_mul_0_l Hos).
Qed.

End a.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem angle_add_overflow_opp :
  ∀ θ, θ ≠ 0%A → angle_add_overflow θ (- θ) = true.
Proof.
intros * Hz.
progress unfold angle_add_overflow.
rewrite angle_add_opp_r.
rewrite angle_sub_diag.
apply angle_lt_iff.
split; [ apply angle_nonneg | ].
now intros H; symmetry in H.
Qed.

Theorem rngl_sin_sub_div_2_div_2_pos :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_cos θ1 < rngl_cos θ2)%L
  → (0 < rngl_sin (θ1 / ₂ - θ2 / ₂))%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzs1 Hzs2 Hcc.
  do 2 rewrite (H1 (rngl_cos _)) in Hcc.
  now apply (rngl_lt_irrefl Hor) in Hcc.
}
intros * Hzs1 Hzs2 Hcc.
cbn.
generalize Hzs2; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
rewrite (rngl_mul_1_l Hon).
generalize Hzs1; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
apply (rngl_lt_0_sub Hop Hor).
rewrite <- rl_sqrt_mul; cycle 1.
apply rngl_1_add_cos_div_2_nonneg.
apply rngl_1_sub_cos_div_2_nonneg.
rewrite <- rl_sqrt_mul; cycle 1.
apply rngl_1_sub_cos_div_2_nonneg.
apply rngl_1_add_cos_div_2_nonneg.
apply (rl_sqrt_lt_rl_sqrt Hon Hop Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor).
apply rngl_1_add_cos_div_2_nonneg.
apply rngl_1_sub_cos_div_2_nonneg.
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
apply (rngl_div_lt_mono_pos_r Hon Hop Hiv Hor Hii). {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
do 2 rewrite (rngl_mul_div_assoc Hiv).
apply (rngl_div_lt_mono_pos_r Hon Hop Hiv Hor Hii). {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
rewrite (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_1_r Hon).
rewrite rngl_mul_add_distr_r.
rewrite (rngl_mul_1_l Hon).
rewrite rngl_mul_add_distr_l.
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_mul_sub_distr_r Hop).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_sub_add_distr Hos).
rewrite (rngl_add_sub_assoc Hop).
apply (rngl_sub_lt_mono_r Hop Hor).
rewrite <- (rngl_add_sub_assoc Hop).
rewrite <- (rngl_sub_sub_distr Hop).
progress unfold rngl_sub at 2.
rewrite Hop.
apply (rngl_add_lt_mono_l Hop Hor).
rewrite (rngl_opp_sub_distr Hop).
apply (rngl_lt_add_lt_sub_r Hop Hor).
rewrite <- (rngl_add_sub_swap Hop).
apply (rngl_lt_sub_lt_add_l Hop Hor).
do 2 rewrite (rngl_add_diag Hon (rngl_cos _)).
apply (rngl_mul_lt_mono_pos_l Hop Hor Hii). {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
easy.
Qed.

Theorem angle_sub_straight_eq_add_straight :
  ∀ θ, (θ - angle_straight = θ + angle_straight)%A.
Proof.
destruct_ac.
intros.
apply angle_sub_move_r.
rewrite <- angle_add_assoc.
rewrite angle_straight_add_straight.
symmetry.
apply angle_add_0_r.
Qed.

Theorem rngl_cos_add_right_div_2_r :
  ∀ θ,
  rngl_cos (θ + angle_right / ₂) = ((rngl_cos θ - rngl_sin θ) / √2)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (rngl_cos _)).
  symmetry.
  apply H1.
}
intros.
cbn.
specialize (rngl_0_le_1 Hon Hop Hor) as H.
apply rngl_leb_le in H.
rewrite H; clear H.
rewrite (rngl_mul_1_l Hon).
rewrite rngl_add_0_r.
rewrite (rngl_sub_0_r Hos).
rewrite <- (rngl_mul_sub_distr_r Hop).
progress unfold rngl_div.
rewrite Hiv.
rewrite (rngl_mul_1_l Hon).
f_equal.
apply rl_nth_root_inv.
apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_sin_right_div_2 : rngl_sin (angle_right / ₂) = √(1 / 2)%L.
Proof.
destruct_ac.
cbn.
now rewrite (rngl_sub_0_r Hos).
Qed.

Theorem rngl_cos_right_div_2 : rngl_cos (angle_right / ₂) = √(1 / 2)%L.
Proof.
destruct_ac.
cbn.
specialize (rngl_0_le_1 Hon Hop Hor) as H1.
apply rngl_leb_le in H1.
rewrite H1; clear H1.
rewrite (rngl_mul_1_l Hon).
now rewrite rngl_add_0_r.
Qed.

Theorem rngl_cos_3_right_div_2 :
  rngl_cos (3 * (angle_right / ₂)) = (- √(1 / 2))%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 (rngl_cos _)); symmetry.
  apply H1.
}
cbn.
specialize (rngl_0_le_1 Hon Hop Hor) as H1.
apply rngl_leb_le in H1.
rewrite H1; clear H1.
do 2 rewrite (rngl_mul_0_r Hos).
do 2 rewrite (rngl_sub_0_r Hos).
do 2 rewrite rngl_add_0_r.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_sub_diag Hos).
rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_l Hop).
f_equal.
rewrite fold_rngl_squ.
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_div_nonneg Hon Hop Hiv Hor). {
    apply (rngl_0_le_1 Hon Hop Hor).
  }
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
rewrite <- (rngl_div_add_distr_r Hiv).
rewrite (rngl_div_diag Hon Hiq). 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
apply (rngl_mul_1_r Hon).
Qed.

Theorem rngl_sin_5_right_div_2 :
  rngl_sin (5 * (angle_right / ₂)) = (- √(1 / 2))%L.
Proof.
destruct_ac.
replace 5 with (2 + 3) by easy.
rewrite angle_mul_add_distr_r.
rewrite angle_div_2_mul_2.
rewrite (rngl_sin_add_right_l Hon Hos).
apply rngl_cos_3_right_div_2.
Qed.

Theorem rngl_sin_3_right_div_2 :
  rngl_sin (3 * (angle_right / ₂)) = √(1 / 2)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 (rngl_sin _)); symmetry.
  apply H1.
}
cbn.
specialize (rngl_0_le_1 Hon Hop Hor) as H1.
apply rngl_leb_le in H1.
rewrite H1; clear H1.
do 2 rewrite (rngl_mul_0_r Hos).
do 2 rewrite (rngl_sub_0_r Hos).
do 2 rewrite rngl_add_0_r.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_sub_diag Hos).
rewrite (rngl_mul_0_r Hos).
rewrite rngl_add_0_l.
rewrite fold_rngl_squ.
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_div_nonneg Hon Hop Hiv Hor). {
    apply (rngl_0_le_1 Hon Hop Hor).
  }
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
rewrite <- (rngl_div_add_distr_r Hiv).
rewrite (rngl_div_diag Hon Hiq). 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
apply (rngl_mul_1_r Hon).
Qed.

Theorem rngl_cos_5_right_div_2 :
  rngl_cos (5 * (angle_right / ₂)) = (- √(1 / 2))%L.
Proof.
destruct_ac.
replace 5 with (2 + 3) by easy.
rewrite angle_mul_add_distr_r.
rewrite angle_div_2_mul_2.
rewrite (rngl_cos_add_right_l Hon Hop).
f_equal.
apply rngl_sin_3_right_div_2.
Qed.

Theorem rl_sqrt_half_nonneg : (0 ≤ √(1 / 2))%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 √_%L).
  apply (rngl_le_refl Hor).
}
apply rl_sqrt_nonneg.
apply (rngl_div_nonneg Hon Hop Hiv Hor).
apply (rngl_0_le_1 Hon Hop Hor).
apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
Qed.

Theorem rl_sqrt_half_pos :
  rngl_characteristic T ≠ 1 →
  (0 < √(1 / 2))%L.
Proof.
destruct_ac.
intros Hc1.
apply (rl_sqrt_pos Hon Hos).
apply (rngl_div_lt_pos Hon Hop Hiv Hor). {
  apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
}
apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_cos_lt_sin_diag :
  ∀ θ,
  (angle_right / ₂ < θ < 5 * (angle_right / ₂))%A
  ↔ (rngl_cos θ < rngl_sin θ)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H2.
  intros.
  rewrite (H2 (angle_right / ₂))%A.
  rewrite (H2 θ), (H2 (_ * _))%A.
  rewrite (H1 (rngl_cos _)), (H1 (rngl_sin _)).
  split. {
    intros (H, _).
    now apply angle_lt_irrefl in H.
  } {
    intros H.
    now apply (rngl_lt_irrefl Hor) in H.
  }
}
intros.
progress unfold angle_ltb.
rewrite rngl_sin_right_div_2.
rewrite rngl_cos_right_div_2.
rewrite rngl_sin_5_right_div_2.
rewrite rngl_cos_5_right_div_2.
rewrite rngl_leb_opp_r, (rngl_opp_0 Hop).
specialize rl_sqrt_half_nonneg as H.
apply rngl_leb_le in H.
rewrite H; clear H.
specialize (rl_sqrt_half_pos Hc1) as H.
apply (rngl_leb_gt Hor) in H.
rewrite H; clear H.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  split. {
    intros (H1, _).
    apply rngl_leb_le in Hzs.
    apply rngl_ltb_lt in H1.
    destruct (rngl_lt_dec Hor (rngl_cos θ) 0) as [Hzc| Hcz]. {
      now apply (rngl_lt_le_trans Hor _ 0).
    }
    apply (rngl_nlt_ge Hor) in Hcz.
    apply (rngl_lt_le_trans Hor _ √(1/2))%L; [ easy | ].
    specialize rngl_sin_nonneg_cos_le_sin_le as H2.
    specialize (H2 θ (angle_right / ₂) Hzs)%A.
    rewrite rngl_sin_right_div_2 in H2.
    rewrite rngl_cos_right_div_2 in H2.
    specialize (H2 rl_sqrt_half_nonneg).
    generalize H1; intros H.
    apply (rngl_lt_le_incl Hor) in H.
    specialize (H2 H); clear H.
    generalize Hcz; intros H.
    apply rngl_leb_le in H.
    now rewrite H in H2; clear H.
  } {
    intros Hcs.
    split; [ | easy ].
    apply rngl_leb_le in Hzs.
    apply rngl_ltb_lt.
    specialize rl_sqrt_half_nonneg as Hs2.
    destruct (rngl_lt_dec Hor (rngl_cos θ) 0) as [Hzc| Hcz]. {
      now apply (rngl_lt_le_trans Hor _ 0).
    }
    apply (rngl_nlt_ge Hor) in Hcz.
    apply (rngl_nle_gt Hor).
    intros Hcc.
    generalize Hcc; intros H.
    apply (rngl_nlt_ge Hor) in H.
    apply H; clear H.
    rewrite <- rngl_cos_right_div_2.
    apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff; try easy. {
      now rewrite rngl_sin_right_div_2.
    } {
      now rewrite rngl_cos_right_div_2.
    }
    rewrite rngl_sin_right_div_2.
    eapply (rngl_le_lt_trans Hor); [ | apply Hcs ].
    easy.
    (* bizarre, comme démonstration *)
  }
} {
  apply (rngl_leb_gt Hor) in Hzs.
  split. {
    intros (_, H1).
    apply rngl_ltb_lt in H1.
    change_angle_add_r θ angle_straight.
    progress sin_cos_add_sub_straight_hyp T H1.
    progress sin_cos_add_sub_straight_hyp T Hzs.
    progress sin_cos_add_sub_straight_goal T.
    rewrite (rngl_add_opp_r Hop).
    apply (rngl_lt_0_sub Hop Hor).
    apply (rngl_le_lt_trans Hor _ √(1/2))%L; [ | easy ].
    specialize rngl_sin_nonneg_cos_lt_sin_lt as H2.
    specialize (H2 (angle_right / ₂) θ)%A.
    rewrite rngl_sin_right_div_2 in H2.
    rewrite rngl_cos_right_div_2 in H2.
    specialize (H2 (rl_sqrt_half_pos Hc1) Hzs H1).
    specialize (rl_sqrt_half_pos Hc1) as H.
    apply rngl_ltb_lt in H.
    rewrite H in H2; clear H.
    now apply (rngl_lt_le_incl Hor) in H2.
  } {
    intros Hcs.
    split; [ easy | ].
    apply rngl_ltb_lt.
    change_angle_add_r θ angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hcs.
    progress sin_cos_add_sub_straight_hyp T Hzs.
    progress sin_cos_add_sub_straight_goal T.
    rewrite (rngl_add_opp_r Hop).
    apply (rngl_lt_0_sub Hop Hor).
    rewrite <- rngl_cos_right_div_2.
    apply angle_add_le_mono_l_lemma_39. {
      rewrite rngl_sin_right_div_2.
      apply (rl_sqrt_half_pos Hc1).
    } {
      now apply (rngl_lt_le_incl Hor) in Hzs.
    } {
      rewrite rngl_cos_right_div_2.
      apply rl_sqrt_half_nonneg.
    } {
      apply (rngl_lt_le_incl Hor) in Hcs, Hzs.
      now apply (rngl_le_trans Hor _ (rngl_sin θ)).
    }
    cbn.
    specialize (rngl_0_le_1 Hon Hop Hor) as H2.
    apply rngl_leb_le in H2.
    rewrite H2; clear H2.
    rewrite (rngl_mul_1_l Hon).
    rewrite rngl_add_0_r, (rngl_sub_0_r Hos).
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_add_opp_r Hop).
    rewrite <- (rngl_mul_sub_distr_l Hop).
    apply (rngl_mul_pos_pos Hop Hor Hii). {
      apply (rl_sqrt_half_pos Hc1).
    }
    now apply (rngl_lt_0_sub Hop Hor).
  }
}
Qed.

Theorem rngl_sin_pos_lt_straight :
  ∀ θ,
  (0 < rngl_sin θ)%L
  → (θ < angle_straight)%A.
Proof.
destruct_ac.
intros * Hzs.
progress unfold angle_ltb.
rewrite (rngl_leb_refl Hor).
generalize Hzs; intros H.
apply (rngl_lt_le_incl Hor) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_ltb_lt; cbn.
apply (rngl_lt_iff Hor).
split; [ apply rngl_cos_bound | ].
intros H; symmetry in H.
apply eq_rngl_cos_opp_1 in H.
subst θ.
now apply (rngl_lt_irrefl Hor) in Hzs.
Qed.

Theorem rngl_sin_nonneg_le_straight :
  ∀ θ,
  (0 ≤ rngl_sin θ)%L
  → (θ ≤ angle_straight)%A.
Proof.
destruct_ac.
intros * Hzs.
progress unfold angle_leb.
rewrite (rngl_leb_refl Hor).
apply rngl_leb_le in Hzs.
rewrite Hzs.
apply rngl_leb_le; cbn.
apply rngl_cos_bound.
Qed.

Theorem angle_add_straight_r_not_overflow :
  ∀ θ, (θ < angle_straight)%A → angle_add_overflow θ angle_straight = false.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  intros * Hts.
  rewrite (H1 θ), (H1 angle_straight) in Hts.
  now apply angle_lt_irrefl in Hts.
}
intros * Hts.
progress unfold angle_ltb in Hts.
cbn in Hts.
rewrite (rngl_leb_refl Hor) in Hts.
progress unfold angle_add_overflow.
progress unfold angle_ltb.
rewrite rngl_sin_add_straight_r.
rewrite rngl_cos_add_straight_r.
rewrite rngl_leb_opp_r.
rewrite (rngl_opp_0 Hop).
destruct (rngl_le_dec Hor 0 (rngl_sin θ)) as [Hzs| Hsz]. {
  generalize Hzs; intros H.
  apply rngl_leb_le in H.
  rewrite H in Hts |-*; clear H.
  apply rngl_ltb_lt in Hts.
  destruct (rngl_le_dec Hor (rngl_sin θ) 0) as [Hsz| Hsz]. {
    apply (rngl_le_antisymm Hor) in Hzs; [ | easy ].
    apply eq_rngl_sin_0 in Hzs.
    destruct Hzs; subst θ; cbn; rewrite (rngl_leb_refl Hor). {
      apply (rngl_ltb_ge Hor).
      apply (rngl_opp_1_le_1 Hon Hop Hor Hc1).
    }
    exfalso.
    now apply (rngl_lt_irrefl Hor) in Hts.
  }
  apply (rngl_nle_gt Hor) in Hsz.
  generalize Hsz; intros H.
  apply (rngl_leb_gt Hor) in H.
  now rewrite H; clear H.
}
apply (rngl_nle_gt Hor) in Hsz.
generalize Hsz; intros H.
apply (rngl_leb_gt Hor) in H.
now rewrite H in Hts.
Qed.

Theorem angle_add_not_overflow_equiv :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  ↔ (θ1 / ₂ + θ2 / ₂ ≤ angle_straight)%A ∧ (θ1 = 0 ∨ θ1 + θ2 ≠ 0)%A.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 θ1).
  rewrite angle_add_overflow_0_l.
  split; [ intros _ | easy ].
  split; [ | now left ].
  do 2 rewrite (H1 (_ / ₂))%A.
  rewrite angle_add_0_l.
  apply angle_nonneg.
}
intros.
split; intros H12. {
  split. {
    rewrite <- angle_div_2_add_not_overflow; [ | easy ].
    apply angle_div_2_le_straight.
  } {
    remember (θ1 =? 0)%A as t1z eqn:Ht1z.
    symmetry in Ht1z.
    destruct t1z. {
      now apply (angle_eqb_eq Hed) in Ht1z; left.
    }
    apply (angle_eqb_neq Hed) in Ht1z; right.
    intros H12z.
    rewrite angle_add_comm in H12z.
    apply angle_add_move_0_r in H12z.
    subst θ2.
    apply Bool.not_true_iff_false in H12.
    apply H12.
    now apply angle_add_overflow_opp.
  }
} {
  destruct H12 as (H12, H112).
  destruct H112 as [H1| H12z]. {
    subst θ1.
    apply angle_add_overflow_0_l.
  }
  progress unfold angle_leb in H12.
  rewrite (rngl_leb_refl Hor) in H12.
  remember (0 ≤? rngl_sin (_ / ₂ + _))%L as zs12d eqn:Hzs12d.
  symmetry in Hzs12d.
  destruct zs12d; [ | easy ].
  apply rngl_leb_le in Hzs12d.
  progress unfold angle_add_overflow.
  progress unfold angle_ltb.
  remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
  remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
  symmetry in Hzs12, Hzs1.
  destruct zs12. {
    destruct zs1. {
      apply rngl_leb_le in Hzs12, Hzs1.
      apply (rngl_ltb_ge Hor).
      destruct (rngl_le_dec Hor 0 (rngl_sin θ2)) as [Hzs2| Hzs2]. {
        destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
          cbn.
          progress unfold rngl_sub.
          rewrite Hop.
          apply (rngl_le_add_le_sub_l Hop Hor).
          rewrite (rngl_sub_mul_r_diag_l Hon Hop).
          apply (rngl_le_trans Hor _ 0). {
            apply (rngl_opp_nonpos_nonneg Hop Hor).
            now apply (rngl_mul_nonneg_nonneg Hop Hor).
          }
          apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
          apply (rngl_le_0_sub Hop Hor).
          apply rngl_cos_bound.
        }
        apply (rngl_nle_gt Hor) in Hzc1.
        change_angle_sub_r θ1 angle_right.
        progress sin_cos_add_sub_right_hyp T Hzs1.
        progress sin_cos_add_sub_right_hyp T Hzs12.
        progress sin_cos_add_sub_right_hyp T Hzc1.
        progress sin_cos_add_sub_right_goal T.
        destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
          apply rngl_sin_sub_nonneg_sin_le_sin; [ | easy | ]. {
            apply (rngl_lt_le_incl Hor) in Hzc1.
            now apply rngl_sin_add_nonneg.
          }
          rewrite angle_add_comm.
          now rewrite angle_add_sub.
        }
        apply (rngl_nle_gt Hor) in Hzc2.
        change_angle_sub_r θ2 angle_right.
        progress sin_cos_add_sub_right_hyp T Hzs2.
        progress sin_cos_add_sub_right_hyp T Hzs12.
        progress sin_cos_add_sub_right_hyp T Hzc2.
        progress sin_cos_add_sub_right_goal T.
        move θ2 before θ1.
        apply (rngl_nlt_ge Hor).
        intros Hcs.
        apply (rngl_nlt_ge Hor) in Hzs12.
        apply Hzs12; clear Hzs12.
        apply (rngl_lt_iff Hor).
        split. {
          apply (rngl_lt_le_incl Hor) in Hzc1, Hzc2.
          now apply rngl_sin_add_nonneg.
        }
        intros H; symmetry in H.
        apply eq_rngl_sin_0 in H.
        destruct H as [Ha12| Ha12]. {
          rewrite Ha12 in Hcs; cbn in Hcs.
          apply (rngl_nle_gt Hor) in Hcs.
          apply Hcs; clear Hcs.
          apply rngl_sin_bound.
        }
        rewrite Ha12 in Hcs.
        apply angle_add_move_l in Ha12.
        subst θ2.
        rewrite (rngl_cos_sub_straight_l Hon Hop) in Hzs2.
        apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs2.
        apply (rngl_le_antisymm Hor) in Hzs1; [ | easy ].
        apply eq_rngl_cos_0 in Hzs1.
        destruct Hzs1; subst θ1. {
          rewrite (angle_right_add_right Hon Hop) in H12z.
          rewrite angle_sub_add in H12z.
          now rewrite angle_straight_add_straight in H12z.
        }
        apply (rngl_nle_gt Hor) in Hzc1.
        apply Hzc1; clear Hzc1; cbn.
        apply (rngl_opp_1_le_0 Hon Hop Hor).
      }
      apply (rngl_nle_gt Hor) in Hzs2.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
        change_angle_opp θ2.
        progress sin_cos_opp_hyp T Hzs2.
        progress sin_cos_opp_hyp T Hzs12.
        progress sin_cos_opp_hyp T Hzc2.
        progress sin_cos_opp_goal T.
        rewrite angle_add_opp_r in H12z.
        rewrite angle_opp_div_2 in Hzs12d.
        remember (θ2 =? 0)%A as t2z eqn:Ht2z.
        symmetry in Ht2z.
        destruct t2z. {
          apply (angle_eqb_eq Hed) in Ht2z.
          subst θ2.
          now apply (rngl_lt_irrefl Hor) in Hzs2.
        }
        rewrite angle_add_assoc in Hzs12d.
        rewrite angle_add_opp_r in Hzs12d.
        rewrite rngl_sin_add_straight_r in Hzs12d.
        apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12d.
        apply (rngl_nlt_ge Hor).
        intros Hcc.
        apply (rngl_nlt_ge Hor) in Hzs12d.
        apply Hzs12d; clear Hzs12d.
        apply rngl_sin_sub_div_2_div_2_pos; [ easy | | ]. {
          now apply (rngl_lt_le_incl Hor) in Hzs2.
        }
        destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
          apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff; try easy. {
            now apply (rngl_lt_le_incl Hor) in Hzs2.
          } {
            apply (rngl_lt_iff Hor).
            split; [ now apply rngl_sin_sub_nonneg_sin_le_sin | ].
            intros H.
            apply rngl_sin_eq in H.
            destruct H; subst θ2. {
              now rewrite angle_sub_diag in H12z.
            }
            apply H12z; clear H12z.
            rewrite angle_sub_sub_distr.
            rewrite <- angle_add_sub_swap.
            rewrite (rngl_cos_sub_straight_l Hon Hop) in Hzc2.
            apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzc2.
            apply (rngl_le_antisymm Hor) in Hzc1; [ | easy ].
            apply eq_rngl_cos_0 in Hzc1.
            destruct Hzc1; subst θ1. {
              rewrite (angle_right_add_right Hon Hop).
              apply angle_sub_diag.
            }
            rewrite angle_add_opp_r.
            rewrite <- (angle_opp_add_distr Hic Hop).
            rewrite (angle_right_add_right Hon Hop).
            rewrite <- (angle_opp_add_distr Hic Hop).
            rewrite angle_straight_add_straight.
            apply angle_opp_0.
          }
        }
        apply (rngl_nle_gt Hor) in Hzc1.
        now apply (rngl_lt_le_trans Hor _ 0).
      }
      apply (rngl_nle_gt Hor) in Hzc2.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
        change_angle_add_r θ2 angle_straight.
        progress sin_cos_add_sub_straight_hyp T Hzs12.
        progress sin_cos_add_sub_straight_hyp T Hzc2.
        progress sin_cos_add_sub_straight_hyp T Hzs2.
        progress sin_cos_add_sub_straight_goal T.
        rewrite angle_add_sub_assoc in H12z.
        clear - ac Hzs12 Hzc2 Hzs2 Hzs1 Hzc1 H12z.
        destruct_ac.
        apply (rngl_nlt_ge Hor) in Hzs12.
        apply (rngl_nlt_ge Hor).
        intros Hcc.
        apply Hzs12; clear Hzs12.
        apply (rngl_lt_iff Hor).
        split. {
          apply (rngl_lt_le_incl Hor) in Hzc2, Hzs2.
          now apply rngl_sin_add_nonneg.
        }
        intros Hs; symmetry in Hs.
        apply eq_rngl_sin_0 in Hs.
        destruct Hs as [Hs| Hs]. {
          apply (rngl_nle_gt Hor) in Hcc.
          apply Hcc; clear Hcc.
          rewrite Hs; cbn.
          apply (rngl_le_opp_l Hop Hor).
          apply rngl_cos_bound.
        }
        rewrite Hs in H12z.
        now rewrite angle_sub_diag in H12z.
      }
      apply (rngl_nle_gt Hor) in Hzc1.
      change_angle_add_r θ2 angle_straight.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hzc2.
      progress sin_cos_add_sub_straight_hyp T Hzs2.
      progress sin_cos_add_sub_straight_goal T.
      rewrite angle_add_sub_assoc in H12z.
      change_angle_sub_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs1.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_hyp T Hzc1.
      progress sin_cos_add_sub_right_goal T.
      apply (rngl_nlt_ge Hor).
      intros Hss.
      apply (rngl_nlt_ge Hor) in Hzs12d.
      apply Hzs12d; clear Hzs12d.
      rewrite angle_div_2_add_not_overflow. 2: {
        progress unfold angle_add_overflow.
        progress unfold angle_ltb.
        progress sin_cos_add_sub_right_goal T.
        generalize Hzs1; intros H.
        apply rngl_leb_le in H.
        rewrite H; clear H.
        generalize Hzc1; intros H.
        apply (rngl_lt_le_incl Hor) in H.
        apply rngl_leb_le in H.
        rewrite H; clear H.
        apply (rngl_ltb_ge Hor).
        apply (rngl_le_trans Hor _ 0); [ | easy ].
        apply (rngl_opp_nonpos_nonneg Hop Hor).
        now apply (rngl_lt_le_incl Hor) in Hzc1.
      }
      rewrite angle_sub_straight_eq_add_straight.
      rewrite angle_div_2_add_not_overflow. 2: {
        progress unfold angle_add_overflow.
        progress unfold angle_ltb.
        progress sin_cos_add_sub_straight_goal T.
        rewrite rngl_leb_opp_r.
        rewrite (rngl_opp_0 Hop).
        generalize Hzs2; intros H.
        apply (rngl_lt_le_incl Hor) in H.
        apply rngl_leb_le in H.
        rewrite H; clear H.
        generalize Hzs2; intros H.
        apply (rngl_leb_gt Hor) in H.
        now rewrite H.
      }
      rewrite angle_straight_div_2.
      rewrite angle_add_assoc.
      rewrite (angle_add_add_swap (θ1 / ₂)).
      rewrite rngl_sin_add_right_r.
      rewrite <- angle_div_2_add_not_overflow. 2: {
        apply angle_add_not_overflow_comm.
        apply angle_add_overflow_lt_straight_le_straight. {
          (* lemma? cf. rngl_sin_nonneg_angle_le_straight *)
          progress unfold angle_ltb.
          generalize Hzs2; intros H.
          apply (rngl_lt_le_incl Hor) in H.
          apply rngl_leb_le in H.
          rewrite H; clear H; cbn.
          rewrite (rngl_leb_refl Hor).
          apply rngl_ltb_lt.
          apply (rngl_le_lt_trans Hor _ 0); [ | easy ].
          apply (rngl_opp_1_le_0 Hon Hop Hor).
        } {
          apply (rngl_lt_le_incl Hor) in Hzc1.
          now apply rngl_sin_nonneg_angle_le_straight.
        }
      }
      rewrite rngl_cos_add_right_div_2_r.
      progress unfold rngl_div.
      rewrite Hiv.
      (* lemma *)
      rewrite (rngl_mul_comm Hic).
      apply (rngl_mul_pos_neg Hop Hor Hid). {
        apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
        apply (rl_sqrt_pos Hon Hos).
        apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
      }
      apply (rngl_lt_sub_0 Hop Hor).
      apply rngl_cos_lt_sin_diag.
      split. {
        apply angle_div_2_lt_compat.
        progress unfold angle_ltb.
        cbn - [ angle_add ].
        specialize (rngl_0_le_1 Hon Hop Hor) as H.
        apply rngl_leb_le in H.
        rewrite H; clear H.
        rename Hzs12 into Hc12z.
        remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
        symmetry in Hzs12.
        destruct zs12; [ | easy ].
        apply rngl_leb_le in Hzs12.
        apply rngl_ltb_lt.
        apply (rngl_lt_iff Hor).
        split; [ easy | ].
        intros H.
        apply eq_rngl_cos_0 in H.
        rename H12 into Hco1.
        destruct H as [H12| H12]. {
          apply H12z.
          rewrite angle_add_add_swap.
          rewrite H12.
          rewrite (angle_right_add_right Hon Hop).
          apply angle_sub_diag.
        }
        apply (rngl_nlt_ge Hor) in Hzs12.
        apply Hzs12; clear Hzs12.
        rewrite H12; cbn.
        apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
      }
      progress unfold angle_ltb.
      rewrite rngl_sin_5_right_div_2.
      rewrite rngl_cos_5_right_div_2.
      rewrite rngl_leb_opp_r.
      rewrite (rngl_opp_0 Hop).
      specialize (rl_sqrt_half_pos Hc1) as H.
      apply (rngl_leb_gt Hor) in H.
      rewrite H; clear H.
      specialize (rngl_sin_div_2_nonneg (θ1 + θ2)) as H.
      apply rngl_leb_le in H.
      now rewrite H; clear H.
    }
    exfalso.
    apply rngl_leb_le in Hzs12.
    apply rngl_leb_nle in Hzs1.
    apply Hzs1; clear Hzs1.
    remember (angle_add_overflow θ1 θ2) as aov eqn:Haov.
    symmetry in Haov.
    destruct aov. 2: {
      now apply (rngl_sin_add_nonneg_sin_nonneg _ θ2).
    }
    specialize (angle_div_2_add_overflow _ _ Haov) as H1.
    symmetry in H1.
    apply angle_add_move_r in H1.
    rewrite angle_sub_straight_eq_add_straight in H1.
    rewrite H1 in Hzs12d, H12.
    rewrite rngl_sin_add_straight_r in Hzs12d.
    apply (rngl_nlt_ge Hor).
    intros Hsz1.
    apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12d.
    apply (rngl_nlt_ge Hor) in Hzs12d.
    apply Hzs12d; clear Hzs12d.
    apply (rngl_lt_iff Hor).
    split; [ apply rngl_sin_div_2_nonneg | ].
    intros H; symmetry in H.
    apply eq_rngl_sin_0 in H.
    destruct H as [H| H]. {
      now apply eq_angle_div_2_0 in H.
    }
    now apply (angle_div_2_not_straight Hc1) in H.
  }
  destruct zs1; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzs12, Hzs1.
  apply (rngl_ltb_ge Hor).
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
    destruct (rngl_le_dec Hor 0 (rngl_sin θ2)) as [Hzs2| Hs2z]. {
      change_angle_add_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzc1.
      progress sin_cos_add_sub_right_hyp T Hzs1.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_goal T.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
        apply rngl_sin_sub_nonneg_sin_le_sin. {
          apply (rngl_lt_le_incl Hor) in Hzs1.
          now apply rngl_sin_add_nonneg.
        } {
          now apply (rngl_lt_le_incl Hor) in Hzs12.
        }
        rewrite angle_add_comm.
        now rewrite angle_add_sub.
      }
      exfalso.
      apply (rngl_nle_gt Hor) in Hc2z.
      apply (rngl_nle_gt Hor) in Hzs12.
      apply Hzs12; clear Hzs12.
      change_angle_sub_r θ2 angle_right.
      progress sin_cos_add_sub_right_hyp T Hc2z.
      progress sin_cos_add_sub_right_hyp T Hzs2.
      progress sin_cos_add_sub_right_goal T.
      apply (rngl_lt_le_incl Hor) in Hzs1, Hc2z.
      now apply rngl_sin_add_nonneg.
    }
    apply (rngl_nle_gt Hor) in Hs2z.
    apply (rngl_nlt_ge Hor).
    intros Hcc.
    specialize (angle_div_2_add_overflow θ1 θ2) as H1.
    assert (H : angle_add_overflow θ1 θ2 = true). {
      progress unfold angle_add_overflow.
      progress unfold angle_ltb.
      generalize Hzs12; intros H.
      apply (rngl_leb_gt Hor) in H.
      rewrite H; clear H.
      generalize Hzs1; intros H.
      apply (rngl_leb_gt Hor) in H.
      rewrite H; clear H.
      now apply rngl_ltb_lt.
    }
    specialize (H1 H); clear H.
    symmetry in H1.
    apply angle_add_move_r in H1.
    rewrite angle_sub_straight_eq_add_straight in H1.
    rewrite H1 in Hzs12d, H12.
    rewrite rngl_sin_add_straight_r in Hzs12d.
    apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12d.
    apply (rngl_nlt_ge Hor) in Hzs12d.
    apply Hzs12d; clear Hzs12d.
    apply (rngl_lt_iff Hor).
    split; [ apply rngl_sin_div_2_nonneg | ].
    intros H; symmetry in H.
    apply eq_rngl_sin_0 in H.
    destruct H as [H| H]. {
      now apply eq_angle_div_2_0 in H.
    }
    now apply (angle_div_2_not_straight Hc1) in H.
  }
  apply (rngl_nle_gt Hor) in Hzc1.
  change_angle_add_r θ1 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzc1.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_goal T.
  destruct (rngl_le_dec Hor 0 (rngl_sin θ2)) as [Hzs2| Hs2z]. {
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
      apply (rngl_lt_le_incl Hor) in Hzs1, Hzc1.
      now apply quadrant_1_rngl_cos_add_le_cos_l.
    }
    apply (rngl_nle_gt Hor) in Hc2z.
    change_angle_sub_r θ2 angle_right.
    progress sin_cos_add_sub_right_hyp T Hc2z.
    progress sin_cos_add_sub_right_hyp T Hzs2.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_goal T.
    apply (rngl_lt_le_incl Hor) in Hzc1.
    apply (rngl_add_nonneg_nonneg Hor); [ | easy ].
    apply (rngl_lt_le_incl Hor) in Hzs1, Hc2z.
    now apply rngl_sin_add_nonneg.
  } {
    apply (rngl_nle_gt Hor) in Hs2z.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
      change_angle_add_r θ2 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzc2.
      progress sin_cos_add_sub_right_hyp T Hs2z.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_goal T.
      apply (rngl_nlt_ge Hor).
      intros Hcc.
      assert (Hss : (0 ≤ rngl_sin (θ1 + θ2))%L). {
        apply (rngl_lt_le_incl Hor) in Hzs1, Hzc1, Hs2z.
        now apply rngl_sin_add_nonneg.
      }
      assert (Haov : angle_add_overflow θ1 θ2 = false). {
        progress unfold angle_add_overflow.
        progress unfold angle_ltb.
        generalize Hss; intros H.
        apply rngl_leb_le in H.
        rewrite H; clear H.
        generalize Hzs1; intros H.
        apply (rngl_lt_le_incl Hor) in H.
        apply rngl_leb_le in H.
        rewrite H; clear H.
        apply (rngl_ltb_ge Hor).
        apply (rngl_lt_le_incl Hor) in Hzs1, Hzc1, Hs2z.
        now apply quadrant_1_rngl_cos_add_le_cos_l.
      }
      specialize (angle_div_2_add_not_overflow θ1 θ2 Haov) as H1.
      rewrite angle_sub_straight_eq_add_straight in Hzs12d.
      apply (rngl_opp_le_compat Hop Hor) in Hzs12d.
      rewrite (rngl_opp_0 Hop) in Hzs12d.
      rewrite <- rngl_sin_add_straight_r in Hzs12d.
      rewrite <- rngl_sin_angle_div_2_add_overflow in Hzs12d. 2: {
        progress unfold angle_add_overflow.
        rewrite angle_add_sub_assoc.
        rewrite angle_add_sub_swap.
        rewrite <- angle_add_sub_assoc.
        rewrite angle_straight_sub_right.
        rewrite angle_add_add_swap.
        progress unfold angle_ltb.
        rewrite rngl_sin_add_right_r.
        rewrite rngl_sin_add_straight_r.
        rewrite rngl_cos_add_straight_r.
        rewrite rngl_cos_add_right_r.
        rewrite rngl_leb_opp_r.
        rewrite (rngl_opp_0 Hop).
        generalize Hzs12; intros H.
        apply (rngl_leb_gt Hor) in H.
        rewrite H; clear H.
        generalize Hzs1; intros H.
        apply (rngl_leb_gt Hor) in H.
        rewrite H; clear H.
        rewrite rngl_ltb_opp_r, (rngl_opp_involutive Hop).
        now apply rngl_ltb_lt.
      }
      apply (rngl_nlt_ge Hor) in Hzs12d.
      apply Hzs12d; clear Hzs12d.
      apply (rngl_lt_iff Hor).
      split; [ apply rngl_sin_div_2_nonneg | ].
      rewrite angle_add_sub_assoc.
      rewrite angle_add_add_swap.
      rewrite <- angle_add_sub_assoc.
      rewrite angle_straight_sub_right.
      intros H; symmetry in H.
      apply eq_rngl_sin_0 in H.
      destruct H as [H| H]. {
        apply eq_angle_div_2_0 in H.
        apply angle_add_move_0_r in H.
        apply (rngl_nlt_ge Hor) in Hss.
        apply Hss; clear Hss.
        rewrite H; cbn.
        apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
      }
      now apply (angle_div_2_not_straight Hc1) in H.
    }
    apply (rngl_nle_gt Hor) in Hc2z.
    change_angle_add_r θ2 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hc2z.
    progress sin_cos_add_sub_straight_hyp T Hs2z.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_goal T.
    apply (rngl_nlt_ge Hor).
    intros Hcc.
    apply (rngl_nlt_ge Hor) in Hzs12d.
    apply Hzs12d; clear Hzs12d.
    do 2 rewrite angle_sub_straight_eq_add_straight.
    apply (rngl_opp_lt_compat Hop Hor).
    rewrite (rngl_opp_0 Hop).
    rewrite <- rngl_sin_add_straight_r.
    rewrite <- angle_div_2_add_overflow. 2: {
      progress unfold angle_add_overflow.
      rewrite angle_add_assoc.
      rewrite angle_add_add_swap.
      rewrite <- (angle_add_assoc θ1).
      rewrite angle_straight_add_straight, angle_add_0_r.
      apply angle_lt_iff.
      split. {
        apply angle_add_le_mono_l. {
          apply (rngl_lt_le_incl Hor) in Hs2z.
          apply angle_add_overflow_lt_straight_le_straight.
          now apply rngl_sin_pos_lt_straight.
          now apply rngl_sin_nonneg_le_straight.
        } {
          apply angle_add_straight_r_not_overflow.
          now apply rngl_sin_pos_lt_straight.
        } {
          apply (rngl_lt_le_incl Hor) in Hs2z.
          now apply rngl_sin_nonneg_angle_le_straight.
        }
      }
      intros H.
      apply (f_equal (λ θ, angle_sub θ θ1)) in H.
      rewrite angle_add_comm, angle_add_sub in H.
      rewrite angle_add_sub_swap, angle_sub_diag in H.
      rewrite angle_add_0_l in H; subst θ2.
      now apply (rngl_lt_irrefl Hor) in Hs2z.
    }
    rewrite angle_add_assoc.
    rewrite (angle_add_add_swap θ1).
    rewrite <- angle_add_assoc.
    rewrite angle_straight_add_straight, angle_add_0_r.
    apply (rngl_lt_iff Hor).
    split; [ apply rngl_sin_div_2_nonneg | ].
    intros H; symmetry in H.
    apply eq_rngl_sin_0 in H.
    destruct H as [H12d| H12d]. {
      apply eq_angle_div_2_0 in H12d.
      rewrite H12d in Hzs12.
      now apply (rngl_lt_irrefl Hor) in Hzs12.
    }
    now apply (angle_div_2_not_straight Hc1) in H12d.
  }
}
Qed.

Theorem angle_mul_nat_overflow_2_pow_div_angle_mul :
  ∀ n i θ,
  angle_mul_nat_overflow (2 ^ i / n) (n * (θ / ₂^i)) = false.
Proof.
destruct_ac.
intros.
(* lemma to do *)
apply Bool.not_true_iff_false.
intros H1.
apply angle_mul_nat_overflow_true_assoc in H1.
apply Bool.not_false_iff_true in H1.
apply H1; clear H1.
(**)
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)). {
  rewrite Nat.mul_comm.
  now apply Nat.mul_div_le.
}
apply angle_mul_nat_overflow_pow_div.
Qed.

Theorem angle_div_2_pow_1 : ∀ θ, (θ / ₂^1 = θ / ₂)%A.
Proof. easy. Qed.

Theorem angle_add_overflow_mul_div_2_pow :
  ∀ n i θ,
  n < 2 ^ i
  → angle_add_overflow (θ / ₂^i) (n * (θ / ₂^i)) = false.
Proof.
destruct_ac.
intros * Hni.
revert θ n Hni.
induction i; intros. {
  cbn in Hni.
  apply Nat.succ_le_mono in Hni.
  apply Nat.le_0_r in Hni; subst n.
  apply angle_add_overflow_0_r.
}
destruct (le_dec (S n) (2 ^ i)) as [Hsni| Hsni]. {
  rewrite angle_div_2_pow_succ_r_2.
  now apply IHi.
}
apply Nat.nle_gt in Hsni.
apply -> Nat.le_succ_l in Hni.
apply -> Nat.lt_succ_r in Hsni.
assert (H1 : n = 2 ^ i + n mod 2 ^ i). {
  specialize (Nat.div_mod n (2 ^ i)) as H1.
  assert (H : 2 ^ i ≠ 0) by now apply Nat.pow_nonzero.
  specialize (H1 H); clear H.
  rewrite (Nat_div_less_small 1) in H1; [ now rewrite Nat.mul_1_r in H1 | ].
  now rewrite Nat.mul_1_l.
}
rewrite H1.
rewrite angle_mul_add_distr_r.
rewrite angle_div_2_pow_succ_r_2 at 2.
rewrite angle_div_2_pow_mul_2_pow.
rewrite angle_div_2_pow_succ_r_1.
rewrite angle_mul_nat_div_2. 2: {
  apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)).
  apply Nat.lt_le_incl, Nat.mod_upper_bound.
  now apply Nat.pow_nonzero.
  apply angle_mul_nat_overflow_pow_div.
}
apply angle_add_not_overflow_move_add. 2: {
  rewrite <- angle_div_2_add_not_overflow. 2: {
    apply IHi.
    apply Nat.mod_upper_bound.
    now apply Nat.pow_nonzero.
  }
  apply angle_add_overflow_div_2_div_2.
}
apply angle_add_overflow_div_2_div_2.
Qed.

Theorem angle_mul_nat_overflow_div_2_pow :
  ∀ n i θ,
  n ≤ 2 ^ i
  → angle_mul_nat_overflow n (θ / ₂^i) = false.
Proof.
destruct_ac.
intros * Hni.
revert i θ Hni.
induction n; intros; [ easy | ].
rewrite (angle_mul_nat_overflow_succ_l Hon Hos).
apply Bool.orb_false_iff.
split. {
  apply IHn.
  apply (Nat.le_trans _ (S n)); [ | easy ].
  apply Nat.le_succ_diag_r.
}
now apply angle_add_overflow_mul_div_2_pow.
Qed.

Theorem angle_mul_div_2_pow_le_straight :
  ∀ n i θ,
  2 * n ≤ 2 ^ i
  → (n * (θ / ₂^i) ≤ angle_straight)%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ * _)%A).
  apply angle_nonneg.
}
intros * Hni.
revert θ.
induction i; intros. {
  cbn in Hni.
  rewrite Nat.add_0_r in Hni.
  destruct n; [ apply (angle_straight_nonneg Hc1) | ].
  cbn in Hni.
  apply Nat.succ_le_mono in Hni.
  rewrite <- Nat.add_succ_comm in Hni; cbn in Hni.
  easy.
}
destruct (le_dec (2 * n) (2 ^ i)) as [Hni1| Hni1]. {
  rewrite angle_div_2_pow_succ_r_2.
  now apply IHi.
}
apply Nat.nle_gt in Hni1.
clear IHi.
rewrite Nat.pow_succ_r' in Hni.
apply Nat.mul_le_mono_pos_l in Hni; [ | easy ].
rewrite angle_div_2_pow_succ_r_1.
rewrite angle_mul_nat_div_2. 2: {
  now apply angle_mul_nat_overflow_div_2_pow.
}
apply angle_div_2_le_straight.
Qed.

Theorem angle_div_2_pow_mul_le_angle :
  ∀ n i θ, n ≤ 2 ^ i → (n * (θ / ₂^i) ≤ θ)%A.
Proof.
intros * Hni.
destruct (le_dec (2 ^ i) n) as [Hin| Hin]. {
  apply Nat.le_antisymm in Hin; [ | easy ].
  subst n.
  rewrite angle_div_2_pow_mul_2_pow.
  apply angle_le_refl.
}
apply Nat.nle_gt in Hin.
clear Hni; rename Hin into Hni.
revert n θ Hni.
induction i; intros. {
  cbn in Hni.
  apply Nat.lt_1_r in Hni; subst n; cbn.
  apply angle_nonneg.
}
destruct (lt_dec n (2 ^ i)) as [Hin| Hin]. {
  rewrite angle_div_2_pow_succ_r_2.
  apply (angle_le_trans _ (θ / ₂)); [ now apply IHi | ].
  apply angle_div_2_le.
}
apply Nat.nlt_ge in Hin.
assert (H1 : n = 2 ^ i + n mod 2 ^ i). {
  specialize (Nat.div_mod n (2 ^ i)) as H1.
  assert (H : 2 ^ i ≠ 0) by now apply Nat.pow_nonzero.
  specialize (H1 H); clear H.
  rewrite (Nat_div_less_small 1) in H1; [ now rewrite Nat.mul_1_r in H1 | ].
  now rewrite Nat.mul_1_l.
}
rewrite H1.
rewrite angle_mul_add_distr_r.
rewrite angle_div_2_pow_succ_r_2 at 1.
rewrite angle_div_2_pow_mul_2_pow.
apply angle_le_trans with (θ2 := (θ / ₂ + θ / ₂)%A). {
  apply angle_add_le_mono_l; cycle 1. {
    apply angle_add_overflow_div_2_div_2.
  } {
    rewrite angle_div_2_pow_succ_r_2.
    apply IHi.
    apply Nat.mod_upper_bound.
    now apply Nat.pow_nonzero.
  }
  apply angle_add_overflow_le with (θ2 := (θ / ₂)%A). 2: {
    apply angle_add_overflow_div_2_div_2.
  }
  rewrite angle_div_2_pow_succ_r_2.
  apply IHi.
  apply Nat.mod_upper_bound.
  now apply Nat.pow_nonzero.
}
rewrite angle_add_div_2_diag.
apply angle_le_refl.
Qed.

Theorem angle_add_lt_mono_l :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ2 = false
  → angle_add_overflow θ1 θ3 = false
  → (θ2 < θ3)%A → (θ1 + θ2 < θ1 + θ3)%A.
Proof.
intros * H12 H13 H23.
apply angle_lt_iff.
split. {
  apply angle_add_le_mono_l; [ easy | easy | ].
  now apply angle_lt_le_incl in H23.
}
intros H.
apply (f_equal (λ θ, (θ - θ1)%A)) in H.
do 2 rewrite angle_add_comm, angle_add_sub in H.
subst θ3.
now apply angle_lt_irrefl in H23.
Qed.

Theorem angle_div_2_pow_mul_lt_angle :
  ∀ n i θ, θ ≠ 0%A → n < 2 ^ i → (n * (θ / ₂^i) < θ)%A.
Proof.
intros * Htz Hni.
revert n θ Hni Htz.
induction i; intros. {
  cbn in Hni.
  apply Nat.lt_1_r in Hni; subst n; cbn.
  apply angle_lt_iff.
  split; [ apply angle_nonneg | ].
  now intros H; apply Htz; symmetry.
}
destruct (lt_dec n (2 ^ i)) as [Hin| Hin]. {
  rewrite angle_div_2_pow_succ_r_2.
  apply (angle_lt_le_trans _ (θ / ₂)). {
    apply IHi; [ easy | ].
    intros H.
    now apply eq_angle_div_2_0 in H.
  }
  apply angle_div_2_le.
}
apply Nat.nlt_ge in Hin.
assert (H1 : n = 2 ^ i + n mod 2 ^ i). {
  specialize (Nat.div_mod n (2 ^ i)) as H1.
  assert (H : 2 ^ i ≠ 0) by now apply Nat.pow_nonzero.
  specialize (H1 H); clear H.
  rewrite (Nat_div_less_small 1) in H1; [ now rewrite Nat.mul_1_r in H1 | ].
  now rewrite Nat.mul_1_l.
}
rewrite H1.
rewrite angle_mul_add_distr_r.
rewrite angle_div_2_pow_succ_r_2 at 1.
rewrite angle_div_2_pow_mul_2_pow.
apply angle_lt_le_trans with (θ2 := (θ / ₂ + θ / ₂)%A). {
  apply angle_add_lt_mono_l; cycle 1. {
    apply angle_add_overflow_div_2_div_2.
  } {
    rewrite angle_div_2_pow_succ_r_2.
    apply IHi. {
      apply Nat.mod_upper_bound.
      now apply Nat.pow_nonzero.
    }
    intros H.
    now apply eq_angle_div_2_0 in H.
  }
  apply angle_add_overflow_le with (θ2 := (θ / ₂)%A). 2: {
    apply angle_add_overflow_div_2_div_2.
  }
  rewrite angle_div_2_pow_succ_r_2.
  apply angle_lt_le_incl.
  apply IHi. {
    apply Nat.mod_upper_bound.
    now apply Nat.pow_nonzero.
  }
  intros H.
  now apply eq_angle_div_2_0 in H.
}
rewrite angle_add_div_2_diag.
apply angle_le_refl.
Qed.

Theorem angle_add_overflow_2_pow_div_mul_2_pow_diag :
  ∀ n i θ,
  1 < n ≤ 2 ^ i
  → angle_add_overflow (2 ^ i / n * (θ / ₂^i)) (2 ^ i / n * (θ / ₂^i)) =
      false.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ * _)%A).
  apply angle_add_overflow_0_l.
}
intros * (Hmi, Hni).
assert (Hnz : n ≠ 0) by flia Hmi.
progress unfold angle_add_overflow.
apply angle_ltb_ge.
progress unfold angle_leb.
remember (seq_angle_to_div_nat θ n) as u eqn:Hu.
remember (0 ≤? rngl_sin (u i))%L as zs eqn:Hzs.
symmetry in Hzs.
rewrite Hu in Hzs.
progress unfold seq_angle_to_div_nat in Hzs.
rewrite Hzs.
destruct zs. {
  apply rngl_leb_le in Hzs.
  remember (0 ≤? rngl_sin (u i + u i))%L as zsm eqn:Hzsm.
  symmetry in Hzsm.
  rewrite Hu in Hzsm.
  progress unfold seq_angle_to_div_nat in Hzsm.
  rewrite Hzsm.
  destruct zsm; [ | easy ].
  apply rngl_leb_le in Hzsm.
  apply rngl_leb_le.
  rewrite angle_add_diag in Hzsm |-*.
  rewrite rngl_sin_mul_2_l in Hzsm.
  rewrite rngl_cos_mul_2_l'.
  apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzsm.
  remember (rngl_cos (u i)) as x eqn:Hx.
  rewrite Hu in Hx.
  progress unfold seq_angle_to_div_nat in Hx.
  rewrite <- Hx.
  destruct Hzsm as [(_, Hzsm)| (H1, H2)]. 2: {
    destruct (rngl_eq_dec Hed (rngl_sin (u i)) 0) as [Hxz| Hxz]. {
      rewrite Hu in Hxz.
      progress unfold seq_angle_to_div_nat in Hxz.
      apply eq_rngl_sin_0 in Hxz.
      destruct Hxz as [Hxz| Hxz]. {
        rewrite Hxz in Hx; cbn in Hx; subst x.
        exfalso; apply (rngl_nlt_ge Hor) in H2.
        apply H2; clear H2.
        rewrite Hxz.
        apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
      } {
        rewrite Hxz in Hx; cbn in Hx; subst x.
        exfalso; clear H1 H2 Hzs.
        revert Hxz.
        apply fold_not.
        destruct n; [ easy | clear Hnz ].
        apply Nat.succ_lt_mono in Hmi.
        destruct n; [ flia Hmi | clear Hmi ].
        destruct n. {
          destruct i; [ cbn in Hni; flia Hni | ].
          rewrite Nat.pow_succ_r'.
          rewrite Nat.mul_comm.
          rewrite Nat.div_mul; [ | easy ].
          rewrite angle_div_2_pow_succ_r_2.
          rewrite angle_div_2_pow_mul_2_pow.
          now apply (angle_div_2_not_straight Hc1).
        }
        destruct i; [ cbn in Hni; flia Hni | ].
        rewrite angle_div_2_pow_succ_r_2.
        specialize angle_div_2_pow_mul_le_angle as H1.
        specialize (H1 (2 ^ S i / S (S (S n))) i (θ / ₂)%A).
        assert (H : 2 ^ S i / S (S (S n)) ≤ 2 ^ i). {
          rewrite Nat.pow_succ_r'.
          apply Nat.div_le_upper_bound; [ easy | ].
          apply Nat.mul_le_mono_r.
          now do 2 apply -> Nat.succ_le_mono.
        }
        specialize (H1 H); clear H.
        intros Hxz.
        rewrite Hxz in H1.
        apply angle_nlt_ge in H1.
        apply H1.
        apply (angle_div_2_lt_straight Hc1).
      }
    }
    exfalso.
    rewrite Hu in Hxz.
    progress unfold seq_angle_to_div_nat in Hxz.
    apply (rngl_le_antisymm Hor) in Hzs; [ easy | ].
    apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ 2%L). {
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    }
    now rewrite rngl_mul_0_r.
  }
  (* variation of the curve y=2x²-x-1 in interval [-1,1] *)
  apply rngl_2_x2_sub_1_le_x.
  rewrite <- Hx in Hzsm.
  split; [ easy | ].
  subst x; apply rngl_cos_bound.
}
apply (rngl_leb_gt Hor) in Hzs.
apply (rngl_nle_gt Hor) in Hzs.
exfalso.
apply Hzs; clear Hzs.
destruct i; [ cbn in Hni; flia Hni Hmi | ].
apply rngl_sin_nonneg_angle_le_straight.
apply angle_mul_div_2_pow_le_straight.
eapply Nat.le_trans; [ now apply Nat.div_mul_le | ].
apply Nat.div_le_upper_bound; [ easy | ].
now apply Nat.mul_le_mono_r.
Qed.

Theorem rngl_mul_if_then_else_distr_l :
  ∀ (v : bool) a b c,
  ((a * if v then b else c) = (if v then a * b else a * c))%L.
Proof. now intros; destruct v. Qed.

Theorem rngl_add_if_then_else_distr_r :
  ∀ (v : bool) a b c,
  ((if v then a else b) + c = if v then a + c else b + c)%L.
Proof. intros; now destruct v. Qed.

Theorem rngl_if_then_else_eq_compat :
  ∀ {A} (u : bool) (a b c d : A),
  (u = true → a = c)
  → (u = false → b = d)
  → ((if u then a else b) = (if u then c else d))%L.
Proof.
intros * Ht Hf.
now destruct u; [ apply Ht | apply Hf ].
Qed.

Theorem binomial_0_r : ∀ n, binomial n 0 = 1.
Proof. now intros; destruct n. Qed.

Theorem binomial_succ_l :
  ∀ n k,
  binomial (S n) k =
    match k with
    | 0 => 1
    | S k' => binomial n k' + binomial n k
    end.
Proof. easy. Qed.

Theorem gre_summation :
  rngl_has_opp T = true →
  let roc := gc_ring_like_op T in
  ∀ b e (f : nat → GComplex T),
  gre (∑ (i = b, e), f i)%L = (∑ (i = b, e), gre (f i))%L.
Proof.
intros Hop.
intros.
progress unfold iter_seq.
progress unfold iter_list.
remember (S e - b) as len eqn:Hlen.
clear e Hlen.
cbn.
revert b.
induction len; intros; [ easy | cbn ].
rewrite fold_left_rngl_add_fun_from_0.
rewrite rngl_add_0_l.
rewrite <- IHlen.
rewrite fold_left_op_fun_from_d with (d := 0%L); cycle 1.
apply gc_add_0_l.
intros; cbn.
set (rop := gc_ring_like_prop_not_alg_closed Hop).
specialize gc_add_comm as H1; cbn in H1.
rewrite H1; clear H1.
apply gc_add_0_l.
apply gc_add_assoc.
cbn.
f_equal.
apply rngl_add_0_l.
Qed.

Theorem gim_summation :
  rngl_has_opp T = true →
  let roc := gc_ring_like_op T in
  ∀ b e (f : nat → GComplex T),
  gim (∑ (i = b, e), f i)%L = (∑ (i = b, e), gim (f i))%L.
Proof.
intros Hop.
intros.
progress unfold iter_seq.
progress unfold iter_list.
remember (S e - b) as len eqn:Hlen.
clear e Hlen.
cbn.
revert b.
induction len; intros; [ easy | cbn ].
rewrite fold_left_rngl_add_fun_from_0.
rewrite rngl_add_0_l.
rewrite <- IHlen.
rewrite fold_left_op_fun_from_d with (d := 0%L); cycle 1.
apply gc_add_0_l.
intros; cbn.
set (rop := gc_ring_like_prop_not_alg_closed Hop).
specialize gc_add_comm as H1; cbn in H1.
rewrite H1; clear H1.
apply gc_add_0_l.
apply gc_add_assoc.
cbn.
f_equal.
apply rngl_add_0_l.
Qed.

Theorem gre_1 :
  let roc := gc_ring_like_op T in
  (gre 1 = 1%L).
Proof.
intros.
cbn; progress unfold rngl_one.
cbn; progress unfold gc_opt_one.
now destruct (rngl_opt_one T).
Qed.

Theorem gim_1 :
  let roc := gc_ring_like_op T in
  (gim 1 = 0%L).
Proof.
intros.
cbn; progress unfold rngl_one.
cbn; progress unfold gc_opt_one.
now destruct (rngl_opt_one T).
Qed.

Theorem gc_power_re_0 :
  ∀ n y,
  (mk_gc 0 y ^ n =
     if Nat.even n then
       mk_gc ((minus_one_pow (n / 2)) * (y ^ n))%L 0
     else
       mk_gc 0 ((minus_one_pow (n / 2)) * (y ^ n))%L)%C.
Proof.
destruct_ac.
intros.
remember (Nat.even n) as b eqn:Hb; symmetry in Hb.
destruct b. {
  apply Nat.even_spec in Hb.
  destruct Hb as (m, Hm).
  subst n.
  rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
  progress unfold gc_power_nat.
  induction m; cbn. {
    rewrite (rngl_mul_1_l Hon).
    apply eq_gc_eq.
    cbn; progress unfold rngl_one.
    cbn; progress unfold gc_opt_one.
    now destruct (rngl_opt_one T).
  }
  rewrite IHm.
  progress unfold gc_mul.
  cbn.
  do 4 rewrite (rngl_mul_0_l Hos).
  do 2 rewrite (rngl_sub_0_l Hop).
  rewrite (rngl_mul_0_r Hos).
  do 2 rewrite rngl_add_0_r.
  rewrite (rngl_opp_0 Hop).
  rewrite (rngl_mul_0_r Hos).
  f_equal.
  do 4 rewrite rngl_mul_assoc.
  rewrite <- (rngl_mul_opp_l Hop).
  f_equal.
  rewrite (rngl_mul_comm Hic).
  rewrite <- (rngl_mul_opp_l Hop).
  rewrite <- rngl_mul_assoc.
  f_equal.
  symmetry.
  apply (minus_one_pow_succ Hop).
} {
  destruct n; [ easy | ].
  apply (f_equal negb) in Hb.
  rewrite Nat.even_succ in Hb.
  cbn in Hb.
  rewrite Nat.negb_odd in Hb.
  apply Nat.even_spec in Hb.
  destruct Hb as (m, Hm).
  subst n.
  rewrite <- Nat.add_1_r.
  rewrite Nat.mul_comm, Nat.div_add_l; [ | easy ].
  rewrite Nat.div_small; [ | easy ].
  rewrite Nat.add_0_r.
  progress unfold gc_power_nat.
  induction m; cbn. {
    rewrite (rngl_mul_1_l Hon).
    rewrite (rngl_mul_1_r Hon).
    apply eq_gc_eq; cbn.
    rewrite gre_1, gim_1.
    do 2 rewrite (rngl_mul_0_l Hos).
    rewrite (rngl_mul_0_r Hos).
    rewrite (rngl_sub_0_r Hos).
    rewrite (rngl_mul_1_r Hon).
    rewrite rngl_add_0_r.
    easy.
  }
  rewrite IHm.
  progress unfold gc_mul.
  cbn.
  do 4 rewrite (rngl_mul_0_l Hos).
  do 2 rewrite (rngl_sub_0_l Hop).
  rewrite (rngl_mul_0_r Hos).
  do 2 rewrite rngl_add_0_r.
  rewrite (rngl_mul_0_r Hos).
  rewrite (rngl_opp_0 Hop).
  f_equal.
  rewrite <- (rngl_mul_opp_r Hop).
  rewrite <- (rngl_mul_opp_l Hop).
  do 4 rewrite rngl_mul_assoc.
  f_equal.
  rewrite (rngl_mul_comm Hic).
  rewrite <- rngl_mul_assoc.
  f_equal.
  symmetry.
  apply (minus_one_pow_succ Hop).
}
Qed.

Theorem gre_rngl_of_nat :
  let gro := gc_ring_like_op T : ring_like_op (GComplex T) in
  ∀ n, gre (rngl_of_nat n) = rngl_of_nat n.
Proof.
intros.
induction n; [ easy | ].
do 2 rewrite rngl_of_nat_succ.
cbn; rewrite IHn.
f_equal.
progress unfold gro.
now rewrite gre_1.
Qed.

Theorem gim_rngl_of_nat :
  let gro := gc_ring_like_op T : ring_like_op (GComplex T) in
  ∀ n, gim (rngl_of_nat n) = 0%L.
Proof.
intros.
induction n; [ easy | ].
rewrite rngl_of_nat_succ.
cbn; rewrite IHn.
progress unfold gro.
rewrite gim_1.
apply rngl_add_0_l.
Qed.

Theorem rngl_cos_sin_nx :
  ∀ n θ,
  rngl_cos (n * θ) =
    (∑ (i = 0, n),
       if Nat.even i then
         minus_one_pow (i / 2) * rngl_of_nat (binomial n i) *
         (rngl_cos θ) ^ (n - i) * (rngl_sin θ) ^ i
       else 0)%L ∧
  rngl_sin (n * θ) =
    (∑ (i = 0, n),
       if Nat.odd i then
         minus_one_pow (i / 2) * rngl_of_nat (binomial n i) *
         (rngl_cos θ) ^ (n - i) * (rngl_sin θ) ^ i
       else 0)%L.
Proof.
destruct_ac.
intros.
specialize (@newton_binomial) as H1.
set (gro := gc_ring_like_op T).
specialize (H1 (GComplex T)).
specialize (H1 gro).
specialize (H1 (gc_ring_like_prop_not_alg_closed Hop)).
assert (Honc : rngl_has_1 (GComplex T) = true). {
  progress unfold rngl_has_1 in Hon.
  progress unfold rngl_has_1.
  cbn.
  progress unfold gc_opt_one.
  now destruct (rngl_opt_one T).
}
assert (Hosc : rngl_has_opp_or_subt (GComplex T) = true). {
  progress unfold rngl_has_opp_or_subt in Hos.
  progress unfold rngl_has_opp_or_subt.
  cbn.
  progress unfold gc_opt_opp_or_subt.
  destruct rngl_opt_opp_or_subt as [s| ]; [ | easy ].
  now destruct s.
}
specialize (H1 Hic Honc Hosc n).
specialize (H1 (mk_gc (rngl_cos θ) 0)).
specialize (H1 (mk_gc 0 (rngl_sin θ))).
cbn - [ rngl_add rngl_zero ] in H1.
remember (∑ (k = _, _), _) as x in H1.
cbn in H1; subst x.
progress unfold gc_add in H1.
cbn - [ rngl_add rngl_zero ] in H1.
rewrite rngl_add_0_r in H1.
rewrite rngl_add_0_l in H1.
progress unfold gro in H1.
specialize (gc_cos_sin_pow θ n) as H2.
progress unfold gc_power_nat in H2.
rewrite H2 in H1; clear H2.
apply eq_gc_eq in H1.
cbn - [ rngl_add rngl_zero ] in H1.
rewrite (gre_summation Hop) in H1.
rewrite (gim_summation Hop) in H1.
destruct H1 as (Hc, Hs).
split. {
  rewrite Hc.
  apply rngl_summation_eq_compat.
  intros * (_, Hi).
  specialize (gc_power_im_0 Hos) as H1.
  progress unfold gc_power_nat in H1.
  rewrite H1.
  specialize gc_power_re_0 as H2.
  progress unfold gc_power_nat in H2.
  rewrite H2.
  cbn - [ "/" ].
  do 2 rewrite (rngl_mul_0_r Hos).
  rewrite (rngl_sub_0_r Hos).
  rewrite rngl_add_0_r.
  rewrite gre_rngl_of_nat.
  rewrite gim_rngl_of_nat.
  do 2 rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_sub_0_r Hos).
  remember (Nat.even i) as ei eqn:Hei.
  symmetry in Hei.
  destruct ei. {
    cbn - [ "/" "*" ].
    rewrite rngl_mul_assoc.
    f_equal.
    rewrite (rngl_mul_comm Hic).
    apply rngl_mul_assoc.
  } {
    cbn - [ "/" "*" ].
    apply (rngl_mul_0_r Hos).
  }
} {
  rewrite Hs.
  apply rngl_summation_eq_compat.
  intros * (_, Hi).
  cbn - [ "/" "*" ].
  rewrite gre_rngl_of_nat.
  rewrite gim_rngl_of_nat.
  do 2 rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_sub_0_r Hos).
  rewrite rngl_add_0_l.
  specialize (gc_power_im_0 Hos) as H1.
  progress unfold gc_power_nat in H1.
  rewrite H1.
  specialize gc_power_re_0 as H2.
  progress unfold gc_power_nat in H2.
  rewrite H2.
  cbn - [ "/" ].
  rewrite (rngl_mul_0_r Hos).
  rewrite (rngl_mul_0_l Hos).
  rewrite rngl_add_0_l.
  rewrite <- Nat.negb_even.
  remember (Nat.even i) as ei eqn:Hei.
  symmetry in Hei.
  destruct ei. {
    cbn - [ "/" "*" ].
    apply (rngl_mul_0_r Hos).
  } {
    cbn - [ "/" "*" ].
    rewrite rngl_mul_assoc.
    f_equal.
    rewrite (rngl_mul_comm Hic).
    apply rngl_mul_assoc.
  }
}
Qed.

Theorem rngl_cos_nx :
  ∀ n θ,
  rngl_cos (n * θ) =
    (∑ (i = 0, n),
       if Nat.even i then
         minus_one_pow (i / 2) * rngl_of_nat (binomial n i) *
         (rngl_cos θ) ^ (n - i) * (rngl_sin θ) ^ i
       else 0)%L.
Proof.
intros.
apply rngl_cos_sin_nx.
Qed.

Theorem rngl_sin_nx :
  ∀ n θ,
  rngl_sin (n * θ) =
    (∑ (i = 0, n),
       if Nat.odd i then
         minus_one_pow (i / 2) * rngl_of_nat (binomial n i) *
         (rngl_cos θ) ^ (n - i) * (rngl_sin θ) ^ i
       else 0)%L.
Proof.
intros.
apply rngl_cos_sin_nx.
Qed.

Theorem angle_lim_move_0_r :
  ∀ f θ, angle_lim f θ → angle_lim (λ i, (f i - θ)%A) 0%A.
Proof.
intros * Hlim.
progress unfold angle_lim in Hlim.
progress unfold angle_lim.
intros ε Hε.
specialize (Hlim ε Hε).
destruct Hlim as (N, HN).
exists N.
intros n Hn.
specialize (HN n Hn).
now rewrite angle_eucl_dist_move_0_r in HN.
Qed.

Theorem angle_lim_0_le_if :
  ∀ f g,
  (∀ i, (f i ≤ g i ≤ angle_straight)%A)
  → angle_lim g 0
  → angle_lim f 0.
Proof.
destruct_ac.
intros * Hfg Hg.
intros ε Hε.
specialize (Hg ε Hε).
destruct Hg as (N, HN).
exists N.
intros n Hn.
specialize (HN n Hn).
eapply (rngl_le_lt_trans Hor); [ | apply HN ].
apply (rngl_cos_le_iff_angle_eucl_le (g n)).
apply rngl_cos_decr.
apply Hfg.
Qed.

Theorem angle_le_eucl_dist_le :
  ∀ θ1 θ2,
  (θ1 ≤ θ2 ≤ angle_straight)%A
  → (angle_eucl_dist θ1 θ2 ≤ angle_eucl_dist θ2 0)%L.
Proof.
destruct_ac.
intros * H12.
rewrite (angle_eucl_dist_symmetry Hic Hop θ2).
apply angle_dist_le_r; [ easy | ].
split; [ apply angle_nonneg | easy ].
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

Theorem angle_same_lim_sub :
  ∀ u v θ, angle_lim u θ → angle_lim v θ → angle_lim (λ i, (u i - v i)%A) 0.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hu Hv ε Hε.
  rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hu Hv.
intros ε Hε.
assert (Hε2 : (0 < ε / 2)%L). {
  apply (rngl_lt_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  now rewrite (rngl_mul_0_l Hos).
}
specialize (Hu _ Hε2)%L.
specialize (Hv _ Hε2)%L.
destruct Hu as (M, HM).
destruct Hv as (N, HN).
exists (max M N).
intros n Hn.
specialize (rngl_div_add_distr_r Hiv ε ε 2)%L as H2.
rewrite (rngl_add_diag2 Hon) in H2.
rewrite (rngl_mul_div Hi1) in H2. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
rewrite H2.
rewrite <- angle_eucl_dist_move_0_r.
eapply (rngl_le_lt_trans Hor). {
  apply (angle_eucl_dist_triangular _ θ).
}
rewrite (angle_eucl_dist_symmetry Hic Hop θ).
specialize (HM _ (Nat.max_lub_l _ _ _ Hn)).
specialize (HN _ (Nat.max_lub_r _ _ _ Hn)).
now apply (rngl_add_lt_compat Hop Hor).
Qed.

Theorem angle_sub_mul_l_diag_r :
  ∀ n θ, n ≠ 0 → (n * θ - θ)%A = ((n - 1) * θ)%A.
Proof.
intros * Hnz.
rewrite angle_mul_sub_distr_r. 2: {
  apply Nat.le_succ_l.
  now apply Nat.neq_0_lt_0.
}
now rewrite angle_mul_1_l.
Qed.

Theorem Nat_add_mul_r_diag_r : ∀ a b, a + b * a = (1 + b) * a.
Proof. easy. Qed.

Theorem angle_add_mul_r_diag_r : ∀ n θ, (θ + n * θ)%A = (S n * θ)%A.
Proof. easy. Qed.

Theorem angle_right_div_2_lt :
  ∀ θ,
  (rngl_cos θ < rngl_sin θ)%L
  → (0 ≤ rngl_sin θ)%L
  → (0 ≤ rngl_cos θ)%L
  → (angle_right / ₂ < θ)%A.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hcs Hs Hc.
  rewrite (H1 (rngl_cos _)) in Hcs.
  rewrite (H1 (rngl_sin _)) in Hcs.
  now apply (rngl_lt_irrefl Hor) in Hcs.
}
intros * Hcs Hs Hc.
progress unfold angle_ltb.
cbn.
rewrite (rngl_sub_0_r Hos), rngl_add_0_r.
apply rngl_leb_le in Hs; rewrite Hs.
apply rngl_leb_le in Hs.
specialize (rngl_0_le_1 Hon Hop Hor) as H1.
apply rngl_leb_le in H1.
rewrite H1; clear H1.
rewrite (rngl_mul_1_l Hon).
specialize rl_sqrt_half_nonneg as Hzs.
generalize Hzs; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_ltb_lt.
specialize (rngl_cos_div_2 angle_right) as H1.
cbn - [ rngl_cos ] in H1.
specialize (rngl_0_le_1 Hon Hop Hor) as H2.
apply rngl_leb_le in H2.
rewrite H2 in H1; clear H2.
rewrite (rngl_mul_1_l Hon) in H1.
cbn - [ angle_div_2 ] in H1.
rewrite rngl_add_0_r in H1.
rewrite <- H1.
apply angle_add_le_mono_l_lemma_39; try easy. {
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  intros H; symmetry in H.
  apply eq_rngl_sin_0 in H.
  destruct H; subst θ. {
    apply (rngl_nle_gt Hor) in Hcs.
    apply Hcs; clear Hcs; cbn.
    apply (rngl_0_le_1 Hon Hop Hor).
  }
  apply (rngl_nlt_ge Hor) in Hc.
  apply Hc; clear Hc; cbn.
  apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
} {
  now cbn; rewrite (rngl_sub_0_r Hos).
} {
  cbn.
  specialize (rngl_0_le_1 Hon Hop Hor) as H2.
  apply rngl_leb_le in H2.
  rewrite H2; clear H2.
  rewrite (rngl_mul_1_l Hon).
  now rewrite rngl_add_0_r.
} {
  cbn.
  specialize (rngl_0_le_1 Hon Hop Hor) as H2.
  apply rngl_leb_le in H2.
  rewrite H2; clear H2.
  rewrite (rngl_mul_1_l Hon).
  rewrite rngl_add_0_r, (rngl_sub_0_r Hos).
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  apply (rngl_mul_pos_pos Hop Hor Hii). {
    now apply (rngl_lt_0_sub Hop Hor).
  }
  apply (rl_sqrt_half_pos Hc1).
}
Qed.

Theorem rngl_sin_7_right_div_2 :
  rngl_sin (7 * (angle_right / ₂)) = (- √(1 / 2))%L.
Proof.
destruct_ac.
replace 7 with (2 + 5) by easy.
rewrite angle_mul_add_distr_r.
rewrite angle_div_2_mul_2.
rewrite (rngl_sin_add_right_l Hon Hos).
apply rngl_cos_5_right_div_2.
Qed.

Theorem rngl_cos_7_right_div_2 :
  rngl_cos (7 * (angle_right / ₂)) = √(1 / 2)%L.
Proof.
destruct_ac.
replace 7 with (2 + 5) by easy.
rewrite angle_mul_add_distr_r.
rewrite angle_div_2_mul_2.
rewrite (rngl_cos_add_right_l Hon Hop).
apply (rngl_opp_inj Hop).
rewrite (rngl_opp_involutive Hop).
apply rngl_sin_5_right_div_2.
Qed.

Theorem quadrant_1_angle_lt_3_angle_right_div_2 :
  rngl_characteristic T ≠ 1 →
  ∀ θ,
  (0 ≤ rngl_sin θ)%L
  → (0 ≤ rngl_cos θ)%L
  → (θ < 3 * (angle_right / ₂))%A.
Proof.
destruct_ac.
intros Hc1 * Hs Hc.
progress unfold angle_ltb.
apply rngl_leb_le in Hs.
rewrite Hs.
apply rngl_leb_le in Hs.
rewrite rngl_sin_3_right_div_2.
rewrite rngl_cos_3_right_div_2.
specialize rl_sqrt_half_nonneg as Hzs.
generalize Hzs; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_ltb_lt.
apply (rngl_lt_le_trans Hor _ 0); [ | easy ].
apply (rngl_opp_neg_pos Hop Hor).
apply (rl_sqrt_half_pos Hc1).
Qed.

Theorem quadrant_4_angle_lt_5_angle_right_div_2 :
  ∀ θ,
  (rngl_sin θ < 0)%L
  → (0 ≤ rngl_cos θ)%L
  → (5 * (angle_right / ₂) < θ)%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hs Hc.
  rewrite (H1 (rngl_sin _)) in Hs.
  now apply (rngl_lt_irrefl Hor) in Hs.
}
intros * Hs Hc.
progress unfold angle_ltb.
rewrite rngl_sin_5_right_div_2.
rewrite rngl_cos_5_right_div_2.
rewrite rngl_leb_opp_r, (rngl_opp_0 Hop).
generalize Hs; intros H.
apply (rngl_leb_gt Hor) in H.
rewrite H; clear H.
remember (√(1 / 2) ≤? 0)%L as sz eqn:Hsz.
symmetry in Hsz.
destruct sz; [ easy | ].
apply rngl_ltb_lt.
apply (rngl_lt_le_trans Hor _ 0); [ | easy ].
apply (rngl_opp_neg_pos Hop Hor).
apply (rl_sqrt_half_pos Hc1).
Qed.

Theorem quadrant_3_angle_lt_5_angle_right_div_2 :
  ∀ θ,
  (rngl_sin θ < rngl_cos θ)%L
  → (rngl_sin θ < 0)%L
  → (rngl_cos θ < 0)%L
  → (5 * (angle_right / ₂) < θ)%A.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hsc Hs Hc.
  rewrite (H1 (rngl_sin _)), (H1 (rngl_cos _)) in Hsc.
  now apply (rngl_lt_irrefl Hor) in Hsc.
}
intros * Hsc Hs Hc.
progress unfold angle_ltb.
rewrite rngl_sin_5_right_div_2.
rewrite rngl_leb_opp_r.
rewrite (rngl_opp_0 Hop).
remember (√(1 / 2) ≤? 0)%L as sz eqn:Hsz.
symmetry in Hsz.
destruct sz. {
  exfalso.
  apply rngl_leb_le in Hsz.
  apply (rngl_nlt_ge Hor) in Hsz.
  apply Hsz; clear Hsz.
  apply (rl_sqrt_half_pos Hc1).
}
apply (rngl_leb_gt Hor) in Hs.
rewrite Hs.
apply (rngl_leb_gt Hor) in Hs.
apply rngl_ltb_lt.
rewrite rngl_cos_5_right_div_2.
change_angle_add_r θ angle_straight.
progress sin_cos_add_sub_straight_hyp T Hc.
progress sin_cos_add_sub_straight_hyp T Hs.
progress sin_cos_add_sub_straight_hyp T Hsc.
progress sin_cos_add_sub_straight_goal T.
rewrite (rngl_add_opp_r Hop).
apply (rngl_lt_0_sub Hop Hor).
rewrite <- rngl_cos_right_div_2.
apply angle_add_le_mono_l_lemma_39; try easy. {
  apply rngl_sin_div_2_nonneg.
} {
  now apply (rngl_lt_le_incl Hor) in Hc.
} {
  apply rngl_cos_div_2_nonneg; cbn.
  apply (rngl_0_le_1 Hon Hop Hor).
} {
  cbn.
  specialize (rngl_0_le_1 Hon Hop Hor) as H2.
  apply rngl_leb_le in H2.
  rewrite H2; clear H2.
  rewrite (rngl_mul_1_l Hon).
  rewrite rngl_add_0_r, (rngl_sub_0_r Hos).
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  apply (rngl_mul_pos_pos Hop Hor Hii). {
    now apply (rngl_lt_0_sub Hop Hor).
  }
  apply (rl_sqrt_half_pos Hc1).
}
Qed.

Theorem quadrant_4_angle_lt_7_angle_right_div_2 :
  ∀ θ,
  (rngl_cos θ < - rngl_sin θ)%L
  → (rngl_sin θ < 0)%L
  → (0 ≤ rngl_cos θ)%L
  → (θ < 7 * (angle_right / ₂))%A.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hcs Hs Hc.
  rewrite (H1 (rngl_sin _)) in Hs.
  now apply (rngl_lt_irrefl Hor) in Hs.
}
specialize rl_sqrt_half_nonneg as Hzs.
intros * Hcs Hs Hc.
progress unfold angle_ltb.
generalize Hs; intros H.
apply (rngl_leb_gt Hor) in H.
rewrite H; clear H.
rewrite rngl_sin_7_right_div_2.
rewrite rngl_cos_7_right_div_2.
rewrite rngl_leb_opp_r, (rngl_opp_0 Hop).
remember (√(1 / 2) ≤? 0)%L as sz eqn:Hsz.
symmetry in Hsz.
destruct sz. {
  exfalso.
  apply rngl_leb_le in Hsz.
  apply (rngl_nlt_ge Hor) in Hsz.
  apply Hsz; clear Hsz.
  apply (rl_sqrt_half_pos Hc1).
}
apply rngl_ltb_lt.
change_angle_opp θ.
progress sin_cos_opp_hyp T Hc.
progress sin_cos_opp_hyp T Hs.
progress sin_cos_opp_hyp T Hcs.
rewrite (rngl_opp_involutive Hop) in Hcs.
cbn.
rewrite <- rngl_cos_right_div_2.
apply angle_add_le_mono_l_lemma_39; try easy. {
  now rewrite rngl_sin_right_div_2.
} {
  now rewrite rngl_cos_right_div_2.
} {
  cbn.
  specialize (rngl_0_le_1 Hon Hop Hor) as H2.
  apply rngl_leb_le in H2.
  rewrite H2; clear H2.
  rewrite (rngl_mul_1_l Hon).
  rewrite rngl_add_0_r, (rngl_sub_0_r Hos).
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  apply (rngl_mul_pos_pos Hop Hor Hii). {
    now apply (rngl_lt_0_sub Hop Hor).
  }
  apply (rl_sqrt_half_pos Hc1).
}
Qed.

Theorem quadrant_2_angle_right_div_2_lt :
  ∀ θ,
  (0 ≤ rngl_sin θ)%L
  → (rngl_cos θ < 0)%L
  → (angle_right / ₂ < θ)%A.
Proof.
destruct_ac.
specialize rl_sqrt_half_nonneg as Hzs.
intros * Hs Hc.
progress unfold angle_ltb.
specialize (rngl_sin_div_2_nonneg angle_right) as H1.
apply rngl_leb_le in H1.
rewrite H1; clear H1.
apply rngl_leb_le in Hs.
rewrite Hs.
apply rngl_leb_le in Hs.
apply rngl_ltb_lt; cbn.
specialize (rngl_0_le_1 Hon Hop Hor) as H1.
apply rngl_leb_le in H1.
rewrite H1; clear H1.
rewrite (rngl_mul_1_l Hon).
rewrite rngl_add_0_r.
now apply (rngl_lt_le_trans Hor _ 0).
Qed.

Theorem quadrant_2_angle_lt_3_angle_right_div_2 :
  ∀ θ,
  (- rngl_cos θ < rngl_sin θ)%L
  → (0 ≤ rngl_sin θ)%L
  → (rngl_cos θ < 0)%L
  → (θ < 3 * (angle_right / ₂))%A.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hcs Hs Hc.
  rewrite (H1 (- _)%L), (H1 (rngl_sin _)) in Hcs.
  now apply (rngl_lt_irrefl Hor) in Hcs.
}
intros * Hcs Hs Hc.
specialize rl_sqrt_half_nonneg as Hzs.
progress unfold angle_ltb.
apply rngl_leb_le in Hs.
rewrite Hs.
apply rngl_leb_le in Hs.
rewrite rngl_sin_3_right_div_2.
rewrite rngl_cos_3_right_div_2.
generalize Hzs; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_ltb_lt.
change_angle_sub_l θ angle_straight.
progress sin_cos_add_sub_straight_hyp T Hc.
progress sin_cos_add_sub_straight_hyp T Hs.
progress sin_cos_add_sub_straight_hyp T Hcs.
progress sin_cos_add_sub_straight_goal T.
rewrite (rngl_add_opp_r Hop).
apply (rngl_lt_0_sub Hop Hor).
specialize (rngl_cos_div_2 angle_right) as H1.
cbn - [ rngl_cos ] in H1.
specialize (rngl_0_le_1 Hon Hop Hor) as H2.
apply rngl_leb_le in H2.
rewrite H2 in H1; clear H2.
rewrite (rngl_mul_1_l Hon) in H1.
cbn - [ angle_div_2 ] in H1.
rewrite rngl_add_0_r in H1.
rewrite <- H1.
apply angle_add_le_mono_l_lemma_39; try easy. {
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  intros H; symmetry in H.
  apply eq_rngl_sin_0 in H.
  destruct H; subst θ. {
    cbn in Hcs.
    apply (rngl_nle_gt Hor) in Hcs.
    apply Hcs; clear Hcs.
    apply (rngl_0_le_1 Hon Hop Hor).
  }
  cbn in Hc.
  apply (rngl_nle_gt Hor) in Hc.
  apply Hc; clear Hc; cbn.
  apply (rngl_opp_1_le_0 Hon Hop Hor).
} {
  now cbn; rewrite (rngl_sub_0_r Hos).
} {
  now apply (rngl_lt_le_incl Hor) in Hc.
} {
  cbn.
  specialize (rngl_0_le_1 Hon Hop Hor) as H2.
  apply rngl_leb_le in H2.
  rewrite H2; clear H2.
  rewrite (rngl_mul_1_l Hon).
  now rewrite rngl_add_0_r.
} {
  cbn.
  specialize (rngl_0_le_1 Hon Hop Hor) as H2.
  apply rngl_leb_le in H2.
  rewrite H2; clear H2.
  rewrite (rngl_mul_1_l Hon).
  rewrite rngl_add_0_r, (rngl_sub_0_r Hos).
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_add_opp_r Hop).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  apply (rngl_mul_pos_pos Hop Hor Hii). {
    now apply (rngl_lt_0_sub Hop Hor).
  }
  apply (rl_sqrt_half_pos Hc1).
}
Qed.

Theorem quadrant_3_angle_lt_7_angle_right_div_2 :
  ∀ θ,
  (rngl_sin θ < 0)%L
  → (rngl_cos θ < 0)%L
  → (θ < 7 * (angle_right / ₂))%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hs Hc.
  rewrite (H1 (rngl_sin _)) in Hs.
  now apply (rngl_lt_irrefl Hor) in Hs.
}
specialize rl_sqrt_half_nonneg as Hzs.
intros * Hs Hc.
change_angle_add_r θ angle_straight.
progress sin_cos_add_sub_straight_hyp T Hc.
progress sin_cos_add_sub_straight_hyp T Hs.
progress unfold angle_ltb.
rewrite (rngl_sin_sub_straight_r Hon Hop).
rewrite rngl_leb_opp_r.
rewrite (rngl_opp_0 Hop).
generalize Hs; intros H.
apply (rngl_leb_gt Hor) in H.
rewrite H; clear H.
rewrite rngl_sin_7_right_div_2.
rewrite rngl_leb_opp_r.
rewrite (rngl_opp_0 Hop).
remember (√(1 / 2) ≤? 0)%L as sz eqn:Hsz.
symmetry in Hsz.
destruct sz. {
  exfalso.
  apply rngl_leb_le in Hsz.
  apply (rngl_nlt_ge Hor) in Hsz.
  apply Hsz; clear Hsz.
  apply (rl_sqrt_half_pos Hc1).
}
apply rngl_ltb_lt.
rewrite (rngl_cos_sub_straight_r Hon Hop).
rewrite rngl_cos_7_right_div_2.
apply (rngl_lt_le_trans Hor _ 0); [ | easy ].
now apply (rngl_opp_neg_pos Hop Hor).
Qed.

Theorem rngl_cos_mul_2_neg_if :
  ∀ θ,
  (rngl_cos (2 * θ) < 0)%L
  → (angle_right / ₂ < θ < 3 * (angle_right / ₂))%A ∨
    (5 * (angle_right / ₂) < θ < 7 * (angle_right / ₂))%A.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * H2.
  rewrite (H1 (rngl_cos _)) in H2.
  now apply (rngl_lt_irrefl Hor) in H2.
}
specialize rl_sqrt_half_nonneg as Hzs.
intros * Hcz.
rewrite rngl_cos_mul_2_l in Hcz.
apply -> (rngl_lt_sub_0 Hop Hor) in Hcz.
apply (rngl_squ_lt_abs_lt Hop Hor Hii) in Hcz.
destruct (rngl_le_dec Hor 0 (rngl_sin θ)) as [Hs| Hs]. {
  rewrite (rngl_abs_nonneg_eq Hop Hor (rngl_sin _)) in Hcz; [ | easy ].
  left.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ)) as [Hc| Hc]. {
    rewrite (rngl_abs_nonneg_eq Hop Hor (rngl_cos _)) in Hcz; [ | easy ].
    split; [ now apply angle_right_div_2_lt | ].
    now apply quadrant_1_angle_lt_3_angle_right_div_2.
  } {
    apply (rngl_nle_gt Hor) in Hc.
    rewrite (rngl_abs_nonpos_eq Hop Hor) in Hcz. 2: {
      now apply (rngl_lt_le_incl Hor) in Hc.
    }
    split. {
      now apply quadrant_2_angle_right_div_2_lt.
    } {
      now apply quadrant_2_angle_lt_3_angle_right_div_2.
    }
  }
} {
  apply (rngl_nle_gt Hor) in Hs.
  rewrite (rngl_abs_nonpos_eq Hop Hor (rngl_sin _)) in Hcz. 2: {
    now apply (rngl_lt_le_incl Hor) in Hs.
  }
  right.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ)) as [Hc| Hc]. {
    rewrite (rngl_abs_nonneg_eq Hop Hor (rngl_cos _)) in Hcz; [ | easy ].
    split. {
      now apply quadrant_4_angle_lt_5_angle_right_div_2.
    } {
      now apply quadrant_4_angle_lt_7_angle_right_div_2.
    }
  }
  apply (rngl_nle_gt Hor) in Hc.
  rewrite (rngl_abs_nonpos_eq Hop Hor) in Hcz. 2: {
    now apply (rngl_lt_le_incl Hor) in Hc.
  }
  apply (rngl_opp_lt_compat Hop Hor) in Hcz.
  split. {
    now apply quadrant_3_angle_lt_5_angle_right_div_2.
  } {
    now apply quadrant_3_angle_lt_7_angle_right_div_2.
  }
}
Qed.

Theorem angle_opp_lt_compat_if :
  ∀ θ1 θ2,
  (θ1 ≠ 0)%A
  → (θ1 < θ2)%A
  → (- θ2 < - θ1)%A.
Proof.
destruct_ac.
intros * H1z H12.
progress unfold angle_ltb in H12.
progress unfold angle_ltb.
cbn.
do 2 rewrite rngl_leb_opp_r, (rngl_opp_0 Hop).
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (rngl_sin θ1 ≤? 0)%L as s1z eqn:Hs1z.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (rngl_sin θ2 ≤? 0)%L as s2z eqn:Hs2z.
symmetry in Hzs1, Hs1z.
symmetry in Hzs2, Hs2z.
destruct s2z. {
  destruct s1z; [ | easy ].
  apply rngl_leb_le in Hs1z.
  apply rngl_leb_le in Hs2z.
  apply rngl_ltb_lt.
  destruct zs2. {
    destruct zs1; [ | easy ].
    apply rngl_leb_le in Hzs1.
    apply rngl_leb_le in Hzs2.
    apply rngl_ltb_lt in H12.
    apply (rngl_le_antisymm Hor) in Hzs1; [ | easy ].
    apply eq_rngl_sin_0 in Hzs1.
    destruct Hzs1; subst θ1; [ easy | clear H1z ].
    apply (rngl_lt_iff Hor).
    split; [ apply rngl_cos_bound | ].
    intros H2; symmetry in H2.
    apply eq_rngl_cos_opp_1 in H2; subst θ2.
    now apply (rngl_lt_irrefl Hor) in H12.
  }
  apply (rngl_leb_gt Hor) in Hzs2.
  destruct zs1; [ | now apply rngl_ltb_lt in H12 ].
  apply rngl_leb_le in Hzs1.
  apply (rngl_le_antisymm Hor) in Hzs1; [ | easy ].
  apply eq_rngl_sin_0 in Hzs1.
  destruct Hzs1; subst θ1; [ easy | clear H1z ].
  apply (rngl_lt_iff Hor).
  split; [ apply rngl_cos_bound | ].
  intros Hc; symmetry in Hc.
  apply eq_rngl_cos_opp_1 in Hc; subst θ2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
apply (rngl_leb_gt Hor) in Hs2z.
destruct zs2. 2: {
  apply (rngl_leb_gt Hor) in Hzs2.
  now apply (rngl_lt_asymm Hor) in Hzs2.
}
clear Hzs2.
destruct zs1; [ | easy ].
destruct s1z; [ | easy ].
exfalso.
apply rngl_leb_le in Hzs1, Hs1z.
apply (rngl_le_antisymm Hor) in Hzs1; [ | easy ].
apply eq_rngl_sin_0 in Hzs1.
destruct Hzs1; subst θ1; [ easy | ].
apply rngl_ltb_lt in H12.
apply (rngl_nle_gt Hor) in H12.
apply H12, rngl_cos_bound.
Qed.

Theorem rngl_sin_mul_2_neg_if :
  ∀ θ,
  (rngl_sin (2 * θ) < 0)%L
  → (angle_right < θ < angle_straight)%A ∨
    (3 * angle_right < θ)%A.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * H2.
  rewrite (H1 (rngl_sin _)) in H2.
  now apply (rngl_lt_irrefl Hor) in H2.
}
specialize rl_sqrt_half_nonneg as Hzs.
intros * Hsz.
rewrite rngl_sin_mul_2_l in Hsz.
apply (rngl_lt_mul_0_if Hop Hor) in Hsz.
destruct Hsz as [(H2sz, Hzc)| (Hz2s, Hcz)]. {
  apply (rngl_lt_mul_0_if Hop Hor) in H2sz.
  destruct H2sz as [(H, _)| (_, Hcz)]. {
    exfalso.
    apply (rngl_nle_gt Hor) in H.
    apply H; clear H.
    apply (rngl_0_le_2 Hon Hop Hor).
  }
  right.
  change_angle_opp θ.
  progress sin_cos_opp_hyp T Hzc.
  progress sin_cos_opp_hyp T Hcz.
  rewrite <- (angle_opp_involutive Hop (_ * _)).
  apply angle_opp_lt_compat_if. {
    intros H; subst θ.
    now apply (rngl_lt_irrefl Hor) in Hcz.
  }
  progress unfold angle_ltb.
  cbn - [ angle_mul_nat ].
  generalize Hcz; intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  rewrite rngl_leb_opp_r.
  rewrite (rngl_opp_0 Hop).
  remember (rngl_sin (_ * _) ≤? 0)%L as s3 eqn:Hs3.
  symmetry in Hs3.
  destruct s3; [ | easy ].
  apply rngl_ltb_lt.
  apply (rngl_le_lt_trans Hor _ 0); [ | easy ].
  cbn.
  do 3 rewrite (rngl_mul_0_l Hos).
  do 2 rewrite (rngl_sub_0_l Hop).
  rewrite (rngl_mul_0_r Hos).
  rewrite (rngl_opp_0 Hop).
  rewrite rngl_add_0_r.
  do 2 rewrite (rngl_mul_0_r Hos).
  rewrite (rngl_opp_0 Hop).
  apply (rngl_le_refl Hor).
}
apply (rngl_mul_pos_cancel_l Hop Hor Hii) in Hz2s. 2: {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
left.
change_angle_sub_r θ angle_right.
progress sin_cos_add_sub_right_hyp T Hcz.
progress sin_cos_add_sub_right_hyp T Hz2s.
split. {
  progress unfold angle_ltb.
  rewrite rngl_sin_add_right_r.
  rewrite rngl_cos_add_right_r.
  cbn.
  specialize (rngl_0_le_1 Hon Hop Hor) as H2.
  apply rngl_leb_le in H2.
  rewrite H2.
  generalize Hz2s; intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  apply rngl_ltb_lt.
  now apply (rngl_opp_neg_pos Hop Hor).
}
apply angle_lt_iff.
split. {
  progress unfold angle_leb.
  rewrite rngl_sin_add_right_r.
  rewrite rngl_cos_add_right_r.
  generalize Hz2s; intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply rngl_leb_le in H.
  rewrite H; clear H; cbn.
  rewrite (rngl_leb_refl Hor).
  rewrite rngl_leb_opp_r.
  rewrite (rngl_opp_involutive Hop).
  apply rngl_leb_le.
  apply rngl_sin_bound.
}
intros H.
apply angle_add_move_r in H.
rewrite angle_straight_sub_right in H.
subst θ.
now apply (rngl_lt_irrefl Hor) in Hz2s.
Qed.

Theorem angle_div_2_pow_mul_neq_0 :
  ∀ n i θ,
  θ ≠ 0%A
  → 0 < n < 2 ^ i
  → (n * (θ / ₂^i) ≠ 0)%A.
Proof.
intros * Htz Hni.
revert θ n Htz Hni.
induction i; intros. {
  cbn in Hni.
  flia Hni.
}
destruct (lt_dec n (2 ^ i)) as [Hn2i| Hn2i]. {
  rewrite angle_div_2_pow_succ_r_2.
  apply IHi; [ | flia Hni Hn2i ].
  intros H.
  now apply eq_angle_div_2_0 in H.
}
apply Nat.nlt_ge in Hn2i.
replace n with ((n - 2 ^ i) + 2 ^ i) by flia Hn2i.
rewrite angle_mul_add_distr_r.
rewrite angle_div_2_pow_succ_r_2 at 2.
rewrite angle_div_2_pow_mul_2_pow.
rewrite angle_div_2_pow_succ_r_1.
rewrite angle_mul_nat_div_2. 2: {
  apply angle_mul_nat_overflow_div_2_pow.
  cbn in Hni.
  flia Hni.
}
assert (Hnii : n - 2 ^ i < 2 ^ i) by (cbn in Hni; flia Hni).
intros H.
remember ((n - 2 ^ i) * (θ / ₂^i))%A as θ' eqn:Hθ'.
assert (Htt : (θ' / ₂ < θ / ₂)%A). {
  apply angle_div_2_lt_compat.
  rewrite Hθ'.
  now apply angle_div_2_pow_mul_lt_angle.
}
apply (angle_add_lt_mono_l (θ' / ₂)) in Htt; cycle 1. {
  apply angle_add_overflow_div_2_div_2.
} {
  apply angle_add_overflow_div_2_div_2.
}
rewrite H in Htt.
apply angle_nle_gt in Htt.
apply Htt; clear Htt.
apply angle_nonneg.
Qed.

Theorem angle_mul_mul_div_2 :
  ∀ m n θ,
  angle_mul_nat_overflow n θ = false
  → (m * ((n * θ) / ₂))%A = (m * n * (θ / ₂))%A.
Proof.
intros * Haov.
rewrite <- angle_mul_nat_assoc.
f_equal.
symmetry.
now apply angle_mul_nat_div_2.
Qed.

Theorem angle_le_sub_diag :
  ∀ θ1 θ2,
  (θ2 ≤ θ1)%A
  → (θ1 - θ2 ≤ θ1)%A.
Proof.
destruct_ac.
intros * H21.
progress unfold angle_leb in H21.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin (θ1 - θ2))%L as zs12 eqn:Hzs12.
symmetry in Hzs1, Hzs2, Hzs12.
destruct zs12. {
  destruct zs1; [ | easy ].
  destruct zs2; [ | easy ].
  apply rngl_leb_le in Hzs1, Hzs2, Hzs12, H21.
  apply rngl_leb_le.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    rewrite <- (angle_sub_add θ1 θ2) at 1.
    assert (Hzc2 : (0 ≤ rngl_cos θ2)%L). {
      now apply (rngl_le_trans Hor _ (rngl_cos θ1)).
    }
    apply quadrant_1_rngl_cos_add_le_cos_l; [ easy | easy | cbn | easy ].
    rewrite (rngl_mul_opp_r Hop), (rngl_sub_opp_r Hop).
    apply (rngl_add_nonneg_nonneg Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  cbn.
  rewrite (rngl_mul_opp_r Hop), (rngl_sub_opp_r Hop).
  apply (rngl_le_sub_le_add_l Hop Hor).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_le_trans Hor _ 0). {
    apply (rngl_lt_le_incl Hor) in Hc1z.
    apply (rngl_mul_nonpos_nonneg Hop Hor); [ easy | ].
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
}
apply (rngl_leb_gt Hor) in Hzs12.
destruct zs2. 2: {
  destruct zs1; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzs1, Hzs2.
  apply rngl_leb_le in H21.
  apply rngl_leb_le.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    exfalso.
    assert (Hzc1 : (0 ≤ rngl_cos θ1)%L). {
      now apply (rngl_le_trans Hor _ (rngl_cos θ2)).
    }
    change_angle_add_r θ1 angle_right.
    rewrite angle_sub_sub_swap in Hzs12.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_hyp T Hzc1.
    progress sin_cos_add_sub_right_hyp T H21.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    change_angle_add_r θ2 angle_right.
    rewrite angle_sub_sub_distr in Hzs12.
    progress sin_cos_add_sub_right_hyp T Hzc2.
    progress sin_cos_add_sub_right_hyp T Hzs2.
    progress sin_cos_add_sub_right_hyp T H21.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    apply (rngl_opp_lt_compat Hop Hor) in Hzs12.
    rewrite (rngl_opp_0 Hop) in Hzs12.
    rewrite <- (rngl_sin_sub_anticomm Hic Hop) in Hzs12.
    apply (rngl_nlt_ge Hor) in H21.
    apply H21; clear H21.
    apply rngl_sin_incr_lt.
    split. {
      progress unfold angle_ltb.
      generalize Hzc1; intros H.
      apply rngl_leb_le in H.
      rewrite H; clear H.
      generalize Hzc2; intros H.
      apply rngl_leb_le in H.
      rewrite H; clear H.
      apply rngl_ltb_lt.
      apply angle_add_le_mono_l_lemma_39; try easy; cycle 1.
      now apply (rngl_lt_le_incl Hor) in Hzs2.
      now apply (rngl_lt_le_incl Hor) in Hzs1.
      apply (rngl_lt_iff Hor).
      split; [ easy | ].
      intros H; symmetry in H.
      apply eq_rngl_sin_0 in H.
      destruct H; subst θ2. {
        rewrite angle_sub_0_l in Hzs12.
        cbn in Hzs12.
        apply (rngl_opp_pos_neg Hop Hor) in Hzs12.
        now apply (rngl_nle_gt Hor) in Hzs12.
      }
      apply (rngl_nle_gt Hor) in Hzs2.
      apply Hzs2; clear Hzs2; cbn.
      apply (rngl_opp_1_le_0 Hon Hop Hor).
    }
    progress unfold angle_leb.
    generalize Hzc2; intros H.
    apply rngl_leb_le in H.
    rewrite H; clear H; cbn.
    specialize (rngl_0_le_1 Hon Hop Hor) as H.
    apply rngl_leb_le in H.
    rewrite H; clear H.
    apply rngl_leb_le.
    now apply (rngl_lt_le_incl Hor) in Hzs2.
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    exfalso.
    change_angle_add_r θ1 angle_right.
    rewrite angle_sub_sub_swap in Hzs12.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_hyp T H21.
    progress sin_cos_add_sub_right_hyp T Hzc1.
    change_angle_add_r θ2 angle_straight.
    rewrite angle_sub_sub_distr in Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hc2z.
    progress sin_cos_add_sub_straight_hyp T H21.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hzs2.
    apply (rngl_nle_gt Hor) in Hzs12.
    apply Hzs12; cbn.
    rewrite (rngl_mul_opp_r Hop), (rngl_sub_opp_r Hop).
    apply (rngl_lt_le_incl Hor) in Hzs1, Hc2z, Hzs2.
    apply (rngl_add_nonneg_nonneg Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  change_angle_add_r θ1 angle_straight.
  rewrite angle_sub_sub_swap in Hzs12 |-*.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T H21.
  progress sin_cos_add_sub_straight_hyp T Hc1z.
  progress sin_cos_add_sub_straight_goal T.
  change_angle_add_r θ2 angle_straight.
  rewrite angle_sub_sub_distr in Hzs12 |-*.
  progress sin_cos_add_sub_straight_hyp T Hc2z.
  progress sin_cos_add_sub_straight_hyp T H21.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_goal T.
  rewrite (rngl_add_opp_l Hop) in H21.
  apply -> (rngl_le_sub_0 Hop Hor) in H21.
  exfalso.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  apply (rngl_lt_le_incl Hor) in Hzs1, Hzs2.
  now apply rngl_sin_sub_nonneg.
}
apply rngl_leb_le in Hzs2.
destruct zs1. {
  exfalso.
  apply rngl_leb_le in Hzs1, H21.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  now apply rngl_sin_sub_nonneg.
}
clear H21.
apply (rngl_leb_gt Hor) in Hzs1.
apply rngl_leb_le.
rewrite <- (angle_sub_add θ1 θ2) at 2.
apply angle_add_overflow_le_lemma_11; [ | easy | ].
now apply (rngl_lt_le_incl Hor) in Hzs12.
now rewrite angle_sub_add.
Qed.

Theorem angle_add_straight_r_le_straight :
  ∀ θ,
  (angle_straight ≤ θ)%A
  → (θ + angle_straight ≤ angle_straight)%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  intros * Hst.
  rewrite (H1 (_ + _)%A).
  apply angle_nonneg.
}
intros * Hst.
progress unfold angle_leb in Hst.
progress unfold angle_leb.
cbn in Hst.
rewrite (rngl_leb_refl Hor) in Hst.
rewrite rngl_sin_add_straight_r.
rewrite rngl_cos_add_straight_r.
cbn.
rewrite (rngl_leb_refl Hor).
rewrite rngl_leb_opp_r.
rewrite (rngl_opp_0 Hop).
destruct (rngl_le_dec Hor 0 (rngl_sin θ)) as [Hzt| Htz]. {
  generalize Hzt; intros H.
  apply rngl_leb_le in H.
  rewrite H in Hst; clear H.
  apply rngl_leb_le in Hst.
  specialize (proj1 (rngl_cos_bound θ)) as H1.
  apply (rngl_le_antisymm Hor) in H1; [ | easy ].
  apply eq_rngl_cos_opp_1 in H1; subst θ; cbn.
  rewrite (rngl_leb_refl Hor).
  apply rngl_leb_le.
  rewrite (rngl_opp_involutive Hop).
  apply (rngl_opp_1_le_1 Hon Hop Hor Hc1).
}
apply (rngl_nle_gt Hor) in Htz.
destruct (rngl_le_dec Hor (rngl_sin θ) 0) as [Hzt| Hzt]. {
  generalize Hzt; intros H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  apply rngl_leb_le.
  apply -> (rngl_opp_le_compat Hop Hor).
  apply rngl_cos_bound.
}
now apply (rngl_lt_le_incl Hor) in Htz.
Qed.

Theorem angle_le_add_r :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → (θ1 ≤ θ1 + θ2)%A.
Proof.
intros * Haov.
now apply angle_ltb_ge in Haov.
Qed.

Theorem angle_add_overflow_2_pow_div_mul_2_pow_mul_when_lt_straight :
  ∀ m n i θ,
  m < n ≤ 2 ^ i
  → (θ < angle_straight)%A
  → angle_add_overflow
      (seq_angle_to_div_nat θ n i)
      (m * seq_angle_to_div_nat θ n i) =
      false.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  intros.
  progress unfold seq_angle_to_div_nat.
  rewrite (H1 (_ * _)%A).
  apply angle_add_overflow_0_l.
}
intros * (Hmi, Hni) Hts.
assert (Hnz : n ≠ 0) by flia Hmi.
progress unfold seq_angle_to_div_nat.
apply angle_add_overflow_le with (θ2 := θ). {
  rewrite <- (angle_div_2_pow_mul_2_pow i θ) at 2.
  rewrite angle_mul_nat_assoc.
  apply angle_mul_nat_le_mono_nonneg_r. {
    apply angle_mul_nat_overflow_pow_div.
  }
  eapply le_trans; [ now apply Nat.div_mul_le | ].
  apply Nat.div_le_upper_bound; [ easy | ].
  apply Nat.mul_le_mono_r.
  now apply Nat.lt_le_incl in Hmi.
}
clear m Hmi.
apply angle_add_not_overflow_comm.
apply angle_add_overflow_lt_straight_le_straight; [ easy | ].
destruct i. {
  cbn in Hni.
  apply Nat.le_1_r in Hni.
  destruct Hni as [| Hni]; [ easy | subst n; cbn ].
  rewrite angle_add_0_r.
  now apply angle_lt_le_incl in Hts.
}
destruct n; [ easy | clear Hnz ].
destruct n. {
  rewrite Nat.div_1_r.
  rewrite angle_div_2_pow_mul_2_pow.
  now apply angle_lt_le_incl in Hts.
}
rewrite angle_div_2_pow_succ_r_1.
rewrite angle_mul_nat_div_2; [ apply angle_div_2_le_straight | ].
apply angle_mul_nat_overflow_div_2_pow.
apply Nat.div_le_upper_bound; [ easy | ].
rewrite Nat.pow_succ_r'.
apply Nat.mul_le_mono_r.
now do 2 apply -> Nat.succ_le_mono.
Qed.

(* to be completed
Theorem angle_add_overflow_2_pow_div_mul_2_pow_mul :
  ∀ m n i θ,
  m < n ≤ 2 ^ i
  → angle_add_overflow
      (seq_angle_to_div_nat θ n i)
      (m * seq_angle_to_div_nat θ n i) =
      false.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  intros.
  progress unfold seq_angle_to_div_nat.
  rewrite (H1 (_ * _)%A).
  apply angle_add_overflow_0_l.
}
intros * (Hmi, Hni).
assert (Hnz : n ≠ 0) by flia Hmi.
(**)
remember (θ <? angle_straight)%A as ts eqn:Hts.
symmetry in Hts.
destruct ts. {
  now apply angle_add_overflow_2_pow_div_mul_2_pow_mul_when_lt_straight.
}
apply angle_ltb_ge in Hts.
(*
destruct i. {
  cbn in Hni.
  apply Nat.le_1_r in Hni.
  destruct Hni as [| Hni]; [ easy | subst n ].
  apply Nat.lt_1_r in Hmi; subst m; cbn.
  apply angle_add_overflow_0_r.
}
destruct (le_dec n (2 ^ i)) as [Hn2i| Hn2i]. {
  specialize angle_add_overflow_2_pow_div_mul_2_pow_mul_when_lt_straight as H1.
  specialize (H1 m n i (θ / ₂)%A).
  assert (H : m < n ≤ 2 ^ i) by easy.
  specialize (H1 H); clear H.
  specialize (angle_div_2_lt_straight Hc1 θ) as H.
  specialize (H1 H); clear H.
  progress unfold seq_angle_to_div_nat in H1.
  progress unfold seq_angle_to_div_nat.
  rewrite <- angle_div_2_pow_succ_r_2 in H1.
Search (angle_add_overflow _ _ = false).
...
*)
destruct i. {
  cbn in Hni.
  apply Nat.le_1_r in Hni.
  destruct Hni as [| Hni]; [ easy | subst n ].
  apply Nat.lt_1_r in Hmi; subst m; cbn.
  apply angle_add_overflow_0_r.
}
destruct i. {
  cbn in Hni.
  destruct n; [ easy | clear Hnz ].
  destruct n. {
    cbn.
    apply Nat.lt_1_r in Hmi; subst m; cbn.
    apply angle_add_overflow_0_r.
  }
  destruct n; [ | flia Hni ].
  destruct m; [ apply angle_add_overflow_0_r | ].
  destruct m; [ | flia Hmi ].
  cbn.
  do 2 rewrite angle_add_0_r.
  apply angle_add_overflow_div_2_div_2.
}
destruct i. {
  cbn in Hni.
  destruct n; [ easy | clear Hnz ].
  destruct n. {
    cbn.
    apply Nat.lt_1_r in Hmi; subst m; cbn.
    apply angle_add_overflow_0_r.
  }
  destruct n. {
    destruct m; [ apply angle_add_overflow_0_r | ].
    destruct m. {
      rewrite angle_mul_1_l.
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat ].
      rewrite angle_div_2_mul_2.
      apply angle_add_overflow_div_2_div_2.
    }
    now do 2 apply Nat.succ_lt_mono in Hmi.
  }
  destruct n. {
    destruct m; [ apply angle_add_overflow_0_r | ].
    destruct m. {
      rewrite angle_mul_1_l.
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat ].
      rewrite angle_mul_1_l.
      apply angle_add_overflow_div_2_div_2.
    }
    destruct m. {
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat ].
      rewrite angle_mul_1_l.
      rewrite angle_div_2_mul_2.
      apply angle_add_overflow_div_2_div_2.
    }
    now do 3 apply Nat.succ_lt_mono in Hmi.
  }
  do 4 apply Nat.succ_le_mono in Hni.
  apply Nat.le_0_r in Hni; subst n.
  progress unfold seq_angle_to_div_nat.
  cbn - [ angle_mul_nat ].
  rewrite angle_mul_1_l.
  destruct m; [ apply angle_add_overflow_0_r | ].
  destruct m. {
    rewrite angle_mul_1_l.
    apply angle_add_overflow_div_2_div_2.
  }
  destruct m. {
    rewrite angle_div_2_mul_2.
    apply angle_add_overflow_div_2_div_2.
  }
  destruct m. {
    rewrite <- angle_div_2_pow_1.
    rewrite <- angle_div_2_pow_1.
    rewrite <- angle_div_pow_2_add_distr.
    now apply angle_add_overflow_mul_div_2_pow.
  }
  now do 4 apply Nat.succ_lt_mono in Hmi.
}
destruct n; [ easy | clear Hnz ].
destruct n. {
  apply Nat.lt_1_r in Hmi; subst m.
  apply angle_add_overflow_0_r.
}
destruct i. {
  destruct m; [ apply angle_add_overflow_0_r | ].
  apply Nat.succ_lt_mono in Hmi.
(**)
  cbn in Hni.
  do 2 apply Nat.succ_le_mono in Hni.
  destruct n. {
    destruct m. {
      rewrite angle_mul_1_l.
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat angle_div_2_pow ].
      rewrite angle_div_2_pow_succ_r_2.
      replace 4 with (2 ^ 2) by easy.
      rewrite angle_div_2_pow_mul_2_pow.
      apply angle_add_overflow_div_2_div_2.
    }
    now apply Nat.succ_lt_mono in Hmi.
  }
  destruct n. {
    destruct m. {
      rewrite angle_mul_1_l.
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat angle_div_2_pow ].
      rewrite angle_div_2_pow_succ_r_1.
      rewrite angle_div_2_mul_2.
      apply angle_add_overflow_div_2_div_2.
    }
    destruct m. {
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat angle_div_2_pow ].
      rewrite angle_div_2_pow_succ_r_1.
      rewrite angle_div_2_mul_2.
      rewrite angle_div_2_pow_succ_r_1.
      rewrite angle_div_2_mul_2.
      apply angle_add_overflow_div_2_div_2.
    }
    now do 2 apply Nat.succ_lt_mono in Hmi.
  }
  destruct n. {
    destruct m. {
      rewrite angle_mul_1_l.
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat angle_div_2_pow ].
      rewrite angle_div_2_pow_succ_r_1.
      rewrite angle_div_2_mul_2.
      apply angle_add_overflow_div_2_div_2.
    }
    destruct m. {
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat angle_div_2_pow ].
      rewrite angle_div_2_pow_succ_r_1.
      rewrite angle_div_2_mul_2.
      rewrite angle_div_2_pow_succ_r_1.
      rewrite angle_div_2_mul_2.
      apply angle_add_overflow_div_2_div_2.
    }
    destruct m. {
      progress unfold seq_angle_to_div_nat.
      cbn - [ angle_mul_nat angle_div_2_pow ].
      rewrite angle_div_2_pow_succ_r_1.
      rewrite angle_div_2_mul_2.
      apply angle_add_overflow_mul_div_2_pow; cbn.
      apply Nat.lt_succ_diag_r.
    }
    now do 3 apply Nat.succ_lt_mono in Hmi.
  }
(**)
  do 5 apply Nat.succ_le_mono in Hni.
  destruct m. {
    rewrite angle_mul_1_l.
    progress unfold seq_angle_to_div_nat.
    cbn - [ angle_mul_nat angle_div_2_pow "/" ].
    rewrite (Nat_div_less_small 1); [ | flia Hni ].
    rewrite angle_mul_1_l.
    apply angle_add_overflow_div_2_div_2.
  }
  destruct m. {
    progress unfold seq_angle_to_div_nat.
    cbn - [ angle_mul_nat angle_div_2_pow "/" ].
    rewrite (Nat_div_less_small 1); [ | flia Hni ].
    rewrite angle_mul_1_l.
    apply angle_add_overflow_mul_div_2_pow; cbn.
    now do 2 apply -> Nat.succ_lt_mono.
  }
  destruct m. {
    progress unfold seq_angle_to_div_nat.
    cbn - [ angle_mul_nat angle_div_2_pow "/" ].
    rewrite (Nat_div_less_small 1); [ | flia Hni ].
    rewrite angle_mul_1_l.
    apply angle_add_overflow_mul_div_2_pow; cbn.
    now do 3 apply -> Nat.succ_lt_mono.
  }
  destruct m. {
    progress unfold seq_angle_to_div_nat.
    cbn - [ angle_mul_nat angle_div_2_pow "/" ].
    rewrite (Nat_div_less_small 1); [ | flia Hni ].
    rewrite angle_mul_1_l.
    apply angle_add_overflow_mul_div_2_pow; cbn.
    now do 4 apply -> Nat.succ_lt_mono.
  }
  destruct m. {
    progress unfold seq_angle_to_div_nat.
    cbn - [ angle_mul_nat angle_div_2_pow "/" ].
    rewrite (Nat_div_less_small 1); [ | flia Hni ].
    rewrite angle_mul_1_l.
    apply angle_add_overflow_mul_div_2_pow; cbn.
    now do 5 apply -> Nat.succ_lt_mono.
  }
  do 8 apply Nat.succ_lt_mono in Hmi.
  destruct n; [ easy | ].
  apply Nat.succ_lt_mono in Hmi.
  destruct n; [ easy | ].
  destruct n. {
    apply Nat.lt_1_r in Hmi; subst m.
    progress unfold seq_angle_to_div_nat.
    cbn - [ angle_mul_nat angle_div_2_pow ].
    rewrite angle_mul_1_l.
    apply angle_add_overflow_mul_div_2_pow; cbn.
    now do 6 apply -> Nat.succ_lt_mono.
  }
  do 3 apply Nat.succ_le_mono in Hni.
  apply Nat.le_0_r in Hni; subst n.
  progress unfold seq_angle_to_div_nat.
  cbn - [ angle_mul_nat angle_div_2_pow ].
  rewrite angle_mul_1_l.
  apply angle_add_overflow_mul_div_2_pow; cbn.
  now do 6 apply -> Nat.succ_lt_mono.
}
...
specialize angle_add_overflow_2_pow_div_mul_2_pow_mul_when_lt_straight as H1.
specialize (H1 m n i (θ / ₂)%A).
assert (H : m < n ≤ 2 ^ i) by easy.
specialize (H1 H); clear H.
assert (H : (θ / ₂ < angle_straight)%A) by apply (angle_div_2_lt_straight Hc1).
specialize (H1 H); clear H.
progress unfold seq_angle_to_div_nat in H1.
progress unfold seq_angle_to_div_nat.
...
destruct m. {
  rewrite angle_mul_0_l.
  apply angle_add_overflow_0_r.
}
destruct m. {
  rewrite angle_mul_1_l.
  destruct i. {
    cbn in Hni.
    now apply Nat.nlt_ge in Hni.
  }
  specialize angle_div_2_pow_mul_le_angle as H1.
  specialize (H1 (2 ^ S i / n) i (θ / ₂)%A).
  assert (H : 2 ^ S i / n ≤ 2 ^ i). {
    destruct n; [ easy | ].
    destruct n; [ flia Hmi Hni | ].
    apply Nat.div_le_upper_bound; [ easy | ].
    rewrite Nat.pow_succ_r; [ | easy ].
    apply Nat.mul_le_mono_r.
    now do 2 apply -> Nat.succ_le_mono.
  }
  specialize (H1 H); clear H.
  rewrite <- angle_div_2_pow_succ_r_2 in H1.
  progress unfold seq_angle_to_div_nat.
  apply angle_add_overflow_diag. 2: {
    intros H.
    rewrite H in H1.
    apply angle_nlt_ge in H1.
    apply H1.
    now apply angle_div_2_lt_straight.
  }
  apply rngl_sin_nonneg_angle_le_straight.
  eapply angle_le_trans; [ apply H1 | ].
  apply angle_div_2_le_straight.
}
destruct m. {
  apply angle_add_not_overflow_equiv.
  progress unfold seq_angle_to_div_nat.
  split. {
    remember (2 ^ i / n * (θ / ₂^i))%A as θ' eqn:Hθ'.
    rewrite angle_mul_2_div_2.
    destruct (angle_lt_dec θ' angle_straight) as [Hts| Hts]. {
      rewrite Hts.
      rewrite <- (angle_div_2_mul_2 θ') at 2.
      rewrite angle_add_mul_r_diag_r.
      rewrite Hθ'.
      rewrite angle_mul_mul_div_2. 2: {
        apply angle_mul_nat_overflow_div_2_pow.
        apply Nat.div_le_upper_bound; [ easy | ].
        destruct n; [ easy | cbn ].
        apply Nat.le_add_r.
      }
      rewrite <- angle_div_2_pow_succ_r_1.
      destruct (Nat.eq_dec n 3) as [Hn3| Hn3]. {
        subst n; clear Hnz Hmi.
        specialize (Nat.div_mod (2 ^ i) 3 (Nat.neq_succ_0 _)) as H1.
        symmetry in H1.
        apply Nat.add_sub_eq_r in H1.
        rewrite <- H1.
        rewrite angle_mul_sub_distr_r; [ | now apply Nat.mod_le ].
        rewrite angle_div_2_pow_succ_r_2 at 1.
        rewrite angle_div_2_pow_mul_2_pow.
        apply (angle_le_trans _ (θ / ₂)); [ | apply angle_div_2_le_straight ].
        apply angle_le_sub_diag.
        rewrite angle_div_2_pow_succ_r_1.
        rewrite angle_mul_nat_div_2. 2: {
          apply angle_mul_nat_overflow_div_2_pow.
          now apply Nat.mod_le.
        }
        apply angle_div_2_le_compat.
        apply angle_div_2_pow_mul_le_angle.
        now apply Nat.mod_le.
      }
      assert (H : 3 < n) by flia Hmi Hn3.
      (* perhaps, the case n=3 above could be included here *)
      move H before Hmi; clear Hmi Hn3; rename H into H3n.
      apply angle_mul_div_2_pow_le_straight.
      rewrite Nat.pow_succ_r'.
      apply Nat.mul_le_mono_l.
      eapply Nat.le_trans; [ now apply Nat.div_mul_le | ].
      apply Nat.div_le_upper_bound; [ easy | ].
      apply Nat.mul_le_mono_r.
      now apply Nat.lt_le_incl in H3n.
    }
    generalize Hts; intros H.
    apply Bool.not_true_iff_false in H.
    rewrite H; clear H.
    apply angle_nlt_ge in Hts.
    rewrite angle_add_assoc.
    apply angle_add_straight_r_le_straight.
    exfalso.
    apply angle_nlt_ge in Hts.
    apply Hts; clear Hts.
    subst θ'.
    destruct i; [ cbn in Hni; flia Hmi Hni | ].
    apply (angle_le_lt_trans _ (2 ^ i * (θ / ₂^S i)))%A. 2: {
      rewrite angle_div_2_pow_succ_r_2.
      rewrite angle_div_2_pow_mul_2_pow.
      apply (angle_div_2_lt_straight Hc1).
    }
    apply angle_mul_nat_le_mono_nonneg_r. {
      apply angle_mul_nat_overflow_div_2_pow.
      apply Nat.pow_le_mono_r; [ easy | ].
      apply Nat.le_succ_diag_r.
    }
    apply Nat.div_le_upper_bound; [ easy | ].
    rewrite Nat.pow_succ_r'.
    apply Nat.mul_le_mono_r.
    now apply Nat.lt_le_incl in Hmi.
  } {
    destruct (angle_eq_dec θ 0) as [Htz| Htz]. {
      subst θ; left.
      rewrite angle_0_div_2_pow.
      apply angle_mul_0_r.
    }
    right.
    rewrite angle_add_mul_r_diag_r.
    intros Htt.
    rewrite angle_mul_nat_assoc in Htt.
    revert Htt.
    apply angle_div_2_pow_mul_neq_0; [ easy | ].
    split. {
      apply Nat.mul_pos_pos; [ easy | ].
      apply Nat.div_str_pos.
      split; [ | easy ].
      now apply Nat.neq_0_lt_0.
    }
    apply (le_lt_trans _ (3 * (2 ^ i / 3))). 2: {
      specialize (Nat.div_mod (2 ^ i) 3 (Nat.neq_succ_0 _)) as H1.
      symmetry in H1.
      apply Nat.add_sub_eq_r in H1.
      rewrite <- H1.
      apply Nat.sub_lt; [ now apply Nat.mod_le | ].
      apply Nat.neq_0_lt_0.
      clear Hni H1.
      induction i; [ easy | ].
      intros H; apply IHi; clear IHi.
      rewrite Nat.pow_succ_r' in H.
      apply Nat.mod_divide in H; [ | easy ].
      apply Nat.gauss in H; [ | easy ].
      now apply Nat.mod_divide.
    }
    apply Nat.mul_le_mono_l.
    apply Nat.div_le_compat_l.
    easy.
  }
}
destruct m. {
  apply angle_add_not_overflow_equiv.
  split. {
...
rewrite angle_div_2_pow_succ_r_1.
rewrite angle_mul_nat_div_2. {
  apply rngl_sin_div_2_nonneg.
}
apply angle_mul_nat_overflow_div_2_pow.
apply Nat.div_le_upper_bound; [ easy | ].
rewrite Nat.pow_succ_r'.
apply Nat.mul_le_mono_r.
now apply Nat.lt_le_incl in Hmi.
...
rewrite <- angle_mul_mul_div_2.
...
rewrite
  destruct n; [ easy | clear Hnz ].
  destruct n; [ flia Hmi | ].
  destruct n; [ flia Hmi | clear Hmi ].
  destruct n. {
    destruct i; [ apply (rngl_le_refl Hor) | ].
    destruct i; [ apply (rngl_le_refl Hor) | ].
    destruct i. {
      cbn - [ angle_mul_nat ].
      rewrite angle_mul_1_l.
      apply rngl_sin_div_2_nonneg.
    }
...
  apply rngl_leb_le.
  apply rngl_leb_le in Hzsa.
  apply (rngl_lt_eq_cases Hor); right.
...
  apply (angle_le_trans _ θ'); [ easy | ].
(**)
  progress unfold angle_leb.
  progress unfold angle_leb in Hts.
  cbn in Hts.
  rewrite (rngl_leb_refl Hor) in Hts.
...
  rewrite angle_add_comm.
  apply angle_le_add_r.
  progress unfold angle_add_overflow.
  apply angle_ltb_ge.
Search (angle_add_overflow _ (_ / ₂)).
Search (2 * (_ / ₂))%A.
  rewrite <- (angle_div_2_mul_2 θ') at 1.
  apply angle_add_overflow_div_2_div_2.
...
      rewrite <- H1.
      apply Nat.sub_lt; [ now apply Nat.mod_le | ].
      apply Nat.neq_0_lt_0.
      clear Hni H1.
      induction i; [ easy | ].
      intros H; apply IHi; clear IHi.
      rewrite Nat.pow_succ_r' in H.
      apply Nat.mod_divide in H; [ | easy ].
      apply Nat.gauss in H; [ | easy ].
      now apply Nat.mod_divide.
...
destruct (Nat.eq_dec (Nat.gcd n 2) 0) as [Hn2| Hn2]. 2: {
  apply neq_2_pow_3_mul_lemma.
  specialize (Nat.mod_upper_bound n 2 (Nat.neq_succ_0 _)) as H1.
  remember (n mod 2) as a.
  destruct a; [ easy | ].
  destruct a; [ easy | ].
  now do 2 apply Nat.succ_lt_mono in H1.
}
replace 3 with (2 + 1) by easy.
rewrite Nat.mul_add_distr_r.
rewrite Nat.mul_1_l.
intros Hmn.
symmetry in Hmn.
apply Nat.add_sub_eq_l in Hmn.
revert n Hn2 Hmn.
induction m; intros. {
  cbn - [ "*" ] in Hmn.
  now destruct n.
}
rewrite Nat.pow_succ_r' in Hmn.
rewrite <- Nat.mul_sub_distr_l in Hmn.
specialize (IHm n).
...
intros * Hmn.
(**)
revert m Hmn.
induction n; intros. {
  cbn in Hmn.
  now apply Nat.pow_nonzero in Hmn.
}
destruct m. {
  rewrite Nat.pow_0_r in Hmn.
  symmetry in Hmn.
  now apply Nat.eq_mul_1 in Hmn.
}
replace 3 with (2 + 1) in Hmn by easy.
rewrite Nat.mul_add_distr_r in Hmn.
rewrite Nat.mul_1_l in Hmn.
symmetry in Hmn.
apply Nat.add_sub_eq_l in Hmn.
rewrite Nat.pow_succ_r' in Hmn.
rewrite <- Nat.mul_sub_distr_l in Hmn.
...
  symmetry in Hc.
  revert c Hc.
  induction i; intros. {
    rewrite Nat.pow_0_r in Hc.
    now apply Nat.eq_mul_1 in Hc.
  }
  rewrite Nat.pow_succ_r' in Hc.
  replace 3 with (2 + 1) in Hc by easy.
  rewrite Nat.mul_add_distr_r in Hc.
  rewrite Nat.mul_1_l in Hc.
  apply Nat.add_sub_eq_l in Hc.
  rewrite <- Nat.mul_sub_distr_l in Hc.
... ...
  apply neq_2_pow_3_mul in Hc.
...
(*
specialize (glop (3 * (2 ^ i / n)) i θ Htz) as H1.
rewrite Htt in H1.
*)
destruct (Nat.eq_dec n 3) as [Hn3| Hn3]. {
  subst n.
  clear Hnz Hmi.
...
  assert (H : 3 * (2 ^ i / 3) < 2 ^ i). {
    clear Hni H1 Htt.
    specialize (Nat.div_mod (2 ^ i) 3 (Nat.neq_succ_0 _)) as H1.
    symmetry in H1.
    apply Nat.add_sub_eq_r in H1.
    rewrite <- H1.
    apply Nat.sub_lt; [ now apply Nat.mod_le | ].
    apply Nat.neq_0_lt_0.
    intros H.
    apply Nat.mod_divides in H; [ | easy ].
    destruct H as (c, Hc).
...
  }
  specialize (H1 H); clear H.
...
Search (_ / _ < _).
    eapply Nat.le_lt_trans. {
      apply (Nat.div_mul_le _ _ _ Hnz).
    }
apply Nat.div_lt_upper_bound; [ easy | ].
...
    cbn - [ "/" ].
    do 2 rewrite Nat.add_0_r.
....
(* ouais, ça va pas forcément le faire, ça dépend de n mais
   "glop" peut se révéler utile *)
...
  eapply Nat.lt_le_trans. {
    apply (Nat.div_mul_le _ _ _ Hnz).
  }
  apply (Nat.div_lt_upper_bound _ _ _ Hnz).

apply Nat.mul_lt_mono_nonneg.
...
    specialize (Nat.div_mod (2 ^ i) n Hnz) as H1.
    symmetry in H1.
    apply Nat.add_sub_eq_r in H1.
...
    destruct n; [ easy | clear Hnz ].
    apply Nat.succ_lt_mono in Hmi.
    destruct n; [ easy | ].
    apply Nat.succ_lt_mono in Hmi.
    destruct n; [ easy | clear Hmi ].
    destruct n. {
      specialize (Nat.div_mod (2 ^ i) 3) as H1.
      specialize (H1 (Nat.neq_succ_0 _)).
      symmetry in H1.
      apply Nat.add_sub_eq_r in H1.
      rewrite <- H1 in Htt; clear H1.
      rewrite angle_mul_sub_distr_r in Htt; [ | now apply Nat.mod_le ].
      rewrite angle_div_2_pow_mul_2_pow in Htt.
      apply -> angle_sub_move_0_r in Htt.
..
      destruct i; [ cbn in Hni; flia Hni | ].
      destruct i; [ cbn in Hni; flia Hni | ].
      cbn - [ "/" "*" ] in Htt.
...
      apply eq_angle_mul_0 in Htt.
      destruct Htt as [Htt| Htt]. {
        apply Nat.eq_add_0 in Htt.
        destruct Htt as (H1, H2).
        apply Nat.div_small_iff in H1; [ | easy ].
        now apply Nat.nle_gt in H1.
      }
      destruct Htt as (H1, H2).
Search (rngl_cos (_ * _)).
Print rngl_cos_mul.
... ...
  }
  destruct (angle_lt_dec θ' angle_straight) as [Hts| Hts]. {
    rewrite Hts.
...
    apply eq_angle_mul_0 in Htt.
    destruct Htt as [| Htt]; [ easy | ].
    destruct Htt as (Hc, _).
    subst θ'.
    rewrite angle_mul_nat_assoc in Hc.
    rewrite rngl_cos_nx in Hc.
    cbn - [ "/" "-" binomial ] in Hc.
...
(**)
  destruct i. {
    cbn in Hni.
    flia Hmi Hni.
  }
  progress unfold seq_angle_to_div_nat.
  remember (2 ^ S i / n * (θ / ₂^S i))%A as θi eqn:Hi.
  remember (θi =? angle_straight)%A as is eqn:His.
  symmetry in His.
  destruct is. {
    apply (angle_eqb_eq Hed) in His.
    rewrite His.
    rewrite <- angle_add_diag.
    rewrite angle_straight_add_straight.
    apply angle_add_overflow_0_r.
  }
  apply (angle_eqb_neq Hed) in His.
  specialize angle_div_2_pow_mul_le_angle as H1.
  specialize (H1 (3 * (2 ^ S i / n)) (S i) θ).
  assert (H : 3 * (2 ^ S i / n) ≤ 2 ^ S i). {
    clear - Hmi.
    destruct n; [ flia Hmi | ].
    apply Nat.succ_lt_mono in Hmi.
    destruct n; [ flia Hmi | ].
    apply Nat.succ_lt_mono in Hmi.
    destruct n; [ now apply Nat.lt_irrefl in Hmi | clear Hmi ].
    remember (2 ^ S i) as j eqn:Hj.
    clear i Hj.
    eapply le_trans; [ | now apply (Nat.mul_div_le _ 3) ].
    apply Nat.mul_le_mono_l.
    apply Nat.div_le_compat_l.
    split; [ easy | ].
    now do 3 apply -> Nat.succ_le_mono.
  }
  specialize (H1 H); clear H.
  rewrite <- angle_mul_nat_assoc in H1.
  rewrite <- Hi in H1.
  progress unfold angle_add_overflow.
  apply angle_ltb_ge.
  rewrite angle_add_mul_r_diag_r.
  progress unfold angle_leb in H1.
  progress unfold angle_leb.
  remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
  remember (0 ≤? rngl_sin θi)%L as zsi eqn:Hzsi.
  remember (0 ≤? rngl_sin (3 * θi))%L as zsi3 eqn:Hzsi3.
  symmetry in Hzs, Hzsi, Hzsi3.
  move zsi before zs; move zsi3 before zsi.
  destruct zsi. {
    destruct zsi3; [ | easy ].
    apply rngl_leb_le in Hzsi3, Hzsi.
    apply rngl_leb_le.
    destruct zs. {
      apply rngl_leb_le in Hzs, H1.
      move Hzsi before Hzs.
      apply rngl_sin_sub_nonneg_if; [ now right | easy | easy | ].
      rewrite angle_sub_mul_l_diag_r; [ | easy ].
      cbn - [ rngl_sin angle_mul_nat ].
      apply (rngl_nlt_ge Hor).
      intros H2.
      apply (rngl_nlt_ge Hor) in H1.
      apply H1; clear H1.
      rename H2 into H1.
      assert (Hci : (rngl_cos θi ≤ 0)%L). {
        apply (rngl_nlt_ge Hor).
        intros H.
        apply (rngl_nle_gt Hor) in H1.
        apply H1; clear H1.
        rewrite rngl_sin_mul_2_l.
        apply (rngl_lt_le_incl Hor) in H.
        apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
        apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
        apply (rngl_0_le_2 Hon Hop Hor).
      }
      generalize H1; intros H.
      apply rngl_sin_mul_2_neg_if in H.
      destruct H as [(H2, H3)| H2]. {
...
      apply (rngl_nle_gt Hor).
      intros Hcc.
      assert (Hc2i : (0 ≤ rngl_cos (2 * θi))%L). {
        apply (rngl_nlt_ge Hor).
        intros H4.
        apply rngl_cos_mul_2_neg_if in H4.
        destruct H4 as [(H4, H5)| (H4, H5)]. {
...
apply (rngl_lt_0_sub Hop Hor).
specialize (rngl_cos_div_2 angle_right) as H1.
cbn - [ rngl_cos ] in H1.
specialize (rngl_0_le_1 Hon Hop Hor) as H2.
apply rngl_leb_le in H2.
...
...
(* pas sûr : par exemple si π/2 < θi < 3π/4
   oui, mais dans ce cas, sin(3*θi), peut-il être positif ? *)
rewrite rngl_sin_nx in Hzsi3.
progress unfold iter_seq in Hzsi3.
progress unfold iter_list in Hzsi3.
rewrite Nat.sub_0_r in Hzsi3.
cbn - [ "/" binomial "-" ] in Hzsi3.
do 2 rewrite rngl_add_0_l in Hzsi3.
rewrite rngl_add_0_r in Hzsi3.
rewrite Nat.div_small in Hzsi3; [ | easy ].
rewrite (Nat_div_less_small 1) in Hzsi3; [ | cbn; flia ].
rewrite (rngl_mul_1_r Hon) in Hzsi3.
cbn - [ "^" ] in Hzsi3.
rewrite (rngl_mul_1_l Hon) in Hzsi3.
do 2 rewrite (rngl_mul_1_r Hon) in Hzsi3.
rewrite rngl_add_0_r in Hzsi3.
rewrite (rngl_mul_1_r Hon) in Hzsi3.
rewrite (rngl_mul_opp_l Hop) in Hzsi3.
rewrite (rngl_mul_1_l Hon) in Hzsi3.
rewrite (rngl_add_opp_r Hop) in Hzsi3.
(* pfff, chais pas *)
...
        replace 3 with (2 + 1) in Hzsi3 by easy.
        rewrite angle_mul_add_distr_r in Hzsi3.
        rewrite angle_mul_1_l in Hzsi3.
        cbn - [ "*"%A ] in Hzsi3.
Search (rngl_sin (_ * _)).
        rewrite rngl_sin_mul_2_l in Hzsi3.
        rewrite rngl_cos_mul_2_l in Hzsi3.
...
        rewrite rngl_cos_mul_2_l'.
...
        rewrite rngl_cos_mul_2_l.
        apply (rngl_le_0_sub Hop Hor).
...
      replace 3 with (2 + 1) by easy.
      rewrite angle_mul_add_distr_r.
      rewrite angle_mul_1_l.
      cbn - [ "*"%A ].
...
      replace 3 with (2 + 1) in Hzsi3 by easy.
      rewrite angle_mul_add_distr_r in Hzsi3.
      rewrite angle_mul_1_l in Hzsi3.
...
  Hzs : (0 ≤ rngl_sin θ)%L
  Hzsi : (0 ≤ rngl_sin θi)%L
  Hzsi3 : (0 ≤ rngl_sin (2 * θi + θi))%L
  H1 : (rngl_cos θ ≤ rngl_cos (3 * θi))%L
  ============================
  (0 ≤ rngl_sin (2 * θi))%L
...
      apply rngl_sin_add_nonneg_sin_nonneg in Hzsi3; [ easy | ].
...
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
...
(*
θi ≤ 2 * (π / 3)
sauf que je sais pas diviser un angle par 3...
θi ≤ π

1/3 = 0,010101...
1/3 = 1/4+1/16+1/64
1/3 = 5/16 + 1/64
3*5/16 = 15/16
θi ≤ 2π*15/16
1/3 ≤ 1/4+1/8 = 3/8
montrer θi ≤ 3 (π / 4)
du coup on aurait π/4 ≤ θi
...
*)
  assert (H2 : (θi ≤ 3 * (angle_straight / ₂^2))%A) by ...
  eapply angle_le_trans.
apply H2.
apply angle_mul_le_mono_l.
(* pas gagné *)
...
  apply angle_mul_nat_overflow_distr_add_overflow.
  rewrite Nat_add_mul_r_diag_r.
  replace (1 + 2) with 3 by easy.
...
  apply angle_all_add_not_overflow.
  intros m Hm.
  destruct m. {
...
eapply angle_mul_nat_overflow_le_r.
...
  apply angle_add_overflow_diag. 2: {
    intros H.
    rewrite H in H1.
    apply angle_nlt_ge in H1.
    apply H1.
    now apply angle_div_2_lt_straight.
  }
  apply rngl_sin_nonneg_angle_le_straight.
  eapply angle_le_trans; [ apply H1 | ].
  apply angle_div_2_le_straight.
...
progress unfold angle_add_overflow.
apply angle_ltb_ge.
rewrite <- angle_mul_succ_l.
progress unfold seq_angle_to_div_nat.
progress unfold angle_leb.
(*
do 2 rewrite rngl_cos_nx.
do 3 rewrite rngl_sin_nx.
remember (rngl_cos (θ / ₂^i)) as c eqn:Hc.
remember (rngl_sin (θ / ₂^i)) as s eqn:Hs.
...
*)
remember (seq_angle_to_div_nat θ n) as u eqn:Hu.
remember (0 ≤? rngl_sin (u i))%L as zs eqn:Hzs.
symmetry in Hzs.
rewrite Hu in Hzs.
progress unfold seq_angle_to_div_nat in Hzs.
rewrite Hzs.
destruct zs. {
  apply rngl_leb_le in Hzs.
  remember (0 ≤? rngl_sin (S m * u i))%L as zsm eqn:Hzsm.
  symmetry in Hzsm.
  rewrite Hu in Hzsm.
  progress unfold seq_angle_to_div_nat in Hzsm.
  rewrite Hzsm.
  destruct zsm; [ | easy ].
  apply rngl_leb_le in Hzsm.
  apply rngl_leb_le.
  rewrite angle_mul_nat_assoc.
  do 2 rewrite rngl_cos_nx.
  remember (∑ (j = _, _), _) as x; subst x.
  remember (∑ (j = _, _ / _), _) as x; subst x.
  remember (rngl_cos (θ / ₂^i)) as c eqn:Hc.
  remember (rngl_sin (θ / ₂^i)) as s eqn:Hs.
  move s before c.
  destruct m. {
    rewrite Nat.mul_1_l.
    apply (rngl_le_refl Hor).
  }
  destruct m. {
Search (binomial (_ + _)).
Search (binomial (_ * _)).
Search binomial.
  rewrite rngl_sin_nx in Hzsm.
  remember (∑ (j = _, _), _) as x in Hzsm; subst x.
  progress unfold iter_seq in Hzsm.
  progress unfold iter_list in Hzsm.
  rewrite Nat.sub_0_r in Hzsm.
  cbn in Hzsm.
  do 2 rewrite rngl_add_0_l in Hzsm.
  do 2 rewrite rngl_add_0_r in Hzsm.
  rewrite (rngl_mul_1_l Hon) in Hzsm.
  do 2 rewrite (rngl_mul_1_r Hon) in Hzsm.
  rewrite rngl_sin_nx in Hzsm.
  rewrite rngl_cos_nx in Hzsm.
  remember (∑ (j = _, _), _) as x in Hzsm; subst x.
  rewrite <- Hc, <- Hs in Hzsm.
...
  remember (∑ (j = _, _), _) as x in Hzs; subst x.
  remember (rngl_cos (θ / ₂^i)) as c eqn:Hc.
  remember (rngl_sin (θ / ₂^i)) as s eqn:Hs.
  move s before c.
...
  erewrite rngl_summation_eq_compat. 2: {
    intros j (_, Hj).
    erewrite rngl_if_then_else_eq_compat; cycle 1. {
      intros H1.
      remember (∑ (k = _, _), _) as x in |-*.
      remember (∑ (k = _, _), _) as y in |-*.
...
Search ((if _ then _ else _) = (if _ then _ else _)).
... ...
  rewrite angle_add_diag in Hzsm |-*.
  rewrite rngl_sin_mul_2_l in Hzsm.
  rewrite rngl_cos_mul_2_l'.
  apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzsm.
  remember (rngl_cos (u i)) as x eqn:Hx.
  rewrite Hu in Hx.
  progress unfold seq_angle_to_div_nat in Hx.
  rewrite <- Hx.
...
  destruct Hzsm as [(_, Hzsm)| (H1, H2)]. 2: {
    destruct (rngl_eq_dec Hed (rngl_sin (u i)) 0) as [Hxz| Hxz]. {
      rewrite Hu in Hxz.
      progress unfold seq_angle_to_div_nat in Hxz.
      apply eq_rngl_sin_0 in Hxz.
      destruct Hxz as [Hxz| Hxz]. {
        rewrite Hxz in Hx; cbn in Hx; subst x.
        exfalso; apply (rngl_nlt_ge Hor) in H2.
        apply H2; clear H2.
        rewrite Hxz.
        apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
      } {
        rewrite Hxz in Hx; cbn in Hx; subst x.
        exfalso; clear H1 H2 Hzs.
        revert Hxz.
        apply fold_not.
        destruct n; [ easy | clear Hnz ].
        apply Nat.succ_lt_mono in Hmi.
        destruct n; [ flia Hmi | clear Hmi ].
        destruct n. {
          destruct i; [ cbn in Hni; flia Hni | ].
          rewrite Nat.pow_succ_r'.
          rewrite Nat.mul_comm.
          rewrite Nat.div_mul; [ | easy ].
          rewrite angle_div_2_pow_succ_r_2.
          rewrite angle_div_2_pow_mul_2_pow.
          now apply (angle_div_2_not_straight Hc1).
        }
        destruct i; [ cbn in Hni; flia Hni | ].
        rewrite angle_div_2_pow_succ_r_2.
        specialize angle_div_2_pow_mul_le_angle as H1.
        specialize (H1 (2 ^ S i / S (S (S n))) i (θ / ₂)%A).
        assert (H : 2 ^ S i / S (S (S n)) ≤ 2 ^ i). {
          rewrite Nat.pow_succ_r'.
          apply Nat.div_le_upper_bound; [ easy | ].
          apply Nat.mul_le_mono_r.
          now do 2 apply -> Nat.succ_le_mono.
        }
        specialize (H1 H); clear H.
        intros Hxz.
        rewrite Hxz in H1.
        apply angle_nlt_ge in H1.
        apply H1.
        apply (angle_div_2_lt_straight Hc1).
      }
    }
    exfalso.
    rewrite Hu in Hxz.
    progress unfold seq_angle_to_div_nat in Hxz.
    apply (rngl_le_antisymm Hor) in Hzs; [ easy | ].
    apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ 2%L). {
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    }
    now rewrite rngl_mul_0_r.
  }
  (* variation of the curve y=2x²-x-1 in interval [-1,1] *)
  apply rngl_2_x2_sub_1_le_x.
  rewrite <- Hx in Hzsm.
  split; [ easy | ].
  subst x; apply rngl_cos_bound.
}
apply (rngl_leb_gt Hor) in Hzs.
apply (rngl_nle_gt Hor) in Hzs.
exfalso.
apply Hzs; clear Hzs.
destruct i; [ cbn in Hni; flia Hni Hmi | ].
apply rngl_sin_nonneg_angle_le_straight.
apply angle_mul_div_2_pow_le_straight.
eapply Nat.le_trans; [ now apply Nat.div_mul_le | ].
apply Nat.div_le_upper_bound; [ easy | ].
now apply Nat.mul_le_mono_r.
Qed.
*)

(* to be completed
Theorem angle_div_nat_is_inf_sum_of_angle_div_2_pow' :
  rngl_is_archimedean T = true →
  rngl_characteristic T = 0 →
  ∀ n θ θ',
  n ≠ 0
  → angle_lim (seq_angle_to_div_nat θ n) θ'
  → θ = (n * θ')%A.
Proof.
destruct_ac.
intros Har Hch.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  now rewrite Hc1 in Hch.
}
intros * Hiz Hlim.
specialize angle_div_nat_is_inf_sum_of_angle_div_2_pow as Hlim'.
specialize (Hlim' Har Hch n θ' Hiz).
remember (angle_mul_nat_overflow n θ') as ao eqn:Hao.
symmetry in Hao.
move Hlim before Hlim'.
destruct ao. 2: {
  specialize (Hlim' eq_refl).
  progress unfold seq_angle_to_div_nat in Hlim.
  progress unfold seq_angle_to_div_nat in Hlim'.
  eapply (angle_lim_eq_compat 0 0) in Hlim'. 2: {
    intros i.
    rewrite Nat.add_0_r.
    rewrite angle_div_2_pow_mul; [ | easy ].
    rewrite angle_mul_nat_assoc.
    easy.
  }
  induction n as (n, IHn) using lt_wf_rec; intros.
  destruct n; [ easy | clear Hiz ].
  destruct n. {
    rewrite angle_mul_1_l.
    eapply (angle_lim_eq_compat 0 0) in Hlim. 2: {
      intros i.
      rewrite Nat.add_0_r.
      rewrite Nat.div_1_r.
      now rewrite angle_div_2_pow_mul_2_pow.
    }
    now apply angle_lim_const in Hlim.
  }
  destruct n. {
    eapply (angle_lim_eq_compat 1 0) in Hlim. 2: {
      intros i.
      rewrite Nat.add_0_r.
      rewrite Nat.pow_add_r.
      rewrite Nat.pow_1_r.
      rewrite Nat.div_mul; [ | easy ].
      rewrite Nat.add_comm.
      rewrite angle_div_2_pow_succ_r_2.
      now rewrite angle_div_2_pow_mul_2_pow.
    }
    apply angle_lim_const in Hlim.
    subst θ'; symmetry.
    apply angle_div_2_mul_2.
  }
  destruct n. {
    generalize Hlim'; intros H.
    eapply angle_same_lim_sub in H; [ | apply Hlim ].
    cbn - [ "/" ] in H.
    eapply (angle_lim_eq_compat 0 0) in H. 2: {
      intros i.
      rewrite Nat.add_0_r.
      rewrite <- angle_mul_nat_assoc.
      rewrite <- angle_mul_sub_distr_l.
      rewrite <- angle_div_2_pow_mul; [ | easy ].
      easy.
    }
Print angle_lim.
Print is_limit_when_tending_to_inf.
Definition nat_seq_diverges (u : nat → nat) :=
  ∀ M, ∃ N, ∀ n, N ≤ n → M < u n.

Theorem angle_lim_0_diverges_l :
  rngl_is_archimedean T = true →
  ∀ (u : nat → nat) f,
  angle_lim (λ i, (u i * f i)%A) 0
  → nat_seq_diverges u
  → (∀ i, angle_mul_nat_overflow (u i) (f i) = false)
  → angle_lim f 0.
Proof.
destruct_ac.
intros Har.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hlim Hdiv Hnov.
  intros ε Hε.
  rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hlim Hdiv Hnov.
intros ε Hε.
progress unfold angle_lim in Hlim.
progress unfold is_limit_when_tending_to_inf in Hlim.
progress unfold nat_seq_diverges in Hdiv.
specialize (int_part Hon Hop Hc1 Hor Har) as H1.
specialize (H1 (1 / ε)%L).
destruct H1 as (M, HM).
specialize (Hdiv M).
destruct Hdiv as (N, HN).
rewrite (rngl_abs_nonneg_eq Hop Hor) in HM. 2: {
  apply (rngl_div_nonneg Hon Hop Hiv Hor); [ | easy ].
  apply (rngl_0_le_1 Hon Hop Hor).
}
(*
specialize (Hlim ε Hε).
specialize (Hlim 1%L).
specialize (Hlim (rngl_0_lt_1 Hon Hop Hc1 Hor)).
*)
(**)
destruct (rngl_lt_dec Hor 1 ε) as [Hε1| Hε1]. {
  specialize (Hlim (ε - 1)%L) as H1.
  assert (H : (0 < ε - 1)%L) by now apply (rngl_lt_0_sub Hop Hor).
  specialize (H1 H); clear H.
  destruct H1 as (P, HP).
  exists (max N P).
  intros n Hn.
  specialize (HN _ (Nat.max_lub_l _ _ _ Hn)) as H2.
  specialize (HP _ (Nat.max_lub_r _ _ _ Hn)) as H3.
  eapply (rngl_le_lt_trans Hor). {
    apply (angle_eucl_dist_triangular _ (u n * f n)).
  }
  replace ε with (1 + (ε - 1))%L. 2: {
    rewrite rngl_add_comm.
    apply (rngl_sub_add Hop).
  }
  apply (rngl_add_le_lt_mono Hop Hor); [ | easy ].
  rewrite angle_eucl_dist_move_0_l.
  rewrite angle_sub_mul_l_diag_r. 2: {
    intros H.
    now rewrite H in H2.
  }
...
  rewrite angle_eucl_dist_is_sqrt.
  rewrite angle_sub_0_l; cbn.
...
rewrite angle_eucl_dist_is_sqrt in HP |-*.
rewrite angle_sub_0_l in HP |-*.
cbn in HP |-*.
...
Check (Nat.le_max_r _ _ Hn).
specialize (HP n (Nat.le_max_r _ _ Hn)).
...
destruct M. {
  cbn in HM.
  rewrite rngl_add_0_r in HM.
  destruct HM as (_, HM).
  apply (rngl_lt_div_l Hon Hop Hiv Hor _ _ _ Hε) in HM.
  rewrite (rngl_mul_1_l Hon) in HM.
  specialize (Hlim 1)%L.
  specialize (rngl_0_lt_1 Hon Hop Hc1 Hor) as H.
  specialize (Hlim H); clear H.
  specialize (Hdiv (u 0)).
  destruct Hdiv as (n, Hn).
  progress unfold abs_diff in Hn.
  remember (u 0 <? u n) as b eqn:Hb.
  symmetry in Hb.
  destruct b. 2: {
    apply Nat.ltb_ge in Hb.
    flia Hb Hn.
  }
  apply Nat.ltb_lt in Hb.
  destruct Hlim as (N, HN).
...
  specialize (HN n).
...
specialize (Hlim (ε / rngl_of_nat M))%L.
assert (H : (0 < ε / rngl_of_nat M)%L). {
...
  apply (rngl_div_lt_pos Hon Hop Hiv Hor _ _ Hε).
  destruct M. {
    cbn in HM.
    destruct HM as (_, HM).
    rewrite rngl_add_0_r in HM.
    apply (rngl_lt_div_l Hon Hop Hiv Hor _ _ _ Hε) in HM.
    rewrite (rngl_mul_1_l Hon) in HM.
...
specialize (Hdiv (1 / ε)).
specialize (Hlim ε Hε).
destruct Hlim as (N, HN).
...
specialize (Hdiv N).
destruct Hdiv as (n, Hn).
... ...
apply angle_lim_0_diverges_l in H. 2: {
...
Theorem angle_div_2_pow_sub :
  ∀ n θ1 θ2,
  angle_add_overflow θ1 (- θ2) = false
  → ((θ1 - θ2) / ₂^n)%A = (θ1 / ₂^n - θ2 / ₂^n)%A.
...
rewrite <- angle_div_2_pow_sub. 2: {
(* ah mais ça, c'est faux, en fait, parce que θ devrait être
   égal à 3θ' *)
      progress unfold angle_sub.
...
Theorem angle_div_2_pow_opp :
  ∀ i θ,
  (- (θ / ₂^i) =
     match i with
     | 0 => -θ
     | S i' => angle_straight / ₂^i' - θ / ₂^i
     end)%A.
Proof.
destruct_ac.
intros.
apply eq_angle_eq.
cbn.
...
 mk_angle (rngl_cos (θ / ₂^i)) (- rngl_sin (θ / ₂^i)))%A.
cbn.
revert θ.
induction i; intros; [ easy | ].
rewrite angle_div_2_pow_succ_r_2.
rewrite IHi.
...
destruct i. {
  cbn.
  progress unfold angle_sub.
Check angle_opp_div_2.
  rewrite angle_opp_div_2.
remember (θ =? 0)%A as tz eqn:Htz.
symmetry in Htz.
destruct tz. {
  apply (angle_eqb_eq Hed) in Htz; subst θ.
  rewrite angle_0_div_2.
  now rewrite angle_add_0_r.
}

  apply (angle_eqb_eq Hed) in Htz; subst θ.
  rewrite angle_0_div_2.
  rewrite angle_add_0_r.
  f_equal.
}
do 2 rewrite angle_div_2_pow_succ_r_2.
rewrite IHi.
cbn.
rewrite Nat.sub_0_r.
rewrite angle_opp_div_2.
remember (θ =? 0)%A as tz eqn:Htz.
symmetry in Htz.
destruct tz. {
  apply (angle_eqb_eq Hed) in Htz; subst θ.
  rewrite angle_0_div_2.
  rewrite angle_add_0_r.
  f_equal.
  remember (i =? 0) as iz eqn:Hiz.
  symmetry in Hiz.
  destruct iz. {
    apply Nat.eqb_eq in Hiz.
    subst i.
    cbn.
}
...
Theorem angle_div_2_pow_opp :
  ∀ i θ, (- (θ / ₂^i) = ((- θ) / ₂^i))%A.
Proof.
destruct_ac.
intros.
revert θ.
induction i; intros; [ easy | ].
do 2 rewrite angle_div_2_pow_succ_r_2.
rewrite IHi.
f_equal.
rewrite angle_opp_div_2.
remember (θ =? 0)%A as tz eqn:Htz.
symmetry in Htz.
destruct tz. {
  apply (angle_eqb_eq Hed) in Htz; subst θ.
  rewrite angle_0_div_2.
  now rewrite angle_add_0_r.
}
... ...
  rewrite angle_div_2_pow_opp.
  rewrite <- angle_div_2_pow_add; [ | ... ].
  rewrite angle_add_opp_r.
  easy.
}
Search (angle_lim (λ _, (_ * (_ / ₂^_)))%A).
...
Search ((_ - _) / ₂^_)%A.
Search (_ * (_ / ₂^_))%A.
Search (angle_lim (λ _, (_ * _)%A)).
...
Search (_ * _ * _)%A.
Search (_ * _ * (_ / ₂^_))%A.
...
clear Hlim' IHn.
...
Search (angle_lim _ _ → _).
...
    apply angle_lim_opp in Hlim.
    apply angle_lim_move_0_r in Hlim.
    eapply (angle_lim_eq_compat 2 0) in Hlim. 2: {
      intros i.
      rewrite Nat.add_0_r.
      rewrite (angle_sub_opp_r Hop).
      rewrite (angle_add_opp_l Hic).
      rewrite <- (angle_div_2_pow_mul_2_pow (i + 2) θ') at 1.
...
      rewrite <- angle_mul_sub_distr_r. 2: {
        rewrite Nat.mul_comm.
        now apply Nat.mul_div_le.
      }
      specialize (Nat.div_mod (2 ^ (i + 2)) 3) as H1.
      specialize (H1 (Nat.neq_succ_0 _)).
      rewrite H1 at 1.
      rewrite Nat.mul_comm.
      rewrite Nat.add_sub_swap; [ | apply Nat.le_refl ].
      rewrite Nat.sub_diag.
      rewrite Nat.add_0_l.
      easy.
    }
Search angle_lim.
...
eapply angle_lim_0_le_if in Hlim'.
...
Search (_ / _ * _).
...
Search (2 ^ _ * _)%A.
    apply angle_lim_0_le_if with (f := λ i, (3 * θ' - θ')%A) in Hlim'. 2: {
      intros i.
      split. {
        progress unfold angle_sub.
        do 2 rewrite (angle_add_comm Hic _ (- θ')%A).
        apply angle_add_le_mono_l. {
Search (angle_add_overflow _ _ = false).
...
destruct_ac.
intros Har Hch.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  now rewrite Hc1 in Hch.
}
intros * Hiz Hlim.
revert θ θ' Hlim.
progress unfold seq_angle_to_div_nat in Hlim.
induction n as (n, IHn) using lt_wf_rec; intros.
destruct n; [ easy | clear Hiz ].
destruct n. {
  rewrite angle_mul_1_l.
  eapply (angle_lim_eq_compat 0 0) in Hlim. 2: {
    intros i.
    rewrite Nat.add_0_r.
    rewrite Nat.div_1_r.
    now rewrite angle_div_2_pow_mul_2_pow.
  }
  now apply angle_lim_const in Hlim.
}
destruct n. {
  eapply (angle_lim_eq_compat 1 0) in Hlim. 2: {
    intros i.
    rewrite Nat.add_0_r.
    rewrite Nat.pow_add_r.
    rewrite Nat.pow_1_r.
    rewrite Nat.div_mul; [ | easy ].
    rewrite Nat.add_comm.
    rewrite angle_div_2_pow_succ_r_2.
    now rewrite angle_div_2_pow_mul_2_pow.
  }
  apply angle_lim_const in Hlim.
  subst θ'; symmetry.
  apply angle_div_2_mul_2.
}
destruct n. {
  eapply (angle_lim_eq_compat 1 0) in Hlim. 2: {
    intros i.
    rewrite Nat.add_0_r.
    rewrite Nat.pow_add_r.
    cbn - [ "/" ].
    easy.
  }
...
destruct_ac.
intros Har Hch.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  now rewrite Hc1 in Hch.
}
intros * Hiz Hlim.
specialize angle_div_nat_is_inf_sum_of_angle_div_2_pow as Hlim'.
(* pourquoi il faut que nθ ne déborde pas ? on est fichus ! *)
specialize (Hlim' Har Hch n θ' Hiz).
remember (angle_mul_nat_overflow n θ') as ao eqn:Hao.
symmetry in Hao.
destruct ao. {
  clear Hlim'.
  apply Bool.not_false_iff_true in Hao.
  exfalso; apply Hao; clear Hao.
Theorem seq_angle_not_mul_overflow :
  ∀ n u θ θ',
  u = seq_angle_to_div_nat θ n
  → angle_lim u θ'
  → ∀ i, angle_mul_nat_overflow n (u i) = false.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  intros * Hu Hlim i.
  rewrite (H1 (u i)).
  apply angle_mul_nat_overflow_0_r.
}
intros * Hu Hlim i.
rewrite Hu.
progress unfold seq_angle_to_div_nat.
destruct (lt_dec (2 ^ i) n) as [Hni| Hni]. {
  rewrite Nat.div_small; [ | easy ].
  rewrite angle_mul_0_l.
  apply angle_mul_nat_overflow_0_r.
}
apply Nat.nlt_ge in Hni.
remember (angle_mul_nat_overflow (2 ^ i / n) θ) as b eqn:Hb.
symmetry in Hb.
destruct b. 2: {
  rewrite <- angle_div_2_pow_mul; [ | easy ].
  now apply angle_mul_nat_overflow_div_2_pow.
}
apply angle_all_add_not_overflow.
intros m Hmi.
assert (Hnz : n ≠ 0) by flia Hmi.
remember (θ =? 0)%A as tz eqn:Htz.
symmetry in Htz.
destruct tz. {
  apply (angle_eqb_eq Hed) in Htz.
  subst θ.
  rewrite angle_0_div_2_pow.
  rewrite angle_mul_0_r.
  apply angle_add_not_overflow_comm.
  apply angle_add_overflow_0_r.
}
apply (angle_eqb_neq Hed) in Htz.
(**)
destruct m. {
  rewrite angle_mul_0_l.
  apply angle_add_overflow_0_r.
}
destruct m. {
  rewrite angle_mul_1_l.
  now apply angle_add_overflow_2_pow_div_mul_2_pow_diag.
}
... ...
now apply angle_add_overflow_2_pow_div_mul_2_pow_mul.
destruct m. {
...
Search (angle_add_overflow _ _ = false).
...
(*
  specialize (angle_mul_add_overflow_mul_div_2_pow n (S i) θ) as H1.
  assert (H : n < 2 ^ S i). {
    apply (Nat.le_lt_trans _ (2 ^ i)); [ easy | ].
    cbn; rewrite Nat.add_0_r.
    remember (2 ^ i) as x.
    destruct x; [ | cbn; flia ].
    symmetry in Heqx.
    now apply Nat.pow_nonzero in Heqx.
  }
  specialize (H1 H); clear H.
  cbn in H1.
*)
...
destruct n; [ easy | clear Hnz ].
destruct n. {
  apply Nat.lt_1_r in Hmi; subst m.
  rewrite angle_mul_0_l.
  apply angle_add_overflow_0_r.
}
destruct n. {
  destruct m. {
    rewrite angle_mul_0_l.
    apply angle_add_overflow_0_r.
  }
  destruct m; [ clear Hmi | flia Hmi ].
  rewrite angle_mul_1_l.
  progress unfold angle_add_overflow.
  apply angle_ltb_ge.
  progress unfold angle_leb.
  remember (0 ≤? rngl_sin (u i))%L as zs eqn:Hzs.
  remember (0 ≤? rngl_sin (u i + u i))%L as zsm eqn:Hzsm.
  symmetry in Hzs, Hzsm.
  rewrite Hu in Hzs, Hzsm.
  progress unfold seq_angle_to_div_nat in Hzs.
  progress unfold seq_angle_to_div_nat in Hzsm.
  rewrite Hzs, Hzsm.
  destruct zs. {
    apply rngl_leb_le in Hzs.
    destruct zsm; [ | easy ].
    apply rngl_leb_le in Hzsm.
    apply rngl_leb_le.
    rewrite (angle_add_diag Hon Hos) in Hzsm |-*.
    rewrite rngl_sin_mul_2_l in Hzsm.
    rewrite rngl_cos_mul_2_l'.
    apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzsm.
    remember (rngl_cos (u i)) as x eqn:Hx.
    rewrite Hu in Hx.
    progress unfold seq_angle_to_div_nat in Hx.
    rewrite <- Hx.
    destruct Hzsm as [(_, Hzsm)| (H1, H2)]. 2: {
      destruct (rngl_eq_dec Hed (rngl_sin (u i)) 0) as [Hxz| Hxz]. {
        rewrite Hu.
        progress unfold seq_angle_to_div_nat.
        apply eq_rngl_sin_0.
        destruct Hxz as [Hxz| Hxz]. {
          rewrite Hxz in Hx; cbn in Hx; subst x.
          exfalso; apply (rngl_nlt_ge Hor) in H2.
          apply H2; clear H2.
          rewrite Hxz.
          apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
        } {
          rewrite Hxz in Hx; cbn in Hx; subst x.
          exfalso; clear H1 H2 Hzs.
          destruct i; [ cbn in Hni; flia Hni | ].
          rewrite angle_div_2_pow_succ_r_1.
          rewrite angle_mul_nat_div_2.
          now apply (angle_div_2_not_straight Hc1).
          rewrite Nat.pow_succ_r'.
          rewrite Nat.mul_comm.
          rewrite Nat.div_mul; [ | easy ].
          apply angle_mul_nat_overflow_pow_div.
        }
      }
      exfalso.
      rewrite Hu in Hxz.
      progress unfold seq_angle_to_div_nat in Hxz.
      apply (rngl_le_antisymm Hor) in Hzs; [ easy | ].
      apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ 2%L). {
        apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
      }
      now rewrite rngl_mul_0_r.
    }
    (* variation of the curve y=2x²-x-1 in interval [-1,1] *)
    apply rngl_2_x2_sub_1_le_x.
    rewrite <- Hx in Hzsm.
    split; [ easy | ].
    subst x; apply rngl_cos_bound.
  }
  apply (rngl_leb_gt Hor) in Hzs.
  apply (rngl_nle_gt Hor) in Hzs.
  exfalso.
  apply Hzs; clear Hzs.
  destruct i; [ cbn in Hni; flia Hni | ].
  rewrite Nat.pow_succ_r'.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul; [ | easy ].
  rewrite angle_div_2_pow_succ_r_2.
  rewrite angle_div_2_pow_mul_2_pow.
  apply rngl_sin_div_2_nonneg.
}
destruct n. {
  destruct m. {
    rewrite angle_mul_0_l.
    apply angle_add_overflow_0_r.
  }
  apply Nat.succ_lt_mono in Hmi.
  destruct m. {
    clear Hmi.
    rewrite angle_mul_1_l.
    progress unfold angle_add_overflow.
    apply angle_ltb_ge.
    progress unfold angle_leb.
    remember (0 ≤? rngl_sin (u i))%L as zs eqn:Hzs.
    remember (0 ≤? rngl_sin (u i + u i))%L as zsm eqn:Hzsm.
    symmetry in Hzs, Hzsm.
    rewrite Hu in Hzs, Hzsm.
    progress unfold seq_angle_to_div_nat in Hzs.
    progress unfold seq_angle_to_div_nat in Hzsm.
    rewrite Hzs, Hzsm.
    destruct zs. {
      apply rngl_leb_le in Hzs.
      destruct zsm; [ | easy ].
      apply rngl_leb_le in Hzsm.
      apply rngl_leb_le.
      rewrite (angle_add_diag Hon Hos) in Hzsm |-*.
      rewrite rngl_sin_mul_2_l in Hzsm.
      rewrite rngl_cos_mul_2_l'.
      apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzsm.
      remember (rngl_cos (u i)) as x eqn:Hx.
      rewrite Hu in Hx.
      progress unfold seq_angle_to_div_nat in Hx.
      rewrite <- Hx in Hzsm |-*.
      destruct Hzsm as [(_, Hzsm)| (H1, H2)]. 2: {
        destruct (rngl_eq_dec Hed (rngl_sin (u i)) 0) as [Hxz| Hxz]. {
          rewrite Hu in Hxz.
          progress unfold seq_angle_to_div_nat in Hxz.
          apply eq_rngl_sin_0 in Hxz.
          destruct Hxz as [Hxz| Hxz]. {
            rewrite Hxz in Hx; cbn in Hx; subst x.
            exfalso; apply (rngl_nlt_ge Hor) in H2.
            apply H2.
            apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
          } {
            rewrite Hxz in Hx; cbn in Hx; subst x.
            exfalso; clear H1 H2 Hzs.
            destruct i; [ cbn in Hni; flia Hni | ].
            rewrite angle_div_2_pow_succ_r_1 in Hxz.
            rewrite angle_mul_nat_div_2 in Hxz.
            now apply (angle_div_2_not_straight Hc1) in Hxz.
            rewrite Nat.pow_succ_r'.
            rewrite Nat.mul_comm.
            apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i * 2 / 2)). {
              apply Nat.div_le_compat_l.
              split; [ easy | apply Nat.le_succ_diag_r ].
            }
            rewrite Nat.div_mul; [ | easy ].
            apply angle_mul_nat_overflow_pow_div.
          }
        }
        exfalso.
        rewrite Hu in Hxz.
        progress unfold seq_angle_to_div_nat in Hxz.
        apply (rngl_le_antisymm Hor) in Hzs; [ easy | ].
        apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ 2%L). {
          apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
        }
        now rewrite rngl_mul_0_r.
      }
      (* variation of the curve y=2x²-x-1 in interval [-1,1] *)
      apply rngl_2_x2_sub_1_le_x.
      split; [ easy | ].
      subst x; apply rngl_cos_bound.
    }
    apply (rngl_leb_gt Hor) in Hzs.
    apply (rngl_nle_gt Hor) in Hzs.
    exfalso.
    apply Hzs; clear Hzs.
    apply rngl_sin_nonneg_angle_le_straight.
    apply angle_mul_div_2_pow_le_straight.
    eapply Nat.le_trans; [ now apply Nat.div_mul_le | ].
    apply Nat.div_le_upper_bound; [ easy | ].
    apply Nat.mul_le_mono_r.
    now do 2 apply -> Nat.succ_le_mono.
  }
  apply Nat.succ_lt_mono in Hmi.
  apply Nat.lt_1_r in Hmi; subst m.
(**)
  destruct i; [ cbn in Hni; flia Hni | ].
  destruct i; [ cbn in Hni; flia Hni | ].
  rewrite angle_div_2_pow_succ_r_1.
  remember (2 ^ S (S i) / 3) as n eqn:Hn.
...
  rewrite angle_mul_nat_div_2. {
    rewrite angle_mul_nat_div_2. {
      apply angle_add_overflow_div_2_div_2.
    }
destruct i. {
  cbn.
  rewrite Bool.orb_false_r.
  do 2 rewrite angle_add_0_r.
  apply angle_add_overflow_div_2_div_2.
}
destruct i. {
  cbn.
  rewrite Bool.orb_false_r.
  do 2 rewrite angle_add_0_r.
  rewrite angle_add_div_2_diag.
  apply angle_add_overflow_div_2_div_2.
}
destruct i. {
  cbn - [ angle_mul_nat angle_div_2_pow ].
  rewrite Bool.orb_false_r.
  rewrite angle_mul_1_l.
  apply angle_mul_nat_overflow_distr_add_overflow.
(* ça peut parfaitement déborder *)
...
Search (angle_add_overflow (_ * _) (_ * _)).
...
  rewrite angle_div_2_pow_succ_r_2.
  rewrite angle_div_2_pow_succ_r_2.
  rewrite angle_div_2_pow_succ_r_2.
Search (_ * (_ / ₂^_))%A.
rewrite <- angle_div_2_pow_mul.
Inspect 5.
...
Search (_ * (_ / ₂))%A.
Inspect 3.
Search (_ * (_ / ₂^_))%A.
rewrite <- angle_div_2_pow_mul.
...
  progress unfold angle_add_overflow.
  apply angle_ltb_ge.
  progress unfold angle_leb.
  remember (0 ≤? rngl_sin (u i))%L as zs eqn:Hzs.
  remember (0 ≤? rngl_sin (u i + 2 * u i))%L as zsm eqn:Hzsm.
  symmetry in Hzs, Hzsm.
  destruct zs. {
    destruct zsm; [ | easy ].
    apply rngl_leb_le in Hzs, Hzsm.
    apply rngl_leb_le.
...
Search (_ * (_ / ₂^_))%A.
rewrite <- angle_div_2_pow_mul.
...
remember (u i) as θ1 eqn:Hθ1.
      rename θ' into θ''.
      change_angle_sub_r θ1 angle_straight.
      rename θ'' into θ'.
      rename Hθ' into Hui; symmetry in Hui.
      rewrite Hui in Hzcu, Hzs.
      progress sin_cos_add_sub_straight_hyp T Hzs.
      progress sin_cos_add_sub_straight_hyp T Hzcu.
...
      rewrite Hu in Hzcu, Hzs.
      progress unfold seq_angle_to_div_nat in Hzcu.
      progress unfold seq_angle_to_div_nat in Hzs.
      destruct i; [ cbn in Hni; flia Hni | ].
      destruct i; [ cbn in Hni; flia Hni | ].
      remember (2 ^ S (S i) / 3 * (θ / ₂^S (S i)))%A as θ1 eqn:H1.
      symmetry in H1.
      generalize H1; intros H2.
      apply angle_div_2_pow_mul_nat_if in H1.
      apply (angle_mul_nat_not_overflow_le_l 3) in H1. 2: {
        apply Nat.div_le_lower_bound. 2: {
          rewrite Nat.mul_comm.
          now apply Nat.mul_div_le.
        }
        intros H.
        apply Nat.div_small_iff in H; [ | easy ].
        now apply Nat.nle_gt in H.
      }
      apply Bool.not_true_iff_false in H1.
      apply H1; clear H1.
      progress unfold angle_mul_nat_overflow.
      apply Bool.orb_true_iff.
      left; cbn.
      rewrite angle_add_0_r.
      progress unfold angle_add_overflow.
      progress unfold angle_ltb.
      rewrite angle_add_assoc.
      generalize Hzs; intros H.
      apply (rngl_leb_gt Hor) in H.
      rewrite H; clear H.
      remember (0 ≤? rngl_sin _)%L as zs3 eqn:Hzs3.
      symmetry in Hzs3.
      destruct zs3; [ easy | ].
      apply (rngl_leb_gt Hor) in Hzs3.
      apply rngl_ltb_lt.
...
      rename θ' into θ''.
      change_angle_sub_r θ1 angle_straight.
      rename θ'' into θ'.
      remember (2 ^ S (S i) / 3 * (θ / ₂^S (S i)))%A as θ2 eqn:H2.
      move Hθ' at top; subst θ2.
      do 2 rewrite angle_add_assoc in Hzs3.
      do 2 rewrite angle_add_assoc.
      progress sin_cos_add_sub_straight_hyp T Hzs.
      progress sin_cos_add_sub_straight_hyp T Hzs3.
      progress sin_cos_add_sub_straight_hyp T Hzs3.
      progress sin_cos_add_sub_straight_hyp T Hzcu.
      progress sin_cos_add_sub_straight_goal T.
      progress sin_cos_add_sub_straight_goal T.
      rewrite (rngl_add_opp_l Hop).
      apply (rngl_lt_sub_0 Hop Hor).
(* c'est faux, ça ; c'est fou, ça *)
...
rewrite (angle_add_opp_l Hic).
        rewrite <- (angle_opp_add_distr Hic Hop).
        rewrite (angle_right_add_right Hon Hop).
        progress unfold angle_add_overflow.
        rewrite angle_add_opp_r.
        rewrite <- (angle_opp_add_distr Hic Hop).
        progress unfold angle_ltb.
        rewrite rngl_sin_opp.
        rewrite (rngl_sin_add_straight_l Hon Hop).
        rewrite (rngl_opp_involutive Hop).
        cbn.
        specialize (rngl_0_le_1 Hon Hop Hor) as H1.
        apply rngl_leb_le in H1.
        rewrite H1; clear H1.
        specialize (rngl_opp_1_lt_0 Hon Hop Hor Hc1) as H1.
        apply (rngl_leb_gt Hor) in H1.
        now rewrite H1.
      }
...
apply (rngl_mul_pos_neg Hop Hor Hid).
...
      destruct (rngl_le_dec Hor 0 (rngl_cos (u i))) as [Hzcu| Hzcu]. {
        apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzsm.
        destruct Hzsm as [(H1, H2)| (H1, H2)]. {
          apply (rngl_le_0_mul Hon Hop Hiv Hor) in H1.
          destruct H1 as [| (H1, H3)]; [ easy | ].
          exfalso; apply (rngl_nlt_ge Hor) in H1.
          apply H1; clear H1.
          apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
        }
        apply (rngl_le_antisymm Hor) in Hzcu; [ | easy ].
        apply eq_rngl_cos_0 in Hzcu.
        destruct Hzcu as [Hzcu| Hzcu]. {
          rewrite Hzcu; cbn.
          apply (rngl_0_le_1 Hon Hop Hor).
        }
        exfalso.
        clear H1 H2 Hmi.
        rewrite Hu in Hzcu.
        progress unfold seq_angle_to_div_nat in Hzcu.
        destruct i; [ cbn in Hni; flia Hni | ].
        destruct i; [ cbn in Hni; flia Hni | ].
        apply angle_div_2_pow_mul_nat_if in Hzcu.
        apply (angle_mul_nat_not_overflow_le_l 3) in Hzcu. 2: {
          apply Nat.div_le_lower_bound. 2: {
            rewrite Nat.mul_comm.
            now apply Nat.mul_div_le.
          }
          intros H.
          apply Nat.div_small_iff in H; [ | easy ].
          now apply Nat.nle_gt in H.
        }
        apply Bool.not_true_iff_false in Hzcu.
        apply Hzcu; clear Hzcu.
        progress unfold angle_mul_nat_overflow.
        apply Bool.orb_true_iff.
        left; cbn.
        rewrite angle_add_0_r.
        rewrite (angle_add_opp_l Hic).
        rewrite <- (angle_opp_add_distr Hic Hop).
        rewrite (angle_right_add_right Hon Hop).
        progress unfold angle_add_overflow.
        rewrite angle_add_opp_r.
        rewrite <- (angle_opp_add_distr Hic Hop).
        progress unfold angle_ltb.
        rewrite rngl_sin_opp.
        rewrite (rngl_sin_add_straight_l Hon Hop).
        rewrite (rngl_opp_involutive Hop).
        cbn.
        specialize (rngl_0_le_1 Hon Hop Hor) as H1.
        apply rngl_leb_le in H1.
        rewrite H1; clear H1.
        specialize (rngl_opp_1_lt_0 Hon Hop Hor Hc1) as H1.
        apply (rngl_leb_gt Hor) in H1.
        now rewrite H1.
      }
      apply (rngl_nle_gt Hor) in Hzcu.
rewrite Hu.
progress unfold seq_angle_to_div_nat.
...
remember (0 ≤? 1)%L as b eqn:Hb.
symmetry in Hb.
destruct b. 2: {
rewrite (rngl_opp_0 Hop).
rewrite (rngl_leb_refl Hor).
remember (0 ≤? - 1)%L as b eqn:Hb.
symmetry in Hb.
destruct b; [ exfalso | easy ].
apply rngl_leb_le in Hb.
apply (rngl_nlt_ge Hor) in Hb.
apply Hb; clear Hb.
apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
}
...
rewrite angle_add_opp_r.
rewrite <- (angle_opp_add_distr Hic Hop).
rewrite angle_add_opp_r.
rewrite (angle_right_add_right Hon Hop).
...
rewrite <- angle_div_2_pow_mul in Hzcu; cycle 1. {
  apply Nat.neq_succ_0.
} {
...
apply eq_angle_eq in Hzcu.
remember (5 * (θ / ₂^4))%A as x.
injection Hzcu; clear Hzcu; intros Hc Hs; subst x.
...
(* 5θ/16 = 3π/2 *)
(* θ = 16.3π/(2.5) = 24π/5 *)
(* θ = 24π/5 = (20π+4π)/5 = 4π/5 *)
(* oui, mais 24π/5 et 4π/5 ne sont pas égaux, ils sont équivalents ;
   cf les nombres rationels où c'est pareil pour 1/2 et 2/4 *)
(* 5θ/16 = 24π/16 = 3π/2 ⇒ 24π/5 est racine *)
(* 5θ/16 = 20π/16/5 = 4π/16 = π/4 ⇒ 4π/5 n'est pas racine *)
...
          rewrite angle_div_2_pow_succ_r_1 in Hzcu.
...
progress unfold angle_add_overflow.
apply angle_ltb_ge.
progress unfold angle_leb.
rewrite <- angle_mul_succ_l.
remember (0 ≤? rngl_sin (u i))%L as zs eqn:Hzs.
remember (0 ≤? rngl_sin (S m * u i))%L as zsm eqn:Hzsm.
symmetry in Hzs, Hzsm.
destruct zs. {
  apply rngl_leb_le in Hzs.
  destruct zsm; [ | easy ].
  apply rngl_leb_le in Hzsm.
  apply rngl_leb_le.
(**)
  destruct n; [ easy | clear Hnz ].
  destruct n. {
    apply Nat.lt_1_r in Hmi; subst m.
    rewrite angle_mul_1_l.
    apply (rngl_le_refl Hor).
  }
  destruct n. {
    destruct m. {
      rewrite angle_mul_1_l.
      apply (rngl_le_refl Hor).
    }
    destruct m; [ clear Hmi | flia Hmi ].
    rewrite rngl_sin_mul_2_l in Hzsm.
    rewrite rngl_cos_mul_2_l'.
    apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzsm.
    remember (rngl_cos (u i)) as x eqn:Hx.
    destruct Hzsm as [(_, Hzsm)| (H1, H2)]. 2: {
      destruct (rngl_eq_dec Hed (rngl_sin (u i)) 0) as [Hxz| Hxz]. {
        apply eq_rngl_sin_0 in Hxz.
        destruct Hxz as [Hxz| Hxz]. {
          rewrite Hxz in Hx; cbn in Hx; subst x.
          exfalso; apply (rngl_nlt_ge Hor) in H2.
          apply H2.
          apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
        } {
          rewrite Hxz in Hx; cbn in Hx; subst x.
          exfalso; clear H1 H2 Hzs.
          rewrite Hu in Hxz.
          progress unfold seq_angle_to_div_nat in Hxz.
          destruct i; [ cbn in Hni; flia Hni | ].
          rewrite angle_div_2_pow_succ_r_1 in Hxz.
          rewrite angle_mul_nat_div_2 in Hxz.
          now apply (angle_div_2_not_straight Hc1) in Hxz.
          rewrite Nat.pow_succ_r'.
          rewrite Nat.mul_comm.
          rewrite Nat.div_mul; [ | easy ].
          apply angle_mul_nat_overflow_pow_div.
        }
      }
      exfalso.
      apply (rngl_le_antisymm Hor) in Hzs; [ easy | ].
      apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ 2%L). {
        apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
      }
      now rewrite rngl_mul_0_r.
    }
    (* variation of the curve y=2x²-x-1 in interval [-1,1] *)
    apply rngl_2_x2_sub_1_le_x.
    split; [ easy | ].
    subst x; apply rngl_cos_bound.
  }
  destruct n. {
    destruct m. {
      rewrite angle_mul_1_l.
      apply (rngl_le_refl Hor).
    }
    destruct m. {
      rewrite rngl_sin_mul_2_l in Hzsm.
      apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzsm.
      remember (rngl_cos (u i)) as x eqn:Hx.
      destruct Hzsm as [(H1, Hzsm)| (H1, H2)]. 2: {
        destruct (rngl_eq_dec Hed (rngl_sin (u i)) 0) as [Hxz| Hxz]. {
          apply eq_rngl_sin_0 in Hxz.
          destruct Hxz as [Hxz| Hxz]. {
            rewrite Hxz in Hx; cbn in Hx; subst x.
            exfalso; apply (rngl_nlt_ge Hor) in H2.
            apply H2.
            apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
          } {
            rewrite Hxz in Hx; cbn in Hx; subst x.
            exfalso; clear H1 H2 Hzs.
            rewrite Hu in Hxz.
            progress unfold seq_angle_to_div_nat in Hxz.
            destruct i; [ cbn in Hni; flia Hni | ].
            rewrite angle_div_2_pow_succ_r_1 in Hxz.
            rewrite angle_mul_nat_div_2 in Hxz.
            now apply (angle_div_2_not_straight Hc1) in Hxz.
            rewrite Nat.pow_succ_r'.
            rewrite Nat.mul_comm.
            apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i * 2 / 2)). 2: {
              rewrite Nat.div_mul; [ | easy ].
              apply angle_mul_nat_overflow_pow_div.
            }
            now apply Nat.div_le_compat_l.
          }
        }
        exfalso.
        apply (rngl_le_antisymm Hor) in Hzs; [ easy | ].
        apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ 2%L). {
          apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
        }
        now rewrite rngl_mul_0_r.
      }
      (* variation of the curve y=2x²-x-1 in interval [-1,1] *)
      rewrite rngl_cos_mul_2_l'.
      subst x.
      apply rngl_2_x2_sub_1_le_x.
      split; [ easy | apply rngl_cos_bound ].
    }
    destruct m; [ clear Hmi | flia Hmi ].
(* ui = 2π/3 + ε ⇒ 3ui = 3ε ⇒ marche pas *)
progress unfold seq_angle_to_div_nat in Hu.
(* oui, mais est-ce que ui peut être égal à 2π/3+ε ? Si ça se
   trouve, non ! *)
...
destruct i; [ cbn in Hni; flia Hni | ].
destruct i; [ cbn in Hni; flia Hni | ].
destruct i. {
  clear Hni.
  rewrite Hu in Hzs, Hzsm |-*.
  cbn - [ angle_mul_nat ] in Hzsm, Hzs |-*.
  rewrite angle_mul_1_l in Hzsm, Hzs |-*.
...
}
destruct i. {
  clear Hni.
  rewrite Hu in Hzs, Hzsm |-*.
  cbn - [ angle_mul_nat ] in Hzsm, Hzs |-*.
...
(*
    replace 3 with (1 + 2) in Hzsm |-* by easy.
    rewrite (angle_mul_add_distr_r Hon Hop) in Hzsm |-*.
    rewrite angle_mul_1_l in Hzsm |-*.
    remember (2 * u i)%A as x.
    cbn in Hzsm |-*; subst x.
...
*)
cbn.
cbn in Hzsm.
remember (rngl_sin (u i)) as s eqn:Hs.
remember (rngl_cos (u i)) as c eqn:Hc.
do 2 rewrite (rngl_mul_0_r Hos) in Hzsm |-*.
rewrite (rngl_sub_0_r Hos) in Hzsm |-*.
rewrite rngl_add_0_r in Hzsm |-*.
do 2 rewrite (rngl_mul_1_r Hon) in Hzsm |-*.
...
Search (rngl_cos _ ≤ rngl_cos _)%L.
Check quadrant_1_rngl_cos_add_le_cos_l.
replace 3 with (1 + 2) by easy.
rewrite (angle_mul_add_distr_r Hon Hop).
rewrite angle_mul_1_l.
apply quadrant_1_rngl_cos_add_le_cos_l; try easy.
(* aïe aïe aïe *)
...
Search (0 ≤ rngl_sin _ → _)%L.
apply rngl_cos_le_anticompat_when_sin_nonneg; try easy.
...
    destruct m; [ clear Hmi | flia Hmi ].
    rewrite rngl_sin_mul_2_l in Hzsm.
    rewrite rngl_cos_mul_2_l'.
    apply (rngl_le_0_mul Hon Hop Hiv Hor) in Hzsm.
    remember (rngl_cos (u i)) as x eqn:Hx.
    destruct Hzsm as [(_, Hzsm)| (H1, H2)]. 2: {
...
  destruct (rngl_le_dec Hor 0 (rngl_cos (u i))) as [Hzc| Hcz]. {
    destruct (rngl_le_dec Hor 0 (rngl_sin (m * u i)%A)) as [Hsmu| Hsmu]. {
      destruct (rngl_le_dec Hor 0 (rngl_cos (m * u i)%A)) as [Hcmu| Hcmu]. {
        cbn - [ rngl_cos ].
        now apply quadrant_1_rngl_cos_add_le_cos_l.
      }
      apply (rngl_nle_gt Hor) in Hcmu.
      cbn.
      eapply (rngl_le_trans Hor). {
        apply (rngl_le_sub_nonneg Hop Hor).
        now apply (rngl_mul_nonneg_nonneg Hop Hor).
      }
      apply (rngl_le_0_sub Hop Hor).
      rewrite (rngl_sub_mul_r_diag_l Hon Hop).
      apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
      apply (rngl_le_0_sub Hop Hor).
      apply rngl_cos_bound.
    }
    apply (rngl_nle_gt Hor) in Hsmu.
    destruct (rngl_le_dec Hor (rngl_cos (m * u i)) 0) as [Hcmu| Hcmu]. {
      apply (rngl_lt_eq_cases Hor) in Hzc.
      destruct Hzc as [Hzc| Hzc]. {
        exfalso.
        apply (rngl_nlt_ge Hor) in Hzsm.
        apply Hzsm; clear Hzsm.
        cbn.
        apply (rngl_add_nonpos_neg Hop Hor). {
          now apply (rngl_mul_nonneg_nonpos Hop Hor).
        }
        now apply (rngl_mul_pos_neg Hop Hor Hid).
      }
      symmetry in Hzc.
      apply eq_rngl_cos_0 in Hzc.
      destruct Hzc as [Hzc| Hzc]. {
        rewrite Hzc in Hsmu, Hcmu.
        destruct m; [ now apply (rngl_lt_irrefl Hor) in Hsmu | ].
        destruct m. {
          exfalso.
          apply (rngl_nle_gt Hor) in Hsmu.
          apply Hsmu; clear Hsmu.
          rewrite angle_mul_1_l.
          apply (rngl_0_le_1 Hon Hop Hor).
        }
(*
        destruct m. {
          exfalso.
          apply (rngl_nle_gt Hor) in Hsmu.
          apply Hsmu; clear Hsmu.
          rewrite <- (angle_add_diag Hon Hos).
          rewrite (angle_right_add_right Hon Hop).
          apply (rngl_le_refl Hor).
        }
*)
        rewrite Hu in Hzc.
        progress unfold seq_angle_to_div_nat in Hzc.
        destruct i. {
          cbn in Hzc.
          destruct n; [ easy | ].
          destruct n; [ flia Hmi | ].
          rewrite Nat.div_small in Hzc; [ | flia ].
          rewrite angle_mul_0_l in Hzc.
          symmetry in Hzc.
          now apply (angle_right_neq_0 Hc1) in Hzc.
        }
        destruct i. {
          cbn in Hzc.
          destruct n; [ easy | ].
          destruct n; [ flia Hmi | ].
          destruct n; [ flia Hmi | ].
          rewrite Nat.div_small in Hzc; [ | flia ].
          rewrite angle_mul_0_l in Hzc.
          symmetry in Hzc.
          now apply (angle_right_neq_0 Hc1) in Hzc.
        }
        cbn - [ div Nat.pow ] in Hzc.
        apply angle_div_4_not_right in Hzc; [ easy | easy | ].
        intros H.
        apply eq_angle_eq in H.
        remember (_ * _)%A as x eqn:Hx in H.
        injection H; clear H; intros Hs Hc; subst x.
        (*
        rewrite rngl_cos_cos_mul in Hc.
        rewrite rngl_sin_sin_mul in Hs.
        *)
        remember (2 ^ S (S i) / n) as s eqn:Hsn.
        symmetry in Hsn.
        destruct s. {
          apply Nat.div_small_iff in Hsn; [ | easy ].
          now apply Nat.nle_gt in Hsn.
        }
        destruct s. {
          cbn in Hc, Hs.
          rewrite (rngl_mul_1_r Hon) in Hc, Hs.
          rewrite (rngl_mul_0_r Hos) in Hc, Hs.
          rewrite (rngl_sub_0_r Hos) in Hc.
          rewrite rngl_add_0_r in Hs.
          apply eq_rngl_cos_1 in Hc.
          now apply eq_angle_div_2_pow_0 in Hc.
        }
        destruct s. {
          rewrite rngl_cos_mul_2_l in Hc.
          rewrite rngl_sin_mul_2_l in Hs.
          rewrite <- rngl_mul_assoc in Hs.
          apply (rngl_eq_mul_0_r Hos Hii) in Hs.
          2: apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
          apply (rngl_integral Hos Hid) in Hs.
          destruct Hs as [Hs| Hs]. {
            rewrite Hs in Hc.
            apply eq_rngl_sin_0 in Hs.
            destruct Hs as [Hs| Hs]. {
              rewrite Hs in Hzc.
              do 2 rewrite angle_0_div_2 in Hzc.
              rewrite angle_mul_0_r in Hzc.
              symmetry in Hzc.
              now apply (angle_right_neq_0 Hc1) in Hzc.
            }
            clear Hzc Hc.
            destruct i. {
              cbn in Hni, Hsn.
              apply Nat_div_less_small_iff in Hsn; [ | easy ].
              cbn in Hsn.
              rewrite Nat.add_0_r in Hsn.
              flia Hmi Hni Hsn.
            }
            cbn in Hs.
            now apply (angle_div_2_not_straight Hc1) in Hs.
          }
          rewrite Hs in Hc.
          rewrite (rngl_squ_0 Hos) in Hc.
          rewrite (rngl_sub_0_l Hop) in Hc.
          symmetry in Hc.
          apply (rngl_add_move_0_r Hop) in Hc.
          apply (rngl_eq_add_0 Hor) in Hc; cycle 1. {
            apply (rngl_0_le_1 Hon Hop Hor).
          } {
            apply (rngl_squ_nonneg Hop Hor).
          }
          destruct Hc as (Hc, _).
          now apply (rngl_1_neq_0_iff Hon) in Hc.
        }
        destruct m. {
          rewrite <- (angle_add_diag Hon Hos) in Hsmu.
          rewrite (angle_right_add_right Hon Hop) in Hsmu.
          cbn in Hsmu.
          now apply (rngl_lt_irrefl Hor) in Hsmu.
        }
        destruct s. {
          apply Nat_div_less_small_iff in Hsn; [ | easy ].
          cbn - [ "*" "^" ] in Hsn.
          destruct i; [ cbn in Hsn; flia Hsn | ].
          destruct i; [ cbn in Hsn; flia Hsn | ].
          destruct i. {
            destruct n; [ easy | clear Hnz ].
            destruct n; [ flia Hmi | ].
            do 2 apply Nat.succ_lt_mono in Hmi.
            destruct n; [ flia Hmi | ].
            destruct n; [ cbn in Hsn; flia Hsn | ].
            destruct n; [ cbn in Hsn; flia Hsn | ].
            destruct n. {
              cbn in Hsn.
              destruct m. {
...
do 2 rewrite Nat.add_0_r in H.
apply eq_angle_mul_0 in H.
destruct H as [H| H]. {
  apply Nat.div_small_iff in H; [ | flia Hmi ].
  now apply Nat.nle_gt in H.
}
destruct H as (Hc, Hs).
cbn in Hc.
...
        clear Hzs.
        rewrite Hu in Hzsm.
        progress unfold seq_angle_to_div_nat in Hzsm.
        cbn - [ Nat.pow "*"%A ] in Hzsm.
        rewrite Hzc in Hzsm.
        destruct m. {
          apply (rngl_nlt_ge Hor) in Hzsm.
          apply Hzsm; clear Hzsm.
          replace 3 with (2 + 1) by easy.
          rewrite (angle_mul_add_distr_r Hon Hop).
          rewrite <- (angle_add_diag Hon Hos).
          rewrite (angle_right_add_right Hon Hop).
          rewrite (rngl_sin_add_straight_l Hon Hop).
          rewrite angle_mul_1_l.
          cbn.
          apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
        }
        destruct m. {
          clear Hzsm Hsmu Hcmu.
          destruct i. {
            cbn in Hni.
            replace n with 4 in H by flia Hmi Hni.
            cbn in H.
            now rewrite angle_add_0_r in H.
          }
          destruct i. {
            cbn in H, Hzc, Hni.
            remember (8 / n) as m eqn:Hm.
            symmetry in Hm.
            destruct m. {
              apply Nat.div_small_iff in Hm; [ | flia Hmi ].
              now apply Nat.nle_gt in Hm.
            }
            destruct m. {
              rewrite angle_mul_1_l in H.
              now apply (eq_angle_div_2_0) in H.
            }
            destruct m. {
              now rewrite angle_div_2_mul_2 in H.
            }
            apply Nat_div_less_small_iff in Hm; [ | flia Hmi ].
            flia Hm Hmi.
          }
          destruct i. {
            cbn in H, Hzc, Hni.
            remember (16 / n) as m eqn:Hm.
            symmetry in Hm.
            destruct m. {
              apply Nat.div_small_iff in Hm; [ | flia Hmi ].
              now apply Nat.nle_gt in Hm.
            }
            destruct m. {
              rewrite angle_mul_1_l in H.
              apply (eq_angle_div_2_0) in H.
              now apply (eq_angle_div_2_0) in H.
            }
            destruct m. {
              rewrite angle_div_2_mul_2 in H.
              now apply (eq_angle_div_2_0) in H.
            }
            destruct m. {
              apply Nat_div_less_small_iff in Hm; [ | flia Hmi ].
              cbn - [ "*" ] in Hm.
              destruct n; [ flia Hm | ].
              destruct n; [ flia Hm | ].
              destruct n; [ flia Hm | ].
              destruct n; [ flia Hm | ].
              destruct n; [ flia Hm | ].
              destruct n. {
                cbn in Hm.
apply eq_angle_mul_0 in H.
...
(*
θ = 8π/3 = (6π+2π)/3 = 2π/3
θ/2 = π/3
θ/2/2 = π/6
3*(θ/2/2) = π/2
*)
...
              rewrite Nat.mul_add_distr_l in Hm.
cbn in Hm.
flia Hni Hm.
...
              rewrite angle_div_2_mul_2 in H.
              now apply (eq_angle_div_2_0) in H.
            }
            apply Nat_div_less_small_iff in Hm; [ | flia Hmi ].
            flia Hm Hmi.
          }
...
Theorem angle_eq_mul_0_r :
  ∀ n θ, (n * θ)%A = 0%A → n mod 2 = 1 → ((n - 1) * θ = angle_straight)%A.
Proof.
destruct_ac.
intros * Hnt Hnz.
rewrite angle_mul_sub_distr_r. 2: {
  rewrite <- Hnz.
  now apply Nat.mod_le.
}
rewrite angle_mul_1_l.
rewrite Hnt.
rewrite (angle_sub_0_l Hon Hos).
specialize (Nat.div_mod n 2 (Nat.neq_succ_0 _)) as H1.
rewrite Hnz in H1.
rewrite H1 in Hnt.
(* ah, fait chier *)
...
apply (angle_opp_inj Hop).
rewrite (angle_opp_involutive Hop).
Search (- angle_straight)%A.
Search (n mod _ ≠ 0).
rewrite
rewrite angle_opp_straight.
... ...
apply angle_eq_mul_0_r in H. 2: {
  intros H'.
  apply Nat.div_small_iff in H'; [ | flia Hmi ].
  now apply Nat.nlt_ge in Hni.
}
...
  rewrite H' in Hzc.
  rewrite angle_mul_0_l in Hzc.
  symmetry in Hzc.
  now apply (angle_right_neq_0 Hc1) in Hzc.
}
...
apply (f_equal (λ θ, (2 * θ)%A)) in H.
symmetry in H.
rewrite <- (angle_add_diag Hon Hos) in H.
rewrite angle_straight_add_straight in H.
symmetry in H.
apply angle_eq_mul_0_r in H; [ | easy ].
cbn - [ div Nat.pow ] in H.
rewrite angle_add_0_r in H.
Search (_ * _ = angle_straight)%A.
...

destruct n; [ easy | ].
(* mmmm... mais ça, c'est faux, ça *)
...
Search (_ * (_ / ₂))%A.
rewrite angle_mul_nat_div_2 in Hzc. 2: {
...
          destruct i. {
            cbn in Hzc.
            destruct n; [ easy | ].
            destruct n; [ flia Hmi | ].
            destruct n; [ flia Hmi | ].
            destruct n; [ flia Hmi | ].
...
            rewrite Nat.div_small in Hzc; [ | flia ].
            rewrite angle_mul_0_l in Hzc.
            symmetry in Hzc.
            now apply (angle_right_neq_0 Hc1) in Hzc.
          }
...
Search (angle_right = 0)%A.
Search (angle_straight = 0)%A.
destruct n; [ flia Hmi | ].
destruct n; [ flia Hmi | ].
...
          rewrite Hzc in *.
          clear Hzs.
          replace 4 with (2 + 2) by easy.
          rewrite (angle_mul_add_distr_r Hon Hop).
          rewrite <- (angle_add_diag Hon Hos).
          rewrite (angle_right_add_right Hon Hop).
          rewrite angle_straight_add_straight.
          cbn.
          exfalso.
          replace 3 with (1 + 2) in Hsmu, Hcmu by easy.
          rewrite (angle_mul_add_distr_r Hon Hop) in Hsmu, Hcmu.
          rewrite <- (angle_add_diag Hon Hos) in Hsmu, Hcmu.
          rewrite (angle_right_add_right Hon Hop) in Hsmu, Hcmu.
          rewrite angle_mul_1_l in Hsmu, Hcmu.
          clear Hsmu Hcmu.
...
        cbn in Hzsm |-*.
        rewrite Hzc in Hzsm |-*.
        cbn in Hzsm |-*.
...
Search (_ * _ ≤ _)%L.
apply rngl_le_div_r; try easy.
...
      apply (rngl_le_sub_le_add_l Hop Hor).
      remember (rngl_cos (u i) * rngl_cos (m * u i))%L as x eqn:Hx.
apply rngl_le_sub_nonneg.
      apply (rngl_le_trans Hor _ (rngl_cos (u i) * rngl_cos (m * u i))
...
(*
apply rngl_sin_cos_nonneg_sin_sub_nonneg_cos_le; try easy.
cbn - [ rngl_cos ].
apply quadrant_1_rngl_cos_add_le_cos_l; try easy. (* faut voir les cas cos *)
*)
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy. (* ça dépend *)
...
  apply rngl_cos_le_anticompat_when_sin_nonneg; [ easy | easy | ].
  rewrite Hu.
...
Theorem angle_lim_seq_angle_not_mul_overflow :
  ∀ n θ θ',
  angle_lim (seq_angle_to_div_nat θ n) θ'
  → angle_mul_nat_overflow n θ' = false.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 θ').
  apply (angle_mul_nat_overflow_0_r Hon Hos).
}
intros * Hlim.
progress unfold seq_angle_to_div_nat in Hlim.
apply (angle_all_add_not_overflow n θ').
intros m Hm.
progress unfold angle_add_overflow.
apply angle_ltb_ge.
progress unfold angle_leb.
rewrite <- angle_mul_succ_l.
remember (0 ≤? rngl_sin θ')%L as zs eqn:Hzs.
remember (0 ≤? rngl_sin (S m * θ'))%L as zsm eqn:Hzsm.
symmetry in Hzs, Hzsm.
(**)
destruct zsm. 2: {
  destruct zs; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzs.
  apply (rngl_leb_gt Hor) in Hzsm.
  apply rngl_leb_le.
...
destruct zsm. {
  apply rngl_leb_le in Hzsm.
  destruct zs. {
    apply rngl_leb_le in Hzs.
    apply rngl_leb_le.
    specialize (angle_lim_seq_angle_le n θ θ' Hlim) as Htt.
    assert (Hts : (θ' ≤ angle_straight)%A). {
      now apply rngl_sin_nonneg_angle_le_straight.
    }
    specialize (Htt Hts).
    cbn - [ rngl_cos ].
    destruct (rngl_le_dec Hor 0 (rngl_cos θ')) as [Hzc| Hzc]. {
      destruct (rngl_le_dec Hor 0 (rngl_sin (m * θ'))) as [Hzm| Hzm]. {
        apply angle_add_overflow_le_lemma_111; try easy.
        now right; right; left.
      }
      apply (rngl_nle_gt Hor) in Hzm.
      cbn - [ rngl_sin ] in Hzsm.
(* c'est faux : m*θ'=-ε ; mais peut-être qu'avec Htt et Hts je peux
   m'en sortir ; aucune idée si j'ai une chance *)
(**)
      exfalso.
      revert n Hlim Hm.
      revert θ' Hzs Hzsm Htt Hts Hzc Hzm.
      induction m; intros. {
        rewrite angle_mul_0_l in Hzm.
        now apply (rngl_lt_irrefl Hor) in Hzm.
      }
      destruct n; [ easy | ].
      apply Nat.succ_lt_mono in Hm.
...
      revert m Hm Hzsm Hzm.
      revert θ' Hzs Htt Hzc Hts Hlim.
      induction n; intros; [ easy | ].
      destruct m. {
        rewrite angle_mul_0_l, angle_add_0_r.
        apply (rngl_le_refl Hor).
      }
      apply Nat.succ_lt_mono in Hm.
      destruct (Nat.eq_dec (S m) n) as [Hsmn| Hsmn]. {
        subst n.
(* ouais, bon, ça sert à rien *)
...
      }
      apply IHn; try easy.
      flia Hm Hsmn.
    }
...
      specialize (IHn _ Hm).
      cbn - [ rngl_sin ] in Hzm.
...
}
now apply H1.
...
specialize (angles_lim_le (λ i, 2 ^ i / n * (θ / ₂^i)) (λ _, θ))%A as H1.
specialize (H1 θ' θ)%A.
cbn in H1.
assert (Htt : (θ' ≤ θ)%A). {
  apply H1; [ | easy | ]. 2: {
    intros ε Hε.
    exists 0.
    intros p _.
    now rewrite angle_eucl_dist_diag.
  }
  intros.
Theorem seq_angle_to_div_nat_le :
  ∀ i n θ, (2 ^ i / n * (θ / ₂^i) ≤ θ)%A.
Proof.
... ...
  apply seq_angle_to_div_nat_le.
}
...
      specialize (Hlim (angle_eucl_dist θ' 0)).
      assert (Htz : (0 < angle_eucl_dist θ' 0)%L). {
        apply (rngl_lt_iff Hor).
        split; [ apply angle_eucl_dist_nonneg | ].
        intros H; symmetry in H.
        apply angle_eucl_dist_separation in H.
        subst θ'.
        rewrite angle_mul_0_r in Hzm.
        now apply (rngl_lt_irrefl Hor) in Hzm.
      }
      specialize (Hlim Htz).
      destruct Hlim as (N, HN).
      specialize (HN N (le_refl _)).
...
specialize (angle_eucl_dist_triangular) as H1.
specialize (H1 θ' (2 ^ N / n * (θ / ₂^N)) 0)%A.
exfalso.
apply (rngl_nlt_ge Hor) in H1.
apply H1; clear H1.
rewrite (angle_eucl_dist_symmetry Hic Hop).
eapply (rngl_le_lt_trans Hor); [ | apply HN ].
(* ah bin non *)
...
Search (rngl_cos _ ≤ rngl_cos _)%L.
apply angle_add_overflow_le_lemma_4 with (θ2 := (m * θ')%A); try easy.
apply quadrant_1_rngl_cos_add_le_cos_l.
Check seq_angle_to_div_nat_le.
... ...
Theorem seq_angle_to_div_nat_le :
  ∀ i n θ, (2 ^ i / n * (θ / ₂^i) ≤ θ)%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ * _)%A), (H1 θ).
  apply angle_le_refl.
}
intros.
progress unfold angle_leb.
remember (0 ≤? rngl_sin (2 ^ i / n * (θ / ₂^i)))%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs2, Hzs.
destruct zs2. {
  clear Hzs2.
  destruct zs; [ | easy ].
  apply rngl_leb_le in Hzs.
  apply rngl_leb_le.
  destruct i. {
    cbn.
    destruct n; [ apply rngl_cos_bound | ].
    destruct n. {
      rewrite Nat.div_1_r.
      rewrite angle_mul_1_l.
      apply (rngl_le_refl Hor).
    }
    rewrite Nat.div_small; [ | now apply -> Nat.succ_lt_mono ].
    rewrite angle_mul_0_l.
    apply rngl_cos_bound.
  }
  destruct n; [ apply rngl_cos_bound | ].
  destruct n. {
    rewrite Nat.div_1_r.
    rewrite angle_div_2_pow_mul_2_pow.
    apply (rngl_le_refl Hor).
  }
  apply (rngl_le_trans Hor _ (rngl_cos (2 ^ S i / 2 * (θ / ₂^S i)))). {
    rewrite Nat.pow_succ_r'.
    rewrite Nat.mul_comm.
    rewrite Nat.div_mul; [ | easy ].
    rewrite angle_div_2_pow_succ_r_2.
    rewrite angle_div_2_pow_mul_2_pow.
    now apply rngl_cos_le_cos_div_2.
  }
  apply rngl_cos_decr.
  split. {
    apply angle_mul_nat_le_mono_nonneg_r. {
      rewrite Nat.pow_succ_r'.
      rewrite Nat.mul_comm.
      rewrite Nat.div_mul; [ | easy ].
      rewrite angle_div_2_pow_succ_r_2.
      apply angle_mul_nat_overflow_pow_div.
    }
    apply Nat.div_le_compat_l.
    split; [ easy | ].
    now do 2 apply -> Nat.succ_le_mono.
  }
  rewrite Nat.pow_succ_r'.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul; [ | easy ].
  rewrite angle_div_2_pow_succ_r_2.
  rewrite angle_div_2_pow_mul_2_pow.
  apply angle_div_2_le_straight.
}
destruct zs. {
  exfalso.
  apply (rngl_leb_gt Hor) in Hzs2.
  apply rngl_leb_le in Hzs.
  apply (rngl_nle_gt Hor) in Hzs2.
  apply Hzs2; clear Hzs2.
  revert n θ Hzs.
  induction i; intros. {
    cbn.
    destruct n; [ apply (rngl_le_refl Hor) | ].
    destruct n. {
      rewrite Nat.div_1_r.
      now rewrite angle_mul_1_l.
    }
    rewrite Nat.div_small; [ | now do 2 apply -> Nat.succ_le_mono ].
    apply (rngl_le_refl Hor).
  }
  rewrite angle_div_2_pow_succ_r_2.
  eapply (rngl_le_trans Hor). {
    apply (IHi n (θ / ₂)%A).
    apply rngl_sin_div_2_nonneg.
  }
(*
destruct n; [ apply (rngl_le_refl Hor) | ].
destruct n. {
  do 2 rewrite Nat.div_1_r.
  rewrite <- angle_div_2_pow_succ_r_2.
  rewrite angle_div_2_pow_mul_2_pow.
  rewrite -> angle_div_2_pow_succ_r_2.
  rewrite angle_div_2_pow_mul_2_pow.
}
*)
  remember (θ ≤? angle_right)%A as tr eqn:Htr.
  symmetry in Htr.
  destruct tr. {
    apply rngl_sin_incr.
    split. {
      apply angle_mul_nat_le_mono_nonneg_r. {
        destruct n; [ easy | ].
        apply angle_mul_nat_not_overflow_le_l with (n := 2 ^ S i). {
          rewrite <- Nat.div_1_r.
          apply Nat.div_le_compat_l.
          split; [ easy | ].
          now apply -> Nat.succ_le_mono.
        }
        rewrite Nat.pow_succ_r'.
        apply angle_mul_nat_overflow_angle_div_2_mul_2_div_2.
        apply angle_mul_nat_overflow_pow_div.
      }
      destruct n; [ easy | ].
      apply Nat.div_le_mono; [ easy | ].
      apply Nat.pow_le_mono_r; [ easy | ].
      apply Nat.le_succ_diag_r.
    }
    destruct n; [ apply angle_right_nonneg | ].
    destruct n. {
      rewrite Nat.div_1_r.
      rewrite <- angle_div_2_pow_succ_r_2.
      now rewrite angle_div_2_pow_mul_2_pow.
    }
...
(*
  rewrite <- (angle_mul_1_l Hon Hos angle_right).
  rewrite <- angle_straight_div_2.
*)
  rewrite <- angle_div_2_pow_succ_r_2.
(*
  rewrite angle_div_2_pow_succ_r_1.
*)
  apply angle_le_trans with (θ2 := (2 ^ S i * (θ / ₂^S i))%A). {
(*
    rewrite <- (angle_mul_1_l Hon Hos (2 ^ S i * _)).
*)
    apply angle_mul_nat_le_mono_nonneg_r. {
      apply angle_mul_nat_overflow_pow_div.
    }
    rewrite <- (Nat.div_1_r (2 ^ S i)) at 2.
    apply Nat.div_le_compat_l.
    split; [ easy | ].
    now apply -> Nat.succ_le_mono.
  }
  rewrite angle_div_2_pow_mul_2_pow.
(* rahhhh... fait chier *)
...
  apply angle_le_trans with (θ2 := 0%A).
Search (_ * _ ≤ _ * _)%A.
...
Show.
Check seq_angle_to_div_nat_le.
Search (_ → angle_mul_nat_overflow _ _ = false).
...
(*
...
Search (_ * (_ / ₂^_))%A.
Search (rngl_cos (_ * _)).
(* faire un Fixpoint, comme pour rngl_cos_div_pow_2 *)
...
Search rngl_cos_div_pow_2.
rngl_cos_div_pow_2_eq: ∀ (θ : angle T) (n : nat), rngl_cos (θ / ₂^S n) = rngl_cos_div_pow_2 (θ / ₂) n
...
Search (_ * _)%A.
rewrite rngl
Search (rngl_cos _ ≤ rngl_cos _)%L.
Check angle_add_overflow_le_lemma_111.
remember ((2 ^ i / n * (θ / ₂^i)))%A as θ' eqn:Hθ'.
destruct (rngl_le_dec Hor 0 (rngl_cos θ')) as [Hsc| Hsc].
specialize (angle_add_overflow_le_lemma_111 θ' (θ - θ')) as H1.
Search (_ + (_ - _))%A.
Search (_ - _ + _)%A.
rewrite angle_add_comm in H1.
rewrite angle_sub_add in H1.
apply H1; try easy; [ now right; right; left | ].
(* θ' ≤ θ ? *)
...
Search (0 ≤ rngl_sin (_ - _))%L.
apply rngl_sin_sub_nonneg; try easy.
...
rewrite angle
rewrite angle_add_0_r in H1.
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
apply rngl_cos_le_anticompat_when_sin_nonneg; try easy.
...
  apply rngl_cos_decr.
  split. {
progress unfold angle_leb.
apply rngl_leb_le in Hzs2, Hzs.
rewrite Hzs2, Hzs.
    destruct i. {
      cbn.
      rewrite <- (angle_mul_1_l Hon Hos θ) at 2.
      apply angle_mul_nat_le_mono_nonneg_r; [ easy | ].
      destruct n; [ easy | ].
      apply Nat.div_le_upper_bound; [ easy | ].
      cbn.
      now apply -> Nat.succ_le_mono.
    }
    cbn.
    rewrite Nat.add_0_r.
    destruct i. {
      cbn.
Search (_ * (_ / ₂))%A.
rewrite angle_mul_nat_div_2.
...
  destruct i. {
    destruct n; [ apply rngl_cos_bound | ].
    remember (S n) as sn; cbn; subst sn.
*)
...
Theorem glop :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos θ1)%L.
Proof.
intros * Hzs1 Hzc1 Hzs12.
cbn.
(* non, c'est faux, ça, suffit que θ2 = 2π-ε *)
... ...
now apply glop.
Search (0 ≤ rngl_sin (_ + _))%L.
specialize (rngl_sin_nonneg_add_nonneg θ' (m * θ') Hzs Hzsm) as H1.
      apply angle_add_overflow_le_lemma_111; try easy. {
        now right; right; left.
      }
      rewrite angle_add_comm in Hzsm.
      apply rngl_sin_add_nonneg_sin_nonneg with (θ2 := θ'); [ | easy ].
      progress unfold angle_add_overflow.
      apply angle_ltb_ge.
      progress unfold angle_leb.
      apply rngl_leb_le in Hzsm.
      rewrite Hzsm.
...
Search (0 ≤ rngl_sin (_ + _))%L.
Search (rngl_cos (_ + _) ≤ rngl_cos _)%L.
...
    apply rngl_cos_decr.
    split; [ | now apply rngl_sin_nonneg_angle_le_straight ].
    progress unfold angle_leb.
    rewrite Hzs.
    apply rngl_leb_le in Hzsm.
    rewrite Hzsm.
    apply rngl_leb_le.
...
destruct n; [ easy | ].
destruct n. {
  cbn.
  rewrite Bool.orb_false_r.
  rewrite angle_add_0_r.
  progress unfold angle_lim in Hlim.
  progress unfold is_limit_when_tending_to_inf in Hlim.
  progress unfold angle_add_overflow.
  progress unfold angle_ltb.
  remember (0 ≤? rngl_sin (θ' + θ'))%L as zsa eqn:Hzsa.
  remember (0 ≤? rngl_sin θ')%L as zs eqn:Hzs.
  symmetry in Hzsa, Hzs.
  destruct zsa. {
    apply rngl_leb_le in Hzsa.
    destruct zs. {
      apply rngl_leb_le in Hzs.
      apply (rngl_ltb_ge Hor).
      destruct (rngl_le_dec Hor 0 (rngl_cos θ')) as [Hzc| Hzc]. {
        apply angle_add_overflow_le_lemma_111; try easy.
        now right; right; left.
      }
      apply (rngl_nle_gt Hor) in Hzc.
      remember (θ' =? angle_straight)%A as ts eqn:Hts.
      symmetry in Hts.
      destruct ts. {
        apply (angle_eqb_eq Hed) in Hts.
        subst θ'.
        clear Hzc Hzs Hzsa.
...
        apply angle_add_overflow_le_lemma_2; try easy. {
          intros H.
          apply eq_rngl_cos_opp_1 in H.
          subst θ'.
cbn in *.
Search (rngl_cos (_ + _) ≤ rngl_cos _)%L.
...
apply angle_add_overflow_le_lemma_111; try easy.
apply angle_add_overflow_le_lemma_1 with (θ2 := θ'); try easy.
apply quadrant_1_rngl_cos_add_le_cos_l; try easy.
...
}
... ...
now apply angle_lim_seq_angle_not_mul_overflow in Hlim.
... ...
destruct ao. 2: {
  specialize (Hlim' eq_refl).
  progress unfold seq_angle_to_div_nat in Hlim.
  progress unfold seq_angle_to_div_nat in Hlim'.
  set (θi := λ i, (2 ^ i / n * (θ / ₂^i))%A).
  set (θ'i := λ i, (2 ^ i / n * (n * θ' / ₂^i))%A).
  progress fold θi in Hlim.
  progress fold θ'i in Hlim'.
  move Hlim before Hlim'.
  move θ'i before θi.
...
(*
...
  clear Hlim'.
  destruct n; [ easy | ].
  apply (angle_mul_nat_overflow_succ_l_true Hon Hos) in Hao.
...
  apply Bool.not_false_iff_true in Hao.
  exfalso; apply Hao; clear Hao Hlim'.
(**)
  progress unfold seq_angle_to_div_nat in Hlim.
...
Theorem glop :
  ∀ n θ u,
  angle_lim u θ
  → (∀ i, angle_mul_nat_overflow n (u i) = false)
  → angle_mul_nat_overflow n θ = false.
Proof.
destruct_ac.
intros * Hlim Hov.
induction n; [ easy | ].
apply (angle_mul_nat_overflow_succ_l_false Hon Hos).
split. {
  apply IHn.
  intros i.
  specialize (Hov i).
  now apply (angle_mul_nat_overflow_succ_l_false Hon Hos) in Hov.
}
progress unfold angle_lim in Hlim.
progress unfold is_limit_when_tending_to_inf in Hlim.
... ...
apply (glop n) in Hlim; [ easy | ].
intros i.
clear Hlim Hiz.
induction n; [ easy | ].
cbn - [ div ].
destruct n; [ easy | ].
set (u := seq_angle_to_div_nat θ).
cbn in IHn.
destruct n. {
  clear IHn.
  cbn - [ u ].
  rewrite Bool.orb_false_iff.
  rewrite angle_add_0_r.
  split; [ | easy ].
  apply angle_add_diag_not_overflow; [ easy | ].
  progress unfold u; cbn - [ div ].
  progress unfold seq_angle_to_div_nat.
  induction i. {
    cbn.
    apply (angle_straight_pos Hc1).
  }
  cbn - [ div ].
  rewrite Nat.add_0_r.
  rewrite Nat_add_diag.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul; [ | easy ].
  rewrite angle_mul_nat_div_2. 2: {
    apply angle_mul_nat_overflow_pow_div.
  }
  apply (angle_div_2_lt_straight Hc1).
}
...
  apply angle_div_2_add_not_overflow.
  cbn in Haov.
Print angle_add_overflow.
Print angle_mul_nat_overflow.
...
Check angle_mul_overflow.
...
2: {
Search (angle_add_overflow _ (S _ * _)).
Search (angle_add_overflow (S _ * _) _).
cbn in Haov.
Search (angle_add_overflow _ (_ + _)).
...
symmetry.
apply angle_div_2_add_not_overflow.
... ...
rewrite angle_mul_nat_div_2.
Search (_ / ₂ < angle_straight)%A.
...
Search (0 ≤ angle_straight)%A.
Search (0 < angle_straight)%A.
    apply angle_straight_nonneg.
...
apply rngl_mul_neg_neg.
...
  apply rngl_leb_nle in Hzst.
  apply Hzst; clear Hzst; cbn.
...
  cbn.
  apply (rngl_le_trans Hor _ (rngl_cos θ * rngl_cos θ)). {
    apply (rngl_le_sub_nonneg Hop Hor).
    apply (rngl_mul_diag_nonneg Hop Hor).
  }
...
apply rngl_mul_non
...
  apply (rngl_mul_nonneg_r).
...
  apply (rngl_le_sub_le_add_r Hop Hor).
Search (_ ≤ _ + _)%L.
...
Search (_ → angle_add_overflow _ _ = false).
Theorem glip :
  ∀ θ i,
  angle_add_overflow (seq_angle_to_div_nat θ 2 i)
    (seq_angle_to_div_nat θ 2 i) = false.
Proof.
destruct_ac.
intros.
induction i. {
  cbn.
  apply angle_add_overflow_0_r.
}
cbn - [ div ].
Theorem seq_angle_to_div_nat_succ_r :
  ∀ θ n i,
  seq_angle_to_div_nat θ n (S i) = 0%A.
Proof.
intros.
progress unfold seq_angle_to_div_nat.
cbn.
rewrite Nat.add_0_r.
Search ((_ + _) / _).
(* ah la la la la... ça a pas l'air simple, c't'histoire *)
...
  revert θ' Hlim.
  induction n; intros; [ easy | clear Hiz ].
  destruct n; [ easy | ].
  specialize (IHn (Nat.neq_succ_0 _)).
  destruct n. {
    cbn.
    rewrite angle_add_0_r.
    rewrite Bool.orb_false_r.
    clear IHn.
    progress unfold seq_angle_to_div_nat in Hlim.
    progress unfold angle_lim in Hlim.
    progress unfold is_limit_when_tending_to_inf in Hlim.
...
  rewrite (angle_mul_nat_overflow_succ_l_false Hon Hos).
...
  progress unfold seq_angle_to_div_nat in Hlim.
  progress unfold angle_lim in Hlim.
  progress unfold is_limit_when_tending_to_inf in Hlim.
*)
...
} {
  specialize (Hlim' eq_refl).
  move Hao before Hiz.
(**)
  progress unfold seq_angle_to_div_nat in Hlim.
  progress unfold seq_angle_to_div_nat in Hlim'.
  set (θi := λ i, (2 ^ i / n * (θ / ₂^i))%A).
  set (θ'i := λ i, (2 ^ i / n * (n * θ / ₂^i))%A).
  progress fold θi in Hlim.
  progress fold θ'i in Hlim'.
...
  assert
      (H :
       angle_lim (λ i, (n * (θi i))%A) θ'). {
    progress unfold angle_lim in Hlim'.
    progress unfold angle_lim.
    progress unfold is_limit_when_tending_to_inf in Hlim'.
    progress unfold is_limit_when_tending_to_inf.
    intros ε Hε.
    specialize (Hlim' ε Hε).
    destruct Hlim' as (N, HN).
    exists N.
    intros m Hm.
    specialize (HN m Hm).
    rewrite angle_div_2_pow_mul in HN; [ | easy | easy ].
    rewrite (angle_mul_nat_assoc Hon Hop) in HN.
    rewrite Nat.mul_comm in HN.
    rewrite <- (angle_mul_nat_assoc Hon Hop) in HN.
    easy.
  }
  clear Hlim'; rename H into Hlim'.
...
  set (u := seq_angle_to_div_nat) in Hlim, Hlim'.
  assert (H :
    ∀ ε, (0 < ε)%L →
    ∃ N, ∀ p, N ≤ p → (angle_eucl_dist (u θ n p) (u (n * θ')%A n p) < ε)%L). {
    intros ε Hε.
    assert (Hε2 : (0 < ε / 2)%L). {
      apply (rngl_lt_div_r Hon Hop Hiv Hor).
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
      now rewrite (rngl_mul_0_l Hos).
    }
    specialize (Hlim (ε / 2) Hε2)%L.
    specialize (Hlim' (ε / 2) Hε2)%L.
    destruct Hlim as (N, HN).
    destruct Hlim' as (N', HN').
    exists (max N N').
    intros p Hp.
    assert (H : N ≤ p) by flia Hp.
    specialize (HN _ H); clear H.
    assert (H : N' ≤ p) by flia Hp.
    specialize (HN' _ H); clear H.
    specialize (angle_eucl_dist_triangular) as H1.
    specialize (H1 (u θ n p) θ' (u (n * θ')%A n p)).
    rewrite (angle_eucl_dist_symmetry Hic Hop θ') in H1.
    eapply (rngl_le_lt_trans Hor); [ apply H1 | ].
    specialize (rngl_div_add_distr_r Hiv ε ε 2)%L as H2.
    rewrite (rngl_add_diag2 Hon) in H2.
    rewrite (rngl_mul_div Hi1) in H2. 2: {
      apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
    }
    rewrite H2.
    now apply (rngl_add_lt_compat Hop Hor).
  }
  remember (θ <? n * θ')%A as tt' eqn:Htt'.
  symmetry in Htt'.
  destruct tt'. {
    exfalso.
    remember (n * θ' - θ)%A as Δθ eqn:Hdt.
    apply angle_add_move_l in Hdt.
    specialize (H 1%L).
    assert (H1 : (0 < 1)%L) by apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
    specialize (H H1); clear H1.
    destruct H as (N, HN).
    specialize (HN N (Nat.le_refl _)).
    rewrite <- Hdt in HN.
    progress unfold u in HN.
    progress unfold seq_angle_to_div_nat in HN.
...
  remember (θ =? n * θ')%A as tt eqn:Htt.
  symmetry in Htt.
  destruct tt; [ now apply angle_eqb_eq in Htt | ].
  apply (angle_eqb_neq Hed) in Htt; exfalso.
Search (_ <? _)%A.
...
    specialize (HN' _ H).
    specialize (HN (Nat.le_max_l _ _)).
  specialize (HN' (Nat.le_max_r _ _)).
  progress unfold angle_eucl_dist in HN.
  progress unfold angle_eucl_dist in HN'.
  set (m := max N N') in HN, HN'.
...
  specialize (Hlim 1%L).
  specialize (H1 1%L).
  assert (H : (0 < 1)%L) by apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
  specialize (Hlim H).
  specialize (H1 H); clear H.
  destruct Hlim as (N, HN).
  destruct H1 as (N', HN').
  specialize (HN (max N N')).
  specialize (HN' (max N N')).
  specialize (HN (Nat.le_max_l _ _)).
  specialize (HN' (Nat.le_max_r _ _)).
  progress unfold angle_eucl_dist in HN.
  progress unfold angle_eucl_dist in HN'.
  set (m := max N N') in HN, HN'.
...
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
progress unfold is_angle_limit_when_tending_to_inf in Hlim.
progress unfold is_gen_limit_when_tending_to_inf in Hlim.
progress unfold seq_angle_to_div_nat in Hlim.
assert
  (H :
    ∀ ε : T, (0 < ε)%L →
      ∃ N : nat, ∀ n : nat, N ≤ n →
      (angle_dist θ θ' < ε)%L). {
  intros ε Hε.
  specialize (Hlim ε Hε).
  destruct Hlim as (N, HN).
  exists N.
  intros n Hn.
  specialize (HN n Hn).
  specialize (Nat.div_mod_eq (2 ^ n) i) as H1.
  symmetry in H1.
  apply Nat.add_sub_eq_r in H1.
  apply (f_equal rngl_of_nat) in H1.
  rewrite (rngl_of_nat_mul Hon Hos) in H1.
  symmetry in H1.
  apply (rngl_mul_move_l Hic Hi1) in H1. 2: {
    intros Hi.
    now apply (eq_rngl_of_nat_0 Hon Hch) in Hi.
  }
...
Fixpoint rngl_to_nat :
  ∀ a,
...
Check rngl_mul_move_l.
Check rngl_mul_move_r.
...
Search (_ * _ = _)%L.
...
Search (_ = _ * _)%L.
...
Search ((_ * _) * _)%A.
progress unfold angle_dist in HN.
Search (rngl_cos (_ * _)%A).
Inspect 8.
...
rat_is_inf_sum_of_inv_rad_pow.
...
intros Hic Hon Hop Har Hed Hch * Hiz Hlim.
destruct_ac.
revert θ θ' Hlim.
induction i; intros; [ easy | ].
clear Hiz.
destruct i. {
  clear IHi; cbn.
  rewrite angle_add_0_r.
  progress unfold seq_angle_to_div_nat in Hlim.
  assert (H : is_angle_limit_when_tending_to_inf (λ _, θ) θ'). {
    intros ε Hε.
    specialize (Hlim ε Hε).
    destruct Hlim as (N, HN).
    exists N.
    intros n Hn.
    specialize (HN n Hn).
    rewrite Nat.div_1_r in HN.
    now rewrite angle_div_2_pow_mul_2_pow in HN.
  }
  clear Hlim; rename H into Hlim.
  progress unfold is_angle_limit_when_tending_to_inf in Hlim.
  specialize (angle_dist_is_dist Hic) as H1.
  specialize (gen_limit_unique Hon Hop Hiv Hor _ _ H1) as H2.
  specialize (H2 (λ _, θ) θ' θ Hlim).
  symmetry.
  apply H2.
  intros ε Hε.
  exists 0.
  intros n Hn.
  now rewrite dist_refl.
}
specialize (IHi (Nat.neq_succ_0 _)).
(**)
destruct i. {
  clear IHi; cbn.
  rewrite angle_add_0_r.
  progress unfold seq_angle_to_div_nat in Hlim.
  assert (H : is_angle_limit_when_tending_to_inf (λ _, θ) (2 * θ')%A). {
    intros ε Hε.
enough (H2ε : (0 < 2 * ε)%L).
    specialize (Hlim (2 * ε)%L H2ε).
    destruct Hlim as (N, HN).
    exists (N - 1). (* au pif *)
    intros n Hn.
    apply Nat.le_sub_le_add_r in Hn.
    specialize (HN (n + 1) Hn).
    rewrite Nat.add_1_r in HN.
    rewrite Nat.pow_succ_r in HN; [ | easy ].
    rewrite Nat.mul_comm in HN.
    rewrite Nat.div_mul in HN; [ | easy ].
    cbn in HN.
    rewrite (angle_div_2_pow_mul_2_pow Hic) in HN.
    progress unfold angle_dist in HN.
    progress unfold angle_dist.
    rewrite rngl_cos_mul_2_l.
    rewrite rngl_sin_mul_2_l.
...
    rewrite Nat.mul_div in HN.
    rewrite Nat.pow_add_r in HN.
    rewrite
Search (_ ^ (_ + _)).
    rewrite Nat.add_
    destruct n. {
...
    rewrite angle_div_2_pow_mul_2_pow in HN.
...
remember (S n) as sn; cbn; subst sn.
rewrite angle_add_comm.
apply (angle_sub_move_r Hic).
apply IHn.
progress unfold seq_angle_to_div_nat.
progress unfold seq_angle_to_div_nat in Hlim.
...
Search (rngl_of_nat _ = 0%L).
  rewrite rngl_of_nat_succ.
...
intros Hic Hon Hop Har Hed * Hnz Hlim.
(*
progress unfold is_angle_upper_limit_when_tending_to_inf in Hlim.
Check rat_is_inf_sum_of_inv_rad_pow.
*)
move Hos before Hed.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
move Hi1 before Hos.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
move Hid before Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  now rewrite (H1 _) in Hnz.
}
move Hc1 before Hid.
move α before θ.
specialize (rat_is_inf_sum_of_inv_rad_pow Hic Hon Hop Hiv Har) as H1.
specialize (H1 2 1 n (le_refl _) Hnz).
progress unfold is_limit_when_tending_to_inf in H1.
progress unfold seq_converging_to_rat in H1.
progress unfold seq_angle_to_div_nat.
Search angle_dist.
...
progress unfold angle_lt in Hα.
progress unfold angle_compare in Hα.
progress unfold rngl_compare in Hα.
cbn in Hα.
rewrite (rngl_leb_refl Hor) in Hα.
remember (0 ≤? rngl_sin α)%L as zs eqn:Hzs; symmetry in Hzs.
destruct zs. {
  apply rngl_leb_le in Hzs.
  remember (rngl_cos α =? 1)%L as ce1 eqn:Hce1; symmetry in Hce1.
  destruct ce1; [ easy | ].
  apply (rngl_eqb_neq Hed) in Hce1.
  remember (rngl_cos α ≤? 1)%L as cl1 eqn:Hcl1; symmetry in Hcl1.
  destruct cl1; [ clear Hα | easy ].
  apply rngl_leb_le in Hcl1.
  specialize (H1 (rngl_sin (angle_div_2 Hiv Hc2 Hor α))).
  assert (H : (0 < rngl_sin (angle_div_2 Hiv Hc2 Hor α))%L). {
    progress unfold angle_div_2.
    cbn.
    rewrite <- (rl_sqrt_0 Hor Hop Hic Hid).
    apply (rl_sqrt_lt_rl_sqrt Hic Hop). {
      apply (rngl_le_refl Hor).
    }
    apply (rngl_div_lt_pos Hon Hop Hiv Hor). 2: {
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    }
    apply (rngl_lt_0_sub Hop Hor).
    now apply (rngl_lt_iff Hor).
  }
  specialize (H1 H); clear H.
  destruct H1 as (N, HN).
  exists N. (* au pif *)
  intros m Hm.
...
rewrite (rngl_squ_mul Hic) in H2.
rewrite <- rngl_squ
Search (√_ * √_)%L.
Search (√_)%L.
...
apply (rngl_mul_le_compat Hop Hor) with (b := √b%L) (d := √a%L).
apply (rngl_
Search (_ * _ < _ * _)%Z.
...
apply (rngl_mul_lt_mono_pos_r Hop Hor Hi1) with (a := √(
...
apply rl_sqrt_lt_rl_sqrt.
Search (_ < √ _)%L.
Search (rngl_squ _ < rngl_squ _)%L.
Search (rngl_squ _ ≤ rngl_squ _)%L.
Search (rngl_abs (√ _))%L.
Search (√ 0)%L.
...
    apply rngl_div_lt_pos.
...

Definition angle_div_nat θ n :=
  {| rngl_cos := 1; rngl_sin := 0;
     rngl_cos2_sin2 := 42 |}%L.
...
*)

Theorem Cauchy_sin_cos_Cauchy_angle :
  ∀ u,
  rngl_is_Cauchy_sequence (λ i, rngl_cos (u i))
  → rngl_is_Cauchy_sequence (λ i, rngl_sin (u i))
  → is_Cauchy_sequence angle_eucl_dist u.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hcc Hcs.
  intros ε Hε.
  rewrite H1 in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hcc Hcs.
intros ε Hε.
assert (Hε2 : (0 < √(ε² / 2))%L). {
  apply (rl_sqrt_pos Hon Hos).
  apply (rngl_lt_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  rewrite (rngl_mul_0_l Hos).
  progress unfold rngl_squ.
  now apply (rngl_mul_pos_pos Hop Hor Hii).
}
specialize (Hcc _ Hε2).
specialize (Hcs _ Hε2).
destruct Hcc as (cn, Hcc).
destruct Hcs as (sn, Hcs).
move sn before cn.
exists (max cn sn).
intros p q Hp Hq.
progress unfold angle_eucl_dist.
rewrite <- (rngl_abs_nonneg_eq Hop Hor √_)%L. 2: {
  apply rl_sqrt_nonneg.
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_squ_nonneg Hop Hor).
  apply (rngl_squ_nonneg Hop Hor).
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor ε)%L. 2: {
  now apply (rngl_lt_le_incl Hor) in Hε.
}
apply (rngl_squ_lt_abs_lt Hop Hor Hii).
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_squ_nonneg Hop Hor).
  apply (rngl_squ_nonneg Hop Hor).
}
specialize (Hcc p q).
specialize (Hcs p q).
assert (H : cn ≤ p) by now apply Nat.max_lub_l in Hp.
specialize (Hcc H); clear H.
assert (H : cn ≤ q) by now apply Nat.max_lub_l in Hq.
specialize (Hcc H); clear H.
assert (H : sn ≤ p) by now apply Nat.max_lub_r in Hp.
specialize (Hcs H); clear H.
assert (H : sn ≤ q) by now apply Nat.max_lub_r in Hq.
specialize (Hcs H); clear H.
progress unfold rngl_dist in Hcc.
progress unfold rngl_dist in Hcs.
apply (rngl_lt_le_incl Hor) in Hε2.
rewrite <- (rngl_abs_nonneg_eq Hop Hor √_)%L in Hcc, Hcs; [ | easy | easy ].
apply (rngl_abs_lt_squ_lt Hic Hop Hor Hid) in Hcc, Hcs.
assert (Hzε2 : (0 ≤ ε² / 2)%L). {
  apply (rngl_le_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_squ_nonneg Hop Hor).
}
rewrite (rngl_squ_sqrt Hon) in Hcc, Hcs; [ | easy | easy ].
specialize (rngl_div_add_distr_r Hiv ε² ε² 2)%L as H1.
rewrite (rngl_add_diag2 Hon) in H1.
rewrite (rngl_mul_div Hi1) in H1. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
rewrite H1.
rewrite (rngl_squ_sub_comm Hop) in Hcc, Hcs.
now apply (rngl_add_lt_compat Hop Hor).
Qed.

(* to be completed
Theorem seq_angle_to_div_nat_is_Cauchy :
  ∀ n θ,
  is_Cauchy_sequence angle_eucl_dist
    (seq_angle_to_div_nat θ n).
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  intros ε Hε.
  rewrite H1 in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros.
set (u := λ i, (2 ^ i / n * angle_div_2_pow θ i)%A).
apply Cauchy_sin_cos_Cauchy_angle. {
  progress unfold seq_angle_to_div_nat.
  enough (H :
    ∀ ε, (0 < ε)%L →
    ∃ N : nat,
      ∀ p q : nat,
      N ≤ p
      → N ≤ q
      → (rngl_abs (rngl_sin (u p / ₂ + u q / ₂)) < ε / 2)%L). {
  intros ε Hε.
  progress unfold rngl_dist.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists N.
  intros p q Hp Hq.
  specialize (HN p q Hp Hq).
  progress fold (u p).
  progress fold (u q).
  rewrite rngl_cos_sub_rngl_cos.
  rewrite (rngl_abs_opp Hop Hor).
  rewrite <- rngl_mul_assoc.
  rewrite (rngl_abs_mul Hop Hi1 Hor).
  replace (rngl_abs 2) with 2%L. 2: {
    symmetry; apply (rngl_abs_nonneg_eq Hop Hor).
    apply (rngl_0_le_2 Hon Hop Hor).
  }
  rewrite (rngl_mul_comm Hic).
  apply (rngl_lt_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_abs_mul Hop Hi1 Hor).
  remember (rngl_sin _)%L as s eqn:Hs.
  eapply (rngl_le_lt_trans Hor _ (rngl_abs s * 1))%L. {
    apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
      apply (rngl_abs_nonneg Hop Hor).
    }
    clear s Hs HN.
    remember (rngl_sin _) as s eqn:Hs.
    progress unfold rngl_abs.
    remember (s ≤? 0)%L as sz eqn:Hsz.
    symmetry in Hsz; subst s.
    destruct sz. {
      apply (rngl_opp_le_compat Hop Hor).
      rewrite (rngl_opp_involutive Hop).
      apply rngl_sin_bound.
    }
    apply rngl_sin_bound.
  }
  rewrite (rngl_mul_1_r Hon).
  easy.
}
intros ε Hε.
...
set (u := seq_angle_to_div_nat θ n).
...

Theorem all_gc_has_nth_root :
  rngl_is_archimedean T = true →
  rngl_characteristic T = 0 →
  rl_has_integral_modulus T = true →
  ∀ n, n ≠ 0 → ∀ z : GComplex T, ∃ x : GComplex T, gc_power_nat x n = z.
Proof.
destruct_ac.
intros Har Hch Him * Hnz *.
specialize (polar Him z) as H1.
set (ρ := √((gre z)² + (gim z)²)%L).
set
  (θ :=
     (if (0 ≤? gim z)%L then rngl_acos Hor (gre z / ρ)%L
      else angle_opp (rngl_acos Hor (gre z / ρ)%L))).
specialize (H1 ρ θ eq_refl eq_refl).
set (ρ' := rl_nth_root n ρ).
specialize angle_div_nat_is_inf_sum_of_angle_div_2_pow as H2.
specialize (H2 Har Hch).
remember (seq_angle_to_div_nat θ n) as θi eqn:Hθi.
progress unfold seq_angle_to_div_nat in Hθi.
...
set (θ' := angle_div_nat θ n).
exists (mk_gc (ρ' * cos θ') (ρ' * sin θ')).
...
assert (Hre : (-1 ≤ gre z / ρ ≤ 1)%L). {
  subst ρ.
... ...
apply rl_sqrt_div_squ_squ.
}
...
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Hiz| Hiz]. {
  rewrite (rngl_cos_acos Htr).
...
  rewrite (rngl_mul_div_r Hon Hic Hiv). 2: {
    subst ρ.
    progress unfold rl_sqrt.
    progress unfold rl_pow.
    rewrite if_bool_if_dec.
    destruct (Sumbool.sumbool_of_bool _) as [H2| H2]. {
      apply (rngl_eqb_eq Heb) in H2.
      generalize Hmi; intros H.
      progress unfold rl_has_integral_modulus in H.
      remember (rl_opt_mod_intgl_prop T) as mi eqn:Hmi1.
      symmetry in Hmi1.
      destruct mi as [mi| ]; [ clear H | easy ].
      apply mi in H2.
      apply (neq_neq_GComplex Heb) in Hz.
      cbn in Hz.
      now destruct Hz.
    }
    apply (rngl_eqb_neq Heb) in H2.
    apply (rl_exp_neq_0 Hon Hop Hiv H10 Htr).
  }
...
Theorem rl_sin_acos {T} {ro : ring_like_op T} {rp : ring_like_prop T}
  {rl : real_like_prop T} :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 2 →
  rngl_has_eq_dec T = true →
  rngl_is_ordered = true →
  rl_has_trigo = true →
  ∀ x, (-1 ≤ x ≤ 1)%L →
  rl_sin (rngl_acos x) = rl_sqrt (1%L - rngl_squ x).
Proof.
intros * Hon Hop Hiv Hc2 Heb Hor Htr * Hx1.
specialize (rl_cos2_sin2 Htr (rngl_acos x)) as H1.
rewrite (rngl_cos_acos Htr _ Hx1) in H1.
apply (rngl_add_sub_eq_l Hos) in H1.
rewrite H1.
rewrite (rl_sqrt_squ Hon Hop Hiv Hc2 Heb Hor Htr).
(* acos est dans [0,Π[, donc sin est >0 *)
...
Theorem rl_sin_acos {T} {ro : ring_like_op T} {rp : ring_like_prop T}
  {rl : real_like_prop T} :
  ∀ x, rl_sin (rngl_acos x) = rl_sqrt (1 - rngl_squ x)%L.
... ...
rewrite rl_sin_acos.
...
rewrite (rl_cos_atan2 Htr).
rewrite <- Hρ.
rewrite (rngl_mul_div_r Hon Hic Hiv). 2: {
  subst ρ.
  progress unfold rl_sqrt.
  progress unfold rl_pow.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [H2| H2]. {
    apply (rngl_eqb_eq Heb) in H2.
    generalize Hmi; intros H.
    progress unfold rl_has_integral_modulus in H.
    remember (rl_opt_mod_intgl_prop T) as mi eqn:Hmi1.
    symmetry in Hmi1.
    destruct mi as [mi| ]; [ clear H | easy ].
    apply mi in H2.
    apply (neq_neq_GComplex Heb) in Hz.
    cbn in Hz.
    now destruct Hz.
  }
  apply (rngl_eqb_neq Heb) in H2.
  apply (rl_exp_neq_0 Hon Hop Hiv H10 Htr).
}
Check rl_cos_atan2.
Theorem rl_sin_atan2 {T} {ro : ring_like_op T} {rp : ring_like_prop T}
  {rl : real_like_prop T} :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 2 →
  rngl_has_eq_dec T = true →
  rngl_is_ordered = true →
  rl_has_trigo = true →
  ∀ x y, rl_sin (rl_atan2 y x) = (y / rl_sqrt (rngl_squ x + rngl_squ y))%L.
Proof.
intros * Hon Hop Hiv Hc2 Heb Hor Htr *.
specialize (rl_cos2_sin2 Htr (rl_atan2 y x)) as H1.
rewrite (rl_cos_atan2 Htr) in H1.
apply (rngl_add_sub_eq_l Hos) in H1.
remember (rl_sqrt _) as ρ eqn:Hρ.
...
specialize (rl_cos2_sin2 Htr (rngl_acos x)) as H1.
rewrite (rngl_cos_acos Htr) in H1.
apply (rngl_add_sub_eq_l Hos) in H1.
rewrite H1.
rewrite (rl_sqrt_squ Hon Hop Hiv Hc2 Heb Hor Hle Htr).
(* acos est dans [0,Π[, donc sin est >0 *)
...

Theorem polyn_modl_tends_tow_inf_when_var_modl_tends_tow_inf {T}
  {ro : ring_like_op T} {rp : ring_like_prop T} {rl : real_like_prop T} :
  let roc := gc_ring_like_op T in
  rngl_has_opp T = true →
  rngl_has_inv (GComplex T) = true →
  rngl_has_1 (GComplex T) = true →
  ∀ la, 1 < length la → llast la 0%L ≠ 0%L →
  ∀ mz, ∃ z₀, ∀ z, (gc_modl z₀ ≤ gc_modl z →
  mz ≤ gc_modl (rngl_eval_polyn la z))%L.
Proof.
intros * Hop Hivc Honc * Hla Hl1 *.
...
*)

(* to be completed
Theorem gc_opt_alg_closed :
  let ro := gc_ring_like_op T in
  if (rngl_has_opp T && rngl_has_inv (GComplex T) &&
      rngl_has_1 (GComplex T))%bool
  then
     ∀ l : list (GComplex T), 1 < length l → List.last l 0%L ≠ 0%L →
     ∃ x : GComplex T, rngl_eval_polyn l x = 0%L
  else not_applicable.
Proof.
intros; cbn.
remember (rngl_has_opp T) as op eqn:Hop; symmetry in Hop.
destruct op; [ | easy ].
remember (rngl_has_inv (GComplex T)) as ivc eqn:Hivc; symmetry in Hivc.
destruct ivc; [ | easy ].
remember (rngl_has_1 (GComplex T)) as onc eqn:Honc; symmetry in Honc.
destruct onc; [ cbn | easy ].
intros la Hla Hl1.
*)

End a.

(* to be completed
Definition gc_ring_like_prop T
  {ro : ring_like_op T} {rp : ring_like_prop T} {rl : real_like_prop T}
  {roc : ring_like_op (GComplex T)}
  (Hop : rngl_has_opp T = true) :
    @ring_like_prop (GComplex T) (gc_ring_like_op T) :=
  let Hos := rngl_has_opp_has_opp_or_subt Hop in
  let Hsu := rngl_has_opp_has_no_subt Hop in
  {| rngl_mul_is_comm := rngl_mul_is_comm T;
     rngl_is_integral_domain := false;
     rngl_is_archimedean := false;
     rngl_is_alg_closed :=
       (rngl_has_opp T && rngl_has_inv (GComplex T) &&
        rngl_has_1 (GComplex T))%bool;
     rngl_characteristic := rngl_characteristic T;
     rngl_add_comm := gc_add_comm;
     rngl_add_assoc := gc_add_assoc;
     rngl_add_0_l := gc_add_0_l;
     rngl_mul_assoc := gc_mul_assoc Hop;
     rngl_opt_mul_1_l := gc_opt_mul_1_l Hos;
     rngl_mul_add_distr_l := gc_mul_add_distr_l Hop;
     rngl_opt_mul_comm := gc_opt_mul_comm;
     rngl_opt_mul_1_r := gc_opt_mul_1_r Hos;
     rngl_opt_mul_add_distr_r := gc_opt_mul_add_distr_r Hop;
     rngl_opt_add_opp_diag_l := gc_opt_add_opp_diag_l Hop;
     rngl_opt_add_sub := gc_opt_add_sub Hsu;
     rngl_opt_sub_add_distr := gc_opt_sub_add_distr Hsu;
     rngl_opt_mul_inv_diag_l := gc_opt_mul_inv_diag_l Hop;
     rngl_opt_mul_inv_diag_r := gc_opt_mul_inv_diag_r;
     rngl_opt_mul_div := gc_opt_mul_div;
     rngl_opt_mul_quot_r := gc_opt_mul_quot_r;
     rngl_opt_le_dec := NA;
     rngl_opt_integral := NA;
     rngl_opt_alg_closed := gc_opt_alg_closed;
     rngl_characteristic_prop := gc_characteristic_prop;
     rngl_opt_le_refl := NA;
     rngl_opt_le_antisymm := NA;
     rngl_opt_le_trans := NA;
     rngl_opt_add_le_compat := NA;
     rngl_opt_mul_le_compat_nonneg := NA;
     rngl_opt_mul_le_compat_nonpos := NA;
     rngl_opt_mul_le_compat_non_opp := NA;
     rngl_opt_not_le := NA;
     rngl_opt_archimedean := NA |}.
*)
