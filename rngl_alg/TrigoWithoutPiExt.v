Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.RingLike.
Require Import TrigoWithoutPi.
Require Import AngleLeSubAdd.
Require Import RealLike.
Require Import TacChangeAngle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

Theorem rngl_cos_add_le_cos :
  ∀ θ1 θ2,
  (θ1 ≠ angle_straight ∨ θ2 ≠ angle_straight ∨
   0 ≤ rngl_cos θ1 ∨ 0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
intros * H12 Hzs1 Hzs2 Hzs12.
rewrite <- or_assoc in H12.
rewrite or_comm in H12.
rewrite or_assoc in H12.
destruct H12 as [H12| H12]. {
  cbn.
  apply (rngl_le_sub_le_add_l Hop Hor).
  apply (rngl_le_0_sub Hop Hor).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_add_nonneg_nonneg Hor).
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  cbn.
  apply (rngl_le_sub_le_add_l Hop Hor).
  apply (rngl_le_0_sub Hop Hor).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_add_nonneg_nonneg Hor).
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
apply (rngl_nle_gt Hor) in Hc1z.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  remember (θ1 - angle_right)%A as θ' eqn:Hθ'.
  apply angle_add_move_r in Hθ'.
  subst θ1; rename θ' into θ1.
  rewrite angle_add_add_swap in Hzs12 |-*.
  rewrite rngl_cos_add_right_r in Hc1z.
  apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
  rewrite rngl_sin_add_right_r in Hzs1, Hzs12.
  do 2 rewrite rngl_cos_add_right_r.
  apply -> (rngl_opp_le_compat Hop Hor).
  apply (rngl_lt_le_incl Hor) in Hc1z.
  apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
  now apply rngl_sin_add_nonneg.
  cbn.
  apply (rngl_le_sub_le_add_l Hop Hor).
  apply (rngl_le_0_sub Hop Hor).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_add_nonneg_nonneg Hor).
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
destruct H12 as [H12| H12]; [ easy | ].
apply (rngl_nle_gt Hor) in Hc2z.
destruct (rngl_eq_dec Heo (rngl_sin θ1) 0) as [Hs1z| Hs1z]. {
  apply eq_rngl_sin_0 in Hs1z.
  destruct Hs1z; subst θ1. {
    rewrite angle_add_0_l.
    apply rngl_cos_bound.
  }
  destruct H12 as [H12| H12]; [ easy | ].
  rewrite rngl_sin_add_straight_l in Hzs12.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
  apply (rngl_le_antisymm Hor) in Hzs12; [ | easy ].
  symmetry in Hzs12.
  apply eq_rngl_sin_0 in Hzs12.
  destruct Hzs12; subst θ2; [ | easy ].
  rewrite angle_add_0_r.
  apply (rngl_le_refl Hor).
}
exfalso.
apply (rngl_nlt_ge Hor) in Hzs12.
apply Hzs12; clear Hzs12.
cbn.
apply (rngl_add_neg_nonpos Hop Hor). {
  apply (rngl_mul_pos_neg Hop Hor); [ | | easy ]. {
    rewrite Bool.orb_true_iff; right.
    rewrite Hi1; cbn.
    apply (rngl_has_eq_dec_or_is_ordered_r Hor).
  }
  apply not_eq_sym in Hs1z.
  now apply (rngl_lt_iff Hor).
} {
  apply (rngl_mul_nonpos_nonneg Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
}
Qed.

Theorem quadrant_1_sin_sub_nonneg_cos_le :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin (θ1 - θ2))%L
  → (rngl_cos θ1 ≤ rngl_cos θ2)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Hsz1 Hzs2 Hzc1 Hzc2 Hzs12.
destruct (rngl_eq_dec Heo (rngl_sin θ2) 0) as [Hs2z| Hs2z]. {
  apply eq_rngl_sin_0 in Hs2z.
  destruct Hs2z; subst θ2. {
    apply rngl_cos_bound.
  }
  exfalso.
  apply (rngl_nlt_ge Hor) in Hzc2.
  apply Hzc2; clear Hzc2; cbn.
  apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
}
cbn in Hzs12.
rewrite (rngl_mul_opp_r Hop) in Hzs12.
rewrite (rngl_add_opp_r Hop) in Hzs12.
apply -> (rngl_le_0_sub Hop Hor) in Hzs12.
apply (rngl_lt_eq_cases Hor) in Hzs2.
apply not_eq_sym in Hs2z.
destruct Hzs2 as [Hzs2| Hzs2]; [ | easy ].
clear Hs2z.
apply (rngl_mul_le_mono_pos_r Hop Hor Hii _ _ (rngl_sin θ2) Hzs2) in Hzs12.
rewrite <- rngl_mul_assoc in Hzs12.
rewrite fold_rngl_squ in Hzs12.
specialize (cos2_sin2_1 θ2) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1 in Hzs12; clear H1.
rewrite (rngl_mul_sub_distr_l Hop) in Hzs12.
rewrite (rngl_mul_1_r Hon) in Hzs12.
apply (rngl_le_sub_le_add_l Hop Hor) in Hzs12.
eapply (rngl_le_trans Hor); [ apply Hzs12 | ].
rewrite (rngl_mul_mul_swap Hic).
progress unfold rngl_squ.
rewrite rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_r.
rewrite <- rngl_cos_sub.
rewrite <- (rngl_mul_1_l Hon).
apply (rngl_mul_le_mono_nonneg_r Hop Hor); [ easy | ].
apply rngl_cos_bound.
Qed.

Theorem rngl_cos_le_cos_add :
  ∀ θ1 θ2,
  (rngl_sin θ1 ≤ 0)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (rngl_cos θ1 ≤ rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs12.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  change_angle_add_r θ1 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_hyp T Hzc1.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_goal T.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    move Hzc2 before Hzc1.
    assert (Hzc12 : (0 ≤ rngl_sin (θ1 + θ2))%L). {
      cbn.
      apply (rngl_add_nonneg_nonneg Hor).
      now apply (rngl_mul_nonneg_nonneg Hop Hor).
      now apply (rngl_mul_nonneg_nonneg Hop Hor).
    }
    apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
    now apply (rngl_lt_le_incl Hor).
    apply angle_le_sub_le_add_l_lemma_1; try easy.
    rewrite angle_sub_diag.
    apply rngl_cos_bound.
    rewrite angle_sub_diag.
    apply (rngl_le_refl Hor).
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  exfalso.
  change_angle_sub_r θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hc2z.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12; cbn.
  apply (rngl_add_nonneg_nonneg Hor).
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hc1z.
change_angle_sub_r θ1 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs1.
progress sin_cos_add_sub_straight_hyp T Hc1z.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_goal T.
apply (rngl_lt_le_incl Hor) in Hc1z, Hzs12.
apply rngl_cos_add_le_cos; try easy.
now right; right; left.
Qed.

Theorem angle_add_overflow_le_lemma_2 :
  ∀ θ1 θ2,
  rngl_cos θ1 ≠ (-1)%L
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_cos θ1 ≤ 0)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hco1 Hzs1 Hzs2 Hc1z Hzs12.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Hco1 Hzs1 Hzs2 Hc1z Hzs12.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hco1.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_le_dec Hor (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
  change_angle_sub_r θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hc2z.
  progress sin_cos_add_sub_right_goal T.
  apply (rngl_nlt_ge Hor).
  intros Hc12.
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  apply (rngl_lt_iff Hor).
  split. {
    cbn.
    apply (rngl_add_nonneg_nonneg Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
  }
  intros H; symmetry in H.
  apply eq_rngl_sin_0 in H.
  destruct H as [H| H]. {
    rewrite H in Hc12.
    apply (rngl_nle_gt Hor) in Hc12.
    apply Hc12; clear Hc12; cbn.
    apply rngl_sin_bound.
  }
  apply angle_add_move_l in H.
  subst θ2.
  clear Hc12 Hc2z.
  rewrite rngl_cos_sub_straight_l in Hzs2.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs2.
  apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
  symmetry in Hzs2.
  apply eq_rngl_cos_0 in Hzs2.
  destruct Hzs2; subst θ1; [ easy | ].
  apply (rngl_nlt_ge Hor) in Hc1z.
  apply Hc1z; clear Hc1z.
  apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
}
apply (rngl_nle_gt Hor) in Hzc2.
move Hzc2 before Hzs1.
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy. {
  cbn.
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
}
apply angle_le_sub_le_add_l_lemma_1; try easy. {
  rewrite angle_sub_diag.
  apply rngl_cos_bound.
} {
  rewrite angle_sub_diag.
  apply (rngl_le_refl Hor).
}
cbn.
apply (rngl_add_nonneg_nonneg Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
now apply (rngl_lt_le_incl Hor).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
Qed.

Theorem angle_add_overflow_le_lemma_5 :
  ∀ θ1 θ2,
  rngl_cos θ1 ≠ 1%L
  → (0 ≤ rngl_sin θ1)%L
  → (rngl_sin θ2 < 0)%L
  → (0 < rngl_cos θ1)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos θ1)%L
  → False.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Hc11 Hzs1 Hzs2 Hzc1 Hzs12 H12.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
  change_angle_opp θ2.
  progress sin_cos_opp_hyp T Hzs2.
  progress sin_cos_opp_hyp T H12.
  progress sin_cos_opp_hyp T Hzs12.
  progress sin_cos_opp_hyp T Hzc2.
  apply (rngl_nlt_ge Hor) in H12.
  apply H12; clear H12.
  rewrite rngl_cos_sub_comm.
  destruct (rngl_eq_dec Heo (rngl_cos θ1) (rngl_cos θ2)) as [Hc1c2| Hc1c2]. {
    apply rngl_cos_eq in Hc1c2.
    destruct Hc1c2; subst θ1. {
      rewrite angle_sub_diag; cbn.
      apply (rngl_lt_iff Hor).
      split; [ apply rngl_cos_bound | easy ].
    }
    cbn in Hzs1, Hzc1.
    rewrite angle_sub_opp_r.
    exfalso.
    apply (rngl_nlt_ge Hor) in Hzs12.
    apply Hzs12; clear Hzs12; cbn.
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_mul_opp_l Hop).
    rewrite (rngl_add_opp_r Hop).
    rewrite <- (rngl_opp_add_distr Hop).
    apply (rngl_opp_neg_pos Hop Hor).
    rewrite (rngl_mul_comm Hic).
    apply (rngl_add_pos_nonneg Hor).
    now apply (rngl_mul_pos_pos Hop Hor Hii).
    apply (rngl_mul_nonneg_nonneg Hop Hor).
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  apply rngl_cos_lt_rngl_cos_sub; try easy.
  apply quadrant_1_sin_sub_nonneg_cos_le; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nlt_ge Hor) in Hzc2.
change_angle_add_r θ2 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs2.
progress sin_cos_add_sub_straight_hyp T H12.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T Hzc2.
exfalso.
apply (rngl_nlt_ge Hor) in Hzs12.
apply Hzs12; clear Hzs12; cbn.
apply (rngl_add_nonneg_pos Hor).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
now apply (rngl_mul_pos_pos Hop Hor).
Qed.

Theorem angle_add_overflow_le_lemma_6 :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (rngl_sin θ2 < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos θ1)%L
  → False.
Proof.
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzs1 Hzs2 Hzs12 H12.
  rewrite (H1 (rngl_sin _)) in Hzs2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
intros * Hzs1 Hzs2 Hzs12 H12.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
  destruct (rngl_eq_dec Heo (rngl_cos θ1) 1) as [H| H]. {
    apply eq_rngl_cos_1 in H.
    subst θ1.
    rewrite angle_add_0_l in Hzs12.
    now apply (rngl_nlt_ge Hor) in Hzs12.
  } {
    apply angle_add_overflow_le_lemma_5 in H12; try easy.
  }
}
apply (rngl_nlt_ge Hor) in Hzc1.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hzc1.
progress sin_cos_add_sub_right_hyp T H12.
progress sin_cos_add_sub_right_hyp T Hzs12.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
  change_angle_opp θ2.
  progress sin_cos_opp_hyp T Hzs2.
  progress sin_cos_opp_hyp T Hzc2.
  progress sin_cos_opp_hyp T Hzs12.
  progress sin_cos_opp_hyp T H12.
  apply (rngl_nlt_ge Hor) in H12.
  apply H12; clear H12.
  rename Hzs12 into Hzc12.
  destruct (rngl_lt_dec Hor (rngl_sin (θ1 - θ2)) 0) as [Hs12z| Hzs12]. {
    eapply (rngl_lt_le_trans Hor); [ apply Hs12z | easy ].
  }
  apply (rngl_nlt_ge Hor) in Hzs12.
  destruct (rngl_eq_dec Heo (rngl_cos θ2) 1) as [Hc21| Hc21]. {
    apply eq_rngl_cos_1 in Hc21.
    subst θ2.
    now apply (rngl_lt_irrefl Hor) in Hzs2.
  }
  destruct (rngl_eq_dec Heo (rngl_cos θ1) 0) as [Hc1z| Hc1z]. {
    apply eq_rngl_cos_0 in Hc1z.
    destruct Hc1z; subst θ1. {
      rewrite rngl_sin_sub_right_l.
      apply (rngl_lt_iff Hor).
      split; [ | easy ].
      apply rngl_cos_bound.
    }
    exfalso.
    apply (rngl_nlt_ge Hor) in Hzc1.
    apply Hzc1; cbn.
    apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
  }
  apply rngl_sin_sub_lt_sin_l; [ easy | easy | ].
  apply (rngl_lt_iff Hor).
  now apply not_eq_sym in Hc1z.
}
apply (rngl_nlt_ge Hor) in Hzc2.
change_angle_add_r θ2 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs2.
progress sin_cos_add_sub_straight_hyp T Hzc2.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T H12.
apply (rngl_nlt_ge Hor) in H12.
apply H12; clear H12.
destruct (rngl_eq_dec Heo (rngl_sin θ1) 0) as [Hs1z| Hs1z]. {
  apply eq_rngl_sin_0 in Hs1z.
  destruct Hs1z; subst θ1. {
    rewrite angle_add_0_l; cbn.
    now rewrite rngl_add_0_l.
  }
  exfalso.
  apply (rngl_nlt_ge Hor) in Hzs1.
  apply Hzs1; cbn.
  apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
}
apply (rngl_add_pos_nonneg Hor). {
  apply not_eq_sym in Hs1z.
  now apply (rngl_lt_iff Hor).
}
cbn.
apply (rngl_add_nonneg_nonneg Hor).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
now apply (rngl_lt_le_incl Hor).
Qed.

(* pas très satisfait de cette preuve. Elle a marché, certes,
   mais me paraît bien compliquée. Il y aurait sûrement un
   moyen de la rendre plus simple, mais j'ai pas le temps
   de regarder. Tant pis, c'est prouvé, c'est déjà ça. Et
   puis ce théorème est important. *)
Theorem angle_add_not_overflow_comm :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → angle_add_overflow θ2 θ1 = false.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov.
  progress unfold angle_add_overflow.
  progress unfold angle_ltb.
  rewrite (H1 (rngl_sin _)).
  rewrite (rngl_leb_refl Hor).
  rewrite (H1 (rngl_sin _)).
  rewrite (rngl_leb_refl Hor).
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_ltb_ge Hor).
  apply (rngl_le_refl Hor).
}
intros * Haov.
progress unfold angle_add_overflow in Haov.
progress unfold angle_add_overflow.
progress unfold angle_ltb in Haov.
progress unfold angle_ltb.
rewrite (angle_add_comm θ2).
remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs12, Hzs1, Hzs2.
destruct zs2. {
  destruct zs12; [ | easy ].
  destruct zs1; [ | easy ].
  apply rngl_leb_le in Hzs1, Hzs12, Hzs2.
  apply (rngl_ltb_ge Hor) in Haov.
  apply (rngl_ltb_ge Hor).
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    rewrite angle_add_comm.
    apply rngl_cos_add_le_cos; try easy.
    now right; right; left.
    now rewrite angle_add_comm.
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  destruct (rngl_eq_dec Heo (rngl_cos θ2) (- 1)) as [Hc2o1| Ho1c2]. {
    apply (eq_rngl_cos_opp_1) in Hc2o1.
    subst θ2.
    rewrite rngl_sin_add_straight_r in Hzs12.
    rewrite rngl_cos_add_straight_r.
    apply -> (rngl_opp_le_compat Hop Hor).
    apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
    apply (rngl_le_antisymm Hor) in Hzs12; [ | easy ].
    symmetry in Hzs12.
    apply (eq_rngl_sin_0) in Hzs12.
    destruct Hzs12; subst θ1; [ apply (rngl_le_refl Hor) | ].
    rewrite angle_straight_add_straight in Haov.
    exfalso.
    apply (rngl_nlt_ge Hor) in Haov.
    apply Haov; cbn.
    apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
  }
  rewrite angle_add_comm.
  apply angle_add_overflow_le_lemma_2 with (θ2 := θ1); try easy.
  now apply (rngl_lt_le_incl Hor).
  now rewrite angle_add_comm.
} {
  apply (rngl_leb_gt Hor) in Hzs2.
  destruct zs12. {
    exfalso.
    destruct zs1; [ | easy ].
    apply rngl_leb_le in Hzs1.
    apply rngl_leb_le in Hzs12.
    apply (rngl_ltb_ge Hor) in Haov.
    apply angle_add_overflow_le_lemma_6 in Haov; try easy.
  }
  apply (rngl_leb_gt Hor) in Hzs12.
  apply (rngl_ltb_ge Hor).
  destruct zs1. {
    clear Haov.
    apply rngl_leb_le in Hzs1.
    rewrite angle_add_comm.
    apply rngl_cos_le_cos_add; try easy.
    now apply (rngl_lt_le_incl Hor).
    now rewrite angle_add_comm.
  }
  apply (rngl_leb_gt Hor) in Hzs1.
  apply (rngl_ltb_ge Hor) in Haov.
  apply (rngl_nlt_ge Hor).
  intros Hc12.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    change_angle_add_r θ1 angle_right.
    progress sin_cos_add_sub_right_hyp T Haov.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_hyp T Hzc1.
    progress sin_cos_add_sub_right_hyp T Hc12.
    progress sin_cos_add_sub_right_goal T.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
      exfalso.
      change_angle_add_r θ2 angle_right.
      progress sin_cos_add_sub_right_hyp T Haov.
      progress sin_cos_add_sub_right_hyp T Hzs2.
      progress sin_cos_add_sub_right_hyp T Hzc2.
      progress sin_cos_add_sub_right_hyp T Hc12.
      apply (rngl_nlt_ge Hor) in Haov.
      apply Haov; clear Haov; cbn.
      rewrite (rngl_add_sub_assoc Hop).
      rewrite (rngl_add_sub_swap Hop).
      rewrite (rngl_sub_mul_r_diag_l Hon Hop).
      apply (rngl_add_nonneg_pos Hor).
      apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
      apply (rngl_le_0_sub Hop Hor).
      apply rngl_sin_bound.
      now apply (rngl_mul_pos_pos Hop Hor Hii).
    }
    apply (rngl_nle_gt Hor) in Hc2z.
    change_angle_add_r θ2 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Haov.
    progress sin_cos_add_sub_straight_hyp T Hzs2.
    progress sin_cos_add_sub_straight_hyp T Hc2z.
    progress sin_cos_add_sub_straight_hyp T Hc12.
    exfalso.
    apply (rngl_nlt_ge Hor) in Haov.
    apply Haov; clear Haov.
    apply (rngl_add_nonneg_pos Hor); [ easy | ].
    eapply (rngl_le_lt_trans Hor); [ | apply Hc12 ].
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  change_angle_add_r θ1 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Haov.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_hyp T Hc1z.
  progress sin_cos_add_sub_straight_hyp T Hc12.
  progress sin_cos_add_sub_straight_goal T.
  destruct (rngl_le_dec Hor (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
    cbn.
    apply (rngl_add_nonpos_nonpos Hor).
    apply (rngl_mul_nonneg_nonpos Hop Hor); [ | easy ].
    now apply (rngl_lt_le_incl Hor).
    apply (rngl_mul_nonneg_nonpos Hop Hor).
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nle_gt Hor) in Hzc2.
  change_angle_add_r θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Haov.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hzc2.
  progress sin_cos_add_sub_right_hyp T Hc12.
  progress sin_cos_add_sub_right_goal T.
  apply (rngl_nlt_ge Hor).
  intros Hc12z.
  apply (rngl_nlt_ge Hor) in Haov.
  apply Haov; clear Haov.
  change_angle_sub_l θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzc2.
  progress sin_cos_add_sub_right_hyp T Hc12.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hc12z.
  progress sin_cos_add_sub_right_goal T.
  apply (rngl_lt_iff Hor).
  split. {
    apply quadrant_1_sin_sub_nonneg_cos_le; try easy.
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor). {
      cbn.
      rewrite (rngl_mul_opp_r Hop).
      rewrite (rngl_sub_opp_r Hop).
      apply (rngl_add_nonneg_nonneg Hor).
      apply (rngl_mul_nonneg_nonneg Hop Hor).
      now apply (rngl_lt_le_incl Hor).
      now apply (rngl_lt_le_incl Hor).
      apply (rngl_mul_nonneg_nonneg Hop Hor).
      now apply (rngl_lt_le_incl Hor).
      now apply (rngl_lt_le_incl Hor).
    }
    rewrite angle_sub_sub_distr.
    rewrite angle_sub_diag.
    rewrite angle_add_0_l.
    now apply (rngl_lt_le_incl Hor).
  }
  intros H.
  apply rngl_cos_eq in H.
  destruct H as [H| H]. {
    apply angle_sub_move_l in H.
    rewrite angle_sub_diag in H.
    subst θ2.
    now apply (rngl_lt_irrefl Hor) in Hzs2.
  }
  rewrite angle_opp_sub_distr in H.
  rewrite rngl_sin_sub_anticomm in Hc12z.
  rewrite <- H in Hc12z.
  apply (rngl_opp_pos_neg Hop Hor) in Hc12z.
  apply (rngl_lt_le_incl Hor) in Hc12z.
  now apply (rngl_nlt_ge Hor) in Hc12z.
}
Qed.

Theorem angle_add_overflow_comm :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = true
  → angle_add_overflow θ2 θ1 = true.
Proof.
intros * H12.
apply Bool.not_false_iff_true in H12.
apply Bool.not_false_iff_true.
intros H; apply H12.
now apply angle_add_not_overflow_comm.
Qed.

Theorem rngl_cos_sub_nonneg :
  ∀ θ1 θ2 : angle T,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos (θ1 - θ2))%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hcs1 Hcs2.
cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
apply (rngl_add_nonneg_nonneg Hor).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
Qed.

Theorem quadrant_1_quadrant_4_cos_lt_cos_add :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_cos θ1)%L
  → (rngl_sin θ2 < 0)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos θ1 < rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Hzs1 Hzc1 Hzs2 Hzc2 Hzs12.
change_angle_opp θ2.
progress sin_cos_opp_hyp T Hzs2.
progress sin_cos_opp_hyp T Hzs12.
progress sin_cos_opp_hyp T Hzc2.
progress sin_cos_opp_goal T.
rewrite rngl_cos_sub_comm.
apply rngl_cos_lt_rngl_cos_sub; [ easy | easy | ].
apply (rngl_lt_le_incl Hor) in Hzs2.
now apply quadrant_1_sin_sub_nonneg_cos_le.
Qed.

Theorem quadrant_1_sin_sub_pos_cos_lt :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 < rngl_sin (θ1 - θ2))%L
  → (rngl_cos θ1 < rngl_cos θ2)%L.
Proof.
destruct_ac.
intros * Hs1z Hzs2 Hc1z Hzc2 Hzs12.
apply (rngl_lt_iff Hor).
split. {
  apply quadrant_1_sin_sub_nonneg_cos_le; try easy.
  now apply (rngl_lt_le_incl Hor).
}
intros H.
apply rngl_cos_eq in H.
destruct H; subst θ1. {
  rewrite angle_sub_diag in Hzs12.
  now apply (rngl_lt_irrefl Hor) in Hzs12.
}
cbn in Hs1z.
rewrite <- angle_opp_add_distr in Hzs12.
cbn - [ angle_add ] in Hzs12.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hs1z.
apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
apply eq_rngl_sin_0 in Hzs2.
destruct Hzs2; subst θ2. {
  rewrite angle_add_0_r in Hzs12.
  cbn in Hzs12.
  rewrite (rngl_opp_0 Hop) in Hzs12.
  now apply (rngl_lt_irrefl Hor) in Hzs12.
}
rewrite angle_straight_add_straight in Hzs12.
cbn in Hzs12.
rewrite (rngl_opp_0 Hop) in Hzs12.
now apply (rngl_lt_irrefl Hor) in Hzs12.
Qed.

Context {rl : real_like_prop T}.

Fixpoint angle_div_2_pow θ i :=
  match i with
  | 0 => θ
  | S i' => angle_div_2 (angle_div_2_pow θ i')
  end.

End a.

Notation "θ /₂^ n" := (angle_div_2_pow θ n)
  (at level 40, format "θ  /₂^ n") : angle_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem angle_div_2_pow_succ_r_1 :
  ∀ n θ, angle_div_2_pow θ (S n) = (angle_div_2_pow θ n /₂)%A.
Proof. easy. Qed.

Theorem angle_div_2_pow_succ_r_2 :
  ∀ n θ, angle_div_2_pow θ (S n) = angle_div_2_pow (θ /₂) n.
Proof.
intros.
induction n; intros; [ easy | ].
remember (S n) as sn; cbn; subst sn.
now rewrite IHn.
Qed.

Theorem angle_div_2_pow_add_r :
  ∀ i j θ, (θ /₂^(i + j) = θ /₂^i /₂^j)%A.
Proof.
intros.
revert j θ.
induction i; intros; [ easy | ].
rewrite Nat.add_succ_l.
do 2 rewrite angle_div_2_pow_succ_r_2.
apply IHi.
Qed.

Fixpoint angle_mul_nat_overflow n θ :=
  match n with
  | 0 | 1 => false
  | S n' =>
      (angle_add_overflow θ (n' * θ) ||
       angle_mul_nat_overflow n' θ)%bool
  end.

Theorem angle_mul_nat_overflow_succ_l_false :
  ∀ θ n,
  angle_mul_nat_overflow (S n) θ = false
  ↔ angle_mul_nat_overflow n θ = false ∧
    angle_add_overflow θ (n * θ) = false.
Proof.
intros.
split; intros Hn. {
  destruct n. {
    split; [ easy | cbn ].
    progress unfold angle_add_overflow.
    rewrite angle_add_0_r.
    apply Bool.not_true_iff_false.
    apply angle_lt_irrefl.
  }
  remember (S n) as sn; cbn in Hn; subst sn.
  now apply Bool.orb_false_iff in Hn.
} {
  destruct n; [ easy | ].
  remember (S n) as sn; cbn; subst sn.
  now apply Bool.orb_false_iff.
}
Qed.

Theorem angle_le_trans :
  ∀ θ1 θ2 θ3,
  (θ1 ≤ θ2 → θ2 ≤ θ3 → θ1 ≤ θ3)%A.
Proof.
destruct_ac.
intros * H12 H23.
progress unfold angle_leb in H12.
progress unfold angle_leb in H23.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ1)%L as z1 eqn:Hz1.
remember (0 ≤? rngl_sin θ2)%L as z2 eqn:Hz2.
remember (0 ≤? rngl_sin θ3)%L as z3 eqn:Hz3.
symmetry in Hz1, Hz2, Hz3.
destruct z1. {
  apply rngl_leb_le in Hz1.
  (* c'est bizarre, quand même : si j'avais utilisé rngl_eq_dec,
     il m'aurait fallu que "rngl_has_eq_dec T = true" soit en
     hypothèse. Tandis que là, non *)
  destruct z3; [ | easy ].
  apply rngl_leb_le.
  apply rngl_leb_le in Hz3.
  destruct z2; [ | easy ].
  apply rngl_leb_le in Hz2, H12, H23.
  now apply (rngl_le_trans Hor _ (rngl_cos θ2)).
} {
  destruct z2; [ easy | ].
  destruct z3; [ easy | ].
  apply rngl_leb_le in H12, H23.
  apply rngl_leb_le.
  now apply (rngl_le_trans Hor _ (rngl_cos θ2)).
}
Qed.

Theorem angle_le_lt_trans :
  ∀ θ1 θ2 θ3,
  (θ1 ≤ θ2 → θ2 < θ3 → θ1 < θ3)%A.
Proof.
destruct_ac.
intros * H12 H23.
progress unfold angle_leb in H12.
progress unfold angle_ltb in H23.
progress unfold angle_ltb.
remember (0 ≤? rngl_sin θ1)%L as z1 eqn:Hz1.
remember (0 ≤? rngl_sin θ2)%L as z2 eqn:Hz2.
remember (0 ≤? rngl_sin θ3)%L as z3 eqn:Hz3.
symmetry in Hz1, Hz2, Hz3.
destruct z1. {
  apply rngl_leb_le in Hz1.
  destruct z3; [ | easy ].
  apply rngl_ltb_lt.
  apply rngl_leb_le in Hz3.
  destruct z2; [ | easy ].
  apply rngl_leb_le in Hz2, H12.
  apply rngl_ltb_lt in H23.
  now apply (rngl_lt_le_trans Hor _ (rngl_cos θ2)).
} {
  destruct z2; [ easy | ].
  destruct z3; [ easy | ].
  apply rngl_leb_le in H12.
  apply rngl_ltb_lt in H23.
  apply rngl_ltb_lt.
  now apply (rngl_le_lt_trans Hor _ (rngl_cos θ2)).
}
Qed.

Theorem angle_lt_trans :
  ∀ θ1 θ2 θ3,
  (θ1 < θ2 → θ2 < θ3 → θ1 < θ3)%A.
Proof.
intros * H12 H23.
apply (angle_le_lt_trans _ θ2); [ | easy ].
now apply angle_lt_le_incl in H12.
Qed.

Theorem quadrant_1_rngl_cos_add_le_cos_l :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzc1 Hzc2.
apply rngl_cos_add_le_cos; try easy.
now right; right; left.
cbn.
apply (rngl_add_nonneg_nonneg Hor).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
Qed.

Theorem rngl_sin_incr_lt :
  ∀ θ1 θ2,
  (θ1 < θ2 ≤ angle_right)%A
  → (rngl_sin θ1 < rngl_sin θ2)%L.
Proof.
destruct_ac.
intros * (H12, H2s).
progress unfold angle_ltb in H12.
progress unfold angle_leb in H2s.
cbn in H2s.
specialize (rngl_0_le_1 Hon Hop Hor) as H1.
apply rngl_leb_le in H1.
rewrite H1 in H2s; clear H1.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs2; [ | easy ].
destruct zs1; [ | easy ].
apply rngl_leb_le in Hzs1, Hzs2, H2s.
apply rngl_ltb_lt in H12.
apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff; try easy.
apply (rngl_le_trans Hor _ (rngl_cos θ2)); [ easy | ].
now apply (rngl_lt_le_incl Hor).
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
    rewrite <- rngl_sin_sub_anticomm in Hzs12.
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
      apply quadrant_1_sin_sub_pos_cos_lt; try easy; cycle 1.
      now apply (rngl_lt_le_incl Hor) in Hzs1.
      now apply (rngl_lt_le_incl Hor) in Hzs2.
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
apply rngl_cos_le_cos_add; [ | easy | ].
now apply (rngl_lt_le_incl Hor) in Hzs12.
now rewrite angle_sub_add.
Qed.

Theorem angle_lt_sub_diag :
  ∀ θ1 θ2, (0 < θ2 < θ1)%A → (θ1 - θ2 < θ1)%A.
Proof.
intros * (Hz2, H21).
apply angle_lt_iff.
split. {
  apply angle_le_sub_diag.
  now apply angle_lt_le_incl in H21.
}
intros H.
apply angle_sub_move_l in H.
rewrite angle_sub_diag in H.
rewrite H in Hz2.
now apply angle_lt_irrefl in Hz2.
Qed.

Theorem angle_lt_eq_cases :
  ∀ θ1 θ2, (θ1 ≤ θ2)%A ↔ (θ1 < θ2)%A ∨ θ1 = θ2.
Proof.
intros.
split; intros H12. {
  remember (θ1 =? θ2)%A as e12 eqn:He12.
  symmetry in He12.
  destruct e12. {
    apply angle_eqb_eq in He12.
    now right.
  }
  left.
  apply angle_eqb_neq in He12.
  now apply angle_lt_iff.
}
destruct H12 as [H12| H12]; [ now apply angle_lt_le_incl | ].
subst θ2.
apply angle_le_refl.
Qed.

Theorem angle_eucl_dist_eq_cos_eq :
  ∀ θ1 θ2 θ3 θ4,
  (angle_eucl_dist θ1 θ2 = angle_eucl_dist θ3 θ4)%L ↔
  (rngl_cos (θ4 - θ3) = rngl_cos (θ2 - θ1))%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  do 2 rewrite (H1 (angle_eucl_dist _ _)).
  do 2 rewrite (H1 (rngl_cos _)).
  easy.
}
intros.
do 2 rewrite angle_eucl_dist_is_sqrt.
split; intros H1234; [ | now rewrite H1234 ].
apply (f_equal rngl_squ) in H1234.
rewrite (rngl_squ_sqrt Hon) in H1234. 2: {
  apply (rngl_mul_nonneg_nonneg Hop Hor).
  apply (rngl_0_le_2 Hon Hop Hor).
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
rewrite (rngl_squ_sqrt Hon) in H1234. 2: {
  apply (rngl_mul_nonneg_nonneg Hop Hor).
  apply (rngl_0_le_2 Hon Hop Hor).
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
apply (rngl_mul_cancel_l Hi1) in H1234. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
(* lemma to do *)
do 2 rewrite <- (rngl_add_opp_r Hop) in H1234.
apply (rngl_add_cancel_l Hos) in H1234.
now apply (rngl_opp_inj Hop) in H1234.
Qed.

Theorem angle_eucl_dist_lt_cos_lt :
  ∀ θ1 θ2 θ3 θ4,
  (angle_eucl_dist θ1 θ2 < angle_eucl_dist θ3 θ4)%L
  ↔ (rngl_cos (θ4 - θ3) < rngl_cos (θ2 - θ1))%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  do 2 rewrite (H1 (angle_eucl_dist _ _)).
  do 2 rewrite (H1 (rngl_cos _)).
  easy.
}
intros.
do 2 rewrite angle_eucl_dist_is_sqrt.
split; intros H1234. {
  apply (rl_sqrt_lt_sqrt Hic Hop Hiv Hon Hor) in H1234; cycle 1. {
    apply (rngl_mul_nonneg_nonneg Hop Hor).
    apply (rngl_0_le_2 Hon Hop Hor).
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  } {
    apply (rngl_mul_nonneg_nonneg Hop Hor).
    apply (rngl_0_le_2 Hon Hop Hor).
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  apply (rngl_mul_lt_mono_pos_l Hop Hor Hii) in H1234. 2: {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  now apply (rngl_sub_lt_mono_l Hop Hor) in H1234.
} {
  apply (rl_sqrt_lt_rl_sqrt Hon Hop Hor). {
    apply (rngl_mul_nonneg_nonneg Hop Hor).
    apply (rngl_0_le_2 Hon Hop Hor).
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  apply (rngl_mul_lt_mono_pos_l Hop Hor Hii). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  now apply (rngl_sub_lt_mono_l Hop Hor).
}
Qed.

Theorem angle_eucl_dist_le_cos_le :
  ∀ θ1 θ2 θ3 θ4,
  (angle_eucl_dist θ1 θ2 ≤ angle_eucl_dist θ3 θ4)%L
  ↔ (rngl_cos (θ4 - θ3) ≤ rngl_cos (θ2 - θ1))%L.
Proof.
destruct_ac.
intros.
split; intros H1234. {
  apply (rngl_lt_eq_cases Hor) in H1234.
  apply (rngl_lt_eq_cases Hor).
  destruct H1234 as [H| H]. {
    now apply angle_eucl_dist_lt_cos_lt in H; left.
  } {
    now apply angle_eucl_dist_eq_cos_eq in H; right.
  }
} {
  apply (rngl_lt_eq_cases Hor) in H1234.
  apply (rngl_lt_eq_cases Hor).
  destruct H1234 as [H| H]. {
    now left; apply angle_eucl_dist_lt_cos_lt.
  } {
    now right; apply angle_eucl_dist_eq_cos_eq in H.
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

Theorem angle_add_straight_r_not_overflow :
  ∀ θ, (θ < angle_straight)%A → angle_add_overflow θ angle_straight = false.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
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
rewrite (rngl_leb_0_opp Hop Hor).
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

Theorem angle_le_add_r :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → (θ1 ≤ θ1 + θ2)%A.
Proof.
intros * Haov.
progress unfold angle_add_overflow in Haov.
apply Bool.not_true_iff_false in Haov.
now apply angle_nlt_ge in Haov.
Qed.

Definition angle_lim :=
  is_limit_when_tending_to_inf angle_eucl_dist.

End a.
