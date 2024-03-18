Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Init.Nat.
Require Import Main.RingLike.
Require Import TrigoWithoutPi AngleLeSubAdd.
Require Import AngleAddOverflowEquiv3.
Require Import TacChangeAngle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

Theorem angle_add_overflow_le_lemma_1 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ2 ≤ rngl_cos θ3)%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos θ1)%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzs1 Hzs2 Hzs3 Hzs12 Hzs13 H32 H12.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Hzs1 Hzs2 Hzs3 Hzs12 Hzs13 H32 H12.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  cbn.
  apply (rngl_le_sub_le_add_r Hop Hor).
  eapply (rngl_le_trans Hor). 2: {
    apply (rngl_le_add_r Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
  }
  apply (rngl_le_0_sub Hop Hor).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
apply (rngl_nle_gt Hor) in Hc1z.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_hyp T H12.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_le_dec Hor (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
  change_angle_sub_r θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T H32.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hc2z.
  progress sin_cos_add_sub_right_hyp T H12.
  apply (rngl_nlt_ge Hor).
  intros Hs13.
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  apply (rngl_lt_iff Hor).
  split. {
    cbn.
    apply (rngl_add_nonneg_nonneg Hor).
    apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
  }
  intros Hs12.
  symmetry in Hs12.
  apply eq_rngl_sin_0 in Hs12.
  destruct Hs12 as [Hs12| Hs12]. {
    apply angle_add_move_l in Hs12.
    rewrite angle_sub_0_l in Hs12.
    subst θ2.
    cbn in Hc2z.
    apply (rngl_opp_nonneg_nonpos Hop Hor) in Hc2z.
    now apply (rngl_nlt_ge Hor) in Hc2z.
  }
  apply angle_add_move_l in Hs12.
  subst θ2.
  rewrite rngl_cos_sub_straight_l in Hzs2.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs2.
  apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
  symmetry in Hzs2.
  apply eq_rngl_cos_0 in Hzs2.
  destruct Hzs2; subst θ1. {
    rewrite angle_straight_sub_right in H12.
    rewrite (angle_right_add_right Hon Hop) in H12.
    apply (rngl_nlt_ge Hor) in H12.
    apply H12; cbn.
    apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  apply Hc1z; cbn.
  apply (rngl_opp_1_le_0 Hon Hop Hor).
}
apply (rngl_nle_gt Hor) in Hzc2.
apply rngl_sin_sub_nonneg_sin_le_sin; try easy. {
  cbn.
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor).
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_trans Hor _ (rngl_cos θ2)).
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
} {
  rewrite angle_add_sub_swap.
  rewrite angle_sub_diag.
  now rewrite angle_add_0_l.
}
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

Theorem angle_add_overflow_le_lemma_3 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ2 ≤ rngl_cos θ3)%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs3 Hzs12 Hzs13 H32.
destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hc1z| Hzc1]. {
  destruct (rngl_eq_dec Hed (rngl_cos θ1) (-1)) as [Hc1o| Hc1o]. {
    apply eq_rngl_cos_opp_1 in Hc1o.
    subst θ1.
    rewrite (rngl_sin_add_straight_l Hon Hop) in Hzs12, Hzs13.
    rewrite (rngl_cos_add_straight_l Hon Hop).
    apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs13.
    apply (rngl_opp_neg_pos Hop Hor) in Hzs12.
    apply (rngl_le_antisymm Hor) in Hzs13; [ | easy ].
    symmetry in Hzs13.
    apply -> (rngl_opp_le_compat Hop Hor).
    apply eq_rngl_sin_0 in Hzs13.
    destruct Hzs13; subst θ3; [ apply (rngl_le_refl Hor) | ].
    cbn in H32.
    specialize (rngl_cos_bound θ2) as H1.
    apply (rngl_le_antisymm Hor) in H32; [ | easy ].
    clear H1.
    symmetry in H32.
    apply eq_rngl_cos_opp_1 in H32.
    subst θ2.
    now apply (rngl_lt_irrefl Hor) in Hzs12.
  }
  now apply angle_add_overflow_le_lemma_2.
}
apply (rngl_nle_gt Hor) in Hzc1.
move Hzc1 before Hzs3.
destruct (rngl_le_dec Hor (rngl_cos θ3) 0) as [Hc3z| Hzc3]. {
  eapply (rngl_le_trans Hor); [ | apply (rngl_lt_le_incl Hor), Hzc1 ].
  cbn.
  progress unfold rngl_sub.
  rewrite Hop.
  apply (rngl_add_nonpos_nonpos Hor).
  apply (rngl_mul_nonneg_nonpos Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_opp_nonpos_nonneg Hop Hor).
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
}
apply (rngl_nle_gt Hor) in Hzc3.
move Hzc3 before Hzc1.
apply angle_le_sub_le_add_l_lemma_1; try easy. {
  now apply (rngl_lt_le_incl Hor).
} {
  rewrite angle_sub_diag.
  apply rngl_cos_bound.
}
rewrite angle_sub_diag.
apply (rngl_le_refl Hor).
Qed.

Theorem angle_add_overflow_le_lemma_4 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (rngl_sin θ2 < 0)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos θ1)%L.
Proof.
destruct_ac.
intros * Hzs1 Hzs2 Hzs3 Hzs12 Hzs13.
destruct (rngl_eq_dec Hed (rngl_cos θ1) (-1)) as [Hc1o| Hc1o]. {
  apply eq_rngl_cos_opp_1 in Hc1o.
  subst θ1.
  rewrite (rngl_sin_add_straight_l Hon Hop) in Hzs13.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs13.
  apply (rngl_le_antisymm Hor) in Hzs13; [ | easy ].
  symmetry in Hzs13.
  apply eq_rngl_sin_0 in Hzs13.
  destruct Hzs13; subst θ3. {
    rewrite (rngl_cos_add_straight_l Hon Hop).
    apply (rngl_le_refl Hor).
  }
  rewrite (rngl_sin_add_straight_l Hon Hop) in Hzs12.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs12.
  apply (rngl_lt_le_incl Hor) in Hzs12.
  now apply (rngl_nlt_ge Hor) in Hzs12.
}
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
  apply angle_le_sub_le_add_l_lemma_1; try easy. {
    rewrite angle_sub_diag.
    apply rngl_cos_bound.
  } {
    rewrite angle_sub_diag.
    apply (rngl_le_refl Hor).
  }
}
apply (rngl_nle_gt Hor) in Hzc1.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hzc1.
progress sin_cos_add_sub_right_hyp T Hc1o.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_goal T.
assert (H : (rngl_sin θ1 ≠ 1)%L) by now intros H; apply Hc1o; f_equal.
move H before Hc1o; clear Hc1o; rename H into Hs11.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
  change_angle_add_r θ2 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs2.
  progress sin_cos_add_sub_right_hyp T Hzc2.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  exfalso.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12; cbn.
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
}
apply (rngl_nle_gt Hor) in Hzc2.
change_angle_add_r θ2 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs2.
progress sin_cos_add_sub_straight_hyp T Hzc2.
progress sin_cos_add_sub_straight_hyp T Hzs12.
destruct (rngl_le_dec Hor (rngl_cos θ3) 0) as [Hc3z| Hzc3]. {
  change_angle_sub_r θ3 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs3.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T Hc3z.
  progress sin_cos_add_sub_right_goal T.
  apply (rngl_nlt_ge Hor).
  intros Hc31.
  apply (rngl_nlt_ge Hor) in Hzs13.
  apply Hzs13; clear Hzs13.
  apply (rngl_lt_iff Hor).
  split. {
    cbn.
    apply (rngl_add_nonneg_nonneg Hor).
    apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
  }
  intros H; symmetry in H.
  apply eq_rngl_sin_0 in H.
  destruct H as [H| H]. {
    rewrite H in Hc31.
    apply (rngl_nle_gt Hor) in Hc31.
    apply Hc31; clear Hc31; cbn.
    apply rngl_sin_bound.
  }
  apply angle_add_move_l in H.
  subst θ3.
  clear Hc3z.
  rewrite rngl_cos_sub_straight_l in Hzs3.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs3.
  apply (rngl_le_antisymm Hor) in Hzs3; [ | easy ].
  symmetry in Hzs3.
  apply eq_rngl_cos_0 in Hzs3.
  destruct Hzs3; subst θ1; [ easy | ].
  apply (rngl_nle_gt Hor) in Hzc1.
  apply Hzc1; cbn.
  apply (rngl_opp_1_le_0 Hon Hop Hor).
}
apply (rngl_nle_gt Hor) in Hzc3.
move Hzc3 before Hzc2.
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy. {
  now apply (rngl_lt_le_incl Hor).
} {
  cbn.
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
}
apply angle_le_sub_le_add_l_lemma_1; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
rewrite angle_sub_diag.
apply rngl_cos_bound.
rewrite angle_sub_diag.
apply (rngl_le_refl Hor).
cbn.
apply (rngl_add_nonneg_nonneg Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor).
now apply (rngl_lt_le_incl Hor).
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
  destruct (rngl_eq_dec Hed (rngl_cos θ1) (rngl_cos θ2)) as [Hc1c2| Hc1c2]. {
    apply rngl_cos_eq in Hc1c2.
    destruct Hc1c2; subst θ1. {
      rewrite angle_sub_diag; cbn.
      apply (rngl_lt_iff Hor).
      split; [ apply rngl_cos_bound | easy ].
    }
    cbn in Hzs1, Hzc1.
    rewrite (angle_sub_opp_r Hop).
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
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzs1 Hzs2 Hzs12 H12.
  rewrite (H1 (rngl_sin _)) in Hzs2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
intros * Hzs1 Hzs2 Hzs12 H12.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
  destruct (rngl_eq_dec Hed (rngl_cos θ1) 1) as [H| H]. {
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
  destruct (rngl_eq_dec Hed (rngl_cos θ2) 1) as [Hc21| Hc21]. {
    apply eq_rngl_cos_1 in Hc21.
    subst θ2.
    now apply (rngl_lt_irrefl Hor) in Hzs2.
  }
  destruct (rngl_eq_dec Hed (rngl_cos θ1) 0) as [Hc1z| Hc1z]. {
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
destruct (rngl_eq_dec Hed (rngl_sin θ1) 0) as [Hs1z| Hs1z]. {
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

Theorem angle_add_overflow_le_lemma_7 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 < rngl_sin θ2)%L
  → (rngl_sin θ3 < 0)%L
  → (0 < rngl_cos θ1)%L
  → (0 < rngl_cos θ2)%L
  → (0 ≤ rngl_cos θ3)%L
  → (0 < rngl_cos (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ3 ≤ rngl_sin θ2)%L
  → False.
Proof.
destruct_ac.
intros * Hzs1 Hzc2 Hzs3 Hzc1 Hzs2 Hzc3 Hzs12 Hzs13 H32.
change_angle_opp θ3.
sin_cos_opp_hyp T Hzs3.
sin_cos_opp_hyp T Hzc3.
sin_cos_opp_hyp T H32.
sin_cos_opp_hyp T Hzs13.
change_angle_sub_l θ2 angle_right.
sin_cos_add_sub_right_hyp T Hzc2.
sin_cos_add_sub_right_hyp T Hzs2.
sin_cos_add_sub_right_hyp T H32.
sin_cos_add_sub_right_hyp T Hzs12.
rewrite rngl_sin_sub_anticomm in Hzs12.
sin_cos_add_sub_right_hyp T Hzs12.
apply (rngl_nlt_ge Hor) in H32.
apply H32; clear H32.
apply (rngl_lt_iff Hor).
split. 2: {
  intros H.
  apply rngl_cos_eq in H.
  destruct H; subst θ2. {
    rewrite rngl_sin_sub_anticomm in Hzs12.
    apply (rngl_opp_pos_neg Hop Hor) in Hzs12.
    now apply (rngl_nle_gt Hor) in Hzs12.
  }
  cbn in Hzs2.
  apply (rngl_opp_pos_neg Hop Hor) in Hzs2.
  apply (rngl_lt_le_incl Hor) in Hzs2.
  now apply (rngl_nlt_ge Hor) in Hzs2.
}
apply rngl_sin_sub_nonneg_sin_le_sin in Hzs13; try easy.
2: now apply (rngl_lt_le_incl Hor).
apply (rngl_lt_le_incl Hor) in Hzs12.
apply rngl_sin_sub_nonneg_sin_le_sin in Hzs12; try easy; cycle 1.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_le_trans Hor _ (rngl_sin θ1)).
Qed.

Theorem angle_add_overflow_le_lemma_8 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (rngl_sin θ2 < 0)%L
  → (rngl_sin θ3 < 0)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → False.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hzs1 Hzs2 Hzs3 Hzs12 Hzs13 H32.
destruct (rngl_le_dec Hor (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
  change_angle_add_r θ2 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T Hc2z.
  progress sin_cos_add_sub_straight_hyp T H32.
  destruct (rngl_lt_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
    apply (rngl_nlt_ge Hor) in H32.
    apply H32; clear H32.
    now apply (rngl_add_pos_nonneg Hor).
  }
  apply (rngl_nlt_ge Hor) in Hc3z.
  change_angle_add_r θ3 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzs3.
  progress sin_cos_add_sub_straight_hyp T Hzs13.
  progress sin_cos_add_sub_straight_hyp T Hc3z.
  progress sin_cos_add_sub_straight_hyp T H32.
  rewrite rngl_add_comm in H32.
  rewrite (rngl_add_opp_r Hop) in H32.
  apply -> (rngl_le_sub_0 Hop Hor) in H32.
  destruct (rngl_lt_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    apply (rngl_nlt_ge Hor) in Hzs13.
    apply Hzs13; clear Hzs13; cbn.
    apply (rngl_add_nonneg_pos Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
    now apply (rngl_mul_pos_pos Hop Hor Hii).
  }
  apply (rngl_nlt_ge Hor) in Hc1z.
  change_angle_sub_r θ1 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hc1z.
  apply (rngl_nlt_ge Hor) in Hzs13.
  apply Hzs13; clear Hzs13.
  eapply (rngl_lt_le_trans Hor); [ apply Hzs12 | ].
  apply angle_le_sub_le_add_l_lemma_1; try easy. {
    cbn.
    apply (rngl_add_nonneg_nonneg Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
    apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
    now apply (rngl_lt_le_incl Hor).
  } {
    now apply (rngl_lt_le_incl Hor).
  } {
    rewrite angle_add_comm.
    now rewrite angle_add_sub.
  } {
    rewrite angle_add_comm.
    rewrite angle_add_sub.
    now apply (rngl_lt_le_incl Hor).
  } {
    cbn.
    apply (rngl_add_nonneg_nonneg Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
    apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
    now apply (rngl_lt_le_incl Hor).
  }
}
apply (rngl_nle_gt Hor) in Hzc2.
change_angle_add_r θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hzc2.
progress sin_cos_add_sub_right_hyp T H32.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
    now apply (angle_add_overflow_le_lemma_7 θ1 θ2 θ3).
  }
  apply (rngl_nle_gt Hor) in Hc3z.
  change_angle_add_r θ3 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzs3.
  progress sin_cos_add_sub_straight_hyp T Hzs13.
  progress sin_cos_add_sub_straight_hyp T H32.
  progress sin_cos_add_sub_straight_hyp T Hc3z.
  apply (rngl_nlt_ge Hor) in Hzs13.
  apply Hzs13; clear Hzs13; cbn.
  apply (rngl_add_nonneg_pos Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_mul_pos_pos Hop Hor).
}
apply (rngl_nlt_ge Hor) in Hc1z.
move Hc1z after Hzs2.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzs12.
apply (rngl_nle_gt Hor) in Hzs12.
apply Hzs12; clear Hzs12; cbn.
apply (rngl_add_nonneg_nonneg Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
now apply (rngl_lt_le_incl Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_add_overflow_le_lemma_9 :
  ∀ θ1 θ2 θ3,
  (rngl_sin θ1 < 0)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ2 ≤ rngl_cos θ3)%L
  → False.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hzs1 Hzs2 Hzs3 Hzs12 Hzs13 H32.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  change_angle_add_r θ1 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_hyp T Hzs13.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  progress sin_cos_add_sub_right_hyp T Hzc1.
  destruct (rngl_le_dec Hor (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
    change_angle_sub_r θ2 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs2.
    progress sin_cos_add_sub_right_hyp T H32.
    progress sin_cos_add_sub_right_hyp T Hzs12.
    progress sin_cos_add_sub_right_hyp T Hc2z.
    apply (rngl_nle_gt Hor) in Hzs12.
    apply Hzs12; clear Hzs12; cbn.
    apply (rngl_add_nonneg_nonneg Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
    apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nle_gt Hor) in Hzc2.
  move Hzc2 before Hzs1.
  destruct (rngl_le_dec Hor (rngl_cos θ3) 0) as [Hc3z| Hzc3]. {
    apply (rngl_nlt_ge Hor) in Hc3z.
    apply Hc3z.
    now apply (rngl_lt_le_trans Hor _ (rngl_cos θ2)).
  }
  apply (rngl_nle_gt Hor) in Hzc3.
  move Hzc3 before Hzc2.
  apply (rngl_nlt_ge Hor) in Hzs13.
  apply Hzs13; clear Hzs13.
  eapply (rngl_lt_le_trans Hor); [ apply Hzs12 | ].
  specialize rngl_sin_nonneg_cos_le_sin_le as H1.
  specialize (H1 θ2 θ3 Hzs2 Hzs3 H32).
  generalize Hzc2; intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply rngl_leb_le in H.
  rewrite H in H1; clear H.
  cbn.
  apply (rngl_sub_le_compat Hop Hor).
  apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_mul_le_mono_nonneg_l Hop Hor).
}
apply (rngl_nle_gt Hor) in Hc1z.
change_angle_add_r θ1 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs1.
progress sin_cos_add_sub_straight_hyp T Hzs13.
progress sin_cos_add_sub_straight_hyp T Hzs12.
progress sin_cos_add_sub_straight_hyp T Hc1z.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
  apply (rngl_nlt_ge Hor) in Hzs13.
  apply Hzs13; clear Hzs13; cbn.
  apply (rngl_add_pos_nonneg Hor).
  now apply (rngl_mul_pos_pos Hop Hor Hii).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nlt_ge Hor) in Hc3z.
change_angle_sub_r θ3 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs13.
progress sin_cos_add_sub_right_hyp T Hzs3.
progress sin_cos_add_sub_right_hyp T H32.
progress sin_cos_add_sub_right_hyp T Hc3z.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  apply (rngl_nlt_ge Hor) in H32.
  apply H32; clear H32.
  now apply (rngl_add_pos_nonneg Hor).
}
apply (rngl_nlt_ge Hor) in Hc2z.
change_angle_sub_r θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs2.
progress sin_cos_add_sub_right_hyp T H32.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hc2z.
apply (rngl_nlt_ge Hor) in Hzs13.
apply Hzs13; clear Hzs13.
eapply (rngl_lt_le_trans Hor); [ apply Hzs12 | ].
specialize rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff as H1.
specialize (H1 θ3 θ2 Hc3z Hc2z Hzs3 Hzs2).
specialize (proj1 H1 H32) as H23; clear H1.
cbn.
apply (rngl_sub_le_compat Hop Hor).
apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ | easy ].
now apply (rngl_lt_le_incl Hor).
apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ | easy ].
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_add_overflow_le_lemma_10 :
  ∀ θ1 θ2,
  (rngl_sin θ1 < 0)%L
  → (rngl_sin θ2 < 0)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (rngl_cos θ1 ≤ rngl_cos (θ1 + θ2))%L
  → False.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hzs1 Hzs2 Hzs12 H12.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  change_angle_add_r θ1 angle_right.
  progress sin_cos_add_sub_right_hyp T Hzs1.
  progress sin_cos_add_sub_right_hyp T Hzc1.
  progress sin_cos_add_sub_right_hyp T H12.
  progress sin_cos_add_sub_right_hyp T Hzs12.
  destruct (rngl_le_dec Hor (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
    change_angle_add_r θ2 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hzs2.
    progress sin_cos_add_sub_straight_hyp T Hc2z.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T H12.
    apply (rngl_nlt_ge Hor) in H12.
    apply H12; clear H12.
    apply (rngl_add_nonneg_pos Hor); [ easy | cbn ].
    apply (rngl_add_nonneg_pos Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
    now apply (rngl_mul_pos_pos Hop Hor Hii).
  }
  apply (rngl_nle_gt Hor) in Hzc2.
  change_angle_opp θ2.
  progress sin_cos_opp_hyp T Hzs2.
  progress sin_cos_opp_hyp T Hzc2.
  progress sin_cos_opp_hyp T Hzs12.
  progress sin_cos_opp_hyp T H12.
  apply (rngl_nlt_ge Hor) in H12.
  apply H12; clear H12.
  now apply rngl_sin_sub_lt_sin_l.
}
apply (rngl_nle_gt Hor) in Hc1z.
change_angle_add_r θ1 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hzs1.
progress sin_cos_add_sub_straight_hyp T Hc1z.
progress sin_cos_add_sub_straight_hyp T H12.
progress sin_cos_add_sub_straight_hyp T Hzs12.
rewrite rngl_add_comm in H12.
rewrite (rngl_add_opp_r Hop) in H12.
apply -> (rngl_le_sub_0 Hop Hor) in H12.
destruct (rngl_le_dec Hor (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
  change_angle_add_r θ2 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzs2.
  progress sin_cos_add_sub_straight_hyp T Hc2z.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T H12.
  apply -> (rngl_le_opp_l Hop Hor) in H12.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12; cbn.
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hzc2.
change_angle_opp θ2.
progress sin_cos_opp_hyp T Hzs2.
progress sin_cos_opp_hyp T Hzc2.
progress sin_cos_opp_hyp T Hzs12.
progress sin_cos_opp_hyp T H12.
apply (rngl_nlt_ge Hor) in H12.
apply H12; clear H12.
rewrite rngl_cos_sub_comm.
apply rngl_cos_lt_rngl_cos_sub; try easy.
now apply (rngl_lt_le_incl Hor).
apply quadrant_1_sin_sub_nonneg_cos_le; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
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
apply angle_add_overflow_le_lemma_111; try easy.
now right; right; left.
cbn.
apply (rngl_add_nonneg_nonneg Hor).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
Qed.

Theorem angle_add_overflow_le :
  ∀ θ1 θ2 θ3,
  (θ3 ≤ θ2)%A
  → angle_add_overflow θ1 θ2 = false
  → angle_add_overflow θ1 θ3 = false.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * H32 H12.
  progress unfold angle_add_overflow.
  apply angle_ltb_ge.
  progress unfold angle_leb.
  rewrite (H1 (rngl_sin θ1)).
  rewrite (rngl_leb_refl Hor).
  rewrite (H1 (rngl_sin (θ1 + θ3))).
  rewrite (rngl_leb_refl Hor).
  apply rngl_leb_le.
  rewrite H1.
  rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * H32 H12.
generalize H12; intros Haov.
progress unfold angle_add_overflow in H12.
progress unfold angle_add_overflow.
apply angle_ltb_ge in H12.
apply angle_ltb_ge.
progress unfold angle_leb in H32.
progress unfold angle_leb in H12.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin θ3)%L as zs3 eqn:Hzs3.
remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
remember (0 ≤? rngl_sin (θ1 + θ3))%L as zs13 eqn:Hzs13.
symmetry in Hzs1, Hzs2, Hzs3, Hzs12, Hzs13.
move Hzs1 after Hzs2.
move Hzs12 before Hzs3; move Hzs13 before Hzs12.
destruct zs1. {
  apply rngl_leb_le in Hzs1.
  destruct zs13; [ | easy ].
  apply rngl_leb_le in Hzs13.
  apply rngl_leb_le.
  destruct zs3. {
    apply rngl_leb_le in Hzs3.
    destruct zs2. {
      apply rngl_leb_le in Hzs2.
      apply rngl_leb_le in H32.
      destruct zs12. {
        apply rngl_leb_le in Hzs12.
        apply rngl_leb_le in H12.
        now apply angle_add_overflow_le_lemma_1 with (θ2 := θ2).
      } {
        clear H12.
        apply (rngl_leb_gt Hor) in Hzs12.
        now apply angle_add_overflow_le_lemma_3 with (θ2 := θ2).
      }
    } {
      clear H32.
      destruct zs12. {
        exfalso.
        apply rngl_leb_le in Hzs12, H12.
        apply (rngl_leb_gt Hor) in Hzs2.
        clear - Hzs12 H12 Hzs2 Hor ac Hzs1 Haov.
        apply (rngl_nle_gt Hor) in Hzs2.
        apply Hzs2; clear Hzs2.
        specialize (rngl_sin_nonneg_add_nonneg θ1 θ2 Hzs1 Hzs12) as H1.
        now rewrite Haov in H1.
      }
      clear H12.
      apply (rngl_leb_gt Hor) in Hzs2, Hzs12.
      now apply angle_add_overflow_le_lemma_4 with (θ2 := θ2).
    }
  } {
    exfalso.
    apply (rngl_leb_gt Hor) in Hzs3.
    destruct zs2; [ easy | ].
    apply  (rngl_leb_gt Hor) in Hzs2.
    apply rngl_leb_le in H32.
    destruct zs12. {
      apply rngl_leb_le in Hzs12.
      apply rngl_leb_le in H12.
      now apply angle_add_overflow_le_lemma_6 in H12.
    }
    clear H12.
    apply (rngl_leb_gt Hor) in Hzs12.
    now apply (angle_add_overflow_le_lemma_8 θ1 θ2 θ3).
  }
}
destruct zs12; [ easy | ].
apply (rngl_leb_gt Hor) in Hzs1, Hzs12.
apply rngl_leb_le in H12.
destruct zs13. {
  exfalso.
  apply rngl_leb_le in Hzs13.
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    destruct zs3; [ | easy ].
    apply rngl_leb_le in Hzs3, H32.
    now apply (angle_add_overflow_le_lemma_9 θ1 θ2 θ3).
  } {
    apply (rngl_leb_gt Hor) in Hzs2.
    specialize angle_add_overflow_le_lemma_10 as H1.
    apply (H1 θ1 θ2 Hzs1 Hzs2 Hzs12 H12).
  }
}
apply (rngl_leb_gt Hor) in Hzs13.
apply rngl_leb_le.
destruct zs3. {
  apply rngl_leb_le in Hzs3.
  apply (rngl_lt_le_incl Hor) in Hzs1.
  now apply angle_add_overflow_le_lemma_11.
}
destruct zs2; [ easy | ].
apply (rngl_leb_gt Hor) in Hzs2, Hzs3.
apply rngl_leb_le in H32.
apply angle_add_overflow_le_lemma_10 in H12; try easy.
Qed.

(*
Theorem angle_add_overflow_lt_le :
  ∀ θ θ1 θ2,
  (θ1 < θ)%A
  → (θ2 ≤ -θ)%A
  → angle_add_overflow θ1 θ2 = false.
Proof.
destruct_ac.
intros * H1 H2.
apply angle_add_not_overflow_equiv3.
progress unfold angle_add_not_overflow3.
destruct (angle_eq_dec θ2 0) as [H2z| H2z]; [ now left | right ].
apply (angle_lt_le_trans _ θ); [ easy | ].
(* lemma? *)
progress unfold angle_leb in H2.
progress unfold angle_leb.
cbn in H2 |-*.
rewrite (rngl_leb_opp_r Hop Hor) in H2.
rewrite (rngl_opp_0 Hop) in H2.
rewrite (rngl_leb_opp_r Hop Hor).
rewrite (rngl_opp_0 Hop).
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
remember (rngl_sin θ2 ≤? 0)%L as sz2 eqn:Hsz2.
remember (rngl_sin θ ≤? 0)%L as sz eqn:Hsz.
symmetry in Hzs2, Hzs, Hsz2, Hsz.
destruct zs. {
  destruct sz2; [ | easy ].
  destruct zs2; [ | now destruct sz ].
  apply rngl_leb_le in Hzs2, Hzs, Hsz2.
  apply rngl_leb_le.
  apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
  apply eq_rngl_sin_0 in Hzs2.
  destruct Hzs2; [ easy | subst θ2 ].
  apply rngl_cos_bound.
}
destruct zs2. 2: {
  destruct sz; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzs2, Hsz, Hzs.
  now apply (rngl_lt_asymm Hor) in Hzs.
}
apply rngl_leb_le in Hzs2.
apply (rngl_leb_gt Hor) in Hzs.
destruct sz. {
  destruct sz2; [ exfalso | easy ].
  apply rngl_leb_le in Hsz, H2, Hsz2.
  apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
  apply eq_rngl_sin_0 in Hzs2.
  destruct Hzs2; [ easy | subst θ2 ].
  apply (rngl_nlt_ge Hor) in H2.
  apply H2; clear H2.
  apply (rngl_lt_iff Hor).
  split; [ apply rngl_cos_bound | ].
  cbn; intros Hcc.
  symmetry in Hcc.
  apply eq_rngl_cos_opp_1 in Hcc.
  subst θ.
  now apply (rngl_lt_irrefl Hor) in Hzs.
}
clear H2.
destruct sz2. {
  exfalso.
  apply rngl_leb_le in Hsz2.
  apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
  apply eq_rngl_sin_0 in Hzs2.
  destruct Hzs2; [ easy | subst θ2 ].
  apply (rngl_leb_gt Hor) in Hsz.
  now apply (rngl_lt_asymm Hor) in Hzs.
}
apply (rngl_leb_gt Hor) in Hsz.
now apply (rngl_lt_asymm Hor) in Hzs.
Qed.
*)

Theorem angle_add_overflow_lt_straight_le_straight :
  ∀ θ1 θ2,
  (θ1 < angle_straight)%A
  → (θ2 ≤ angle_straight)%A
  → angle_add_overflow θ1 θ2 = false.
Proof.
destruct_ac.
intros * H1 H2.
progress unfold angle_add_overflow.
progress unfold angle_ltb.
progress unfold angle_ltb in H1.
progress unfold angle_leb in H2.
cbn in H1, H2.
rewrite (rngl_leb_refl Hor) in H1.
rewrite (rngl_leb_refl Hor) in H2.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
symmetry in Hzs1, Hzs2, Hzs12.
destruct zs1; [ | easy ].
destruct zs2; [ | easy ].
destruct zs12; [ | easy ].
apply rngl_ltb_lt in H1.
clear H2.
apply rngl_leb_le in Hzs1.
apply rngl_leb_le in Hzs2.
apply rngl_leb_le in Hzs12.
apply (rngl_ltb_ge Hor).
remember (0 ≤? rngl_cos θ1)%L as zc1 eqn:Hzc1.
symmetry in Hzc1.
destruct zc1. {
  apply rngl_leb_le in Hzc1.
  apply angle_add_overflow_le_lemma_111; try easy.
  now right; right; left.
}
apply (rngl_leb_gt Hor) in Hzc1.
apply angle_add_overflow_le_lemma_2; try easy. 2: {
  now apply (rngl_lt_le_incl Hor).
}
intros H.
apply (eq_rngl_cos_opp_1) in H.
subst θ1.
now apply (rngl_lt_irrefl Hor) in H1.
Qed.

End a.
