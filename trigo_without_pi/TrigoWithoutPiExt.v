Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.Misc Main.RingLike.
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

Theorem rngl_acos_prop :
  ∀ x, (x² ≤ 1)%L → cos2_sin2_prop x √(1 - x²)%L.
Proof.
destruct_ac.
intros * Hx1.
progress unfold cos2_sin2_prop.
rewrite Hon, Hop, Hic, Hed; cbn.
apply (rngl_eqb_eq Hed).
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_le_add_le_sub_r Hop Hor).
  now rewrite rngl_add_0_l.
}
rewrite rngl_add_comm.
apply (rngl_sub_add Hop).
Qed.

Definition rngl_acos (x : T) :=
  match (rngl_le_dec ac_or x² 1)%L with
  | left Hx1 =>
      {| rngl_cos := x; rngl_sin := √(1 - x²)%L;
         rngl_cos2_sin2 := rngl_acos_prop x Hx1 |}
  | _ =>
      angle_zero
  end.

Arguments rngl_acos x%_L.

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

Definition angle_lim := is_limit_when_tending_to_inf angle_eucl_dist.

Definition seq_angle_to_div_nat θ (n i : nat) := (2 ^ i / n * (θ /₂^i))%A.

(*
Definition seq_angle_to_mul θ (x : T) (i : nat) :=
  (x * rngl_of_nat (2 ^ i) * (θ /₂^i))%A.
*)

Theorem angle_eucl_dist_opp_opp :
  ∀ θ1 θ2, angle_eucl_dist (- θ1) (- θ2) = angle_eucl_dist θ1 θ2.
Proof.
destruct_ac.
intros.
progress unfold angle_eucl_dist.
cbn.
f_equal.
f_equal.
rewrite (rngl_sub_opp_r Hop).
rewrite rngl_add_comm.
rewrite (rngl_add_opp_r Hop).
rewrite <- (rngl_opp_sub_distr Hop).
apply (rngl_squ_opp Hop).
Qed.

Theorem angle_eucl_dist_sub_l_diag :
  ∀ θ Δθ, angle_eucl_dist (θ - Δθ) θ = angle_eucl_dist Δθ 0.
Proof.
destruct_ac.
intros.
progress unfold angle_eucl_dist.
remember (θ - Δθ)%A as x; cbn; subst x.
do 4 rewrite (rngl_squ_sub Hop Hic Hon).
rewrite (rngl_squ_1 Hon).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_squ_0 Hos).
rewrite (rngl_mul_0_r Hos).
rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_diag Hos).
rewrite rngl_add_0_l.
rewrite rngl_add_assoc.
rewrite (rngl_add_sub_assoc Hop).
rewrite rngl_add_add_swap.
rewrite <- (rngl_add_sub_swap Hop (rngl_cos θ)²)%L.
rewrite cos2_sin2_1.
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- rngl_add_assoc.
rewrite cos2_sin2_1.
rewrite <- (rngl_add_sub_swap Hop 1)%L.
do 2 rewrite <- rngl_mul_assoc.
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite <- (rngl_sub_add_distr Hos).
remember (θ - Δθ)%A as x.
replace (_ * _ + _ * _)%L with (rngl_cos (θ - x))%A. 2: {
  cbn.
  rewrite (rngl_mul_opp_r Hop).
  now rewrite rngl_sub_opp_r.
}
subst x.
rewrite angle_sub_sub_distr.
rewrite angle_sub_diag.
rewrite angle_add_0_l.
rewrite <- rngl_add_assoc.
rewrite cos2_sin2_1.
rewrite <- (rngl_add_sub_swap Hop).
now rewrite (rngl_sub_mul_r_diag_l Hon Hop).
Qed.

Theorem angle_eucl_dist_move_0_l :
  ∀ θ1 θ2, angle_eucl_dist θ1 θ2 = angle_eucl_dist (θ2 - θ1) 0.
Proof.
destruct_ac.
intros.
replace θ1 with (θ2 - (θ2 - θ1))%A. 2: {
  rewrite angle_sub_sub_distr.
  rewrite angle_sub_diag.
  apply angle_add_0_l.
}
rewrite angle_eucl_dist_sub_l_diag.
rewrite angle_sub_sub_distr.
rewrite angle_sub_diag.
f_equal; symmetry.
apply angle_add_0_l.
Qed.

Theorem angle_eucl_dist_move_0_r :
  ∀ θ1 θ2, angle_eucl_dist θ1 θ2 = angle_eucl_dist (θ1 - θ2) 0.
Proof.
destruct_ac.
intros.
rewrite angle_eucl_dist_move_0_l.
rewrite <- angle_eucl_dist_opp_opp.
rewrite angle_opp_0.
f_equal.
apply angle_opp_sub_distr.
Qed.

Theorem angle_eucl_dist_cos_sin :
  ∀ θ, ((angle_eucl_dist θ 0)² = (1 - rngl_cos θ)² + (rngl_sin θ)²)%L.
Proof.
destruct_ac.
intros.
progress unfold angle_eucl_dist; cbn.
rewrite (rngl_sub_0_l Hop).
rewrite (rngl_squ_opp Hop).
apply (rngl_squ_sqrt Hon).
apply (rngl_add_nonneg_nonneg Hor);
apply (rngl_squ_nonneg Hop Hor).
Qed.

Theorem rngl_cos_angle_eucl_dist :
  ∀ θ, (rngl_cos θ = 1 - (angle_eucl_dist θ 0)² / 2)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite H1; apply H1.
}
intros.
specialize (angle_eucl_dist_cos_sin θ) as H1.
rewrite (rngl_squ_sub Hop Hic Hon) in H1.
rewrite (rngl_squ_1 Hon) in H1.
rewrite (rngl_mul_1_r Hon) in H1.
rewrite <- rngl_add_assoc in H1.
rewrite cos2_sin2_1 in H1.
rewrite <- (rngl_add_sub_swap Hop) in H1.
rewrite (rngl_sub_mul_r_diag_l Hon Hop) in H1.
symmetry in H1.
apply (rngl_mul_move_l Hic Hi1) in H1. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
now apply (rngl_sub_move_l Hop) in H1.
Qed.

Theorem rngl_cos_le_iff_angle_eucl_le :
  ∀ θ θ',
  (rngl_cos θ ≤ rngl_cos θ' ↔ angle_eucl_dist θ' 0 ≤ angle_eucl_dist θ 0)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  split; intros. {
    rewrite H1, (H1 (angle_eucl_dist _ _)).
    apply (rngl_le_refl Hor).
  } {
    rewrite H1, (H1 (rngl_cos _)).
    apply (rngl_le_refl Hor).
  }
}
intros.
rewrite <- (rngl_abs_nonneg_eq Hop Hor (angle_eucl_dist _ _)). 2: {
  apply (dist_nonneg Hon Hop Hiv Hor).
  apply angle_eucl_dist_is_dist.
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor (angle_eucl_dist θ _)). 2: {
  apply (dist_nonneg Hon Hop Hiv Hor).
  apply angle_eucl_dist_is_dist.
}
do 2 rewrite rngl_cos_angle_eucl_dist.
split; intros H1. {
  apply (rngl_sub_le_mono_l Hop Hor) in H1.
  apply (rngl_div_le_mono_pos_r Hon Hop Hiv Hor Hii) in H1. 2: {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  now apply (rngl_squ_le_abs_le Hop Hor Hii) in H1.
} {
  apply (rngl_sub_le_mono_l Hop Hor).
  apply (rngl_div_le_mono_pos_r Hon Hop Hiv Hor Hii). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  now apply (rngl_abs_le_squ_le Hop Hor).
}
Qed.

Theorem angle_eucl_dist_nonneg : ∀ θ1 θ2, (0 ≤ angle_eucl_dist θ1 θ2)%L.
Proof.
destruct_ac.
intros.
apply (dist_nonneg Hon Hop Hiv Hor).
apply angle_eucl_dist_is_dist.
Qed.

Theorem angle_lim_const :
  ∀ θ1 θ2, angle_lim (λ _, θ1) θ2 → θ2 = θ1.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  rewrite (H1 θ1); apply H1.
}
intros * H1.
progress unfold angle_lim in H1.
progress unfold is_limit_when_tending_to_inf in H1.
apply angle_eucl_dist_separation.
rewrite angle_eucl_dist_symmetry.
specialize (angle_eucl_dist_nonneg θ1 θ2) as Hzx.
remember (angle_eucl_dist θ1 θ2) as x eqn:Hx.
clear θ1 θ2 Hx.
specialize (proj1 (rngl_lt_eq_cases Hor _ x) Hzx) as H3.
destruct H3 as [H3| H3]; [ | easy ].
clear Hzx; exfalso.
specialize (H1 (x / 2)%L).
assert (H : (0 < x / 2)%L). {
  apply (rngl_div_lt_pos Hon Hop Hiv Hor); [ easy | ].
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
specialize (H1 H); clear H.
destruct H1 as (N, HN).
specialize (HN N (Nat.le_refl _)).
apply (rngl_nle_gt Hor) in HN.
apply HN; clear HN.
apply (rngl_le_div_l Hon Hop Hiv Hor).
apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
rewrite (rngl_mul_2_r Hon).
apply (rngl_le_add_l Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_mul_1_l : ∀ θ, (1 * θ)%A = θ.
Proof.
intros; cbn.
apply angle_add_0_r.
Qed.

Theorem angle_mul_nat_assoc :
  ∀ a b θ, (a * (b * θ) = (a * b) * θ)%A.
Proof.
intros.
induction a; [ easy | cbn ].
rewrite IHa.
symmetry.
apply angle_mul_add_distr_r.
Qed.

Theorem angle_div_2_pow_mul_2_pow :
  ∀ n θ, (2 ^ n * (θ /₂^n))%A = θ.
Proof.
intros.
induction n; intros; [ apply angle_add_0_r | ].
cbn - [ "^" ].
rewrite Nat.pow_succ_r; [ | easy ].
rewrite Nat.mul_comm.
rewrite <- angle_mul_nat_assoc.
rewrite angle_div_2_mul_2.
apply IHn.
Qed.

Theorem angle_lim_add_add :
  ∀ u v θ1 θ2,
  angle_lim u θ1
  → angle_lim v θ2
  → angle_lim (λ i, (u i + v i))%A (θ1 + θ2).
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros * Hu Hv ε Hε.
  rewrite (rngl_characteristic_1 Hon Hos Hc1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hu Hv.
intros ε Hε.
assert (Hε2 : (0 < ε / 2)%L). {
  apply (rngl_lt_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  now rewrite (rngl_mul_0_l Hos).
}
specialize (Hu _ Hε2).
specialize (Hv _ Hε2).
destruct Hu as (M, HM).
destruct Hv as (N, HN).
exists (max M N).
intros n Hn.
specialize (HM n (Nat.max_lub_l _ _ _ Hn)).
specialize (HN n (Nat.max_lub_r _ _ _ Hn)).
rewrite angle_eucl_dist_move_0_l in HM, HN.
rewrite angle_eucl_dist_move_0_l.
specialize (rngl_div_add_distr_r Hiv ε ε 2)%L as Hεε2.
rewrite <- (rngl_mul_2_r Hon) in Hεε2.
rewrite (rngl_mul_div Hi1) in Hεε2. 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
rewrite Hεε2.
eapply (rngl_le_lt_trans Hor). {
  apply (angle_eucl_dist_triangular _ (θ1 - u n)).
}
apply (rngl_add_lt_compat Hop Hor); [ | easy ].
rewrite angle_add_comm.
rewrite angle_eucl_dist_move_0_r.
rewrite angle_sub_sub_swap.
rewrite angle_sub_sub_distr.
rewrite angle_add_sub.
rewrite angle_sub_add_distr.
now rewrite angle_add_sub.
Qed.

Theorem angle_lim_mul :
  ∀ k u θ,
  angle_lim u θ
  → angle_lim (λ i, (k * u i)%A) (k * θ).
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
intros * Hu.
induction k. {
  intros ε Hε.
  exists 0.
  intros n _.
  progress unfold angle_eucl_dist.
  cbn.
  do 2 rewrite (rngl_sub_diag Hos).
  rewrite (rngl_squ_0 Hos).
  rewrite rngl_add_0_l.
  rewrite (rl_sqrt_0 Hon Hop Hic Hor); [ easy | ].
  rewrite Hi1.
  apply Bool.orb_true_r.
}
cbn.
now apply angle_lim_add_add.
Qed.

Theorem angle_0_div_2_pow : ∀ n, (0 /₂^n = 0)%A.
Proof.
intros.
induction n; [ easy | cbn ].
rewrite IHn.
apply angle_0_div_2.
Qed.

Theorem angle_mul_0_r : ∀ n, (n * 0 = 0)%A.
Proof.
destruct_ac.
intros.
apply eq_angle_eq; cbn.
induction n; [ easy | cbn ].
do 2 rewrite (rngl_mul_1_l Hon).
do 2 rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_r Hos).
now rewrite rngl_add_0_l.
Qed.

Theorem angle_div_2_pow_le :
  ∀ n θ1 θ2, (θ1 ≤ θ2)%A → (θ1 /₂^n ≤ θ2 /₂^n)%A.
Proof.
intros * H12.
revert θ1 θ2 H12.
induction n; intros; [ easy | cbn ].
apply angle_div_2_le_compat.
now apply IHn.
Qed.

Theorem angle_mul_nat_overflow_0_r :
  ∀ n, angle_mul_nat_overflow n 0 = false.
Proof.
intros.
induction n; [ easy | cbn ].
destruct n; [ easy | ].
rewrite angle_add_overflow_0_l.
now apply Bool.orb_false_iff.
Qed.

Theorem angle_add_not_overflow_move_add :
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → angle_add_overflow (θ1 + θ3) θ2 = false
  → angle_add_overflow θ1 (θ2 + θ3) = false.
Proof.
destruct_ac.
intros * H13 H132.
progress unfold angle_add_overflow in H132.
progress unfold angle_add_overflow.
apply Bool.not_true_iff_false in H132.
apply angle_nlt_ge in H132.
apply Bool.not_true_iff_false.
apply angle_nlt_ge.
rewrite angle_add_add_swap in H132.
rewrite <- angle_add_assoc in H132.
apply (angle_le_trans _ (θ1 + θ3))%A; [ | apply H132 ].
progress unfold angle_add_overflow in H13.
apply Bool.not_true_iff_false in H13.
now apply angle_nlt_ge in H13.
Qed.

Theorem angle_add_diag : ∀ θ, (θ + θ = 2 * θ)%A.
Proof.
intros; cbn.
now rewrite angle_add_0_r.
Qed.

Theorem angle_mul_nat_overflow_succ_l_true :
  ∀ θ n,
  angle_mul_nat_overflow (S n) θ = true
  ↔ angle_mul_nat_overflow n θ = true ∨
    angle_add_overflow θ (n * θ) = true.
Proof.
intros.
split; intros Hn. {
  apply Bool.not_false_iff_true in Hn.
  remember (angle_mul_nat_overflow n θ) as x eqn:Hx.
  symmetry in Hx.
  destruct x; [ now left | right ].
  apply Bool.not_false_iff_true.
  intros Hy.
  apply Hn.
  now apply angle_mul_nat_overflow_succ_l_false.
} {
  apply Bool.not_false_iff_true.
  intros Hx.
  apply angle_mul_nat_overflow_succ_l_false in Hx.
  destruct Hx as (Hx, Hy).
  rewrite Hx in Hn.
  rewrite Hy in Hn.
  now destruct Hn.
}
Qed.

Theorem angle_mul_nat_overflow_succ_l :
  ∀ θ n,
  angle_mul_nat_overflow (S n) θ =
    (angle_mul_nat_overflow n θ || angle_add_overflow θ (n * θ))%bool.
Proof.
intros.
remember (_ || _)%bool as b eqn:Hb.
symmetry in Hb.
destruct b. {
  apply Bool.orb_true_iff in Hb.
  now apply angle_mul_nat_overflow_succ_l_true.
} {
  apply Bool.orb_false_iff in Hb.
  now apply angle_mul_nat_overflow_succ_l_false.
}
Qed.

Fixpoint rngl_cos_div_pow_2 θ n :=
  match n with
  | 0 => rngl_cos θ
  | S n' => (√((1 + rngl_cos_div_pow_2 θ n') / 2))%L
  end.

Fixpoint squ_rngl_cos_div_pow_2 θ n :=
  match n with
  | 0 => rngl_cos θ
  | S n' => ((1 + squ_rngl_cos_div_pow_2 θ n') / 2)%L
  end.

Theorem rngl_cos_div_pow_2_eq :
  ∀ θ n, rngl_cos (θ /₂^S n) = rngl_cos_div_pow_2 (θ /₂) n.
Proof.
destruct_ac.
intros.
rewrite angle_div_2_pow_succ_r_2.
induction n; intros; [ easy | cbn ].
rewrite IHn.
remember (0 ≤? _)%L as zsa eqn:Hzsa.
symmetry in Hzsa.
destruct zsa; [ apply (rngl_mul_1_l Hon) | ].
exfalso.
apply rngl_leb_nle in Hzsa.
apply Hzsa; clear Hzsa.
destruct n; cbn. {
  apply rl_sqrt_nonneg.
  apply rngl_1_sub_cos_div_2_nonneg.
} {
  apply rl_sqrt_nonneg.
  apply rngl_1_sub_cos_div_2_nonneg.
}
Qed.

Theorem rngl_cos_div_pow_2_0 : ∀ n, rngl_cos_div_pow_2 0 n = 1%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 1%L).
  apply H1.
}
intros n.
induction n; [ easy | cbn ].
rewrite IHn.
rewrite (rngl_div_diag Hon Hiq). 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
apply (rl_sqrt_1 Hic Hon Hop Hor).
now rewrite Bool.orb_true_iff; right.
Qed.

Theorem squ_rngl_cos_div_pow_2_0 : ∀ n, squ_rngl_cos_div_pow_2 0 n = 1%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 1%L).
  apply H1.
}
intros n.
induction n; [ easy | cbn ].
rewrite IHn.
apply (rngl_div_diag Hon Hiq).
apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_cos_div_pow_2_div_2_bound :
  ∀ n θ, (-1 ≤ rngl_cos_div_pow_2 (θ /₂) n)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (-1)%L), (H1 (rngl_cos_div_pow_2 _ _)).
  apply (rngl_le_refl Hor).
}
intros.
induction n; cbn - [ angle_div_2 ]; [ apply rngl_cos_bound | ].
apply (rngl_le_trans Hor _ 0). {
  apply (rngl_opp_1_le_0 Hon Hop Hor).
}
apply rl_sqrt_nonneg.
apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
now apply (rngl_le_opp_l Hop Hor).
Qed.

Theorem squ_rngl_cos_div_pow_2_div_2_bound :
  ∀ n θ, (-1 ≤ squ_rngl_cos_div_pow_2 (θ /₂) n ≤ 1)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (-1)%L), (H1 (squ_rngl_cos_div_pow_2 _ _)), (H1 1%L).
  split; apply (rngl_le_refl Hor).
}
intros.
induction n; cbn - [ angle_div_2 ]; [ apply rngl_cos_bound | ].
split. {
  apply (rngl_le_trans Hor _ 0). {
    apply (rngl_opp_1_le_0 Hon Hop Hor).
  }
  apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  now apply (rngl_le_opp_l Hop Hor).
} {
  apply (rngl_le_div_l Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_mul_1_l Hon).
  apply (rngl_add_le_mono_l Hop Hor).
  apply IHn.
}
Qed.

Theorem rngl_cos_div_pow_2_lower_bound :
  ∀ n θ,
  (squ_rngl_cos_div_pow_2 (θ /₂) n ≤ rngl_cos_div_pow_2 (θ /₂) n)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 (squ_rngl_cos_div_pow_2 _ _)).
  rewrite (H1 (rngl_cos_div_pow_2 _ _)).
  apply (rngl_le_refl Hor).
}
intros.
remember (θ =? 0)%A as tz eqn:Htz.
symmetry in Htz.
destruct tz. {
  apply angle_eqb_eq in Htz.
  subst θ.
  rewrite angle_0_div_2.
  rewrite rngl_cos_div_pow_2_0.
  rewrite squ_rngl_cos_div_pow_2_0.
  apply (rngl_le_refl Hor).
}
apply angle_eqb_neq in Htz.
revert θ Htz.
induction n; intros; [ apply (rngl_le_refl Hor) | ].
cbn.
remember (1 + squ_rngl_cos_div_pow_2 _ _)%L as a eqn:Ha.
remember (1 + rngl_cos_div_pow_2 _ _)%L as b eqn:Hb.
move b before a.
rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
  apply rl_sqrt_nonneg; subst b.
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_div_pow_2_div_2_bound.
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor (a / 2))%L. 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_mul_0_l Hos).
  subst a.
  apply (rngl_le_opp_l Hop Hor).
  apply squ_rngl_cos_div_pow_2_div_2_bound.
}
apply (rngl_squ_le_abs_le Hop Hor Hii).
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  subst b.
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_div_pow_2_div_2_bound.
}
rewrite (rngl_squ_div Hic Hon Hos Hiv). 2: {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
progress unfold rngl_squ at 2.
rewrite <- (rngl_div_div Hos Hon Hiv); cycle 1. {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
} {
  apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
}
apply (rngl_div_le_mono_pos_r Hon Hop Hiv Hor Hii). {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
apply (rngl_le_div_l Hon Hop Hiv Hor). {
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
subst a b.
rewrite (rngl_squ_add Hic Hon).
rewrite (rngl_squ_1 Hon).
rewrite (rngl_mul_1_r Hon).
rewrite <- rngl_add_assoc.
rewrite (rngl_mul_add_distr_r _ _ 2)%L.
rewrite (rngl_mul_1_l Hon).
rewrite <- rngl_add_assoc.
apply (rngl_add_le_mono_l Hop Hor).
rewrite (rngl_mul_comm Hic), rngl_add_comm.
apply (rngl_add_le_compat Hor). 2: {
  apply (rngl_mul_le_mono_nonneg_r Hop Hor). {
    apply (rngl_0_le_2 Hon Hop Hor).
  }
  now apply IHn.
}
rewrite <- (rngl_squ_1 Hon).
apply (rngl_abs_le_squ_le Hop Hor).
rewrite (rngl_abs_1 Hon Hop Hor).
progress unfold rngl_abs.
remember (squ_rngl_cos_div_pow_2 (θ /₂) n ≤? 0)%L as scz eqn:Hscz.
symmetry in Hscz.
destruct scz. {
  apply rngl_leb_le in Hscz.
  apply (rngl_le_opp_l Hop Hor).
  rewrite rngl_add_comm.
  apply (rngl_le_opp_l Hop Hor).
  apply squ_rngl_cos_div_pow_2_div_2_bound.
}
apply (rngl_leb_gt Hor) in Hscz.
apply squ_rngl_cos_div_pow_2_div_2_bound.
Qed.

Theorem rngl_cos_angle_div_2_pow_tending_to_1 :
  rngl_characteristic T ≠ 1 →
  rngl_is_archimedean T = true →
  ∀ θ, rngl_is_limit_when_tending_to_inf (λ i, rngl_cos (θ /₂^i)) 1%L.
Proof.
intros Hc1 Har.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros.
enough (H :
    ∀ ε, (0 < ε)%L → ∃ N, ∀ n, N ≤ n → (1 - rngl_cos (θ /₂^n) < ε)%L). {
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists N.
  intros n Hn.
  specialize (HN n Hn).
  progress unfold rngl_dist.
  rewrite (rngl_abs_nonpos_eq Hop Hor). 2: {
    apply (rngl_le_sub_0 Hop Hor).
    apply rngl_cos_bound.
  }
  rewrite (rngl_opp_sub_distr Hop).
  easy.
}
enough (H :
    ∀ ε, (0 < ε)%L → ∃ N, ∀ n, N ≤ n →
    (1 - ε < rngl_cos_div_pow_2 (θ /₂) n)%L). {
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists (S N).
  intros n Hn.
  destruct n; [ easy | ].
  apply Nat.succ_le_mono in Hn.
  specialize (HN n Hn).
  rewrite rngl_cos_div_pow_2_eq.
  apply (rngl_lt_sub_lt_add_l Hop Hor).
  apply (rngl_lt_sub_lt_add_r Hop Hor).
  easy.
}
enough (H :
    ∀ ε, (0 < ε)%L → ∃ N, ∀ n, N ≤ n →
    (1 - ε < squ_rngl_cos_div_pow_2 (θ /₂) n)%L). {
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists N.
  intros n Hn.
  eapply (rngl_lt_le_trans Hor). 2: {
    apply rngl_cos_div_pow_2_lower_bound.
  }
  now apply HN.
}
enough (H :
    ∀ ε, (0 < ε)%L → ∃ N, ∀ n, N ≤ n →
    ((1 - rngl_cos (θ /₂)) / 2 ^ n < ε)%L). {
  intros ε Hε.
  specialize (H ε Hε).
  destruct H as (N, HN).
  exists N.
  intros n Hn.
  remember (θ /₂)%A as θ' eqn:Hθ.
  specialize (HN n Hn).
  clear N Hn.
  revert ε Hε HN.
  induction n; intros. {
    cbn in HN |-*.
    rewrite (rngl_div_1_r Hon Hiq Hc1) in HN.
    apply (rngl_lt_sub_lt_add_l Hop Hor).
    apply (rngl_lt_sub_lt_add_r Hop Hor).
    easy.
  }
  cbn.
  apply (rngl_lt_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_mul_sub_distr_r Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite <- (rngl_add_sub_assoc Hop).
  apply (rngl_add_lt_mono_l Hop Hor).
  apply IHn. {
    rewrite rngl_mul_add_distr_l.
    rewrite (rngl_mul_1_r Hon).
    apply (rngl_lt_trans Hor _ ε); [ easy | ].
    now apply (rngl_lt_add_l Hos Hor).
  }
  apply (rngl_lt_div_l Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite (rngl_div_div Hos Hon Hiv); cycle 1. {
    apply (rngl_pow_nonzero Hon Hc1 Hos Hii).
    apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
  } {
    apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
  }
  cbn in HN.
  now destruct n.
}
intros ε Hε.
remember ((1 - rngl_cos (θ /₂)))%L as a eqn:Ha.
specialize (int_part Hon Hop Hc1 Hor Har) as H1.
specialize (H1 (a / ε))%L.
destruct H1 as (N, HN).
exists (Nat.log2 N + 1).
intros n Hn.
apply (rngl_lt_div_l Hon Hop Hiv Hor). {
  apply (rngl_pow_pos_nonneg Hon Hop Hiv Hc1 Hor).
  apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
}
rewrite (rngl_mul_comm Hic).
apply (rngl_lt_div_l Hon Hop Hiv Hor); [ easy | ].
rewrite <- (rngl_abs_nonneg_eq Hop Hor (_ / _))%L. 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor); [ easy | ].
  rewrite (rngl_mul_0_l Hos).
  rewrite Ha.
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
eapply (rngl_lt_le_trans Hor); [ apply HN | ].
apply (Nat.pow_le_mono_r 2) in Hn; [ | easy ].
apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor) in Hn.
do 2 rewrite (rngl_of_nat_pow Hon Hos) in Hn.
cbn in Hn.
rewrite rngl_add_0_r in Hn.
eapply (rngl_le_trans Hor); [ | apply Hn ].
replace 2%L with (rngl_of_nat 2). 2: {
  cbn.
  now rewrite rngl_add_0_r.
}
rewrite <- (rngl_of_nat_pow Hon Hos).
apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor).
rewrite Nat.add_1_r.
apply Nat.le_succ_l.
clear HN Hn.
rewrite Nat.add_1_r.
cbn.
rewrite Nat.add_0_r.
induction N; [ easy | ].
specialize (Nat.log2_succ_or N) as H1.
destruct H1 as [H1| H1]. {
  rewrite H1.
  cbn.
  rewrite Nat.add_0_r.
  apply Nat.succ_lt_mono in IHN.
  eapply Nat.lt_le_trans; [ apply IHN | ].
  rewrite <- Nat.add_1_r.
  apply Nat.add_le_mono_l.
  apply Nat.neq_0_lt_0.
  intros H.
  apply Nat.eq_add_0 in H.
  destruct H as (H, _).
  revert H.
  now apply Nat.pow_nonzero.
}
apply Nat.le_neq.
split; [ now rewrite H1 | ].
intros H2.
rewrite H1 in H2.
rewrite <- Nat_mul_2_l in H2.
rewrite <- Nat.pow_succ_r in H2; [ | easy ].
specialize (Nat.log2_spec (S N)) as H3.
specialize (H3 (Nat.lt_0_succ _)).
rewrite H1 in H3.
rewrite <- H2 in H3.
destruct H3 as (H3, H4).
now apply Nat.lt_irrefl in H4.
Qed.

Theorem rngl_cos_decr :
  ∀ θ1 θ2, (θ1 ≤ θ2 ≤ angle_straight)%A → (rngl_cos θ2 ≤ rngl_cos θ1)%L.
Proof.
intros * (H12, H2s).
destruct_ac.
progress unfold angle_leb in H12, H2s.
cbn in H2s.
rewrite (rngl_leb_refl Hor) in H2s.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs2.
destruct zs2; [ | easy ].
destruct (0 ≤? rngl_sin θ1)%L; [ | easy ].
now apply rngl_leb_le in H12.
Qed.

Theorem rngl_cos_acos :
  ∀ x, (-1 ≤ x ≤ 1)%L → rngl_cos (rngl_acos x) = x.
Proof.
destruct_ac.
intros * Hx1.
progress unfold rngl_acos.
destruct (rngl_le_dec ac_or x² 1) as [| H]; [ easy | ].
exfalso; apply H; clear H.
now apply (rngl_squ_le_1 Hon Hop Hor).
Qed.

Theorem rngl_sin_acos :
  ∀ x, (-1 ≤ x ≤ 1)%L → rngl_sin (rngl_acos x) = √(1 - x²)%L.
Proof.
destruct_ac.
intros * Hx1.
progress unfold rngl_acos.
destruct (rngl_le_dec ac_or x² 1) as [| H]; [ easy | ].
exfalso; apply H; clear H.
now apply (rngl_squ_le_1 Hon Hop Hor).
Qed.

Theorem angle_le_opp_r : ∀ θ1 θ2, θ1 ≠ 0%A → (θ1 ≤ - θ2)%A → (θ2 ≤ - θ1)%A.
Proof.
destruct_ac.
intros * H2z H2.
progress unfold angle_leb in H2.
progress unfold angle_leb.
cbn in H2 |-*.
rewrite (rngl_leb_0_opp Hop Hor) in H2.
rewrite (rngl_leb_opp_r Hop Hor).
rewrite (rngl_opp_0 Hop).
remember (0 ≤? rngl_sin θ1)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin θ2)%L as zs eqn:Hzs.
remember (rngl_sin θ1 ≤? 0)%L as sz2 eqn:Hsz2.
remember (rngl_sin θ2 ≤? 0)%L as sz eqn:Hsz.
symmetry in Hzs2, Hzs, Hsz2, Hsz.
destruct zs. {
  destruct sz2; [ | easy ].
  destruct zs2; [ | now destruct sz ].
  apply rngl_leb_le in Hzs2, Hzs, Hsz2.
  apply rngl_leb_le.
  apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
  apply eq_rngl_sin_0 in Hzs2.
  destruct Hzs2; [ easy | subst θ1 ].
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
  destruct Hzs2; [ easy | subst θ1 ].
  apply (rngl_nlt_ge Hor) in H2.
  apply H2; clear H2.
  apply (rngl_lt_iff Hor).
  split; [ apply rngl_cos_bound | ].
  cbn; intros Hcc.
  symmetry in Hcc.
  apply eq_rngl_cos_opp_1 in Hcc.
  subst θ2.
  now apply (rngl_lt_irrefl Hor) in Hzs.
}
clear H2.
destruct sz2. {
  exfalso.
  apply rngl_leb_le in Hsz2.
  apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
  apply eq_rngl_sin_0 in Hzs2.
  destruct Hzs2; [ easy | subst θ1 ].
  apply (rngl_leb_gt Hor) in Hsz.
  now apply (rngl_lt_asymm Hor) in Hzs.
}
apply (rngl_leb_gt Hor) in Hsz.
now apply (rngl_lt_asymm Hor) in Hzs.
Qed.

End a.

Arguments rngl_acos {T ro rp ac rl} x%_L.
