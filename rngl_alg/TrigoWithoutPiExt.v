Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.RingLike.
Require Import TrigoWithoutPi.
Require Import AngleLeSubAdd.
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
destruct (rngl_eq_dec Hed (rngl_sin θ1) 0) as [Hs1z| Hs1z]. {
  apply eq_rngl_sin_0 in Hs1z.
  destruct Hs1z; subst θ1. {
    rewrite angle_add_0_l.
    apply rngl_cos_bound.
  }
  destruct H12 as [H12| H12]; [ easy | ].
  rewrite (rngl_sin_add_straight_l Hon Hop) in Hzs12.
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
  apply (rngl_mul_pos_neg Hop Hor Hid); [ | easy ].
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
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Hsz1 Hzs2 Hzc1 Hzc2 Hzs12.
destruct (rngl_eq_dec Hed (rngl_sin θ2) 0) as [Hs2z| Hs2z]. {
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
rewrite <- (rngl_cos_sub Hop).
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
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov.
  progress unfold angle_add_overflow.
  apply angle_ltb_ge.
  progress unfold angle_leb.
  rewrite (H1 (rngl_sin _)).
  rewrite (rngl_leb_refl Hor).
  rewrite (H1 (rngl_sin _)).
  rewrite (rngl_leb_refl Hor).
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_leb_refl Hor).
}
intros * Haov.
progress unfold angle_add_overflow in Haov.
progress unfold angle_add_overflow.
apply angle_ltb_ge in Haov.
apply angle_ltb_ge.
progress unfold angle_leb in Haov.
progress unfold angle_leb.
rewrite (angle_add_comm θ2).
remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs12, Hzs1, Hzs2.
destruct zs2. {
  destruct zs12; [ | easy ].
  destruct zs1; [ | easy ].
  apply rngl_leb_le in Hzs1, Hzs12, Hzs2, Haov.
  apply rngl_leb_le.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    rewrite angle_add_comm.
    apply rngl_cos_add_le_cos; try easy.
    now right; right; left.
    now rewrite angle_add_comm.
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  destruct (rngl_eq_dec Hed (rngl_cos θ2) (- 1)) as [Hc2o1| Ho1c2]. {
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
    apply rngl_leb_le in Haov.
    apply angle_add_overflow_le_lemma_6 in Haov; try easy.
  }
  apply (rngl_leb_gt Hor) in Hzs12.
  apply rngl_leb_le.
  destruct zs1. {
    clear Haov.
    apply rngl_leb_le in Hzs1.
    rewrite angle_add_comm.
    apply rngl_cos_le_cos_add; try easy.
    now apply (rngl_lt_le_incl Hor).
    now rewrite angle_add_comm.
  }
  apply (rngl_leb_gt Hor) in Hzs1.
  apply rngl_leb_le in Haov.
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
  rewrite (angle_opp_sub_distr Hic Hop) in H.
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

End a.
