(* equivalent definition of angle_add_overflow *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.RingLike.
Require Import TrigoWithoutPi.
Require Import TrigoWithoutPiExt.
Require Import AngleLeSubAdd.
Require Import TacChangeAngle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

Definition angle_add_not_overflow3 θ1 θ2 :=
  θ2 = 0%A ∨ (θ1 < -θ2)%A.

Theorem rngl_sin_nonneg_is_pos :
  ∀ θ,
  θ ≠ 0%A
  → θ ≠ angle_straight
  → (0 ≤ rngl_sin θ)%L
  → (0 < rngl_sin θ)%L.
Proof.
intros * Hz Hs Hsz.
destruct_ac.
apply (rngl_lt_iff Hor).
split; [ easy | ].
intros H; symmetry in H.
apply eq_rngl_sin_0 in H.
now destruct H.
Qed.

Theorem rngl_sin_nonpos_is_neg :
  ∀ θ,
  θ ≠ 0%A
  → θ ≠ angle_straight
  → (rngl_sin θ ≤ 0)%L
  → (rngl_sin θ < 0)%L.
Proof.
intros * Hz Hs Hsz.
destruct_ac.
apply (rngl_lt_iff Hor).
split; [ easy | ].
intros H.
apply eq_rngl_sin_0 in H.
now destruct H.
Qed.

Theorem quadrant_2_quadrant_34_rngl_cos_lt_cos_add :
  ∀ θ1 θ2,
  θ2 ≠ 0%A
  → (0 ≤ rngl_sin θ1)%L
  → (rngl_cos θ1 < 0)%L
  → (rngl_sin θ2 ≤ 0)%L
  → (rngl_cos θ1 < rngl_cos (θ1 + θ2))%L.
Proof.
intros * Hs2z Hzs1 Hc1z Hsz2.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_goal T.
change_angle_add_r θ2 angle_right.
progress sin_cos_add_sub_right_hyp T Hsz2.
progress sin_cos_add_sub_right_goal T.
apply (rngl_lt_opp_l Hop Hor); cbn.
rewrite rngl_add_comm.
rewrite (rngl_add_sub_assoc Hop).
rewrite (rngl_add_sub_swap Hop).
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
apply (rngl_add_pos_nonneg Hor). {
  apply (rngl_mul_pos_pos Hop Hor Hii); [ easy | ].
  apply (rngl_lt_0_sub Hop Hor).
  apply (rngl_lt_iff Hor).
  split; [ apply rngl_sin_bound | ].
  intros H.
  apply eq_rngl_sin_1 in H.
  subst θ2.
  now rewrite angle_sub_diag in Hs2z.
}
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

Theorem quadrant_12_quadrant_2_rngl_cos_lt :
  ∀ θ1 θ2,
  θ2 ≠ 0%A
  → (0 ≤ rngl_sin θ1)%L
  → (rngl_sin θ2 ≤ 0)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos θ1)%L
  → (rngl_cos θ2 < rngl_cos θ1)%L.
Proof.
intros * H2z Hzs1 Hsz2 Hzc2 Hzs12 H12.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  exfalso; apply H2z, H1.
}
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  exfalso.
  apply (rngl_nlt_ge Hor) in H12.
  apply H12; clear H12.
  apply quadrant_1_quadrant_4_cos_lt_cos_add; try easy.
  apply rngl_sin_nonpos_is_neg; [ easy | | easy ].
  intros H; subst θ2.
  apply (rngl_nlt_ge Hor) in Hzc2.
  apply Hzc2; clear Hzc2; cbn.
  apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
}
exfalso.
apply (rngl_nlt_ge Hor) in H12.
apply H12; clear H12.
apply (rngl_nle_gt Hor) in Hc1z.
apply quadrant_2_quadrant_34_rngl_cos_lt_cos_add; try easy.
Qed.

Theorem quadrant_12_quadrant_3_rngl_cos_lt_cos_add :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (rngl_sin θ2 ≤ 0)%L
  → (rngl_cos θ2 < 0)%L
  → (rngl_cos θ1 ≤ rngl_cos θ2)%L
  → (rngl_cos θ1 < rngl_cos (θ1 + θ2))%L.
Proof.
destruct_ac.
intros * Hzs1 Hsz2 Hc2z Hcc.
apply (rngl_nle_gt Hor).
intros H12.
apply (rngl_nlt_ge Hor) in Hcc.
apply Hcc; clear Hcc.
change_angle_add_r θ2 angle_straight.
progress sin_cos_add_sub_straight_hyp T Hc2z.
progress sin_cos_add_sub_straight_hyp T Hsz2.
progress sin_cos_add_sub_straight_hyp T H12.
progress sin_cos_add_sub_straight_goal T.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  now apply (rngl_add_pos_nonneg Hor).
}
exfalso.
apply (rngl_nle_gt Hor) in Hc1z.
apply (rngl_nlt_ge Hor) in H12.
apply H12; clear H12.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_goal T.
apply (rngl_add_pos_nonneg Hor); [ easy | ].
apply (rngl_lt_le_incl Hor) in Hc1z, Hc2z.
now apply rngl_sin_add_nonneg.
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

Theorem angle_add_not_overflow_equiv3 :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false ↔ angle_add_not_overflow3 θ1 θ2.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 θ2), angle_add_overflow_0_r.
  progress unfold angle_add_not_overflow3.
  split; [ now intros; left | easy ].
}
intros.
progress unfold angle_add_overflow.
progress unfold angle_add_not_overflow3.
split; intros H12. {
  destruct (angle_eq_dec θ2 0) as [H2z| H2z]; [ now left | right ].
  progress unfold angle_ltb in H12.
  progress unfold angle_ltb.
  move H2z before θ2.
  cbn.
  rewrite (rngl_leb_opp_r Hop Hor).
  rewrite (rngl_opp_0 Hop).
  remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
  remember (rngl_sin θ2 ≤? 0)%L as sz2 eqn:Hsz2.
  remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
  symmetry in Hzs1, Hsz2, Hzs12.
  destruct zs12. {
    destruct zs1; [ | easy ].
    destruct sz2; [ | easy ].
    apply rngl_leb_le in Hzs1, Hzs12, Hsz2.
    apply rngl_ltb_lt.
    apply (rngl_ltb_ge Hor) in H12.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
      now apply quadrant_12_quadrant_2_rngl_cos_lt.
    } {
      apply (rngl_nle_gt Hor) in Hc2z.
      apply (rngl_nle_gt Hor).
      intros Hcc.
      apply (rngl_nlt_ge Hor) in H12.
      apply H12; clear H12.
      now apply quadrant_12_quadrant_3_rngl_cos_lt_cos_add.
    }
  }
  apply (rngl_leb_gt Hor) in Hzs12.
  destruct zs1. {
    clear H12.
    destruct sz2; [ | easy ].
    apply rngl_leb_le in Hzs1, Hsz2.
    apply rngl_ltb_lt.
    (* lemma? *)
(* ... *)
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
      change_angle_opp θ2.
      progress sin_cos_opp_hyp T Hzc2.
      progress sin_cos_opp_hyp T Hsz2.
      progress sin_cos_opp_hyp T Hzs12.
      apply (rngl_opp_nonpos_nonneg Hop Hor) in Hsz2.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
        cbn.
        apply (rngl_opp_lt_compat Hop Hor) in Hzs12.
        rewrite (rngl_opp_0 Hop) in Hzs12.
        rewrite <- rngl_sin_sub_anticomm in Hzs12.
        apply quadrant_1_sin_sub_pos_cos_lt; try easy.
      }
      exfalso.
      apply (rngl_nle_gt Hor) in Hzs12.
      apply Hzs12; clear Hzs12.
      apply (rngl_nle_gt Hor) in Hc1z.
      change_angle_sub_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs1.
      progress sin_cos_add_sub_right_hyp T Hc1z.
      progress sin_cos_add_sub_right_goal T.
      apply (rngl_lt_le_incl Hor) in Hc1z.
      now apply rngl_cos_sub_nonneg.
    }
    apply (rngl_nle_gt Hor) in Hc2z.
    change_angle_add_r θ2 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hc2z.
    progress sin_cos_add_sub_straight_hyp T Hsz2.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_goal T.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      now apply (rngl_add_pos_nonneg Hor).
    }
    apply (rngl_nle_gt Hor) in Hc1z.
    change_angle_sub_l θ1 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hzs1.
    progress sin_cos_add_sub_straight_hyp T Hc1z.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_goal T.
    apply (rngl_lt_0_sub Hop Hor).
    apply (rngl_lt_le_incl Hor) in Hc1z, Hc2z.
    now apply quadrant_1_sin_sub_pos_cos_lt.
  }
  apply (rngl_leb_gt Hor) in Hzs1.
  apply (rngl_ltb_ge Hor) in H12.
  destruct sz2. {
    exfalso.
    apply rngl_leb_le in Hsz2.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
      change_angle_opp θ2.
      progress sin_cos_opp_hyp T Hzc2.
      progress sin_cos_opp_hyp T Hsz2.
      progress sin_cos_opp_hyp T Hzs12.
      apply (rngl_opp_nonpos_nonneg Hop Hor) in Hsz2.
      rewrite angle_add_opp_r in H12.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
        change_angle_add_r θ1 angle_right.
        rewrite angle_sub_sub_swap in Hzs12, H12.
        progress sin_cos_add_sub_right_hyp T Hzs1.
        progress sin_cos_add_sub_right_hyp T Hzc1.
        progress sin_cos_add_sub_right_hyp T Hzs12.
        progress sin_cos_add_sub_right_hyp T H12.
        apply (rngl_nlt_ge Hor) in H12.
        apply H12; clear H12.
        apply rngl_sin_sub_lt_sin_l; [ easy | | easy ].
        apply rngl_sin_nonneg_is_pos; [ | | easy ]. {
          now intros H; subst θ2; rewrite angle_opp_0 in H2z.
        } {
          intros H; subst θ2.
          progress sin_cos_add_sub_straight_hyp T Hzs12.
          now apply (rngl_lt_asymm Hor) in Hzs12.
        }
      }
      apply (rngl_nle_gt Hor) in Hc1z.
      change_angle_add_r θ1 angle_straight.
      rewrite angle_sub_sub_swap in Hzs12, H12.
      progress sin_cos_add_sub_straight_hyp T Hzs1.
      progress sin_cos_add_sub_straight_hyp T Hc1z.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T H12.
      rewrite (rngl_add_opp_l Hop) in H12.
      apply -> (rngl_le_sub_0 Hop Hor) in H12.
      apply (rngl_nlt_ge Hor) in H12.
      apply H12; clear H12.
      rewrite rngl_cos_sub_comm.
      (* lemma? *)
      apply rngl_cos_lt_rngl_cos_sub. {
        now apply (rngl_lt_le_incl Hor) in Hzs1.
      } {
        apply rngl_sin_nonneg_is_pos; [ | | easy ]. {
          now intros H; subst θ2; rewrite angle_opp_0 in H2z.
        } {
          intros H; subst θ2.
          progress sin_cos_add_sub_straight_hyp T Hzs12.
          now apply (rngl_lt_asymm Hor) in Hzs12.
        }
      }
      apply (rngl_lt_le_incl Hor) in Hc1z.
      apply (rngl_lt_le_incl Hor) in Hzs1, Hzs12.
      now apply quadrant_1_sin_sub_nonneg_cos_le.
    }
    apply (rngl_nle_gt Hor) in Hc2z.
    change_angle_add_r θ2 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hc2z.
    progress sin_cos_add_sub_straight_hyp T Hsz2.
    progress sin_cos_add_sub_straight_hyp T H12.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      change_angle_add_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs1.
      progress sin_cos_add_sub_right_hyp T Hzc1.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_hyp T H12.
      apply (rngl_nlt_ge Hor) in H12.
      apply H12; clear H12.
      apply (rngl_add_nonneg_pos Hor); [ easy | ].
      cbn.
      apply (rngl_add_nonneg_pos Hor).
      apply (rngl_lt_le_incl Hor) in Hc2z.
      now apply (rngl_mul_nonneg_nonneg Hop Hor).
      apply (rngl_mul_pos_pos Hop Hor Hii); [ easy | ].
      apply rngl_sin_nonneg_is_pos; [ | | easy ]. {
        intros H; subst θ2.
        rewrite angle_add_0_r in Hzs12.
        now apply (rngl_lt_asymm Hor) in Hzs12.
      }
      intros H; subst θ2.
      now rewrite angle_sub_diag in H2z.
    }
    apply (rngl_nle_gt Hor) in Hc1z.
    change_angle_add_r θ1 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hzs1.
    progress sin_cos_add_sub_straight_hyp T Hc1z.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    apply (rngl_nle_gt Hor) in Hzs12.
    apply Hzs12; clear Hzs12.
    apply (rngl_lt_le_incl Hor) in Hzs1, Hc2z, Hc1z.
    now apply rngl_sin_add_nonneg.
  }
  apply (rngl_leb_gt Hor) in Hsz2.
  apply rngl_ltb_lt.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      change_angle_opp θ1.
      progress sin_cos_opp_hyp T Hzs1.
      progress sin_cos_opp_hyp T H12.
      progress sin_cos_opp_hyp T Hzc1.
      cbn.
      rewrite angle_add_opp_l in H12, Hzs12.
      apply (rngl_nle_gt Hor).
      intros Hcc.
      apply (rngl_nle_gt Hor) in Hzs12.
      apply Hzs12; clear Hzs12.
      apply (rngl_lt_le_incl Hor) in Hzs1, Hsz2.
      now apply rngl_sin_sub_nonneg.
    }
    apply (rngl_nle_gt Hor) in Hc1z.
    change_angle_add_r θ1 angle_straight.
    progress sin_cos_add_sub_straight_hyp T H12.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hzs1.
    progress sin_cos_add_sub_straight_hyp T Hc1z.
    progress sin_cos_add_sub_straight_goal T.
    now apply (rngl_add_pos_nonneg Hor).
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    exfalso.
    apply (rngl_nle_gt Hor) in Hzs12.
    apply Hzs12; clear Hzs12.
    change_angle_add_r θ1 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzs1.
    progress sin_cos_add_sub_right_hyp T Hzc1.
    progress sin_cos_add_sub_right_hyp T H12.
    progress sin_cos_add_sub_right_goal T.
    apply (rngl_lt_le_incl Hor) in Hc2z, Hzs1, Hsz2.
    change_angle_sub_r θ2 angle_right.
    progress sin_cos_add_sub_right_hyp T Hc2z.
    progress sin_cos_add_sub_right_hyp T Hsz2.
    progress sin_cos_add_sub_right_hyp T H12.
    progress sin_cos_add_sub_right_goal T.
    now apply rngl_sin_add_nonneg.
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  change_angle_add_r θ1 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_hyp T Hc1z.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T H12.
  progress sin_cos_add_sub_straight_goal T.
  change_angle_sub_l θ2 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_hyp T H12.
  progress sin_cos_add_sub_straight_hyp T Hc2z.
  progress sin_cos_add_sub_straight_hyp T Hsz2.
  progress sin_cos_add_sub_straight_goal T.
  rewrite (rngl_add_opp_r Hop) in H12.
  rewrite <- (rngl_opp_add_distr Hop) in H12.
  apply (rngl_opp_nonpos_nonneg Hop Hor) in H12.
  apply (rngl_lt_0_sub Hop Hor).
  apply (rngl_nle_gt Hor).
  intros Hcc.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  apply (rngl_lt_le_incl Hor) in Hzs1, Hsz2.
  now apply (rngl_sin_sub_nonneg).
}
apply angle_ltb_ge.
destruct H12 as [H12| H12]. {
  subst θ2.
  rewrite angle_add_0_r.
  apply angle_le_refl.
}
progress unfold angle_ltb in H12.
progress unfold angle_leb.
cbn in H12.
rewrite (rngl_leb_opp_r Hop Hor) in H12.
rewrite (rngl_opp_0 Hop) in H12.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (rngl_sin θ2 ≤? 0)%L as sz2 eqn:Hsz2.
remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
symmetry in Hzs1, Hsz2, Hzs12.
destruct zs1. {
  destruct zs12; [ | easy ].
  apply rngl_leb_le in Hzs1, Hzs12.
  apply rngl_leb_le.
  destruct sz2. {
    apply rngl_leb_le in Hsz2.
    apply rngl_ltb_lt in H12.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
      apply (rngl_nlt_ge Hor).
      intros Hcc.
      change_angle_opp θ2.
      progress sin_cos_opp_hyp T Hzc2.
      progress sin_cos_opp_hyp T Hcc.
      progress sin_cos_opp_hyp T Hzs12.
      progress sin_cos_opp_hyp T H12.
      progress sin_cos_opp_hyp T Hsz2.
      apply (rngl_opp_nonpos_nonneg Hop Hor) in Hsz2.
      apply (rngl_opp_le_compat Hop Hor) in Hzs12.
      rewrite (rngl_opp_0 Hop) in Hzs12.
      rewrite <- rngl_sin_sub_anticomm in Hzs12.
      apply (rngl_nlt_ge Hor) in Hzs12.
      apply Hzs12; clear Hzs12.
      apply rngl_sin_nonneg_is_pos. {
        intros H.
        apply -> angle_sub_move_0_r in H; subst θ2.
        now apply (rngl_lt_irrefl Hor) in H12.
      } {
        intros H.
        apply angle_sub_move_r in H; subst θ2.
        rewrite angle_sub_add_distr in Hcc.
        rewrite angle_sub_sub_swap in Hcc.
        rewrite angle_sub_diag in Hcc.
        rewrite angle_sub_0_l in Hcc.
        apply (rngl_nle_gt Hor) in Hcc.
        apply Hcc; clear Hcc; cbn.
        apply rngl_cos_bound.
      }
      apply (rngl_lt_le_incl Hor) in H12.
      now apply rngl_sin_sub_nonneg.
    }
    apply (rngl_nle_gt Hor) in Hc2z.
    change_angle_add_r θ2 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hc2z.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T H12.
    progress sin_cos_add_sub_straight_hyp T Hsz2.
    progress sin_cos_add_sub_straight_goal T.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      apply (rngl_nlt_ge Hor).
      intros Hcc.
      apply (rngl_nlt_ge Hor) in Hzs12.
      apply Hzs12; clear Hzs12.
      apply rngl_sin_nonneg_is_pos. {
        intros H.
        apply angle_add_move_0_r in H.
        subst θ1.
        cbn in Hzs1.
        apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs1.
        apply (rngl_le_antisymm Hor) in Hsz2; [ | easy ].
        apply eq_rngl_sin_0 in Hsz2.
        destruct Hsz2; subst θ2. {
          rewrite angle_add_0_r in Hcc.
          apply (rngl_nle_gt Hor) in Hcc.
          apply Hcc; cbn.
          apply (rngl_0_le_2 Hon Hop Hor).
        }
        cbn in Hc2z.
        apply (rngl_nle_gt Hor) in Hc2z.
        apply Hc2z; clear Hc2z.
        apply (rngl_opp_1_le_0 Hon Hop Hor).
      } {
        intros H.
        apply angle_add_move_r in H.
        subst θ1.
        rewrite rngl_cos_sub_straight_l in H12.
        now apply (rngl_lt_irrefl Hor) in H12.
      }
      apply (rngl_lt_le_incl Hor) in Hc2z.
      now apply rngl_sin_add_nonneg.
    }
    apply (rngl_nle_gt Hor) in Hc1z.
    change_angle_sub_l θ1 angle_straight.
    progress sin_cos_add_sub_straight_hyp T Hzs1.
    progress sin_cos_add_sub_straight_hyp T H12.
    progress sin_cos_add_sub_straight_hyp T Hzs12.
    progress sin_cos_add_sub_straight_hyp T Hc1z.
    progress sin_cos_add_sub_straight_goal T.
    apply (rngl_nlt_ge Hor).
    intros Hcc.
    apply (rngl_nle_gt Hor) in H12.
    apply H12; clear H12.
    apply (rngl_opp_le_compat Hop Hor) in Hzs12.
    rewrite (rngl_opp_0 Hop) in Hzs12.
    rewrite <- rngl_sin_sub_anticomm in Hzs12.
    apply (rngl_lt_le_incl Hor) in Hc2z, Hc1z.
    now apply quadrant_1_sin_sub_nonneg_cos_le.
  }
  clear H12.
  apply (rngl_leb_gt Hor) in Hsz2.
  apply rngl_cos_add_le_cos; try easy. {
    right; left.
    intros H; subst θ2.
    now apply (rngl_lt_irrefl Hor) in Hsz2.
  }
  now apply (rngl_lt_le_incl Hor) in Hsz2.
}
destruct sz2; [ easy | ].
apply (rngl_leb_gt Hor) in Hzs1, Hsz2.
apply rngl_ltb_lt in H12.
destruct zs12. {
  exfalso.
  apply rngl_leb_le in Hzs12.
  (* lemma? *)
  apply (rngl_nle_gt Hor) in H12.
  apply H12; clear H12.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
      change_angle_opp θ1.
      progress sin_cos_opp_hyp T Hzs1.
      progress sin_cos_opp_hyp T Hzc1.
      rewrite angle_add_opp_l in Hzs12.
      cbn.
      apply (rngl_lt_le_incl Hor) in Hsz2, Hzs1.
      now apply quadrant_1_sin_sub_nonneg_cos_le.
    }
    apply (rngl_nle_gt Hor) in Hc2z.
    change_angle_add_r θ1 angle_right.
    progress sin_cos_add_sub_right_hyp T Hzc1.
    change_angle_sub_r θ2 angle_right.
    progress sin_cos_add_sub_right_hyp T Hc2z.
    progress sin_cos_add_sub_right_goal T.
    apply (rngl_lt_le_incl Hor) in Hc2z.
    now apply (rngl_add_nonneg_nonneg Hor).
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  change_angle_add_r θ1 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hzs1.
  progress sin_cos_add_sub_straight_hyp T Hc1z.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_goal T.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    exfalso.
    apply (rngl_nlt_ge Hor) in Hzs12.
    apply Hzs12; clear Hzs12.
    (* faire lemme rngl_sin_add_pos *)
    cbn.
    apply (rngl_add_nonneg_pos Hor).
    apply (rngl_lt_le_incl Hor) in Hzs1.
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
    now apply (rngl_mul_pos_pos Hop Hor Hii).
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  change_angle_sub_l θ2 angle_straight.
  progress sin_cos_add_sub_straight_hyp T Hsz2.
  progress sin_cos_add_sub_straight_hyp T Hc2z.
  progress sin_cos_add_sub_straight_hyp T Hzs12.
  progress sin_cos_add_sub_straight_goal T.
  rewrite (rngl_add_opp_l Hop).
  apply (rngl_le_sub_0 Hop Hor).
  apply (rngl_lt_le_incl Hor) in Hzs1, Hsz2, Hc1z, Hc2z.
  now apply quadrant_1_sin_sub_nonneg_cos_le.
}
apply (rngl_leb_gt Hor) in Hzs12.
apply rngl_leb_le.
apply (rngl_lt_le_incl Hor) in Hzs1, Hsz2.
apply rngl_cos_le_cos_add; try easy.
Qed.

End a.
