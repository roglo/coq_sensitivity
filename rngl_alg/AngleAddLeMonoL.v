(* just a file for this theorem:
     (θ2 ≤ θ3)%A → (θ1 + θ2 ≤ θ1 + θ3)%A
 *)

Set Nested Proofs Allowed.
Require Import Utf8 ZArith.
(*
Require Import Init.Nat.
Import List List.ListNotations.
*)
Require Import (*Main.Misc*) Main.RingLike (*Main.IterAdd*).
Require Import (*RealLike*) TrigoWithoutPi (*AngleLeSubAdd*).
(*
Require Import AngleAddOverflowLe.
*)

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

Theorem angle_add_le_mono_l :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
    angle_add_overflow θ1 θ2 = false
    → angle_add_overflow θ1 θ3 = false
    → (θ2 ≤ θ3)%A → (θ1 + θ2 ≤ θ1 + θ3)%A.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov12 Haov13 H23.
  progress unfold angle_leb.
  rewrite (H1 (rngl_sin (θ1 + θ2))).
  rewrite (rngl_leb_refl Hor).
  rewrite (H1 (rngl_sin (θ1 + θ3))).
  rewrite (rngl_leb_refl Hor).
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_leb_refl Hor).
}
intros * Haov12 Haov13 H23.
progress unfold angle_leb in H23.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin θ3)%L as zs3 eqn:Hzs3.
remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
remember (0 ≤? rngl_sin (θ1 + θ3))%L as zs13 eqn:Hzs13.
symmetry in Hzs2, Hzs3, Hzs12, Hzs13.
move H23 at bottom.
destruct zs12. {
  destruct zs13; [ | easy ].
  apply rngl_leb_le in Hzs12, Hzs13.
  apply rngl_leb_le.
  destruct zs2. {
    apply rngl_leb_le in Hzs2.
    destruct zs3. {
      apply rngl_leb_le in Hzs3, H23.
...
      now apply angle_add_le_mono_l_lemma_3.
    }
    clear H23.
    apply (rngl_leb_gt Hor) in Hzs3.
    destruct (rngl_lt_dec Hor (rngl_cos θ3) 0)%L as [Hc3z| Hzc3]. {
      exfalso.
      apply Bool.not_true_iff_false in Haov13.
      apply Haov13.
      now apply angle_add_le_mono_l_lemma_11.
    } {
      apply (rngl_nlt_ge Hor) in Hzc3.
      now apply angle_add_le_mono_l_lemma_7.
    }
  }
  destruct zs3; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzs2, Hzs3.
  apply rngl_leb_le in H23.
  destruct (rngl_lt_dec Hor (rngl_cos θ3) 0)%L as [Hc3z| Hzc3]. {
    exfalso.
    apply Bool.not_true_iff_false in Haov13.
    apply Haov13.
    now apply angle_add_le_mono_l_lemma_11.
  } {
    apply (rngl_nlt_ge Hor) in Hzc3.
    now apply angle_add_le_mono_l_lemma_16.
  }
}
apply (rngl_leb_gt Hor) in Hzs12.
destruct zs2. {
  apply rngl_leb_le in Hzs2.
  destruct zs3. {
    apply rngl_leb_le in Hzs3, H23.
    destruct zs13. {
      exfalso.
      apply rngl_leb_le in Hzs13.
      apply (rngl_nle_gt Hor) in Hzs12.
      apply Hzs12; clear Hzs12.
      now apply angle_add_le_mono_l_lemma_19 with (θ3 := θ3).
    }
    apply (rngl_leb_gt Hor) in Hzs13.
    apply rngl_leb_le.
    destruct (rngl_lt_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
      now apply angle_add_le_mono_l_lemma_20.
    } {
      apply (rngl_nlt_ge Hor) in Hc3z.
      now apply angle_add_le_mono_l_lemma_28.
    }
  } {
    clear H23.
    apply (rngl_leb_gt Hor) in Hzs3.
    destruct zs13. {
      exfalso.
      apply rngl_leb_le in Hzs13.
      apply (rngl_nle_gt Hor) in Hzs12.
      apply Hzs12; clear Hzs12.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
        destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
          destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
            now apply (rngl_sin_add_nonneg Hop).
          } {
            apply (rngl_nle_gt Hor) in Hc1z.
            exfalso.
            apply (Bool.not_true_iff_false) in Haov13.
            apply Haov13.
            now apply angle_add_le_mono_l_lemma_30.
          }
        } {
          apply (rngl_nle_gt Hor) in Hs1z.
          destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
            now apply (angle_add_le_mono_l_lemma_32 Hic Hon Hop Hed _ _ θ3).
          } {
            apply (rngl_nle_gt Hor) in Hc1z.
            apply angle_add_overflow_false_comm in Haov13; try easy.
            exfalso.
            apply Bool.not_true_iff_false in Haov13.
            apply Haov13; clear Haov13.
            apply angle_add_le_mono_l_lemma_11; try easy.
            now rewrite (angle_add_comm Hic).
          }
        }
      } {
        apply (rngl_nle_gt Hor) in Hc2z.
        change_angle_sub_r Hic Hon Hop Hed θ2 angle_right.
        sin_cos_add_sub_right_hyp Hic Hon Hop Hzs2.
        sin_cos_add_sub_right_hyp Hic Hon Hop Hc2z.
        sin_cos_add_sub_right_goal Hic Hon Hop.
        destruct (rngl_le_dec Hor (rngl_sin θ1) 0) as [Hs1z| Hzs1]. {
         now apply (angle_add_le_mono_l_lemma_34 Hic Hon Hop Hed _ _ θ3).
        } {
          apply (rngl_nle_gt Hor) in Hzs1.
          destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
            apply (rngl_nlt_ge Hor).
            intros Hc12z.
            apply Bool.not_true_iff_false in Haov13.
            apply Haov13; clear Haov13.
            now apply angle_add_le_mono_l_lemma_37.
          } {
            apply (rngl_nle_gt Hor) in Hc3z.
            now apply (angle_add_le_mono_l_lemma_38 Hic Hon Hop Hed _ _ θ3).
          }
        }
      }
    } {
      apply (rngl_leb_gt Hor) in Hzs13.
      apply rngl_leb_le.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
        now apply angle_add_le_mono_l_lemma_41.
      } {
        apply (rngl_nle_gt Hor) in Hc3z.
        now apply angle_add_le_mono_l_lemma_44.
      }
    }
  }
}
destruct zs3; [ easy | ].
apply (rngl_leb_gt Hor) in Hzs2, Hzs3.
apply rngl_leb_le in H23.
destruct zs13. {
  exfalso.
  apply rngl_leb_le in Hzs13.
  apply Bool.not_true_iff_false in Haov13.
  apply Haov13; clear Haov13.
  now apply (angle_add_le_mono_l_lemma_47 Hic Hon Hop Hed _ θ2).
}
apply rngl_leb_le.
apply (rngl_leb_gt Hor) in Hzs13.
change_angle_add_r Hic Hon Hop Hed θ2 angle_straight.
sin_cos_add_sub_straight_hyp Hic Hon Hop Hzs2.
sin_cos_add_sub_straight_hyp Hic Hon Hop H23.
sin_cos_add_sub_straight_hyp Hic Hon Hop Hzs12.
sin_cos_add_sub_straight_goal Hic Hon Hop.
change_angle_add_r Hic Hon Hop Hed θ3 angle_straight.
sin_cos_add_sub_straight_hyp Hic Hon Hop H23.
sin_cos_add_sub_straight_hyp Hic Hon Hop Hzs13.
sin_cos_add_sub_straight_hyp Hic Hon Hop Hzs3.
sin_cos_add_sub_straight_goal Hic Hon Hop.
rewrite (rngl_add_opp_l Hop) in H23.
apply -> (rngl_le_sub_0 Hop Hor) in H23.
apply angle_add_le_mono_l_lemma_3; try easy; cycle 1.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
progress unfold angle_add_overflow in Haov13.
progress unfold angle_ltb in Haov13.
progress unfold angle_add_overflow.
progress unfold angle_ltb.
sin_cos_add_sub_straight_hyp Hic Hon Hop Haov13.
generalize Hzs13; intros H.
apply (rngl_lt_le_incl Hor) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hzs13; intros H.
apply (rngl_opp_lt_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
rewrite H in Haov13; clear H.
destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
  generalize Hzs1; intros H.
  apply rngl_leb_le in H.
  rewrite H in Haov13 |-*; clear H.
  clear Haov13.
  apply (rngl_ltb_ge Hor).
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    apply angle_add_overflow_le_lemma_111; try easy.
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  change_angle_sub_r Hic Hon Hop Hed θ1 angle_right.
  sin_cos_add_sub_right_hyp Hic Hon Hop Hzs12.
  sin_cos_add_sub_right_hyp Hic Hon Hop Hc1z.
  sin_cos_add_sub_right_hyp Hic Hon Hop Hzs1.
  sin_cos_add_sub_right_hyp Hic Hon Hop Hzs13.
  sin_cos_add_sub_right_goal Hic Hon Hop.
  apply (rngl_le_0_sub Hop Hor).
  destruct (rngl_le_dec Hor (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
    exfalso.
    change_angle_sub_r Hic Hon Hop Hed θ2 angle_right.
    sin_cos_add_sub_right_hyp Hic Hon Hop Hzs2.
    sin_cos_add_sub_right_hyp Hic Hon Hop H23.
    sin_cos_add_sub_right_hyp Hic Hon Hop Hzs12.
    sin_cos_add_sub_right_hyp Hic Hon Hop Hc2z.
    apply (rngl_nle_gt Hor) in Hzs12.
    apply Hzs12; clear Hzs12.
    apply (rngl_sin_add_nonneg Hop); try easy.
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nle_gt Hor) in Hzc2.
  move Hzs2 at bottom; move Hzs3 at bottom; move Hc1z at bottom.
  move Hzs1 at bottom.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
    apply rngl_sin_sub_nonneg_sin_le_sin; try easy. {
      apply (rngl_sin_add_nonneg Hop); try easy.
      now apply (rngl_lt_le_incl Hor).
      now apply (rngl_lt_le_incl Hor).
    } {
      now apply (rngl_lt_le_incl Hor).
    } {
      rewrite (angle_add_comm Hic).
      rewrite (angle_add_sub Hic Hon Hop Hed).
      now apply (rngl_lt_le_incl Hor).
    }
  }
  exfalso.
  apply (rngl_nle_gt Hor) in Hc3z.
  change_angle_sub_r Hic Hon Hop Hed θ3 angle_right.
  sin_cos_add_sub_right_hyp Hic Hon Hop Hzs13.
  sin_cos_add_sub_right_hyp Hic Hon Hop H23.
  sin_cos_add_sub_right_hyp Hic Hon Hop Hzs3.
  sin_cos_add_sub_right_hyp Hic Hon Hop Hc3z.
  apply (rngl_nle_gt Hor) in Hzs13.
  apply Hzs13; clear Hzs13.
  apply (rngl_sin_add_nonneg Hop); try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hs1z.
exfalso.
generalize Hs1z; intros H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
rewrite H in Haov13; clear H.
apply (rngl_ltb_ge Hor) in Haov13.
apply (rngl_le_opp_r Hop Hor) in Haov13.
move Hzs2 at bottom; move Hzs3 at bottom.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzs1| Hc1z]. {
  change_angle_add_r Hic Hon Hop Hed θ1 angle_right.
  sin_cos_add_sub_right_hyp Hic Hon Hop Hzs12.
  sin_cos_add_sub_right_hyp Hic Hon Hop Haov13.
  sin_cos_add_sub_right_hyp Hic Hon Hop Hs1z.
  sin_cos_add_sub_right_hyp Hic Hon Hop Hzs13.
  sin_cos_add_sub_right_hyp Hic Hon Hop Hzs1.
  move Hs1z at bottom.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
    apply (rngl_nlt_ge Hor) in Haov13.
    apply Haov13; clear Haov13.
    apply (rngl_add_nonneg_pos Hor); [ easy | ].
    now apply (rngl_sin_add_pos_1 Hic Hon Hop Hed).
  }
  apply (rngl_nle_gt Hor) in Hc3z.
  change_angle_sub_r Hic Hon Hop Hed θ3 angle_right.
  sin_cos_add_sub_right_hyp Hic Hon Hop Hzs13.
  sin_cos_add_sub_right_hyp Hic Hon Hop H23.
  sin_cos_add_sub_right_hyp Hic Hon Hop Haov13.
  sin_cos_add_sub_right_hyp Hic Hon Hop Hzs3.
  sin_cos_add_sub_right_hyp Hic Hon Hop Hc3z.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    apply Bool.not_true_iff_false in Haov12.
    apply Haov12; clear Haov12.
    progress unfold angle_add_overflow.
    rewrite (angle_add_sub_assoc Hop).
    rewrite <- (angle_add_sub_swap Hic Hop).
    progress unfold angle_ltb.
    rewrite (rngl_sin_sub_straight_r Hon Hop).
    do 2 rewrite (rngl_sin_sub_right_r Hon Hop).
    rewrite (rngl_opp_involutive Hop).
    generalize Hzs12; intros H.
    apply (rngl_nle_gt Hor) in H.
    apply rngl_leb_nle in H.
    rewrite H; clear H.
    generalize Hs1z; intros H.
    apply (rngl_opp_lt_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply (rngl_nle_gt Hor) in H.
    apply rngl_leb_nle in H.
    rewrite H; clear H.
    rewrite (rngl_cos_sub_straight_r Hon Hop).
    do 2 rewrite (rngl_cos_sub_right_r Hon Hop).
    apply rngl_ltb_lt.
    apply (rngl_lt_opp_l Hop Hor).
    apply (rngl_add_pos_nonneg Hor); [ | easy ].
    now apply (rngl_sin_add_pos_1 Hic Hon Hop Hed).
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  change_angle_sub_r Hic Hon Hop Hed θ2 angle_right.
  sin_cos_add_sub_right_hyp Hic Hon Hop Hzs12.
  sin_cos_add_sub_right_hyp Hic Hon Hop H23.
  sin_cos_add_sub_right_hyp Hic Hon Hop Hzs2.
  sin_cos_add_sub_right_hyp Hic Hon Hop Hc2z.
  apply Bool.not_true_iff_false in Haov12.
  apply Haov12; clear Haov12.
  progress unfold angle_add_overflow.
  rewrite (angle_add_sub_assoc Hop).
  rewrite (angle_add_assoc Hop).
  rewrite <- (angle_add_sub_swap Hic Hop).
  rewrite (angle_sub_add Hic Hon Hop Hed).
  progress unfold angle_ltb.
  rewrite (rngl_sin_sub_straight_r Hon Hop).
  rewrite (rngl_sin_sub_right_r Hon Hop).
  generalize Hzs12; intros H.
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_nle_gt Hor) in H.
  apply rngl_leb_nle in H.
  rewrite H; clear H.
  generalize Hs1z; intros H.
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_nle_gt Hor) in H.
  apply rngl_leb_nle in H.
  rewrite H; clear H.
  rewrite (rngl_cos_sub_straight_r Hon Hop).
  rewrite (rngl_cos_sub_right_r Hon Hop).
  apply rngl_ltb_lt.
  apply (rngl_lt_opp_l Hop Hor).
  cbn.
  rewrite <- (rngl_add_sub_swap Hop).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_add_pos_nonneg Hor). {
    now apply (rngl_mul_pos_pos Hop Hor Hii).
  }
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply (rngl_sin_bound Hon Hop Hiv Hic Hed Hor).
}
apply (rngl_nle_gt Hor) in Hc1z.
change_angle_add_r Hic Hon Hop Hed θ1 angle_straight.
sin_cos_add_sub_straight_hyp Hic Hon Hop Hzs12.
sin_cos_add_sub_straight_hyp Hic Hon Hop Haov13.
sin_cos_add_sub_straight_hyp Hic Hon Hop Hs1z.
sin_cos_add_sub_straight_hyp Hic Hon Hop Hzs13.
sin_cos_add_sub_straight_hyp Hic Hon Hop Hc1z.
rewrite (rngl_add_opp_r Hop) in Haov13.
rewrite <- (rngl_opp_add_distr Hop) in Haov13.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Haov13.
move Hs1z at bottom.
destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
  exfalso.
  apply (rngl_nle_gt Hor) in Hzs13.
  apply Hzs13; clear Hzs13.
  apply (rngl_sin_add_nonneg Hop); try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hc3z.
change_angle_sub_r Hic Hon Hop Hed θ3 angle_right.
sin_cos_add_sub_right_hyp Hic Hon Hop Hzs13.
sin_cos_add_sub_right_hyp Hic Hon Hop H23.
sin_cos_add_sub_right_hyp Hic Hon Hop Haov13.
sin_cos_add_sub_right_hyp Hic Hon Hop Hzs3.
sin_cos_add_sub_right_hyp Hic Hon Hop Hc3z.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  exfalso.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  apply (rngl_sin_add_nonneg Hop); try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hc2z.
change_angle_sub_r Hic Hon Hop Hed θ2 angle_right.
sin_cos_add_sub_right_hyp Hic Hon Hop Hzs12.
sin_cos_add_sub_right_hyp Hic Hon Hop H23.
sin_cos_add_sub_right_hyp Hic Hon Hop Hzs2.
sin_cos_add_sub_right_hyp Hic Hon Hop Hc2z.
rewrite (angle_add_sub_swap Hic Hop) in Haov12.
rewrite <- (angle_sub_sub_distr Hic Hop) in Haov12.
rewrite (angle_straight_sub_right Hon Hop) in Haov12.
apply Bool.not_true_iff_false in Haov12.
apply Haov12; clear Haov12.
progress unfold angle_add_overflow.
rewrite (angle_add_sub_assoc Hop).
rewrite <- (angle_add_sub_swap Hic Hop).
rewrite (angle_sub_sub_swap Hic Hop).
progress unfold angle_ltb.
do 2 rewrite (rngl_sin_sub_straight_r Hon Hop).
rewrite (rngl_sin_sub_right_r Hon Hop).
rewrite (rngl_opp_involutive Hop).
generalize Hzs12; intros H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
rewrite H; clear H.
generalize Hs1z; intros H.
apply (rngl_opp_lt_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
rewrite H; clear H.
do 2 rewrite (rngl_cos_sub_straight_r Hon Hop).
rewrite (rngl_cos_sub_right_r Hon Hop).
apply rngl_ltb_lt.
apply -> (rngl_opp_lt_compat Hop Hor).
change_angle_sub_l Hic Hon Hop Hed θ2 angle_right.
sin_cos_add_sub_right_hyp Hic Hon Hop Hzs12.
sin_cos_add_sub_right_hyp Hic Hon Hop H23.
sin_cos_add_sub_right_hyp Hic Hon Hop Hzs2.
sin_cos_add_sub_right_hyp Hic Hon Hop Hc2z.
sin_cos_add_sub_right_goal Hic Hon Hop.
rewrite (rngl_cos_sub_comm Hic Hop).
apply (rngl_cos_lt_rngl_cos_sub); try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
apply angle_add_le_mono_l_lemma_39; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
Qed.
