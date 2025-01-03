(* derivation of trigonometric functions *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.RingLike.

Require Import Trigo.RealLike.
Require Import Trigo.Angle.
Require Import Trigo.AngleDiv2.
Require Import Trigo.TrigoWithoutPiExt.
Require Import Trigo.Angle_order.
Require Import Trigo.AngleDivNat.
Require Import Trigo.AngleAddLeMonoL.
Require Import Trigo.AngleDiv2Add.
Require Import Work4.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

(* to be completed
Theorem rngl_cos_derivative :
  is_derivative angle_eucl_dist rngl_dist angle_lt_sub
    rngl_cos (λ θ, (- rngl_sin θ)%L).
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros θ₀ ε Hε.
  rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
apply is_derivative_iff.
intros θ₀ ε Hε.
destruct (angle_eq_dec θ₀ 0) as [Htz| Htz]. {
  subst θ₀.
  cbn.
  exists angle_right, ε.
  split; [ easy | ].
  progress unfold angle_lt_sub.
  intros dθ Hzθ Hdθ.
  rewrite angle_sub_0_r in Hzθ.
  rewrite (rngl_opp_0 Hop).
  rewrite rngl_cos_angle_eucl_dist.
  rewrite (rngl_sub_sub_swap Hop).
  rewrite (rngl_sub_diag Hos).
  rewrite (rngl_sub_0_l Hop).
  progress unfold rngl_dist.
  rewrite (rngl_sub_0_r Hos).
  rewrite (rngl_div_opp_l Hop Hiv).
  rewrite (rngl_abs_opp Hop Hor).
  rewrite (rngl_div_div_swap Hic Hiv).
  progress unfold rngl_squ.
  rewrite (rngl_mul_div Hi1). 2: {
    intros H; rewrite H in Hdθ.
    destruct Hdθ as (H1, _).
    now apply (rngl_lt_irrefl Hor) in H1.
  }
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
      apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
    }
    apply angle_eucl_dist_nonneg.
  }
  apply (rngl_lt_div_l Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  eapply (rngl_lt_le_trans Hor _ ε); [ easy | ].
  rewrite <- (rngl_mul_1_r Hon ε) at 1.
  apply (rngl_mul_le_mono_pos_l Hop Hor Hii); [ easy | ].
  apply (rngl_le_add_l Hor).
  apply (rngl_0_le_1 Hon Hos Hor).
}
destruct (angle_eq_dec θ₀ angle_straight) as [Hts| Hts]. {
  subst θ₀.
  cbn.
  exists angle_right, ε.
  split; [ easy | ].
  progress unfold angle_lt_sub.
  intros dθ Hzθ Hdθ.
  rewrite (rngl_sub_opp_r Hop).
  rewrite (rngl_opp_0 Hop).
About rngl_cos_angle_eucl_dist.
...
Search (angle_eucl_dist _ angle_straight).
...
Search (angle_eucl_dist _ 0).
  rewrite rngl_cos_angle_eucl_dist.
  rewrite (rngl_sub_sub_swap Hop).
  rewrite (rngl_sub_diag Hos).
  rewrite (rngl_sub_0_l Hop).
  progress unfold rngl_dist.
  rewrite (rngl_sub_0_r Hos).
  rewrite (rngl_div_opp_l Hop Hiv).
  rewrite (rngl_abs_opp Hop Hor).
  rewrite (rngl_div_div_swap Hic Hiv).
  progress unfold rngl_squ.
  rewrite (rngl_mul_div Hi1). 2: {
    intros H; rewrite H in Hdθ.
    destruct Hdθ as (H1, _).
    now apply (rngl_lt_irrefl Hor) in H1.
  }
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    apply (rngl_div_nonneg Hon Hop Hiv Hor). 2: {
      apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
    }
    apply angle_eucl_dist_nonneg.
  }
  apply (rngl_lt_div_l Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  eapply (rngl_lt_le_trans Hor _ ε); [ easy | ].
  rewrite <- (rngl_mul_1_r Hon ε) at 1.
  apply (rngl_mul_le_mono_pos_l Hop Hor Hii); [ easy | ].
  apply (rngl_le_add_l Hor).
  apply (rngl_0_le_1 Hon Hos Hor).
}
...
progress unfold angle_lt_sub.
enough (H :
  ∃ η ζ, (0 < ζ)%L ∧
  ∀ dθ,
  (0 < dθ < η)%A
  → (0 < angle_eucl_dist dθ 0 < ζ)%L
  → (rngl_dist
        ((rngl_cos (θ₀ + dθ) - rngl_cos θ₀) / angle_eucl_dist dθ 0)
        (- rngl_sin θ₀) < ε)%L). {
  destruct H as (η & ζ & Hζ & Hd).
  exists η, ζ.
  split; [ easy | ].
  intros θ Hη Hθ.
  remember (θ - θ₀)%A as dθ eqn:H.
  symmetry in H.
  apply angle_sub_move_r in H.
  subst θ.
  specialize (Hd dθ Hη).
  rewrite angle_eucl_dist_move_0_r in Hθ |-*.
  rewrite angle_add_sub in Hθ |-*.
  rewrite angle_add_comm.
  now apply Hd.
}
specialize rngl_sin_is_continuous as Hsc.
progress unfold continuous in Hsc.
progress unfold continuous_at in Hsc.
progress unfold is_limit_when_tending_to in Hsc.
specialize (Hsc θ₀ ε Hε).
destruct Hsc as (ζ1 & Hζ1 & Hsc).
progress unfold rngl_dist in Hsc.
move ζ1 before ε.
...
destruct (angle_lt_dec θ₀ angle_straight) as [Hts| Hts]. {
  remember (angle_eucl_dist angle_right 0) as x.
  remember (angle_eucl_dist θ₀ 0) as y.
  exists angle_right.
  exists (rngl_min4 x y (angle_eucl_dist θ₀ angle_straight) ζ1).
  subst x y.
  split. {
    apply rngl_min_glb_lt; [ | easy ].
    apply rngl_min_glb_lt. {
      apply rngl_min_glb_lt. {
        apply angle_eucl_dist_pos_angle_neq.
        apply neq_angle_neq; intros H.
        injection H; clear H; intros H1 H2.
        now apply (rngl_1_neq_0_iff Hon) in H1.
      }
      now apply angle_eucl_dist_pos_angle_neq.
    }
    apply angle_eucl_dist_pos_angle_neq.
    intros H.
    rewrite H in Hts.
    now apply angle_lt_irrefl in Hts.
  }
  intros dθ Hdθ Hζ.
  destruct Hζ as (H1, H2).
  apply (rngl_min_glb_lt_iff Hor) in H2.
  destruct H2 as (H2, H4).
  apply (rngl_min_glb_lt_iff Hor) in H2.
  destruct H2 as (H2, H3).
  apply (rngl_min_glb_lt_iff Hor) in H2.
  destruct H2 as (H2, H5).
  progress unfold rngl_dist.
  rewrite (rngl_sub_opp_r Hop).
  rewrite rngl_cos_sub_cos.
  remember (angle_add_overflow (θ₀ + dθ) θ₀) as ovt eqn:Hovt.
  remember (θ₀ + dθ <? θ₀)%A as tt eqn:Htt.
  symmetry in Hovt, Htt.
  destruct (angle_le_dec dθ angle_straight) as [Htds| Htds]. {
    destruct tt. {
      exfalso.
      apply angle_nle_gt in Htt.
      apply Htt; clear Htt.
      (* lemma *)
      rewrite <- (angle_add_0_r θ₀) at 1.
      apply angle_add_le_mono_l; [ | apply angle_nonneg ].
      now apply angle_add_not_overflow_lt_straight_le_straight.
    }
    apply angle_ltb_ge in Htt.
    rewrite angle_add_sub_swap.
    rewrite angle_sub_diag.
    rewrite angle_add_0_l.
    rewrite angle_add_0_r.
    rewrite (angle_add_comm θ₀).
    rewrite <- angle_add_assoc.
    rewrite <- angle_mul_2_l.
    destruct ovt. 2: {
      rewrite angle_add_0_r.
      rewrite angle_div_2_add_not_overflow. 2: {
        rewrite angle_mul_2_l.
        rewrite angle_add_comm in Hovt.
        rewrite angle_add_not_overflow_move_add; [ easy | | easy ].
        rewrite angle_add_overflow_comm.
        apply angle_ltb_ge in Htt.
        now rewrite <- angle_add_overflow_equiv2.
      }
      rewrite (rngl_sin_angle_eucl_dist' (dθ/₂)). 2: {
        apply angle_div_2_le_straight.
      }
      rewrite angle_mul_2_div_2; [ | easy ].
      rewrite angle_div_2_mul_2.
      rewrite (rngl_mul_div_assoc Hiv).
      rewrite (rngl_div_opp_l Hop Hiv).
      rewrite (rngl_div_div_swap Hic Hiv).
      rewrite (rngl_mul_div Hi1). 2: {
        intros H.
        rewrite H in H1.
        now apply (rngl_lt_irrefl Hor) in H1.
      }
      rewrite <- (rngl_div_opp_l Hop Hiv).
      rewrite (rngl_mul_comm Hic).
      rewrite <- (rngl_mul_opp_l Hop).
      rewrite (rngl_mul_div Hi1). 2: {
        apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
      }
      rewrite <- (rngl_abs_opp Hop Hor).
      rewrite (rngl_opp_add_distr Hop).
      rewrite (rngl_sub_opp_r Hop).
      rewrite (rngl_add_opp_l Hop).
      rewrite angle_add_comm.
      specialize (Hsc (θ₀ + dθ /₂))%A.
      rewrite angle_eucl_dist_move_0_r in Hsc.
      rewrite angle_add_comm, angle_add_sub in Hsc.
      rewrite angle_add_comm.
      apply Hsc.
      apply (rngl_le_lt_trans Hor _ (angle_eucl_dist dθ 0)); [ | easy ].
      apply angle_le_angle_eucl_dist_le; [ | easy | ]. 2: {
        apply angle_div_2_le.
      }
      apply angle_div_2_le_straight.
    }
    rewrite angle_div_2_add_overflow. 2: {
      rewrite angle_mul_2_l.
      rewrite angle_add_comm in Hovt.
      rewrite angle_add_overflow_move_add; [ easy | | easy ].
      now apply angle_lt_straight_add_same_not_overflow.
    }
    rewrite <- angle_add_assoc.
    rewrite angle_straight_add_straight.
    rewrite angle_add_0_r.
    rewrite angle_mul_2_div_2; [ | easy ].
    rewrite (rngl_sin_angle_eucl_dist' (dθ/₂)). 2: {
      apply angle_div_2_le_straight.
    }
    rewrite angle_div_2_mul_2.
    rewrite (rngl_mul_comm Hic).
    rewrite rngl_mul_assoc.
    rewrite (rngl_div_mul Hon Hiv). 2: {
      apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
    }
    rewrite (rngl_mul_comm Hic).
    rewrite (rngl_div_opp_l Hop Hiv).
    rewrite (rngl_mul_div Hi1). 2: {
      intros H.
      rewrite H in H1.
      now apply (rngl_lt_irrefl Hor) in H1.
    }
    rewrite <- (rngl_abs_opp Hop Hor).
    rewrite (rngl_opp_add_distr Hop).
    rewrite (rngl_sub_opp_r Hop).
    rewrite (rngl_add_opp_l Hop).
    apply Hsc.
    rewrite angle_eucl_dist_move_0_r.
    rewrite angle_add_sub.
    apply (rngl_le_lt_trans Hor _ (angle_eucl_dist dθ 0)); [ | easy ].
    apply angle_le_angle_eucl_dist_le; [ | easy | ]. 2: {
      apply angle_div_2_le.
    }
    apply angle_div_2_le_straight.
  }
  exfalso.
  apply Htds; clear Htds.
  apply (angle_le_trans _ angle_right).
  now apply angle_lt_le_incl.
  apply angle_right_le_straight.
} {
 apply angle_nlt_ge in Hts.
 remember (angle_eucl_dist angle_right 0) as x.
 remember (angle_eucl_dist θ₀ 0) as y.
 exists angle_right.
 exists (rngl_min4 x y (angle_eucl_dist θ₀ angle_straight) ζ1).
 subst x y.
 split. {
  apply rngl_min_glb_lt; [ | easy ].
  apply rngl_min_glb_lt. {
      apply rngl_min_glb_lt. {
        apply angle_eucl_dist_pos_angle_neq.
        apply neq_angle_neq; intros H.
        injection H; clear H; intros H1 H2.
        now apply (rngl_1_neq_0_iff Hon) in H1.
      }
      now apply angle_eucl_dist_pos_angle_neq.
    }
    apply angle_eucl_dist_pos_angle_neq.
    intros H.
    rewrite H in Hts.
...
    now apply angle_lt_irrefl in Hts.
  }
  intros dθ Hdθ Hζ.
  destruct Hζ as (H1, H2).
  apply (rngl_min_glb_lt_iff Hor) in H2.
  destruct H2 as (H2, H4).
  apply (rngl_min_glb_lt_iff Hor) in H2.
  destruct H2 as (H2, H3).
  apply (rngl_min_glb_lt_iff Hor) in H2.
  destruct H2 as (H2, H5).
  progress unfold rngl_dist.
  rewrite (rngl_sub_opp_r Hop).
  rewrite rngl_cos_sub_cos.
  remember (angle_add_overflow (θ₀ + dθ) θ₀) as ovt eqn:Hovt.
  remember (θ₀ + dθ <? θ₀)%A as tt eqn:Htt.
  symmetry in Hovt, Htt.
  destruct (angle_le_dec dθ angle_straight) as [Htds| Htds]. {
...
    remember (angle_add_overflow dθ (2 * θ₀)) as ovd eqn:Hovd.
    symmetry in Hovd.
    rewrite angle_add_overflow_comm in Hovd.
    rewrite angle_mul_2_l in Hovd.
    move Hovd before Hovt.
    destruct ovd. {
      rewrite <- angle_add_overflow_equiv2 in Hovt, Hovd.
      progress unfold angle_add_overflow2 in Hovt, Hovd.
      rewrite angle_add_add_swap in Hovt.
      do 2 rewrite rngl_sin_add_straight_r.
      do 2 rewrite (rngl_mul_opp_r Hop).
      rewrite (rngl_mul_opp_l Hop).
      rewrite (rngl_opp_involutive Hop).
      rewrite (rngl_div_opp_l Hop Hiv).
      rewrite (rngl_sin_angle_eucl_dist' (dθ /₂)). 2: {
        apply angle_div_2_le_straight.
      }
      rewrite angle_div_2_mul_2.
      rewrite (rngl_mul_div_assoc Hiv).
      rewrite (rngl_div_div_swap Hic Hiv).
      rewrite (rngl_mul_div Hi1). 2: {
        intros H.
        rewrite H in H1.
        now apply (rngl_lt_irrefl Hor) in H1.
      }
      rewrite (rngl_mul_comm Hic).
      rewrite (rngl_mul_div Hi1). 2: {
        apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
      }
      rewrite <- (rngl_abs_opp Hop Hor).
      rewrite (rngl_opp_add_distr Hop).
      rewrite (rngl_sub_opp_r Hop).
      rewrite (rngl_add_opp_l Hop).
      apply angle_ltb_ge in Hovt.
      move Hts at bottom.
      progress unfold angle_leb in Hovt.
      progress unfold angle_ltb in Hovd, Htt, Htds, Hts.
      cbn - [ angle_add ] in Hovt, Hovd, Htt, Htds, Hts.
      rewrite (rngl_leb_refl Hor) in Htds, Hts.
      remember (0 ≤? rngl_sin θ₀)%L as zst eqn:Hzst.
      symmetry in Hzst.
      destruct zst; [ | easy ].
      apply rngl_leb_le in Hzst.
      apply rngl_ltb_lt in Hts.
      remember (0 ≤? rngl_sin (θ₀ + dθ))%L as zstd eqn:Hztd.
      symmetry in Hztd.
      destruct zstd; [ | easy ].
      apply rngl_leb_le in Hztd.
      apply rngl_ltb_lt in Htt.
      remember (0 ≤? rngl_sin dθ)%L as zsd eqn:Hzsd.
      symmetry in Hzsd.
      destruct zsd. {
        exfalso.
        apply rngl_ltb_lt in Htds.
        apply rngl_nle_gt in Htds.
        apply Htds, rngl_cos_bound.
      }
      clear Htds.
      apply rngl_leb_gt in Hzsd.
      remember (0 ≤? rngl_sin (θ₀ + θ₀))%L as zstt eqn:Hzstt.
      symmetry in Hzstt.
      destruct zstt. {
        apply rngl_leb_le in Hzstt.
        remember (0 ≤? rngl_sin (θ₀ + θ₀ + dθ))%L as zsttd eqn:Hzsttd.
        symmetry in Hzsttd.
        destruct zsttd; [ | easy ].
        apply rngl_leb_le in Hzsttd, Hovt.
        apply rngl_ltb_lt in Hovd.
        destruct (rngl_le_dec Hor 0 (rngl_cos dθ)) as [Hzcd| Hzcd]. {
(*1
    change_angle_add_r dθ angle_right.
    progress sin_cos_add_sub_right_hyp T Hovt.
    progress sin_cos_add_sub_right_hyp T Hzsttd.
    progress sin_cos_add_sub_right_hyp T Hztd.
    progress sin_cos_add_sub_right_hyp T Hovd.
    progress sin_cos_add_sub_right_hyp T Hzsd.
    progress sin_cos_add_sub_right_hyp T Htt.
    progress sin_cos_add_sub_right_hyp T Hzcd.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hzc| Hzc]. {
      rewrite angle_div_2_sub.
      remember (angle_right ≤? dθ)%A as rd eqn:Hrd.
      symmetry in Hrd.
      destruct rd. {
        progress unfold angle_leb in Hrd.
        cbn in Hrd.
        rewrite (rngl_0_leb_1 Hon Hos Hor) in Hrd.
        generalize Hzcd; intros H.
        apply rngl_leb_le in H.
        rewrite H in Hrd; clear H.
        apply rngl_leb_le in Hrd.
        now apply rngl_nlt_ge in Hrd.
      }
      clear Hrd.
      rewrite angle_add_add_swap.
      rewrite rngl_sin_add_straight_r.
      rewrite <- angle_add_sub_swap.
rewrite rngl_sin_sub_anticomm.
rewrite (rngl_opp_involutive Hop).
apply Hsc.
rewrite angle_eucl_dist_move_0_r.
rewrite <- angle_sub_add_distr.
rewrite <- angle_eucl_dist_move_0_r.
...1
*)
          change_angle_opp dθ.
          progress sin_cos_opp_hyp T Hovt.
          progress sin_cos_opp_hyp T Hzsttd.
          progress sin_cos_opp_hyp T Hztd.
          progress sin_cos_opp_hyp T Hovd.
          progress sin_cos_opp_hyp T Hzsd.
          progress sin_cos_opp_hyp T Htt.
          progress sin_cos_opp_hyp T Hzcd.
          destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hzc| Hzc]. {
            rewrite angle_opp_div_2.
            remember (dθ =? 0)%A as dz eqn:Hdz.
            symmetry in Hdz.
            destruct dz. {
              apply angle_eqb_eq in Hdz; subst dθ.
              now apply (rngl_lt_irrefl Hor) in Hzsd.
            }
            apply angle_eqb_neq in Hdz.
            rewrite angle_add_add_swap.
            rewrite rngl_sin_add_straight_r.
            rewrite angle_eucl_dist_opp_0 in H1, H2, H3, H4, H5.
            rewrite angle_add_opp_l.
            rewrite <- rngl_sin_sub_anticomm.
            move Hzcd after Hzsd.
            move Hzst after Hzcd.
            move Hzc after Hzst.
            move Hztd after Hzsd.
            move Hzsttd after Hzstt.
clear Hzstt Hzsttd Hovd Htt Hovt.
move Hη1 before Hε.
move Hdz before Htz.
move dθ before θ₀.
exfalso.
...
            apply Hsc.
            rewrite angle_eucl_dist_move_0_r.
            rewrite <- angle_sub_add_distr.
            rewrite <- angle_eucl_dist_move_0_r.
...
      rewrite angle_add_comm.
      rewrite angle_add_opp_r.
      rewrite rngl_sin_sub_sin.
...
      apply Hsc.
      rewrite angle_eucl_dist_move_0_r.
      rewrite angle_add_sub.
...
      apply (rngl_le_lt_trans Hor _ (angle_eucl_dist dθ 0)). {
(* ah bin non, c'est pas sûr *)
...
        apply angle_le_angle_eucl_dist_le; [ | | ]. 2: {
...
        apply angle_le_angle_eucl_dist_le; [ | easy | ]. 2: {
        apply angle_div_2_le.
      }
      apply angle_div_2_le_straight.
    }
    eapply (rngl_lt_le_trans Hor); [ apply Hdθ | ].
    apply (rngl_le_min_r Hor).
...
        move Hovt at bottom.
        rewrite <- angle_add_overflow_equiv2 in Hovt.
        progress unfold angle_add_overflow2 in Hovt.
...
        exfalso.
        apply angle_nle_gt in Hovt.
        apply Hovt; clear Hovt.
        rewrite angle_add_opp_l.
...
progress unfold angle_sub.
rewrite angle_add_comm.
rewrite <- angle_sub_opp_r.
rewrite <- angle_opp_add_distr.
...
apply angle_opp_le_compat_if. 2: {
  rewrite angle_add_opp_l.
Search (_ - _ ≤ _ - _)%A.
  rewrite <- (angle_sub_0_r dθ) at 2.
  apply angle_sub_le_mono_l.
2: {
...
intros H.
rewrite angle_add_opp_l in H.
apply -> angle_sub_move_0_r in H.
subst dθ.
rewrite angle_mul_2_l in Hzstd.
rewrite angle_sub_add_distr in Hzstd.
...
        rewrite <- angle_sub_0_l.
...
        apply angle_sub_le_mono_r.
Search (_ ≤ _ - _)%A.
Search (_ < _ - _)%A.
Search (_ - _ < _ - _)%A.
Search (_ - _ ≤ _ - _)%A.
...
Search (angle_eucl_dist _ _ ≤ angle_eucl_dist _ _)%L.
(*
apply angle_le_angle_eucl_dist_le. {
Search (_ - _ ≤ _)%A.
...
*)
apply rngl_cos_le_iff_angle_eucl_le.
rewrite rngl_cos_sub_straight_r.
rewrite rngl_cos_sub_right_r.
cbn.
...
apply angle_eucl_dist_lt_angle_eucl_dist.
...
apply rngl_cos_lt_angle_eucl_dist_lt. {
  now apply (rngl_lt_le_incl Hor).
}
rewrite angle_sub_0_l.
rewrite rngl_cos_opp.
rewrite rngl_cos_sub_right_r.
Search (angle_eucl_dist _ _ < _)%L.
...
Search (0 < rngl_sin _)%L.
Search (angle_straight ≤ _)%A.
Search (_ ≤ angle_straight)%A.
  apply rngl_sin_nonneg_angle_le_straight in Hsd.


...
          progress unfold rngl_dist in Hsc.
          rewrite rngl_sin_add_sin.
          rewrite (angle_add_comm θ₀).
          rewrite angle_add_sub.
...
      apply angle_ltb_ge in Htt.
...
      exfalso.
      apply angle_nle_gt in Htds.
      apply Htds; clear Htds.
...
    exfalso.
    destruct Hdθ as (_, H1).
    apply rngl_nle_gt in H1.
    apply H1; clear H1.
... à voir...
    apply (rngl_min_le_iff Hor).
    left.
Search (angle_eucl_dist _ _ < angle_eucl_dist _ _)%L.
    apply angle_nle_gt in Htds.
    apply Htds; clear Htds.
...
enough (H :
  ∃ η : T, (0 < η)%L ∧
  ∀ dθ : angle T,
  (0 < angle_eucl_dist dθ 0 < η)%L
  → (rngl_dist
       ((rngl_cos (θ₀ + dθ) - rngl_cos θ₀) / angle_eucl_dist dθ 0)
       (- rngl_sin θ₀) < ε)%L). {
  destruct H as (η & Hη & Hd).
  exists η.
  move η before ε.
  split; [ easy | ].
  intros dθ Hdθ.
  do 2 rewrite rngl_cos_angle_eucl_dist.
  rewrite (rngl_sub_sub_distr Hop).
  rewrite (rngl_sub_sub_swap Hop).
  rewrite (rngl_sub_diag Hos).
  rewrite (rngl_sub_0_l Hop).
  rewrite (rngl_add_opp_l Hop).
  rewrite <- (rngl_div_sub_distr_r Hop Hiv).
  progress unfold rngl_dist.
  rewrite (rngl_div_div_swap Hic Hiv).
  rewrite (rngl_sub_opp_r Hop).
  destruct (angle_le_dec θ₀ angle_straight) as [Hts| Hts]. {
    rewrite rngl_sin_angle_eucl_dist'; [ | easy ].
    rewrite <- (rngl_div_add_distr_r Hiv).
    rewrite angle_mul_2_l.
    rewrite (rngl_abs_div Hon Hop Hiv Hed Hor). 2: {
      apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
    }
    rewrite (rngl_abs_2 Hon Hos Hor).
    apply (rngl_lt_div_l Hon Hop Hiv Hor). {
      apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
    }
    rewrite (rngl_abs_nonneg_eq Hop Hor).
    eapply (rngl_le_lt_trans Hor). {
      apply (rngl_add_le_mono_l Hop Hor).
      apply (angle_eucl_dist_triangular _ θ₀).
    }
    rewrite (angle_eucl_dist_move_0_r (_ + _) θ₀).
    rewrite angle_add_sub.
    rewrite <- (rngl_mul_2_r Hon).
Search (rngl_cos _ - rngl_cos _ = _)%L.
Check rngl_cos_sub_cos.
...
rngl_cos_angle_eucl_dist:
  ∀ {T : Type} {ro : ring_like_op T} {rp : ring_like_prop T} {rl : real_like_prop T} 
    {ac : angle_ctx T} (θ : angle T), rngl_cos θ = (1 - (angle_eucl_dist θ 0)² / 2)%L
rngl_sin_angle_eucl_dist':
  ∀ θ : angle T, (θ ≤ angle_straight)%A → rngl_sin θ = (angle_eucl_dist (2 * θ) 0 / 2)%L
...
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ θ,
  (0 < angle_eucl_dist θ θ₀ < η)%L
  → (rngl_dist
        ((rngl_cos θ - rngl_cos θ₀) / angle_eucl_dist θ θ₀)
        (- rngl_sin θ₀) < ε)%L). {
  destruct H as (η & Hη & Hd).
  exists η.
  move η before ε.
  split; [ easy | ].
  intros θ Hθ.
  do 2 rewrite rngl_cos_angle_eucl_dist.
  rewrite (rngl_sub_sub_distr Hop).
  rewrite (rngl_sub_sub_swap Hop).
  rewrite (rngl_sub_diag Hos).
  rewrite (rngl_sub_0_l Hop).
  rewrite (rngl_add_opp_l Hop).
  rewrite <- (rngl_div_sub_distr_r Hop Hiv).
  progress unfold rngl_dist.
  rewrite (rngl_div_div_swap Hic Hiv).
  rewrite (rngl_sub_opp_r Hop).
  destruct (angle_le_dec θ₀ angle_straight) as [Hts| Hts]. {
    rewrite rngl_sin_angle_eucl_dist'; [ | easy ].
    rewrite <- (rngl_div_add_distr_r Hiv).
    rewrite angle_mul_2_l.
    rewrite (rngl_abs_div Hon Hop Hiv Hed Hor). 2: {
      apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
    }
    rewrite (rngl_abs_2 Hon Hos Hor).
    apply (rngl_lt_div_l Hon Hop Hiv Hor). {
      apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
    }
    rewrite (rngl_abs_nonneg_eq Hop Hor).
    eapply (rngl_le_lt_trans Hor). {
      apply (rngl_add_le_mono_l Hop Hor).
      apply (angle_eucl_dist_triangular _ θ₀).
    }
    rewrite (angle_eucl_dist_move_0_r (_ + _)).
    rewrite angle_add_sub.
    rewrite <- (rngl_mul_2_r Hon).
...
Check angle_eucl_dist_is_2_mul_sin_sub_div_2.
Search (rngl_sin _ = _).
Search (angle_eucl_dist _ _ + _)%L.
(* bof, j'y arrive pas, chuis nul *)
...4
enough (H :
  if (θ₀ <? angle_straight)%A then
    ∃ η : T, (0 < η)%L ∧
    ∀ θ, (0 < angle_eucl_dist θ θ₀ < η)%L
    → (rngl_dist
           ((rngl_cos θ - rngl_cos θ₀) / angle_eucl_dist θ θ₀)
           (- rngl_sin θ₀) < ε)%L
  else
    ∃ η : T, (0 < η)%L ∧
    ∀ θ, (0 < angle_eucl_dist θ θ₀ < η)%L
    → (rngl_dist
           ((rngl_cos θ - rngl_cos θ₀) / angle_eucl_dist θ θ₀)
           (- rngl_sin θ₀) < ε)%L). {
  remember (θ₀ <? angle_straight)%A as tzs eqn:Htzs.
  symmetry in Htzs.
  destruct tzs. {
    exists (angle_eucl_dist θ₀ angle_straight)%L.
    split. {
      apply (rngl_lt_iff Hor).
      split; [ apply angle_eucl_dist_nonneg | ].
      intros H1; symmetry in H1.
      rewrite angle_eucl_dist_separation in H1; subst θ₀.
      now apply angle_lt_irrefl in Htzs.
    }
    intros θ Hθ.
    move θ before θ₀.
    (* todo: define angle_dec? *)
    remember (angle_ltb (θ + angle_right) θ₀) as tr eqn:Htr.
    symmetry in Htr.
    destruct tr. {
      exfalso.
      apply angle_nle_gt in Htr.
      apply Htr; clear Htr.
      progress unfold angle_leb.
      rewrite rngl_sin_add_right_r.
      rewrite rngl_cos_add_right_r.
      generalize Htzs; intros H1.
      apply angle_lt_le_incl in H1.
      apply rngl_sin_nonneg_angle_le_straight in H1.
      apply rngl_leb_le in H1.
      rewrite H1; clear H1.
      remember (0 ≤? rngl_cos θ)%L as zc eqn:Hzc.
      symmetry in Hzc.
      destruct zc; [ | easy ].
      apply rngl_leb_le in Hzc.
      apply rngl_leb_le.
      destruct Hθ as (Hzt, Ht).
      apply angle_eucl_dist_lt_angle_eucl_dist in Ht.
      rewrite rngl_cos_sub_straight_r in Ht.
      apply (rngl_le_opp_l Hop Hor).
      apply (rngl_lt_opp_l Hop Hor) in Ht.
(**)
      remember (θ - θ₀)%A as dθ eqn:Hd.
      apply angle_add_move_r in Hd.
      subst θ.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hzcz| Hzcz]. {
        destruct (rngl_le_dec Hor 0 (rngl_cos dθ)) as [Hzcd| Hzcd]. {
          cbn.
          rewrite rngl_add_add_swap.
          rewrite (rngl_add_mul_l_diag_r Hon).
          apply (rngl_add_nonneg_nonneg Hor). {
            apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
            rewrite rngl_add_comm.
            apply (rngl_le_opp_l Hop Hor).
            apply rngl_sin_bound.
          }
          apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
          apply angle_lt_le_incl in Htzs.
          now apply rngl_sin_nonneg_angle_le_straight in Htzs.
        }
        apply (rngl_nle_gt_iff Hor) in Hzcd.
        destruct (rngl_le_dec Hor 0 (rngl_sin dθ)) as [Hzsd| Hzsd]. {
          exfalso.
          rewrite rngl_cos_add in Hzc.
          apply -> (rngl_le_0_sub Hop Hor) in Hzc.
          apply rngl_nlt_ge in Hzc.
          apply Hzc; clear Hzc.
          eapply (rngl_lt_le_trans Hor _ 0). {
            rewrite (rngl_mul_comm Hic).
            apply (rngl_mul_pos_neg Hop Hor); [ | | easy ]. 2: {
              apply (rngl_lt_iff Hor).
              split; [ easy | ].
              intros H1; symmetry in H1.
              apply eq_rngl_cos_0 in H1.
              destruct H1; subst θ₀. {
                cbn in Ht.
                rewrite rngl_add_0_l in Ht.
                apply (rngl_lt_le_incl Hor) in Ht.
                now apply rngl_nlt_ge in Ht.
              }
              cbn in Ht.
              rewrite rngl_add_0_l in Ht.
              apply (rngl_lt_le_incl Hor) in Ht.
              now apply rngl_nlt_ge in Ht.
            }
            rewrite Bool.orb_true_iff; right.
            rewrite Hi1; cbn.
            apply (rngl_has_eq_dec_or_is_ordered_r Hor).
          }
          apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
          apply angle_lt_le_incl in Htzs.
          now apply rngl_sin_nonneg_angle_le_straight.
        }
        generalize Htzs; intros Hz.
        apply angle_lt_le_incl in Hz.
        apply rngl_sin_nonneg_angle_le_straight in Hz.
        apply (rngl_nle_gt_iff Hor) in Hzsd.
        change_angle_add_r dθ angle_straight.
        progress sin_cos_add_sub_straight_hyp T Hzc.
        progress sin_cos_add_sub_straight_hyp T Ht.
        progress sin_cos_add_sub_straight_hyp T Hzt.
        progress sin_cos_add_sub_straight_hyp T Hzsd.
        progress sin_cos_add_sub_straight_hyp T Hzcd.
        progress sin_cos_add_sub_straight_goal T.
        change_angle_sub_l dθ angle_right.
        progress sin_cos_add_sub_right_hyp T Hzc.
        progress sin_cos_add_sub_right_hyp T Ht.
        progress sin_cos_add_sub_right_hyp T Hzt.
        progress sin_cos_add_sub_right_hyp T Hzsd.
        progress sin_cos_add_sub_right_hyp T Hzcd.
        progress sin_cos_add_sub_right_goal T.
        rewrite (rngl_add_opp_l Hop).
        apply (rngl_le_0_sub Hop Hor).
        rewrite rngl_sin_sub_anticomm in Hzc.
        apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzc.
        rewrite rngl_cos_sub_comm.
        change_angle_sub_l θ₀ angle_right.
        progress sin_cos_add_sub_right_hyp T Hz.
        progress sin_cos_add_sub_right_hyp T Hzcz.
        progress sin_cos_add_sub_right_hyp T Hzc.
        progress sin_cos_add_sub_right_hyp T Ht.
        progress sin_cos_add_sub_right_hyp T Hzt.
        progress sin_cos_add_sub_right_goal T.
        rewrite <- angle_sub_add_distr.
        rewrite rngl_cos_sub_right_l.
        apply -> (rngl_lt_0_sub Hop Hor) in Ht.
(* je crois que c'est faux *)
...
Search (rngl_cos (_ - _) ≤ rngl_cos _)%L.
Search (rngl_cos _ < rngl_cos (_ - _))%L.
...
            apply (rngl_lt_le_incl Hor) in Hzcd.
            now apply (rngl_mul_nonpos_nonneg Hop Hor).
          }
          eapply (rngl_le_lt_trans Hor _ 0). {
            apply (rngl_lt_le_incl Hor) in Hzcd.
            now apply (rngl_mul_nonpos_nonneg Hop Hor).
          }
...
(*
      change_angle_sub_l θ angle_straight.
      rewrite <- angle_sub_add_distr in Ht.
      progress sin_cos_add_sub_straight_hyp T Hzc.
      progress sin_cos_add_sub_straight_hyp T Ht.
      progress sin_cos_add_sub_straight_goal T.
...
*)
      change_angle_add_r θ angle_right.
      rewrite angle_sub_sub_swap in Ht.
      progress sin_cos_add_sub_right_hyp T Hzc.
      progress sin_cos_add_sub_right_hyp T Ht.
      progress sin_cos_add_sub_right_goal T.
...
Search (angle_eucl_dist _ _ < angle_eucl_dist _ _)%L.
...
    rewrite angle_cos_sub_cos_angle_eucl_dist_mul.
    rewrite (rngl_mul_comm Hic).
    rewrite (rngl_mul_div Hi1). 2: {
      destruct Hθ as (Hθ, _).
      apply (rngl_lt_iff Hor) in Hθ.
      destruct Hθ as (_, Hθ).
      now apply not_eq_sym in Hθ.
    }
(*1
    remember (Bool.eqb _ _) as b eqn:Hb.
    symmetry in Hb.
    destruct b. {
      progress unfold rngl_dist.
      rewrite (rngl_sub_opp_r Hop).
      rewrite (rngl_add_opp_l Hop).
      specialize (angle_eucl_dist_is_2_mul_sin_sub_div_2 θ₀ (-θ)) as H1.
      rewrite angle_sub_opp_r in H1.
      rewrite angle_add_comm in H1.
      apply (f_equal (λ x, (x / 2)%L)) in H1.
      rewrite (rngl_mul_comm Hic) in H1.
      rewrite (rngl_mul_div Hi1) in H1. 2: {
        apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
      }
      rewrite <- H1; clear H1.
...1
*)
    assert (Hov : angle_add_overflow θ θ₀ = false). {
(*
rename θ₀ into θ1.
rename θ into θ2.
*)
      rewrite angle_add_overflow_comm.
      apply angle_add_not_overflow_lt_straight_le_straight; [ easy | ].
      destruct Hθ as (_, Hθ).
(*
clear ε Hε H.
     move θ2 before θ1.
*)
      move θ before θ₀.
      move Htzs at bottom.
      rewrite angle_eucl_dist_symmetry in Hθ.
      apply angle_nlt_ge.
      intros Hst.
      apply rngl_nle_gt in Hθ.
      apply Hθ; clear Hθ.
      destruct H as (η & Hzη & H).
      move η before ε.
...
specialize (H θ2).
Inspect 1.
apply (rngl_lt_le_incl Hor).
apply angle_around_straight_eucl_dist; [ easy | ].
(* à voir *)
...
Theorem glop :
  ∀ θ1 θ2 θ3,
  (θ1 < θ2 < θ3)%A
  → (θ3 < θ1 + angle_straight)%A
  → (angle_eucl_dist θ1 θ2 < angle_eucl_dist θ1 θ3)%L.
Proof.
(* en fait c'est faux : par exemple si θ1, θ2 et θ3 sont
   dans le premier quadrant *)
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * (H12, H23) H31.
progress unfold angle_ltb in H12.
progress unfold angle_ltb in H23.
progress unfold angle_ltb in H31.
rewrite rngl_sin_add_straight_r in H31.
rewrite rngl_cos_add_straight_r in H31.
rewrite (rngl_leb_0_opp Hop Hor) in H31.
(*2*)
apply angle_eucl_dist_lt_angle_eucl_dist.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
remember (0 ≤? rngl_sin θ3)%L as zs3 eqn:Hzs3.
symmetry in Hzs1, Hzs2, Hzs3.
destruct zs2. {
  destruct zs1; [ | easy ].
  destruct zs3. {
    apply rngl_ltb_lt in H12, H23.
    apply rngl_leb_le in Hzs1, Hzs2, Hzs3.
    remember (rngl_sin θ1 ≤? 0)%L as s1z eqn:Hs1z.
    symmetry in Hs1z.
    destruct s1z. {
      apply rngl_leb_le in Hs1z.
      apply (rngl_le_antisymm Hor) in Hzs1; [ | easy ].
      clear Hs1z.
      apply eq_rngl_sin_0 in Hzs1.
      destruct Hzs1; subst θ1; [ now do 2 rewrite angle_sub_0_l | ].
      exfalso.
      apply rngl_ltb_lt in H31.
      apply rngl_nle_gt in H31.
      apply H31; clear H31; cbn.
      rewrite (rngl_opp_involutive Hop).
      apply rngl_cos_bound.
    }
    clear H31.
    apply (rngl_leb_gt Hor) in Hs1z.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
      destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
        destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hzc3]. {
          apply (rngl_lt_iff Hor).
          split. {
(*
            do 2 rewrite rngl_cos_sub.
            apply (rngl_le_sub_le_add_r Hop Hor).
            rewrite <- (rngl_add_sub_assoc Hop).
            rewrite <- (rngl_mul_sub_distr_l Hop).
            apply (rngl_le_add_le_sub_l Hop Hor).
            rewrite <- (rngl_mul_sub_distr_l Hop).
            destruct (rngl_le_dec Hor (rngl_cos θ1) (rngl_cos θ2))
                as [Hc12| Hc12]. {
            apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
*)
rngl_cos _ ≤ rngl_cos _)%L.
...
      do 2 rewrite rngl_cos_sub.
      apply (rngl_add_lt_compat Hop Hor). {
        now apply (rngl_mul_lt_mono_pos_l Hop Hor Hii).
      }
      apply (rngl_mul_lt_mono_pos_l Hop Hor Hii); [ easy | ].
...
      apply (rngl_lt_trans Hor _ (rngl_sin θ2)). {
        apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff; try easy.
...
      apply (rngl_lt_le_incl Hor).
      now apply glop.
...
specialize (angle_eucl_dist_triangular θ1 angle_straight θ2) as H1.
apply (rngl_nle_gt_iff Hor) in Hθ.
apply Hθ; clear Hθ.
eapply (rngl_le_trans Hor).
...
      assert (H1 : (angle_straight - θ1 < θ2 - θ1)%A). {
...
        destruct Hθ as (H1, H2).
        move Htzs before Hst.
        (* lemma *)
        progress unfold angle_ltb in Htzs.
        progress unfold angle_ltb in Hst.
        progress unfold angle_ltb.
        cbn in Htzs.
        rewrite (rngl_leb_refl Hor) in Htzs.
        cbn in Hst.
        rewrite (rngl_leb_refl Hor) in Hst.
        rewrite rngl_sin_sub_straight_l.
        rewrite rngl_cos_sub_straight_l.
        remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
        symmetry in Hzs1.
        destruct zs1; [ | easy ].
        apply rngl_leb_le in Hzs1.
        apply rngl_ltb_lt in Htzs.
        apply (rngl_lt_iff Hor) in Htzs.
        destruct Htzs as (_, Hco1).
        apply not_eq_sym in Hco1.
        remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
        symmetry in Hzs2.
        destruct zs2; [ | clear Hst ]. {
          exfalso.
          apply rngl_ltb_lt in Hst.
          apply rngl_nle_gt in Hst.
          apply Hst, rngl_cos_bound.
        }
        apply (rngl_leb_gt Hor) in Hzs2.
        progress unfold angle_eucl_dist in H2.
        rewrite rngl_cos_straight in H2.
        rewrite rngl_sin_straight in H2.
        rewrite (rngl_sub_0_l Hop) in H2.
        progress unfold rl_modl in H2.
        rewrite <- (rngl_opp_add_distr Hop) in H2.
        do 2 rewrite (rngl_squ_opp Hop) in H2.
        rewrite (rngl_add_comm _ 1) in H2.
        rewrite (rngl_squ_add Hic Hon) in H2.
        rewrite (rngl_squ_1 Hon) in H2.
        rewrite (rngl_mul_1_r Hon) in H2.
        rewrite <- rngl_add_assoc in H2.
        rewrite cos2_sin2_1 in H2.
        rewrite rngl_add_add_swap in H2.
...
        remember (0 ≤? rngl_sin (θ2 - θ1))%L as zs21 eqn:Hzs21.
        symmetry in Hzs21.
        destruct zs21; [ | easy ].
        apply rngl_leb_le in Hzs21.
        apply rngl_ltb_lt.
Search (rngl_cos _ + rngl_cos _ < 0)%L.
rewrite rngl_cos_sub.
...
Search (_ + _ < _ + _)%A.
Search (_ - _ < _ - _)%A.
Search (_ - _ < _)%A.
Search (_ < _ - _)%A.
Search (_ < _ + _)%A.
...
      rewrite (angle_eucl_dist_symmetry θ₀) in Hθ.
      do 2 rewrite angle_eucl_dist_is_2_mul_sin_sub_div_2 in Hθ.
...
      progress unfold angle_leb.
      cbn.
      rewrite (rngl_leb_refl Hor).
      remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
      symmetry in Hzs.
      destruct zs; [ apply rngl_leb_le, rngl_cos_bound | exfalso ].
      apply (rngl_leb_gt Hor) in Hzs.
      destruct Hθ as (H1, H2).
do 2 rewrite angle_eucl_dist_is_sqrt in H2.
...
      do 2 rewrite angle_eucl_dist_is_2_mul_sin_sub_div_2 in H2.
      rewrite <- (rngl_mul_div_assoc Hiv) in H2.
      apply (rngl_mul_lt_mono_pos_l Hop Hor Hii) in H2. 2: {
        apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
      }
      do 2 rewrite angle_div_2_sub in H2.
      generalize Htzs; intros H3.
      apply angle_nle_gt in H3.
      apply Bool.not_true_iff_false in H3.
      rewrite H3 in H2; clear H3.
      rewrite angle_straight_div_2 in H2.
      rewrite <- (angle_add_sub_swap (θ₀ /₂))in H2.
      rewrite <- angle_add_sub_assoc in H2.
      rewrite angle_straight_sub_right in H2.
      rewrite rngl_sin_add_right_r in H2.
      remember (θ₀ ≤? θ)%A as tt eqn:Htt.
      symmetry in Htt.
      destruct tt. {
        rewrite rngl_sin_sub in H2.
        cbn in H2.
        generalize Hzs; intros H3.
        apply (rngl_leb_gt Hor) in H3.
        rewrite H3 in H2; clear H3.
        rewrite (rngl_mul_opp_l Hop) in H2.
        rewrite (rngl_mul_1_l Hon) in H2.
        remember (0 ≤? rngl_sin θ₀)%L as zz eqn:Hzz.
        symmetry in Hzz.
        destruct zz. 2: {
          progress unfold angle_ltb in Htzs.
          cbn in Htzs.
          rewrite (rngl_leb_refl Hor) in Htzs.
          now rewrite Hzz in Htzs.
        }
        rewrite (rngl_mul_1_l Hon) in H2.
        rewrite (rngl_mul_opp_l Hop) in H2.
        rewrite (rngl_sub_opp_r Hop) in H2.
Search (√_ * √_ + _)%L.
...
Check angle_eucl_dist_is_2_mul_sin_sub_div_2.
Check angle_eucl_dist_is_sqrt.
...
Search angle_ltb.
Check angle_le_angle_eucl_dist_le.
(* θ-θ₀ ≤ π-θ₀ *)
...
      change_angle_add_r θ1 angle_straight.
      rewrite rngl_sin_sub_straight_r in Hzs1.
      apply (rngl_leb_gt Hor) in Hzs1.
      apply (rngl_opp_neg_pos Hop Hor) in Hzs1.
      rewrite rngl_cos_sub_straight_r.
      rewrite (rngl_sub_opp_r Hop).
      rewrite (rngl_add_opp_r Hop).
Search (angle_eucl_dist (_ - _)).
rewrite angle_eucl_dist_move_0_r.
rewrite angle_sub_sub_swap.
rewrite <- angle_eucl_dist_move_0_r.
Search (angle_eucl_dist angle_straight _).
Check angle_eucl_dist_2_mul_sqrt_sub_sqrt.
...
Search (- _ < 0)%L.

Search (_ ≤? - _)%L.
rewrite rngl_leb_0_opp in Hzs1.
...
...
Search (√ _ + √ _)%L.
About rngl_sin_nonneg_sin_nonneg_add_1_cos_add_add.
...
destruct_ac.
intros.
rewrite angle_eucl_dist_is_sqrt.
rewrite rl_sqrt_mul; cycle 1. {
  apply (rngl_0_le_2 Hon Hos Hor).
} {
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
Arguments rngl_squ_sqrt {T ro rp rl} Hon a%_L.
rewrite <- (rngl_squ_sqrt Hon 2) at 2. 2: {
  apply (rngl_0_le_2 Hon Hos Hor).
}
progress unfold rngl_squ.
rewrite <- rngl_mul_assoc.
f_equal.
rewrite <- (rl_sqrt_squ Hon Hop Hor).
rewrite <- rl_sqrt_mul; cycle 1. {
  apply (rngl_0_le_2 Hon Hos Hor).
} {
  apply (rngl_squ_nonneg Hos Hor).
}
f_equal.
specialize (cos2_sin2_1 ((θ1 - θ2) /₂)) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
rewrite angle_div_2_sub.
remember (θ2 ≤? θ1)%A as t21 eqn:Ht21.
symmetry in Ht21.
destruct t21. {
  rewrite (rngl_mul_sub_distr_l Hop).
  rewrite (rngl_mul_1_r Hon).
  rewrite (rngl_add_sub_swap Hop).
  rewrite <- (rngl_sub_sub_distr Hop).
  f_equal.
  symmetry.
  apply (rngl_sub_move_0_r Hop).
  rewrite (rngl_sub_sub_swap Hop).
  do 2 rewrite rngl_cos_sub.
  rewrite (rngl_sub_add_distr Hos).
  cbn.
  remember (rngl_cos θ1) as c1 eqn:Hco1.
  remember (rngl_cos θ2) as c2 eqn:Hco2.
  remember (rngl_sin θ1) as s1 eqn:Hsi1.
  remember (rngl_sin θ2) as s2 eqn:Hsi2.
  move c2 before c1; move s1 before c2; move s2 before s1.
  remember (0 ≤? s1)%L as zs1 eqn:Hzs1.
  remember (0 ≤? s2)%L as zs2 eqn:Hzs2.
  symmetry in Hzs1, Hzs2.
  destruct zs1. {
    rewrite (rngl_mul_1_l Hon).
    destruct zs2. {
      rewrite (rngl_mul_1_l Hon).
...
rewrite angle_add_overflow_comm.
apply angle_add_not_overflow_lt_straight_le_straight; [ easy | ].
destruct Hθ as (H1, H2).
apply angle_nlt_ge.
intros Hst.
apply (rngl_nle_gt_iff Hor) in H2.
apply H2; clear H2.
apply (rngl_le_div_l Hon Hop Hiv Hor). {
  apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
}
rewrite (rngl_mul_2_r Hon).
eapply (rngl_le_trans Hor). {
  apply angle_eucl_dist_triangular with (θ2 := θ).
}
rewrite angle_eucl_dist_symmetry.
apply (rngl_add_le_mono_l Hop Hor).
...
apply angle_eucl_dist_lt_angle_eucl_dist in H2.
rewrite rngl_cos_sub_straight_r in H2.
...
apply angle_eucl_dist_pos_angle_neq in H1.
apply (rngl_lt_opp_l Hop Hor) in H2.
progress unfold angle_leb.
cbn.
rewrite (rngl_leb_refl Hor).
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs; [ apply rngl_leb_le, rngl_cos_bound | ].
exfalso.
apply rngl_leb_nle in Hzs.
apply Hzs; clear Hzs.
move Htzs at bottom.
progress unfold angle_ltb in Htzs.
cbn in Htzs.
rewrite (rngl_leb_refl Hor) in Htzs.
remember (0 ≤? rngl_sin θ₀)%L as zz eqn:Hzz.
symmetry in Hzz.
destruct zz; [ | easy ].
apply rngl_leb_le in Hzz.
apply rngl_ltb_lt in Htzs.
apply (rngl_lt_iff Hor) in Htzs.
destruct Htzs as (_, Hc).
apply not_eq_sym in Hc.
destruct (rngl_le_dec Hor 0 (rngl_cos θ₀)) as [Hcz| Hcz]. {
  destruct (rngl_le_dec Hor 0 (rngl_cos θ)) as [Hct| Hct]. {
    apply (rngl_nlt_ge_iff Hor).
    intros Hsz.
    rewrite rngl_cos_sub in H2.
    change_angle_opp θ.
    progress sin_cos_opp_hyp T H2.
    progress sin_cos_opp_hyp T Hsz.
    progress sin_cos_opp_hyp T Hct.
...
    change_angle_add_r θ angle_right.
    progress sin_cos_add_sub_right_hyp T H2.
    progress sin_cos_add_sub_right_hyp T Hsz.
    progress sin_cos_add_sub_right_hyp T Hct.
...
      apply angle_add_not_overflow_iff.
      destruct Hθ as (H1, H2).
      apply angle_eucl_dist_lt_angle_eucl_dist in H2.
      rewrite rngl_cos_sub_straight_r in H2.
      apply angle_eucl_dist_pos_angle_neq in H1.
      destruct (angle_eq_dec θ 0) as [Htz| Htz]; [ now left | right ].
      apply (rngl_lt_opp_l Hop Hor) in H2.
(*
rewrite rngl_cos_sub in H2.
rewrite rngl_add_assoc in H2.
rewrite (rngl_add_mul_r_diag_r Hon) in H2.
*)
      progress unfold angle_ltb.
      cbn.
      rewrite (rngl_leb_0_opp Hop Hor).
      remember (0 ≤? rngl_sin θ₀)%L as zs eqn:Hzs.
      remember (rngl_sin θ ≤? 0)%L as sz eqn:Hsz.
      symmetry in Hzs, Hsz.
      destruct zs. {
        destruct sz; [ | easy ].
        apply rngl_ltb_lt.
        apply rngl_leb_le in Hzs, Hsz.
...
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ θ, (0 < angle_eucl_dist θ θ₀ < η)%L →
  (rngl_dist
     (if Bool.eqb (angle_add_overflow θ θ₀) (θ <? θ₀)%A then
        - rngl_sin ((θ + θ₀) /₂)
      else
        rngl_sin ((θ + θ₀) /₂))
     (- rngl_sin θ₀) < ε)%L). {
  destruct H as (η & Hzη & H).
  exists η.
  move η before ε.
  split; [ easy | ].
  intros θ Hθ.
  rewrite angle_cos_sub_cos_angle_eucl_dist_mul.
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_mul_div Hi1). 2: {
    destruct Hθ as (Hθ, _).
    apply (rngl_lt_iff Hor) in Hθ.
    destruct Hθ as (_, Hθ).
    now apply not_eq_sym in Hθ.
  }
  now apply H.
}
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ dθ, (0 < angle_eucl_dist θ₀ (θ₀ + dθ) < η)%L →
  (rngl_dist
     (if Bool.eqb (angle_add_overflow θ₀ (θ₀ + dθ)) (θ₀ + dθ <? θ₀)%A then
        - rngl_sin ((2 * θ₀ + dθ) /₂)
      else
        rngl_sin ((2 * θ₀ + dθ) /₂))
     (- rngl_sin θ₀) < ε)%L). {
  destruct H as (η & Hzη & H).
  exists η.
  move η before ε.
  split; [ easy | ].
  intros θ Hθ.
  specialize (H (θ - θ₀))%A.
  rewrite angle_add_sub_assoc in H.
  rewrite angle_add_comm in H.
  rewrite angle_add_sub in H.
  rewrite angle_eucl_dist_symmetry in H.
  specialize (H Hθ).
  rewrite angle_add_overflow_comm in H.
  rewrite angle_mul_2_l in H.
  rewrite angle_add_sub_assoc in H.
  rewrite (angle_add_comm _ θ) in H.
  rewrite angle_add_assoc in H.
  now rewrite angle_add_sub in H.
}
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ dθ, (0 < angle_eucl_dist dθ 0 < η)%L →
  (rngl_abs
     (rngl_sin θ₀ +
      (if Bool.eqb (angle_add_overflow θ₀ (θ₀ + dθ)) (θ₀ + dθ <? θ₀)%A then
         - rngl_sin ((2 * θ₀ + dθ) /₂)
       else
         rngl_sin ((2 * θ₀ + dθ) /₂))) < ε)%L). {
  destruct H as (η & Hzη & H).
  exists η.
  move η before ε.
  split; [ easy | ].
  intros dθ Hθ.
  rewrite angle_eucl_dist_move_0_l in Hθ.
  rewrite angle_add_comm in Hθ.
  rewrite angle_add_sub in Hθ.
  progress unfold rngl_dist.
  rewrite (rngl_sub_opp_r Hop).
  rewrite rngl_add_comm.
  now apply H.
}
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ θ, (0 < angle_eucl_dist θ θ₀ < η)%L →
  (rngl_abs
     (rngl_sin θ₀ + (rngl_cos θ - rngl_cos θ₀) / angle_eucl_dist θ θ₀) <
     ε)%L). {
  destruct H as (η & Hzη & H).
  exists η.
  move η before ε.
  split; [ easy | ].
  intros θ Hθ.
  progress unfold rngl_dist.
  rewrite (rngl_sub_opp_r Hop).
  rewrite rngl_add_comm.
  now apply H.
}
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ θ, (0 < angle_eucl_dist θ θ₀ < η)%L →
  let s :=
    if Bool.eqb (angle_add_overflow θ θ₀) (θ <? θ₀)%A then (-1)%L
    else 1%L
  in
  (rngl_abs (rngl_sin θ₀ + s * rngl_sin ((θ + θ₀) /₂)) < ε)%L). {
  clear - H Hor Hop Hon Hic Hi1.
  destruct H as (η & Hzη & H).
  exists η.
  split; [ easy | ].
  intros θ Hθ.
  specialize (H θ Hθ).
  cbn - [ angle_div_2 ] in H.
  destruct Hθ as (Hθ, _).
  apply (rngl_lt_iff Hor) in Hθ.
  destruct Hθ as (_, Hθ).
  apply not_eq_sym in Hθ.
  rewrite angle_cos_sub_cos_angle_eucl_dist_mul.
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_mul_div Hi1); [ | easy ].
  destruct (Bool.eqb _ _). {
    rewrite (rngl_mul_opp_l Hop) in H.
    now rewrite (rngl_mul_1_l Hon) in H.
  } {
    now rewrite (rngl_mul_1_l Hon) in H.
  }
}
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ θ, (0 < angle_eucl_dist θ θ₀ < η)%L →
  let s :=
    if Bool.eqb (angle_add_overflow θ θ₀) (θ <? θ₀)%A then (-1)%L
    else 1%L
  in
  (rngl_abs (rngl_sin θ₀ + s * rngl_sin ((θ + θ₀) /₂)) < ε)%L). {
  destruct H as (η & Hzη & H1).
  exists η.
  move η before ε.
  split; [ easy | ].
  intros θ Hθ.
  specialize (H1 θ Hθ).
  cbn - [ angle_div_2 ] in H1.
  remember (angle_add_overflow θ θ₀) as ov eqn:Hov.
  remember (θ <? θ₀)%A as tt eqn:Htt.
  symmetry in Hov, Htt.
  destruct ov. {
    progress replace (Bool.eqb true tt) with tt in H1 |-*. 2: {
      now destruct tt.
    }
    destruct tt. {
      cbn - [ angle_div_2 ].
      rewrite (rngl_mul_opp_l Hop).
      rewrite (rngl_mul_1_l Hon).
      rewrite (rngl_add_opp_r Hop).
      rewrite rngl_sin_angle_div_2_add_overflow; [ | easy ].
      rewrite rngl_sin_add_straight_r.
      rewrite (rngl_sub_opp_r Hop).
      destruct Hθ as (Hzd, Hde).
      apply rngl_cos_lt_angle_eucl_dist_lt in Hde. 2: {
        now apply (rngl_lt_le_incl Hor) in Hzη.
      }
Search (rngl_cos _ + rngl_cos _ = _)%L.
...
Search (rngl_sin _ + rngl_sin _)%L.
...
Inspect 4.
...
(* bien. Bon, faut voir... *)
Check rngl_cos_lt_angle_eucl_dist_lt.
Check exists_nat_such_that_rngl_cos_close_to_1.
...
enough (H :
  ∃ η, (0 < η)%L ∧
  ∀ θ, (angle_eucl_dist θ θ₀ < η)%L →
  (rngl_abs
     ((rngl_cos θ - rngl_cos θ₀) / angle_eucl_dist θ θ₀ + rngl_sin θ₀) <
     ε)%L). {
  destruct H as (η & Hη & H).
  exists η.
  move η before ε.
  split; [ easy | ].
  intros θ Hθ.
  rewrite rngl_cos_sub_cos.
  remember (angle_add_overflow θ θ₀) as ov eqn:Hov.
  remember (θ <? θ₀)%A as tt eqn:Htt.
  symmetry in Hov, Htt.
  destruct ov. {
    destruct tt. {
      do 2 rewrite rngl_sin_add_straight_r.
      do 2 rewrite (rngl_mul_opp_r Hop).
      rewrite (rngl_mul_opp_l Hop).
      rewrite (rngl_opp_involutive Hop).
      rewrite (rngl_div_opp_l Hop Hiv).
      rewrite (rngl_add_opp_l Hop).
      rewrite <- (rngl_add_opp_r Hop).
      rewrite <- (rngl_div_opp_l Hop Hiv).
      rewrite <- (rngl_mul_opp_r Hop).
      rewrite <- rngl_sin_opp.
      rewrite angle_opp_div_2.
      rewrite angle_opp_sub_distr.
      remember (θ - θ₀ =? 0)%A as ttz eqn:Httz.
      symmetry in Httz.
      destruct ttz. {
        apply angle_eqb_eq in Httz.
        apply -> angle_sub_move_0_r in Httz; subst θ.
        now apply angle_lt_irrefl in Htt.
      }
      rewrite rngl_sin_add_straight_r.
      rewrite (rngl_mul_opp_r Hop).
      rewrite (rngl_div_opp_l Hop Hiv).
      rewrite (rngl_add_opp_r Hop).
      rewrite angle_div_2_add.
      rewrite Hov.
      rewrite rngl_sin_add_straight_r.
      rewrite angle_div_2_sub.
      generalize Htt; intros H1.
      apply angle_lt_le_incl in H1.
      rewrite H1; clear H1.
      rewrite (rngl_mul_opp_r Hop).
      rewrite (rngl_mul_opp_l Hop).
      rewrite (rngl_div_opp_l Hop Hiv).
      rewrite (rngl_sub_opp_r Hop).
      rewrite angle_add_comm.
      rewrite <- rngl_mul_assoc.
      rewrite rngl_sin_add, rngl_sin_sub.
      remember (rngl_sin (θ₀ /₂)) as a.
      remember (rngl_cos (θ₀ /₂)) as b.
      remember (rngl_sin (θ /₂)) as c.
      remember (rngl_cos (θ /₂)) as d.
      rewrite (rngl_mul_comm Hic (_ + _)).
      rewrite (rngl_squ_sub_squ' Hop).
      rewrite (rngl_mul_comm Hic (b * c)).
      rewrite (rngl_add_sub Hos).
      subst a b c d.
      cbn.
      do 4 rewrite (rngl_squ_mul Hic).
      rewrite (rngl_squ_sqrt Hon); [ | apply rngl_1_sub_cos_div_2_nonneg ].
      rewrite (rngl_squ_sqrt Hon); [ | apply rngl_1_add_cos_div_2_nonneg ].
      rewrite (rngl_squ_sqrt Hon); [ | apply rngl_1_add_cos_div_2_nonneg ].
      rewrite (rngl_squ_sqrt Hon); [ | apply rngl_1_sub_cos_div_2_nonneg ].
      replace (if _ ≤? _ then _ else _)²%L with 1%L. 2: {
        destruct (0 ≤? rngl_sin θ)%L; symmetry; [ apply (rngl_squ_1 Hon) | ].
        apply (rngl_squ_opp_1 Hon Hop).
      }
      replace (if _ ≤? _ then _ else _)²%L with 1%L. 2: {
        destruct (0 ≤? rngl_sin θ₀)%L; symmetry; [ apply (rngl_squ_1 Hon) | ].
        apply (rngl_squ_opp_1 Hon Hop).
      }
      do 2 rewrite (rngl_mul_1_l Hon).
      rewrite (rngl_mul_sub_distr_r Hop).
      do 2 rewrite <- rngl_mul_assoc.
      rewrite (rngl_div_mul Hon Hiv). 2: {
        apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
      }
      rewrite (rngl_div_mul Hon Hiv). 2: {
        apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
      }
      do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
...
      remember ((θ + q) /₂)%A as a.
  remember ((p - q) /₂)%A as b.
  move b before a.
  rewrite (rngl_sub_opp_r Hop).
  rewrite (rngl_opp_add_distr Hop).
  rewrite (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_add Hop).
  rewrite <- (rngl_opp_add_distr Hop).
  rewrite <- (rngl_mul_2_l Hon).
  rewrite <- rngl_mul_assoc.
  rewrite <- (rngl_mul_opp_r Hop).
  f_equal.
...
enough (H :
  ∃ η : T,
  (0 < η)%L ∧
  ∀ dθ : angle T,
    (angle_eucl_dist (θ₀ + dθ) θ₀ < η)%L
    → (rngl_dist
         (rngl_dist
            (rngl_cos (θ + dθ)) (rngl_cos θ) / angle_eucl_dist (θ + dθ) θ)
            (- rngl_sin θ) <
       ε)%L). {
  destruct H as (η & Hzη & H).
  exists η.
  split; [ easy | ].
  intros θ' Hθ'.
  specialize (H (θ' - θ))%A.
  rewrite angle_add_sub_assoc in H.
  rewrite angle_add_sub_swap in H.
  rewrite angle_sub_diag, angle_add_0_l in H.
  now specialize (H Hθ').
}
enough (H :
  ∃ η : T,
  (0 < η)%L ∧
  ∀ dθ : angle T,
    (angle_eucl_dist (θ + dθ) θ < η)%L
    → (rngl_dist
         (rngl_abs (rngl_cos (θ + dθ) - rngl_cos θ) /
            rl_modl
              (rngl_cos (θ + dθ) - rngl_cos θ)
              (rngl_sin (θ + dθ) - rngl_sin θ))
         (- rngl_sin θ) <
       ε)%L). {
  destruct H as (η & Hzη & H).
  exists η.
  split; [ easy | ].
  intros dθ Hdθ.
  specialize (H dθ Hdθ)%A.
  progress unfold rngl_dist at 2.
  (* lemma *)
  progress unfold angle_eucl_dist.
  progress unfold rl_modl.
  rewrite (rngl_squ_sub_comm Hop).
  rewrite (rngl_squ_sub_comm Hop (rngl_sin θ)).
  rewrite fold_rl_modl.
  easy.
}
enough (H :
  ∃ η : T,
  (0 < η)%L ∧
  ∀ dθ : angle T,
    (1 - η² / 2 < rngl_cos dθ)%L
  → (rngl_abs
     (rngl_sin θ +
      rngl_abs (rngl_cos (θ + dθ) - rngl_cos θ) /
      rl_modl
        (rngl_cos (θ + dθ) - rngl_cos θ)
        (rngl_sin (θ + dθ) - rngl_sin θ)) < ε)%L). {
  destruct H as (η & Hzη & H).
  exists η.
  move η before ε.
  split; [ easy | ].
  intros dθ Hdθ.
  rewrite angle_eucl_dist_is_sqrt in Hdθ.
  rewrite angle_sub_add_distr in Hdθ.
  rewrite angle_sub_diag in Hdθ.
  rewrite angle_sub_0_l in Hdθ.
  rewrite rngl_cos_opp in Hdθ.
  apply (rngl_lt_lt_squ Hop Hor Hii) in Hdθ; cycle 1. {
    apply (rngl_mul_comm Hic).
  } {
    apply rl_sqrt_nonneg.
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply (rngl_0_le_2 Hon Hos Hor).
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  rewrite (rngl_squ_sqrt Hon) in Hdθ. 2: {
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply (rngl_0_le_2 Hon Hos Hor).
    apply (rngl_le_0_sub Hop Hor).
    apply rngl_cos_bound.
  }
  rewrite (rngl_mul_comm Hic) in Hdθ.
  apply (rngl_lt_div_r Hon Hop Hiv Hor) in Hdθ. 2: {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  apply (rngl_lt_sub_lt_add_r Hop Hor) in Hdθ.
  rewrite rngl_add_comm in Hdθ.
  apply (rngl_lt_sub_lt_add_r Hop Hor) in Hdθ.
  progress unfold rngl_dist.
  rewrite (rngl_sub_opp_r Hop).
  rewrite rngl_add_comm.
  now apply H.
}
...
  specialize (H dθ Hdθ)%A.
  rewrite rngl_cos_sub_cos.
  rewrite rngl_sin_sub_sin.
  rewrite (angle_add_comm θ).
  rewrite angle_add_sub.
  rewrite <- angle_add_assoc.
  do 2 rewrite (angle_add_comm dθ).
  rewrite <- angle_mul_2_l.
  rewrite angle_div_2_add.
(**)
  rewrite fold_angle_add_overflow2.
  rewrite angle_add_overflow_equiv3.
  remember (angle_add_overflow θ dθ) as ov1 eqn:Hov1.
  remember (angle_add_overflow (θ + dθ) θ) as ov2 eqn:Hov2.
  remember (angle_add_overflow (2 * θ) dθ) as ov3 eqn:Hov3.
  symmetry in Hov1, Hov2, Hov3.
  destruct ov1. {
    rewrite rngl_sin_add_straight_r.
    destruct ov2. {
      rewrite rngl_sin_add_straight_r.
      destruct ov3. {
        rewrite rngl_sin_add_straight_r.
        rewrite <- angle_add_assoc.
        rewrite angle_straight_add_straight.
        rewrite angle_add_0_r.
        do 4 rewrite (rngl_mul_opp_r Hop).
        do 2 rewrite (rngl_opp_involutive Hop).
        rewrite angle_mul_2_l in Hov3.
...
        rewrite <- angle_mul_nat_div_2. 2: {
Search ((2 * _) /₂)%A.
Search (rngl_dist _ (- _)).
...
    rewrite angle_add_comm in Hov2.
    apply angle_add_not_overflow_move_add in Hov2. 2: {
...
    rewrite angle_add_overflow_comm in Hov2.
    rewrite <- angle_mul_2_l in Hov2.
    rewrite Hov2.
    rewrite angle_add_0_r.
...
Search ((_ * _) /₂)%A.
    rewrite <- angle_mul_nat_div_2. 2: {
      cbn.
      rewrite angle_add_0_r, Bool.orb_false_r.
      rewrite <- (angle_mul_1_l θ).
      apply angle_mul_nat_overflow_distr_add_overflow.
      cbn - [ angle_mul_nat_overflow ].
      rewrite <-<- angle_mul_2_l in Hov2.
Search (angle_add_overflow (_ + _)).
      apply angle_add_not_overflow_move_add in Hov2.
(* ouais, bon, c'est pas clair *)
...
    apply angle_mul_nat_overflow_distr_add_overflow in Hov2.
    rewrite <-<- angle_mul_2_l in Hov2.
...

Theorem rngl_cos_sub_cos :
  ∀ p q,
  (rngl_cos p - rngl_cos q =
     - (2 * rngl_sin ((p + q) /₂) * rngl_sin ((p - q) /₂)))%L.
Proof.
destruct_ac.
intros.
specialize (rngl_cos_add_cos p (q + angle_straight)) as H1.
rewrite angle_add_assoc in H1.
rewrite angle_sub_add_distr in H1.
rewrite rngl_cos_add_straight_r in H1.
rewrite (rngl_add_opp_r Hop) in H1.
(* I need a lemma angle_lt_dec *)
remember ((p + q) <? angle_straight)%A as pqs eqn:Hpqs.
symmetry in Hpqs.
destruct pqs. {
  rewrite rngl_sin_angle_div_2_add_not_overflow in H1. 2: {
    (* lemma *)
    progress unfold angle_add_overflow.
    apply Bool.andb_false_iff.
    remember (p + q ≠? 0)%A as pqz eqn:Hpqz.
    symmetry in Hpqz.
    destruct pqz; [ right | now left ].
    apply angle_leb_gt.
    apply angle_lt_opp_r; [ | now rewrite angle_opp_straight ].
    intros H.
    now apply angle_neqb_neq in Hpqz.
  }
...
    (* lemma *)
    rewrite <- angle_add_overflow_equiv3.
    progress unfold angle_add_overflow2.
    (* lemma *)
    apply Bool.not_true_iff_false.
    intros H.
    apply angle_nle_gt in H.
    apply H; clear H.
    (* end lemma *)
Search (_ ≤ _ + _)%A.
    (* lemma *)
    rewrite <- (angle_add_0_r (p + q)) at 1.
    apply angle_add_le_mono_l.
...
    apply angle_le_add_l.
    apply angle_ltb_ge.
...
    rewrite angle_add_overflow_equiv2.
    progress unfold angle_add_overflow.
    apply Bool.andb_false_iff.

Search (_ → angle_add_overflow _ _ = false).
Search (rngl_sin ((_ + _) /₂)).
...
rewrite H1; clear H1.
...
rewrite rngl_mul_assoc.
...
Print rngl_dist.
progress unfold rngl_dist.
enough (H : ...
...
Check rngl_cos_add_cos.
Search (rngl_cos _ - rngl_cos _)%L.
progress unfold angle_eucl_dist at 1.
...
*)

End a.
