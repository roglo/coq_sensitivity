(* derivation of trigonometric functions *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.RingLike.

Require Import Trigo.RealLike.
Require Import Trigo.Angle.
Require Import Trigo.AngleDiv2.
Require Import Trigo.TacChangeAngle.
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

Theorem rngl_cos_derivative_lemma_4 :
  ∀ θ₀ ε,
  (0 < ε)%L
  → (0 < θ₀ < angle_straight)%A
  → ∃ (η : angle T) (ζ : T), (0 < ζ)%L ∧
    ∀ dθ : angle T,
    (0 < dθ < η)%A
    → (0 < angle_eucl_dist dθ 0 < ζ)%L
    → (rngl_dist
         ((rngl_cos (θ₀ + dθ) - rngl_cos θ₀) / angle_eucl_dist dθ 0)
         (- rngl_sin θ₀) < ε)%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros θ₀ ε Hε.
  rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
intros * Hε (Htz, Htls).
specialize rngl_sin_is_continuous as Hsc.
progress unfold continuous in Hsc.
progress unfold continuous_at in Hsc.
progress unfold is_limit_when_tending_to in Hsc.
specialize (Hsc θ₀ ε Hε).
destruct Hsc as (ζ1 & Hζ1 & Hsc).
progress unfold rngl_dist in Hsc.
move ζ1 before ε.
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
    apply angle_eucl_dist_pos_angle_neq.
    intros H; rewrite H in Htz.
    now apply angle_lt_irrefl in Htz.
  }
  apply angle_eucl_dist_pos_angle_neq.
  intros H; rewrite H in Htls.
  now apply angle_lt_irrefl in Htls.
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
Qed.

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
  rewrite rngl_cos_angle_eucl_dist_0_r.
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
  rewrite rngl_cos_angle_eucl_dist_straight_r.
  rewrite (rngl_sub_add Hop).
  rewrite (rngl_div_div_swap Hic Hiv).
  progress unfold rngl_squ.
  rewrite (rngl_mul_div Hi1). 2: {
    intros H; rewrite H in Hdθ.
    destruct Hdθ as (H1, _).
    now apply (rngl_lt_irrefl Hor) in H1.
  }
  progress unfold rngl_dist.
  rewrite (rngl_sub_0_r Hos).
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
destruct (angle_lt_dec θ₀ angle_straight) as [Htls| Htls]. {
  apply (rngl_cos_derivative_lemma_4 _ _ Hε).
  split; [ | easy ].
  apply angle_lt_iff.
  split; [ apply angle_nonneg | ].
  easy.
} {
  apply angle_nlt_ge in Htls.
  change_angle_sub_r θ₀ angle_straight.
  apply (rngl_cos_derivative_lemma_4 _ _ Hε).
  split. {
    apply angle_lt_iff.
    split; [ apply angle_nonneg | easy ].
  }
  (* lemma *)
  progress unfold angle_leb in Htls.
  progress unfold angle_ltb.
  rewrite rngl_cos_add_straight_r in Htls |-*.
  rewrite rngl_sin_add_straight_r in Htls |-*.
  cbn in Htls |-*.
  rewrite (rngl_leb_refl Hor) in Htls |-*.
  rewrite (rngl_leb_0_opp Hop Hor) in Htls |-*.
  remember (rngl_sin θ₀ ≤? 0)%L as sz eqn:Hsz.
  symmetry in Hsz.
  destruct sz. {
    rewrite (rngl_leb_opp_r Hop Hor) in Htls.
    rewrite (rngl_opp_involutive Hop) in Htls.
    apply rngl_leb_le in Htls.
    apply rngl_ltb_lt.
    apply -> (rngl_opp_lt_compat Hop Hor).
    apply (rngl_lt_iff Hor).
    split; [ apply rngl_cos_bound | ].
    intros H.
    apply eq_rngl_cos_1 in H.
    subst θ₀.
    now rewrite angle_add_0_l in Hts.
  }
  exfalso.
  clear Htls.
  apply (rngl_leb_gt Hor) in Hsz.
  (* ah bin merde alors *)
...
les feux sauvages
...
*)

End a.
