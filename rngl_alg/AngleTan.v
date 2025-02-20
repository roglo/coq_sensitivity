(* trigonometry; tangent; derivability of a product *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Require Import Main.RingLike.
Require Import Trigo.RealLike.
Require Import Trigo.Angle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Definition rngl_tan θ := (rngl_sin θ / rngl_cos θ)%L.

Context {Hop : rngl_has_opp T = true}.
Context {Hor : rngl_is_ordered T = true}.

Theorem rngl_dist_mul_distr_r :
 (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c,
  (0 ≤ c)%L → (rngl_dist a b * c = rngl_dist (a * c) (b * c))%L.
Proof.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros Hii.
intros * Hzc.
progress unfold rngl_dist.
rewrite <- (rngl_mul_sub_distr_r Hop).
progress unfold rngl_abs.
rewrite (rngl_mul_sub_distr_r Hop).
do 2 rewrite (rngl_leb_sub_0 Hop Hor).
rewrite <- (rngl_mul_sub_distr_r Hop).
remember (a ≤? b)%L as ab eqn:Hab.
remember (a * c ≤? b * c)%L as acbc eqn:Hacbc.
symmetry in Hab, Hacbc.
destruct ab. {
  destruct acbc; [ apply (rngl_mul_opp_l Hop) | ].
  apply rngl_leb_le in Hab.
  apply (rngl_leb_gt Hor) in Hacbc.
  exfalso.
  apply rngl_nle_gt in Hacbc.
  apply Hacbc; clear Hacbc.
  now apply (rngl_mul_le_mono_nonneg_r Hop Hor).
}
apply (rngl_leb_gt Hor) in Hab.
destruct acbc; [ | easy ].
apply rngl_leb_le in Hacbc.
apply (rngl_lt_eq_cases Hor) in Hzc.
destruct Hzc as [Hzc| Hzc]. {
  exfalso.
  apply rngl_nlt_ge in Hacbc.
  apply Hacbc; clear Hacbc.
  now apply (rngl_mul_lt_mono_pos_r Hop Hor Hii).
}
subst c.
rewrite (rngl_mul_0_r Hos).
symmetry.
apply (rngl_opp_0 Hop).
Qed.

Definition is_limit_when_tending_to_neighbourhood_le (is_left : bool) {A B} lt
  (da : distance A) (db : distance B) (f : A → B) (x₀ : A) (L : B) :=
  (∀ ε : T, 0 < ε →
   ∃ η : T, (0 < η)%L ∧ ∀ x : A,
   (if is_left then lt x x₀ else lt x₀ x)
   → d_dist x x₀ < η
   → d_dist (f x) L ≤ ε)%L.

Theorem is_limit_lt_is_limit_le_iff :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ is_left {A B} lt da db (f : A → B) x₀ L,
  is_limit_when_tending_to_neighbourhood is_left lt da db f x₀ L
  ↔ is_limit_when_tending_to_neighbourhood_le is_left lt da db f x₀ L.
Proof.
intros Hon Hiv.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  split; intros H ε; rewrite (H1 ε); intro Hε;
  now apply (rngl_lt_irrefl Hor) in Hε.
}
specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as Hz2.
intros.
split; intros H1 ε Hε. {
  specialize (H1 ε Hε).
  destruct H1 as (η & Hη & H1).
  exists η.
  split; [ easy | ].
  intros x Hlt Hd.
  apply (rngl_lt_le_incl Hor).
  now apply H1.
} {
  specialize (H1 (ε / 2))%L.
  assert (Hε2 : (0 < ε / 2)%L). {
    apply (rngl_div_pos Hon Hop Hiv Hor _ _ Hε Hz2).
  }
  specialize (H1 Hε2).
  destruct H1 as (η & Hη & H1).
  exists η.
  split; [ easy | ].
  intros x Hlt Hd.
  apply (rngl_le_lt_trans Hor _ (ε / 2)). 2: {
    apply (rngl_lt_div_l Hon Hop Hiv Hor _ _ _ Hz2).
    rewrite (rngl_mul_2_r Hon).
    apply (rngl_lt_add_l Hos Hor _ _ Hε).
  }
  now apply H1.
}
Qed.

Definition rngl_distance :=
  {| d_dist := rngl_dist; d_prop := rngl_dist_is_dist Hop Hor |}.

Theorem derivable_continuous_when_derivative_eq_0 :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ A le lt, (∀ x, ¬ (lt x x)) → (∀ x y, le x y → lt x y) →
  ∀ da (f : A → T) x,
  left_derivative_at lt da rngl_distance f x 0%L
  → left_continuous_at le da rngl_distance f x.
Proof.
intros Hon Hiv.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hlti Hlet * Hd.
rename x into x₀.
intros ε Hε.
specialize (Hd √ε).
assert (Hsε : (0 < √ε)%L) by now apply (rl_sqrt_pos Hon Hos Hor).
specialize (Hd Hsε).
destruct Hd as (η & Hη & Hd).
exists (rngl_min √ε η).
split; [ now apply rngl_min_glb_lt | ].
intros x Hle Hdxx.
generalize Hle; intros Hlt.
apply Hlet in Hlt.
specialize (Hd x Hlt).
apply (rngl_min_glb_lt_iff Hor) in Hdxx.
destruct Hdxx as (Hdε, Hdη).
specialize (Hd Hdη).
assert (Hdz : d_dist x x₀ ≠ 0%L). {
  intros H.
  apply dist_separation in H; [ | apply d_prop ].
  subst x.
  now apply Hlti in Hlt.
}
apply (rngl_mul_lt_mono_pos_r Hop Hor Hii (d_dist x x₀)) in Hd. 2: {
  clear H.
  apply (rngl_lt_iff Hor).
  split; [ apply (dist_nonneg Hon Hop Hiv Hor) | easy ].
}
cbn in Hd |-*.
rewrite (rngl_dist_mul_distr_r Hii) in Hd. 2: {
  apply (dist_nonneg Hon Hop Hiv Hor).
}
rewrite (rngl_div_mul Hon Hiv) in Hd; [ | easy ].
rewrite (rngl_mul_0_l Hos) in Hd.
progress unfold rngl_dist in Hd.
progress unfold rngl_dist.
rewrite (rngl_sub_0_r Hos) in Hd.
eapply (rngl_lt_le_trans Hor). {
  rewrite <- (rngl_abs_opp Hop Hor).
  rewrite (rngl_opp_sub_distr Hop).
  apply Hd.
}
eapply (rngl_le_trans Hor). {
  apply (rngl_mul_le_mono_pos_l Hop Hor Hii). {
    now apply (rl_sqrt_pos Hon Hos Hor).
  }
  apply (rngl_lt_le_incl Hor), Hdε.
}
rewrite fold_rngl_squ.
rewrite (rngl_squ_sqrt Hon); [ apply (rngl_le_refl Hor) | ].
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem left_derivable_continuous :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ A le lt, (∀ x, ¬ (lt x x)) → (∀ x y, le x y → lt x y) →
  ∀ da (f : A → T) x a,
  left_derivative_at lt da rngl_distance f x a
  → left_continuous_at le da rngl_distance f x.
Proof.
intros Hic Hon Hiv.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hlti Hlet * Hd ε Hε.
  rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as Hz2.
specialize (rngl_2_neq_0 Hon Hos Hc1 Hor) as H2z.
intros * Hlti Hlet * Hd.
rename x into x₀.
destruct (rngl_eq_dec Heo a 0) as [Hfz| Hfz]. {
  subst a.
  specialize (derivable_continuous_when_derivative_eq_0 Hon Hiv) as H1.
  now apply (H1 _ le lt Hlti Hlet da f).
}
progress unfold left_derivative_at in Hd.
progress unfold is_limit_when_tending_to_neighbourhood in Hd.
specialize (Hd (rngl_abs a))%L.
assert (Haz : (0 < rngl_abs a)%L) by now apply (rngl_abs_pos Hop Hor).
specialize (Hd Haz).
destruct Hd as (η & Hη & Hd).
intros ε Hε.
exists (rngl_min η (ε / (2 * rngl_abs a)))%L.
split. {
  apply rngl_min_glb_lt; [ easy | ].
  apply (rngl_div_pos Hon Hop Hiv Hor); [ easy | ].
  apply (rngl_mul_pos_pos Hos Hor Hii); [ easy | ].
  now apply (rngl_abs_pos Hop Hor).
}
intros x Hle Hdxx.
generalize Hle; intros Hlt.
apply Hlet in Hlt.
move Hlt before Hle.
specialize (Hd x Hlt).
apply (rngl_min_glb_lt_iff Hor) in Hdxx.
destruct Hdxx as (H1, H2).
specialize (Hd H1).
assert (Hdz : d_dist x x₀ ≠ 0%L). {
  intros H.
  apply dist_separation in H; [ | apply d_prop ].
  subst x.
  now apply Hlti in Hlt.
}
cbn in Hd |-*.
apply (rngl_mul_lt_mono_pos_r Hop Hor Hii (d_dist x x₀)) in Hd. 2: {
  clear H.
  apply (rngl_lt_iff Hor).
  split; [ apply (dist_nonneg Hon Hop Hiv Hor) | easy ].
}
rewrite (rngl_dist_mul_distr_r Hii) in Hd. 2: {
  apply (dist_nonneg Hon Hop Hiv Hor).
}
rewrite (rngl_div_mul Hon Hiv) in Hd; [ | easy ].
progress unfold rngl_dist in Hd.
progress unfold rngl_dist.
progress unfold rngl_abs in Hd at 1.
rewrite (rngl_leb_sub_0 Hop Hor) in Hd.
remember (f x₀ - f x ≤? a * d_dist x x₀)%L as b eqn:Hb.
symmetry in Hb.
destruct b. {
  apply rngl_leb_le in Hb.
  rewrite (rngl_opp_sub_distr Hop) in Hd.
  progress unfold rngl_abs.
  rewrite (rngl_leb_sub_0 Hop Hor).
  remember (f x ≤? f x₀)%L as c eqn:Hc.
  symmetry in Hc.
  destruct c. {
    apply rngl_leb_le in Hc.
    rewrite (rngl_opp_sub_distr Hop).
    destruct (rngl_le_dec Hor a 0) as [Hflz| Hflz]. {
      apply (rngl_nle_gt_iff Hor).
      intros Hea.
      apply rngl_nlt_ge in Hb.
      apply Hb; clear Hb.
      eapply (rngl_le_lt_trans Hor). {
        apply (rngl_mul_le_mono_pos_r Hop Hor Hii). {
          apply (rngl_lt_iff Hor).
          split; [ apply (dist_nonneg Hon Hop Hiv Hor) | easy ].
        }
        apply Hflz.
      }
      rewrite (rngl_mul_0_l Hos).
      apply (rngl_lt_0_sub Hop Hor).
      apply (rngl_lt_iff Hor).
      split; [ easy | ].
      intros H; rewrite H, (rngl_sub_diag Hos) in Hea.
      now apply rngl_nlt_ge in Hea.
    }
    apply (rngl_nle_gt_iff Hor) in Hflz.
    eapply (rngl_le_lt_trans Hor); [ apply Hb | ].
    rewrite (rngl_abs_nonneg_eq Hop Hor) in H2. 2: {
      now apply (rngl_lt_le_incl Hor).
    }
    eapply (rngl_lt_le_trans Hor). {
      apply (rngl_mul_lt_mono_pos_l Hop Hor Hii); [ easy | ].
      apply H2.
    }
    rewrite (rngl_mul_comm Hic 2).
    rewrite <- (rngl_div_div Hos Hon Hiv); [ | easy | easy ].
    rewrite (rngl_mul_comm Hic).
    rewrite (rngl_div_mul Hon Hiv); [ | easy ].
    apply (rngl_le_div_l Hon Hop Hiv Hor); [ easy | ].
    rewrite (rngl_mul_2_r Hon).
    apply (rngl_le_add_l Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_leb_gt Hor) in Hc.
  rewrite (rngl_sub_sub_distr Hop) in Hd.
  rewrite <- (rngl_add_sub_swap Hop) in Hd.
  rewrite <- (rngl_add_sub_assoc Hop) in Hd.
  apply (rngl_lt_add_lt_sub_l Hop Hor) in Hd.
  rewrite <- (rngl_mul_sub_distr_r Hop) in Hd.
  destruct (rngl_lt_dec Hor a 0) as [Haz'| Haz']. {
    generalize Haz'; intros Haz''.
    apply (rngl_lt_le_incl Hor) in Haz''.
    rewrite (rngl_abs_nonpos_eq Hop Hor) in Hd; [ | easy ].
    rewrite (rngl_abs_nonpos_eq Hop Hor) in H2; [ | easy ].
    eapply (rngl_lt_le_trans Hor); [ apply Hd | ].
    eapply (rngl_le_trans Hor). {
      apply (rngl_mul_le_mono_pos_l Hop Hor Hii). {
        rewrite <- (rngl_opp_add_distr Hop).
        apply (rngl_opp_pos_neg Hop Hor).
        rewrite <- (rngl_mul_2_l Hon).
        apply (rngl_mul_pos_neg Hop Hor); [ | easy | easy ].
        rewrite Bool.orb_true_iff; right.
        rewrite Hi1; cbn.
        apply (rngl_has_eq_dec_or_is_ordered_r Hor).
      }
      apply (rngl_lt_le_incl Hor), H2.
    }
    rewrite (rngl_mul_2_l Hon).
    rewrite (rngl_add_opp_r Hop).
    rewrite (rngl_mul_comm Hic).
    rewrite (rngl_div_mul Hon Hiv). 2: {
      intros H.
      rewrite <- (rngl_add_opp_r Hop) in H.
      apply (rngl_eq_add_0 Hor) in H. {
        destruct H as (H, _).
        rewrite <- (rngl_opp_0 Hop) in H.
        now apply (rngl_opp_inj Hop) in H.
      } {
        now apply (rngl_opp_nonneg_nonpos Hop Hor).
      } {
        now apply (rngl_opp_nonneg_nonpos Hop Hor).
      }
    }
    apply (rngl_le_refl Hor).
  }
  apply (rngl_nlt_ge_iff Hor) in Haz'.
  rewrite (rngl_abs_nonneg_eq Hop Hor) in Hd; [ | easy ].
  rewrite (rngl_sub_diag Hos) in Hd.
  rewrite (rngl_mul_0_l Hos) in Hd.
  apply -> (rngl_lt_sub_0 Hop Hor) in Hd.
  apply (rngl_lt_le_incl Hor) in Hd.
  now apply rngl_nlt_ge in Hd.
}
apply (rngl_leb_gt Hor) in Hb.
progress unfold rngl_abs.
rewrite (rngl_leb_sub_0 Hop Hor).
remember (f x ≤? f x₀)%L as c eqn:Hc.
symmetry in Hc.
destruct c. {
  apply rngl_leb_le in Hc.
  rewrite (rngl_opp_sub_distr Hop).
  destruct (rngl_le_dec Hor a 0) as [Hflz| Hflz]. {
    rewrite (rngl_abs_nonpos_eq Hop Hor) in Hd; [ | easy ].
    apply (rngl_lt_sub_lt_add_r Hop Hor) in Hd.
    rewrite (rngl_mul_opp_l Hop) in Hd.
    rewrite (rngl_add_opp_l Hop) in Hd.
    rewrite (rngl_sub_diag Hos) in Hd.
    apply -> (rngl_lt_sub_0 Hop Hor) in Hd.
    now apply rngl_nle_gt in Hd.
  }
  apply (rngl_nle_gt_iff Hor) in Hflz.
  rewrite (rngl_abs_nonneg_eq Hop Hor) in Hd, H2; cycle 1. {
    now apply (rngl_lt_le_incl Hor).
  } {
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_lt_sub_lt_add_r Hop Hor) in Hd.
  rewrite <- (rngl_mul_2_l Hon) in Hd.
  eapply (rngl_lt_le_trans Hor); [ apply Hd | ].
  rewrite rngl_mul_assoc.
  rewrite (rngl_mul_comm Hic).
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    now apply (rngl_mul_pos_pos Hos Hor Hii).
  }
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_leb_gt Hor) in Hc.
destruct (rngl_le_dec Hor a 0) as [Hflz| Hflz]. {
  rewrite <- (rngl_opp_sub_distr Hop) in Hb.
  apply (rngl_lt_opp_r Hop Hor) in Hb.
  rewrite rngl_add_comm in Hb.
  apply (rngl_lt_opp_r Hop Hor) in Hb.
  eapply (rngl_lt_le_trans Hor); [ apply Hb | ].
  rewrite <- (rngl_mul_opp_l Hop).
  rewrite <- (rngl_abs_nonpos_eq Hop Hor); [ | easy ].
  rewrite (rngl_mul_comm Hic).
  apply (rngl_le_div_r Hon Hop Hiv Hor); [ easy | ].
  eapply (rngl_le_trans Hor). {
    apply (rngl_lt_le_incl Hor), H2.
  }
  rewrite <- (rngl_div_div Hos Hon Hiv); [ | | easy ]. 2: {
    intros H.
    now apply (eq_rngl_abs_0 Hop) in H.
  }
  apply (rngl_le_div_l Hon Hop Hiv Hor); [ easy | ].
  rewrite (rngl_mul_2_r Hon).
  apply (rngl_le_add_l Hor).
  apply (rngl_div_nonneg Hon Hop Hiv Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt_iff Hor) in Hflz.
exfalso.
apply rngl_nle_gt in Hb.
apply Hb; clear Hb.
apply (rngl_le_trans Hor _ 0). {
  apply (rngl_le_sub_0 Hop Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_mul_nonneg_nonneg Hos Hor).
now apply (rngl_lt_le_incl Hor).
apply (dist_nonneg Hon Hop Hiv Hor).
Qed.

(* to be completed
Theorem left_derivative_mul :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ A lt, (∀ x, ¬ (lt x x)) →
  ∀ da (f g : A → T) x₀ u v,
  left_derivative_at lt da rngl_distance f x₀ u
  → left_derivative_at lt da rngl_distance g x₀ v
  → left_derivative_at lt da rngl_distance (λ x : A, (f x * g x)%L)
      x₀ (f x₀ * v + u * g x₀)%L.
Proof.
intros Hic Hon Hiv.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hlit * Hf Hg ε Hε.
  rewrite (H1 ε) in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as Hz2.
specialize (rngl_0_le_2 Hon Hos Hor) as Hz2'.
specialize (rngl_2_neq_0 Hon Hos Hc1 Hor) as H2z.
assert (Hz4 : (0 < 4)%L). {
  apply (rngl_lt_le_trans Hor _ 2); [ easy | ].
  apply (rngl_add_le_mono_r Hop Hor).
  now apply (rngl_le_add_l Hor).
}
assert (Hz4' : (0 ≤ 4)%L). {
  apply (rngl_le_trans Hor _ 2); [ easy | ].
  apply (rngl_add_le_mono_r Hop Hor).
  now apply (rngl_le_add_l Hor).
}
intros * Hlti * Hf Hg.
generalize Hf; intros Hcf.
apply (left_derivable_continuous Hic Hon Hiv _ lt) in Hcf; [ | easy | easy ].
generalize Hg; intros Hcg.
apply (left_derivable_continuous Hic Hon Hiv _ lt) in Hcg; [ | easy | easy ].
(**)
progress unfold left_derivative_at in Hf.
progress unfold left_derivative_at in Hg.
apply (is_limit_lt_is_limit_le_iff Hon Hiv) in Hf, Hg.
apply (is_limit_lt_is_limit_le_iff Hon Hiv).
progress unfold is_limit_when_tending_to_neighbourhood_le in Hf.
progress unfold is_limit_when_tending_to_neighbourhood_le in Hg.
intros ε Hε.
specialize (Hf (ε / (4 * rngl_abs (g x₀) + 1)))%L.
assert (H : (0 < ε / (4 * rngl_abs (g x₀) + 1))%L). {
  apply (rngl_div_pos Hon Hop Hiv Hor _ _ Hε).
  apply (rngl_add_nonneg_pos Hor).
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
  apply (rngl_abs_nonneg Hop Hor).
  apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
}
specialize (Hf H); clear H.
specialize (Hg (ε / (4 * rngl_abs (f x₀) + 1)))%L.
assert (H : (0 < ε / (4 * rngl_abs (f x₀) + 1))%L). {
  apply (rngl_div_pos Hon Hop Hiv Hor _ _ Hε).
  apply (rngl_add_nonneg_pos Hor).
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
  apply (rngl_abs_nonneg Hop Hor).
  apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
}
specialize (Hg H); clear H.
assert (H : (0 < √ε / 2)%L). {
  apply (rngl_div_pos Hon Hop Hiv Hor); [ | easy ].
  now apply (rl_sqrt_pos Hon Hos Hor).
}
specialize (Hcf (√ε / 2) H)%L.
specialize (Hcg (√ε / 2) H)%L; clear H.
move Hε before ε.
destruct Hf as (ηf & Hηf & Hf).
destruct Hg as (ηg & Hηg & Hg).
destruct Hcf as (ηcf & Hηcf & Hcf).
destruct Hcg as (ηcg & Hηcg & Hcg).
move ηf before ε.
move ηg before ηf.
move ηcf before ηg.
move ηcg before ηcf.
move Hηg before Hηf.
move Hηcf before Hηg.
move Hηcg before Hηcf.
exists (rngl_min3 ηf ηg (rngl_min3 ηcf ηcg ε)).
split. {
  apply rngl_min_glb_lt.
  now apply rngl_min_glb_lt.
  apply rngl_min_glb_lt; [ | easy ].
  now apply rngl_min_glb_lt.
}
intros x Hlt Hd.
move x before x₀.
apply (rngl_min_glb_lt_iff Hor) in Hd.
destruct Hd as (H1, H3).
apply (rngl_min_glb_lt_iff Hor) in H1, H3.
destruct H1 as (H1, H2).
destruct H3 as (H3, H5).
apply (rngl_min_glb_lt_iff Hor) in H3.
destruct H3 as (H3, H4).
specialize (Hf x Hlt H1).
specialize (Hg x Hlt H2).
specialize (Hcf x Hlt H3).
specialize (Hcg x Hlt H4).
cbn.
assert (Hzd : (0 < d_dist x x₀)%L). {
  apply (rngl_lt_iff Hor).
  destruct da as (da, dap).
  split; [ now apply (dist_nonneg Hon Hop Hiv Hor) | ].
  cbn; intros H; symmetry in H.
  apply dist_separation in H; [ | easy ].
  subst x.
  now apply Hlti in Hlt.
}
assert (Hzed : (0 ≤ d_dist x x₀)%L). {
  now apply (dist_nonneg Hon Hop Hiv Hor).
}
apply (rngl_mul_le_mono_pos_r Hop Hor Hii _ _ _ Hzd) in Hf.
apply (rngl_mul_le_mono_pos_r Hop Hor Hii _ _ _ Hzd) in Hg.
apply (rngl_mul_le_mono_pos_r Hop Hor Hii _ _ _ Hzd).
cbn in Hf, Hg.
rewrite (rngl_dist_mul_distr_r Hii _ _ _ Hzed) in Hf.
rewrite (rngl_dist_mul_distr_r Hii _ _ _ Hzed) in Hg.
rewrite (rngl_dist_mul_distr_r Hii _ _ _ Hzed).
rewrite (rngl_div_mul Hon Hiv) in Hf. 2: {
  intros H; rewrite H in Hzd.
  now apply (rngl_lt_irrefl Hor) in Hzd.
}
rewrite (rngl_div_mul Hon Hiv) in Hg. 2: {
  intros H; rewrite H in Hzd.
  now apply (rngl_lt_irrefl Hor) in Hzd.
}
rewrite (rngl_div_mul Hon Hiv). 2: {
  intros H; rewrite H in Hzd.
  now apply (rngl_lt_irrefl Hor) in Hzd.
}
rewrite rngl_mul_add_distr_r.
rewrite <- (rngl_add_sub Hos (_ - _) (f x * g x₀)).
rewrite (rngl_add_sub_swap Hop).
rewrite (rngl_sub_sub_swap Hop).
rewrite <- (rngl_mul_sub_distr_r Hop).
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- (rngl_add_sub_assoc Hop).
rewrite <- (rngl_mul_sub_distr_l Hop).
cbn in Hcf, Hcg.
progress unfold rngl_dist in Hcf.
progress unfold rngl_dist in Hcg.
rewrite <- (rngl_abs_opp Hop Hor) in Hcf, Hcg.
rewrite (rngl_opp_sub_distr Hop) in Hcf, Hcg.
remember (f x₀ - f x)%L as a.
remember (g x₀ - g x)%L as b.
rewrite (rngl_add_comm (_ * _ * _)).
rewrite (rngl_mul_mul_swap Hic u).
rewrite <- (rngl_mul_assoc (f x₀)).
rewrite (rngl_mul_comm Hic (f x₀)).
remember (u * d_dist x x₀)%L as c.
remember (v * d_dist x x₀)%L as d.
move x before x₀.
move a before x; move b before a; move c before b; move d before c.
move Heqb before Heqa.
move Hf at bottom.
move Hg at bottom.
rewrite (rngl_mul_comm Hic _ b).
progress unfold rngl_dist.
progress unfold rngl_dist in Hf.
progress unfold rngl_dist in Hg.
rewrite (rngl_sub_add_distr Hos).
rewrite (rngl_add_sub_swap Hop).
rewrite <- (rngl_mul_sub_distr_r Hop).
rewrite <- (rngl_add_sub Hos (_ - _) (b  * f x₀)).
rewrite <- (rngl_add_sub_swap Hop).
rewrite rngl_add_add_swap.
rewrite (rngl_add_sub_swap Hop).
rewrite <- (rngl_add_sub_assoc Hop _ (b * f x₀)).
rewrite <- (rngl_mul_sub_distr_r Hop).
rewrite (rngl_add_sub_swap Hop).
rewrite <- (rngl_sub_sub_distr Hop).
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite <- Heqa.
rewrite (rngl_mul_comm Hic b).
(* lemma *)
rewrite <- (rngl_add_opp_r Hop).
eapply (rngl_le_trans Hor); [ apply (rngl_abs_triangle Hop Hor) | ].
rewrite (rngl_abs_opp Hop Hor).
eapply (rngl_le_trans Hor). {
  apply (rngl_add_le_mono_r Hop Hor).
  apply (rngl_abs_triangle Hop Hor).
}
do 2 rewrite (rngl_abs_mul Hop Hi1 Hor).
eapply (rngl_le_trans Hor). {
  apply (rngl_add_le_mono_r Hop Hor).
  apply (rngl_add_le_mono_r Hop Hor).
  apply (rngl_mul_le_mono_nonneg_r Hop Hor).
  apply (rngl_abs_nonneg Hop Hor).
  apply Hf.
}
rewrite (rngl_mul_mul_swap Hic).
eapply (rngl_le_trans Hor). {
  apply (rngl_add_le_mono_r Hop Hor).
  apply (rngl_add_le_mono_r Hop Hor).
  apply (rngl_le_trans Hor _ (ε * d_dist x x₀ / 4)). 2: {
    apply (rngl_le_refl Hor).
  }
  rewrite <- (rngl_div_mul_mul_div Hic Hiv).
  apply (rngl_mul_le_mono_nonneg_r Hop Hor _ _ _ Hzed).
  apply -> (rngl_le_div_r Hon Hop Hiv Hor); [ | easy ].
  rewrite (rngl_mul_mul_swap Hic).
  rewrite <- rngl_mul_assoc.
  rewrite (rngl_div_mul_mul_div Hic Hiv).
  apply (rngl_le_div_l Hon Hop Hiv Hor). {
    apply (rngl_add_nonneg_pos Hor).
    apply (rngl_mul_nonneg_nonneg Hos Hor _ _ Hz4').
    apply (rngl_abs_nonneg Hop Hor).
    apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
  }
  apply (rngl_mul_le_mono_nonneg_l Hop Hor).
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_le_add_r Hor).
  apply (rngl_0_le_1 Hon Hos Hor).
}
rewrite (rngl_add_comm (_ / _)).
eapply (rngl_le_trans Hor). {
  apply (rngl_add_le_mono_r Hop Hor).
  apply (rngl_add_le_mono_r Hop Hor).
  apply (rngl_mul_le_mono_nonneg_r Hop Hor).
  apply (rngl_abs_nonneg Hop Hor).
  apply Hg.
}
rewrite (rngl_mul_mul_swap Hic).
eapply (rngl_le_trans Hor). {
  apply (rngl_add_le_mono_r Hop Hor).
  apply (rngl_add_le_mono_r Hop Hor).
  apply (rngl_le_trans Hor _ (ε * d_dist x x₀ / 4)). 2: {
    apply (rngl_le_refl Hor).
  }
  rewrite <- (rngl_div_mul_mul_div Hic Hiv).
  apply (rngl_mul_le_mono_nonneg_r Hop Hor _ _ _ Hzed).
  apply -> (rngl_le_div_r Hon Hop Hiv Hor); [ | easy ].
  rewrite (rngl_mul_mul_swap Hic).
  rewrite <- rngl_mul_assoc.
  rewrite (rngl_div_mul_mul_div Hic Hiv).
  apply (rngl_le_div_l Hon Hop Hiv Hor). {
    apply (rngl_add_nonneg_pos Hor).
    apply (rngl_mul_nonneg_nonneg Hos Hor _ _ Hz4').
    apply (rngl_abs_nonneg Hop Hor).
    apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
  }
  apply (rngl_mul_le_mono_nonneg_l Hop Hor).
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_le_add_r Hor).
  apply (rngl_0_le_1 Hon Hos Hor).
}
(* voilà. Mais il reste ce fichu terme rngl_abs (a * b) *)
(* ça doit se démontrer par la continuité de f et de g *)
rewrite (rngl_abs_mul Hop Hi1 Hor).
eapply (rngl_le_trans Hor). {
  apply (rngl_add_le_mono_l Hop Hor).
  apply (rngl_mul_le_compat_nonneg Hor). {
    split; [ | apply (rngl_lt_le_incl Hor), Hcf ].
    apply (rngl_abs_nonneg Hop Hor).
  } {
    split; [ | apply (rngl_lt_le_incl Hor), Hcg ].
    apply (rngl_abs_nonneg Hop Hor).
  }
}
rewrite fold_rngl_squ.
rewrite (rngl_squ_div Hic Hon Hos Hiv); [ | easy ].
rewrite <- (rngl_mul_2_l Hon).
rewrite (rngl_squ_sqrt Hon); [ | now apply (rngl_lt_le_incl Hor) ].
...
eapply (rngl_le_trans Hor). {
  apply (rngl_add_le_compat Hor). {
    apply (rngl_add_le_compat Hor). {

....

Theorem derivative_mul :
  ∀ A lt da db (f g f' g' : A → T),
  is_derivative lt da db f f'
  → is_derivative lt da db g g'
  → is_derivative lt da db
      (λ x, (f x * g x)%L)
      (λ x, (f x * g' x + f' x * g x)%L).
Proof.
intros * Hf Hg.
...
*)

End a.
