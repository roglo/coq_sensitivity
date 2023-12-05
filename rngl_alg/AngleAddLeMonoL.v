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
Require Import (*RealLike*) TrigoWithoutPi AngleLeSubAdd.
Require Import AngleAddOverflowLe.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

Theorem angle_sub_move_0_r :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2, (θ1 - θ2)%A = 0%A ↔ θ1 = θ2.
Proof.
intros Hic Hon Hop Hed.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
split; intros H12. {
  apply (angle_sub_move_r Hic Hon Hop Hed) in H12.
  now rewrite (angle_add_0_l Hon Hos) in H12.
} {
  apply (angle_sub_move_r Hic Hon Hop Hed).
  now rewrite (angle_add_0_l Hon Hos).
}
Qed.

Theorem angle_add_overflow_straight_straight :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  angle_add_overflow angle_straight angle_straight = true.
Proof.
intros Hon Hop Hc1.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
progress unfold angle_add_overflow.
rewrite (angle_straight_add_straight Hon Hop).
progress unfold angle_ltb; cbn.
rewrite (rngl_leb_refl Hor).
apply rngl_ltb_lt.
apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
Qed.

(* pas très satisfait de cette preuve. Elle a marché, certes,
   mais me paraît bien compliquée. Il y aurait sûrement un
   moyen de la rendre plus simple, mais j'ai pas le temps
   de regarder. Tant pis, c'est prouvé, c'est déjà ça. Et
   puis ce théorème est important. *)
Theorem angle_add_overflow_false_comm :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → angle_add_overflow θ2 θ1 = false.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
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
rewrite (angle_add_comm Hic θ2).
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
    rewrite (angle_add_comm Hic).
    apply angle_add_overflow_le_lemma_111; try easy.
    now rewrite (angle_add_comm Hic).
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  destruct (rngl_eq_dec Hed (rngl_cos θ2) (- 1)) as [Hc2o1| Ho1c2]. {
    apply (eq_rngl_cos_opp_1 Hic Hon Hop Hed) in Hc2o1.
    subst θ2.
    rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs12.
    rewrite (rngl_cos_add_straight_r Hon Hop).
    apply -> (rngl_opp_le_compat Hop Hor).
    apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
    apply (rngl_le_antisymm Hor) in Hzs12; [ | easy ].
    symmetry in Hzs12.
    apply (eq_rngl_sin_0 Hic Hon Hop Hed) in Hzs12.
    destruct Hzs12; subst θ1; [ apply (rngl_le_refl Hor) | ].
    rewrite (angle_straight_add_straight Hon Hop) in Haov.
    exfalso.
    apply (rngl_nlt_ge Hor) in Haov.
    apply Haov; cbn.
    apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
  }
  rewrite (angle_add_comm Hic).
  apply angle_add_overflow_le_lemma_2 with (θ2 := θ1); try easy.
  now apply (rngl_lt_le_incl Hor).
  now rewrite (angle_add_comm Hic).
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
    rewrite (angle_add_comm Hic).
    apply angle_add_overflow_le_lemma_11; try easy.
    now apply (rngl_lt_le_incl Hor).
    now rewrite (angle_add_comm Hic).
  }
  apply (rngl_leb_gt Hor) in Hzs1.
  apply rngl_leb_le in Haov.
  apply (rngl_nlt_ge Hor).
  intros Hc12.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  (**)
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    remember (θ1 + angle_right)%A as θ eqn:Hθ.
    apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
    subst θ1; rename θ into θ1.
    rewrite <- (angle_add_sub_swap Hic Hop) in Haov, Hc12 |-*.
    rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs1 |-*.
    rewrite (rngl_cos_sub_right_r Hon Hop) in Haov, Haov, Hzc1, Hc12.
    apply (rngl_opp_neg_pos Hop Hor) in Hzs1.
    apply (rngl_opp_nonneg_nonpos Hop Hor).
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
      exfalso.
      remember (θ2 + angle_right)%A as θ eqn:Hθ.
      apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
      subst θ2; rename θ into θ2.
      rewrite (angle_add_sub_assoc Hop) in Haov, Hc12.
      rewrite (rngl_sin_sub_right_r Hon Hop) in Haov, Hzs2, Hc12.
      rewrite (rngl_cos_sub_right_r Hon Hop) in Hzc2, Hc12.
      apply (rngl_opp_neg_pos Hop Hor) in Hzs2.
      apply (rngl_le_opp_r Hop Hor) in Haov.
      apply (rngl_lt_opp_l Hop Hor) in Hc12.
      apply (rngl_nlt_ge Hor) in Haov.
      apply Haov; clear Haov; cbn.
      rewrite (rngl_add_sub_assoc Hop).
      rewrite (rngl_add_sub_swap Hop).
      rewrite (rngl_sub_mul_r_diag_l Hon Hop).
      apply (rngl_add_nonneg_pos Hor).
      apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
      apply (rngl_le_0_sub Hop Hor).
      apply (rngl_sin_bound Hon Hop Hiv Hic Hed Hor).
      now apply (rngl_mul_pos_pos Hop Hor Hii).
    }
    apply (rngl_nle_gt Hor) in Hc2z.
    remember (θ2 + angle_straight)%A as θ eqn:Hθ.
    apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
    subst θ2; rename θ into θ2.
    rewrite (angle_add_sub_assoc Hop) in Haov, Hc12 |-*.
    rewrite (rngl_sin_sub_straight_r Hon Hop) in Haov, Hzs2, Hc12.
    rewrite (rngl_cos_sub_straight_r Hon Hop) in Hc2z, Hc12 |-*.
    apply (rngl_le_opp_r Hop Hor) in Haov.
    apply (rngl_opp_neg_pos Hop Hor) in Hzs2, Hc2z.
    apply (rngl_opp_lt_compat Hop Hor) in Hc12.
    apply (rngl_opp_nonpos_nonneg Hop Hor).
    exfalso.
    apply (rngl_nlt_ge Hor) in Haov.
    apply Haov; clear Haov.
    apply (rngl_add_nonneg_pos Hor); [ easy | ].
    eapply (rngl_le_lt_trans Hor); [ | apply Hc12 ].
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  remember (θ1 + angle_straight)%A as θ eqn:Hθ.
  apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
  subst θ1; rename θ into θ1.
  rewrite <- (angle_add_sub_swap Hic Hop) in Haov, Hc12 |-*.
  rewrite (rngl_sin_sub_straight_r Hon Hop) in Hzs1 |-*.
  rewrite (rngl_cos_sub_straight_r Hon Hop) in Haov, Haov, Hc1z, Hc12.
  apply (rngl_opp_le_compat Hop Hor) in Haov.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs1, Hc1z.
  apply (rngl_lt_opp_l Hop Hor) in Hc12.
  apply (rngl_opp_nonneg_nonpos Hop Hor).
  destruct (rngl_le_dec Hor (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
    cbn.
    apply (rngl_add_nonpos_nonpos Hor).
    apply (rngl_mul_nonneg_nonpos Hop Hor).
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
    apply (rngl_mul_nonneg_nonpos Hop Hor); [ | easy ].
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nle_gt Hor) in Hzc2.
  remember (θ2 + angle_right)%A as θ eqn:Hθ.
  apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
  subst θ2; rename θ into θ2.
  rewrite (angle_add_sub_assoc Hop) in Haov, Hc12 |-*.
  rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs2 |-*.
  rewrite (rngl_cos_sub_right_r Hon Hop) in Haov, Hzc2, Hc12, Hc12.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs2.
  apply (rngl_opp_nonpos_nonneg Hop Hor).
  apply (rngl_nlt_ge Hor).
  intros Hc12z.
  apply (rngl_nlt_ge Hor) in Haov.
  apply Haov; clear Haov.
  remember (angle_right - θ2)%A as θ eqn:Hθ.
  apply (angle_sub_move_l Hic Hon Hop Hed) in Hθ.
  subst θ2; rename θ into θ2; move θ2 before θ1.
  rewrite (angle_add_comm Hic) in Hc12, Hc12z |-*.
  rewrite <- (angle_sub_sub_distr Hic Hop) in Hc12, Hc12z |-*.
  rewrite (rngl_sin_sub_right_l Hon Hos) in Hc12, Hzc2, Hc12 |-*.
  rewrite (rngl_cos_sub_right_l Hon Hop) in Hzs2, Hc12z.
  rewrite (rngl_sin_sub_anticomm Hic Hop) in Hc12z.
  apply (rngl_opp_neg_pos Hop Hor) in Hc12z.
  rewrite (rngl_cos_sub_comm Hic Hop) in Hc12.
  (**)
  rewrite (rngl_cos_sub_comm Hic Hop) in Hc12 |-*.
  apply (rngl_lt_iff Hor).
  split. {
    apply rngl_sin_cos_nonneg_sin_sub_nonneg_cos_le; try easy.
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
    rewrite (angle_sub_sub_distr Hic Hop).
    rewrite (angle_sub_diag Hic Hon Hop Hed).
    rewrite (angle_add_0_l Hon Hos).
    now apply (rngl_lt_le_incl Hor).
  }
  intros H.
  apply (rngl_cos_eq Hic Hon Hop Hed) in H.
  destruct H as [H| H]. {
    apply (angle_sub_move_l Hic Hon Hop Hed) in H.
    rewrite (angle_sub_diag Hic Hon Hop Hed) in H.
    subst θ2.
    now apply (rngl_lt_irrefl Hor) in Hzs2.
  }
  rewrite (angle_opp_sub_distr Hic Hop) in H.
  rewrite (rngl_sin_sub_anticomm Hic Hop) in Hc12z.
  rewrite <- H in Hc12z.
  apply (rngl_opp_pos_neg Hop Hor) in Hc12z.
  apply (rngl_lt_le_incl Hor) in Hc12z.
  now apply (rngl_nlt_ge Hor) in Hc12z.
}
Qed.

Theorem rngl_sin_add_nonneg :
  rngl_has_opp T = true →
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L.
Proof.
intros Hop.
destruct ac as (Hiv, Hc2, Hor).
intros * Hzs1 Hzs2 Hcs1 Hcs2.
cbn.
apply (rngl_add_nonneg_nonneg Hor).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
Qed.

Theorem rngl_sin_add_pos_1 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 < rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 < rngl_sin (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros  * Hs1z Hs2z Hc1z Hc2z.
cbn.
apply (rngl_add_pos_nonneg Hor).
now apply (rngl_mul_pos_pos Hop Hor Hii).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
Qed.

Theorem rngl_sin_add_pos_2 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (0 < rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 < rngl_cos θ2)%L
  → (0 < rngl_sin (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros  * Hs1z Hs2z Hc1z Hc2z.
cbn.
apply (rngl_add_nonneg_pos Hor).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
now apply (rngl_mul_pos_pos Hop Hor Hii).
Qed.

Theorem rngl_cos_sub_nonneg :
  rngl_has_opp T = true →
  ∀ θ1 θ2 : angle T,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos (θ1 - θ2))%L.
Proof.
intros Hop.
destruct ac as (Hiv, Hc2, Hor).
intros * Hzs1 Hzs2 Hcs1 Hcs2.
cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
apply (rngl_add_nonneg_nonneg Hor).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
now apply (rngl_mul_nonneg_nonneg Hop Hor).
Qed.

Theorem rngl_sin_add_nonneg_sin_nonneg :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin θ1)%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
intros * Haov12 Hzs12.
apply (rngl_nlt_ge Hor).
intros Hs1z.
remember (θ1 + angle_right)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ1; rename θ into θ1.
rewrite <- (angle_add_sub_swap Hic Hop) in Hzs12.
rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs12, Hs1z.
apply (rngl_opp_neg_pos Hop Hor) in Hs1z.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
progress unfold angle_add_overflow in Haov12.
apply angle_ltb_ge in Haov12.
apply angle_nlt_ge in Haov12.
apply Haov12; clear Haov12.
rewrite <- (angle_add_sub_swap Hic Hop).
progress unfold angle_ltb.
rewrite (rngl_sin_sub_right_r Hon Hop).
generalize Hzs12; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
rewrite (rngl_sin_sub_right_r Hon Hop).
generalize Hs1z; intros H.
apply (rngl_opp_lt_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
now rewrite H; clear H.
Qed.

Theorem rngl_cos_add_nonneg_cos_add_nonneg :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_sin θ2 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos (θ1 + θ3))%L
  → (0 ≤ rngl_cos (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
intros * Hzs1 Hzs2 Hzs3 Hzc1 Hzc2 Hzc3 H23 Hzc13.
eapply (rngl_le_trans Hor); [ apply Hzc13 | cbn ].
apply (rngl_sub_le_compat Hop Hor). {
  apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ easy | ].
  generalize H23; intros H32.
  now apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff in H32.
}
now apply (rngl_mul_le_mono_nonneg_l Hop Hor).
Qed.

Theorem angle_add_le_mono_l_lemma_1 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
intros * Haov13 Hzs2 Hzs3 Hzc1 Hzs12 Hzs13 H23.
generalize Hzs13; intros Hzs1.
apply rngl_sin_add_nonneg_sin_nonneg in Hzs1; try easy.
apply angle_le_sub_le_add_l_lemma_1; try easy. {
  rewrite (angle_add_comm Hic).
  now rewrite (angle_add_sub Hic Hon Hop Hed).
} {
  rewrite (angle_add_comm Hic).
  now rewrite (angle_add_sub Hic Hon Hop Hed).
}
Qed.

Theorem angle_add_le_mono_l_lemma_2 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_cos θ1 < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Haov13 Hzs1 Hzs2 Hzs3 Hc1z Hzs12 Hzs13 H23.
remember (θ1 - angle_right)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1.
move θ1 after θ2.
rewrite (angle_add_add_swap Hic Hop) in Hzs13, Hzs12.
rewrite (angle_add_add_swap Hic Hop).
rewrite (angle_add_add_swap Hic Hop _ _ θ2).
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs13, Hzs12, Hzs1.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc1z.
do 2 rewrite (rngl_cos_add_right_r Hon Hop).
apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
apply -> (rngl_opp_le_compat Hop Hor).
move Hc1z after Hzs2; move Hzs1 before Hzs3.
specialize rngl_sin_nonneg_cos_le_sin_le as H1.
specialize (H1 Hic Hon Hop Hed θ3 θ2 Hzs3 Hzs2 H23).
destruct (rngl_le_dec Hor 0 (rngl_cos θ3))%L as [Hzc3| Hc3z]. {
  move Hzc3 before Hzs1.
  apply rngl_leb_le in Hzc3.
  rewrite Hzc3 in H1.
  rename H1 into Hs23.
  apply rngl_leb_le in Hzc3.
  destruct (rngl_lt_dec Hor (rngl_cos θ2) 0)%L as [Hc2z| Hzc2]. {
    apply (rngl_nle_gt Hor) in Hc2z.
    exfalso; apply Hc2z; clear Hc2z.
    eapply (rngl_le_trans Hor); [ apply Hzc3 | easy ].
  }
  apply (rngl_nlt_ge Hor) in Hzc2.
  move Hzc2 before Hzs1.
  rename Hzs12 into Hzc12; rename Hzs13 into Hzc13.
  assert (Hzs12 : (0 ≤ rngl_sin (θ1 + θ2))%L). {
    apply (rngl_lt_le_incl Hor) in Hc1z.
    now apply (rngl_sin_add_nonneg Hop).
  }
  assert (Hzs13 : (0 ≤ rngl_sin (θ1 + θ3))%L). {
    apply (rngl_lt_le_incl Hor) in Hc1z.
    now apply (rngl_sin_add_nonneg Hop).
  }
  specialize rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff as H1.
  apply H1; try easy.
  clear H1.
  apply angle_add_le_mono_l_lemma_1; try easy.
  progress unfold angle_add_overflow.
  apply angle_ltb_ge.
  progress unfold angle_leb.
  generalize Hc1z; intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  apply rngl_leb_le in Hzs13.
  rewrite Hzs13.
  apply rngl_leb_le in Hzs13.
  apply rngl_leb_le.
  apply angle_le_sub_le_add_l_lemma_1; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  rewrite (angle_sub_diag Hic Hon Hop Hed).
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  rewrite (angle_sub_diag Hic Hon Hop Hed).
  apply (rngl_le_refl Hor).
}
apply rngl_leb_nle in Hc3z.
rewrite Hc3z in H1.
apply (rngl_leb_gt Hor) in Hc3z.
apply (rngl_nlt_ge Hor) in Hzs13.
exfalso; apply Hzs13; clear Hzs13.
apply (rngl_lt_iff Hor).
split. {
  cbn.
  apply (rngl_le_sub_0 Hop Hor).
  apply (rngl_le_trans Hor _ 0).
  apply (rngl_mul_nonneg_nonpos Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
}
intros Hc13.
apply (eq_rngl_cos_0 Hic Hon Hop Hed) in Hc13.
destruct Hc13 as [Hc13| Hc13]. {
  apply (angle_add_move_l Hic Hon Hop Hed) in Hc13.
  subst θ3.
  apply (rngl_nle_gt Hor) in Hc3z.
  apply Hc3z.
  rewrite (rngl_cos_sub_right_l Hon Hop).
  now apply (rngl_lt_le_incl Hor).
}
apply (angle_add_move_l Hic Hon Hop Hed) in Hc13.
subst θ3.
progress unfold angle_add_overflow in Haov13.
apply angle_ltb_ge in Haov13.
apply angle_nlt_ge in Haov13.
apply Haov13; clear Haov13.
rewrite (angle_add_sub_assoc Hop).
rewrite angle_add_opp_r.
rewrite (angle_add_sub Hic Hon Hop Hed).
rewrite (angle_sub_diag Hic Hon Hop Hed).
progress unfold angle_ltb.
rewrite (rngl_sin_add_right_r Hon Hos).
rewrite (rngl_leb_refl Hor).
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
apply rngl_ltb_lt.
rewrite (rngl_cos_add_right_r Hon Hop).
apply (rngl_lt_opp_l Hop Hor); cbn.
apply (rngl_add_pos_nonneg Hor); [ easy | ].
apply (rngl_0_le_1 Hon Hop Hor).
Qed.

Theorem angle_add_le_mono_l_lemma_3 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Haov13 Hzs2 Hzs3 Hzs12 Hzs13 H23.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
  move Hzc1 before Hzs3.
  now apply angle_add_le_mono_l_lemma_1.
}
apply (rngl_nle_gt Hor) in Hc1z.
move Hc1z before Hzs3.
destruct (rngl_le_dec Hor 0 (rngl_sin θ1))%L as [Hzs1| Hs1z]. {
  move Hzs1 after Hzs2.
  now apply angle_add_le_mono_l_lemma_2.
}
apply (rngl_nle_gt Hor) in Hs1z.
move Hs1z after Hzs2.
remember (θ1 - angle_straight)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1.
move θ1 after θ2.
rewrite (angle_add_add_swap Hic Hop) in Hzs13, Hzs12 |-*.
rewrite (angle_add_add_swap Hic Hop _ _ θ2).
rewrite (rngl_sin_add_straight_r Hon Hop) in Hs1z, Hzs13, Hzs12.
rewrite (rngl_cos_add_straight_r Hon Hop) in Hc1z.
do 2 rewrite (rngl_cos_add_straight_r Hon Hop).
apply (rngl_opp_neg_pos Hop Hor) in Hs1z, Hc1z.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs13, Hzs12.
apply -> (rngl_opp_le_compat Hop Hor).
move Hs1z before Hzs2; move Hc1z before Hzs3.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ2))%L as [Hzc2| Hc2z]. {
  move Hzc2 before Hc1z.
  exfalso.
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  apply (rngl_lt_le_incl Hor) in Hc1z.
  now apply rngl_sin_add_pos_2.
}
apply (rngl_nlt_ge Hor) in Hc2z.
remember (θ2 - angle_right)%A as θ eqn:Hθ.
apply (angle_add_move_r Hic Hon Hop Hed) in Hθ.
subst θ2; rename θ into θ2; move θ2 before θ1.
rewrite (angle_add_assoc Hop) in Hzs12 |-*.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs2, Hzs12.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc2z, H23 |-*.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc2z.
apply (rngl_le_opp_r Hop Hor) in H23.
apply (rngl_le_opp_l Hop Hor).
move Hc2z before Hs1z; move Hzs2 after Hc1z.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ3))%L as [Hzc3| Hc3z]. {
  move Hzc3 before Hzs2.
  exfalso.
  apply (rngl_nlt_ge Hor) in Hzs13.
  apply Hzs13; clear Hzs13.
  apply (rngl_lt_le_incl Hor) in Hc1z.
  now apply rngl_sin_add_pos_2.
}
apply (rngl_nlt_ge Hor) in Hc3z.
remember (θ3 - angle_right)%A as θ eqn:Hθ.
apply (angle_add_move_r Hic Hon Hop Hed) in Hθ.
subst θ3; rename θ into θ3; move θ3 before θ2.
rewrite (angle_add_assoc Hop) in Hzs13 |-*.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs3, Hzs13.
rewrite (rngl_cos_add_right_r Hon Hop) in H23, Hc3z |-*.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc3z.
rewrite (rngl_add_opp_l Hop) in H23.
rewrite (rngl_add_opp_r Hop).
apply -> (rngl_le_sub_0 Hop Hor) in H23.
apply (rngl_le_0_sub Hop Hor).
move Hc3z before Hc2z; move Hzs3 after Hzs2.
generalize H23; intros H32.
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff in H32; try easy.
move H32 before H23.
assert (Hs12z : (0 ≤ rngl_sin (θ1 + θ2))%L). {
  apply (rngl_lt_le_incl Hor) in Hs1z, Hc1z.
  now apply (rngl_sin_add_nonneg Hop).
}
assert (Hs13z : (0 ≤ rngl_sin (θ1 + θ3))%L). {
  apply (rngl_lt_le_incl Hor) in Hs1z, Hc1z.
  now apply (rngl_sin_add_nonneg Hop).
}
apply rngl_cos_cos_sin_sin_neg_sin_le_cos_le_iff; try easy.
apply angle_add_le_mono_l_lemma_1; try easy; cycle 1.
now apply (rngl_lt_le_incl Hor).
progress unfold angle_add_overflow.
apply angle_ltb_ge.
progress unfold angle_leb.
generalize Hs1z; intros H.
apply (rngl_lt_le_incl Hor) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hs13z; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_leb_le.
apply angle_add_overflow_le_lemma_111; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
Qed.


Theorem angle_add_le_mono_l_lemma_8 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  angle_add_overflow θ1 (θ2 - angle_straight)%A = false
  → (0 ≤ rngl_cos θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 < rngl_cos θ2)%L
  → (0 < rngl_sin (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov12 Hzc1 Hzs2 Hc2z.
  rewrite (H1 (rngl_sin _)) in Hzs2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
intros * Haov12 Hzc1 Hzs2 Hc2z.
destruct (rngl_lt_dec Hor 0 (rngl_sin θ1))%L as [Hzs1| Hs1z]. {
  apply (rngl_lt_le_incl Hor) in Hzs2.
  now apply rngl_sin_add_pos_2.
}
apply (rngl_nlt_ge Hor) in Hs1z.
apply (rngl_nle_gt Hor).
intros Hzs12.
remember (θ1 + angle_right)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ1; rename θ into θ1.
rewrite <- (angle_add_sub_swap Hic Hop) in Hzs12.
rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs12, Hs1z.
rewrite (rngl_cos_sub_right_r Hon Hop) in Hzc1.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hs1z, Hzs12.
progress unfold angle_add_overflow in Haov12.
apply angle_ltb_ge in Haov12.
apply angle_nlt_ge in Haov12.
apply Haov12; clear Haov12.
rewrite (angle_add_sub_assoc Hop).
rewrite <- (angle_add_sub_swap Hic Hop).
progress unfold angle_ltb.
rewrite (rngl_sin_sub_straight_r Hon Hop).
rewrite (rngl_sin_sub_right_r Hon Hop).
rewrite (rngl_opp_involutive Hop).
rewrite (rngl_sin_sub_right_r Hon Hop).
generalize Hs1z; intros H.
apply (rngl_lt_eq_cases Hor) in H.
destruct H as [H| H]. {
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_leb_gt Hor) in H.
  rewrite H; clear H.
  rewrite (rngl_cos_sub_straight_r Hon Hop).
  do 2 rewrite (rngl_cos_sub_right_r Hon Hop).
  destruct (0 ≤? rngl_cos _)%L; [ easy | ].
  apply rngl_ltb_lt.
  apply (rngl_lt_opp_l Hop Hor).
  apply (rngl_add_pos_nonneg Hor); [ | easy ].
  apply (rngl_lt_iff Hor).
  split. {
    apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z.
    now apply (rngl_sin_add_nonneg Hop).
  }
  intros H; symmetry in H.
  apply (eq_rngl_sin_0 Hic Hon Hop Hed) in H.
  destruct H as [H| H]. {
    apply (angle_add_move_l Hic Hon Hop Hed) in H.
    rewrite (angle_sub_0_l Hon Hos) in H.
    subst θ2.
    cbn in Hzs2.
    apply (rngl_opp_pos_neg Hop Hor) in Hzs2.
    now apply (rngl_nle_gt Hor) in Hzs2.
  }
  apply (angle_add_move_l Hic Hon Hop Hed) in H.
  subst θ2.
  rewrite (rngl_cos_sub_straight_l Hon Hop) in Hc2z.
  apply (rngl_opp_pos_neg Hop Hor) in Hc2z.
  now apply (rngl_nle_gt Hor) in Hc2z.
}
exfalso.
symmetry in H.
apply (eq_rngl_cos_0 Hic Hon Hop Hed) in H.
destruct H; subst θ1. {
  rewrite (rngl_cos_add_right_l Hon Hop) in Hzs12.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
  now apply (rngl_nlt_ge Hor) in Hzs12.
}
apply (rngl_nlt_ge Hor) in Hzc1.
apply Hzc1.
apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
Qed.

Theorem angle_add_le_mono_l_lemma_9 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  angle_add_overflow θ1 (θ2 - angle_straight)%A = false
  → (rngl_cos θ1 < 0)%L
  → (rngl_sin θ1 < 0)%L
  → (0 < rngl_sin (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
intros * Haov12 Hc1z Hs1z.
apply (rngl_nle_gt Hor).
intros Hzs12.
remember (θ1 + angle_straight)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ1; rename θ into θ1.
rewrite <- (angle_add_sub_swap Hic Hop) in Hzs12.
rewrite (rngl_sin_sub_straight_r Hon Hop) in Hs1z, Hzs12.
rewrite (rngl_cos_sub_straight_r Hon Hop) in Hc1z.
apply (rngl_opp_neg_pos Hop Hor) in Hs1z, Hc1z.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzs12.
progress unfold angle_add_overflow in Haov12.
apply angle_ltb_ge in Haov12.
apply angle_nlt_ge in Haov12.
apply Haov12; clear Haov12.
rewrite (angle_add_sub_assoc Hop).
rewrite <- (angle_add_sub_swap Hic Hop).
rewrite <- (angle_sub_add_distr Hic Hop).
rewrite (angle_straight_add_straight Hon Hop).
rewrite (angle_sub_0_r Hon Hop).
progress unfold angle_ltb.
rewrite (rngl_sin_sub_straight_r Hon Hop).
generalize Hs1z; intros H.
apply (rngl_opp_lt_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply (rngl_nle_gt Hor) in H.
apply (rngl_leb_nle) in H.
rewrite H; clear H.
rewrite (rngl_cos_sub_straight_r Hon Hop).
apply rngl_leb_le in Hzs12.
now rewrite Hzs12.
Qed.

Theorem angle_add_le_mono_l_lemma_11 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  (rngl_sin θ2 < 0)%L
  → (rngl_cos θ2 < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → angle_add_overflow θ1 θ2 = true.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hzs2 Hc2z Hzs12.
remember (θ2 + angle_straight)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ2; rename θ into θ2.
rewrite (angle_add_sub_assoc Hop) in Hzs12.
rewrite (rngl_sin_sub_straight_r Hon Hop) in Hzs2, Hzs12.
rewrite (rngl_cos_sub_straight_r Hon Hop) in Hc2z.
apply (rngl_opp_neg_pos Hop Hor) in Hzs2, Hc2z.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Bool.not_false_iff_true.
  intros H.
  apply Hzs12; clear Hzs12.
  now apply angle_add_le_mono_l_lemma_8.
}
apply (rngl_nle_gt Hor) in Hc1z.
destruct (rngl_lt_dec Hor (rngl_sin θ1) 0)%L as [Hs1z| Hzs1]. {
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Bool.not_false_iff_true.
  intros H.
  apply Hzs12; clear Hzs12.
  now apply angle_add_le_mono_l_lemma_9.
}
apply (rngl_nlt_ge Hor) in Hzs1.
remember (θ1 - angle_right)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1.
rewrite (angle_add_add_swap Hic Hop) in Hzs12.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1, Hzs12.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc1z.
apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
progress unfold angle_add_overflow.
rewrite (angle_add_sub_assoc Hop).
rewrite (angle_add_add_swap Hic Hop).
rewrite (angle_add_sub_swap Hic Hop).
rewrite <- (angle_sub_sub_distr Hic Hop).
rewrite (angle_straight_sub_right Hon Hop).
progress unfold angle_ltb.
rewrite (rngl_sin_sub_right_r Hon Hop).
generalize Hzs12; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
rewrite (rngl_sin_add_right_r Hon Hos).
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
rewrite (rngl_cos_add_right_r Hon Hop).
rewrite (rngl_cos_sub_right_r Hon Hop).
apply rngl_ltb_lt.
apply (rngl_lt_le_trans Hor _ 0); [ now apply (rngl_opp_neg_pos Hop Hor) | ].
apply (rngl_lt_le_incl Hor) in Hc1z, Hzs2, Hc2z.
now apply (rngl_sin_add_nonneg Hop).
Qed.

Theorem angle_add_le_mono_l_lemma_4 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  angle_add_overflow θ1 (θ2 - angle_right)%A = false
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 < rngl_cos θ2)%L
  → (rngl_cos (θ1 + θ2) ≤ 0)%L
  → False.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Haov12 Hzs1 Hzc2 Hzc1 Hzs2 Hzs12.
progress unfold angle_add_overflow in Haov12.
apply angle_ltb_ge in Haov12.
apply angle_nlt_ge in Haov12.
apply Haov12; clear Haov12.
rewrite (angle_add_sub_assoc Hop).
progress unfold angle_ltb.
rewrite (rngl_sin_sub_right_r Hon Hop).
generalize Hzs12; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
apply rngl_ltb_lt.
rewrite (rngl_cos_sub_right_r Hon Hop).
remember (angle_right - θ2)%A as θ eqn:Hθ.
apply (angle_sub_move_l Hic Hon Hop Hed) in Hθ.
subst θ2; rename θ into θ2.
rewrite (angle_add_sub_assoc Hop) in Hzs12 |-*.
rewrite (angle_add_sub_swap Hic Hop) in Hzs12 |-*.
rewrite (rngl_sin_sub_right_l Hon Hos) in Hzc2.
rewrite (rngl_sin_add_right_r Hon Hos).
rewrite (rngl_cos_sub_right_l Hon Hop) in Hzs2.
rewrite (rngl_cos_add_right_r Hon Hop) in Hzs12.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzs12.
rewrite (rngl_cos_sub_comm Hic Hop).
apply (rngl_lt_iff Hor).
split. {
  rewrite (rngl_cos_sub_comm Hic Hop).
  apply rngl_sin_cos_nonneg_sin_sub_nonneg_cos_le; try easy. {
    cbn.
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_sub_opp_r Hop).
    apply (rngl_add_nonneg_nonneg Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
    apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
    now apply (rngl_lt_le_incl Hor).
  } {
    rewrite (angle_sub_sub_distr Hic Hop).
    rewrite (angle_sub_diag Hic Hon Hop Hed).
    rewrite (angle_add_0_l Hon Hos).
    now apply (rngl_lt_le_incl Hor).
  }
}
intros H.
apply (rngl_cos_eq Hic Hon Hop Hed) in H.
destruct H. {
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  rewrite (rngl_sin_sub_anticomm Hic Hop).
  rewrite <- H.
  apply (rngl_opp_neg_pos Hop Hor).
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  intros H1; symmetry in H1.
  apply (eq_rngl_sin_0 Hic Hon Hop Hed) in H1.
  move H1 at top.
  destruct H1; subst θ1. {
    rewrite (angle_sub_0_r Hon Hop) in H.
    subst θ2.
    now apply (rngl_lt_irrefl Hor) in Hzs2.
  }
  apply (angle_add_move_r Hic Hon Hop Hed) in H.
  rewrite (angle_straight_add_straight Hon Hop) in H.
  subst θ2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
rewrite (angle_opp_sub_distr Hic Hop) in H.
apply (angle_sub_move_l Hic Hon Hop Hed) in H.
rewrite (angle_sub_diag Hic Hon Hop Hed) in H.
subst θ2.
now apply (rngl_lt_irrefl Hor) in Hzs2.
Qed.

Theorem angle_add_le_mono_l_lemma_5 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ θ1 θ2,
  angle_add_overflow θ1 (θ2 - angle_right)%A = false
  → (rngl_cos (θ1 + θ2) ≤ 0)%L
  → (rngl_sin θ1 < 0)%L
  → False.
Proof.
intros Hon Hop.
destruct ac as (Hiv, Hc2, Hor).
intros * Haov12 Hzs12 Hs1z.
progress unfold angle_add_overflow in Haov12.
apply angle_ltb_ge in Haov12.
apply angle_nlt_ge in Haov12.
apply Haov12; clear Haov12.
rewrite (angle_add_sub_assoc Hop).
progress unfold angle_ltb.
rewrite (rngl_sin_sub_right_r Hon Hop).
generalize Hzs12; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hs1z; intros H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
now rewrite H.
Qed.

Theorem angle_add_le_mono_l_lemma_6 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 (θ3 - angle_right)%A = false
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_cos θ2 ≤ 0)%L
  → (0 < rngl_cos θ3)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (rngl_cos (θ1 + θ3) ≤ 0)%L
  → (rngl_sin (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Haov13 Hzs2 Hzc3 Hc2z Hzs3 Hzs12 Hzs13.
remember (θ2 - angle_right)%A as θ eqn:Hθ.
apply (angle_add_move_r Hic Hon Hop Hed) in Hθ.
subst θ2; rename θ into θ2; move θ2 before θ1.
rewrite (angle_add_assoc Hop) in Hzs12 |-*.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs2, Hzs12.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc2z |-*.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc2z.
apply (rngl_le_opp_r Hop Hor).
destruct (rngl_le_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
  exfalso.
  destruct (rngl_le_dec Hor 0 (rngl_sin θ1))%L as [Hzs1| Hs1z]. {
    now apply angle_add_le_mono_l_lemma_4 in Hzs13.
  } {
    apply (rngl_nle_gt Hor) in Hs1z.
    now apply angle_add_le_mono_l_lemma_5 in Hzs13.
  }
}
apply (rngl_nle_gt Hor) in Hc1z.
destruct (rngl_le_dec Hor (rngl_sin θ1) 0)%L as [Hs1z| Hzs1]. {
  apply (rngl_add_nonpos_nonpos Hor); cbn.
  apply (rngl_add_nonpos_nonpos Hor); cbn.
  apply (rngl_mul_nonpos_nonneg Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_mul_nonpos_nonneg Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_add_nonpos_nonpos Hor); cbn.
  apply (rngl_mul_nonpos_nonneg Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_mul_nonpos_nonneg Hop Hor).
}
apply (rngl_nle_gt Hor) in Hzs1.
remember (θ1 - angle_right)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1; move θ1 after θ2.
rewrite (angle_add_add_swap Hic Hop) in Hzs13, Hzs12 |-*.
rewrite (angle_add_add_swap Hic Hop _ _ θ2).
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1.
do 2 rewrite (rngl_sin_add_right_r Hon Hos).
rewrite (rngl_cos_add_right_r Hon Hop) in Hc1z, Hzs13, Hzs12.
apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzs13.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
exfalso.
apply (rngl_nlt_ge Hor) in Hzs12.
apply Hzs12; clear Hzs12.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_lt_le_incl Hor) in Hzs1, Hc1z.
  now apply (rngl_sin_add_nonneg Hop).
}
intros H; symmetry in H.
apply (eq_rngl_sin_0 Hic Hon Hop Hed) in H.
destruct H as [H| H]. {
  apply (angle_add_move_l Hic Hon Hop Hed) in H.
  rewrite (angle_sub_0_l Hon Hos) in H.
  subst θ2.
  cbn in Hc2z.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hc2z.
  now apply (rngl_nlt_ge Hor) in Hc2z.
}
apply (angle_add_move_l Hic Hon Hop Hed) in H.
subst θ2.
rewrite (rngl_cos_sub_straight_l Hon Hop) in Hzs2.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs2.
now apply (rngl_nlt_ge Hor) in Hzs2.
Qed.

Theorem angle_add_le_mono_l_lemma_7 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin θ3 < 0)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov13 Hzs2 Hzs3 Hzs12 Hzs13 Hzc3.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Haov13 Hzs2 Hzs3 Hzs12 Hzs13 Hzc3.
generalize Hzs13; intros Hzs1.
apply rngl_sin_add_nonneg_sin_nonneg in Hzs1; try easy.
remember (θ3 + angle_right)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ3; rename θ into θ3; move θ3 before θ2.
rewrite (angle_add_sub_assoc Hop) in Hzs13 |-*.
rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs3, Hzs13.
rewrite (rngl_cos_sub_right_r Hon Hop) in Hzc3 |-*.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs13.
apply (rngl_opp_neg_pos Hop Hor) in Hzs3.
destruct (rngl_le_dec Hor (rngl_cos θ2) 0)%L as [Hc2z| Hzc2]. {
  now apply angle_add_le_mono_l_lemma_6.
}
apply (rngl_nle_gt Hor) in Hzc2.
move Hzc2 after Hzs3.
apply (rngl_nlt_ge Hor).
intros H123.
progress unfold angle_add_overflow in Haov13.
apply angle_ltb_ge in Haov13.
apply angle_nlt_ge in Haov13.
apply Haov13; clear Haov13.
rewrite (angle_add_sub_assoc Hop).
progress unfold angle_ltb.
rewrite (rngl_sin_sub_right_r Hon Hop).
generalize Hzs13; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
rewrite (rngl_cos_sub_right_r Hon Hop).
apply rngl_ltb_lt.
remember (angle_right - θ3)%A as θ.
apply (angle_sub_move_l Hic Hon Hop Hed) in Heqθ.
subst θ3; rename θ into θ3; move θ3 before θ2.
rewrite (angle_add_comm Hic) in Hzs13 |-*.
rewrite (angle_add_comm Hic _ (_ - _))%A in H123.
rewrite <- (angle_sub_sub_distr Hic Hop) in H123, Hzs13 |-*.
rewrite (rngl_sin_sub_right_l Hon Hos) in Hzc3, H123 |-*.
rewrite (rngl_cos_sub_right_l Hon Hop) in Hzs3, Hzs13.
rewrite (rngl_sin_sub_anticomm Hic Hop) in Hzs13.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzs13.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
  destruct (rngl_eq_dec Hed 0 (rngl_sin (θ1 - θ3)))
      as [Hzs1s3| Hs1s3z]. {
    symmetry in Hzs1s3.
    apply (eq_rngl_sin_0 Hic Hon Hop Hed) in Hzs1s3.
    destruct Hzs1s3 as [H| H]. {
      apply -> (angle_sub_move_0_r Hic Hon Hop Hed) in H.
      subst θ3.
      rewrite (angle_sub_diag Hic Hon Hop Hed) in H123 |-*.
      cbn.
      apply (rngl_lt_iff Hor).
      split; [ apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor) | ].
      intros H.
      apply (eq_rngl_cos_1 Hic Hon Hop Hed) in H.
      subst θ1.
      now apply (rngl_lt_irrefl Hor) in Hzs3.
    }
    apply (angle_sub_move_l Hic Hon Hop Hed) in H.
    subst θ3.
    rewrite (rngl_sin_sub_straight_r Hon Hop) in Hzs3.
    apply (rngl_opp_pos_neg Hop Hor) in Hzs3.
    now apply (rngl_nle_gt Hor) in Hzs3.
  }
  apply not_eq_sym in Hs1s3z.
  apply rngl_cos_lt_rngl_cos_sub; try easy.
  apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff; try easy.
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_lt_iff Hor).
  split; [ now apply rngl_sin_sub_nonneg_sin_le_sin | ].
  intros H.
  apply (rngl_sin_eq Hic Hon Hop Hed) in H.
  destruct H; subst θ3. {
    now rewrite (angle_sub_diag Hic Hon Hop Hed) in Hs1s3z.
  }
  rewrite (rngl_cos_sub_straight_l Hon Hop) in Hzc3.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzc3.
  apply (rngl_le_antisymm Hor) in Hzc3; [ | easy].
  symmetry in Hzc3.
  apply (eq_rngl_cos_0 Hic Hon Hop Hed) in Hzc3.
  destruct Hzc3; subst θ1. {
    rewrite (angle_straight_sub_right Hon Hop) in Hs1s3z.
    now rewrite (angle_sub_diag Hic Hon Hop Hed) in Hs1s3z.
  }
  apply (rngl_nlt_ge Hor) in Hzs1.
  apply Hzs1; cbn.
  apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
}
apply (rngl_nle_gt Hor) in Hc1z.
remember (θ1 - angle_right)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1; move θ1 after θ2.
rewrite (angle_add_sub_swap Hic Hop) in Hzs13.
rewrite (angle_add_add_swap Hic Hop) in H123, Hzs12.
rewrite (angle_sub_add_distr Hic Hop) in H123 |-*.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1, Hzs13, Hzs12.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc1z, H123 |-*.
rewrite (rngl_cos_sub_right_r Hon Hop) in H123 |-*.
apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
apply (rngl_lt_opp_l Hop Hor) in H123.
apply (rngl_lt_opp_l Hop Hor).
destruct (rngl_eq_dec Hed (rngl_cos θ3) 1) as [Hc31| Hc31]. {
  apply (eq_rngl_cos_1 Hic Hon Hop Hed) in Hc31.
  subst θ3.
  now apply (rngl_lt_irrefl Hor) in Hzs3.
}
cbn.
rewrite rngl_add_assoc.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
rewrite (rngl_sub_mul_r_diag_r Hon Hop).
apply (rngl_add_pos_nonneg Hor).
apply (rngl_mul_pos_pos Hop Hor Hii); [ | easy ].
apply (rngl_lt_0_sub Hop Hor).
apply (rngl_lt_iff Hor).
split; [ | easy ].
apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_add_le_mono_l_lemma_12 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  (0 < rngl_cos θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 < rngl_cos θ3)%L
  → (rngl_sin (θ1 + θ2) ≤ 0)%L
  → (rngl_cos (θ1 + θ3) ≤ 0)%L
  → False.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hzc1 Hzs2 Hc2z Hzc3 Hzs3 Hzs12 Hzs13.
destruct (rngl_le_dec Hor 0 (rngl_sin θ1))%L as [Hzs1| Hs1z]. {
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  now apply rngl_sin_add_pos_1.
}
apply (rngl_nle_gt Hor) in Hs1z.
remember (θ1 + angle_right)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ1; rename θ into θ1.
rewrite <- (angle_add_sub_swap Hic Hop) in Hzs13, Hzs12.
rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs12, Hs1z.
rewrite (rngl_cos_sub_right_r Hon Hop) in Hzs13, Hzc1.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzs12.
apply (rngl_opp_neg_pos Hop Hor) in Hs1z.
apply (rngl_nlt_ge Hor) in Hzs13.
apply Hzs13; clear Hzs13.
apply (rngl_lt_le_incl Hor) in Hs1z.
now apply rngl_sin_add_pos_2.
Qed.

Theorem angle_add_le_mono_l_lemma_13 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_cos θ1 ≤ 0)%L
  → (0 ≤ rngl_cos θ2)%L
  → (rngl_sin (θ1 + θ2) ≤ 0)%L
  → angle_add_overflow θ1 (θ2 - angle_straight)%A = true.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzs1 Hzs2 Hzc3 Hc1z Hc2z Hzs12.
  rewrite (H1 (rngl_sin _)) in Hzs2.
  now apply (rngl_lt_irrefl Hor) in Hzs2.
}
intros * Hzs1 Hzs2 Hzc3 Hc1z Hc2z Hzs12.
remember (θ1 - angle_right)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1.
rewrite (angle_add_add_swap Hic Hop) in Hzs12.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1, Hzs12.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc1z.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc1z.
progress unfold angle_add_overflow.
rewrite (angle_add_sub_assoc Hop).
rewrite (angle_add_add_swap Hic Hop).
rewrite (angle_add_sub_swap Hic Hop).
rewrite <- (angle_sub_sub_distr Hic Hop).
rewrite (angle_straight_sub_right Hon Hop).
progress unfold angle_ltb.
rewrite (rngl_sin_sub_right_r Hon Hop).
generalize Hzs12; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
rewrite (rngl_sin_add_right_r Hon Hos).
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
rewrite (rngl_cos_sub_right_r Hon Hop).
rewrite (rngl_cos_add_right_r Hon Hop).
apply rngl_ltb_lt.
apply (rngl_lt_opp_l Hop Hor).
apply (rngl_lt_iff Hor).
split. {
  cbn.
  rewrite rngl_add_assoc.
  rewrite rngl_add_add_swap.
  rewrite (rngl_add_mul_r_diag_l Hon).
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  apply (rngl_le_opp_l Hop Hor).
  apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
}
intros H; symmetry in H.
apply (rngl_add_move_0_r Hop) in H.
generalize Hc1z; intros H1.
rewrite H in H1.
apply (rngl_opp_nonneg_nonpos Hop Hor) in H1.
apply (rngl_nlt_ge Hor) in H1.
apply H1; clear H1.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_lt_le_incl Hor) in Hzs2.
  now apply (rngl_sin_add_nonneg Hop).
}
intros H1; symmetry in H1.
apply (eq_rngl_sin_0 Hic Hon Hop Hed) in H1.
destruct H1 as [H1| H1]. {
  apply (angle_add_move_l Hic Hon Hop Hed) in H1.
  rewrite (angle_sub_0_l Hon Hos) in H1.
  subst θ2.
  cbn in Hzs2.
  apply (rngl_opp_pos_neg Hop Hor) in Hzs2.
  now apply (rngl_nlt_ge Hor) in Hzs2.
}
apply (angle_add_move_l Hic Hon Hop Hed) in H1.
subst θ2.
rewrite (rngl_cos_sub_straight_l Hon Hop) in Hc2z.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hc2z.
apply (rngl_le_antisymm Hor) in Hc2z; [ | easy ].
symmetry in Hc2z.
apply (eq_rngl_cos_0 Hic Hon Hop Hed) in Hc2z.
destruct Hc2z; subst θ1. {
  rewrite (angle_straight_sub_right Hon Hop) in H.
  rewrite (angle_right_add_right Hon Hop) in H.
  cbn in H.
  rewrite (rngl_opp_0 Hop) in H.
  now apply (rngl_1_eq_0_iff Hon Hos) in H.
}
apply (rngl_nlt_ge Hor) in Hc1z.
apply Hc1z; cbn.
apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
Qed.

Theorem angle_add_le_mono_l_lemma_14 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 (θ3 - angle_right)%A = false
  → (0 ≤ rngl_sin θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 < rngl_cos θ3)%L
  → (rngl_sin θ2 ≤ rngl_sin θ3)%L
  → (rngl_cos (θ1 + θ2) ≤ 0)%L
  → (rngl_cos (θ1 + θ3) ≤ 0)%L
  → (rngl_sin (θ1 + θ3) ≤ rngl_sin (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
intros * Haov13 Hzs1 Hzc2 Hzc3 Hzc1 Hzs2 Hzs3 H23 Hzs12 Hzs13.
apply rngl_cos_cos_sin_sin_neg_sin_le_cos_le_iff; try easy. {
  apply (rngl_lt_le_incl Hor) in Hzs3.
  now apply (rngl_sin_add_nonneg Hop).
} {
  apply (rngl_lt_le_incl Hor) in Hzc2.
  now apply (rngl_sin_add_nonneg Hop).
}
apply angle_add_le_mono_l_lemma_3; try easy. {
  apply (angle_add_overflow_le) with (θ2 := (θ3 - angle_right)%A);
    try easy.
  progress unfold angle_leb.
  apply rngl_leb_le in Hzc3.
  rewrite Hzc3.
  apply rngl_leb_le in Hzc3.
  rewrite (rngl_sin_sub_right_r Hon Hop).
  generalize Hzs3; intros H.
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_nle_gt Hor) in H.
  apply rngl_leb_nle in H.
  now rewrite H.
} {
  now apply (rngl_lt_le_incl Hor).
} {
  apply (rngl_lt_le_incl Hor) in Hzc2.
  now apply (rngl_sin_add_nonneg Hop).
} {
  apply (rngl_lt_le_incl Hor) in Hzs3.
  now apply (rngl_sin_add_nonneg Hop).
}
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_add_le_mono_l_lemma_16 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ2 = false
  → angle_add_overflow θ1 θ3 = false
  → (rngl_sin θ2 < 0)%L
  → (rngl_sin θ3 < 0)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_cos θ2 ≤ rngl_cos θ3)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (rngl_cos (θ1 + θ3) ≤ rngl_cos (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Haov12 Haov13 Hzs2 Hzs3 Hzc3 H23 Hzs12 Hzs13.
generalize Hzs13; intros Hzs1.
apply rngl_sin_add_nonneg_sin_nonneg in Hzs1; try easy.
remember (θ3 + angle_right)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ3; rename θ into θ3; move θ3 before θ2.
rewrite (angle_add_sub_assoc Hop) in Hzs13 |-*.
rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs3, Hzs13.
rewrite (rngl_cos_sub_right_r Hon Hop) in Hzc3, H23 |-*.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs13.
apply (rngl_opp_neg_pos Hop Hor) in Hzs3.
destruct (rngl_le_dec Hor (rngl_cos θ2) 0)%L as [Hc2z| Hzc2]. {
  exfalso.
  remember (θ2 + angle_straight)%A as θ eqn:Hθ.
  apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
  subst θ2; rename θ into θ2.
  rewrite (angle_add_sub_assoc Hop) in Hzs12.
  rewrite (rngl_sin_sub_straight_r Hon Hop) in Hzs2, Hzs12.
  rewrite (rngl_cos_sub_straight_r Hon Hop) in H23, Hc2z.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs2.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
  apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc2z.
  apply (rngl_le_opp_l Hop Hor) in H23.
  destruct (rngl_lt_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
    now apply (angle_add_le_mono_l_lemma_12 Hic Hon Hop Hed θ1 θ2 θ3).
  } {
    apply (rngl_nlt_ge Hor) in Hc1z.
    apply Bool.not_true_iff_false in Haov12.
    apply Haov12.
    now apply (angle_add_le_mono_l_lemma_13 Hic Hon Hop Hed _ _ θ3).
  }
}
apply (rngl_nle_gt Hor) in Hzc2.
remember (θ2 + angle_right)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ2; rename θ into θ2; move θ2 before θ1.
rewrite (angle_add_sub_assoc Hop) in Hzs12 |-*.
rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs2, Hzs12.
rewrite (rngl_cos_sub_right_r Hon Hop) in H23, Hzc2 |-*.
apply (rngl_opp_neg_pos Hop Hor) in Hzs2.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
move Hzc2 after Hzc3; move Hzs2 before Hzs3.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  apply (rngl_lt_le_incl Hor) in Hzs2.
  now apply angle_add_le_mono_l_lemma_14.
}
apply (rngl_nle_gt Hor) in Hc1z.
apply (rngl_nlt_ge Hor).
intros Hs123.
progress unfold angle_add_overflow in Haov12.
apply angle_ltb_ge in Haov12.
apply angle_nlt_ge in Haov12.
apply Haov12; clear Haov12.
rewrite (angle_add_sub_assoc Hop).
progress unfold angle_ltb.
rewrite (rngl_sin_sub_right_r Hon Hop).
generalize Hzs12; intros H.
apply (rngl_opp_le_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply rngl_leb_le in Hzs1.
apply rngl_ltb_lt.
rewrite (rngl_cos_sub_right_r Hon Hop).
remember (θ1 - angle_right)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1.
rewrite (angle_add_add_swap Hic Hop) in Hzs13, Hzs12 |-*.
do 2 rewrite (angle_add_add_swap Hic Hop _ angle_right) in Hs123.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1, Hs123, Hs123 |-*.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc1z, Hzs13, Hzs12 |-*.
apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzs13, Hzs12.
apply (rngl_lt_opp_l Hop Hor).
cbn.
rewrite (rngl_add_sub_assoc Hop).
rewrite rngl_add_comm.
rewrite <- (rngl_add_sub_assoc Hop).
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
apply (rngl_add_nonneg_pos Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
now apply (rngl_lt_le_incl Hor).
apply (rngl_mul_pos_pos Hop Hor Hii); [ easy | ].
apply (rngl_lt_0_sub Hop Hor).
apply (rngl_lt_iff Hor).
split; [ apply (rngl_sin_bound Hon Hop Hiv Hic Hed Hor) | ].
intros H.
apply (eq_rngl_sin_1 Hic Hon Hop Hed) in H.
subst θ2.
now apply (rngl_lt_irrefl Hor) in Hzs2.
Qed.

Theorem angle_add_le_mono_l_lemma_18 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ2 = false
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_cos θ2 ≤ rngl_cos θ3)%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc3, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov12 Hzs1 Hzs2 Hzs3 Hzc3 H32 Hzs12.
  rewrite (H1 (rngl_sin _)).
  apply (rngl_le_refl Hor).
}
intros * Haov12 Hzs1 Hzs2 Hzs3 Hzc3 H32 Hzs12.
apply (rngl_nlt_ge Hor).
intros Hzs13.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  apply (rngl_nle_gt Hor) in Hzs13.
  apply Hzs13; clear Hzs13.
  now apply (rngl_sin_add_nonneg Hop).
}
apply (rngl_nle_gt Hor) in Hc1z.
move Hc1z after Hzc3.
remember (θ1 - angle_right)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1; move θ1 after θ3.
rewrite (angle_add_add_swap Hic Hop) in Hzs13, Hzs12.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1, Hzs12, Hzs13.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc1z.
apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
move Hc1z after Hzs3; move Hzs1 before Hzc3.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  move Hzc2 before Hzc3.
  apply (rngl_lt_le_incl Hor) in Hc1z.
  apply (rngl_nle_gt Hor) in Hzs13.
  apply Hzs13; clear Hzs13.
  apply rngl_cos_add_nonneg_cos_add_nonneg with (θ3 := θ2); try easy.
  now apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff.
}
apply (rngl_nle_gt Hor) in Hc2z.
remember (θ2 - angle_right)%A as θ eqn:Hθ.
apply (angle_add_move_r Hic Hon Hop Hed) in Hθ.
subst θ2; rename θ into θ2; move θ2 before θ3.
rewrite (angle_add_assoc Hop) in Hzs12.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs2.
rewrite (rngl_cos_add_right_r Hon Hop) in Hzs12, Hc2z, H32.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
apply (rngl_opp_neg_pos Hop Hor) in Hc2z.
apply (rngl_le_opp_l Hop Hor) in H32.
move Hc2z before Hzs3; move Hzs2 after Hzc3.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ1)) as [H| H]. {
  apply (rngl_nlt_ge Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  apply (rngl_lt_le_incl Hor) in Hc1z.
  now apply rngl_sin_add_pos_1.
}
apply (rngl_nlt_ge Hor) in H.
apply (rngl_le_antisymm Hor) in H; [ | easy ].
symmetry in H.
apply (eq_rngl_cos_0 Hic Hon Hop Hed) in H.
destruct H; subst θ1. {
  rewrite (rngl_sin_add_right_l Hon Hos) in Hzs12.
  apply (rngl_le_antisymm Hor) in Hzs12; [ | easy ].
  symmetry in Hzs12.
  apply (eq_rngl_cos_0 Hic Hon Hop Hed) in Hzs12.
  destruct Hzs12; subst θ2. {
    rewrite (angle_right_add_right Hon Hop) in Haov12.
    now rewrite angle_add_overflow_straight_straight in Haov12.
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  apply Hc2z; cbn.
  apply (rngl_opp_1_le_0 Hon Hop Hor).
}
apply (rngl_nlt_ge Hor) in Hc1z.
apply Hc1z.
apply (rngl_opp_1_le_0 Hon Hop Hor).
Qed.

Theorem angle_add_le_mono_l_lemma_10 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  angle_add_overflow (θ1 + angle_right)%A θ2 = false
  → (0 < rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_cos θ1)%L
  → (rngl_cos θ2 ≤ 0)%L
  → (0 ≤ rngl_cos (θ1 + θ2))%L
  → False.
Proof.
intros Hic Hon Hop Hed.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct ac as (Hiv, Hc2, Hor).
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov12 Hc1z Hzs2 Hzs1 Hc2z Hzs12.
  rewrite (H1 (rngl_sin _)) in Hc1z.
  now apply (rngl_lt_irrefl Hor) in Hc1z.
}
intros * Haov12 Hc1z Hzs2 Hzs1 Hc2z Hzs12.
remember (θ2 - angle_right)%A as θ eqn:Hθ.
apply (angle_add_move_r Hic Hon Hop Hed) in Hθ.
subst θ2; rename θ into θ2; move θ2 before θ1.
rewrite (angle_add_assoc Hop) in Hzs12.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs2.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc2z, Hzs12.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc2z.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
apply (rngl_nlt_ge Hor) in Hzs12.
apply Hzs12; clear Hzs12.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_lt_le_incl Hor) in Hc1z.
  now apply (rngl_sin_add_nonneg Hop).
}
intros H; symmetry in H.
apply (eq_rngl_sin_0 Hic Hon Hop Hed) in H.
destruct H as [H| H]. {
  apply (angle_add_move_l Hic Hon Hop Hed) in H.
  rewrite (angle_sub_0_l Hon Hos) in H.
  subst θ2.
  cbn in Hc2z.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hc2z.
  now apply (rngl_nlt_ge Hor) in Hc2z.
}
apply (angle_add_move_l Hic Hon Hop Hed) in H.
subst θ2.
rewrite (rngl_cos_sub_straight_l Hon Hop) in Hzs2.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs2.
apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
symmetry in Hzs2.
apply (eq_rngl_cos_0 Hic Hon Hop Hed) in Hzs2.
destruct Hzs2; subst θ1. {
  progress unfold angle_add_overflow in Haov12.
  apply angle_ltb_ge in Haov12.
  apply (angle_nlt_ge) in Haov12.
  apply Haov12; clear Haov12.
  rewrite (angle_right_add_right Hon Hop).
  rewrite (angle_sub_add Hic Hon Hop Hed).
  rewrite (angle_straight_add_straight Hon Hop).
  progress unfold angle_ltb; cbn.
  rewrite (rngl_leb_refl Hor).
  apply rngl_ltb_lt.
  apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
}
rewrite (angle_sub_opp_r Hop) in Hc2z.
rewrite (rngl_sin_add_right_r Hon Hos) in Hc2z.
apply (rngl_nlt_ge Hor) in Hc2z.
apply Hc2z; clear Hc2z; cbn.
apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
Qed.

Theorem angle_add_le_mono_l_lemma_19 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ1 θ3 = false
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_sin (θ1 + θ3))%L
  → (0 ≤ rngl_sin (θ1 + θ2))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Haov13 Hzs2 Hzs3 H23 Hzs13.
apply (rngl_nlt_ge Hor).
intros Hzs12.
generalize Hzs13; intros Hzs1.
apply rngl_sin_add_nonneg_sin_nonneg in Hzs1; try easy.
move Hzs1 after Hzs2.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  move Hzc2 after Hzs3.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  now apply angle_add_le_mono_l_lemma_18 with (θ2 := θ3).
} {
  apply (rngl_nle_gt Hor) in Hc2z.
  remember (θ2 - angle_right)%A as θ eqn:Hθ.
  apply (angle_add_move_r Hic Hon Hop Hed) in Hθ.
  subst θ2; rename θ into θ2; move θ2 before θ3.
  rewrite (angle_add_assoc Hop) in Hzs12.
  rewrite (rngl_sin_add_right_r Hon Hos) in Hzs2, Hzs12.
  rewrite (rngl_cos_add_right_r Hon Hop) in Hc2z, H23.
  apply (rngl_opp_neg_pos Hop Hor) in Hc2z.
  apply (rngl_le_opp_r Hop Hor) in H23.
  move Hc2z before Hzs3.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
    apply (rngl_nlt_ge Hor) in H23.
    apply H23; clear H23.
    now apply (rngl_add_nonneg_pos Hor).
  }
  apply (rngl_nle_gt Hor) in Hc3z.
  remember (θ3 - angle_right)%A as θ eqn:Hθ.
  apply (angle_add_move_r Hic Hon Hop Hed) in Hθ.
  subst θ3; rename θ into θ3; move θ3 before θ2.
  rewrite (angle_add_assoc Hop) in Hzs13.
  rewrite (rngl_sin_add_right_r Hon Hos) in Hzs3, Hzs13.
  rewrite (rngl_cos_add_right_r Hon Hop) in H23, Hc3z.
  apply (rngl_opp_neg_pos Hop Hor) in Hc3z.
  rewrite (rngl_add_opp_l Hop) in H23.
  apply -> (rngl_le_sub_0 Hop Hor) in H23.
  move Hc3z before Hc2z.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    apply (rngl_lt_le_incl Hor) in Hc2z, Hc3z.
    now apply rngl_cos_add_nonneg_cos_add_nonneg with (θ3 := θ3).
  } {
    apply (rngl_nle_gt Hor) in Hc1z.
    rewrite (angle_add_comm Hic) in Hzs13.
    apply angle_add_le_mono_l_lemma_10 in Hzs13; try easy.
    2: now apply (rngl_lt_le_incl Hor).
    now apply (angle_add_overflow_false_comm Hic Hon Hop Hed).
  }
}
Qed.

Theorem angle_add_le_mono_l_lemma_20 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 < rngl_cos θ3)%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (rngl_sin (θ1 + θ3) < 0)%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos (θ1 + θ3))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
intros * Hzs2 Hzs3 Hzc3 H23 Hzs12 Hzs13.
assert (Hzc2 : (0 < rngl_cos θ2)%L). {
  eapply (rngl_lt_le_trans Hor); [ apply Hzc3 | apply H23 ].
}
destruct (rngl_lt_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    exfalso.
    apply (rngl_nle_gt Hor) in Hzs12.
    apply Hzs12; clear Hzs12.
    apply (rngl_lt_le_incl Hor) in Hzc2, Hzs1.
    now apply (rngl_sin_add_nonneg Hop).
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  remember (angle_straight - θ1)%A as θ.
  apply (angle_sub_move_l Hic Hon Hop Hed) in Heqθ.
  subst θ1; rename θ into θ1; move θ1 after θ2.
  rewrite <- (angle_sub_sub_distr Hic Hop) in Hzs13, Hzs12.
  do 2 rewrite <- (angle_sub_sub_distr Hic Hop).
  rewrite (rngl_sin_sub_straight_l Hon Hop) in Hzs13, Hzs12.
  rewrite (rngl_cos_sub_straight_l Hon Hop) in Hc1z.
  do 2 rewrite (rngl_cos_sub_straight_l Hon Hop).
  apply -> (rngl_opp_le_compat Hop Hor).
  rewrite (rngl_sin_sub_anticomm Hic Hop) in Hzs13, Hzs12.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs13, Hzs12, Hc1z.
  do 2 rewrite (rngl_cos_sub_comm Hic Hop θ1).
  destruct (rngl_eq_dec Hed (rngl_sin θ2) (rngl_sin θ3)) as
    [Hes23| Hes23]. {
    apply (rngl_sin_eq Hic Hon Hop Hed) in Hes23.
    destruct Hes23; subst θ2; [ apply (rngl_le_refl Hor) | ].
    rewrite (rngl_cos_sub_straight_l Hon Hop) in H23.
    rewrite <- (angle_sub_add_distr Hic Hop) in Hzs12 |-*.
    rewrite (rngl_sin_sub_straight_l Hon Hop) in Hzs12.
    rewrite (rngl_cos_sub_straight_l Hon Hop) in Hzc2 |-*.
    apply (rngl_opp_pos_neg Hop Hor) in Hzc2.
    apply (rngl_le_opp_r Hop Hor).
    cbn.
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_sub_opp_r Hop).
    rewrite (rngl_add_sub_assoc Hop).
    rewrite (rngl_add_add_swap).
    rewrite (rngl_add_sub Hos).
    rewrite <- (rngl_mul_add_distr_r).
    apply (rngl_mul_nonpos_nonneg Hop Hor); [ | ].
    apply (rngl_lt_le_incl Hor) in Hzc2.
    now apply (rngl_add_nonpos_nonpos Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nlt_ge Hor).
  intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply rngl_sin_sub_nonneg in H; try easy. {
    rewrite (angle_sub_sub_distr Hic Hop) in H.
    rewrite (angle_sub_sub_swap Hic Hop) in H.
    rewrite (angle_sub_add Hic Hon Hop Hed) in H.
    apply (rngl_nlt_ge Hor) in H.
    apply H; clear H.
    cbn.
    eapply (rngl_le_lt_trans Hor). {
      apply (rngl_add_le_mono_l Hop Hor).
      apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ easy | ].
      apply H23.
    }
    rewrite (rngl_mul_comm Hic).
    rewrite <- rngl_mul_add_distr_r.
    rewrite (rngl_add_opp_l Hop).
    rewrite (rngl_mul_comm Hic).
    apply (rngl_mul_pos_neg Hop Hor Hid); [ easy | ].
    apply (rngl_lt_sub_0 Hop Hor).
    apply (rngl_lt_iff Hor).
    split; [ | easy ].
    apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nlt_ge Hor) in Hs1z.
destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [Hzc1| Hc1z]. {
  cbn.
  apply (rngl_sub_le_compat Hop Hor).
  now apply (rngl_mul_le_mono_nonpos_l Hop Hor).
  apply (rngl_mul_le_mono_nonpos_l Hop Hor); [ easy | ].
  apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hc1z.
remember (θ1 + angle_right)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ1; rename θ into θ1; move θ1 after θ2.
rewrite <- (angle_add_sub_swap Hic Hop) in Hzs13, Hzs12.
do 2 rewrite <- (angle_add_sub_swap Hic Hop).
rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs13, Hzs12, Hs1z.
rewrite (rngl_cos_sub_right_r Hon Hop) in Hc1z.
do 2 rewrite (rngl_cos_sub_right_r Hon Hop).
apply (rngl_opp_neg_pos Hop Hor) in Hzs13, Hzs12.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hs1z.
assert (Hs12 : (0 ≤ rngl_sin (θ1 + θ2))%L). {
  apply (rngl_lt_le_incl Hor) in Hc1z, Hzc2.
  now apply (rngl_sin_add_nonneg Hop).
}
assert (Hs13 : (0 ≤ rngl_sin (θ1 + θ3))%L). {
  apply (rngl_lt_le_incl Hor) in Hc1z, Hzc3.
  now apply (rngl_sin_add_nonneg Hop).
}
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
apply angle_add_le_mono_l_lemma_3; try easy.
progress unfold angle_add_overflow.
apply angle_ltb_ge.
progress unfold angle_leb.
generalize Hc1z; intros H.
apply (rngl_lt_le_incl Hor) in H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hs13; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
apply rngl_leb_le.
apply angle_add_overflow_le_lemma_111; try easy.
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_add_le_mono_l_lemma_21 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (rngl_cos (θ1 + θ3) < 0)%L
  → (rngl_cos (θ1 + θ2) + rngl_sin (θ1 + θ3) ≤ 0)%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hzs1 Hzs2 Hzs3 Hzc2 Hzc3 Hzs12 Hzc13.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  exfalso.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  now apply (rngl_sin_add_nonneg Hop).
}
apply (rngl_nle_gt Hor) in Hc1z.
remember (θ1 - angle_right)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1; move θ1 after θ2.
rewrite (angle_add_add_swap Hic Hop) in Hzs12, Hzc13.
do 2 rewrite (angle_add_add_swap Hic Hop _ angle_right).
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1, Hzs12 |-*.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc1z, Hzc13 |-*.
apply (rngl_opp_neg_pos Hop Hor) in Hc1z, Hzc13.
rewrite (rngl_add_opp_l Hop).
apply (rngl_le_sub_0 Hop Hor).
destruct (rngl_le_dec Hor (rngl_cos (θ1 + θ3)) 0) as [H| Hzs13]. {
  eapply (rngl_le_trans Hor); [ apply H | ].
  apply (rngl_lt_le_incl Hor) in Hc1z.
  now apply (rngl_sin_add_nonneg Hop).
}
apply (rngl_nle_gt Hor) in Hzs13.
remember (angle_right - θ2)%A as θ eqn:Hθ.
apply (angle_sub_move_l Hic Hon Hop Hed) in Hθ.
subst θ2; rename θ into θ2; move θ2 before θ1.
rewrite (angle_add_comm Hic _ (_ - _)%A) in Hzs12 |-*.
rewrite <- (angle_add_sub_swap Hic Hop) in Hzs12 |-*.
rewrite <- (angle_add_sub_assoc Hop) in Hzs12 |-*.
rewrite (rngl_sin_sub_right_l Hon Hos) in Hzs2.
rewrite (rngl_cos_sub_right_l Hon Hop) in Hzc2.
rewrite (rngl_sin_add_right_l Hon Hos).
rewrite (rngl_cos_add_right_l Hon Hop) in Hzs12.
apply (rngl_opp_neg_pos Hop Hor) in Hzs12.
apply rngl_sin_cos_nonneg_sin_sub_nonneg_cos_le; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
apply (rngl_lt_le_incl Hor) in Hc1z.
now apply rngl_cos_sub_nonneg.
rewrite (angle_sub_sub_distr Hic Hop).
rewrite (angle_add_sub_swap Hic Hop).
rewrite (angle_sub_diag Hic Hon Hop Hed).
rewrite (angle_add_0_l Hon Hos).
now apply (rngl_sin_add_nonneg Hop).
Qed.

(* to be completed
Theorem angle_add_le_mono_l_lemma_22 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  (rngl_sin θ1 < 0)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ2)%L
  → (0 ≤ rngl_cos θ3)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (rngl_cos (θ1 + θ3) < 0)%L
  → (rngl_cos (θ1 + θ2) + rngl_sin (θ1 + θ3) ≤ 0)%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hs1z Hzs2 Hzs3 Hzc2 Hzc3 Hs12z Hs13z.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  exfalso.
  apply (rngl_nle_gt Hor) in Hs13z.
  apply Hs13z; clear Hs13z.
  now apply (rngl_cos_add_nonneg Hic Hon Hop Hed).
...
}
apply (rngl_nle_gt Hor) in Hc1z.
remember (θ1 + angle_straight)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ1; rename θ into θ1.
rewrite <- (angle_add_sub_swap Hic Hop) in Hs13z, Hs12z.
do 2 rewrite <- (angle_add_sub_swap Hic Hop).
rewrite (rngl_sin_sub_straight_r Hon Hop) in Hs1z, Hs12z |-*.
rewrite (rngl_cos_sub_straight_r Hon Hop) in Hc1z, Hs13z |-*.
apply (rngl_opp_neg_pos Hop Hor) in Hc1z, Hs1z, Hs13z, Hs12z.
rewrite (rngl_add_opp_r Hop).
rewrite <- (rngl_opp_add_distr Hop).
apply (rngl_opp_nonpos_nonneg Hop Hor).
remember (angle_right - θ3)%A as θ eqn:Hθ.
apply (angle_sub_move_l Hic Hon Hop Hed) in Hθ.
subst θ3; rename θ into θ3; move θ3 before θ2.
rewrite (angle_add_comm Hic) in Hs13z |-*.
rewrite <- (angle_sub_sub_distr Hic Hop) in Hs13z |-*.
rewrite (rngl_sin_sub_right_l Hon Hos) in Hzs3 |-*.
rewrite (rngl_cos_sub_right_l Hon Hop) in Hs13z, Hzc3.
apply rngl_add_cos_nonneg_when_sin_nonneg; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
rewrite (angle_add_assoc Hop).
rewrite (angle_sub_add Hic Hon Hop Hed).
now apply (rngl_sin_add_nonneg Hop).
apply (rngl_lt_le_incl Hor) in Hs1z, Hc1z.
now apply (rngl_cos_sub_nonneg Hop).
Qed.

Theorem angle_add_le_mono_l_lemma_28 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_cos θ3 ≤ 0)%L
  → (rngl_cos θ3 ≤ rngl_cos θ2)%L
  → (rngl_sin (θ1 + θ2) < 0)%L
  → (rngl_sin (θ1 + θ3) < 0)%L
  → (rngl_cos (θ1 + θ2) ≤ rngl_cos (θ1 + θ3))%L.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzs2 Hzs3 Hc3z Hc32 Hs12z Hs13z.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Hzs2 Hzs3 Hc3z Hc32 Hs12z Hs13z.
remember (θ3 - angle_right)%A as θ eqn:Hθ.
apply (angle_add_move_r Hic Hon Hop Hed) in Hθ.
subst θ3; rename θ into θ3; move θ3 before θ2.
rewrite (angle_add_assoc Hop) in Hs13z |-*.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs3, Hs13z.
rewrite (rngl_cos_add_right_r Hon Hop) in Hc32, Hc3z |-*.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc3z.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  apply (rngl_le_opp_r Hop Hor).
  destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
    now apply angle_add_le_mono_l_lemma_21.
  } {
    apply (rngl_nle_gt Hor) in Hs1z.
    now apply angle_add_le_mono_l_lemma_22.
...
  }
} {
  apply (rngl_nle_gt Hor) in Hc2z.
  apply (rngl_le_opp_l Hop Hor) in Hc32.
  apply (rngl_le_opp_r Hop Hor).
  move Hc2z after Hzs3; move Hc32 after Hs12z.
  remember (θ2 - angle_right)%A as θ eqn:Hθ.
  apply (angle_add_move_r Hic Hon Hop Hed) in Hθ.
  subst θ2; rename θ into θ2; move θ2 before θ3.
  rewrite (angle_add_assoc Hop) in Hs12z |-*.
  rewrite (rngl_sin_add_right_r Hon Hos) in Hzs2, Hs12z.
  rewrite (rngl_cos_add_right_r Hon Hop) in Hc2z, Hc32 |-*.
  apply (rngl_opp_neg_pos Hop Hor) in Hc2z.
  rewrite (rngl_add_opp_r Hop) in Hc32.
  apply -> (rngl_le_0_sub Hop Hor) in Hc32.
  rewrite (rngl_add_opp_l Hop).
  apply (rngl_le_sub_0 Hop Hor).
  move Hc32 after Hs12z.
  destruct (rngl_eq_dec Hed (rngl_cos θ2) 0) as [H| Hc2ez]. {
    apply (eq_rngl_cos_0 Hic Hon Hop Hed) in H.
    destruct H; subst θ2. {
      cbn in Hc32.
      specialize (rngl_sin_bound Hon Hop Hiv Hic Hed Hor θ3) as H.
      apply (rngl_le_antisymm Hor) in Hc32; [ clear H | easy ].
      apply (eq_rngl_sin_1 Hic Hon Hop Hed) in Hc32.
      subst θ3.
      apply (rngl_le_refl Hor).
    }
    exfalso.
    apply (rngl_nle_gt Hor) in Hc2z.
    apply Hc2z; cbn.
    apply (rngl_opp_1_le_0 Hon Hop Hor).
  }
  assert (H : (0 < rngl_cos θ2)%L). {
    apply not_eq_sym in Hc2ez.
    now apply (rngl_lt_iff Hor).
  }
  move H before Hzs2; clear Hzs2.
  rename H into Hzs2; clear Hc2ez.
  destruct (rngl_eq_dec Hed (rngl_cos θ3) 0) as [H| Hc3ez]. {
    apply (eq_rngl_cos_0 Hic Hon Hop Hed) in H.
    destruct H; subst θ3. {
      clear Hc3z Hc32 Hzs3.
      rewrite (rngl_sin_add_right_r Hon Hos).
      rewrite (rngl_cos_add_right_r Hon Hop) in Hs13z.
      apply (rngl_opp_neg_pos Hop Hor) in Hs13z.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
        apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z, Hs13z, Hs12z.
        apply angle_add_le_mono_l_lemma_23; try easy.
      } {
        apply (rngl_nle_gt Hor) in Hc1z.
        apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z, Hs13z, Hc1z.
        apply angle_add_le_mono_l_lemma_24; try easy.
      }
    }
    exfalso.
    apply (rngl_nlt_ge Hor) in Hc3z.
    apply Hc3z; cbn.
    apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
  }
  assert (H : (0 < rngl_cos θ3)%L). {
    apply not_eq_sym in Hc3ez.
    now apply (rngl_lt_iff Hor).
  }
  move H before Hzs3; clear Hzs3.
  rename H into Hzs3; clear Hc3ez.
  destruct (rngl_le_dec Hor 0 (rngl_sin θ1)) as [Hzs1| Hs1z]. {
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z, Hzs3, Hs12z, Hs13z.
      now apply angle_add_le_mono_l_lemma_25.
    } {
      apply (rngl_nle_gt Hor) in Hc1z.
      apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z, Hzs3, Hs12z, Hs13z.
      apply (rngl_lt_le_incl Hor) in Hc1z.
      now apply angle_add_le_mono_l_lemma_26.
    }
  } {
    apply (rngl_nle_gt Hor) in Hs1z.
    apply (rngl_lt_le_incl Hor) in Hzs2, Hc2z.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
      exfalso.
      apply (rngl_nle_gt Hor) in Hs12z.
      apply Hs12z; clear Hs12z.
      now apply (rngl_cos_add_nonneg Hic Hon Hop Hed).
    } {
      apply (rngl_nle_gt Hor) in Hc1z.
      apply (rngl_lt_le_incl Hor) in Hzs3, Hs13z.
      now apply angle_add_le_mono_l_lemma_27.
    }
  }
}
Qed.

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
...
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
*)

End a.
