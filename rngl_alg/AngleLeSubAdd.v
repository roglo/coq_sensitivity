(* just a file for this theorem:
     (θ1 - θ2 ≤ θ3)%A → (θ1 ≤ θ2 + θ3)%A
   actually not used, should be removed one day,
   its lemmas being tranfered where necessary.
     It is a shame, it was a big effort, and its statement is simple and
   perhaps could be used one day, but if I keep all this kind of theorem,
   my software is going to be unnecessarily huge.
 *)
(*
Set Nested Proofs Allowed.
*)
Require Import Utf8 Arith.
Require Import Main.RingLike.
Require Import TrigoWithoutPi.
Require Import TacChangeAngle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

(*
Theorem eq_rngl_sin_opp_1 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ, (rngl_sin θ = -1)%L → (θ = - angle_right)%A.
Proof.
intros Hic Hon Hop Hed * Hθ.
destruct ac as (Hiv, Hc2, Hor).
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
destruct θ as (c, s, Hcs).
cbn in Hθ |-*.
subst s.
apply eq_angle_eq; cbn.
f_equal.
apply (cos2_sin2_prop_add_squ Hon Hop Hic Hed) in Hcs.
rewrite (rngl_squ_opp Hop) in Hcs.
rewrite (rngl_squ_1 Hon) in Hcs.
apply (rngl_add_sub_eq_r Hos) in Hcs.
rewrite (rngl_sub_diag Hos) in Hcs.
symmetry in Hcs.
now apply (eq_rngl_squ_0 Hos Hid) in Hcs.
Qed.
*)

Theorem rngl_sin_sub_nonneg_sin_le_sin :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_cos θ1)%L
  → (0 ≤ rngl_sin (θ1 - θ2))%L
  → (rngl_sin θ2 ≤ rngl_sin θ1)%L.
Proof.
destruct_ac; intros * Hzs1 Hcs1 Hzs12.
cbn in Hzs12.
rewrite rngl_add_comm in Hzs12.
rewrite (rngl_mul_opp_r Hop) in Hzs12.
rewrite (rngl_add_opp_l Hop) in Hzs12.
apply -> (rngl_le_0_sub Hop Hor) in Hzs12.
apply (rngl_mul_le_mono_nonneg_l Hop Hor (rngl_cos θ1)) in Hzs12; [ | easy ].
rewrite rngl_mul_assoc in Hzs12.
rewrite fold_rngl_squ in Hzs12.
specialize (cos2_sin2_1 θ1) as H1.
apply (rngl_add_move_r Hop) in H1.
rewrite H1 in Hzs12; clear H1.
rewrite (rngl_mul_sub_distr_r Hop) in Hzs12.
rewrite (rngl_mul_1_l Hon) in Hzs12.
apply (rngl_le_sub_le_add_r Hop Hor) in Hzs12.
rewrite (rngl_mul_comm Hic) in Hzs12.
progress unfold rngl_squ in Hzs12.
do 2 rewrite <- rngl_mul_assoc in Hzs12.
rewrite <- rngl_mul_add_distr_l in Hzs12.
rewrite (rngl_mul_comm Hic (rngl_cos θ2)) in Hzs12.
rewrite <- rngl_cos_sub in Hzs12.
eapply (rngl_le_trans Hor); [ apply Hzs12 | ].
apply (rngl_le_0_sub Hop Hor).
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
apply (rngl_le_0_sub Hop Hor).
apply rngl_cos_bound.
Qed.

(*
Theorem angle_le_0_r :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ, (θ ≤ 0)%A → θ = 0%A.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
intros * Hθ.
progress unfold angle_leb in Hθ.
cbn in Hθ.
rewrite (rngl_leb_refl Hor) in Hθ.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs; [ | easy ].
apply rngl_leb_le in Hzs, Hθ.
specialize (rngl_cos_bound Hon Hop Hiv Hic Hed Hor θ) as H1.
apply (rngl_le_antisymm Hor) in Hθ; [ | easy ].
now apply (eq_rngl_cos_1 Hic Hon Hop Hed) in Hθ.
Qed.
*)

Theorem angle_straight_sub_right :
  (angle_straight - angle_right)%A = angle_right.
Proof.
destruct_ac.
intros.
apply eq_angle_eq; cbn.
do 2 rewrite (rngl_mul_0_r Hos).
rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_diag Hos).
f_equal.
rewrite (rngl_squ_opp_1 Hon Hop).
apply rngl_add_0_l.
Qed.

(*
Theorem rngl_cos_nonneg :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ θ, (0 ≤ rngl_cos θ)%L ↔ (θ ≤ angle_right ∨ - angle_right ≤ θ)%A.
Proof.
intros Hon Hop.
destruct ac as (Hiv, Hc2, Hor).
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  progress unfold angle_leb.
  cbn.
  rewrite (H1 1)%L.
  rewrite (rngl_leb_refl Hor).
  rewrite (H1 (rngl_sin _)).
  rewrite (rngl_leb_refl Hor).
  rewrite (H1 (rngl_cos _)).
  rewrite (rngl_leb_refl Hor).
  split; intros H; [ now left | ].
  apply (rngl_le_refl Hor).
}
intros.
progress unfold angle_leb.
cbn.
specialize (rngl_0_le_1 Hon Hop Hor) as H.
apply rngl_leb_le in H.
rewrite H; clear H.
assert (H : (-1 < 0)%L). {
  apply (rngl_opp_neg_pos Hop Hor).
  apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
}
apply (rngl_leb_gt Hor) in H.
rewrite H; clear H.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  split; intros H. {
    left.
    now apply rngl_leb_le.
  }
  destruct H as [H| H]; [ | easy ].
  now apply rngl_leb_le.
}
split; intros H. {
  right.
  now apply rngl_leb_le.
}
destruct H as [H| H]; [ easy | ].
now apply rngl_leb_le.
Qed.

Theorem rngl_cos_nonpos :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ θ, (rngl_cos θ ≤ 0)%L ↔ (angle_right ≤ θ ≤ (- angle_right)%A)%A.
Proof.
intros Hon Hop.
destruct ac as (Hiv, Hc2, Hor).
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  progress unfold angle_leb.
  cbn.
  rewrite (H1 1)%L.
  rewrite (rngl_leb_refl Hor).
  rewrite (H1 (rngl_sin _)).
  rewrite (rngl_leb_refl Hor).
  rewrite (H1 (rngl_cos _)).
  rewrite (rngl_leb_refl Hor).
  split; intros H. {
    rewrite (rngl_opp_0 Hop).
    now rewrite (rngl_leb_refl Hor).
  }
  apply (rngl_le_refl Hor).
}
intros.
progress unfold angle_leb.
cbn.
specialize (rngl_0_le_1 Hon Hop Hor) as H.
apply rngl_leb_le in H.
rewrite H; clear H.
assert (H : (-1 < 0)%L). {
  apply (rngl_opp_neg_pos Hop Hor).
  apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
}
apply (rngl_leb_gt Hor) in H.
rewrite H; clear H.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  split; intros H. {
    split; [ now apply rngl_leb_le | easy ].
  }
  destruct H as (H, _).
  now apply rngl_leb_le.
}
split; intros H. {
  split; [ easy | ].
  now apply rngl_leb_le.
}
destruct H as (_, H).
now apply rngl_leb_le.
Qed.

Theorem angle_opp_0 :
  rngl_has_opp T = true →
  (- 0 = 0)%A.
Proof.
intros Hop.
apply eq_angle_eq; cbn.
f_equal.
apply (rngl_opp_0 Hop).
Qed.

Theorem angle_sub_not_overflow_sin_neg_sin_sub_nonneg :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2,
  angle_add_overflow θ1 (- θ2)%A = false
  → (rngl_sin θ1 < 0)%L
  → (0 ≤ rngl_sin (θ1 - θ2))%L
  → False.
Proof.
intros Hic Hon Hop Hed.
destruct ac as (Hiv, Hc2, Hor).
intros * Hsov Hzs1 Hzs12.
destruct (rngl_lt_dec Hor 0 (rngl_sin θ2)) as [Hzs2| Hs2z]. {
  progress unfold angle_add_overflow in Hsov.
  apply angle_ltb_ge in Hsov.
  apply angle_nlt_ge in Hsov.
  apply Hsov; clear Hsov.
  rewrite angle_add_opp_r.
  progress unfold angle_ltb.
  apply rngl_leb_le in Hzs12.
  rewrite Hzs12.
  apply rngl_leb_le in Hzs12.
  generalize Hzs1; intros H.
  apply (rngl_nle_gt Hor) in H.
  apply rngl_leb_nle in H.
  now rewrite H.
}
apply (rngl_nlt_ge Hor) in Hs2z.
remember (θ1 - angle_straight)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1.
move θ1 after θ2.
rewrite (angle_add_sub_swap Hic Hop) in Hzs12.
rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs1, Hzs12.
rewrite <- (rngl_sin_sub_anticomm Hic Hop) in Hzs12.
apply (rngl_opp_neg_pos Hop Hor) in Hzs1.
remember (θ2 - angle_straight)%A as θ.
apply (angle_add_move_r Hic Hon Hop Hed) in Heqθ.
subst θ2; rename θ into θ2.
move θ2 before θ1.
rewrite (angle_add_sub_swap Hic Hop) in Hzs12.
rewrite (rngl_sin_add_straight_r Hon Hop) in Hs2z, Hzs12.
rewrite <- (rngl_sin_sub_anticomm Hic Hop) in Hzs12.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hs2z.
progress unfold angle_add_overflow in Hsov.
apply angle_ltb_ge in Hsov.
apply angle_nlt_ge in Hsov.
apply Hsov; clear Hsov.
rewrite angle_add_opp_r.
rewrite (angle_sub_add_distr Hic Hop).
rewrite (angle_add_sub_swap Hic Hop).
rewrite <- (angle_add_sub_assoc Hop).
rewrite (angle_sub_diag Hic Hon Hop Hed).
rewrite (angle_add_0_r Hon Hos).
progress unfold angle_ltb.
apply rngl_leb_le in Hzs12.
rewrite Hzs12.
apply rngl_leb_le in Hzs12.
rewrite (rngl_sin_add_straight_r Hon Hop).
generalize Hzs1; intros H.
apply (rngl_opp_lt_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
now rewrite H.
Qed.
*)

Theorem rngl_sin_sub_lt_sin_l :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 < rngl_sin θ2)%L
  → (0 < rngl_cos θ1)%L
  → (rngl_sin (θ1 - θ2) < rngl_sin θ1)%L.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hc1z Hzs2 Hzc1.
cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
apply (rngl_lt_sub_lt_add_r Hop Hor).
eapply (rngl_le_lt_trans Hor _ (rngl_sin θ1)). {
  apply (rngl_le_0_sub Hop Hor).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cos_bound.
}
apply (rngl_lt_add_r Hos Hor).
now apply (rngl_mul_pos_pos Hop Hor Hii).
Qed.

Theorem angle_le_sub_le_add_l_lemma_1 :
  ∀ θ1 θ2 θ3,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (0 ≤ rngl_cos θ2)%L
  → (rngl_cos θ3 ≤ rngl_cos (θ1 - θ2))%L
  → (0 ≤ rngl_sin (θ1 - θ2))%L
  → (0 ≤ rngl_sin (θ2 + θ3))%L
  → (rngl_cos (θ2 + θ3) ≤ rngl_cos θ1)%L.
Proof.
(* thanks Geoffroy *)
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite H1, (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Hzs1 Hzs2 Hzs3 Hzc2 Hc123 Hzs12 Hzs23.
destruct (rngl_le_dec Hor 0 (rngl_cos θ3))%L as [Hzc3| Hc3z]. {
  move Hzc3 before Hzs3.
  generalize Hc123; intros Hc123v.
  cbn in Hc123 |-*.
  rewrite (rngl_mul_opp_r Hop) in Hc123.
  rewrite (rngl_sub_opp_r Hop) in Hc123.
  apply (rngl_le_sub_le_add_r Hop Hor).
  apply (rngl_mul_le_mono_nonneg_l Hop Hor (rngl_cos θ2)) in Hc123;
    [ | easy ].
  rewrite rngl_mul_add_distr_l in Hc123.
  rewrite (rngl_mul_comm Hic _ (_ * _))%L in Hc123.
  rewrite <- rngl_mul_assoc in Hc123.
  rewrite fold_rngl_squ in Hc123.
  specialize (cos2_sin2_1 θ2) as H1.
  apply (rngl_add_move_r Hop) in H1.
  rewrite H1 in Hc123; clear H1.
  rewrite (rngl_mul_sub_distr_l Hop) in Hc123.
  rewrite (rngl_mul_1_r Hon) in Hc123.
  eapply (rngl_le_trans Hor); [ apply Hc123 | ].
  rewrite <- (rngl_add_sub_swap Hop).
  rewrite <- (rngl_add_sub_assoc Hop).
  apply (rngl_add_le_mono_l Hop Hor).
  progress unfold rngl_squ.
  do 2 rewrite rngl_mul_assoc.
  rewrite <- (rngl_mul_sub_distr_r Hop).
  rewrite (rngl_mul_comm Hic _ (rngl_sin θ2)).
  apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ easy | ].
  rewrite (rngl_mul_comm Hic (rngl_cos θ2)).
  rewrite <- rngl_sin_sub.
  specialize rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff as H1.
  assert (H : (0 ≤ rngl_cos (θ1 - θ2))%L). {
    now apply (rngl_le_trans Hor _ (rngl_cos θ3)).
  }
  now apply (H1 _ _ Hzs12 Hzs3 H Hzc3).
}
apply (rngl_nle_gt Hor) in Hc3z.
change_angle_sub_r θ3 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs3.
progress sin_cos_add_sub_right_hyp T Hc123.
progress sin_cos_add_sub_right_hyp T Hc3z.
progress sin_cos_add_sub_right_hyp T Hzs23.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1))%L as [Hzc1| Hc1z]. {
  move Hzc1 before Hc3z.
  apply (rngl_add_nonneg_nonneg Hor); [ | easy ].
  apply (rngl_lt_le_incl Hor) in Hc3z.
  now apply (rngl_sin_add_nonneg).
}
apply (rngl_nle_gt Hor) in Hc1z.
change_angle_sub_r θ1 angle_right.
progress sin_cos_add_sub_right_hyp T Hzs1.
progress sin_cos_add_sub_right_hyp T Hzs12.
progress sin_cos_add_sub_right_hyp T Hc123.
progress sin_cos_add_sub_right_hyp T Hc1z.
progress sin_cos_add_sub_right_goal T.
destruct (rngl_eq_dec Hed (rngl_cos θ2) 0) as [Hc2z| Hc2z]. {
  exfalso.
  cbn in Hc123.
  rewrite (rngl_mul_opp_r Hop) in Hc123.
  rewrite (rngl_add_opp_r Hop) in Hc123.
  apply (rngl_le_sub_le_add_r Hop Hor) in Hc123.
  apply (rngl_nlt_ge Hor) in Hzs23.
  apply Hzs23; clear Hzs23; cbn.
  rewrite Hc2z.
  rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_sub_0_l Hop).
  apply (rngl_opp_neg_pos Hop Hor).
  apply (rngl_mul_pos_pos Hop Hor Hii); [ | easy ].
  apply eq_rngl_cos_0 in Hc2z.
  destruct Hc2z; subst θ2. {
    apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
  }
  rewrite angle_sub_opp_r in Hzs12.
  rewrite rngl_cos_add_right_r in Hzs12.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
  now apply (rngl_nlt_ge Hor) in Hzs12.
}
rename Hc123 into Hs123.
destruct (rngl_le_dec Hor (rngl_cos θ1) (rngl_cos (θ2 + θ3)))
    as [Hc123| Hc231]. {
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii _ _ (rngl_cos θ2)). {
    apply not_eq_sym in Hc2z.
    now apply (rngl_lt_iff Hor).
  }
  cbn in Hs123 |-*.
  rewrite (rngl_mul_opp_r Hop) in Hs123.
  rewrite (rngl_add_opp_r Hop) in Hs123.
  apply (rngl_le_sub_le_add_l Hop Hor) in Hs123.
  rewrite rngl_mul_add_distr_r.
  rewrite rngl_add_comm.
  rewrite (rngl_mul_mul_swap Hic).
  rewrite fold_rngl_squ.
  specialize (cos2_sin2_1 θ2) as H1.
  apply (rngl_add_move_r Hop) in H1.
  rewrite H1; clear H1.
  rewrite (rngl_mul_sub_distr_r Hop).
  rewrite (rngl_mul_1_l Hon).
  rewrite <- (rngl_add_sub_swap Hop).
  rewrite <- (rngl_add_sub_assoc Hop).
  apply (rngl_le_sub_le_add_l Hop Hor).
  apply (rngl_le_sub_le_add_r Hop Hor) in Hs123.
  eapply (rngl_le_trans Hor); [ apply Hs123 | ].
  progress unfold rngl_squ.
  do 2 rewrite <- rngl_mul_assoc.
  rewrite <- (rngl_mul_sub_distr_l Hop).
  rewrite (rngl_mul_comm Hic (rngl_cos θ3)).
  rewrite <- rngl_cos_add.
  rewrite (rngl_mul_comm Hic).
  now apply (rngl_mul_le_mono_nonneg_l Hop Hor).
}
apply (rngl_nle_gt Hor) in Hc231.
move Hc231 before Hs123.
specialize rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff as H1.
apply (rngl_lt_le_incl Hor) in Hc1z, Hc231.
apply H1; try easy.
cbn.
apply (rngl_add_nonneg_nonneg Hor). {
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
} {
  apply (rngl_lt_le_incl Hor) in Hc3z.
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
}
Qed.

(*
Theorem angle_le_sub_le_add_l_lemma_2 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ2 θ3 = false
  → angle_add_overflow θ1 (- θ2)%A = false
  → (θ2 ≤ θ1)%A
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (0 ≤ rngl_sin θ3)%L
  → (rngl_cos θ2 < 0)%L
  → (rngl_cos θ3 ≤ rngl_cos (θ1 - θ2))%L
  → (0 ≤ rngl_sin (θ1 - θ2))%L
  → (0 ≤ rngl_sin (θ2 + θ3))%L
  → (rngl_cos (θ2 + θ3) ≤ rngl_cos θ1)%L.
Proof.
intros Hic Hon Hop Hed.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros * Haov Hsov H21 Hzs1 Hzs2 Hzs3 Hc2z Hc123 Hzs12 Hzs23.
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
intros * Haov Hsov H21 Hzs1 Hzs2 Hzs3 Hc2z Hc123 Hzs12 Hzs23.
remember (angle_straight - θ2)%A as θ.
apply (angle_sub_move_l Hic Hon Hop Hed) in Heqθ.
subst θ2; rename θ into θ2.
move θ2 before θ1.
rewrite <- (angle_sub_sub_distr Hic Hop) in Hzs23 |-*.
rewrite (angle_sub_sub_distr Hic Hop) in Hzs12, Hc123.
rewrite (angle_add_comm Hic) in Hzs12, Hc123.
rewrite (angle_add_sub_assoc Hop) in Hzs12, Hc123.
rewrite (rngl_cos_sub_straight_l Hon Hop) in Hc2z |-*.
rewrite (rngl_sin_sub_straight_l Hon Hop) in Hzs2, Hzs23.
rewrite (rngl_cos_sub_straight_r Hon Hop) in Hc123.
rewrite (rngl_sin_sub_straight_r Hon Hop) in Hzs12.
apply (rngl_opp_neg_pos Hop Hor) in Hc2z.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12.
apply (rngl_le_opp_r Hop Hor) in Hc123.
rewrite <- (rngl_sub_0_l Hop).
apply (rngl_le_sub_le_add_r Hop Hor).
assert (Hc1z : (rngl_cos θ1 ≤ 0)%L). {
  progress unfold angle_leb in H21.
  rewrite (rngl_sin_sub_straight_l Hon Hop) in H21.
  apply rngl_leb_le in Hzs1, Hzs2.
  rewrite Hzs1, Hzs2 in H21.
  rewrite (rngl_cos_sub_straight_l Hon Hop) in H21.
  apply rngl_leb_le in Hzs1, Hzs2.
  apply rngl_leb_le in H21.
  eapply (rngl_le_trans Hor); [ apply H21 | ].
  apply (rngl_opp_nonpos_nonneg Hop Hor).
  now apply (rngl_lt_le_incl Hor).
}
remember (angle_straight - θ1)%A as θ.
apply (angle_sub_move_l Hic Hon Hop Hed) in Heqθ.
subst θ1; rename θ into θ1.
move θ1 after θ2.
move H21 before θ3.
rewrite (angle_add_comm Hic) in Hc123, Hzs12.
rewrite <- (angle_sub_sub_distr Hic Hop) in Hc123, Hzs12.
rewrite (rngl_cos_sub_straight_l Hon Hop) in Hc123, Hc1z |-*.
rewrite (rngl_sin_sub_straight_l Hon Hop) in Hzs1, Hzs12.
rewrite (rngl_add_opp_r Hop) in Hc123.
apply -> (rngl_le_sub_0 Hop Hor) in Hc123.
rewrite (rngl_add_opp_l Hop).
apply (rngl_le_0_sub Hop Hor).
rewrite (rngl_sin_sub_anticomm Hic Hop) in Hzs12.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc1z, Hzs12.
move Hc1z after Hc2z.
apply (rngl_nlt_ge Hor).
intros H23.
assert (H : (0 < rngl_sin θ2)%L). {
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  intros H; symmetry in H.
  apply (eq_rngl_sin_0 Hic Hon Hop Hed) in H.
  destruct H; subst θ2. {
    cbn in Hzs12, Hzs23.
    rewrite (rngl_mul_1_l Hon) in Hzs12, Hzs23.
    rewrite (rngl_mul_0_l Hos) in Hzs12, Hzs23.
    rewrite rngl_add_0_r in Hzs12, Hzs23.
    apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12, Hzs23.
    apply (rngl_le_antisymm Hor) in Hzs1; [ | easy ].
    apply (rngl_le_antisymm Hor) in Hzs3; [ | easy ].
    apply (eq_rngl_sin_0 Hic Hon Hop Hed) in Hzs1, Hzs3.
    destruct Hzs1; subst θ1. {
      destruct Hzs3; subst θ3. {
        cbn in H23.
        apply (rngl_nle_gt Hor) in H23.
        apply H23.
        rewrite (rngl_mul_1_l Hon).
        rewrite (rngl_mul_0_l Hos).
        rewrite (rngl_sub_0_r Hos).
        apply (rngl_le_refl Hor).
      }
      rewrite (angle_sub_0_r Hon Hop) in Haov.
      progress unfold angle_add_overflow in Haov.
      progress unfold angle_ltb in Haov.
      rewrite (rngl_sin_add_straight_r Hon Hop) in Haov.
      rewrite rngl_cos_add_straight_r in Haov.
      cbn in Haov.
      rewrite (rngl_opp_0 Hop) in Haov.
      rewrite (rngl_leb_refl Hor) in Haov.
      rewrite (rngl_opp_involutive Hop) in Haov.
      apply rngl_ltb_nlt in Haov.
      apply Haov.
      apply (rngl_le_lt_trans Hor _ 0%L). {
        apply (rngl_opp_nonpos_nonneg Hop Hor).
        apply (rngl_0_le_1 Hon Hop Hor).
      }
      apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
    }
    apply (rngl_nle_gt Hor) in H23.
    apply H23; cbn.
    rewrite (rngl_mul_1_l Hon).
    rewrite (rngl_mul_0_l Hos).
    rewrite (rngl_sub_0_r Hos).
    apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  apply Hc2z; cbn.
  apply (rngl_opp_nonpos_nonneg Hop Hor).
  apply (rngl_0_le_1 Hon Hop Hor).
}
move H before Hzs2; clear Hzs2; rename H into Hzs2.
progress unfold angle_add_overflow in Haov.
progress unfold angle_ltb in Haov.
rewrite <- (angle_sub_sub_distr Hic Hop) in Haov.
do 2 rewrite (rngl_sin_sub_straight_l Hon Hop) in Haov.
do 2 rewrite (rngl_cos_sub_straight_l Hon Hop) in Haov.
generalize Hzs2; intros H.
apply (rngl_lt_le_incl Hor) in H.
apply rngl_leb_le in Hzs23, H.
rewrite Hzs23, H in Haov; clear H.
apply rngl_leb_le in Hzs23.
apply (rngl_ltb_ge Hor) in Haov.
apply (rngl_opp_le_compat Hop Hor) in Haov.
destruct (rngl_lt_dec Hor (rngl_cos θ3) 0)%L as [Hc3z| Hzc3]. {
  apply (rngl_nlt_ge Hor) in Hzs23.
  apply Hzs23; clear Hzs23; cbn.
  rewrite (rngl_mul_opp_r Hop).
  apply (rngl_add_nonpos_neg Hop Hor). {
    apply (rngl_opp_nonpos_nonneg Hop Hor).
    apply (rngl_lt_le_incl Hor) in Hc2z.
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
  }
  now apply (rngl_mul_pos_neg Hop Hor Hid).
}
apply (rngl_nlt_ge Hor) in Hzc3.
move Hzc3 before Hc2z.
assert (H : (0 < rngl_cos θ1)%L). {
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  intros H; symmetry in H.
  apply eq_rngl_cos_0 in H.
  destruct H; subst θ1. {
    apply (rngl_nle_gt Hor) in H23.
    apply H23; clear H23; cbn.
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_sub_opp_r Hop).
    apply (rngl_add_nonneg_nonneg Hor).
    apply (rngl_lt_le_incl Hor) in Hc2z.
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
    apply (rngl_lt_le_incl Hor) in Hzs2.
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
  }
  apply (rngl_nle_gt Hor) in Hzs1.
  apply Hzs1; clear Hzs1.
  cbn.
  apply (rngl_opp_neg_pos Hop Hor).
  apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
}
move H before Hc1z; clear Hc1z.
rename H into Hzc1.
rewrite (angle_opp_sub_distr Hic Hop) in Hsov.
progress unfold angle_add_overflow in Hsov.
rewrite (angle_add_sub_assoc Hop) in Hsov.
rewrite (angle_add_sub_swap Hic Hop) in Hsov.
rewrite (angle_sub_sub_swap Hic Hop) in Hsov.
rewrite (angle_sub_diag Hic Hon Hop Hed) in Hsov.
rewrite <- (angle_add_sub_swap Hic Hop) in Hsov.
rewrite (angle_add_0_l Hon Hos) in Hsov.
progress unfold angle_ltb in Hsov.
apply rngl_leb_le in Hzs12, Hzs1.
rewrite Hzs12 in Hsov.
rewrite (rngl_sin_sub_straight_l Hon Hop) in Hsov.
rewrite Hzs1 in Hsov.
apply rngl_leb_le in Hzs12, Hzs1.
rewrite (rngl_cos_sub_straight_l Hon Hop) in Hsov.
apply (rngl_ltb_ge Hor) in Hsov.
apply (rngl_le_opp_r Hop Hor) in Hsov.
apply (rngl_nlt_ge Hor) in Hsov.
apply Hsov; clear Hsov.
cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
apply (rngl_add_nonneg_pos Hor); [ | easy ].
apply (rngl_add_nonneg_nonneg Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_le_sub_le_add_l_lemma_3 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ2 θ3 = false
  → angle_add_overflow θ1 (- θ2)%A = false
  → (θ2 ≤ θ1)%A
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin θ3 < 0)%L
  → (0 < rngl_cos θ2)%L
  → (0 ≤ rngl_sin (θ1 - θ2))%L
  → (0 ≤ rngl_sin (θ2 + θ3))%L
  → (rngl_cos (θ2 + θ3) ≤ rngl_cos θ1)%L.
Proof.
intros Hic Hon Hop Hed.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros θ1 θ2 θ3 Haov Hsov H21 Hzs1 Hzs2 Hzs3 Hzc2 Hzs12 Hzs23.
destruct (rngl_le_dec Hor (rngl_cos θ3) 0) as [Hc3z| Hzc3]. {
  remember (θ3 - angle_straight)%A as θ.
  apply angle_add_move_r in Heqθ.
  subst θ3; rename θ into θ3.
  move θ3 before θ2.
  rewrite angle_add_assoc in Hzs23 |-*.
  rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs3, Hzs23.
  rewrite rngl_cos_add_straight_r in Hc3z |-*.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs3.
  apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc3z.
  apply (rngl_le_0_sub Hop Hor).
  rewrite (rngl_sub_opp_r Hop).
  apply (rngl_nlt_ge Hor).
  intros Hcc.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs23.
  apply (rngl_nlt_ge Hor) in Hzs23.
  apply Hzs23; clear Hzs23.
  cbn.
  apply (rngl_add_pos_nonneg Hor).
  now apply (rngl_mul_pos_pos Hop Hor Hii).
  now apply rngl_mul_nonneg_nonneg.
}
apply (rngl_nle_gt Hor) in Hzc3.
move Hzc2 before Hzs2; move Hzc3 before Hzc2.
progress unfold angle_add_overflow in Haov.
progress unfold angle_add_overflow in Hsov.
apply angle_ltb_ge in Haov, Hsov.
progress unfold angle_leb in Haov.
progress unfold angle_leb in Hsov.
rewrite angle_add_opp_r in Hsov.
apply rngl_leb_le in Hzs1, Hzs2, Hzs23, Hzs12.
rewrite Hzs2, Hzs23 in Haov.
rewrite Hzs1, Hzs12 in Hsov.
apply rngl_leb_le in Haov, Hsov.
apply rngl_leb_le in Hzs1, Hzs2, Hzs23, Hzs12.
remember (θ3 + angle_right)%A as θ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Heqθ.
subst θ3; rename θ into θ3.
move θ3 before θ2.
rewrite (angle_add_sub_assoc Hop) in Haov, Hzs23 |-*.
rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs3, Hzs23.
rewrite (rngl_cos_sub_right_r Hon Hop) in Haov, Hzc3 |-*.
apply (rngl_opp_neg_pos Hop Hor) in Hzs3.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs23.
move Hzc3 before Hzs2; move Hzs3 after Hzc2.
apply (rngl_nlt_ge Hor).
intros Hc123.
assert (H : (0 < rngl_sin θ2)%L). {
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  intros H; symmetry in H.
  apply (eq_rngl_sin_0 Hic Hon Hop Hed) in H.
  destruct H; subst θ2. {
    rewrite (angle_add_0_l Hon Hos) in Hzs23.
    now apply (rngl_nlt_ge Hor) in Hzs23.
  }
  apply (rngl_nle_gt Hor) in Hzc2.
  apply Hzc2; cbn.
  apply (rngl_opp_nonpos_nonneg Hop Hor).
  apply (rngl_0_le_1 Hon Hop Hor).
}
move H before Hzs2; clear Hzs2; rename H into Hzs2.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  move Hzc1 after Hzc2.
  apply (rngl_nlt_ge Hor) in Hsov.
  apply Hsov; clear Hsov.
  rewrite (rngl_cos_sub_comm Hic Hop).
  apply rngl_cos_lt_rngl_cos_sub; try easy.
  now apply (rngl_lt_le_incl Hor).
  progress unfold angle_leb in H21.
  generalize Hzs2; intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply rngl_leb_le in H.
  rewrite H in H21; clear H.
  apply rngl_leb_le in Hzs1.
  rewrite Hzs1 in H21.
  apply rngl_leb_le in Hzs1.
  apply rngl_leb_le in H21.
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  intros H.
  rewrite H in Hc123.
  now apply (rngl_nle_gt Hor) in Hc123.
}
apply (rngl_nle_gt Hor) in Hc1z.
remember (θ1 - angle_right)%A as θ.
apply angle_add_move_r in Heqθ.
subst θ1; rename θ into θ1.
move θ1 after θ2.
rewrite (angle_add_sub_swap Hic Hop) in Hsov, Hzs12.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1, Hzs12.
rewrite rngl_cos_add_right_r in Hsov, Hsov, Hc1z, Hc123.
apply (rngl_opp_le_compat Hop Hor) in Hsov.
apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
move Hc1z after Hzs2.
move Hzs1 after Hzc3.
assert (H : (0 < rngl_cos θ1)%L). {
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  intros H; symmetry in H.
  apply eq_rngl_cos_0 in H.
  destruct H; subst θ1. {
    rewrite (rngl_sin_sub_right_l Hon Hos) in Hsov.
    rewrite (rngl_cos_sub_right_l Hon Hop) in Hzs12.
    cbn in Hsov.
    apply (rngl_le_antisymm Hor) in Hsov. 2: {
      apply (rngl_cos_bound Hon Hop Hiv Hic Hed Hor).
    }
    apply (eq_rngl_cos_1 Hic Hon Hop Hed) in Hsov.
    subst θ2.
    rewrite (angle_add_0_l Hon Hos) in Hzs23.
    now apply (rngl_nlt_ge Hor) in Hzs23.
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  apply Hc1z; cbn.
  apply (rngl_opp_nonpos_nonneg Hop Hor).
  apply (rngl_0_le_1 Hon Hop Hor).
}
move H before Hzs1; clear Hzs1; rename H into Hzc1.
apply (rngl_nlt_ge Hor) in Hsov.
apply Hsov; clear Hsov.
apply (rngl_sin_sub_lt_sin_l Hic Hon Hop Hed); try easy.
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_le_sub_le_add_l_lemma_4 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ2 θ3 = false
  → angle_add_overflow θ1 (- θ2)%A = false
  → (θ2 ≤ θ1)%A
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin θ3 < 0)%L
  → (rngl_cos θ2 ≤ 0)%L
  → (0 ≤ rngl_sin (θ1 - θ2))%L
  → (0 ≤ rngl_sin (θ2 + θ3))%L
  → (rngl_cos (θ2 + θ3) ≤ rngl_cos θ1)%L.
Proof.
intros Hic Hon Hop Hed.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  do 2 rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
intros * Haov Hsov H21 Hzs1 Hzs2 Hzs3 Hc2z Hzs12 Hzs23.
remember (θ3 - angle_straight)%A as θ.
apply angle_add_move_r in Heqθ.
subst θ3; rename θ into θ3.
move θ3 before θ2.
rewrite angle_add_assoc in Hzs23 |-*.
rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs3, Hzs23.
rewrite rngl_cos_add_straight_r.
apply (rngl_opp_neg_pos Hop Hor) in Hzs3.
move Hzs3 after Hzs2.
remember (θ2 - angle_right)%A as θ.
apply angle_add_move_r in Heqθ.
subst θ2; rename θ into θ2.
move θ2 before θ1.
rewrite (angle_sub_add_distr Hic Hop) in Hzs12.
rewrite (angle_add_add_swap Hic Hop) in Hzs23 |-*.
rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs12.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs2, Hzs23.
rewrite rngl_cos_add_right_r in Hc2z |-*.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc2z.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs12, Hzs23.
rewrite (rngl_opp_involutive Hop).
rename Hzs2 into Hzc2; rename Hc2z into Hzs2.
destruct (rngl_le_dec Hor (rngl_cos θ2) 0) as [H| H]. {
  apply (rngl_le_antisymm Hor) in H; [ | easy ].
  symmetry in H.
  apply eq_rngl_cos_0 in H.
  destruct H; subst θ2. {
    progress unfold angle_leb in H21.
    rewrite (rngl_sin_add_right_l Hon Hos) in H21.
    rewrite (rngl_cos_add_right_l Hon Hop) in H21.
    cbn in H21.
    rewrite (rngl_leb_refl Hor) in H21.
    apply rngl_leb_le in Hzs1.
    rewrite Hzs1 in H21.
    apply rngl_leb_le in Hzs1.
    apply rngl_leb_le in H21.
    specialize (rngl_cos_bound Hon Hop Hiv Hic Hed Hor θ1) as H1.
    apply (rngl_le_antisymm Hor) in H21; [ | easy ].
    clear H1.
    symmetry in H21.
    apply (eq_rngl_cos_opp_1 Hic Hon Hop Hed) in H21.
    subst θ1.
    progress unfold angle_add_overflow in Haov.
    apply angle_ltb_ge in Haov.
    progress unfold angle_leb in Haov.
    rewrite (rngl_sin_add_right_l Hon Hos) in Haov.
    rewrite (rngl_leb_refl Hor) in Haov.
    rewrite angle_add_assoc in Haov.
    rewrite (rngl_sin_add_straight_r Hon Hop) in Haov.
    rewrite (angle_add_comm Hic) in Haov.
    rewrite angle_add_assoc in Haov.
    rewrite (rngl_sin_add_right_r Hon Hos) in Haov.
    rewrite rngl_cos_add_right_r in Haov.
    rewrite (rngl_opp_involutive Hop) in Haov.
    generalize Hzs3; intros H.
    apply (rngl_lt_le_incl Hor) in Hzs3.
    apply rngl_leb_le in Hzs3.
    rewrite Hzs3 in Haov.
    rewrite rngl_cos_add_straight_r in Haov.
    rewrite rngl_cos_add_right_r in Haov.
    rewrite (rngl_sin_add_right_r Hon Hos) in Haov.
    rewrite (rngl_opp_involutive Hop) in Haov.
    rewrite rngl_cos_add_right_r in Haov.
    cbn in Haov.
    apply rngl_leb_le in Haov.
    specialize (rngl_cos_bound Hon Hop Hiv Hic Hed Hor θ3) as H1.
    apply (rngl_le_antisymm Hor) in Haov; [ | easy ].
    clear H1.
    symmetry in Haov.
    apply (eq_rngl_cos_opp_1 Hic Hon Hop Hed) in Haov.
    subst θ3.
    rewrite (rngl_sin_add_straight_r Hon Hop).
    cbn.
    apply (rngl_le_refl Hor).
  }
  apply (rngl_nlt_ge Hor) in Hzs2.
  exfalso; apply Hzs2; clear Hzs2; cbn.
  apply (rngl_opp_neg_pos Hop Hor).
  apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
}
apply (rngl_nle_gt Hor) in H.
move H before Hzc2; clear Hzc2; rename H into Hzc2.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  move Hzc1 after Hzc2.
  apply (rngl_nlt_ge Hor) in Hzs12.
  exfalso; apply Hzs12; clear Hzs12; cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_sub_opp_r Hop).
  apply (rngl_add_pos_nonneg Hor).
  now apply (rngl_mul_pos_pos Hop Hor Hii).
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
}
apply (rngl_nlt_ge Hor) in Hc1z.
remember (θ1 - angle_right)%A as θ.
apply angle_add_move_r in Heqθ.
subst θ1; rename θ into θ1.
move θ1 after θ2.
rewrite (angle_add_sub_swap Hic Hop) in Hzs12.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1.
rewrite rngl_cos_add_right_r in Hzs12, Hc1z |-*.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzs12, Hc1z.
move Hc1z after Hzs1; move Hzs1 before Hzc2.
destruct (rngl_le_dec Hor (rngl_cos θ1) 0) as [H| H]. {
  apply (rngl_le_antisymm Hor) in H; [ | easy ].
  symmetry in H.
  apply eq_rngl_cos_0 in H.
  destruct H; subst θ1. {
    clear Hc1z Hzs1.
    progress unfold angle_add_overflow in Hsov.
    apply angle_ltb_ge in Hsov.
    progress unfold angle_leb in Hsov.
    rewrite (rngl_sin_add_right_l Hon Hos) in Hsov.
    rewrite (rngl_leb_refl Hor) in Hsov.
    rewrite (angle_opp_add_distr Hic Hop) in Hsov.
    rewrite (angle_add_sub_assoc Hop) in Hsov.
    rewrite angle_add_opp_r in Hsov.
    rewrite (angle_add_sub Hic Hon Hop Hed) in Hsov.
    rewrite (rngl_sin_sub_right_l Hon Hos) in Hsov.
    generalize Hzc2; intros H.
    apply (rngl_lt_le_incl Hor) in H.
    apply rngl_leb_le in H.
    rewrite H in Hsov; clear H.
    apply rngl_leb_le in Hsov.
    rewrite (rngl_cos_add_right_l Hon Hop) in Hsov.
    rewrite (rngl_cos_sub_right_l Hon Hop) in Hsov.
    cbn in Hsov.
    specialize (rngl_sin_bound Hon Hop Hiv Hic Hed Hor θ2) as H1.
    apply (rngl_le_antisymm Hor) in Hsov; [ | easy ].
    symmetry in Hsov.
    apply (eq_rngl_sin_opp_1 Hic Hon Hop Hed) in Hsov.
    subst θ2.
    cbn in Hzc2.
    now apply (rngl_lt_irrefl Hor) in Hzc2.
  }
  remember (θ2 + θ3)%A as x; cbn; subst x.
  rewrite (rngl_opp_involutive Hop).
  apply (rngl_sin_bound Hon Hop Hiv Hic Hed Hor).
}
apply (rngl_nle_gt Hor) in H.
move H before Hzs1; clear Hzs1.
rename Hc1z into Hzs1; rename H into Hzc1.
progress unfold angle_add_overflow in Hsov.
apply angle_ltb_ge in Hsov.
progress unfold angle_leb in Hsov.
rewrite (rngl_sin_add_right_r Hon Hos) in Hsov.
generalize Hzc1; intros H.
apply (rngl_lt_le_incl Hor) in H.
apply rngl_leb_le in H.
rewrite H in Hsov; clear H.
rewrite (angle_opp_add_distr Hic Hop) in Hsov.
rewrite (angle_add_sub_assoc Hop) in Hsov.
rewrite angle_add_opp_r in Hsov.
rewrite (angle_add_sub Hic Hon Hop Hed) in Hsov.
apply rngl_leb_le in Hzs12.
rewrite Hzs12 in Hsov.
apply rngl_leb_le in Hzs12.
rewrite rngl_cos_add_right_r in Hsov.
apply rngl_leb_le in Hsov.
apply (rngl_nlt_ge Hor) in Hsov.
exfalso; apply Hsov; clear Hsov; cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
apply (rngl_le_lt_trans Hor _ 0). {
  now apply (rngl_opp_nonpos_nonneg Hop Hor).
}
apply (rngl_add_pos_nonneg Hor). {
  now apply (rngl_mul_pos_pos Hop Hor Hii).
}
now apply (rngl_mul_nonneg_nonneg Hop Hor).
Qed.

Theorem angle_le_sub_le_add_l_lemma_5 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ2 θ3 = false
  → (θ2 ≤ θ1)%A
  → (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_sin θ3 < 0)%L
  → (0 < rngl_sin (θ2 - θ1))%L
  → (rngl_cos (θ2 - θ1) ≤ rngl_cos θ3)%L
  → (0 ≤ rngl_sin (θ2 + θ3))%L
  → (rngl_cos (θ2 + θ3) ≤ rngl_cos θ1)%L.
Proof.
intros Hic Hon Hop Hed.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Haov H21 Hzs1 Hzs2 Hzs3 Hzs12 Hc123 Hzs23.
progress unfold angle_leb in H21.
apply rngl_leb_le in Hzs1, Hzs2.
rewrite Hzs2, Hzs1 in H21.
apply rngl_leb_le in Hzs1, Hzs2.
apply rngl_leb_le in H21.
remember (θ3 - angle_straight)%A as θ.
apply angle_add_move_r in Heqθ.
subst θ3; rename θ into θ3.
move θ3 before θ2.
rewrite angle_add_assoc in Hzs23 |-*.
rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs3, Hzs23.
rewrite rngl_cos_add_straight_r in Hc123 |-*.
apply (rngl_opp_neg_pos Hop Hor) in Hzs3.
rewrite (rngl_cos_sub_comm Hic Hop) in Hc123.
move Hzs3 after Hzs2.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  generalize Hzs12; intros H.
  apply (rngl_lt_le_incl Hor) in H.
  apply (rngl_sin_sub_nonneg_sin_le_sin Hic Hon Hop Hed _ _ Hzs2) in H. 2: {
    eapply (rngl_le_trans Hor); [ apply Hzc1 | apply H21 ].
  }
  cbn in Hzs12.
  rewrite (rngl_mul_opp_r Hop) in Hzs12.
  rewrite (rngl_add_opp_l Hop) in Hzs12.
  apply -> (rngl_lt_0_sub Hop Hor) in Hzs12.
  exfalso.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff in H; try easy. 2: {
    eapply (rngl_le_trans Hor); [ apply Hzc1 | apply H21 ].
  }
  apply (rngl_le_antisymm Hor) in H; [ | easy ].
  apply (rngl_cos_eq Hic Hon Hop Hed) in H.
  rewrite (rngl_mul_comm Hic).
  destruct H; subst θ1. {
    apply (rngl_le_refl Hor).
  }
  cbn in Hzs1.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs1.
  apply (rngl_le_antisymm Hor) in Hzs1; [ | easy ].
  rewrite rngl_cos_opp.
  rewrite <- Hzs1; cbn.
  symmetry in Hzs1.
  apply (eq_rngl_sin_0 Hic Hon Hop Hed) in Hzs1.
  destruct Hzs1; subst θ2; cbn; rewrite (rngl_opp_0 Hop);
    apply (rngl_le_refl Hor).
}
apply (rngl_nle_gt Hor) in Hc1z.
remember (θ1 - angle_right)%A as θ.
apply angle_add_move_r in Heqθ.
subst θ1; rename θ into θ1.
move θ1 after θ2.
rewrite (rngl_cos_sub_comm Hic Hop) in Hc123.
rewrite (angle_sub_add_distr Hic Hop) in Hc123, Hzs12.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1.
rewrite rngl_cos_add_right_r in H21, Hc1z |-*.
rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs12.
rewrite (rngl_cos_sub_right_r Hon Hop) in Hc123.
apply (rngl_opp_pos_neg Hop Hor) in Hzs12.
apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
apply (rngl_le_opp_r Hop Hor) in Hc123.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs23.
apply -> (rngl_opp_le_compat Hop Hor).
apply (rngl_le_opp_l Hop Hor) in H21.
move Hc1z after Hzs2; move Hzs1 after Hzs3.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  apply (rngl_nle_gt Hor) in Hzs12.
  exfalso; apply Hzs12; clear Hzs12; cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_sub_opp_r Hop).
  apply (rngl_add_nonneg_nonneg Hor).
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
  apply (rngl_lt_le_incl Hor) in Hc1z.
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
}
apply (rngl_nle_gt Hor) in Hc2z.
remember (θ2 - angle_right)%A as θ.
apply angle_add_move_r in Heqθ.
subst θ2; rename θ into θ2.
move θ2 before θ1.
rewrite (angle_add_sub_swap Hic Hop) in Hzs12, Hc123.
rewrite (angle_add_add_swap Hic Hop) in Hzs23 |-*.
rewrite (rngl_sin_add_right_r Hon Hos) in Hc123, Hzs2, Hzs23.
rewrite rngl_cos_add_right_r in H21, Hzs12, Hc2z |-*.
rewrite (rngl_add_opp_r Hop) in H21.
apply (rngl_opp_neg_pos Hop Hor) in Hzs12, Hc2z.
apply -> (rngl_le_0_sub Hop Hor) in H21.
move Hc2z before Hc1z.
move Hzs2 after Hzs1.
apply (rngl_le_opp_r Hop Hor).
destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
  exfalso.
  apply (rngl_nlt_ge Hor) in Hc123.
  apply Hc123; clear Hc123; cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_sub_opp_r Hop).
  apply (rngl_add_pos_nonneg Hor); [ | easy ].
  apply (rngl_add_nonneg_pos Hor).
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
  now apply (rngl_mul_pos_pos Hop Hor).
}
apply (rngl_nle_gt Hor) in Hc3z.
remember (θ3 - angle_right)%A as θ.
apply angle_add_move_r in Heqθ.
subst θ3; rename θ into θ3.
move θ3 before θ2.
rewrite angle_add_assoc in Hzs23 |-*.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs3 |-*.
rewrite rngl_cos_add_right_r in Hc123, Hc3z, Hzs23.
rewrite (rngl_add_opp_r Hop) in Hc123.
apply -> (rngl_le_sub_0 Hop Hor) in Hc123.
apply (rngl_opp_neg_pos Hop Hor) in Hc3z.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzs23.
move Hc3z before Hc2z; move Hzs3 after Hzs2.
progress unfold angle_add_overflow in Haov.
apply angle_ltb_ge in Haov.
progress unfold angle_leb in Haov.
rewrite (rngl_sin_add_right_r Hon Hos) in Haov.
apply rngl_leb_le in Hzs2.
rewrite Hzs2 in Haov.
apply rngl_leb_le in Hzs2.
do 2 rewrite angle_add_assoc in Haov.
rewrite (rngl_sin_add_straight_r Hon Hop) in Haov.
rewrite (rngl_sin_add_right_r Hon Hos) in Haov.
rewrite (angle_add_add_swap Hic Hop) in Haov.
rewrite rngl_cos_add_right_r in Haov.
rewrite (rngl_opp_involutive Hop) in Haov.
apply rngl_leb_le in Hzs23.
rewrite Hzs23 in Haov.
apply rngl_leb_le in Hzs23.
rewrite rngl_cos_add_straight_r in Haov.
do 2 rewrite rngl_cos_add_right_r in Haov.
rewrite (rngl_sin_add_right_r Hon Hos) in Haov.
rewrite (rngl_opp_involutive Hop) in Haov.
apply rngl_leb_le in Haov.
apply (rngl_le_opp_r Hop Hor) in Haov.
rewrite rngl_add_comm in Haov.
apply (rngl_nlt_ge Hor) in H21.
exfalso.
apply H21; clear H21.
apply (rngl_lt_iff Hor).
split.
apply rngl_sin_sub_nonneg_sin_le_sin; try easy.
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
intros H.
apply (rngl_sin_eq Hic Hon Hop Hed) in H.
destruct H; subst θ1. {
  rewrite (angle_sub_diag Hic Hon Hop Hed) in Hzs12.
  now apply (rngl_lt_irrefl Hor) in Hzs12.
}
rewrite (angle_sub_sub_distr Hic Hop) in Hzs12, Hc123.
rewrite (angle_add_comm Hic) in Hzs12, Hc123.
rewrite (angle_add_sub_assoc Hop) in Hzs12, Hc123.
rewrite (rngl_sin_sub_straight_r Hon Hop) in Hzs12.
rewrite (rngl_sin_sub_straight_l Hon Hop) in Hc1z.
rewrite (rngl_cos_sub_straight_l Hon Hop) in Hzs1.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs1.
apply (rngl_le_antisymm Hor) in Hzs1; [ | easy ].
symmetry in Hzs1.
apply eq_rngl_cos_0 in Hzs1.
destruct Hzs1; subst θ2. {
  rewrite (rngl_sin_add_right_l Hon Hos) in Hzs12.
  cbn in Hzs12.
  rewrite (rngl_opp_0 Hop) in Hzs12.
  now apply (rngl_lt_irrefl Hor) in Hzs12.
}
cbn in Hc1z.
apply (rngl_nle_gt Hor) in Hc1z.
apply Hc1z.
apply (rngl_opp_nonpos_nonneg Hop Hor).
apply (rngl_0_le_1 Hon Hop Hor).
Qed.

Theorem angle_le_sub_le_add_l_lemma_6 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ2 θ3 = false
  → angle_add_overflow θ1 (- θ2)%A = false
  → (rngl_sin θ1 < 0)%L
  → (rngl_sin θ3 < 0)%L
  → (0 ≤ rngl_cos θ3)%L
  → (0 < rngl_sin (θ2 - θ1))%L
  → (0 ≤ rngl_sin (θ2 + θ3))%L
  → (rngl_cos (θ2 - θ1) ≤ rngl_cos θ3)%L
  → False.
Proof.
intros Hic Hon Hop Hed.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Haov Hsov Hzs1 Hzs3 Hzc3 Hzs12 Hzs23 Hc123.
  rewrite (H1 (rngl_sin θ1)) in Hzs1.
  now apply (rngl_lt_irrefl Hor) in Hzs1.
}
intros * Haov Hsov Hzs1 Hzs3 Hzc3 Hzs12 Hzs23 Hc123.
remember (θ3 + angle_right)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ3; rename θ into θ3.
move θ3 before θ2.
rewrite (angle_add_sub_assoc Hop) in Hzs23.
rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs3, Hzs23.
rewrite (rngl_cos_sub_right_r Hon Hop) in Hzc3, Hc123.
apply (rngl_opp_neg_pos Hop Hor) in Hzs3.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs23.
move Hzc3 before Hzs1.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  remember (θ1 + angle_right)%A as θ eqn:Hθ.
  apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
  subst θ1; rename θ into θ1.
  move θ1 after θ2.
  rewrite (angle_sub_sub_distr Hic Hop) in Hzs12, Hc123.
  rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs1.
  rewrite (rngl_cos_sub_right_r Hon Hop) in Hzc1.
  rewrite (rngl_sin_add_right_r Hon Hos) in Hzs12.
  rewrite rngl_cos_add_right_r in Hc123.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs1.
  apply (rngl_le_opp_l Hop Hor) in Hc123.
  move Hzs1 before Hzs3; move Hzc1 after Hzc3.
  destruct (rngl_lt_dec Hor (rngl_sin θ2) 0) as [Hs2z| Hzs2]. {
    progress unfold angle_add_overflow in Haov.
    apply angle_ltb_ge in Haov.
    apply angle_nlt_ge in Haov.
    apply Haov; clear Haov.
    rewrite (angle_add_sub_assoc Hop).
    progress unfold angle_ltb.
    rewrite (rngl_sin_sub_right_r Hon Hop).
    generalize Hzs23; intros H.
    apply (rngl_opp_le_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply rngl_leb_le in H.
    rewrite H; clear H.
    apply (rngl_leb_gt Hor) in Hs2z.
    now rewrite Hs2z.
  }
  apply (rngl_nlt_ge Hor) in Hzs2.
  move Hzs2 before Hzc1.
  destruct (rngl_lt_dec Hor (rngl_cos θ2) 0) as [Hc2z| Hzc2]. {
    remember (θ2 - angle_right)%A as θ eqn:Hθ.
    apply angle_add_move_r in Hθ.
    subst θ2; rename θ into θ2.
    move θ2 before θ1.
    rewrite (angle_add_add_swap Hic Hop) in Hzs23.
    rewrite (angle_add_sub_swap Hic Hop) in Hc123, Hzs12.
    rewrite (rngl_sin_add_right_r Hon Hos) in Hzs2, Hc123.
    rewrite rngl_cos_add_right_r in Hc2z, Hzs23, Hzs12.
    rewrite <- (rngl_sin_sub_anticomm Hic Hop) in Hzs12.
    apply (rngl_opp_neg_pos Hop Hor) in Hc2z.
    apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzs23.
    move Hc2z before Hzc1; move Hzs2 after Hzs1.
    progress unfold angle_add_overflow in Hsov.
    apply angle_ltb_ge in Hsov.
    apply angle_nlt_ge in Hsov.
    apply Hsov; clear Hsov.
    rewrite angle_add_opp_r.
    rewrite (angle_sub_add_distr Hic Hop).
    rewrite (angle_sub_sub_swap Hic Hop θ1).
    rewrite <- (angle_sub_add_distr Hic Hop).
    rewrite (angle_right_add_right Hon Hop).
    progress unfold angle_ltb.
    rewrite (rngl_sin_sub_straight_r Hon Hop).
    generalize Hzs12; intros H.
    apply (rngl_opp_lt_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply (rngl_nle_gt Hor) in H.
    apply rngl_leb_nle in H.
    rewrite H; clear H.
    rewrite (rngl_sin_sub_right_r Hon Hop).
    generalize Hzs1; intros H.
    apply (rngl_opp_lt_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply (rngl_nle_gt Hor) in H.
    apply rngl_leb_nle in H.
    rewrite H; clear H.
    rewrite (rngl_cos_sub_straight_r Hon Hop).
    rewrite (rngl_cos_sub_right_r Hon Hop).
    apply rngl_ltb_lt.
    apply (rngl_lt_opp_l Hop Hor).
    apply (rngl_lt_iff Hor).
    split. {
      apply (rngl_add_nonneg_nonneg Hor); [ cbn | easy ].
      rewrite (rngl_mul_opp_r Hop).
      rewrite (rngl_sub_opp_r Hop).
      apply (rngl_add_nonneg_nonneg Hor).
      apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
      now apply (rngl_lt_le_incl Hor).
      apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
      now apply (rngl_lt_le_incl Hor).
    }
    intros H; symmetry in H.
    rewrite (rngl_cos_sub_comm Hic Hop) in Hc123.
    rewrite rngl_add_comm in H.
    apply (rngl_add_move_0_r Hop) in H.
    generalize Hzc1; intros H1.
    rewrite H in H1.
    apply (rngl_opp_nonneg_nonpos Hop Hor) in H1.
    apply (rngl_cos_nonpos Hon Hop) in H1.
    destruct H1 as (H1, H2).
    apply angle_nlt_ge in H1.
    apply H1; clear H1.
    progress unfold angle_ltb.
    generalize Hzs12; intros H3.
    apply (rngl_lt_le_incl Hor) in H3.
    apply rngl_leb_le in H3.
    rewrite H3; clear H3.
    cbn - [ rngl_cos ].
    specialize (rngl_0_le_1 Hon Hop Hor) as H4.
    apply rngl_leb_le in H4.
    rewrite H4; clear H4.
    apply rngl_ltb_lt.
    replace (rngl_cos angle_right)%L with 0%L by easy.
    apply (rngl_lt_iff Hor).
    split. {
      apply (rngl_cos_nonneg Hon Hop).
      left.
      progress unfold angle_leb.
      generalize Hzs12; intros H3.
      apply (rngl_lt_le_incl Hor) in H3.
      apply rngl_leb_le in H3.
      rewrite H3; clear H3.
      cbn.
      specialize (rngl_0_le_1 Hon Hop Hor) as H4.
      apply rngl_leb_le in H4.
      rewrite H4; clear H4.
      apply rngl_leb_le.
      rewrite (rngl_mul_opp_r Hop).
      rewrite (rngl_sub_opp_r Hop).
      apply (rngl_add_nonneg_nonneg Hor).
      apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
      now apply (rngl_lt_le_incl Hor).
      apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
      now apply (rngl_lt_le_incl Hor).
    }
    intros H3.
    symmetry in H3.
    apply eq_rngl_cos_0 in H3.
    destruct H3 as [H3| H3]. {
      rewrite H3 in H.
      cbn in H.
      rewrite (rngl_opp_0 Hop) in H.
      apply (eq_rngl_sin_0 Hic Hon Hop Hed) in H.
      destruct H; subst θ1. {
        rewrite (angle_sub_0_l Hon Hos) in H3.
        apply (f_equal angle_opp) in H3.
        rewrite (angle_opp_involutive Hop) in H3.
        subst θ2.
        cbn in Hc2z.
        apply (rngl_nle_gt Hor) in Hc2z.
        apply Hc2z.
        apply (rngl_opp_nonpos_nonneg Hop Hor).
        apply (rngl_0_le_1 Hon Hop Hor).
      }
      cbn in Hzs1.
      apply (rngl_nle_gt Hor) in Hzs1.
      apply Hzs1.
      apply (rngl_opp_nonpos_nonneg Hop Hor).
      apply (rngl_0_le_1 Hon Hop Hor).
    }
    rewrite H3 in Hzs12; cbn in Hzs12.
    apply (rngl_nle_gt Hor) in Hzs12.
    apply Hzs12.
    apply (rngl_opp_nonpos_nonneg Hop Hor).
    apply (rngl_0_le_1 Hon Hop Hor).
  }
  apply (rngl_nlt_ge Hor) in Hzc2.
  move Hzc2 before Hzs1.
  progress unfold angle_add_overflow in Hsov.
  apply angle_ltb_ge in Hsov.
  apply angle_nlt_ge in Hsov.
  apply Hsov; clear Hsov.
  rewrite angle_add_opp_r.
  rewrite (angle_sub_sub_swap Hic Hop θ1).
  progress unfold angle_ltb.
  rewrite (rngl_sin_sub_right_r Hon Hop).
  generalize Hzs12; intros H.
  rewrite (rngl_cos_sub_comm Hic Hop) in H.
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_nle_gt Hor) in H.
  apply rngl_leb_nle in H.
  rewrite H; clear H.
  rewrite (rngl_sin_sub_right_r Hon Hop).
  generalize Hzs1; intros H.
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_nle_gt Hor) in H.
  apply rngl_leb_nle in H.
  rewrite H; clear H.
  apply rngl_ltb_lt.
  rewrite (rngl_cos_sub_right_r Hon Hop).
  rewrite (rngl_cos_sub_right_r Hon Hop).
  rewrite (rngl_cos_sub_comm Hic Hop) in Hzs12.
  apply rngl_sin_sub_lt_sin_l; try easy.
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  intros H.
  symmetry in H.
  apply (eq_rngl_sin_0 Hic Hon Hop Hed) in H.
  destruct H; subst θ2. {
    rewrite (angle_add_0_l Hon Hos) in Hzs23.
    now apply (rngl_nlt_ge Hor) in Hzs23.
  }
  rewrite (rngl_cos_add_straight_l Hon Hop) in Hzs23.
  apply (rngl_nlt_ge Hor) in Hzc2.
  apply Hzc2; cbn.
  apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
}
apply (rngl_nle_gt Hor) in Hc1z.
remember (θ1 - angle_straight)%A as θ.
apply angle_add_move_r in Heqθ.
subst θ1; rename θ into θ1.
move θ1 after θ2.
rewrite (angle_sub_add_distr Hic Hop) in Hzs12, Hc123.
rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs1.
rewrite rngl_cos_add_straight_r in Hc1z.
rewrite (rngl_sin_sub_straight_r Hon Hop) in Hzs12.
rewrite (rngl_cos_sub_straight_r Hon Hop) in Hc123.
apply (rngl_opp_neg_pos Hop Hor) in Hzs1, Hc1z.
rewrite <- (rngl_sin_sub_anticomm Hic Hop) in Hzs12.
rewrite (rngl_cos_sub_comm Hic Hop) in Hc123.
apply (rngl_le_opp_l Hop Hor) in Hc123.
move Hzs1 before Hzc3; move Hc1z before Hzc3.
destruct (rngl_lt_dec Hor 0 (rngl_sin θ2)) as [Hzs2| Hs2z]. {
  destruct (rngl_lt_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    move Hzs2 before Hzs1; move Hzc2 before Hc1z.
    progress unfold angle_add_overflow in Hsov.
    apply angle_ltb_ge in Hsov.
    apply angle_nlt_ge in Hsov.
    apply Hsov; clear Hsov.
    rewrite angle_add_opp_r.
    rewrite (angle_add_sub_swap Hic Hop θ1).
    progress unfold angle_ltb.
    rewrite (rngl_sin_add_straight_r Hon Hop).
    generalize Hzs12; intros H.
    apply (rngl_opp_lt_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply (rngl_nle_gt Hor) in H.
    apply rngl_leb_nle in H.
    rewrite H; clear H.
    rewrite (rngl_sin_add_straight_r Hon Hop).
    generalize Hzs1; intros H.
    apply (rngl_opp_lt_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply (rngl_nle_gt Hor) in H.
    apply rngl_leb_nle in H.
    rewrite H; clear H.
    do 2 rewrite rngl_cos_add_straight_r.
    apply rngl_ltb_lt.
    apply -> (rngl_opp_lt_compat Hop Hor).
    rewrite (rngl_cos_sub_comm Hic Hop).
    apply rngl_cos_lt_rngl_cos_sub; try easy.
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
    apply (rngl_lt_iff Hor).
    split. {
      apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
      now apply (rngl_lt_le_incl Hor).
      now apply (rngl_lt_le_incl Hor).
      now apply (rngl_lt_le_incl Hor).
      now apply (rngl_lt_le_incl Hor).
      apply rngl_sin_sub_nonneg_sin_le_sin; try easy.
      now apply (rngl_lt_le_incl Hor).
      now apply (rngl_lt_le_incl Hor).
      now apply (rngl_lt_le_incl Hor).
    }
    intros H.
    apply (rngl_cos_eq Hic Hon Hop Hed) in H.
    destruct H; subst θ1. {
      rewrite (angle_sub_diag Hic Hon Hop Hed) in Hzs12.
      now apply (rngl_lt_irrefl Hor) in Hzs12.
    }
    cbn in Hzs1.
    apply (rngl_opp_pos_neg Hop Hor) in Hzs1.
    apply (rngl_lt_le_incl Hor) in Hzs1.
    now apply (rngl_nlt_ge Hor) in Hzs1.
  }
  apply (rngl_nlt_ge Hor) in Hc2z.
  remember (θ2 - angle_right)%A as θ eqn:Hθ.
  apply angle_add_move_r in Hθ.
  subst θ2; rename θ into θ2.
  move θ2 before θ1.
  rewrite (angle_add_add_swap Hic Hop) in Hzs23.
  rewrite (angle_sub_add_distr Hic Hop) in Hc123, Hzs12.
  rewrite (rngl_sin_add_right_r Hon Hos) in Hzs2.
  rewrite rngl_cos_add_right_r in Hc2z, Hzs23.
  rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs12.
  rewrite (rngl_cos_sub_right_r Hon Hop) in Hc123.
  apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc2z, Hzs23.
  apply (rngl_opp_pos_neg Hop Hor) in Hzs12.
  move Hc2z before Hzs1; move Hzs2 before Hc1z.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12; cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_sub_opp_r Hop).
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nlt_ge Hor) in Hs2z.
destruct (rngl_lt_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  remember (θ2 + angle_right)%A as θ eqn:Hθ.
  apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
  subst θ2; rename θ into θ2.
  move θ2 before θ1.
  rewrite <- (angle_add_sub_swap Hic Hop) in Hzs23.
  rewrite (angle_sub_sub_distr Hic Hop) in Hc123, Hzs12.
  rewrite (rngl_sin_sub_right_r Hon Hop) in Hs2z.
  rewrite (rngl_cos_sub_right_r Hon Hop) in Hzc2, Hzs23.
  rewrite (rngl_sin_add_right_r Hon Hos) in Hzs12.
  rewrite rngl_cos_add_right_r in Hc123.
  apply (rngl_opp_nonpos_nonneg Hop Hor) in Hs2z.
  rewrite (rngl_add_opp_l Hop) in Hc123.
  apply -> (rngl_le_0_sub Hop Hor) in Hc123.
  move Hzc2 before Hzs1; move Hs2z before Hc1z.
  apply (rngl_nlt_ge Hor) in Hzs23.
  apply Hzs23; clear Hzs23; cbn.
  apply (rngl_add_nonneg_pos Hor).
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
  now apply (rngl_mul_pos_pos Hop Hor Hii).
}
apply (rngl_nlt_ge Hor) in Hc2z.
remember (θ2 - angle_straight)%A as θ.
apply angle_add_move_r in Heqθ.
subst θ2; rename θ into θ2.
move θ2 before θ1.
rewrite (angle_add_add_swap Hic Hop) in Hzs23.
rewrite (angle_sub_add_distr Hic Hop) in Hc123, Hzs12.
rewrite (rngl_sin_add_straight_r Hon Hop) in Hs2z.
rewrite rngl_cos_add_straight_r in Hc2z, Hzs23.
rewrite (rngl_sin_sub_straight_r Hon Hop) in Hzs12.
rewrite (rngl_cos_sub_straight_r Hon Hop) in Hc123.
rewrite (rngl_add_opp_l Hop) in Hc123.
apply -> (rngl_le_0_sub Hop Hor) in Hc123.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hc2z, Hs2z, Hzs23.
rewrite <- (rngl_sin_sub_anticomm Hic Hop) in Hzs12.
move Hs2z before Hzs1; move Hc2z before Hc1z.
progress unfold angle_add_overflow in Haov.
apply angle_ltb_ge in Haov.
apply angle_nlt_ge in Haov.
apply Haov; clear Haov.
rewrite (angle_add_sub_assoc Hop).
rewrite (angle_add_add_swap Hic Hop).
rewrite <- (angle_add_sub_assoc Hop).
rewrite (angle_straight_sub_right Hon Hop).
progress unfold angle_ltb.
rewrite (rngl_sin_add_right_r Hon Hos).
rewrite (rngl_sin_add_straight_r Hon Hop).
apply rngl_leb_le in Hzs23.
rewrite Hzs23.
apply rngl_leb_le in Hzs23.
rewrite rngl_cos_add_straight_r.
rewrite rngl_cos_add_right_r.
remember (0 ≤? - rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs2.
destruct zs2; [ | easy ].
apply rngl_ltb_lt.
apply -> (rngl_opp_lt_compat Hop Hor).
apply rngl_leb_le in Hzs2.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs2.
apply (rngl_le_antisymm Hor) in Hzs2; [ | easy ].
symmetry in Hzs2.
apply (eq_rngl_sin_0 Hic Hon Hop Hed) in Hzs2.
exfalso.
destruct Hzs2; subst θ2. {
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12.
  rewrite (angle_sub_0_l Hon Hos); cbn.
  apply (rngl_opp_nonpos_nonneg Hop Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nlt_ge Hor) in Hc2z.
apply Hc2z; clear Hc2z; cbn.
apply (rngl_opp_neg_pos Hop Hor).
apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
Qed.

Theorem angle_le_sub_le_add_l_lemma_7 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ2 θ3 = false
  → angle_add_overflow θ1 (- θ2)%A = false
  → (rngl_sin θ1 < 0)%L
  → (rngl_sin θ3 < 0)%L
  → (rngl_cos θ3 < 0)%L
  → (0 < rngl_sin (θ2 - θ1))%L
  → (0 ≤ rngl_sin (θ2 + θ3))%L
  → (rngl_cos (θ2 - θ1) ≤ rngl_cos θ3)%L
  → False.
Proof.
intros Hic Hon Hop Hed.
destruct_ac.
intros * Haov Hsov Hzs1 Hzs3 Hc3z Hzs12 Hzs23 Hc123.
remember (θ3 + angle_straight)%A as θ eqn:Hθ.
apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
subst θ3; rename θ into θ3.
move θ3 before θ2.
rewrite (angle_add_sub_assoc Hop) in Hzs23.
rewrite (rngl_sin_sub_straight_r Hon Hop) in Hzs3, Hzs23.
rewrite (rngl_cos_sub_straight_r Hon Hop) in Hc3z, Hc123.
apply (rngl_opp_neg_pos Hop Hor) in Hzs3.
apply (rngl_opp_nonneg_nonpos Hop Hor) in Hzs23.
apply (rngl_opp_neg_pos Hop Hor) in Hc3z.
apply (rngl_le_opp_r Hop Hor) in Hc123.
move Hc3z before Hzs3.
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  remember (θ1 + angle_right)%A as θ eqn:Hθ.
  apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
  subst θ1; rename θ into θ1.
  move θ1 after θ2.
  rewrite (angle_sub_sub_distr Hic Hop) in Hzs12, Hc123.
  rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs1.
  rewrite (rngl_cos_sub_right_r Hon Hop) in Hzc1.
  rewrite (rngl_sin_add_right_r Hon Hos) in Hzs12.
  rewrite rngl_cos_add_right_r in Hc123.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs1.
  rewrite (rngl_add_opp_l Hop) in Hc123.
  apply -> (rngl_le_sub_0 Hop Hor) in Hc123.
  rewrite (rngl_cos_sub_comm Hic Hop) in Hzs12.
  move Hzc1 after Hzs3; move Hzs1 after Hzs3.
  destruct (rngl_le_dec Hor 0 (rngl_sin θ2)) as [Hzs2| Hs2z]. {
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
      move Hzs2 before Hzc1; move Hzc2 before Hzs1.
      progress unfold angle_add_overflow in Hsov.
      apply angle_ltb_ge in Hsov.
      apply angle_nlt_ge in Hsov.
      apply Hsov; clear Hsov.
      rewrite angle_add_opp_r.
      rewrite (angle_sub_sub_swap Hic Hop).
      progress unfold angle_ltb.
      rewrite (rngl_sin_sub_right_r Hon Hop).
      rewrite (rngl_cos_sub_right_r Hon Hop).
      generalize Hzs12; intros H.
      apply (rngl_opp_lt_compat Hop Hor) in H.
      rewrite (rngl_opp_0 Hop) in H.
      apply (rngl_nle_gt Hor) in H.
      apply rngl_leb_nle in H.
      rewrite H; clear H.
      rewrite (rngl_sin_sub_right_r Hon Hop).
      generalize Hzs1; intros H.
      apply (rngl_opp_lt_compat Hop Hor) in H.
      rewrite (rngl_opp_0 Hop) in H.
      apply (rngl_nle_gt Hor) in H.
      apply rngl_leb_nle in H.
      rewrite H; clear H.
      rewrite (rngl_cos_sub_right_r Hon Hop).
      apply rngl_ltb_lt.
      apply (rngl_lt_le_trans Hor _ 0); [ | easy ].
      rewrite (rngl_sin_sub_anticomm Hic Hop).
      apply (rngl_opp_neg_pos Hop Hor).
      eapply (rngl_lt_le_trans Hor); [ apply Hc3z | apply Hc123 ].
    }
    apply (rngl_nle_gt Hor) in Hc2z.
    remember (θ2 - angle_right)%A as θ eqn:Hθ.
    apply angle_add_move_r in Hθ.
    subst θ2; rename θ into θ2.
    move θ2 before θ1.
    rewrite (angle_add_sub_swap Hic Hop) in Hc123.
    rewrite (angle_add_add_swap Hic Hop) in Hzs23.
    rewrite (angle_sub_add_distr Hic Hop) in Hzs12.
    rewrite (rngl_sin_add_right_r Hon Hos) in Hzs2, Hc123, Hzs23.
    rewrite rngl_cos_add_right_r in Hc2z.
    rewrite (rngl_cos_sub_right_r Hon Hop) in Hzs12.
    apply (rngl_opp_neg_pos Hop Hor) in Hc2z.
    move Hc2z before Hzc1; move Hzs2 before Hzs1.
    progress unfold angle_add_overflow in Hsov.
    apply angle_ltb_ge in Hsov.
    apply angle_nlt_ge in Hsov.
    apply Hsov; clear Hsov.
    rewrite angle_add_opp_r.
    rewrite (angle_sub_add_distr Hic Hop).
    rewrite (angle_sub_sub_swap Hic Hop).
    rewrite <- (angle_sub_add_distr Hic Hop θ1).
    rewrite (angle_right_add_right Hon Hop).
    rewrite (angle_sub_sub_swap Hic Hop).
    progress unfold angle_ltb.
    rewrite (rngl_sin_sub_straight_r Hon Hop).
    generalize Hzs12; intros H.
    apply (rngl_opp_lt_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply (rngl_nle_gt Hor) in H.
    apply rngl_leb_nle in H.
    rewrite H; clear H.
    rewrite (rngl_sin_sub_right_r Hon Hop).
    generalize Hzs1; intros H.
    apply (rngl_opp_lt_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply (rngl_nle_gt Hor) in H.
    apply rngl_leb_nle in H.
    rewrite H; clear H.
    rewrite (rngl_cos_sub_straight_r Hon Hop).
    rewrite (rngl_cos_sub_right_r Hon Hop).
    apply rngl_ltb_lt.
    apply (rngl_lt_le_trans Hor _ 0); [ | easy ].
    apply (rngl_opp_neg_pos Hop Hor).
    rewrite (rngl_cos_sub_comm Hic Hop).
    eapply (rngl_lt_le_trans Hor); [ apply Hc3z | apply Hc123 ].
  }
  apply (rngl_nle_gt Hor) in Hs2z.
  progress unfold angle_add_overflow in Haov.
  apply angle_ltb_ge in Haov.
  apply angle_nlt_ge in Haov.
  apply Haov; clear Haov.
  rewrite (angle_add_sub_assoc Hop).
  progress unfold angle_ltb.
  rewrite (rngl_sin_sub_straight_r Hon Hop).
  generalize Hzs23; intros H.
  apply (rngl_opp_le_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply rngl_leb_le in H.
  rewrite H; clear H.
  apply (rngl_leb_gt Hor) in Hs2z.
  now rewrite Hs2z.
}
apply (rngl_nle_gt Hor) in Hc1z.
remember (θ1 - angle_straight)%A as θ.
apply angle_add_move_r in Heqθ.
subst θ1; rename θ into θ1.
move θ1 after θ2.
rewrite (angle_sub_add_distr Hic Hop) in Hzs12, Hc123.
rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs1.
rewrite rngl_cos_add_straight_r in Hc1z.
rewrite (rngl_sin_sub_straight_r Hon Hop) in Hzs12.
rewrite (rngl_cos_sub_straight_r Hon Hop) in Hc123.
apply (rngl_opp_neg_pos Hop Hor) in Hzs1, Hc1z.
rewrite <- (rngl_sin_sub_anticomm Hic Hop) in Hzs12.
rewrite (rngl_cos_sub_comm Hic Hop) in Hc123.
rewrite (rngl_add_opp_l Hop) in Hc123.
apply -> (rngl_le_sub_0 Hop Hor) in Hc123.
move Hzs1 before Hzs3; move Hc1z after Hc3z.
destruct (rngl_le_dec Hor 0 (rngl_sin θ2)) as [Hzs2| Hs2z]. {
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    move Hzs2 before Hzs1; move Hzc2 before Hc1z.
    apply (rngl_nlt_ge Hor) in Hzs23.
    apply Hzs23; clear Hzs23.
    apply (rngl_lt_iff Hor).
    split. {
      cbn.
      apply (rngl_add_nonneg_nonneg Hor).
      apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
      now apply (rngl_lt_le_incl Hor).
      apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
      now apply (rngl_lt_le_incl Hor).
    }
    intros H; symmetry in H.
    apply (eq_rngl_sin_0 Hic Hon Hop Hed) in H.
    destruct H as [H| H]. {
      apply (angle_add_move_l Hic Hon Hop Hed) in H.
      progress unfold angle_sub in H.
      rewrite (angle_add_0_l Hon Hos) in H.
      subst θ3.
      cbn in Hzs3.
      apply (rngl_opp_pos_neg Hop Hor) in Hzs3.
      now apply (rngl_nle_gt Hor) in Hzs3.
    }
    apply (angle_add_move_l Hic Hon Hop Hed) in H.
    subst θ3.
    rewrite (rngl_cos_sub_straight_l Hon Hop) in Hc3z.
    apply (rngl_opp_pos_neg Hop Hor) in Hc3z.
    now apply (rngl_nle_gt Hor) in Hc3z.
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  remember (θ2 - angle_right)%A as θ eqn:Hθ.
  apply angle_add_move_r in Hθ.
  subst θ2; rename θ into θ2.
  move θ2 before θ1.
  rewrite (angle_add_add_swap Hic Hop) in Hzs23.
  rewrite (angle_sub_add_distr Hic Hop) in Hc123, Hzs12.
  rewrite (rngl_sin_add_right_r Hon Hos) in Hzs2, Hzs23.
  rewrite rngl_cos_add_right_r in Hc2z.
  rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs12.
  rewrite (rngl_cos_sub_right_r Hon Hop) in Hc123.
  apply (rngl_opp_neg_pos Hop Hor) in Hc2z.
  apply (rngl_opp_pos_neg Hop Hor) in Hzs12.
  move Hc2z before Hzs1; move Hzs2 before Hc1z.
  apply (rngl_nle_gt Hor) in Hzs12.
  apply Hzs12; clear Hzs12; cbn.
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_sub_opp_r Hop).
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hs2z.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  remember (θ2 + angle_right)%A as θ eqn:Hθ.
  apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
  subst θ2; rename θ into θ2.
  move θ2 before θ1.
  rewrite <- (angle_add_sub_swap Hic Hop) in Hzs23.
  rewrite (angle_sub_sub_distr Hic Hop) in Hc123, Hzs12.
  rewrite (rngl_sin_sub_right_r Hon Hop) in Hs2z, Hzs23.
  rewrite (rngl_cos_sub_right_r Hon Hop) in Hzc2.
  rewrite (rngl_sin_add_right_r Hon Hos) in Hzs12.
  rewrite rngl_cos_add_right_r in Hc123.
  apply (rngl_opp_neg_pos Hop Hor) in Hs2z.
  apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzs23.
  rewrite <- (rngl_sin_sub_anticomm Hic Hop) in Hc123.
  move Hzc2 before Hzs1; move Hs2z before Hc1z.
  progress unfold angle_add_overflow in Haov.
  apply angle_ltb_ge in Haov.
  apply angle_nlt_ge in Haov.
  apply Haov; clear Haov.
  rewrite (angle_add_sub_assoc Hop).
  rewrite <- (angle_add_sub_swap Hic Hop).
  progress unfold angle_ltb.
  rewrite (rngl_sin_sub_straight_r Hon Hop).
  rewrite (rngl_sin_sub_right_r Hon Hop).
  rewrite (rngl_opp_involutive Hop).
  apply rngl_leb_le in Hzs23.
  rewrite Hzs23.
  apply rngl_leb_le in Hzs23.
  rewrite (rngl_sin_sub_right_r Hon Hop).
  generalize Hs2z; intros H.
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_nle_gt Hor) in H.
  apply rngl_leb_nle in H.
  now rewrite H; clear H.
}
apply (rngl_nle_gt Hor) in Hc2z.
remember (θ2 - angle_straight)%A as θ.
apply angle_add_move_r in Heqθ.
subst θ2; rename θ into θ2.
move θ2 before θ1.
rewrite (angle_add_add_swap Hic Hop) in Hzs23.
rewrite (angle_sub_add_distr Hic Hop) in Hc123, Hzs12.
rewrite (rngl_sin_add_straight_r Hon Hop) in Hs2z, Hzs23.
rewrite rngl_cos_add_straight_r in Hc2z.
rewrite (rngl_sin_sub_straight_r Hon Hop) in Hzs12.
rewrite (rngl_cos_sub_straight_r Hon Hop) in Hc123.
rewrite <- (rngl_sin_sub_anticomm Hic Hop) in Hzs12.
apply (rngl_opp_neg_pos Hop Hor) in Hc2z, Hs2z.
apply (rngl_opp_nonpos_nonneg Hop Hor) in Hzs23.
apply (rngl_le_opp_r Hop Hor) in Hc123.
apply (rngl_nlt_ge Hor) in Hc123.
apply Hc123; clear Hc123; cbn.
apply (rngl_add_pos_nonneg Hor); [ easy | ].
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
apply (rngl_add_nonneg_nonneg Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_le_sub_le_add_l_lemma_8 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ2 θ3 = false
  → angle_add_overflow θ1 (- θ2)%A = false
  → (rngl_sin θ1 < 0)%L
  → (rngl_sin θ3 < 0)%L
  → (0 < rngl_sin (θ2 - θ1))%L
  → (rngl_cos (θ1 - θ2) ≤ rngl_cos θ3)%L
  → (rngl_sin (θ2 + θ3) < 0)%L
  → (rngl_cos θ1 ≤ rngl_cos (θ2 + θ3))%L.
Proof.
intros Hic Hon Hop Hed.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Haov Hsov Hzs1 Hzs3 Hzs12 Hc123 Hzs23.
remember (θ1 - angle_straight)%A as θ.
apply angle_add_move_r in Heqθ.
subst θ1; rename θ into θ1.
move θ1 after θ2.
rewrite (angle_sub_add_distr Hic Hop) in Hzs12.
rewrite (angle_add_sub_swap Hic Hop) in Hc123.
rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs1.
rewrite rngl_cos_add_straight_r in Hc123 |-*.
rewrite (rngl_sin_sub_straight_r Hon Hop) in Hzs12.
remember (θ3 - angle_straight)%A as θ.
apply angle_add_move_r in Heqθ.
subst θ3; rename θ into θ3.
rewrite angle_add_assoc in Hzs23 |-*.
rewrite (rngl_sin_add_straight_r Hon Hop) in Hzs3, Hzs23.
rewrite rngl_cos_add_straight_r in Hc123 |-*.
apply (rngl_opp_neg_pos Hop Hor) in Hzs1, Hzs3, Hzs23.
rewrite <- (rngl_sin_sub_anticomm Hic Hop) in Hzs12.
move Hzs1 before Hzs3.
apply (rngl_opp_le_compat Hop Hor) in Hc123.
apply -> (rngl_opp_le_compat Hop Hor).
move Hc123 at bottom.
destruct (rngl_le_dec Hor 0 (rngl_sin θ2)) as [Hzs2| Hs2z]. {
  destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
    apply angle_le_sub_le_add_l_lemma_1; try easy;
      try now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nle_gt Hor) in Hc2z.
  remember (θ2 - angle_right)%A as θ eqn:Hθ.
  apply angle_add_move_r in Hθ.
  subst θ2; rename θ into θ2.
  move θ2 before θ1.
  rewrite (angle_add_add_swap Hic Hop) in Hzs23 |-*.
  rewrite (angle_sub_add_distr Hic Hop) in Hc123, Hzs12.
  rewrite (rngl_sin_add_right_r Hon Hos) in Hzs2, Hzs23.
  rewrite rngl_cos_add_right_r in Hc2z |-*.
  rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs12.
  rewrite (rngl_cos_sub_right_r Hon Hop) in Hc123.
  apply (rngl_opp_neg_pos Hop Hor) in Hc2z.
  apply (rngl_opp_pos_neg Hop Hor) in Hzs12.
  apply (rngl_le_opp_l Hop Hor).
  move Hc2z before Hzs1.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    exfalso.
    apply (rngl_nle_gt Hor) in Hzs12.
    apply Hzs12; clear Hzs12; cbn.
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_sub_opp_r Hop).
    apply (rngl_add_nonneg_nonneg Hor).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
    apply (rngl_mul_nonneg_nonneg Hop Hor).
    now apply (rngl_lt_le_incl Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  remember (θ1 - angle_right)%A as θ.
  apply angle_add_move_r in Heqθ.
  subst θ1; rename θ into θ1.
  move θ1 after θ2.
  rewrite (angle_add_sub_swap Hic Hop) in Hc123, Hzs12.
  rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1, Hc123.
  rewrite rngl_cos_add_right_r in Hc1z, Hzs12 |-*.
  apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs12.
  rewrite (rngl_add_opp_r Hop).
  apply (rngl_le_0_sub Hop Hor).
  move Hc1z after Hc2z; move Hzs1 before Hzs2.
  progress unfold angle_add_overflow in Hsov.
  apply angle_ltb_ge in Hsov.
  apply angle_nlt_ge in Hsov.
  exfalso.
  apply Hsov; clear Hsov.
  rewrite angle_add_opp_r.
  rewrite (angle_add_add_swap Hic Hop).
  rewrite (angle_sub_add_distr Hic Hop).
  rewrite (angle_add_sub_swap Hic Hop).
  rewrite (angle_add_sub Hic Hon Hop Hed).
  rewrite (angle_add_sub_swap Hic Hop).
  progress unfold angle_ltb.
  rewrite (rngl_sin_add_straight_r Hon Hop).
  generalize Hzs12; intros H.
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_nle_gt Hor) in H.
  apply rngl_leb_nle in H.
  rewrite H; clear H.
  rewrite (rngl_sin_add_right_r Hon Hos).
  rewrite rngl_cos_add_straight_r.
  generalize Hzs1; intros H.
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_nle_gt Hor) in H.
  apply rngl_leb_nle in H.
  rewrite H; clear H.
  rewrite rngl_cos_add_straight_r.
  rewrite rngl_cos_add_right_r.
  rewrite (rngl_sin_add_straight_r Hon Hop).
  rewrite (rngl_opp_involutive Hop).
  apply rngl_ltb_lt.
  apply (rngl_lt_opp_l Hop Hor).
  cbn.
  apply (rngl_add_nonneg_pos Hor); [ | easy ].
  rewrite (rngl_mul_opp_r Hop).
  rewrite (rngl_sub_opp_r Hop).
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
  apply (rngl_mul_nonneg_nonneg Hop Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hs2z.
destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
  remember (θ2 + angle_right)%A as θ eqn:Hθ.
  apply (angle_sub_move_r Hic Hon Hop Hed) in Hθ.
  subst θ2; rename θ into θ2.
  move θ2 before θ1.
  rewrite <- (angle_add_sub_swap Hic Hop) in Hzs23.
  rewrite (angle_sub_sub_distr Hic Hop) in Hc123, Hzs12.
  rewrite <- (angle_add_sub_swap Hic Hop).
  rewrite (rngl_sin_sub_right_r Hon Hop) in Hs2z, Hzs23.
  rewrite (rngl_cos_sub_right_r Hon Hop) in Hzc2 |-*.
  rewrite (rngl_sin_add_right_r Hon Hos) in Hzs12.
  rewrite rngl_cos_add_right_r in Hc123.
  apply (rngl_opp_neg_pos Hop Hor) in Hs2z.
  rewrite <- (rngl_sin_sub_anticomm Hic Hop) in Hc123.
  apply (rngl_opp_pos_neg Hop Hor) in Hzs23.
  move Hzc2 before Hzs1.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
    exfalso.
    progress unfold angle_add_overflow in Haov.
    apply angle_ltb_ge in Haov.
    apply angle_nlt_ge in Haov.
    apply Haov; clear Haov.
    rewrite angle_add_assoc.
    rewrite <- (angle_add_sub_swap Hic Hop).
    rewrite <- (angle_add_sub_swap Hic Hop).
    rewrite <- (angle_add_sub_assoc Hop).
    rewrite (angle_straight_sub_right Hon Hop).
    progress unfold angle_ltb.
    rewrite (rngl_sin_add_right_r Hon Hos).
    generalize Hzs23; intros H.
    apply (rngl_nle_gt Hor) in H.
    apply rngl_leb_nle in H.
    rewrite H; clear H.
    rewrite (rngl_sin_sub_right_r Hon Hop).
    generalize Hs2z; intros H.
    apply (rngl_opp_lt_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply (rngl_nle_gt Hor) in H.
    apply rngl_leb_nle in H.
    rewrite H; clear H.
    rewrite rngl_cos_add_right_r.
    rewrite (rngl_cos_sub_right_r Hon Hop).
    apply rngl_ltb_lt.
    apply (rngl_lt_opp_l Hop Hor).
    apply (rngl_add_pos_nonneg Hor); [ | easy ].
    cbn.
    apply (rngl_add_pos_nonneg Hor).
    now apply (rngl_mul_pos_pos Hop Hor Hii).
    now apply (rngl_mul_nonneg_nonneg Hop Hor).
  }
  apply (rngl_nle_gt Hor) in Hc3z.
  remember (θ3 - angle_right)%A as θ.
  apply angle_add_move_r in Heqθ.
  subst θ3; rename θ into θ3.
  move θ3 before θ2.
  rewrite angle_add_assoc in Hzs23 |-*.
  rewrite (rngl_sin_add_right_r Hon Hos) in Hzs3 |-*.
  rewrite rngl_cos_add_right_r in Hc123, Hc3z, Hzs23.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs23, Hc3z.
  apply (rngl_le_opp_l Hop Hor) in Hc123.
  move Hc3z before Hzc2; move Hzs3 after Hs2z.
  destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
    apply (rngl_nlt_ge Hor).
    intros H123.
    progress unfold angle_add_overflow in Haov.
    apply angle_ltb_ge in Haov.
    apply angle_nlt_ge in Haov.
    apply Haov; clear Haov.
    rewrite angle_add_assoc.
    rewrite <- (angle_add_sub_swap Hic Hop).
    rewrite angle_add_assoc.
    rewrite (angle_add_sub Hic Hon Hop Hed).
    progress unfold angle_ltb.
    rewrite (rngl_sin_add_straight_r Hon Hop).
    generalize Hzs23; intros H.
    apply (rngl_opp_lt_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply (rngl_nle_gt Hor) in H.
    apply rngl_leb_nle in H.
    rewrite H; clear H.
    rewrite (rngl_sin_sub_right_r Hon Hop).
    generalize Hs2z; intros H.
    apply (rngl_opp_lt_compat Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    apply (rngl_nle_gt Hor) in H.
    apply rngl_leb_nle in H.
    rewrite H; clear H.
    rewrite rngl_cos_add_straight_r.
    rewrite (rngl_cos_sub_right_r Hon Hop).
    apply rngl_ltb_lt.
    apply (rngl_lt_opp_l Hop Hor).
    apply (rngl_add_pos_nonneg Hor); [ | easy ].
    now apply (rngl_le_lt_trans Hor _ (rngl_cos θ1)).
  }
  apply (rngl_nle_gt Hor) in Hc1z.
  remember (θ1 - angle_right)%A as θ.
  apply angle_add_move_r in Heqθ.
  subst θ1; rename θ into θ1.
  move θ1 after θ2.
  rewrite (angle_add_sub_swap Hic Hop) in Hzs12.
  rewrite (angle_sub_add_distr Hic Hop) in Hc123.
  rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1.
  rewrite rngl_cos_add_right_r in Hc1z, Hzs12 |-*.
  rewrite (rngl_sin_sub_right_r Hon Hop) in Hc123.
  apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
  rewrite <- (rngl_sin_sub_anticomm Hic Hop) in Hzs12.
  rewrite (rngl_add_opp_r Hop) in Hc123.
  apply -> (rngl_le_0_sub Hop Hor) in Hc123.
  apply (rngl_le_opp_r Hop Hor).
  move Hc1z after Hzc2.
  move Hzs1 after Hc3z.
  apply (rngl_nlt_ge Hor).
  intros H231.
  progress unfold angle_add_overflow in Haov.
  apply angle_ltb_ge in Haov.
  apply angle_nlt_ge in Haov.
  apply Haov; clear Haov.
  do 2 rewrite angle_add_assoc.
  do 2 rewrite <- (angle_add_sub_swap Hic Hop).
  rewrite (angle_add_sub Hic Hon Hop Hed).
  progress unfold angle_ltb.
  rewrite (rngl_sin_add_straight_r Hon Hop).
  generalize Hzs23; intros H.
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_nle_gt Hor) in H.
  apply rngl_leb_nle in H.
  rewrite H; clear H.
  rewrite (rngl_sin_sub_right_r Hon Hop).
  generalize Hs2z; intros H.
  apply (rngl_opp_lt_compat Hop Hor) in H.
  rewrite (rngl_opp_0 Hop) in H.
  apply (rngl_nle_gt Hor) in H.
  apply rngl_leb_nle in H.
  rewrite H; clear H.
  rewrite rngl_cos_add_straight_r.
  rewrite (rngl_cos_sub_right_r Hon Hop).
  apply rngl_ltb_lt.
  apply (rngl_lt_opp_l Hop Hor).
  cbn.
  rewrite <- (rngl_add_sub_swap Hop).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_mul_r_diag_l Hon Hop).
  apply (rngl_add_pos_nonneg Hor).
  now apply (rngl_mul_pos_pos Hop Hor Hii).
  apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
  apply (rngl_le_0_sub Hop Hor).
  apply (rngl_sin_bound Hon Hop Hiv Hic Hed Hor).
}
apply (rngl_nle_gt Hor) in Hc2z.
remember (θ2 - angle_straight)%A as θ.
apply angle_add_move_r in Heqθ.
subst θ2; rename θ into θ2.
move θ2 before θ1.
rewrite (angle_add_add_swap Hic Hop) in Hzs23 |-*.
rewrite (angle_sub_add_distr Hic Hop) in Hc123, Hzs12.
rewrite (rngl_sin_add_straight_r Hon Hop) in Hs2z, Hzs23.
rewrite rngl_cos_add_straight_r in Hc2z |-*.
rewrite (rngl_sin_sub_straight_r Hon Hop) in Hzs12.
rewrite (rngl_cos_sub_straight_r Hon Hop) in Hc123.
rewrite <- (rngl_sin_sub_anticomm Hic Hop) in Hzs12.
apply (rngl_opp_neg_pos Hop Hor) in Hc2z, Hs2z.
apply (rngl_opp_pos_neg Hop Hor) in Hzs23.
apply (rngl_le_opp_r Hop Hor) in Hc123.
apply (rngl_le_opp_l Hop Hor).
move Hs2z before Hzs1.
apply (rngl_nlt_ge Hor).
intros H231.
progress unfold angle_add_overflow in Haov.
apply angle_ltb_ge in Haov.
apply angle_nlt_ge in Haov.
apply Haov; clear Haov.
rewrite (angle_add_add_swap Hic Hop).
rewrite angle_add_assoc.
rewrite <- angle_add_assoc.
rewrite (angle_straight_add_straight Hon Hop).
rewrite (angle_add_0_r Hon Hos).
progress unfold angle_ltb.
generalize Hzs23; intros H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
rewrite H; clear H.
rewrite (rngl_sin_add_straight_r Hon Hop).
generalize Hs2z; intros H.
apply (rngl_opp_lt_compat Hop Hor) in H.
rewrite (rngl_opp_0 Hop) in H.
apply (rngl_nle_gt Hor) in H.
apply rngl_leb_nle in H.
rewrite H; clear H.
rewrite rngl_cos_add_straight_r.
apply rngl_ltb_lt.
apply (rngl_lt_opp_r Hop Hor).
eapply (rngl_le_lt_trans Hor); [ | apply H231 ].
apply (rngl_add_le_mono_l Hop Hor).
destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hc1z]. {
  apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  apply rngl_sin_sub_nonneg_sin_le_sin; try easy.
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_nle_gt Hor) in Hc1z.
remember (θ1 - angle_right)%A as θ.
apply angle_add_move_r in Heqθ.
subst θ1; rename θ into θ1.
move θ1 after θ2.
rewrite (angle_sub_add_distr Hic Hop) in Hzs12.
rewrite (angle_add_sub_swap Hic Hop) in Hc123.
rewrite (rngl_sin_add_right_r Hon Hos) in Hzs1.
rewrite rngl_cos_add_right_r in Hc1z, Hc123, H231 |-*.
rewrite (rngl_sin_sub_right_r Hon Hop) in Hzs12.
rewrite (rngl_add_opp_r Hop) in Hc123, H231.
apply (rngl_opp_neg_pos Hop Hor) in Hc1z.
apply -> (rngl_le_sub_0 Hop Hor) in Hc123.
apply -> (rngl_lt_sub_0 Hop Hor) in H231.
apply (rngl_opp_pos_neg Hop Hor) in Hzs12.
move Hc1z after Hs2z; move Hzs1 after Hzs3.
apply (rngl_nle_gt Hor) in Hzs12.
exfalso.
apply Hzs12; clear Hzs12; cbn.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
apply (rngl_add_nonneg_nonneg Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
apply (rngl_mul_nonneg_nonneg Hop Hor).
now apply (rngl_lt_le_incl Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem angle_le_sub_le_add_l :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ θ1 θ2 θ3,
  angle_add_overflow θ2 θ3 = false
  → angle_add_overflow θ1 (- θ2)%A = false
  → (θ2 ≤ θ1)%A
  → (θ1 - θ2 ≤ θ3)%A
  → (θ1 ≤ θ2 + θ3)%A.
Proof.
(* perhaps the hypothesis (θ2 ≤ θ1) is not necessary
   because of "angle_add_overflow θ1 (- θ2)"
   but not sure *)
intros Hic Hon Hop Hed.
destruct_ac.
intros * Haov Hsov H21 Hc123.
progress unfold angle_leb in Hc123.
progress unfold angle_leb.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ3)%L as zs3 eqn:Hzs3.
remember (0 ≤? rngl_sin (θ1 - θ2))%L as zs12 eqn:Hzs12.
remember (0 ≤? rngl_sin (θ2 + θ3))%L as zs23 eqn:Hzs23.
symmetry in Hzs1, Hzs3, Hzs12, Hzs23.
destruct zs1. {
  apply rngl_leb_le in Hzs1.
  destruct (rngl_lt_dec Hor (rngl_sin θ2) 0) as [Hs2z| Hzs2]. {
    progress unfold angle_leb in H21.
    apply (rngl_nle_gt Hor) in Hs2z.
    apply rngl_leb_nle in Hs2z.
    rewrite Hs2z in H21.
    apply rngl_leb_le in Hzs1.
    now rewrite Hzs1 in H21.
  }
  apply (rngl_nlt_ge Hor) in Hzs2.
  move Hzs2 before Hzs1.
  destruct zs23; [ | easy ].
  apply rngl_leb_le in Hzs23.
  apply rngl_leb_le.
  destruct zs12. {
    apply rngl_leb_le in Hzs12.
    destruct zs3. {
      apply rngl_leb_le in Hzs3.
      apply rngl_leb_le in Hc123.
      move Hzs12 before Hzs23.
      move Hzs1 after Hzs3; move Hzs2 after Hzs3.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ2))%L as [Hzc2| Hc2z]. {
        now apply angle_le_sub_le_add_l_lemma_1.
      } {
        apply (rngl_nle_gt Hor) in Hc2z.
        now apply angle_le_sub_le_add_l_lemma_2.
      }
    } {
      clear Hc123.
      apply (rngl_leb_gt Hor) in Hzs3.
      destruct (rngl_lt_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
        now apply angle_le_sub_le_add_l_lemma_3.
      } {
        apply (rngl_nlt_ge Hor) in Hc2z.
        now apply angle_le_sub_le_add_l_lemma_4.
      }
    }
  } {
    destruct zs3; [ easy | ].
    apply (rngl_leb_gt Hor) in Hzs3, Hzs12.
    apply rngl_leb_le in Hc123.
    rewrite (rngl_sin_sub_anticomm Hic Hop) in Hzs12.
    rewrite (rngl_cos_sub_comm Hic Hop) in Hc123.
    apply (rngl_opp_neg_pos Hop Hor) in Hzs12.
    now apply angle_le_sub_le_add_l_lemma_5.
  }
}
apply (rngl_leb_gt Hor) in Hzs1.
destruct zs23. {
  exfalso.
  apply rngl_leb_le in Hzs23.
  destruct zs12. {
    apply rngl_leb_le in Hzs12.
    now apply angle_sub_not_overflow_sin_neg_sin_sub_nonneg in Hzs12.
  } {
    apply (rngl_leb_gt Hor) in Hzs12.
    destruct zs3; [ easy | ].
    apply (rngl_leb_gt Hor) in Hzs3.
    apply rngl_leb_le in Hc123.
    rewrite (rngl_sin_sub_anticomm Hic Hop) in Hzs12.
    rewrite (rngl_cos_sub_comm Hic Hop) in Hc123.
    apply (rngl_opp_neg_pos Hop Hor) in Hzs12.
    move Hzs1 after Hzs3.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ3)) as [Hzc3| Hc3z]. {
      now apply (angle_le_sub_le_add_l_lemma_6 Hic Hon Hop Hed θ1 θ2 θ3).
    } {
      apply (rngl_nle_gt Hor) in Hc3z.
      now apply (angle_le_sub_le_add_l_lemma_7 Hic Hon Hop Hed θ1 θ2 θ3).
    }
  }
}
apply (rngl_leb_gt Hor) in Hzs23.
apply rngl_leb_le.
destruct zs12. {
  exfalso.
  apply rngl_leb_le in Hzs12.
  now apply angle_sub_not_overflow_sin_neg_sin_sub_nonneg in Hzs12.
} {
  destruct zs3; [ easy | ].
  apply (rngl_leb_gt Hor) in Hzs3, Hzs12.
  apply rngl_leb_le in Hc123.
  rewrite (rngl_sin_sub_anticomm Hic Hop) in Hzs12.
  apply (rngl_opp_neg_pos Hop Hor) in Hzs12.
  move Hzs1 after Hzs3.
  now apply angle_le_sub_le_add_l_lemma_8.
}
Qed.
*)

End a.
