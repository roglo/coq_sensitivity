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

End a.
