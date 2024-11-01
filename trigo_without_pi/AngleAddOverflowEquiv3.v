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

Definition angle_add_overflow3 θ1 θ2 :=
  ((θ1 ≠? 0)%A && (- θ1 ≤? θ2)%A)%bool.

(* to be completed
Theorem angle_add_overflow_equiv3 :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = angle_add_overflow3 θ1 θ2.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  intros.
  rewrite (H1 θ1), (H1 θ2).
  rewrite angle_add_overflow_0_l; symmetry.
  progress unfold angle_add_overflow3.
  progress unfold angle_eqb.
  cbn.
  rewrite (proj2 (rngl_eqb_eq Hed _ 1%L) eq_refl).
  rewrite (proj2 (rngl_eqb_eq Hed _ 0%L) eq_refl).
  easy.
}
intros.
progress unfold angle_add_overflow.
progress unfold angle_add_overflow3.
remember (θ1 =? 0)%A as z1 eqn:Hz1.
symmetry in Hz1.
destruct z1. {
  cbn.
  apply angle_eqb_eq in Hz1.
  subst θ1.
  rewrite angle_add_0_l.
  apply Bool.not_true_iff_false.
  apply angle_nlt_ge.
  apply angle_nonneg.
}
apply angle_eqb_neq in Hz1.
progress unfold angle_ltb.
progress unfold angle_leb.
cbn - [ angle_add ].
rewrite (rngl_leb_opp_r Hop Hor).
rewrite (rngl_opp_0 Hop).
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (rngl_sin θ1 ≤? 0)%L as s1z eqn:Hs1z.
symmetry in Hzs1, Hs1z.
move s1z before zs1.
destruct zs1. {
  destruct s1z. {
    apply rngl_leb_le in Hzs1, Hs1z.
    apply (rngl_le_antisymm Hor) in Hzs1; [ clear Hs1z | easy ].
    apply eq_rngl_sin_0 in Hzs1.
    destruct Hzs1; [ easy | subst θ1 ].
    clear Hz1.
    rewrite rngl_sin_add_straight_l.
    rewrite rngl_cos_add_straight_l.
    cbn.
    rewrite (rngl_leb_opp_r Hop Hor).
    rewrite (rngl_opp_0 Hop).
    remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
    remember (rngl_sin θ2 ≤? 0)%L as s2z eqn:Hs2z.
    symmetry in Hzs2, Hs2z.
    move s2z before zs2.
    destruct zs2. {
      destruct s2z. {
        apply rngl_leb_le in Hzs2, Hs2z.
        apply (rngl_le_antisymm Hor) in Hzs2; [ clear Hs2z | easy ].
        apply eq_rngl_sin_0 in Hzs2.
        destruct Hzs2; subst θ2; cbn. {
          transitivity false. {
            apply rngl_ltb_ge.
            apply (rngl_le_refl Hor).
          } {
            symmetry.
            apply (rngl_leb_gt Hor).
            apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
          }
        }
        cbn.
        rewrite (rngl_opp_involutive Hop).
        transitivity true. {
          apply rngl_ltb_lt.
          apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
        } {
          symmetry.
          apply rngl_leb_le.
          apply (rngl_le_refl Hor).
        }
      }
      symmetry.
      apply (rngl_leb_gt Hor).
      apply (rngl_lt_iff Hor).
      split; [ apply rngl_cos_bound | ].
      intros H; symmetry in H.
      apply eq_rngl_cos_opp_1 in H; subst θ2.
      cbn in Hs2z, Hzs2.
      now rewrite Hs2z in Hzs2.
    }
    destruct s2z. {
      apply rngl_ltb_lt.
      apply (rngl_opp_lt_compat Hop Hor).
      do 2 rewrite (rngl_opp_involutive Hop).
      apply (rngl_lt_iff Hor).
      split; [ apply rngl_cos_bound | ].
      intros H.
      apply eq_rngl_cos_1 in H; subst θ2.
      cbn in Hs2z, Hzs2.
      now rewrite Hs2z in Hzs2.
    }
    exfalso.
    apply (rngl_leb_gt Hor) in Hzs2, Hs2z.
    now apply (rngl_lt_asymm Hor) in Hzs2.
  }
  remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
  remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
  symmetry in Hzs12, Hzs2.
  destruct zs12. {
    destruct zs2. {
      apply rngl_leb_le in Hzs1, Hzs2, Hzs12.
      apply (rngl_leb_gt Hor) in Hs1z.
      apply rngl_ltb_ge.
      apply rngl_cos_add_le_cos; [ | easy | easy | easy ].
      left.
      intros H; subst θ1.
      cbn in Hs1z.
      now apply (rngl_lt_irrefl Hor) in Hs1z.
    }
    apply rngl_leb_le in Hzs1, Hzs12.
    apply (rngl_leb_gt Hor) in Hs1z, Hzs2.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ1)) as [Hzc1| Hzc1]. {
      remember (rngl_cos θ1 ≤? rngl_cos θ2)%L as c12 eqn:Hc12.
      symmetry in Hc12.
      destruct c12. {
        apply rngl_leb_le in Hc12.
        apply rngl_ltb_lt.
        apply quadrant_1_quadrant_4_cos_lt_cos_add; try easy.
        now apply (rngl_le_trans Hor _ (rngl_cos θ1)).
      }
      apply (rngl_leb_gt Hor) in Hc12.
      apply rngl_ltb_ge.
      destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
        change_angle_opp θ2.
        progress sin_cos_opp_hyp T Hzs2.
        progress sin_cos_opp_hyp T Hzs12.
        progress sin_cos_opp_hyp T Hc12.
        progress sin_cos_opp_hyp T Hzc2.
        progress sin_cos_opp_goal T.
        exfalso.
        apply (rngl_nle_gt Hor) in Hc12.
        apply Hc12; clear Hc12.
        apply quadrant_1_sin_sub_nonneg_cos_le; try easy.
        now apply (rngl_lt_le_incl Hor) in Hzs2.
      }
      apply (rngl_nle_gt Hor) in Hzc2.
      change_angle_add_r θ2 angle_straight.
      progress sin_cos_add_sub_straight_hyp T Hzs2.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hc12.
      progress sin_cos_add_sub_straight_hyp T Hzc2.
      progress sin_cos_add_sub_straight_goal T.
      exfalso.
      apply (rngl_nlt_ge Hor) in Hzs12.
      apply Hzs12; clear Hzs12.
      cbn.
      apply (rngl_add_pos_nonneg Hor).
      now apply (rngl_mul_pos_pos Hop Hor Hii).
      apply (rngl_lt_le_incl Hor) in Hzs2.
      now apply (rngl_mul_nonneg_nonneg Hop Hor).
    }
    remember (rngl_cos θ1 ≤? rngl_cos θ2)%L as c12 eqn:Hc12.
    symmetry in Hc12.
    destruct c12. {
      apply rngl_leb_le in Hc12.
      apply rngl_ltb_lt.
      apply (rngl_nle_gt Hor) in Hzc1.
(**)
      change_angle_sub_l θ1 angle_straight.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hs1z.
      progress sin_cos_add_sub_straight_hyp T Hzs1.
      progress sin_cos_add_sub_straight_hyp T Hc12.
      progress sin_cos_add_sub_straight_hyp T Hzc1.
      progress sin_cos_add_sub_straight_goal T.
      rewrite (rngl_add_opp_r Hop).
      apply (rngl_lt_0_sub Hop Hor).
      destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hzc2]. {
        change_angle_opp θ2.
        progress sin_cos_opp_hyp T Hzs2.
        progress sin_cos_opp_hyp T Hc12.
        progress sin_cos_opp_hyp T Hzc2.
        rewrite angle_sub_opp_r in Hzs12 |-*.
Search (rngl_cos _ < rngl_cos _)%L.
apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff; try easy.
now apply (rngl_lt_le_incl Hor) in Hzc1.
About rngl_sin_add_nonneg.
Search (0 ≤ rngl_cos _)%L.
apply rngl_cos_lt_rngl_cos_sub with (θ2 := θ2) in Hzs12; try easy.
rewrite rngl_cos_sub_comm in Hzs12.
now rewrite angle_add_sub in Hzs12.
...
        change_angle_add_r θ2 angle_right.
        progress sin_cos_add_sub_right_hyp T Hzs2.
        progress sin_cos_add_sub_right_hyp T Hc12.
        progress sin_cos_add_sub_right_hyp T Hzc2.
        rewrite angle_sub_sub_distr in Hzs12 |-*.
        progress sin_cos_add_sub_right_goal T.
        rewrite rngl_sin_add_right_r in Hzs12.
...
        apply quadrant_1_sin_sub_pos_cos_lt; try easy. {
Search (0 ≤ rngl_cos (_ + _))%L.
...
Search (rngl_cos _ < rngl_cos _)%L.
apply rngl_cos_cos_sin_sin_nonneg_sin_lt_cos_lt_iff; try easy.
Search (rngl_cos (_ + _) < rngl_cos _)%L.
...
      change_angle_sub_r θ1 angle_right.
      progress sin_cos_add_sub_right_hyp T Hzs12.
      progress sin_cos_add_sub_right_hyp T Hs1z.
      progress sin_cos_add_sub_right_hyp T Hzs1.
      progress sin_cos_add_sub_right_hyp T Hc12.
      progress sin_cos_add_sub_right_hyp T Hzc1.
      progress sin_cos_add_sub_right_goal T.
...
      change_angle_add_r θ1 angle_straight.
      progress sin_cos_add_sub_straight_hyp T Hzs12.
      progress sin_cos_add_sub_straight_hyp T Hs1z.
      progress sin_cos_add_sub_straight_hyp T Hzs1.
...
Search (0 ≤ rngl_cos (_ + _) + rngl_cos _)%L.
...
        apply rngl_cos_decr.
        split
Search (_ → rngl_cos _ ≤ rngl_cos _)%L.
...
        apply rngl_cos_decr.
...
        rewrite rngl_cos_sub_comm.
        apply quadrant_1_sin_sub_nonneg_cos_le; try easy.
Search (rngl_cos (_ - _) ≤ rngl_cos _)%L.
...
        change_angle_add_r θ2 angle_straight.
        progress sin_cos_add_sub_straight_hyp T Hzs2.
        progress sin_cos_add_sub_straight_hyp T Hzs12.
        progress sin_cos_add_sub_straight_hyp T Hc12.
        progress sin_cos_add_sub_straight_hyp T Hzc2.
        progress sin_cos_add_sub_straight_goal T.
        cbn.
...
        change_angle_add_r θ2 angle_right.
        progress sin_cos_add_sub_right_hyp T Hzs2.
        progress sin_cos_add_sub_right_hyp T Hzc2.
        progress sin_cos_add_sub_right_hyp T Hzs12.
        progress sin_cos_add_sub_right_hyp T Hc12.
        progress sin_cos_add_sub_right_goal T.
        apply (rngl_lt_le_incl Hor) in Hzs2.
Search (_ → rngl_sin _ ≤ rngl_sin _)%L.
...
        apply rngl_sin_sub_nonneg_sin_le_sin; try easy.
        rewrite angle_sub_add_distr.
        rewrite angle_sub_sub_swap.
        rewrite angle_sub_diag.
        rewrite angle_sub_0_l.
        cbn.
        apply (rngl_nle_gt Hor) in Hcc.
        apply Hcc; clear Hcc; cbn.
        apply rngl_cos_bound.
Search (_ → rngl_sin (_ + _) ≤ rngl_sin _)%L.
...
...
...
Search (_ → rngl_cos _ < rngl_cos (_ + _))%L.
...
      rewrite angle_add_comm.
      apply rngl_cos_le_cos_add; try easy.
...
...
Search (rngl_sin (_ + _) ≤ rngl_cos _)%L.
Search (_ → rngl_cos (_ + _) ≤ rngl_cos _)%L.
Search (rngl_cos (_ + _) < rngl_cos _ → _)%L.
...
      apply rngl_cos_add_le_cos; try easy.
...
*)

Definition angle_add_not_overflow3 θ1 θ2 :=
  θ2 = 0%A ∨ (θ1 < -θ2)%A.

Theorem angle_add_not_overflow3_not :
  ∀ θ1 θ2, angle_add_not_overflow3 θ1 θ2 ↔ angle_add_overflow3 θ1 θ2 = false.
Proof.
destruct_ac.
intros.
progress unfold angle_add_overflow3.
progress unfold angle_add_not_overflow3.
remember (θ1 =? 0)%A as z1 eqn:Hz1.
symmetry in Hz1.
split; intros H12. {
  destruct z1; [ easy | ].
  apply angle_eqb_neq in Hz1.
  destruct H12 as [H12| H12]. {
    subst θ2.
    progress unfold angle_leb.
    cbn.
    rewrite (rngl_leb_refl Hor).
    rewrite (rngl_leb_0_opp Hop Hor).
    remember (rngl_sin θ1 ≤? 0)%L as s1z eqn:Hs1z.
    symmetry in Hs1z.
    destruct s1z; [ | easy ].
    apply rngl_leb_le in Hs1z.
    apply (rngl_leb_gt Hor).
    apply (rngl_lt_iff Hor).
    split; [ apply rngl_cos_bound | ].
    intros H1.
    now apply eq_rngl_cos_1 in H1.
  }
  apply angle_leb_gt.
  now apply angle_lt_opp_r.
}
destruct z1. {
  apply angle_eqb_eq in Hz1; subst θ1.
  destruct (angle_eq_dec θ2 0) as [H2z| H2z]; [ now left | right ].
  apply angle_lt_iff.
  split; [ apply angle_nonneg | ].
  intros H; symmetry in H.
  apply H2z; clear H2z.
  apply angle_opp_inj.
  now rewrite angle_opp_0.
}
apply angle_leb_gt in H12.
destruct (angle_eq_dec θ2 0) as [H2z| H2z]; [ now left | right ].
now apply angle_lt_opp_r.
Qed.

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
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
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

Theorem angle_add_not_overflow_equiv3_1 :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = false ↔ angle_add_not_overflow3 θ1 θ2.
Proof.
destruct_ac.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros.
progress unfold angle_add_overflow.
progress unfold angle_add_not_overflow3.
split; intros H12. {
  destruct (angle_eq_dec θ2 0) as [H2z| H2z]; [ now left | right ].
  progress unfold angle_ltb in H12.
  progress unfold angle_ltb.
  move H2z before θ2.
  cbn.
  rewrite (rngl_leb_0_opp Hop Hor).
  remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
  remember (rngl_sin θ2 ≤? 0)%L as sz2 eqn:Hsz2.
  remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
  symmetry in Hzs1, Hsz2, Hzs12.
  destruct zs12. {
    destruct zs1; [ | easy ].
    destruct sz2; [ | easy ].
    apply rngl_leb_le in Hzs1, Hzs12, Hsz2.
    apply rngl_ltb_lt.
    apply (rngl_ltb_ge_iff Hor) in H12.
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
  apply (rngl_ltb_ge_iff Hor) in H12.
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
destruct H12 as [H12| H12]. {
  subst θ2.
  rewrite angle_add_0_r.
  apply Bool.not_true_iff_false.
  apply angle_lt_irrefl.
}
progress unfold angle_ltb in H12.
progress unfold angle_ltb.
cbn in H12.
rewrite (rngl_leb_0_opp Hop Hor) in H12.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (rngl_sin θ2 ≤? 0)%L as sz2 eqn:Hsz2.
remember (0 ≤? rngl_sin (θ1 + θ2))%L as zs12 eqn:Hzs12.
symmetry in Hzs1, Hsz2, Hzs12.
destruct zs1. {
  destruct zs12; [ | easy ].
  apply rngl_leb_le in Hzs1, Hzs12.
  destruct sz2. {
    apply rngl_leb_le in Hsz2.
    apply rngl_ltb_lt in H12.
    destruct (rngl_le_dec Hor 0 (rngl_cos θ2)) as [Hzc2| Hc2z]. {
      apply Bool.not_true_iff_false.
      intros Hcc.
      apply rngl_ltb_lt in Hcc.
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
      apply Bool.not_true_iff_false.
      intros Hcc.
      apply rngl_ltb_lt in Hcc.
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
          apply (rngl_opp_1_le_1 Hon Hop Hor).
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
    apply Bool.not_true_iff_false.
    intros Hcc.
    apply rngl_ltb_lt in Hcc.
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
  apply rngl_ltb_ge.
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
apply rngl_ltb_ge.
apply (rngl_lt_le_incl Hor) in Hzs1, Hsz2.
apply rngl_cos_le_cos_add; try easy.
Qed.

Theorem angle_add_overflow_equiv3 :
  ∀ θ1 θ2,
  angle_add_overflow θ1 θ2 = angle_add_overflow3 θ1 θ2.
Proof.
intros.
remember (angle_add_overflow3 θ1 θ2) as ov3 eqn:Hov3.
symmetry in Hov3.
destruct ov3. 2: {
  apply angle_add_not_overflow_equiv3_1.
  now apply angle_add_not_overflow3_not.
} {
  apply Bool.not_false_iff_true in Hov3.
  apply Bool.not_false_iff_true.
  intros H; apply Hov3; clear Hov3.
  rename H into Hov3.
  apply angle_add_not_overflow_equiv3_1 in Hov3.
  now apply angle_add_not_overflow3_not.
}
Qed.

End a.
