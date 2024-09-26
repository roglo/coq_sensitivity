(* RingLike_mul_with_order.v
   This file deals with multiplication properties in rings that have an
   order relation. The theorems here assume that this order relation is
   defined. *)

Require Import Utf8 Arith.
Require Import RingLike_structures.
Require Import RingLike_order.
Require Import RingLike_add.
Require Import RingLike_add_with_order.
Require Import RingLike_mul.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem rngl_mul_le_compat_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L.
Proof.
intros Hop Hor *.
specialize rngl_opt_ord as rr.
rewrite Hor in rr.
move rr after rp.
specialize rngl_ord_mul_le_compat_nonneg as H.
rewrite Hop in H.
apply H.
Qed.

Theorem rngl_mul_le_compat_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L.
Proof.
intros Hop Hor *.
specialize rngl_opt_ord as rr.
rewrite Hor in rr.
move rr after rp.
specialize rngl_ord_mul_le_compat_nonpos as H.
rewrite Hop in H.
apply H.
Qed.

Theorem rngl_mul_le_compat_non_opp :
  rngl_has_opp T = false →
  rngl_is_ordered T = true →
  ∀ a b c d, (a ≤ c)%L → (b ≤ d)%L → (a * b ≤ c * d)%L.
Proof.
intros Hop Hor * Hac Hbd.
specialize rngl_opt_ord as rr.
rewrite Hor in rr.
move rr after rp.
specialize rngl_ord_mul_le_compat_non_opp as H.
rewrite Hop in H.
cbn in H.
now apply H.
Qed.

Theorem rngl_mul_le_compat_nonpos_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d,
  (0 ≤ c ≤ a)%L
  → (b ≤ d ≤ 0)%L
  → (a * b ≤ c * d)%L.
Proof.
intros Hop Hor * Had Hcd.
apply (rngl_opp_le_compat Hop Hor).
do 2 rewrite <- (rngl_mul_opp_r Hop).
apply (rngl_mul_le_compat_nonneg Hop Hor); [ easy | ].
split.
now apply (rngl_opp_nonneg_nonpos Hop Hor).
now apply -> (rngl_opp_le_compat Hop Hor).
Qed.

Theorem rngl_mul_nonneg_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → 0 ≤ b → 0 ≤ a * b)%L.
Proof.
intros * Hop Hor * Ha Hb.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_mul_le_compat_nonneg Hop Hor) as H1.
specialize (H1 0 0 a b)%L.
assert (H : (0 ≤ 0 ≤ a)%L) by now split; [ apply (rngl_le_refl Hor) | ].
specialize (H1 H); clear H.
assert (H : (0 ≤ 0 ≤ b)%L) by now split; [ apply (rngl_le_refl Hor) | ].
specialize (H1 H); clear H.
now rewrite (rngl_mul_0_l Hos) in H1.
Qed.

Theorem rngl_mul_nonpos_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ 0 → b ≤ 0 → 0 ≤ a * b)%L.
Proof.
intros * Hop Hor * Ha Hb.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_mul_le_compat_nonpos Hop Hor) as H1.
specialize (H1 0 0 a b)%L.
assert (H : (a ≤ 0 ≤ 0)%L) by now split; [ | apply (rngl_le_refl Hor) ].
specialize (H1 H); clear H.
assert (H : (b ≤ 0 ≤ 0)%L) by now split; [ | apply (rngl_le_refl Hor) ].
specialize (H1 H); clear H.
now rewrite (rngl_mul_0_l Hos) in H1.
Qed.

Theorem rngl_mul_nonneg_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → b ≤ 0 → a * b ≤ 0)%L.
Proof.
intros * Hop Hor * Ha Hb.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_mul_le_compat_nonneg Hop Hor) as H1.
specialize (H1 0 0 a (- b))%L.
assert (H : (0 ≤ 0 ≤ a)%L) by now split; [ apply (rngl_le_refl Hor) | ].
specialize (H1 H); clear H.
assert (H : (0 ≤ 0 ≤ - b)%L). {
  split; [ apply (rngl_le_refl Hor) | ].
  apply (rngl_opp_le_compat Hop Hor) in Hb.
  now rewrite (rngl_opp_0 Hop) in Hb.
}
specialize (H1 H); clear H.
rewrite (rngl_mul_0_l Hos) in H1.
rewrite (rngl_mul_opp_r Hop) in H1.
apply (rngl_opp_le_compat Hop Hor) in H1.
rewrite (rngl_opp_involutive Hop) in H1.
now rewrite (rngl_opp_0 Hop) in H1.
Qed.

Theorem rngl_mul_nonpos_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ 0 → 0 ≤ b → a * b ≤ 0)%L.
Proof.
intros * Hop Hor * Ha Hb.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_mul_le_compat_nonneg Hop Hor) as H1.
specialize (H1 0 0 (- a) b)%L.
assert (H : (0 ≤ 0 ≤ - a)%L). {
  split; [ apply (rngl_le_refl Hor) | ].
  apply (rngl_opp_le_compat Hop Hor) in Ha.
  now rewrite (rngl_opp_0 Hop) in Ha.
}
specialize (H1 H); clear H.
assert (H : (0 ≤ 0 ≤ b)%L) by now split; [ apply (rngl_le_refl Hor) | ].
specialize (H1 H); clear H.
rewrite (rngl_mul_0_l Hos) in H1.
rewrite (rngl_mul_opp_l Hop) in H1.
apply (rngl_opp_le_compat Hop Hor) in H1.
rewrite (rngl_opp_involutive Hop) in H1.
now rewrite (rngl_opp_0 Hop) in H1.
Qed.

Theorem rngl_0_le_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (0 ≤ 1)%L.
Proof.
intros Hon Hop Hor.
destruct (rngl_le_dec Hor 0%L 1%L) as [| H1]; [ easy | ].
apply (rngl_not_le Hor) in H1.
destruct H1 as (H1, H2).
specialize (rngl_mul_nonpos_nonpos Hop Hor) as H3.
specialize (H3 1 1 H2 H2)%L.
now rewrite (rngl_mul_1_l Hon) in H3.
Qed.

Theorem rngl_0_leb_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (0 ≤? 1)%L = true.
Proof.
intros * Hon Hop Hor.
apply rngl_leb_le.
apply (rngl_0_le_1 Hon Hop Hor).
Qed.

Theorem rngl_mul_pos_neg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
  ∀ a b, (0 < a → b < 0 → a * b < 0)%L.
Proof.
intros Hop Hor Hid * Hza Hbz.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_mul_nonneg_nonpos Hop Hor). {
    now apply (rngl_lt_le_incl Hor).
  } {
    now apply (rngl_lt_le_incl Hor).
  }
}
intros H.
apply (rngl_integral Hos Hid) in H.
destruct H as [H| H]. {
  subst a.
  now apply (rngl_lt_irrefl Hor) in Hza.
} {
  subst b.
  now apply (rngl_lt_irrefl Hor) in Hbz.
}
Qed.

Theorem rngl_mul_diag_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ a * a)%L.
Proof.
intros Hop Hor *.
destruct (rngl_le_dec Hor 0%L a) as [Hap| Han]. {
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
} {
  apply (rngl_not_le Hor) in Han.
  now apply (rngl_mul_nonpos_nonpos Hop Hor).
}
Qed.

Theorem rngl_squ_abs :
  rngl_has_opp T = true →
  ∀ a, rngl_squ (rngl_abs a) = rngl_squ a.
Proof.
intros Hop *.
progress unfold rngl_abs.
destruct (a ≤? 0)%L; [ | easy ].
apply (rngl_squ_opp Hop).
Qed.

Theorem rngl_squ_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ a²)%L.
Proof.
intros Hop Hor *.
now apply rngl_mul_diag_nonneg.
Qed.

Theorem eq_rngl_add_square_0 :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool =
    true →
  ∀ a b : T, (a * a + b * b = 0)%L → a = 0%L ∧ b = 0%L.
Proof.
intros * Hop Hor Hii * Hab.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_eq_add_0 Hor) in Hab; cycle 1. {
  apply (rngl_mul_diag_nonneg Hop Hor).
} {
  apply (rngl_mul_diag_nonneg Hop Hor).
}
destruct Hab as (Ha, Hb).
split. {
  now apply (rngl_integral Hos Hii) in Ha; destruct Ha.
} {
  now apply (rngl_integral Hos Hii) in Hb; destruct Hb.
}
Qed.

Theorem rngl_0_lt_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  (0 < 1)%L.
Proof.
intros Hon Hop Hc1 Hor.
apply (rngl_lt_iff Hor).
split. 2: {
  apply not_eq_sym.
  now apply (rngl_1_neq_0_iff Hon).
}
apply (rngl_0_le_1 Hon Hop Hor).
Qed.

Theorem rngl_0_lt_2 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  (0 < 2)%L.
Proof.
intros Hon Hop Hc1 Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_le_lt_trans Hor _ 1)%L. {
  apply (rngl_0_le_1 Hon Hop Hor).
}
apply (rngl_lt_add_r Hos Hor).
apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_0_le_2 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (0 ≤ 2)%L.
Proof.
intros Hon Hop Hor.
apply (rngl_le_trans Hor _ 1)%L. {
  apply (rngl_0_le_1 Hon Hop Hor).
}
apply (rngl_le_add_r Hor).
apply (rngl_0_le_1 Hon Hop Hor).
Qed.

Theorem rngl_2_neq_0 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  (2 ≠ 0)%L.
Proof.
intros Hon Hop Hc1 Hor.
specialize (rngl_0_lt_2 Hon Hop Hc1 Hor) as H5.
intros H; rewrite H in H5.
now apply (rngl_lt_irrefl Hor) in H5.
Qed.

Theorem rngl_opp_1_le_0 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (-1 ≤ 0)%L.
Proof.
intros Hon Hop Hor.
apply (rngl_opp_nonpos_nonneg Hop Hor).
apply (rngl_0_le_1 Hon Hop Hor).
Qed.

Theorem rngl_opp_1_lt_0 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  rngl_characteristic T ≠ 1 →
  (-1 < 0)%L.
Proof.
intros Hon Hop Hor Hc1.
apply (rngl_opp_neg_pos Hop Hor).
apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_opp_1_lt_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  rngl_characteristic T ≠ 1 →
  (-1 < 1)%L.
Proof.
intros Hon Hop Hor Hc1.
apply (rngl_lt_le_trans Hor _ 0)%L.
apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
apply (rngl_0_le_1 Hon Hop Hor).
Qed.

Theorem rngl_opp_1_le_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  rngl_characteristic T ≠ 1 →
  (-1 ≤ 1)%L.
Proof.
intros Hon Hop Hor Hc1.
apply (rngl_lt_le_incl Hor).
apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
Qed.

Theorem rngl_of_nat_nonneg :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ n, (0 ≤ rngl_of_nat n)%L.
Proof.
intros Hon Hop Hor *.
induction n; [ apply (rngl_le_refl Hor) | ].
rewrite rngl_of_nat_succ.
eapply (rngl_le_trans Hor); [ apply IHn | ].
apply (rngl_le_add_l Hor).
apply (rngl_0_le_1 Hon Hop Hor).
Qed.

Theorem rngl_of_nat_inj_le :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  ∀ i j, i ≤ j ↔ (rngl_of_nat i ≤ rngl_of_nat j)%L.
Proof.
intros Hon Hop Hc1 Hor *.
apply (rngl_mul_nat_inj_le Hop Hor).
apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_of_nat_inj_lt :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  ∀ i j, i < j ↔ (rngl_of_nat i < rngl_of_nat j)%L.
Proof.
intros Hon Hop Hc1 Hor *.
apply (rngl_mul_nat_inj_lt Hop Hor).
apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_abs_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_abs 1 = 1)%L.
Proof.
intros Hon Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  now rewrite (H1 (rngl_abs 1)%L), (H1 1%L).
}
progress unfold rngl_abs.
remember (1 ≤? 0)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ | easy ].
apply rngl_leb_le in Hc.
apply (rngl_nlt_ge Hor) in Hc.
exfalso; apply Hc.
apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_abs_2 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_abs 2 = 2)%L.
Proof.
intros Hon Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1; apply H1.
}
progress unfold rngl_abs.
remember (2 ≤? 0)%L as tz eqn:Htz.
symmetry in Htz.
destruct tz; [ | easy ].
apply rngl_leb_le in Htz.
apply (rngl_nlt_ge Hor) in Htz.
exfalso; apply Htz.
apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_abs_mul :
  rngl_has_opp T = true →
  rngl_has_inv_and_1_or_quot T = true →
  rngl_is_ordered T = true →
  ∀ a b, (rngl_abs (a * b) = rngl_abs a * rngl_abs b)%L.
Proof.
intros Hop Hi1 Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
unfold rngl_abs.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
remember (b ≤? 0)%L as bz eqn:Hbz; symmetry in Hbz.
remember (a * b ≤? 0)%L as abz eqn:Habz; symmetry in Habz.
destruct abz. {
  apply rngl_leb_le in Habz.
  destruct az. {
    rewrite (rngl_mul_opp_l Hop).
    apply rngl_leb_le in Haz.
    destruct bz; [ | easy ].
    rewrite (rngl_mul_opp_r Hop).
    apply rngl_leb_le in Hbz.
    specialize (rngl_mul_nonpos_nonpos Hop Hor _ _ Haz Hbz) as H1.
    apply (rngl_le_antisymm Hor _ _ Habz) in H1.
    rewrite H1.
    now do 2 rewrite (rngl_opp_0 Hop).
  }
  apply (rngl_leb_gt Hor) in Haz.
  destruct bz; [ now rewrite (rngl_mul_opp_r Hop) | ].
  apply (rngl_leb_gt Hor) in Hbz.
  apply (rngl_nlt_ge Hor) in Habz.
  exfalso; apply Habz; clear Habz.
  apply (rngl_lt_iff Hor).
  split. {
    now apply (rngl_mul_nonneg_nonneg Hop Hor); apply (rngl_lt_le_incl Hor).
  }
  apply not_eq_sym.
  intros H1.
  apply (rngl_eq_mul_0_l Hos) in H1. {
    now subst a; apply (rngl_lt_irrefl Hor) in Haz.
  } {
    rewrite Hi1.
    now destruct (rngl_is_integral_domain T).
  } {
    intros H; subst b.
    now apply (rngl_lt_irrefl Hor) in Hbz.
  }
}
apply (rngl_leb_gt Hor) in Habz.
destruct az. {
  rewrite (rngl_mul_opp_l Hop).
  apply rngl_leb_le in Haz.
  destruct bz. {
    rewrite (rngl_mul_opp_r Hop).
    symmetry.
    apply (rngl_opp_involutive Hop).
  }
  apply (rngl_leb_gt Hor) in Hbz.
  apply (rngl_lt_iff Hor) in Hbz.
  destruct Hbz as (Hbz, Hzb).
  specialize (rngl_mul_nonpos_nonneg Hop Hor _ _ Haz Hbz) as H1.
  now apply (rngl_nlt_ge Hor) in H1.
}
apply (rngl_leb_gt Hor) in Haz.
destruct bz; [ | easy ].
apply rngl_leb_le in Hbz.
apply (rngl_lt_iff Hor) in Haz.
destruct Haz as (Haz, Hza).
specialize (rngl_mul_nonneg_nonpos Hop Hor _ _ Haz Hbz) as H1.
now apply (rngl_nlt_ge Hor) in H1.
Qed.

Theorem rngl_add_squ_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a² + b²)%L.
Proof.
intros Hop Hor *.
apply (rngl_add_nonneg_nonneg Hor);
apply (rngl_squ_nonneg Hop Hor).
Qed.

Theorem eq_rngl_squ_rngl_abs :
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
  ∀ a b, rngl_squ a = rngl_squ b → rngl_abs a = rngl_abs b.
Proof.
intros Hop Hic Hor Hii * Hab.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_sub_move_0_r Hop) in Hab.
rewrite (rngl_squ_sub_squ Hop Hic) in Hab.
apply (rngl_integral Hos Hii) in Hab.
destruct Hab as [Hab| Hab]. {
  apply (rngl_add_move_0_r Hop) in Hab.
  subst a.
  apply (rngl_abs_opp Hop Hor).
} {
  apply -> (rngl_sub_move_0_r Hop) in Hab.
  now subst a.
}
Qed.

Theorem rngl_mul_pos_pos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (0 < a)%L → (0 < b)%L → (0 < a * b)%L.
Proof.
intros Hop Hor Hii * Haz Hbz.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_lt_iff Hor) in Haz.
apply (rngl_lt_iff Hor) in Hbz.
apply (rngl_lt_iff Hor).
destruct Haz as (Haz, Hza).
destruct Hbz as (Hbz, Hzb).
split. {
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
}
apply not_eq_sym in Hza, Hzb.
apply not_eq_sym.
intros Hab.
now apply (rngl_eq_mul_0_l Hos Hii) in Hab.
Qed.

Theorem rngl_mul_neg_neg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (a < 0)%L → (b < 0)%L → (0 < a * b)%L.
Proof.
intros Hop Hor Hii * Haz Hbz.
rewrite <- (rngl_mul_opp_opp Hop).
apply (rngl_mul_pos_pos Hop Hor Hii).
now apply (rngl_opp_pos_neg Hop Hor).
now apply (rngl_opp_pos_neg Hop Hor).
Qed.

Theorem rngl_mul_pos_cancel_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (0 < a → 0 < a * b ↔ 0 < b)%L.
Proof.
intros Hop Hor Hii * Ha.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hb. {
  apply (rngl_lt_iff Hor) in Ha.
  apply (rngl_lt_iff Hor) in Hb.
  apply (rngl_lt_iff Hor).
  destruct Ha as (Haz, Hza).
  destruct Hb as (Habz, Hzab).
  apply not_eq_sym in Hza, Hzab.
  split. {
    apply (rngl_lt_eq_cases Hor) in Habz.
    destruct Habz as [Habz| Habz]. {
      apply (rngl_nle_gt Hor) in Habz.
      apply (rngl_nlt_ge Hor).
      intros Hb; apply Habz; clear Habz.
      apply (rngl_mul_nonneg_nonpos Hop Hor); [ easy | ].
      now apply (rngl_lt_le_incl Hor).
    }
    now rewrite Habz in Hzab.
  }
  intros H; subst b.
  now rewrite (rngl_mul_0_r Hos) in Hzab.
} {
  now apply (rngl_mul_pos_pos Hop Hor).
}
Qed.

Theorem rngl_mul_pos_cancel_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (0 < b → 0 < a * b ↔ 0 < a)%L.
Proof.
intros Hop Hor Hii * Ha.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hb. {
  apply (rngl_lt_iff Hor) in Ha.
  apply (rngl_lt_iff Hor) in Hb.
  apply (rngl_lt_iff Hor).
  destruct Ha as (Haz, Hza).
  destruct Hb as (Habz, Hzab).
  apply not_eq_sym in Hza, Hzab.
  split. {
    apply (rngl_lt_eq_cases Hor) in Habz.
    destruct Habz as [Habz| Habz]. {
      apply (rngl_nle_gt Hor) in Habz.
      apply (rngl_nlt_ge Hor).
      intros Hb; apply Habz; clear Habz.
      apply (rngl_mul_nonpos_nonneg Hop Hor); [ | easy ].
      now apply (rngl_lt_le_incl Hor).
    }
    now rewrite Habz in Hzab.
  }
  intros H; subst a.
  now rewrite (rngl_mul_0_l Hos) in Hzab.
} {
  now apply (rngl_mul_pos_pos Hop Hor).
}
Qed.

Theorem rngl_mul_lt_mono_pos_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c : T, (0 < a)%L → (b < c)%L ↔ (a * b < a * c)%L.
Proof.
intros Hop Hor Hii * Ha.
split; intros Hbc. {
  apply (rngl_lt_0_sub Hop Hor).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  apply (rngl_mul_pos_pos Hop Hor Hii); [ easy | ].
  now apply (rngl_lt_0_sub Hop Hor).
} {
  apply (rngl_lt_0_sub Hop Hor) in Hbc.
  rewrite <- (rngl_mul_sub_distr_l Hop) in Hbc.
  apply (rngl_mul_pos_cancel_l Hop Hor Hii) in Hbc; [ | easy ].
  now apply (rngl_lt_0_sub Hop Hor).
}
Qed.

Theorem rngl_mul_lt_mono_pos_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c : T, (0 < a)%L → (b < c)%L ↔ (b * a < c * a)%L.
Proof.
intros Hop Hor Hii * Ha.
split; intros Hbc. {
  apply (rngl_lt_0_sub Hop Hor).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  apply (rngl_mul_pos_pos Hop Hor Hii); [ | easy ].
  now apply (rngl_lt_0_sub Hop Hor).
} {
  apply (rngl_lt_0_sub Hop Hor) in Hbc.
  rewrite <- (rngl_mul_sub_distr_r Hop) in Hbc.
  apply (rngl_mul_pos_cancel_r Hop Hor Hii) in Hbc; [ | easy ].
  now apply (rngl_lt_0_sub Hop Hor).
}
Qed.

Theorem rngl_mul_le_mono_pos_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c : T, (0 < c)%L → (a ≤ b)%L ↔ (c * a ≤ c * b)%L.
Proof.
intros Hop Hor Hii * Hc.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hab. {
  apply (rngl_lt_eq_cases Hor) in Hab.
  destruct Hab as [Hab| Hab]; [ | subst b; apply (rngl_le_refl Hor) ].
  apply (rngl_le_0_sub Hop Hor).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  apply (rngl_mul_nonneg_nonneg Hop Hor). {
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_le_0_sub Hop Hor).
  now apply (rngl_lt_le_incl Hor).
} {
  apply (rngl_le_0_sub Hop Hor) in Hab.
  rewrite <- (rngl_mul_sub_distr_l Hop) in Hab.
  apply (rngl_nlt_ge Hor) in Hab.
  apply (rngl_nlt_ge Hor).
  intros H1; apply Hab; clear Hab.
  replace 0%L with (c * 0)%L by apply (rngl_mul_0_r Hos).
  apply (rngl_mul_lt_mono_pos_l Hop Hor Hii); [ easy | ].
  apply (rngl_nle_gt Hor).
  intros H2.
  apply -> (rngl_le_0_sub Hop Hor) in H2.
  now apply (rngl_nlt_ge Hor) in H2.
}
Qed.

Theorem rngl_mul_le_mono_nonneg_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 ≤ a)%L → (b ≤ c)%L → (a * b ≤ a * c)%L.
Proof.
intros Hop Hor * Ha Hbc.
apply (rngl_lt_eq_cases Hor) in Hbc.
destruct Hbc as [Hbc| Hbc]; [ | subst b; apply (rngl_le_refl Hor) ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_l Hop).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
apply (rngl_le_0_sub Hop Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_mul_le_mono_nonneg_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 ≤ c → a ≤ b → a * c ≤ b * c)%L.
Proof.
intros Hop Hor * Hc Hab.
apply (rngl_lt_eq_cases Hor) in Hab.
destruct Hab as [Hab| Hab]; [ | subst b; apply (rngl_le_refl Hor) ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_r Hop).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
apply (rngl_le_0_sub Hop Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_mul_le_mono_pos_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c : T, (0 < c)%L → (a ≤ b)%L ↔ (a * c ≤ b * c)%L.
Proof.
intros Hop Hor Hii * Hc.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hab. {
  apply (rngl_mul_le_mono_nonneg_r Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
} {
  apply (rngl_le_0_sub Hop Hor) in Hab.
  rewrite <- (rngl_mul_sub_distr_r Hop) in Hab.
  apply (rngl_nlt_ge Hor) in Hab.
  apply (rngl_nlt_ge Hor).
  intros H1; apply Hab; clear Hab.
  replace 0%L with (0 * c)%L by apply (rngl_mul_0_l Hos).
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii); [ easy | ].
  apply (rngl_nle_gt Hor).
  intros H2.
  apply -> (rngl_le_0_sub Hop Hor) in H2.
  now apply (rngl_nlt_ge Hor) in H2.
}
Qed.

Theorem rngl_mul_le_mono_nonpos_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a ≤ 0)%L → (b ≤ c)%L → (a * c ≤ a * b)%L.
Proof.
intros Hop Hor * Ha Hbc.
apply (rngl_lt_eq_cases Hor) in Hbc.
destruct Hbc as [Hbc| Hbc]; [ | subst b; apply (rngl_le_refl Hor) ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_l Hop).
apply (rngl_mul_nonpos_nonpos Hop Hor); [ easy | ].
apply (rngl_le_sub_0 Hop Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_mul_le_mono_nonpos_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (c ≤ 0 → a ≤ b → b * c ≤ a * c)%L.
Proof.
intros Hop Hor * Hc Hab.
apply (rngl_lt_eq_cases Hor) in Hab.
destruct Hab as [Hab| Hab]; [ | subst b; apply (rngl_le_refl Hor) ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_r Hop).
apply (rngl_mul_nonpos_nonpos Hop Hor); [ | easy ].
apply (rngl_le_sub_0 Hop Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_mul_lt_mono_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
   rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c d, (0 ≤ a < b → 0 ≤ c < d → a * c < b * d)%L.
Proof.
intros Hop Hor Hii * (Haz, Hab) (Hcz, Hcd).
apply (rngl_le_lt_trans Hor _ (b * c)%L). {
  apply (rngl_mul_le_mono_nonneg_r Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_mul_lt_mono_pos_l Hop Hor Hii); [ | easy ].
now apply (rngl_le_lt_trans Hor _ a).
Qed.

Theorem rngl_mul_min_distr_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c, (0 ≤ a)%L → rngl_min (a * b)%L (a * c)%L = (a * rngl_min b c)%L.
Proof.
intros Hop Hor Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Hza.
destruct (rngl_eq_dec Heo a 0%L) as [Haz| Haz]. {
  subst a.
  do 3 rewrite (rngl_mul_0_l Hos).
  apply (rngl_min_id Hor).
}
assert (H : (0 < a)%L). {
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  now apply not_eq_sym.
}
clear Hza Haz; rename H into Hza.
progress unfold rngl_min.
remember (_ * _ ≤? _ * _)%L as abc eqn:Habc.
remember (b ≤? c)%L as bc eqn:Hbc.
symmetry in Habc, Hbc.
destruct abc. {
  f_equal.
  destruct bc; [ easy | ].
  apply rngl_leb_le in Habc.
  apply (rngl_leb_gt Hor) in Hbc.
  apply (rngl_mul_le_mono_pos_l Hop Hor Hii) in Habc; [ | easy ].
  now apply (rngl_nle_gt Hor) in Hbc.
}
destruct bc; [ | easy ].
f_equal.
apply rngl_leb_le in Hbc.
apply (rngl_leb_gt Hor) in Habc.
apply (rngl_mul_lt_mono_pos_l Hop Hor Hii) in Habc; [ | easy ].
now apply (rngl_nle_gt Hor) in Habc.
Qed.

Theorem rngl_lt_mul_0_if :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a * b < 0)%L → (a < 0 < b)%L ∨ (0 < a)%L ∧ (b < 0)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hab.
remember (a <? 0)%L as az eqn:Haz.
symmetry in Haz.
destruct az. {
  apply rngl_ltb_lt in Haz.
  left.
  split; [ easy | ].
  remember (0 <? b)%L as zb eqn:Hzb.
  symmetry in Hzb.
  destruct zb; [ now apply rngl_ltb_lt in Hzb | exfalso ].
  apply (rngl_ltb_ge Hor) in Hzb.
  apply (rngl_nle_gt Hor) in Hab.
  apply Hab; clear Hab.
  apply (rngl_mul_nonpos_nonpos Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor) in Haz.
}
apply (rngl_ltb_ge Hor) in Haz.
right.
split. {
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  intros H; subst a.
  rewrite (rngl_mul_0_l Hos) in Hab.
  now apply (rngl_lt_irrefl Hor) in Hab.
}
apply (rngl_nle_gt Hor).
intros Hzb.
apply (rngl_nle_gt Hor) in Hab.
apply Hab; clear Hab.
now apply (rngl_mul_nonneg_nonneg Hop Hor).
Qed.

Theorem rngl_square_le_simpl_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b, (0 ≤ b → a * a ≤ b * b → a ≤ b)%L.
Proof.
intros Hop Hor Hii * Hzb Hab.
destruct (rngl_le_dec Hor a 0%L) as [Haz| Haz]. {
  now apply (rngl_le_trans Hor a 0%L b).
}
apply (rngl_nle_gt Hor) in Haz.
apply (rngl_nlt_ge Hor) in Hab.
apply (rngl_nlt_ge Hor).
intros Hba; apply Hab; clear Hab.
now apply (rngl_mul_lt_mono_nonneg Hop Hor Hii).
Qed.

Theorem rngl_pow_pos_nonneg :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  ∀ a n, (0 < a → 0 < a ^ n)%L.
Proof.
intros Hon Hop Hiv Hc1 Hor * Hza.
induction n; cbn. {
  apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
}
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
now apply (rngl_mul_pos_pos Hop Hor Hii).
Qed.

Theorem rngl_pow_ge_1 :
  rngl_has_opp T = true →
  rngl_has_1 T = true →
  rngl_is_ordered T = true →
  ∀ a n, (1 ≤ a → 1 ≤ a ^ n)%L.
Proof.
intros Hop Hon Hor * Hza.
induction n; [ apply (rngl_le_refl Hor) | cbn ].
rewrite <- (rngl_mul_1_l Hon 1%L).
apply (rngl_mul_le_compat_nonneg Hop Hor). {
  split; [ | easy ].
  apply (rngl_0_le_1 Hon Hop Hor).
} {
  split; [ | easy ].
  apply (rngl_0_le_1 Hon Hop Hor).
}
Qed.

Theorem rngl_pow_le_mono_r :
  rngl_has_opp T = true →
  rngl_has_1 T = true →
  rngl_is_ordered T = true →
  ∀ a m n, (1 ≤ a)%L → m ≤ n → (a ^ m ≤ a ^ n)%L.
Proof.
intros Hop Hon Hor * H1a Hmn.
revert n Hmn.
induction m; intros; cbn. {
  now apply (rngl_pow_ge_1 Hop Hon Hor).
}
destruct n; [ easy | cbn ].
apply Nat.succ_le_mono in Hmn.
apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
  apply (rngl_le_trans Hor _ 1%L); [ | easy ].
  apply (rngl_0_le_1 Hon Hop Hor).
}
now apply IHm.
Qed.

Theorem rngl_le_0_mul :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a * b → 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0)%L.
Proof.
intros Hon Hop Hiv Hor * Hab.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (rngl_le_dec Hor 0 a)%L as [Hza| Hza]. {
  destruct (rngl_lt_dec Hor 0 a)%L as [Hlza| Hlza]. 2: {
    apply (rngl_nlt_ge Hor) in Hlza.
    apply (rngl_le_antisymm Hor) in Hza; [ | easy ].
    subst a.
    destruct (rngl_le_dec Hor 0 b)%L as [Hzb| Hzb]; [ now left | ].
    apply (rngl_nle_gt Hor), (rngl_lt_le_incl Hor) in Hzb.
    now right.
  }
  rewrite <- (rngl_mul_0_r Hos a) in Hab.
  now left; apply (rngl_mul_le_mono_pos_l Hop Hor Hii) in Hab.
} {
  apply (rngl_nle_gt Hor) in Hza.
  right.
  rewrite <- (rngl_mul_0_l Hos b) in Hab.
  split; [ now apply (rngl_lt_le_incl Hor) | ].
  apply (rngl_nle_gt Hor) in Hza.
  apply (rngl_nlt_ge Hor).
  intros Hzb; apply Hza.
  now apply (rngl_mul_le_mono_pos_r Hop Hor Hii) in Hab.
}
Qed.

Theorem rngl_abs_le_squ_le :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (rngl_abs a ≤ rngl_abs b → a² ≤ b²)%L.
Proof.
intros Hop Hor * Hab.
progress unfold rngl_squ.
progress unfold rngl_abs in Hab.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
remember (b ≤? 0)%L as bz eqn:Hbz; symmetry in Hbz.
destruct az. {
  apply rngl_leb_le in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Hab.
    now apply (rngl_mul_le_compat_nonpos Hop Hor).
  } {
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Haz.
    rewrite (rngl_opp_0 Hop) in Haz.
    rewrite <- (rngl_mul_opp_opp Hop).
    apply (rngl_lt_le_incl Hor) in Hbz.
    now apply (rngl_mul_le_compat_nonneg Hop Hor).
  }
} {
  apply (rngl_leb_gt Hor) in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Hbz.
    rewrite (rngl_opp_0 Hop) in Hbz.
    rewrite <- (rngl_mul_opp_opp Hop b).
    apply (rngl_lt_le_incl Hor) in Haz.
    now apply (rngl_mul_le_compat_nonneg Hop Hor).
  } {
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_lt_le_incl Hor) in Haz, Hbz.
    now apply (rngl_mul_le_compat_nonneg Hop Hor).
  }
}
Qed.

Theorem rngl_abs_lt_squ_lt :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
  ∀ a b : T, (rngl_abs a < rngl_abs b)%L → (a² < b²)%L.
Proof.
intros Hic Hop Hor Hii * Hab.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_abs_le_squ_le Hop Hor).
  now apply (rngl_lt_le_incl Hor).
}
intros H.
apply (eq_rngl_squ_rngl_abs Hop Hic Hor Hii) in H.
rewrite H in Hab.
now apply (rngl_lt_irrefl Hor) in Hab.
Qed.

Theorem rngl_squ_le_abs_le :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b, (a² ≤ b² → rngl_abs a ≤ rngl_abs b)%L.
Proof.
intros Hop Hor Hii * Hab.
progress unfold rngl_squ in Hab.
progress unfold rngl_abs.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
remember (b ≤? 0)%L as bz eqn:Hbz; symmetry in Hbz.
destruct az. {
  apply rngl_leb_le in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    rewrite <- (rngl_mul_opp_opp Hop) in Hab.
    rewrite <- (rngl_mul_opp_opp Hop b) in Hab.
    apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in Hab; [ easy | ].
    rewrite <- (rngl_opp_0 Hop).
    now apply -> (rngl_opp_le_compat Hop Hor).
  } {
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Haz.
    rewrite (rngl_opp_0 Hop) in Haz.
    rewrite <- (rngl_mul_opp_opp Hop) in Hab.
    apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in Hab; [ easy | ].
    now apply (rngl_lt_le_incl Hor).
  }
} {
  apply (rngl_leb_gt Hor) in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Hbz.
    rewrite (rngl_opp_0 Hop) in Hbz.
    rewrite <- (rngl_mul_opp_opp Hop b) in Hab.
    now apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in Hab.
  } {
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_lt_le_incl Hor) in Haz, Hbz.
    now apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in Hab.
  }
}
Qed.

Theorem rngl_squ_lt_abs_lt :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (a² < b²)%L → (rngl_abs a < rngl_abs b)%L.
Proof.
intros Hop Hor Hii * Hab.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_squ_le_abs_le Hop Hor Hii).
  now apply (rngl_lt_le_incl Hor).
}
intros H.
apply (f_equal rngl_squ) in H.
do 2 rewrite (rngl_squ_abs Hop) in H.
rewrite H in Hab.
now apply (rngl_lt_irrefl Hor) in Hab.
Qed.

Theorem int_part :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  rngl_is_archimedean T = true →
  ∀ a, ∃ n, (rngl_of_nat n ≤ rngl_abs a < rngl_of_nat (n + 1))%L.
Proof.
intros Hon Hop Hc1 Hor Har *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_archimedean_ub Har Hor) as H1.
destruct (rngl_lt_dec Hor (rngl_abs a) 1)%L as [H1x| H1x]. {
  exists 0; cbn.
  rewrite rngl_add_0_r.
  split; [ | easy ].
  apply (rngl_abs_nonneg Hop Hor).
}
destruct (rngl_lt_dec Hor 1 (rngl_abs a))%L as [Hx1| Hx1]. 2: {
  apply (rngl_nlt_ge Hor) in H1x, Hx1.
  apply (rngl_le_antisymm Hor) in H1x; [ | easy ].
  rewrite H1x.
  exists 1; cbn.
  rewrite rngl_add_0_r.
  split; [ apply (rngl_le_refl Hor) | ].
  apply (rngl_lt_iff Hor).
  split. 2: {
    intros H12.
    apply (f_equal (λ b, rngl_sub b 1))%L in H12.
    rewrite (rngl_sub_diag Hos) in H12.
    rewrite (rngl_add_sub Hos) in H12.
    symmetry in H12; revert H12.
    apply (rngl_1_neq_0_iff Hon), Hc1.
  }
  apply (rngl_le_add_r Hor).
  apply (rngl_0_le_1 Hon Hop Hor).
}
clear H1x.
apply (H1 1 (rngl_abs a))%L.
split; [ apply (rngl_0_lt_1 Hon Hop Hc1 Hor) | easy ].
Qed.

End a.

Arguments rngl_mul_le_mono_pos_l {T ro rp} Hop Hor Hii (a b c)%_L.
Arguments rngl_mul_le_mono_pos_r {T ro rp} Hop Hor Hii (a b c)%_L.
