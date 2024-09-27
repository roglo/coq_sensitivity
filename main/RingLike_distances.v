(* distances and limits *)

Require Import Utf8 Arith.
Require Import RingLike_structures.
Require Import RingLike_order.
Require Import RingLike_add.
Require Import RingLike_mul.
Require Import RingLike_div.
Require Import RingLike_add_with_order.
Require Import RingLike_mul_with_order.
Require Import RingLike_div_with_order.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

(* distances *)

Record is_dist {A} (dist : A → A → T) :=
  { is_dist_symmetry : ∀ a b, dist a b = dist b a;
    is_dist_separation : ∀ a b, dist a b = 0%L ↔ a = b;
    is_dist_triangular : ∀ a b c, (dist a c ≤ dist a b + dist b c)%L }.

Definition rngl_dist a b := rngl_abs (a - b)%L.

Theorem rngl_dist_is_dist :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  is_dist rngl_dist.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
progress unfold rngl_dist.
split. {
  intros.
  apply (rngl_abs_sub_comm Hop Hor).
} {
  intros.
  split; intros Hab. {
    apply (eq_rngl_abs_0 Hop) in Hab.
    now apply -> (rngl_sub_move_0_r Hop) in Hab.
  }
  subst b.
  rewrite (rngl_sub_diag Hos).
  apply (rngl_abs_0 Hop).
} {
  intros.
  specialize (rngl_abs_triangle Hop Hor) as H1.
  specialize (H1 (a - b) (b - c))%L.
  rewrite (rngl_add_sub_assoc Hop) in H1.
  now rewrite (rngl_sub_add Hop) in H1.
}
Qed.

(* limits *)

Definition is_Cauchy_sequence {A} (dist : A → A → T) (u : nat → A) :=
  ∀ ε : T, (0 < ε)%L →
  ∃ N : nat, ∀ p q : nat, N ≤ p → N ≤ q → (dist (u p) (u q) < ε)%L.

Definition is_limit_when_tending_to {A B} da db (f : A → B) (a : A) (l : B) :=
  (∀ ε, 0 < ε → ∃ η, 0 < η ∧
   ∀ x : A, da x a < η → db (f x) l < ε)%L.

Definition is_limit_when_tending_to_inf {A} dist (f : nat → A) (l : A) :=
  ∀ ε, (0 < ε)%L → ∃ N, ∀ n, N ≤ n → (dist (f n) l < ε)%L.

Definition is_complete A (dist : A → A → T) :=
  ∀ u, is_Cauchy_sequence dist u
  → ∃ c, is_limit_when_tending_to_inf dist u c.

Definition is_derivative {A} (da : A → A → T) dist f f' :=
  ∀ a,
  is_limit_when_tending_to da dist (λ x, dist (f x) (f a) / da x a)%L
    a (f' a).

Definition continuous_at {A B} da db (f : A → B) a :=
  is_limit_when_tending_to da db f a (f a).

Definition continuous {A B} da db (f : A → B) :=
  ∀ a, continuous_at da db f a.

(* limit with ring-like distance *)

Definition rngl_is_Cauchy_sequence :=
  is_Cauchy_sequence rngl_dist.

Definition rngl_is_limit_when_tending_to :=
  is_limit_when_tending_to rngl_dist rngl_dist.

Definition rngl_is_limit_when_tending_to_inf :=
  is_limit_when_tending_to_inf rngl_dist.

Definition rngl_is_derivative :=
  is_derivative rngl_dist.

Definition rngl_is_complete :=
  is_complete T rngl_dist.

Definition rngl_continuous_at :=
  continuous_at rngl_dist rngl_dist.

Definition rngl_continuous :=
  continuous rngl_dist rngl_dist.

(* properties of distances and limits *)

Theorem dist_refl :
  ∀ A (dist : A → A → T) (Hid : is_dist dist) a, dist a a = 0%L.
Proof.
intros * Hid *.
destruct Hid as (Hdsym, Hdsep, Hdtri).
apply (proj2 (Hdsep a a) eq_refl).
Qed.

Theorem dist_nonneg :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ A (dist : A → A → T) (Hid : is_dist dist) a b, (0 ≤ dist a b)%L.
Proof.
intros Hon Hop Hiv Hor * Hid *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1.
  apply (rngl_le_refl Hor).
}
destruct Hid as (Hdsym, Hdsep, Hdtri).
specialize (proj2 (Hdsep a a) eq_refl) as H1.
specialize (Hdtri a b a) as H2.
rewrite H1, (Hdsym b a) in H2.
rewrite <- (rngl_mul_2_l Hon) in H2.
replace 0%L with (2 * 0)%L in H2 by apply (rngl_mul_0_r Hos).
apply (rngl_mul_le_mono_pos_l Hop Hor Hii) in H2; [ easy | ].
apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_limit_interv :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ u a b c,
  (∀ i, (a ≤ u i ≤ b)%L)
  → is_limit_when_tending_to_inf rngl_dist u c
  → (a ≤ c ≤ b)%L.
Proof.
intros Hop Hor.
intros * Hi Hlim.
progress unfold is_limit_when_tending_to_inf in Hlim.
split. {
  apply (rngl_nlt_ge Hor).
  intros Hca.
  specialize (Hlim (a - c))%L.
  assert (H : (0 < a - c)%L) by now apply (rngl_lt_0_sub Hop Hor).
  specialize (Hlim H); clear H.
  destruct Hlim as (N, HN).
  specialize (HN N (Nat.le_refl _)).
  specialize (Hi N).
  specialize (is_dist_triangular _ (rngl_dist_is_dist Hop Hor)) as H1.
  specialize (H1 (u N) a c).
  progress unfold rngl_dist in HN.
  progress unfold rngl_dist in H1.
  rewrite (rngl_abs_nonneg_eq Hop Hor) in HN. 2: {
    apply (rngl_le_0_sub Hop Hor).
    apply (rngl_le_trans Hor _ a); [ | apply Hi ].
    now apply (rngl_lt_le_incl Hor) in Hca.
  }
  apply (rngl_sub_lt_mono_r Hop Hor) in HN.
  now apply (rngl_nle_gt Hor) in HN.
} {
  apply (rngl_nlt_ge Hor).
  intros Hbc.
  specialize (Hlim (c - b))%L.
  assert (H : (0 < c - b)%L) by now apply (rngl_lt_0_sub Hop Hor).
  specialize (Hlim H); clear H.
  destruct Hlim as (N, HN).
  specialize (HN N (Nat.le_refl _)).
  specialize (Hi N).
  specialize (is_dist_triangular _ (rngl_dist_is_dist Hop Hor)) as H1.
  specialize (H1 (u N) b c).
  progress unfold rngl_dist in HN.
  progress unfold rngl_dist in H1.
  rewrite (rngl_abs_nonpos_eq Hop Hor) in HN. 2: {
    apply (rngl_le_sub_0 Hop Hor).
    apply (rngl_le_trans Hor _ b); [ apply Hi | ].
    now apply (rngl_lt_le_incl Hor) in Hbc.
  }
  rewrite (rngl_opp_sub_distr Hop) in HN.
  apply (rngl_sub_lt_mono_l Hop Hor) in HN.
  now apply (rngl_nle_gt Hor) in HN.
}
Qed.

Theorem limit_unique :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ A (dist : A → A → T) (id : is_dist dist) u lim1 lim2,
  is_limit_when_tending_to_inf dist u lim1
  → is_limit_when_tending_to_inf dist u lim2
  → lim1 = lim2.
Proof.
intros Hon Hop Hiv Hor * Hid * Hu1 Hu2.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  destruct Hid as (Hdsym, Hdsep, Hdtri).
  assert (H : ∀ a b : A, a = b) by now intros; apply Hdsep, H1.
  apply H.
}
specialize (dist_nonneg Hon Hop Hiv Hor _ dist Hid) as Hdpos.
destruct Hid as (Hdsym, Hdsep, Hdtri).
assert (Hu : is_limit_when_tending_to_inf dist (λ _, lim1) lim2). {
  intros ε Hε.
  assert (Hε2 : (0 < ε / 2)%L). {
    apply (rngl_mul_lt_mono_pos_r Hop Hor Hii) with (a := 2%L). {
      apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
    }
    rewrite (rngl_mul_0_l Hos).
    rewrite (rngl_div_mul Hon Hiv); [ easy | ].
    apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
  }
  specialize (Hu1 (ε / 2) Hε2)%L.
  specialize (Hu2 (ε / 2) Hε2)%L.
  destruct Hu1 as (N1, Hu1).
  destruct Hu2 as (N2, Hu2).
  exists (max N1 N2).
  intros n HN.
  eapply (rngl_le_lt_trans Hor); [ apply (Hdtri _ (u n)) | ].
  rewrite Hdsym.
  replace ε with (ε / 2 + ε / 2)%L. 2: {
    apply (rngl_mul_cancel_r Hi1 _ _ 2%L). {
      apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
    }
    rewrite rngl_mul_add_distr_r.
    rewrite (rngl_div_mul Hon Hiv). 2: {
      apply (rngl_2_neq_0 Hon Hop Hc1 Hor).
    }
    symmetry.
    apply (rngl_mul_2_r Hon).
  }
  apply (rngl_add_lt_compat Hop Hor). {
    apply Hu1.
    eapply Nat.le_trans; [ | apply HN ].
    apply Nat.le_max_l.
  } {
    apply Hu2.
    eapply Nat.le_trans; [ | apply HN ].
    apply Nat.le_max_r.
  }
}
assert (H : ∀ ε : T, (0 < ε)%L → (dist lim1 lim2 < ε)%L). {
  intros ε Hε.
  specialize (Hu ε Hε).
  destruct Hu as (N, HN).
  now apply (HN N).
}
clear Hu; rename H into Hu.
apply Hdsep.
apply (rngl_abs_le_ε Hon Hop Hiv Hor).
intros ε Hε.
specialize (Hu ε Hε).
rewrite (rngl_abs_nonneg_eq Hop Hor); [ | apply Hdpos ].
apply (rngl_lt_le_incl Hor).
eapply (rngl_le_lt_trans Hor); [ | apply Hu ].
apply (rngl_le_refl Hor).
Qed.

End a.

Arguments rngl_is_complete T {ro}.
