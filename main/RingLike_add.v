Require Import Utf8 Arith.
Require Import RingLike_structures.
Require Import RingLike_order.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem rngl_add_0_r : ∀ a, (a + 0 = a)%L.
Proof.
intros a; simpl.
rewrite rngl_add_comm.
apply rngl_add_0_l.
Qed.

Theorem rngl_add_opp_l :
  rngl_has_opp T = true →
  ∀ a b, (- a + b)%L = (b - a)%L.
Proof.
intros Hop *.
rewrite rngl_add_comm.
progress unfold rngl_sub.
now rewrite Hop.
Qed.

Theorem rngl_add_opp_r :
  rngl_has_opp T = true →
  ∀ a b, (a + - b)%L = (a - b)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
now rewrite Hop.
Qed.

Theorem rngl_add_opp_diag_l :
  rngl_has_opp T = true →
  ∀ x, (- x + x = 0)%L.
Proof.
intros H1 *.
specialize rngl_opt_add_opp_diag_l as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_sub_diag :
  rngl_has_opp_or_subt T = true →
  ∀ a, (a - a = 0)%L.
Proof.
intros Hos *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite Hop.
  rewrite rngl_add_comm.
  now apply rngl_add_opp_diag_l.
}
remember (rngl_has_subt T) as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_add_sub as H1.
  rewrite Hmo in H1.
  specialize (H1 0%L a).
  now rewrite rngl_add_0_l in H1.
}
apply rngl_has_opp_or_subt_iff in Hos.
destruct Hos; congruence.
Qed.

Theorem rngl_subt_diag :
  rngl_has_opp_or_subt T = true →
  ∀ a, rngl_subt a a = 0%L.
Proof.
intros Hos *.
specialize (rngl_sub_diag Hos a) as H1.
unfold rngl_sub in H1.
remember (rngl_has_opp T) as op eqn:Hop; symmetry in Hop.
destruct op. {
  unfold rngl_subt.
  unfold rngl_has_opp in Hop.
  destruct rngl_opt_opp_or_subt; [ | easy ].
  now destruct s.
}
remember (rngl_has_subt T) as su eqn:Hsu; symmetry in Hsu.
destruct su; [ easy | ].
apply rngl_has_opp_or_subt_iff in Hos.
destruct Hos; congruence.
Qed.

Theorem rngl_sub_add :
  rngl_has_opp T = true →
  ∀ a b, (a - b + b = a)%L.
Proof.
intros Hop *.
unfold rngl_sub; rewrite Hop.
rewrite <- rngl_add_assoc.
rewrite (rngl_add_opp_diag_l Hop).
apply rngl_add_0_r.
Qed.

Theorem rngl_add_sub :
  rngl_has_opp_or_subt T = true →
  ∀ a b, (a + b - b = a)%L.
Proof.
intros Hom *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite Hop.
  rewrite <- rngl_add_assoc.
  rewrite (rngl_add_comm b).
  now rewrite rngl_add_opp_diag_l, rngl_add_0_r.
}
remember (rngl_has_subt T) as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_add_sub as H1.
  rewrite Hmo in H1.
  apply H1.
}
apply rngl_has_opp_or_subt_iff in Hom.
destruct Hom; congruence.
Qed.

Theorem rngl_add_cancel_l :
  rngl_has_opp_or_subt T = true →
  ∀ a b c, (a + b = a + c)%L → (b = c)%L.
Proof.
intros Hom * Habc.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  apply (f_equal (λ x, rngl_sub x a)) in Habc.
  do 2 rewrite (rngl_add_comm a) in Habc.
  unfold rngl_sub in Habc.
  rewrite Hop in Habc.
  do 2 rewrite <- rngl_add_assoc in Habc.
  rewrite rngl_add_opp_r in Habc; [ | easy ].
  rewrite rngl_sub_diag in Habc; [ | easy ].
  now do 2 rewrite rngl_add_0_r in Habc.
}
remember (rngl_has_subt T) as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_add_sub as H1.
  rewrite Hmo in H1.
  specialize (H1 c a) as H2.
  rewrite rngl_add_comm, <- Habc in H2.
  rewrite rngl_add_comm in H2.
  now rewrite H1 in H2.
}
apply rngl_has_opp_or_subt_iff in Hom.
destruct Hom; congruence.
Qed.

Theorem rngl_add_move_l :
  rngl_has_opp T = true →
  ∀ a b c, (a + b)%L = c ↔ b = (c - a)%L.
Proof.
intros Hop *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hb. {
  subst c; symmetry.
  rewrite rngl_add_comm.
  apply (rngl_add_sub Hos).
} {
  subst b.
  rewrite rngl_add_comm.
  apply (rngl_sub_add Hop).
}
Qed.

Theorem rngl_add_move_r :
  rngl_has_opp T = true →
  ∀ a b c, (a + b)%L = c ↔ a = (c - b)%L.
Proof.
intros Hop *.
rewrite rngl_add_comm.
apply (rngl_add_move_l Hop).
Qed.

Theorem rngl_sub_move_l :
  rngl_has_opp T = true →
  ∀ a b c, (a - b)%L = c ↔ b = (a - c)%L.
Proof.
intros Hop *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hb. {
  apply (rngl_add_move_l Hop).
  subst c.
  apply (rngl_sub_add Hop).
} {
  apply (rngl_add_move_l Hop) in Hb.
  subst a.
  apply (rngl_add_sub Hos).
}
Qed.

Theorem rngl_sub_move_r :
  rngl_has_opp T = true →
  ∀ a b c, (a - b)%L = c ↔ a = (c + b)%L.
Proof.
intros Hop *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Ha. {
  subst c; symmetry.
  apply (rngl_sub_add Hop).
} {
  subst a.
  apply (rngl_add_sub Hos).
}
Qed.

Theorem rngl_add_sub_eq_l :
  rngl_has_opp_or_subt T = true →
  ∀ a b c, (a + b = c → c - a = b)%L.
Proof.
intros Hom * Hab.
rewrite <- Hab.
rewrite rngl_add_comm.
now apply rngl_add_sub.
Qed.

Theorem rngl_add_sub_eq_r :
  rngl_has_opp_or_subt T = true →
   ∀ a b c, (a + b = c → c - b = a)%L.
Proof.
intros Hom * Hab.
apply rngl_add_sub_eq_l; [ easy | ].
now rewrite rngl_add_comm.
Qed.

Theorem rngl_sub_compat_l : ∀ a b c,
  a = b → (a - c = b - c)%L.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem rngl_add_cancel_r :
  rngl_has_opp_or_subt T = true →
  ∀ a b c, (a + c = b + c)%L → (a = b)%L.
Proof.
intros Hom * Habc.
apply rngl_sub_compat_l with (c := c) in Habc.
now do 2 rewrite rngl_add_sub in Habc.
Qed.

Theorem rngl_add_move_0_r :
  rngl_has_opp T = true →
  ∀ a b, (a + b = 0)%L ↔ (a = - b)%L.
Proof.
intros Hro *.
split; intros H. {
  apply rngl_sub_compat_l with (c := b) in H.
  rewrite rngl_add_sub in H; [ | now apply rngl_has_opp_or_subt_iff; left ].
  unfold rngl_sub in H.
  rewrite Hro in H.
  now rewrite rngl_add_0_l in H.
} {
  rewrite H.
  now rewrite rngl_add_opp_diag_l.
}
Qed.

Theorem rngl_add_compat_r : ∀ a b c,
  (a = b)%L → (a + c = b + c)%L.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem rngl_sub_move_0_r :
  rngl_has_opp T = true →
  ∀ a b : T, (a - b)%L = 0%L ↔ a = b.
Proof.
intros Hop *.
split. {
  intros Hab.
  apply (rngl_add_compat_r _ _ b) in Hab.
  unfold rngl_sub in Hab.
  rewrite Hop in Hab.
  rewrite <- rngl_add_assoc in Hab.
  rewrite rngl_add_opp_diag_l in Hab; [ | easy ].
  now rewrite rngl_add_0_r, rngl_add_0_l in Hab.
} {
  intros Hab.
  rewrite Hab.
  apply rngl_sub_diag.
  now apply rngl_has_opp_or_subt_iff; left.
}
Qed.

Theorem rngl_opp_0 : rngl_has_opp T = true → (- 0 = 0)%L.
Proof.
intros Hro.
transitivity (0 + - 0)%L. {
  symmetry.
  apply rngl_add_0_l.
}
rewrite rngl_add_opp_r; [ | easy ].
apply rngl_sub_diag.
now apply rngl_has_opp_or_subt_iff; left.
Qed.

Theorem rngl_subt_0_r :
  rngl_has_subt T = true →
  ∀ a, rngl_subt a 0%L = a.
Proof.
intros Hsu *.
specialize rngl_opt_add_sub as H1.
rewrite Hsu in H1.
unfold rngl_sub in H1.
rewrite Hsu in H1.
unfold rngl_has_subt in Hsu.
unfold rngl_has_opp in H1.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
destruct os as [opp| subt ]; [ easy | ].
specialize (H1 a 0%L).
now rewrite rngl_add_0_r in H1.
Qed.

Theorem rngl_sub_0_l :
  rngl_has_opp T = true →
  ∀ a, (0 - a = - a)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
rewrite Hop.
apply rngl_add_0_l.
Qed.

Theorem rngl_sub_0_r :
  rngl_has_opp_or_subt T = true →
  ∀ a, (a - 0 = a)%L.
Proof.
intros Hom *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite Hop.
  rewrite rngl_opp_0; [ | easy ].
  apply rngl_add_0_r.
}
remember (rngl_has_subt T) as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_add_sub as H1.
  rewrite Hmo in H1.
  specialize (H1 a 0%L) as H2.
  now rewrite rngl_add_0_r in H2.
}
apply rngl_has_opp_or_subt_iff in Hom.
destruct Hom; congruence.
Qed.

Theorem rngl_opp_add_distr :
  rngl_has_opp T = true →
  ∀ a b, (- (a + b) = - b - a)%L.
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hop'.
rewrite Hop in Hop'.
apply rngl_add_cancel_l with (a := (a + b)%L); [ now apply Hop'; left | ].
rewrite (rngl_add_opp_r Hop).
rewrite rngl_sub_diag; [ | now apply Hop'; left ].
unfold rngl_sub.
rewrite Hop.
rewrite rngl_add_assoc.
do 2 rewrite (rngl_add_opp_r Hop).
rewrite rngl_add_sub; [ | now apply Hop'; left ].
symmetry.
apply rngl_sub_diag.
now apply Hop'; left.
Qed.

Theorem rngl_add_add_swap : ∀ n m p, (n + m + p = n + p + m)%L.
Proof.
intros n m p; simpl.
do 2 rewrite <- rngl_add_assoc.
assert (m + p = p + m)%L as H by apply rngl_add_comm.
rewrite H; reflexivity.
Qed.

Theorem rngl_add_add_add_swap :
  ∀ a b c d, ((a + b) + (c + d) = (a + c) + (b + d))%L.
Proof.
intros.
do 2 rewrite <- rngl_add_assoc.
f_equal.
rewrite rngl_add_comm, rngl_add_assoc.
apply rngl_add_add_swap.
Qed.

Theorem rngl_sub_sub_swap :
  rngl_has_opp T = true →
  ∀ a b c, (a - b - c = a - c - b)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
rewrite Hop.
apply rngl_add_add_swap.
Qed.

Theorem rngl_add_compat_l : ∀ a b c,
  (a = b)%L → (c + a = c + b)%L.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem rngl_add_sub_assoc :
  rngl_has_opp T = true →
  ∀ a b c, (a + (b - c) = a + b - c)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
rewrite Hop.
apply rngl_add_assoc.
Qed.

Theorem rngl_add_sub_swap :
  rngl_has_opp T = true →
  ∀ a b c, (a + b - c = a - c + b)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
rewrite Hop.
apply rngl_add_add_swap.
Qed.

Theorem rngl_add_sub_simpl_l :
  rngl_has_opp_or_subt T = true →
  ∀ a b c : T, (a + b - (a + c) = b - c)%L.
Proof.
intros Hom *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub; rewrite Hop.
  rewrite rngl_opp_add_distr; [ | easy ].
  unfold rngl_sub; rewrite Hop.
  rewrite rngl_add_assoc.
  rewrite rngl_add_add_swap.
  rewrite (rngl_add_add_swap a).
  rewrite rngl_add_opp_r; [ | easy ].
  rewrite rngl_add_opp_r; [ | easy ].
  rewrite rngl_add_opp_r; [ | easy ].
  rewrite rngl_sub_diag, rngl_add_0_l; [ easy | easy ].
}
remember (rngl_has_subt T) as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_sub_add_distr as H1.
  rewrite Hmo in H1.
  rewrite H1.
  rewrite rngl_add_comm.
  rewrite rngl_add_sub; [ easy | easy ].
}
apply rngl_has_opp_or_subt_iff in Hom.
destruct Hom; congruence.
Qed.

Theorem rngl_opp_involutive :
  rngl_has_opp T = true →
  ∀ x, (- - x)%L = x.
Proof.
intros Hro *.
symmetry.
apply (rngl_add_move_0_r Hro).
rewrite (rngl_add_opp_r Hro).
apply rngl_sub_diag.
now apply rngl_has_opp_or_subt_iff; left.
Qed.

Theorem rngl_sub_opp_r :
  rngl_has_opp T = true →
  ∀ a b, (a - - b = a + b)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
rewrite Hop.
f_equal.
apply (rngl_opp_involutive Hop).
Qed.

Theorem rngl_opp_inj :
  rngl_has_opp T = true →
  ∀ a b, (- a = - b)%L → a = b.
Proof.
intros Hro * H.
rewrite <- (rngl_opp_involutive Hro a).
rewrite H.
now apply rngl_opp_involutive.
Qed.

Theorem rngl_add_le_compat :
  rngl_is_ordered T = true →
  ∀ a b c d, (a ≤ b → c ≤ d → a + c ≤ b + d)%L.
Proof.
intros Hor *.
specialize rngl_opt_ord as H.
rewrite Hor in H.
apply H.
Qed.

Theorem rngl_eq_add_0 :
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → 0 ≤ b → a + b = 0 → a = 0 ∧ b = 0)%L.
Proof.
intros Hor * Haz Hbz Hab.
split. {
  apply (rngl_le_antisymm Hor) in Haz; [ easy | ].
  rewrite <- Hab.
  remember (a + b)%L as ab.
  rewrite <- (rngl_add_0_r a); subst ab.
  apply rngl_add_le_compat; [ easy | now apply rngl_le_refl | easy ].
} {
  apply (rngl_le_antisymm Hor) in Hbz; [ easy | ].
  rewrite <- Hab.
  remember (a + b)%L as ab.
  rewrite <- (rngl_add_0_l b); subst ab.
  apply rngl_add_le_compat; [ easy | easy | now apply rngl_le_refl ].
}
Qed.

Theorem rngl_opp_sub_distr :
  rngl_has_opp T = true →
  ∀ a b, (- (a - b) = b - a)%L.
Proof.
intros Hro *.
unfold rngl_sub at 1.
rewrite Hro.
rewrite rngl_opp_add_distr; [ | easy ].
now rewrite rngl_opp_involutive.
Qed.

Theorem rngl_sub_add_distr :
  rngl_has_opp_or_subt T = true →
  ∀ a b c, (a - (b + c) = a - b - c)%L.
Proof.
intros Hos *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite rngl_opp_add_distr; [ | easy ].
  unfold rngl_sub; rewrite Hop.
  rewrite rngl_add_assoc.
  apply rngl_add_add_swap.
}
remember (rngl_has_subt T) as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_sub_add_distr as H1.
  now rewrite Hmo in H1.
}
apply rngl_has_opp_or_subt_iff in Hos.
now destruct Hos; congruence.
Qed.

Theorem rngl_sub_sub_distr :
  rngl_has_opp T = true →
  ∀ a b c, (a - (b - c) = a - b + c)%L.
Proof.
intros Hop *.
unfold rngl_sub.
rewrite Hop.
rewrite (rngl_opp_add_distr Hop).
rewrite (rngl_opp_involutive Hop).
unfold rngl_sub; rewrite Hop.
rewrite rngl_add_assoc.
apply rngl_add_add_swap.
Qed.

Theorem rngl_le_0_sub :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 ≤ b - a ↔ a ≤ b)%L.
Proof.
intros * Hop Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_add_le_compat Hor) as H1.
split; intros Hab. {
  specialize (H1 0%L (b - a)%L a a Hab (rngl_le_refl Hor _)).
  rewrite <- (rngl_sub_sub_distr Hop) in H1.
  rewrite (rngl_sub_diag Hos) in H1.
  now rewrite rngl_add_0_l, (rngl_sub_0_r Hos) in H1.
} {
  specialize (H1 a b (- a)%L (- a)%L Hab (rngl_le_refl Hor _)).
  do 2 rewrite (rngl_add_opp_r Hop) in H1.
  now rewrite (rngl_sub_diag Hos) in H1.
}
Qed.

Theorem rngl_le_sub_0 :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a - b ≤ 0 ↔ a ≤ b)%L.
Proof.
intros Hop Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_add_le_compat Hor) as H1.
split; intros Hab. {
  specialize (H1 (a - b) 0 b b Hab (rngl_le_refl Hor _))%L.
  rewrite (rngl_sub_add Hop) in H1.
  now rewrite rngl_add_0_l in H1.
} {
  specialize (H1 a b (- b) (- b) Hab (rngl_le_refl Hor _))%L.
  do 2 rewrite (rngl_add_opp_r Hop) in H1.
  now rewrite (rngl_sub_diag Hos) in H1.
}
Qed.

Theorem rngl_leb_sub_0 :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, ((a - b ≤? 0) = (a ≤? b))%L.
Proof.
intros Hop Hor.
intros.
apply rngl_le_iff_leb_eq.
apply (rngl_le_sub_0 Hop Hor).
Qed.

Theorem rngl_lt_0_sub :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < b - a ↔ a < b)%L.
Proof.
intros * Hop Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hab. {
  apply (rngl_lt_iff Hor) in Hab.
  apply (rngl_lt_iff Hor).
  destruct Hab as (Hab, Habz).
  split; [ now apply (rngl_le_0_sub Hop Hor) | ].
  intros H; subst b.
  now rewrite (rngl_sub_diag Hos) in Habz.
} {
  apply (rngl_lt_iff Hor) in Hab.
  apply (rngl_lt_iff Hor).
  destruct Hab as (Hab, Habz).
  split; [ now apply (rngl_le_0_sub Hop Hor) | ].
  apply not_eq_sym.
  intros H1.
  apply Habz; symmetry.
  now apply (rngl_sub_move_0_r Hop).
}
Qed.

Theorem rngl_opp_le_compat :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ x y, (x ≤ y ↔ - y ≤ - x)%L.
Proof.
intros * Hop Hor *.
split; intros Hxy. {
  apply (rngl_le_0_sub Hop Hor).
  rewrite (rngl_sub_opp_r Hop).
  rewrite rngl_add_comm, (rngl_add_opp_r Hop).
  now apply (rngl_le_0_sub Hop Hor).
} {
  apply (rngl_le_0_sub Hop Hor).
  progress unfold rngl_sub.
  rewrite Hop.
  rewrite rngl_add_comm.
  rewrite <- (rngl_opp_involutive Hop y).
  rewrite (rngl_add_opp_r Hop).
  now apply (rngl_le_0_sub Hop Hor).
}
Qed.

Theorem rngl_opp_lt_compat :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ x y, (x < y ↔ - y < - x)%L.
Proof.
intros * Hop Hor *.
split; intros Hxy. {
  apply (rngl_lt_iff Hor) in Hxy.
  apply (rngl_lt_iff Hor).
  split. {
    apply (rngl_opp_le_compat Hop Hor).
    now do 2 rewrite (rngl_opp_involutive Hop).
  } {
    intros H; symmetry in H.
    apply (f_equal rngl_opp) in H.
    now do 2 rewrite (rngl_opp_involutive Hop) in H.
  }
} {
  apply (rngl_lt_iff Hor) in Hxy.
  apply (rngl_lt_iff Hor).
  split. {
    now apply (rngl_opp_le_compat Hop Hor).
  } {
    intros H; symmetry in H.
    now apply (f_equal rngl_opp) in H.
  }
}
Qed.

Theorem rngl_opp_nonneg_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ - a)%L ↔ (a ≤ 0)%L.
Proof.
intros Hop Hor *.
split; intros Ha. {
  apply (rngl_opp_le_compat Hop Hor).
  now rewrite (rngl_opp_0 Hop).
} {
  apply (rngl_opp_le_compat Hop Hor) in Ha.
  now rewrite (rngl_opp_0 Hop) in Ha.
}
Qed.

Theorem rngl_opp_nonpos_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (- a ≤ 0)%L ↔ (0 ≤ a)%L.
Proof.
intros Hop Hor *.
split; intros Ha. {
  apply (rngl_opp_le_compat Hop Hor).
  now rewrite (rngl_opp_0 Hop).
} {
  apply (rngl_opp_le_compat Hop Hor) in Ha.
  now rewrite (rngl_opp_0 Hop) in Ha.
}
Qed.

Theorem rngl_opp_neg_pos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (- a < 0 ↔ 0 < a)%L.
Proof.
intros Hop Hor *.
rewrite <- (rngl_opp_0 Hop) at 1.
split; intros Ha. {
  now apply (rngl_opp_lt_compat Hop Hor) in Ha.
} {
  now apply (rngl_opp_lt_compat Hop Hor) in Ha.
}
Qed.

Theorem rngl_opp_pos_neg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 < - a)%L ↔ (a < 0)%L.
Proof.
intros Hop Hor *.
split; intros Ha. {
  apply (rngl_opp_lt_compat Hop Hor).
  now rewrite (rngl_opp_0 Hop).
} {
  apply (rngl_opp_lt_compat Hop Hor) in Ha.
  now rewrite (rngl_opp_0 Hop) in Ha.
}
Qed.

Theorem rngl_mul_nat_add_r : ∀ a m n,
  rngl_mul_nat a (m + n) = (rngl_mul_nat a m + rngl_mul_nat a n)%L.
Proof.
intros.
unfold rngl_mul_nat, mul_nat.
induction m; cbn; [ now rewrite rngl_add_0_l | ].
rewrite <- rngl_add_assoc; f_equal.
apply IHm.
Qed.

Theorem rngl_of_nat_add : ∀ m n,
  rngl_of_nat (m + n) = (rngl_of_nat m + rngl_of_nat n)%L.
Proof.
intros.
apply rngl_mul_nat_add_r.
Qed.

Theorem rngl_of_nat_sub :
  rngl_has_opp_or_subt T = true →
  ∀ m n : nat, n ≤ m → rngl_of_nat (m - n) = (rngl_of_nat m - rngl_of_nat n)%L.
Proof.
intros Hos * Hnm.
replace m with (n + (m - n)) at 2. 2: {
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm.
  apply Nat.add_sub.
}
rewrite rngl_of_nat_add.
symmetry.
rewrite rngl_add_comm.
apply (rngl_add_sub Hos).
Qed.

Theorem rngl_of_nat_1 : rngl_of_nat 1 = 1%L.
Proof. apply rngl_add_0_r. Qed.

Theorem rngl_of_nat_2 : rngl_of_nat 2 = 2%L.
Proof. now cbn; rewrite rngl_add_0_r. Qed.

Theorem rngl_mul_nat_succ :
  ∀ a n, rngl_mul_nat a (S n) = (a + rngl_mul_nat a n)%L.
Proof.
intros.
rewrite <- Nat.add_1_l.
rewrite rngl_mul_nat_add_r.
now cbn; rewrite rngl_add_0_r.
Qed.

Theorem rngl_of_nat_succ :
  ∀ n, rngl_of_nat (S n) = (1 + rngl_of_nat n)%L.
Proof. easy. Qed.

Theorem rngl_add_lt_mono :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T,
  (a < b → c + a < c + b)%L.
Proof.
intros Hos Hor * Hab.
apply (rngl_lt_iff Hor) in Hab.
destruct Hab as (Hab, Haeb).
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_add_le_compat Hor); [ | easy ].
  apply (rngl_le_refl Hor).
} {
  intros H; apply Haeb; clear Haeb.
  now apply (rngl_add_cancel_l Hos) in H.
}
Qed.

Theorem rngl_add_lt_mono_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T,
  (a < b ↔ c + a < c + b)%L.
Proof.
intros Hop Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hab. {
  now apply (rngl_add_lt_mono Hos Hor).
} {
  apply (rngl_lt_0_sub Hop Hor) in Hab.
  rewrite (rngl_add_sub_simpl_l Hos) in Hab.
  now apply (rngl_lt_0_sub Hop Hor).
}
Qed.

Theorem rngl_add_lt_mono_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T,
  (a < b ↔ a + c < b + c)%L.
Proof.
intros Hop Hor *.
do 2 rewrite (rngl_add_comm _ c).
now apply (rngl_add_lt_mono_l Hop Hor).
Qed.

Theorem rngl_le_add_le_sub_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a + b ≤ c ↔ b ≤ c - a)%L.
Proof.
intros Hop Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Habc. {
  specialize (rngl_add_le_compat Hor) as H1.
  specialize (H1 (a + b) c (- a) (- a) Habc)%L.
  specialize (H1 (rngl_le_refl Hor _)).
  do 2 rewrite (rngl_add_opp_r Hop) in H1.
  rewrite rngl_add_comm in H1.
  now rewrite (rngl_add_sub Hos) in H1.
} {
  apply (rngl_le_0_sub Hop Hor).
  rewrite (rngl_sub_add_distr Hos).
  now apply (rngl_le_0_sub Hop Hor).
}
Qed.

Theorem rngl_le_add_le_sub_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a + b ≤ c ↔ a ≤ c - b)%L.
Proof.
intros Hop Hor *.
rewrite rngl_add_comm.
apply (rngl_le_add_le_sub_l Hop Hor).
Qed.

Theorem rngl_sub_le_mono_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T, (a ≤ b)%L ↔ (c - b ≤ c - a)%L.
Proof.
intros Hop Hor *.
split; intros Hab. {
  progress unfold rngl_sub.
  rewrite Hop.
  apply (rngl_add_le_compat Hor); [ apply (rngl_le_refl Hor) | ].
  now apply -> (rngl_opp_le_compat Hop Hor).
} {
  apply (rngl_opp_le_compat Hop Hor) in Hab.
  do 2 rewrite (rngl_opp_sub_distr Hop) in Hab.
  apply (rngl_add_le_compat Hor) with (c := c) (d := c) in Hab. 2: {
    apply (rngl_le_refl Hor).
  }
  now do 2 rewrite (rngl_sub_add Hop) in Hab.
}
Qed.

Theorem rngl_sub_le_mono_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a ≤ b ↔ a - c ≤ b - c)%L.
Proof.
intros Hop Hor *.
split; intros Hab. {
  rewrite <- (rngl_opp_sub_distr Hop c a).
  rewrite <- (rngl_opp_sub_distr Hop c b).
  apply -> (rngl_opp_le_compat Hop Hor).
  now apply (rngl_sub_le_mono_l Hop Hor).
} {
  apply (rngl_add_le_compat Hor _ _ c c) in Hab. 2: {
    apply (rngl_le_refl Hor).
  }
  now do 2 rewrite (rngl_sub_add Hop) in Hab.
}
Qed.

Theorem rngl_sub_lt_mono_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T, (a < b)%L ↔ (c - b < c - a)%L.
Proof.
intros Hop Hor *.
progress unfold rngl_sub.
rewrite Hop.
split; intros Hab. {
  apply (rngl_add_lt_mono_l Hop Hor).
  now apply -> (rngl_opp_lt_compat Hop Hor).
} {
  apply (rngl_add_lt_mono_l Hop Hor) in Hab.
  now apply (rngl_opp_lt_compat Hop Hor).
}
Qed.

Theorem rngl_sub_lt_mono_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T, (a < b)%L ↔ (a - c < b - c)%L.
Proof.
intros Hop Hor *.
progress unfold rngl_sub.
rewrite Hop.
apply (rngl_add_lt_mono_r Hop Hor).
Qed.

Theorem rngl_add_le_mono_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (b ≤ c ↔ a + b ≤ a + c)%L.
Proof.
intros Hop Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hbc. {
  apply (rngl_add_le_compat Hor); [ apply (rngl_le_refl Hor) | easy ].
}
apply (rngl_sub_le_mono_r Hop Hor) with (c := a) in Hbc.
now do 2 rewrite rngl_add_comm, (rngl_add_sub Hos) in Hbc.
Qed.

Theorem rngl_add_le_mono_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a ≤ b ↔ a + c ≤ b + c)%L.
Proof.
intros Hop Hor *.
do 2 rewrite (rngl_add_comm _ c).
apply (rngl_add_le_mono_l Hop Hor).
Qed.

Theorem rngl_le_sub_le_add_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a - b ≤ c ↔ a ≤ b + c)%L.
Proof.
intros Hop Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Habc. {
  apply (rngl_sub_le_mono_r Hop Hor _ _ b).
  now rewrite rngl_add_comm, (rngl_add_sub Hos).
} {
  apply (rngl_sub_le_mono_r Hop Hor _ _ b) in Habc.
  now rewrite rngl_add_comm, (rngl_add_sub Hos) in Habc.
}
Qed.

Theorem rngl_le_sub_le_add_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a - b ≤ c ↔ a ≤ c + b)%L.
Proof.
intros Hop Hor *.
rewrite rngl_add_comm.
apply (rngl_le_sub_le_add_l Hop Hor).
Qed.

Theorem rngl_lt_sub_lt_add_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a - b < c ↔ a < b + c)%L.
Proof.
intros Hop Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Habc. {
  apply (rngl_sub_lt_mono_r Hop Hor _ _ b).
  now rewrite rngl_add_comm, (rngl_add_sub Hos).
} {
  apply (rngl_sub_lt_mono_r Hop Hor _ _ b) in Habc.
  now rewrite rngl_add_comm, (rngl_add_sub Hos) in Habc.
}
Qed.

Theorem rngl_lt_sub_lt_add_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a - b < c ↔ a < c + b)%L.
Proof.
intros Hop Hor *.
rewrite rngl_add_comm.
apply (rngl_lt_sub_lt_add_l Hop Hor).
Qed.

Theorem rngl_sub_le_compat :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (a ≤ b → c ≤ d → a - d ≤ b - c)%L.
Proof.
intros Hop Hor * Hab Hcd.
apply (rngl_le_sub_le_add_l Hop Hor).
rewrite (rngl_add_sub_assoc Hop).
apply (rngl_le_add_le_sub_l Hop Hor).
now apply (rngl_add_le_compat Hor).
Qed.

Theorem rngl_add_lt_compat :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (a < b → c < d → a + c < b + d)%L.
Proof.
intros Hop Hor * Hab Hcd.
apply (rngl_lt_trans Hor _ (a + d)%L). {
  now apply (rngl_add_lt_mono_l Hop Hor).
} {
  now apply (rngl_add_lt_mono_r Hop Hor).
}
Qed.

Theorem rngl_add_le_lt_mono :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (a ≤ b)%L → (c < d)%L → (a + c < b + d)%L.
Proof.
intros Hop Hor * Hab Hcd.
apply (rngl_lt_le_trans Hor _ (a + d))%L.
now apply (rngl_add_lt_mono_l Hop Hor).
now apply (rngl_add_le_mono_r Hop Hor).
Qed.

Theorem rngl_add_lt_le_mono :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (a < b)%L → (c ≤ d)%L → (a + c < b + d)%L.
Proof.
intros Hop Hor * Hab Hcd.
apply (rngl_lt_le_trans Hor _ (b + c))%L.
now apply (rngl_add_lt_mono_r Hop Hor).
now apply (rngl_add_le_mono_l Hop Hor).
Qed.

Theorem rngl_lt_sub_0 :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a - b < 0 ↔ a < b)%L.
Proof.
intros Hop Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_add_lt_le_mono Hop Hor) as H1.
split; intros Hab. {
  specialize (H1 (a - b) 0 b b Hab (rngl_le_refl Hor _))%L.
  rewrite (rngl_sub_add Hop) in H1.
  now rewrite rngl_add_0_l in H1.
} {
  specialize (H1 a b (- b) (- b) Hab (rngl_le_refl Hor _))%L.
  do 2 rewrite (rngl_add_opp_r Hop) in H1.
  now rewrite (rngl_sub_diag Hos) in H1.
}
Qed.

Theorem rngl_le_add_l :
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → b ≤ a + b)%L.
Proof.
intros Hor * Hbz.
remember (a + b)%L as c.
rewrite <- (rngl_add_0_l b); subst c.
apply (rngl_add_le_compat Hor); [ easy | apply (rngl_le_refl Hor) ].
Qed.

Theorem rngl_le_add_r :
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ b → a ≤ a + b)%L.
Proof.
intros Hor * Hbz.
rewrite rngl_add_comm.
now apply (rngl_le_add_l Hor).
Qed.

Theorem rngl_lt_add_l :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < a)%L → (b < a + b)%L.
Proof.
intros Hos Hor * Hbz.
apply (rngl_lt_iff Hor).
split; [ now apply (rngl_le_add_l Hor), (rngl_lt_le_incl Hor) | ].
intros H.
symmetry in H.
apply (rngl_add_sub_eq_r Hos) in H.
rewrite (rngl_sub_diag Hos) in H; subst a.
revert Hbz.
apply (rngl_lt_irrefl Hor).
Qed.

Theorem rngl_lt_add_r :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < b)%L → (a < a + b)%L.
Proof.
intros Hos Hor * Hbz.
rewrite rngl_add_comm.
now apply (rngl_lt_add_l Hos Hor).
Qed.

Theorem rngl_le_sub_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ b ↔ a - b ≤ a)%L.
Proof.
intros Hop Hor *.
split; intros Hb. {
  apply (rngl_le_sub_le_add_r Hop Hor).
  now apply (rngl_le_add_r Hor).
} {
  apply (rngl_le_sub_le_add_l Hop Hor) in Hb.
  apply (rngl_add_le_mono_r Hop Hor _ _ a).
  now rewrite rngl_add_0_l.
}
Qed.

Theorem rngl_lt_add_lt_sub_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a + b < c ↔ b < c - a)%L.
Proof.
intros Hop Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
rewrite rngl_add_comm.
split; intros Hab. {
  apply (rngl_sub_lt_mono_r Hop Hor _ _ a) in Hab.
  now rewrite (rngl_add_sub Hos) in Hab.
} {
  apply (rngl_sub_lt_mono_r Hop Hor _ _ a).
  now rewrite (rngl_add_sub Hos).
}
Qed.

Theorem rngl_lt_add_lt_sub_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a + b < c ↔ a < c - b)%L.
Proof.
intros Hop Hor *.
rewrite rngl_add_comm.
apply (rngl_lt_add_lt_sub_l Hop Hor).
Qed.

Theorem rngl_le_opp_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (- a ≤ b ↔ 0 ≤ a + b)%L.
Proof.
intros Hop Hor *.
rewrite <- (rngl_sub_0_l Hop).
split; intros Hab.
now apply (rngl_le_sub_le_add_l Hop Hor) in Hab.
now apply (rngl_le_sub_le_add_l Hop Hor) in Hab.
Qed.

Theorem rngl_le_opp_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ - b ↔ a + b ≤ 0)%L.
Proof.
intros Hop Hor *.
rewrite <- (rngl_sub_0_l Hop).
split; intros Hab.
now apply (rngl_le_add_le_sub_r Hop Hor) in Hab.
now apply (rngl_le_add_le_sub_r Hop Hor) in Hab.
Qed.

Theorem rngl_lt_opp_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (- a < b ↔ 0 < a + b)%L.
Proof.
intros Hop Hor *.
rewrite <- (rngl_sub_0_l Hop).
split; intros Hab.
now apply (rngl_lt_sub_lt_add_l Hop Hor) in Hab.
now apply (rngl_lt_sub_lt_add_l Hop Hor) in Hab.
Qed.

Theorem rngl_lt_opp_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a < - b ↔ a + b < 0)%L.
Proof.
intros Hop Hor *.
rewrite <- (rngl_sub_0_l Hop).
split; intros Hab.
now apply (rngl_lt_add_lt_sub_r Hop Hor) in Hab.
now apply (rngl_lt_add_lt_sub_r Hop Hor) in Hab.
Qed.

Theorem rngl_add_nonneg_nonneg :
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → 0 ≤ b → 0 ≤ a + b)%L.
Proof.
intros Hor * Ha Hb.
apply (rngl_le_trans Hor _ a); [ easy | ].
now apply (rngl_le_add_r Hor).
Qed.

Theorem rngl_add_pos_nonneg :
  rngl_is_ordered T = true →
  ∀ a b, (0 < a)%L → (0 ≤ b)%L → (0 < a + b)%L.
Proof.
intros Hor * Hza Hzb.
apply (rngl_lt_le_trans Hor _ a); [ easy | ].
now apply (rngl_le_add_r Hor).
Qed.

Theorem rngl_add_nonneg_pos :
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a)%L → (0 < b)%L → (0 < a + b)%L.
Proof.
intros Hor * Hza Hzb.
rewrite rngl_add_comm.
now apply (rngl_add_pos_nonneg Hor).
Qed.

Theorem rngl_add_nonpos_nonpos :
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ 0 → b ≤ 0 → a + b ≤ 0)%L.
Proof.
intros Hor * Ha Hb.
apply (rngl_le_trans Hor _ a); [ | easy ].
rewrite <- rngl_add_0_r.
apply (rngl_add_le_compat Hor); [ | easy ].
apply (rngl_le_refl Hor).
Qed.

Theorem rngl_mul_nat_inj_le :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 < a)%L → ∀ i j, i ≤ j ↔ (rngl_mul_nat a i ≤ rngl_mul_nat a j)%L.
Proof.
intros Hop Hor * Haz *.
progress unfold rngl_mul_nat.
progress unfold mul_nat.
revert j.
induction i; intros; cbn. {
  split; [ | intros; apply Nat.le_0_l ].
  intros H; clear H.
  induction j; [ apply (rngl_le_refl Hor) | cbn ].
  eapply (rngl_le_trans Hor); [ apply IHj | ].
  now apply (rngl_le_add_l Hor), (rngl_lt_le_incl Hor).
}
destruct j. {
  split; [ easy | cbn ].
  intros H; exfalso.
  apply (rngl_nlt_ge Hor) in H; apply H; clear H.
  eapply (rngl_lt_le_trans Hor); [ apply Haz | ].
  apply (rngl_le_add_r Hor).
  clear IHi.
  induction i; [ apply (rngl_le_refl Hor) | cbn ].
  eapply (rngl_le_trans Hor); [ apply IHi | ].
  now apply (rngl_le_add_l Hor), (rngl_lt_le_incl Hor).
}
cbn.
split; intros Hij. {
  apply Nat.succ_le_mono in Hij.
  apply (rngl_add_le_compat Hor); [ apply (rngl_le_refl Hor) | ].
  now apply IHi.
} {
  apply -> Nat.succ_le_mono.
  apply (rngl_add_le_mono_l Hop Hor) in Hij.
  now apply IHi.
}
Qed.

Theorem rngl_mul_nat_inj_lt :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 < a)%L → ∀ i j, i < j ↔ (rngl_mul_nat a i < rngl_mul_nat a j)%L.
Proof.
intros Hop Hor * Haz *.
progress unfold rngl_mul_nat.
progress unfold mul_nat.
revert j.
induction i; intros; cbn. {
  split; intros Hj. 2: {
    destruct j; [ | apply Nat.lt_0_succ ].
    now apply (rngl_lt_irrefl Hor) in Hj.
  }
  induction j; [ easy | clear Hj ].
  cbn.
  apply (rngl_lt_le_trans Hor _ a); [ easy | ].
  apply (rngl_le_add_r Hor).
  destruct j; [ apply (rngl_le_refl Hor) | ].
  apply (rngl_lt_le_incl Hor), IHj.
  apply Nat.lt_0_succ.
}
destruct j. {
  split; [ easy | cbn ].
  intros H; exfalso.
  apply (rngl_nle_gt Hor) in H; apply H; clear H.
  eapply (rngl_le_trans Hor); [ apply (rngl_lt_le_incl Hor), Haz | ].
  apply (rngl_le_add_r Hor).
  clear IHi.
  induction i; [ apply (rngl_le_refl Hor) | cbn ].
  eapply (rngl_le_trans Hor); [ apply IHi | ].
  now apply (rngl_le_add_l Hor), (rngl_lt_le_incl Hor).
}
cbn.
split; intros Hij. {
  apply Nat.succ_lt_mono in Hij.
  apply (rngl_add_lt_mono_l Hop Hor).
  now apply IHi.
} {
  apply -> Nat.succ_lt_mono.
  apply (rngl_add_lt_mono_l Hop Hor) in Hij.
  now apply IHi.
}
Qed.

Theorem rngl_abs_0 :
  rngl_has_opp T = true →
  rngl_abs 0%L = 0%L.
Proof.
intros Hop.
progress unfold rngl_abs.
rewrite (rngl_opp_0 Hop).
now destruct (0 ≤? 0)%L.
Qed.

Theorem eq_rngl_abs_0 :
  rngl_has_opp T = true →
  ∀ a, rngl_abs a = 0%L → a = 0%L.
Proof.
intros Hop * Ha.
progress unfold rngl_abs in Ha.
destruct (a ≤? 0)%L; [ | easy ].
rewrite <- (rngl_opp_0 Hop) in Ha.
now apply (rngl_opp_inj Hop) in Ha.
Qed.

Theorem rngl_abs_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ rngl_abs a)%L.
Proof.
intros Hop Hor *.
progress unfold rngl_abs.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
destruct az. {
  apply rngl_leb_le in Haz.
  apply (rngl_opp_le_compat Hop Hor) in Haz.
  now rewrite (rngl_opp_0 Hop) in Haz.
} {
  apply (rngl_leb_gt Hor) in Haz.
  now apply (rngl_lt_le_incl Hor).
}
Qed.

Theorem rngl_abs_le :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ x y, (- x ≤ y ≤ x ↔ rngl_abs y ≤ x)%L.
Proof.
intros * Hop Hor *.
progress unfold rngl_abs.
split. {
  intros (Hxy, Hyx).
  remember (y ≤? 0)%L as yz eqn:Hyz; symmetry in Hyz.
  destruct yz; [ | easy ].
  apply (rngl_opp_le_compat Hop Hor).
  now rewrite (rngl_opp_involutive Hop).
} {
  intros Hyx.
  remember (y ≤? 0)%L as yz eqn:Hyz; symmetry in Hyz.
  destruct yz. {
    apply rngl_leb_le in Hyz.
    split. {
      apply (rngl_opp_le_compat Hop Hor) in Hyx.
      now rewrite (rngl_opp_involutive Hop) in Hyx.
    } {
      apply (rngl_le_trans Hor _ 0%L); [ easy | ].
      apply (rngl_le_trans Hor _ (- y)%L); [ | easy ].
      apply (rngl_le_0_sub Hop Hor) in Hyz.
      progress unfold rngl_sub in Hyz.
      rewrite Hop in Hyz.
      now rewrite rngl_add_0_l in Hyz.
    }
  }
  split; [ | easy ].
  apply (rngl_leb_gt Hor) in Hyz.
  apply (rngl_lt_le_incl Hor).
  apply (rngl_le_lt_trans Hor _ 0)%L; [ | easy ].
  rewrite <- (rngl_opp_0 Hop).
  apply -> (rngl_opp_le_compat Hop Hor).
  apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_trans Hor _ y)%L.
}
Qed.

Theorem rngl_abs_lt :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ x y, (- x < y < x ↔ rngl_abs y < x)%L.
Proof.
intros * Hop Hor *.
progress unfold rngl_abs.
split. {
  intros (Hxy, Hyx).
  remember (y ≤? 0)%L as yz eqn:Hyz; symmetry in Hyz.
  destruct yz; [ | easy ].
  apply (rngl_opp_lt_compat Hop Hor).
  now rewrite (rngl_opp_involutive Hop).
} {
  intros Hyx.
  remember (y ≤? 0)%L as yz eqn:Hyz; symmetry in Hyz.
  destruct yz. {
    apply rngl_leb_le in Hyz.
    split. {
      apply (rngl_opp_lt_compat Hop Hor) in Hyx.
      now rewrite (rngl_opp_involutive Hop) in Hyx.
    } {
      apply (rngl_le_lt_trans Hor _ 0%L); [ easy | ].
      apply (rngl_le_lt_trans Hor _ (- y)%L); [ | easy ].
      apply (rngl_le_0_sub Hop Hor) in Hyz.
      progress unfold rngl_sub in Hyz.
      rewrite Hop in Hyz.
      now rewrite rngl_add_0_l in Hyz.
    }
  }
  split; [ | easy ].
  apply (rngl_leb_gt Hor) in Hyz.
  apply (rngl_le_lt_trans Hor _ 0)%L; [ | easy ].
  rewrite <- (rngl_opp_0 Hop).
  apply -> (rngl_opp_le_compat Hop Hor).
  apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_trans Hor _ y)%L.
}
Qed.

Theorem rngl_abs_opp :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, rngl_abs (- a)%L = rngl_abs a.
Proof.
intros Hop Hor *.
progress unfold rngl_abs.
remember (- a ≤? 0)%L as c eqn:Hc; symmetry in Hc.
remember (a ≤? 0)%L as d eqn:Hd; symmetry in Hd.
destruct c. {
  apply rngl_leb_le in Hc.
  rewrite (rngl_opp_involutive Hop).
  rewrite <- (rngl_opp_0 Hop) in Hc.
  apply (rngl_opp_le_compat Hop Hor) in Hc.
  destruct d; [ | easy ].
  apply rngl_leb_le in Hd.
  apply (rngl_le_antisymm Hor) in Hd; [ | easy ].
  subst a.
  symmetry; apply (rngl_opp_0 Hop).
} {
  apply (rngl_leb_gt Hor) in Hc.
  rewrite <- (rngl_opp_0 Hop) in Hc.
  apply (rngl_opp_lt_compat Hop Hor) in Hc.
  destruct d; [ easy | ].
  apply (rngl_leb_gt Hor) in Hd.
  now apply (rngl_lt_asymm Hor) in Hd.
}
Qed.

Theorem rngl_abs_sub_comm :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, rngl_abs (a - b)%L = rngl_abs (b - a)%L.
Proof.
intros Hop Hor *.
rewrite <- (rngl_abs_opp Hop Hor).
now rewrite (rngl_opp_sub_distr Hop).
Qed.

Theorem rngl_abs_nonneg_eq :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ a)%L → rngl_abs a = a.
Proof.
intros Hop Hor * Hza.
progress unfold rngl_abs.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
destruct az; [ | easy ].
apply rngl_leb_le in Haz.
apply (rngl_le_antisymm Hor _ _ Hza) in Haz.
subst a.
apply (rngl_opp_0 Hop).
Qed.

Theorem rngl_abs_nonpos_eq :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a : T, (a ≤ 0)%L → rngl_abs a = (- a)%L.
Proof.
intros Hop Hor * Haz.
rewrite <- (rngl_opp_involutive Hop a) at 1.
rewrite (rngl_abs_opp Hop Hor).
apply (rngl_abs_nonneg_eq Hop Hor).
rewrite <- (rngl_opp_0 Hop).
now apply -> (rngl_opp_le_compat Hop Hor).
Qed.

Theorem rngl_abs_pos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ x, (x ≠ 0 → 0 < rngl_abs x)%L.
Proof.
intros Hop Hor * Hxz.
apply (rngl_lt_iff Hor).
split. 2: {
  apply not_eq_sym.
  intros H; apply Hxz; clear Hxz.
  progress unfold rngl_abs in H.
  remember (x ≤? 0)%L as xz eqn:Hxz; symmetry in Hxz.
  destruct xz; [ | easy ].
  apply (f_equal rngl_opp) in H.
  rewrite (rngl_opp_involutive Hop) in H.
  now rewrite (rngl_opp_0 Hop) in H.
}
apply (rngl_abs_nonneg Hop Hor).
Qed.

Theorem rngl_abs_triangle :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (rngl_abs (a + b) ≤ rngl_abs a + rngl_abs b)%L.
Proof.
intros Hop Hor *.
progress unfold rngl_abs.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
remember (b ≤? 0)%L as bz eqn:Hbz; symmetry in Hbz.
remember (a + b ≤? 0)%L as abz eqn:Habz; symmetry in Habz.
destruct abz. {
  apply rngl_leb_le in Habz.
  destruct az. {
    apply rngl_leb_le in Haz.
    rewrite (rngl_opp_add_distr Hop).
    progress unfold rngl_sub.
    rewrite Hop.
    rewrite rngl_add_comm.
    apply (rngl_add_le_compat Hor); [ apply (rngl_le_refl Hor) | ].
    destruct bz; [ apply (rngl_le_refl Hor) | ].
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_lt_le_incl Hor).
    apply (rngl_lt_trans Hor _ 0)%L; [ | easy ].
    rewrite <- (rngl_opp_0 Hop).
    now apply -> (rngl_opp_lt_compat Hop Hor).
  }
  apply (rngl_leb_gt Hor) in Haz.
  destruct bz. {
    rewrite rngl_add_comm.
    rewrite (rngl_opp_add_distr Hop).
    progress unfold rngl_sub.
    rewrite Hop.
    apply (rngl_add_le_compat Hor); [ | apply (rngl_le_refl Hor) ].
    apply (rngl_lt_le_incl Hor).
    apply (rngl_lt_trans Hor _ 0)%L; [ | easy ].
    rewrite <- (rngl_opp_0 Hop).
    now apply -> (rngl_opp_lt_compat Hop Hor).
  }
  apply (rngl_leb_gt Hor) in Hbz.
  apply (rngl_nlt_ge Hor) in Habz.
  exfalso; apply Habz; clear Habz.
  apply (rngl_lt_le_trans Hor _ a); [ easy | ].
  apply (rngl_le_add_r Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_leb_gt Hor) in Habz.
destruct az. {
  apply rngl_leb_le in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    apply (rngl_nle_gt Hor) in Habz.
    exfalso; apply Habz; clear Habz.
    rewrite <- rngl_add_0_r.
    now apply (rngl_add_le_compat Hor).
  }
  apply (rngl_add_le_compat Hor); [ | apply (rngl_le_refl Hor) ].
  apply (rngl_le_trans Hor _ 0)%L; [ easy | ].
  apply (rngl_opp_le_compat Hop Hor).
  rewrite (rngl_opp_involutive Hop).
  now rewrite (rngl_opp_0 Hop).
}
apply (rngl_leb_gt Hor) in Haz.
apply (rngl_add_le_compat Hor); [ apply (rngl_le_refl Hor) | ].
destruct bz; [ | apply (rngl_le_refl Hor) ].
apply rngl_leb_le in Hbz.
apply (rngl_le_trans Hor _ 0)%L; [ easy | ].
apply (rngl_opp_le_compat Hop Hor).
rewrite (rngl_opp_involutive Hop).
now rewrite (rngl_opp_0 Hop).
Qed.

Theorem rngl_le_abs :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (a ≤ rngl_abs a)%L.
Proof.
intros Hop Hor *.
progress unfold rngl_abs.
remember (a ≤? 0)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ | apply (rngl_le_refl Hor) ].
apply rngl_leb_le in Hc.
apply (rngl_le_sub_0 Hop Hor).
rewrite (rngl_sub_opp_r Hop).
rewrite <- (rngl_add_0_l 0%L).
now apply (rngl_add_le_compat Hor).
Qed.

Theorem rngl_add_neg_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a < 0)%L → (b ≤ 0)%L → (a + b < 0)%L.
Proof.
intros Hop Hor * Haz Hbz.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
eapply (rngl_lt_le_trans Hor); [ | apply Hbz ].
apply (rngl_lt_add_lt_sub_r Hop Hor).
now rewrite (rngl_sub_diag Hos).
Qed.

Theorem rngl_add_nonpos_neg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ 0)%L → (b < 0)%L → (a + b < 0)%L.
Proof.
intros Hop Hor * Haz Hbz.
rewrite rngl_add_comm.
now apply (rngl_add_neg_nonpos Hop Hor).
Qed.

Theorem rngl_leb_opp_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (-a ≤? b)%L = (-b ≤? a)%L.
Proof.
intros Hop Hor *.
remember (-a ≤? b)%L as ab eqn:Hab.
symmetry in Hab.
symmetry.
destruct ab. {
  apply rngl_leb_le in Hab.
  apply rngl_leb_le.
  apply (rngl_le_opp_l Hop Hor) in Hab.
  rewrite rngl_add_comm in Hab.
  now apply (rngl_le_opp_l Hop Hor) in Hab.
} {
  apply (rngl_leb_gt Hor) in Hab.
  apply (rngl_leb_gt Hor).
  apply (rngl_lt_opp_r Hop Hor).
  rewrite rngl_add_comm.
  now apply (rngl_lt_opp_r Hop Hor).
}
Qed.

Theorem rngl_leb_opp_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤? -b)%L = (b ≤? -a)%L.
Proof.
intros Hop Hor *.
remember (a ≤? -b)%L as ab eqn:Hab.
symmetry in Hab.
symmetry.
destruct ab. {
  apply rngl_leb_le in Hab.
  apply rngl_leb_le.
  apply (rngl_le_opp_r Hop Hor) in Hab.
  rewrite rngl_add_comm in Hab.
  now apply (rngl_le_opp_r Hop Hor) in Hab.
} {
  apply (rngl_leb_gt Hor) in Hab.
  apply (rngl_leb_gt Hor).
  apply (rngl_lt_opp_l Hop Hor).
  rewrite rngl_add_comm.
  now apply (rngl_lt_opp_l Hop Hor).
}
Qed.

Theorem rngl_leb_0_opp :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤? - a)%L = (a ≤? 0)%L.
Proof.
intros Hop Hor *.
rewrite (rngl_leb_opp_r Hop Hor).
now rewrite (rngl_opp_0 Hop).
Qed.

Theorem rngl_ltb_opp_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (-a <? b)%L = (-b <? a)%L.
Proof.
intros Hop Hor *.
remember (-a <? b)%L as ab eqn:Hab.
symmetry in Hab.
symmetry.
destruct ab. {
  apply rngl_ltb_lt in Hab.
  apply rngl_ltb_lt.
  apply (rngl_lt_opp_l Hop Hor) in Hab.
  rewrite rngl_add_comm in Hab.
  now apply (rngl_lt_opp_l Hop Hor) in Hab.
} {
  apply (rngl_ltb_ge Hor) in Hab.
  apply (rngl_ltb_ge Hor).
  apply (rngl_le_opp_r Hop Hor).
  rewrite rngl_add_comm.
  now apply (rngl_le_opp_r Hop Hor).
}
Qed.

Theorem rngl_ltb_opp_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a <? -b)%L = (b <? -a)%L.
Proof.
intros Hop Hor *.
remember (a <? -b)%L as ab eqn:Hab.
symmetry in Hab.
symmetry.
destruct ab. {
  apply rngl_ltb_lt in Hab.
  apply rngl_ltb_lt.
  apply (rngl_lt_opp_r Hop Hor) in Hab.
  rewrite rngl_add_comm in Hab.
  now apply (rngl_lt_opp_r Hop Hor) in Hab.
} {
  apply (rngl_ltb_ge Hor) in Hab.
  apply (rngl_ltb_ge Hor).
  apply (rngl_le_opp_l Hop Hor).
  rewrite rngl_add_comm.
  now apply (rngl_le_opp_l Hop Hor).
}
Qed.

Theorem rngl_archimedean_ub :
  rngl_is_archimedean T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < a < b)%L →
  ∃ n : nat, (rngl_mul_nat a n ≤ b < rngl_mul_nat a (n + 1))%L.
Proof.
intros Har Hor * (Ha, Hab).
specialize rngl_opt_archimedean as H1.
rewrite Har, Hor in H1; cbn in H1.
specialize (H1 a b Ha).
destruct H1 as (m, Hm).
induction m. {
  exfalso; cbn in Hm.
  apply (rngl_nle_gt Hor) in Hm.
  apply Hm; clear Hm.
  now apply (rngl_le_trans Hor _ a); apply (rngl_lt_le_incl Hor).
}
destruct (rngl_le_dec Hor (rngl_mul_nat a m) b) as [Hba| Hba]. {
  now exists m; rewrite Nat.add_1_r.
}
apply (rngl_nle_gt Hor) in Hba.
now apply IHm.
Qed.

Theorem rngl_archimedean :
  rngl_is_archimedean T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 < a)%L → ∃ n, (b < rngl_mul_nat a n)%L.
Proof.
intros Har Hor.
specialize rngl_opt_archimedean as H1.
now rewrite Har, Hor in H1.
Qed.

Theorem rngl_add_opp_diag_r :
  rngl_has_opp T = true →
  ∀ x : T, (x + - x)%L = 0%L.
Proof.
intros Hop *.
rewrite (rngl_add_opp_r Hop).
apply rngl_sub_diag.
now apply rngl_has_opp_or_subt_iff; left.
Qed.

Arguments rngl_mul_nat {T ro} a%_L n%_nat.

Theorem rngl_of_nat_0 : rngl_of_nat 0 = 0%L.
Proof. easy. Qed.

Theorem fold_rngl_mul_nat :
  ∀ a n, List.fold_right rngl_add 0%L (List.repeat a n)%L = rngl_mul_nat a n.
Proof. easy. Qed.

End a.

Section b.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem rngl_characteristic_0 :
  rngl_has_1 T = true →
  rngl_characteristic T = 0 →
  ∀ i : nat, rngl_of_nat (S i) ≠ 0%L.
Proof.
intros Hon Hcz.
specialize (rngl_opt_characteristic_prop) as H1.
now rewrite Hon, Hcz in H1.
Qed.

Theorem rngl_characteristic_non_0 :
  rngl_has_1 T = true →
  rngl_characteristic T ≠ 0 →
  (∀ i : nat, 0 < i < rngl_characteristic T → rngl_of_nat i ≠ 0%L) ∧
  rngl_of_nat (rngl_characteristic T) = 0%L.
Proof.
intros Hon Hcz.
specialize (rngl_opt_characteristic_prop) as H1.
apply Nat.eqb_neq in Hcz.
now rewrite Hon, Hcz in H1.
Qed.

Theorem rngl_1_neq_0_iff :
  rngl_has_1 T = true → rngl_characteristic T ≠ 1 ↔ (1 ≠ 0)%L.
Proof.
intros Hon.
specialize rngl_opt_characteristic_prop as H1.
rewrite Hon in H1.
split. {
  intros Hc.
  remember (Nat.eqb (rngl_characteristic T) 0) as cz eqn:Hcz; symmetry in Hcz.
  destruct cz. {
    specialize (H1 0); cbn in H1.
    now rewrite rngl_add_0_r in H1.
  }
  destruct H1 as (Hbef, H1).
  destruct rngl_characteristic as [| n]; [ easy | ].
  destruct n; [ easy | ].
  specialize (Hbef 1).
  cbn in Hbef.
  rewrite rngl_add_0_r in Hbef.
  apply Hbef.
  unfold lt.
  split; [ easy | ].
  do 2 apply le_n_S.
  destruct n; [ easy | apply le_0_n ].
} {
  intros H10 Hc.
  rewrite Hc in H1; cbn in H1.
  now rewrite rngl_add_0_r in H1.
}
Qed.

Theorem eq_rngl_of_nat_0 :
  rngl_has_1 T = true →
  rngl_characteristic T = 0 →
  ∀ i, rngl_of_nat i = 0%L → i = 0.
Proof.
intros Hon Hch * Hi.
destruct i; [ easy | exfalso ].
cbn in Hi.
specialize (rngl_characteristic_0 Hon Hch) as H1.
now specialize (H1 i) as H.
Qed.

Theorem rngl_of_nat_inj :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_characteristic T = 0 →
  ∀ i j,
  rngl_of_nat i = rngl_of_nat j
  → i = j.
Proof.
intros Hon Hom Hch * Hij.
revert i Hij.
induction j; intros. {
  cbn in Hij.
  now apply eq_rngl_of_nat_0 in Hij.
}
destruct i. {
  exfalso.
  symmetry in Hij.
  now apply eq_rngl_of_nat_0 in Hij.
}
f_equal.
cbn in Hij.
apply rngl_add_cancel_l in Hij; [ | easy ].
now apply IHj.
Qed.

End b.

Arguments rngl_abs {T ro} a%_L.
Arguments rngl_abs_nonneg_eq {T ro rp} Hop Hor a%_L.
Arguments rngl_add {T ring_like_op} (a b)%_L.
Arguments rngl_add_comm {T ro ring_like_prop} (a b)%_L.
Arguments rngl_add_sub {T ro rp} Hom (a b)%_L.
Arguments rngl_eq_dec {T ro} Hed (a b)%_L.
Arguments rngl_le_add_r {T ro rp} Hor (a b)%_L Hb.
Arguments rngl_le_dec {T ro rp} Hor (a b)%_L.
Arguments rngl_le_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_le_lt_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_lt_le_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_lt_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_lt_dec {T ro rp} Hor (a b)%_L.
Arguments rngl_min {T ro} (a b)%_L.
Arguments rngl_mul {T ring_like_op} (a b)%_L.
Arguments rngl_mul_nat {T ro} a%_L n%_nat.
Arguments rngl_squ {T ro} x%_L.
Arguments rngl_sub {T ro} (a b)%_L.
Arguments rngl_subt {T ro} (a b)%_L.
