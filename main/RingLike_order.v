Require Import Utf8.
Require Import RingLike_structures.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem rngl_leb_le :
  ∀ a b, (a ≤? b)%L = true ↔ (a ≤ b)%L.
Proof.
intros.
progress unfold rngl_leb.
progress unfold rngl_le.
now split; intros Hab; destruct rngl_opt_leb.
Qed.

Theorem rngl_ltb_lt :
  ∀ a b, (a <? b)%L = true ↔ (a < b)%L.
Proof.
intros.
progress unfold rngl_ltb.
progress unfold rngl_lt.
split; intros Hab. {
  destruct rngl_opt_leb; [ | easy ].
  now apply Bool.negb_true_iff.
} {
  destruct rngl_opt_leb; [ | easy ].
  now apply Bool.negb_true_iff.
}
Qed.

Theorem rngl_leb_nle :
  ∀ a b, (a ≤? b)%L = false ↔ ¬ (a ≤ b)%L.
Proof.
intros.
progress unfold rngl_leb.
progress unfold rngl_le.
split; intros Hab. {
  apply Bool.not_true_iff_false in Hab.
  now destruct rngl_opt_leb.
} {
  apply Bool.not_true_iff_false.
  now destruct rngl_opt_leb.
}
Qed.

Theorem rngl_ltb_nlt :
  ∀ a b, (a <? b)%L = false ↔ ¬ (a < b)%L.
Proof.
intros.
progress unfold rngl_ltb.
progress unfold rngl_lt.
split; intros Hab. {
  destruct rngl_opt_leb; [ | easy ].
  apply Bool.negb_false_iff in Hab.
  apply Bool.not_false_iff_true.
  easy.
} {
  destruct rngl_opt_leb; [ | easy ].
  apply Bool.negb_false_iff.
  apply Bool.not_false_iff_true in Hab.
  easy.
}
Qed.

Theorem rngl_le_dec :
  rngl_is_ordered T = true →
  ∀ a b : T, ({a ≤ b} + {¬ a ≤ b})%L.
Proof.
intros Hor *.
specialize rngl_opt_ord as H.
rewrite Hor in H.
apply H.
Qed.

Theorem rngl_le_refl :
  rngl_is_ordered T = true →
  ∀ a, (a ≤ a)%L.
Proof.
intros Hor *.
specialize rngl_opt_ord as H.
rewrite Hor in H.
apply H.
Qed.

Theorem rngl_leb_refl :
  rngl_is_ordered T = true →
  ∀ a, (a ≤? a)%L = true.
Proof.
intros Hor *.
apply rngl_leb_le.
apply (rngl_le_refl Hor).
Qed.

Theorem rngl_le_antisymm :
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ b → b ≤ a → a = b)%L.
Proof.
intros Hor *.
specialize rngl_opt_ord as H.
rewrite Hor in H.
apply H.
Qed.

Theorem rngl_le_trans :
  rngl_is_ordered T = true →
   ∀ a b c : T, (a ≤ b)%L → (b ≤ c)%L → (a ≤ c)%L.
Proof.
intros Hor *.
specialize rngl_opt_ord as H.
rewrite Hor in H.
apply H.
Qed.

Theorem rngl_le_iff_leb_eq :
  ∀ a b c d,
  (a ≤ b ↔ c ≤ d)%L
  → ((a ≤? b) = (c ≤? d))%L.
Proof.
intros * Habcd.
remember (a ≤? b)%L as ab eqn:Hab.
remember (c ≤? d)%L as cd eqn:Hcd.
symmetry in Hab, Hcd.
destruct ab. {
  destruct cd; [ easy | ].
  apply rngl_leb_le in Hab.
  apply rngl_leb_nle in Hcd.
  exfalso; apply Hcd.
  apply Habcd, Hab.
} {
  destruct cd; [ | easy ].
  apply rngl_leb_nle in Hab.
  apply rngl_leb_le in Hcd.
  exfalso; apply Hab.
  apply Habcd, Hcd.
}
Qed.

Theorem rngl_lt_iff :
  rngl_is_ordered T = true → ∀ a b, (a < b ↔ a ≤ b ∧ a ≠ b)%L.
Proof.
intros * Hor a b.
progress unfold rngl_lt.
progress unfold rngl_le.
specialize rngl_opt_ord as rr.
rewrite Hor in rr.
move rr after rp.
specialize rngl_ord_not_le as H1.
specialize (rngl_le_antisymm Hor) as H2.
progress unfold rngl_le in H1.
progress unfold rngl_le in H2.
destruct rngl_opt_leb as [rngl_leb| ]; [ | easy ].
split. {
  intros Hab.
  specialize (H1 b a) as H3.
  rewrite Hab in H3.
  assert (H : false ≠ true) by easy.
  specialize (H3 H); clear H.
  split; [ easy | ].
  destruct H3; congruence.
} {
  intros (H3, H4).
  remember (rngl_leb b a) as x eqn:Hx; symmetry in Hx.
  destruct x; [ | easy ].
  now specialize (H2 _ _ H3 Hx).
}
Qed.

Theorem rngl_lt_eq_cases :
  rngl_is_ordered T = true → ∀ a b : T, (a ≤ b)%L ↔ (a < b)%L ∨ a = b.
Proof.
intros Hor *.
progress unfold rngl_lt.
progress unfold rngl_le.
specialize rngl_opt_ord as rr.
rewrite Hor in rr.
move rr after rp.
specialize rngl_ord_not_le as H1.
specialize (rngl_le_antisymm Hor) as H2.
specialize (rngl_le_refl Hor) as H3.
progress unfold rngl_le in H1.
progress unfold rngl_le in H2.
progress unfold rngl_le in H3.
destruct rngl_opt_leb as [rngl_leb| ]; [ | easy ].
split. {
  intros H.
  remember (rngl_leb b a) as ba eqn:Hba; symmetry in Hba.
  destruct ba; [ | now left ].
  now specialize (H2 _ _ H Hba); right.
} {
  intros H.
  destruct H as [H4| H4]; [ now apply H1; rewrite H4 | ].
  subst b; apply H3.
}
Qed.

Theorem rngl_lt_dec :
  rngl_is_ordered T = true →
  ∀ a b : T, ({a < b} + {¬ a < b})%L.
Proof.
intros Hor *.
specialize rngl_opt_ord as rr.
rewrite Hor in rr.
move rr after rp.
specialize rngl_ord_le_dec as H1.
destruct (H1 b a) as [H2| H2]; [ right | left ]. {
  intros H3.
  apply (rngl_lt_iff Hor) in H3.
  destruct H3 as (H3, H4).
  now apply (rngl_le_antisymm Hor) in H2.
} {
  specialize rngl_ord_not_le as H3.
  apply H3 in H2.
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  destruct H2 as (H2, _).
  now apply not_eq_sym.
}
Qed.

Theorem rngl_lt_irrefl :
  rngl_is_ordered T = true → ∀ a : T, ¬ (a < a)%L.
Proof.
intros * Hor a Ha.
unfold rngl_lt in Ha.
specialize (rngl_le_refl Hor a) as H1.
unfold rngl_le in H1.
destruct rngl_opt_leb; congruence.
Qed.

Theorem rngl_lt_asymm :
  rngl_is_ordered T = true →
  ∀ a b, (a < b → ¬ b < a)%L.
Proof.
intros Hor * Hab Hba.
apply (rngl_lt_iff Hor) in Hab, Hba.
destruct Hab as (Hab, Hnab).
destruct Hba as (Hba, _).
now apply Hnab, (rngl_le_antisymm Hor).
Qed.

Theorem rngl_not_le :
  rngl_is_ordered T = true →
  ∀ a b, (¬ a ≤ b → a ≠ b ∧ b ≤ a)%L.
Proof.
intros Hor *.
specialize rngl_opt_ord as rr.
rewrite Hor in rr.
move rr after rp.
specialize rngl_ord_not_le as H.
apply H.
Qed.

Theorem rngl_lt_le_incl :
  rngl_is_ordered T = true →
  ∀ a b, (a < b → a ≤ b)%L.
Proof.
intros Hor * Hab.
now apply (rngl_lt_iff Hor) in Hab.
Qed.

Theorem rngl_nle_gt :
  rngl_is_ordered T = true →
  ∀ a b, (¬ (a ≤ b) ↔ b < a)%L.
Proof.
intros Hor *.
split; intros Hab. {
  apply (rngl_not_le Hor) in Hab.
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  now apply not_eq_sym.
} {
  intros H1.
  apply (rngl_lt_iff Hor) in Hab.
  destruct Hab as (H2, H3).
  now apply H3, (rngl_le_antisymm Hor).
}
Qed.

Theorem rngl_nlt_ge :
  rngl_is_ordered T = true →
  ∀ a b, (¬ (a < b) ↔ b ≤ a)%L.
Proof.
intros Hor *.
split; intros Hab. {
  destruct (rngl_le_dec Hor b a) as [H1| H1]; [ easy | ].
  exfalso; apply Hab.
  now apply (rngl_nle_gt Hor).
} {
  intros H1.
  apply (rngl_lt_iff Hor) in H1.
  destruct H1 as (H2, H3).
  now apply H3, (rngl_le_antisymm Hor).
}
Qed.

Theorem rngl_lt_le_trans :
  rngl_is_ordered T = true →
   ∀ a b c : T, (a < b)%L → (b ≤ c)%L → (a < c)%L.
Proof.
intros Hor * Hab Hbc.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_le_trans Hor _ b); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
} {
  intros H; subst c.
  now apply (rngl_nle_gt Hor) in Hab.
}
Qed.

Theorem rngl_le_lt_trans :
  rngl_is_ordered T = true →
   ∀ a b c : T, (a ≤ b)%L → (b < c)%L → (a < c)%L.
Proof.
intros Hor * Hab Hbc.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_le_trans Hor _ b); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
} {
  intros H; subst c.
  now apply (rngl_nle_gt Hor) in Hbc.
}
Qed.

Theorem rngl_lt_trans :
  rngl_is_ordered T = true →
   ∀ a b c : T, (a < b)%L → (b < c)%L → (a < c)%L.
Proof.
intros Hor * Hab Hbc.
apply (rngl_le_lt_trans Hor _ b); [ | easy ].
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_leb_gt :
  rngl_is_ordered T = true →
  ∀ a b, ((a ≤? b) = false ↔ b < a)%L.
Proof.
intros Hor *.
split; intros Hab. {
  apply rngl_leb_nle in Hab.
  apply (rngl_not_le Hor) in Hab.
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  now apply not_eq_sym.
} {
  apply rngl_leb_nle.
  intros H1.
  now apply (rngl_nle_gt Hor) in Hab.
}
Qed.

Theorem rngl_ltb_ge :
  rngl_is_ordered T = true →
  ∀ a b, ((a <? b) = false ↔ b ≤ a)%L.
Proof.
intros Hor *.
split; intros Hab. {
  apply rngl_ltb_nlt in Hab.
  now apply (rngl_nlt_ge Hor) in Hab.
} {
  apply rngl_ltb_nlt.
  intros H1.
  now apply (rngl_nlt_ge Hor) in Hab.
}
Qed.

Theorem rngl_min_id :
  rngl_is_ordered T = true →
  ∀ a, rngl_min a a = a.
Proof.
intros Hor *.
progress unfold rngl_min.
now rewrite (rngl_leb_refl Hor).
Qed.

End a.
