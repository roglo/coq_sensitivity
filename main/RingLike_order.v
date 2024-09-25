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

End a.
