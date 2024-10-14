(* maximum of a list or of a sequence *)

Require Import Utf8.
Require Import Misc RingLike.
Import List.ListNotations.
Open Scope list.

Notation "'Max' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, rngl_max c (g)) 0%L)
  (at level 45, i at level 0, b at level 60, e at level 60).

Notation "'Max' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, rngl_max c (g)) 0%L)
  (at level 45, i at level 0, l at level 60).

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem max_iter_list_app :
  rngl_is_ordered T = true →
  ∀ A (la lb : list A) f,
  (∀ x, x ∈ lb → rngl_max 0 (f x) = f x)
  → Max (i ∈ la ++ lb), f i =
      rngl_max (Max (i ∈ la), f i) (Max (i ∈ lb), f i).
Proof.
intros Hor * Hm.
rewrite iter_list_app.
rewrite (rngl_max_comm Hor).
progress unfold iter_list.
revert la.
induction lb as [| b]; intros; cbn. {
  symmetry.
  apply (rngl_max_r_iff Hor).
  remember (List.fold_left _ _ _) as v eqn:Hv.
  remember 0%L as z in Hv.
  assert (Hz : (0 ≤ z)%L). {
    subst z.
    apply (rngl_le_refl Hor).
  }
  clear Heqz; subst v.
  revert z Hz.
  induction la as [| a]; intros; [ easy | cbn ].
  apply IHla.
  apply (rngl_le_trans Hor _ z); [ easy | ].
  apply (rngl_le_max_l Hor).
}
assert (H : ∀ x, x ∈ lb → rngl_max 0 (f x) = f x). {
  intros x Hx.
  now apply Hm; right.
}
specialize (IHlb H).
specialize (IHlb (la ++ [b])) as H1; clear H.
rewrite List.fold_left_app in H1.
cbn in H1.
rewrite H1; clear H1.
rewrite (rngl_max_comm Hor _ (f b)).
rewrite (rngl_max_assoc Hor).
f_equal.
specialize (IHlb [b]) as H1.
cbn in H1.
rewrite H1.
f_equal.
symmetry.
now apply Hm; left.
Qed.

Theorem max_iter_list_cons :
  rngl_is_ordered T = true →
  ∀ A a (la : list A) f,
  (∀ x, x ∈ a :: la → rngl_max 0 (f x) = f x)
  → Max (i ∈ a :: la), f i = rngl_max (f a) (Max (i ∈ la), f i).
Proof.
intros Hor * Hm.
rewrite List_cons_is_app.
rewrite (max_iter_list_app Hor _ _ _ _). {
  progress unfold iter_list at 1.
  cbn.
  rewrite Hm; [ easy | now left ].
}
intros x Hx.
now apply Hm; right.
Qed.

Theorem le_max_list_r :
  rngl_is_ordered T = true →
  ∀ A l (a : A) f,
  (∀ x, x ∈ l → rngl_max 0 (f x) = f x)%L
  → a ∈ l
  → (f a ≤ Max (i ∈ l), f i)%L.
Proof.
intros Hor * Hm Hal.
revert a Hal.
induction l as [| b]; intros; [ easy | ].
rewrite (max_iter_list_cons Hor); [ | easy ].
destruct Hal as [Hal| Hal]; [ subst b; apply (rngl_le_max_l Hor) | ].
eapply (rngl_le_trans Hor); [ | apply (rngl_le_max_r Hor) ].
apply IHl; [ | easy ].
intros x Hx.
now apply Hm; right.
Qed.

Theorem le_max_seq_r :
  rngl_is_ordered T = true →
  ∀ b e a f,
  (∀ x, x ∈ List.seq b (S e - b) → rngl_max 0 (f x) = f x)%L
  → a ∈ List.seq b (S e - b)
  → (f a ≤ Max (i = b, e), f i)%L.
Proof.
intros Hor * Hm His.
progress unfold iter_seq.
now apply (le_max_list_r Hor).
Qed.

End a.
