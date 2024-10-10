Require Import Utf8.
Require Import Misc RingLike.
Open Scope list.

Notation "'Max' d ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, rngl_max c (g)) d)
  (at level 45, d at level 1, i at level 0, b at level 60, e at level 60).

Notation "'Max' d ( i ∈ l ) , g" :=
  (iter_list l (λ c i, rngl_max c (g)) d)
  (at level 45, d at level 1, i at level 0, l at level 60).

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem max_list_app :
  rngl_is_ordered T = true →
  ∀ A (la lb : list A) f d,
  (∀ x, rngl_max d x = x)
  → Max d (i ∈ la ++ lb), f i =
      rngl_max (Max d (i ∈ la), f i) (Max d (i ∈ lb), f i).
Proof.
intros Hor * Hm.
rewrite iter_list_app.
progress unfold iter_list.
apply fold_left_op_fun_from_d; [ easy | | ]. {
  intros.
  rewrite (rngl_max_comm Hor).
  apply Hm.
} {
  intros.
  apply (rngl_max_assoc Hor).
}
Qed.

Theorem max_list_cons :
  rngl_is_ordered T = true →
  ∀ A (a : A) la f d,
  (∀ x, rngl_max d x = x)
  → Max d (i ∈ a :: la), f i = rngl_max (f a) (Max d (i ∈ la), f i).
Proof.
intros Hor * Hm.
apply iter_list_cons; [ easy | | ]. {
  intros.
  rewrite (rngl_max_comm Hor).
  apply Hm.
} {
  intros.
  apply (rngl_max_assoc Hor).
}
Qed.

End a.
