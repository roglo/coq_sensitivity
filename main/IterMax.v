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

(* to be completed
Theorem max_iter_list_app :
  rngl_is_ordered T = true →
  ∀ A (la lb : list A) f,
  (∀ x, rngl_max 0 (f x) = f x)
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
specialize (IHlb (la ++ [b])) as H1.
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
now rewrite Hm.
Qed.
...
*)

Theorem max_iter_list_app :
  rngl_is_ordered T = true →
  ∀ A (la lb : list A) f,
  (∀ x, rngl_max 0 x = x)
  → Max (i ∈ la ++ lb), f i =
      rngl_max (Max (i ∈ la), f i) (Max (i ∈ lb), f i).
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

(*
Theorem max_list_app' :
  rngl_is_ordered T = true →
  ∀ A (la lb : list A) f,
  (∀ x, x ∈ List.map f lb → rngl_max 0 x = x)
  → Max (i ∈ la ++ lb), f i =
      rngl_max (Max (i ∈ la), f i) (Max (i ∈ lb), f i).
Proof.
intros Hor * Hm.
rewrite iter_list_app.
progress unfold iter_list.
apply fold_left_op_fun_from_d'; [ easy | | ]. {
  intros.
  rewrite (rngl_max_comm Hor).
  apply Hm.
...
  intros.
  apply (rngl_max_assoc Hor).
}
Qed.
*)

Theorem max_iter_list_cons :
  rngl_is_ordered T = true →
  ∀ A (a : A) la f,
  (∀ x, rngl_max 0 x = x)
  → Max (i ∈ a :: la), f i = rngl_max (f a) (Max (i ∈ la), f i).
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
