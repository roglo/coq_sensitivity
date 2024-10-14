(* maximum of a list or of a sequence *)

Require Import Utf8.
Require Import Misc RingLike.
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

Theorem max_list_app :
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

Theorem max_list_cons :
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
