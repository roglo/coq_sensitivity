(* iterators of "and" on bool *)

Set Nested Proofs Allowed.

Require Import Utf8 (*Arith Permutation*).
Require Import Misc (*RingLike*).
Import List (*List.ListNotations*).

Notation "'⋀' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, (c && g)%bool) true)
  (at level 45, i at level 0, b at level 60, e at level 60).

Notation "'⋀' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, (c && g)%bool) true)
  (at level 45, i at level 0, l at level 60).

Theorem all_true_and_list_true_iff : ∀ A (l : list A) f,
  (∀ a, a ∈ l → f a = true)
  ↔ ⋀ (a ∈ l), f a = true.
Proof.
intros.
induction l as [| b]; [ easy | ].
rewrite iter_list_cons; cycle 1. {
  apply Bool.andb_true_l.
} {
  apply Bool.andb_true_r.
} {
  apply Bool.andb_assoc.
}
rewrite Bool.andb_true_iff.
split. {
  intros Hb.
  split; [ now apply Hb; left | ].
  apply IHl.
  intros a Ha.
  now apply Hb; right.
} {
  intros Hb a Ha.
  destruct Ha as [Ha| Ha]; [ now subst b | ].
  now apply IHl.
}
Qed.

Theorem all_true_and_seq_true_iff : ∀ b e f,
  (∀ i, b ≤ i ≤ e → f i = true)
  ↔ ⋀ (i = b, e), f i = true.
Proof.
intros.
specialize (all_true_and_list_true_iff nat (seq b (S e - b))) as H1.
split. {
  intros Hb.
  apply H1.
  intros i Hi; apply in_seq in Hi.
  apply Hb; flia Hi.
} {
  intros Hb i Hi.
  apply H1; [ easy | ].
  apply in_seq; flia Hi.
}
Qed.

Theorem and_seq_eq_compat : ∀ g h b k,
  (∀ i, b ≤ i ≤ k → g i = h i)
  → ⋀ (i = b, k), g i = ⋀ (i = b, k), h i.
Proof.
intros * Hgh.
now apply iter_seq_eq_compat.
Qed.

Theorem and_seq_succ_succ : ∀ b k g,
  ⋀ (i = S b, S k), g i = ⋀ (i = b, k), g (S i).
Proof.
intros b k g.
apply iter_seq_succ_succ.
Qed.
