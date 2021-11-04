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

Theorem and_list_true_if : ∀ A (l : list A) f,
  ⋀ (a ∈ l), f a = true →
  ∀ a, a ∈ l → f a = true.
Proof.
intros * Hb a Ha.
induction l as [| b]; [ easy | ].
rewrite iter_list_cons in Hb; [ | easy | | ]; cycle 1. {
  apply Bool.andb_true_r.
} {
  apply Bool.andb_assoc.
}
apply Bool.andb_true_iff in Hb.
destruct Ha as [Ha| Ha]; [ now subst b | ].
now apply IHl.
Qed.

Theorem and_seq_true_if : ∀ b e f,
  ⋀ (i = b, e), f i = true →
  ∀ i, b ≤ i ≤ e → f i = true.
Proof.
intros * Hb i Hi.
unfold iter_seq in Hb.
apply and_list_true_if with (l := seq b (S e - b)); [ easy | ].
apply in_seq; flia Hi.
Qed.
