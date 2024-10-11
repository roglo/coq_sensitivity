(* Sorting algorithms : bubble, selection, insertion, merge *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Import List.ListNotations.
Import Init.Nat.

Require Import Misc PermutationFun.
Require Export SortingFun_common.
Require Export SortingFun_misc.

Require Export SortingFun_isort.
Require Export SortingFun_ssort.
Require Export SortingFun_bsort.
Require Export SortingFun_msort.

(* isort and ssort return same *)

Theorem isort_ssort : ∀ (A : Type) (eqb : A → _) (rel : A → A → bool),
  equality eqb →
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ l, isort rel l = ssort rel l.
Proof.
intros * Heqb Hant Htra Htot *.
specialize (total_relation_is_reflexive Htot) as Href.
apply (sorted_unique Heqb Href Hant Htra). {
  clear l; intros l.
  split; [ | now apply sorted_isort ].
  apply (permutation_sym Heqb).
  now apply permuted_isort.
} {
  clear l; intros l.
  split; [ | now apply sorted_ssort ].
  apply (permutation_sym Heqb).
  now apply permuted_ssort.
}
Qed.

(* ssort and bsort return same *)

Theorem ssort_bsort : ∀ A (eqb : A → _) (rel : A → A → bool),
  equality eqb →
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ l, ssort rel l = bsort rel l.
Proof.
intros * Heqb Hant Htra Htot *.
specialize (total_relation_is_reflexive Htot) as Href.
apply (sorted_unique Heqb Href Hant Htra). {
  clear l; intros l.
  split; [ | now apply sorted_ssort ].
  now apply permutation_sym, permuted_ssort.
} {
  clear l; intros l.
  split; [ | now apply sorted_bsort ].
  now apply permutation_sym, permuted_bsort.
}
Qed.

(* bsort and isort return same *)

Theorem bsort_isort : ∀ A (eqb : A → _) (rel : A → A → bool),
  equality eqb →
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ l, bsort rel l = isort rel l.
Proof.
intros * Heqb Hant Htra Htot *.
specialize (total_relation_is_reflexive Htot) as Href.
apply (sorted_unique Heqb Href Hant Htra). {
  clear l; intros l.
  split; [ | now apply sorted_bsort ].
  now apply permutation_sym, permuted_bsort.
} {
  clear l; intros l.
  split; [ | now apply sorted_isort ].
  now apply permutation_sym, permuted_isort.
}
Qed.
