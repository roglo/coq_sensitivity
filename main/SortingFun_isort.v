(* isort: sort by insertion *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Import List.ListNotations.
(*
Import Init.Nat.
*)

Require Import Misc(* PermutationFun*).

Fixpoint isort_insert {A} (rel : A → A → bool) a lsorted :=
  match lsorted with
  | [] => [a]
  | b :: l => if rel a b then a :: lsorted else b :: isort_insert rel a l
  end.

Fixpoint isort {A} (rel : A → A → bool) l :=
  match l with
  | [] => []
  | a :: l' => isort_insert rel a (isort rel l')
  end.

Theorem fold_isort : ∀ A (rel : A → _) a l,
  isort_insert rel a (isort rel l) = isort rel (a :: l).
Proof. easy. Qed.

(* isort length *)

Theorem isort_insert_length : ∀ A rel (a : A) lsorted,
  length (isort_insert rel a lsorted) = S (length lsorted).
Proof.
intros.
induction lsorted as [| b]; intros; [ easy | cbn ].
destruct (rel a b); [ easy | ].
now cbn; f_equal.
Qed.

Theorem isort_length : ∀ A rel (l : list A), length (isort rel l) = length l.
Proof.
intros.
induction l as [| a]; [ easy | cbn ].
rewrite <- IHl.
apply isort_insert_length.
Qed.
