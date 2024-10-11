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
