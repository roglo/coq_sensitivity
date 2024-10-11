(* bsort: bubble sort *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Import List.ListNotations.

Require Import Misc PermutationFun.
Require Import SortingFun_common.

Fixpoint bsort_swap {A} (rel : A → A → bool) l :=
  match l with
  | [] | [_] => None
  | a :: (b :: l'') as l' =>
      if rel a b then
        match bsort_swap rel l' with
        | Some l''' => Some (a :: l''')
        | None => None
        end
      else
        Some (b :: a :: l'')
  end.

Fixpoint bsort_loop {A} (rel : A → A → bool) it l :=
  match it with
  | 0 => l
  | S it' =>
      match bsort_swap rel l with
      | Some l' => bsort_loop rel it' l'
      | None => l
      end
  end.

Definition bsort {A} (rel : A → _) l :=
  bsort_loop rel (length l * length l) l.
