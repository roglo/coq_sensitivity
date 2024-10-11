Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Import List.ListNotations.
(*
Import Init.Nat.
*)

Require Import Misc PermutationFun.

(* relation properties *)

Definition irreflexive {A} (rel : A → A → bool) :=
  ∀ a, rel a a = false.

Definition antisymmetric {A} (rel : A → A → bool) :=
  ∀ a b, rel a b = true → rel b a = true → a = b.

(* https://ncatlab.org/nlab/show/connected+relation *)
Definition connected_relation {A} (rel : A → A → bool) :=
  ∀ a b, rel a b = false → rel b a = false → a = b.

Definition transitive {A} (rel : A → A → bool) :=
  ∀ a b c, rel a b = true → rel b c = true → rel a c = true.

Definition total_relation {A} (rel : A → _) := ∀ a b,
  (rel a b || rel b a)%bool = true.

Theorem total_relation_is_reflexive : ∀ {A} {rel : A → _},
  total_relation rel → reflexive rel.
Proof.
intros * Htot a.
specialize (Htot a a) as H1.
apply Bool.orb_true_iff in H1.
now destruct H1.
Qed.

(* compute if a list is sorted *)

Fixpoint is_sorted {A} (rel : A → A → bool) l :=
  match l with
  | [] => true
  | [a] => true
  | a :: (b :: _) as la => (rel a b && is_sorted rel la)%bool
  end.

Fixpoint all_sorted {A} (rel : A → A → bool) a l :=
  match l with
  | [] => true
  | b :: l' => (rel a b && all_sorted rel a l')%bool
  end.

Fixpoint is_strongly_sorted {A} (rel : A → A → bool) l :=
  match l with
  | [] => true
  | a :: l' => (all_sorted rel a l' && is_strongly_sorted rel l')%bool
  end.

Definition sorted {A} (rel : A → _) l :=
  is_sorted rel l = true.
Definition strongly_sorted {A} (rel : A → _) l :=
  is_strongly_sorted rel l = true.
