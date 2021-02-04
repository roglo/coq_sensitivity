(* vectors *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith (*Bool*).
Import List List.ListNotations.
(*
Require Import Init.Nat.

Require Import Misc.
*)
Require Import RingLike (* RLsummation RLproduct*).

Record vector (n : nat) T := mk_vect
  { vect_el : nat → T }.

(* function extensionality required for vectors *)
Axiom vector_eq : ∀ n T (VA VB : vector n T),
  (∀ i, i < n → vect_el VA i = vect_el VB i)
  → VA = VB.

Definition vect_of_list {T} d (l : list T) :=
  mk_vect (length l) (λ i, nth i l d).
Definition list_of_vect {n T} (v : vector n T) :=
  map (vect_el v) (seq 0 n).

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.

Definition vect_zero n := mk_vect n (λ _, 0%F).

(* addition, subtraction of vector *)

Definition vect_add {n} (U V : vector n T) :=
  mk_vect n (λ i, (vect_el U i + vect_el V i)%F).
Definition vect_opp {n} (V : vector n T) :=
  mk_vect n (λ i, (- vect_el V i)%F).

Definition vect_sub {n} (U V : vector n T) := vect_add U (vect_opp V).

End a.

