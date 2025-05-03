(* LapPolyn.v *)

Set Nested Proofs Allowed.

From Stdlib Require Import Utf8 Arith.
Import List.ListNotations Init.Nat.

Require Import RingLike.RingLike.
Require Import RingLike.IterAdd.
Require Import RingLike.LapRingLike.

Require Import Misc.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.

(* evaluation of a polynomial in x *)
(* and composition of polynomials *)

Definition rlap_horner {A} (zero : A) (add mul : A → A → A) rla x :=
  iter_list rla (λ accu a, add (mul accu x) a) zero.

Definition eval_rlap :=
  rlap_horner 0%L rngl_add rngl_mul.

Definition eval_lap la x :=
  eval_rlap (List.rev la) x.

Definition rlap_compose rla rlb :=
  rlap_horner [] lap_add lap_mul (List.map (λ a, [a]) rla) (List.rev rlb).

Definition lap_compose la lb :=
  rlap_compose (List.rev la) (List.rev lb).

End a.
