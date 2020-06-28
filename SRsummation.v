(* summations on ar semiring *)

Require Import Utf8 Arith.
Require Import Semiring.
Import List.

Notation "'Σ' ( i = b , e ) , g" :=
  (fold_left (λ c i, (c + g)%Srng) (seq b (S e - b)) 0%Srng)
  (at level 45, i at level 0, b at level 60, e at level 60) : semiring_scope.

Notation "'Σ' ( i = b , e ) , g" :=
  (fold_left (λ c i, (c + g)%Rng) (seq b (S e - b)) 0%Rng)
  (at level 45, i at level 0, b at level 60, e at level 60) : ring_scope.
