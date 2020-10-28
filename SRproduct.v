(* products on a semiring *)

Set Nested Proofs Allowed.

Require Import Utf8.
Require Import Misc Semiring.

Notation "'Π' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, (c * g)%Srng) 1%Srng)
  (at level 45, i at level 0, b at level 60, e at level 60) :
     semiring_scope.
