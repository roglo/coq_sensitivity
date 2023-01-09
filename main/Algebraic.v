(* attempt to define algebraic numbers *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List ListNotations Init.Nat.

Require Import Misc RingLike.
Require Import Polynomial Matrix.

(* Sylvester matrix *)

Section a.

Context {A : Type}.
Context {ro : ring_like_op A}.

Definition rlap_sylvester_list_list (rp rq : list A) : list (list A) :=
  let m := length rp - 1 in
  let n := length rq - 1 in
  map (λ i, repeat 0%L i ++ rp ++ repeat 0%L (n - 1 - i)) (seq 0 n) ++
  map (λ i, repeat 0%L i ++ rq ++ repeat 0%L (m - 1 - i)) (seq 0 m).

Definition rlap_sylvester_mat (rp rq : list A) : matrix A :=
  mk_mat (rlap_sylvester_list_list rp rq).

End a.

Require Import RnglAlg.Qrl.
Require Import RnglAlg.Rational.
Import Q.Notations.
Open Scope Q_scope.

Compute (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9]).
Compute (mat_nrows (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9])).
Compute (mat_ncols (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9])).
Compute (is_square_matrix (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9])).
...
Compute (rlap_sylvester_mat [1] [6]).
Compute (rlap_sylvester_mat [1;2] [6;7]).
Compute (rlap_sylvester_mat [1;2;3] [6;7;8]).
