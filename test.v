Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Rational.
Require Import Qfield2.
Require Import CharacPolyn.
Require Import SRpolynomial.
Require Import Matrix.
Require Import Lemma_2_2.
Import matrix_Notations.

Import Q.Notations.
Open Scope Q_scope.

Existing Instance Q_semiring_op.
Existing Instance Q_ring_op.
Existing Instance Q_sring_dec_prop.
Existing Instance Q_field_op.
Existing Instance Q_semiring_prop.
Existing Instance Q_ring_prop.

Definition qtest_gj ll :=
  let r := gauss_jordan (mat_of_list_list 0%Q ll) in
  list_list_of_mat r.
Definition qtest_gj' ll :=
  let r := gauss_jordan' (mat_of_list_list 0%Q ll) in
  list_list_of_mat r.
(*
Definition qtest_gjl ll :=
  let r := gauss_jordan_list (mat_of_list_list 0%Q ll) in
  map (@list_list_of_mat _) r.
*)
Definition qtest_gjso (ll : list (list Q)) r i j :=
  let M := mat_of_list_list 0 ll in
  list_list_of_mat (gauss_jordan_step_op M r i j).
Definition qtest_gjs (ll : list (list Q)) r i j :=
  let M := mat_of_list_list 0 ll in
  list_list_of_mat (gauss_jordan_step_op M r i j * M)%M.
Definition qresolve (ll : list (list Q)) v :=
  resolve (mat_of_list_list 0 ll) (vect_of_list 0 v).
Definition qcp ll := polyn_list (charac_polyn (mat_of_list_list 0 ll)).
Definition qtest_mul_m_v m v :=
  list_of_vect (mat_mul_vect_r (mat_of_list_list 0 m) (vect_of_list 0 v)).
Definition qtest_det ll := determinant (mat_of_list_list 0 ll).
Definition qtest_det_mf ll := det_mult_fact_from_gjl (mat_of_list_list 0 ll).

Compute qtest_gj [[1]].
Compute qtest_gj [[2; -1; 0]; [-1; 2; -1]; [0; -1; 2]].
(* = [[〈1〉; 0; 0]; [0; 〈1〉; 0]; [0; 0; 〈1〉]] *)
Compute qtest_gj [[1;3;1;9];[1;1;-1;1];[3;11;5;35]].
Compute qtest_gj' [[1;3;1;9];[1;1;-1;1];[3;11;5;35]].
(* = [[〈1〉; 0; 〈-2〉; 〈-3〉]; [0; 〈1〉; 〈1〉; 〈4〉]; [0; 0; 0; 0]] *)
Compute qtest_det [[2; -1; 0]; [-1; 2; -1]; [0; -1; 2]].
Compute qtest_det_mf [[2; -1; 0]; [-1; 2; -1]; [0; -1; 2]].

Compute qtest_gj [[2;1;-1;8];[-3;-1;2;-11];[-2;1;2;-3]].
Compute qtest_gj' [[2;1;-1;8];[-3;-1;2;-11];[-2;1;2;-3]].
(* = [[〈1〉; 0; 0; 〈2〉]; [0; 〈1〉; 0; 〈3〉]; [0; 0; 〈1〉; 〈-1〉]] *)
Compute qtest_det [[2;1;-1];[-3;-1;2];[-2;1;2]].
Compute qtest_det_mf [[2;1;-1];[-3;-1;2];[-2;1;2]].

Compute qtest_gj [[2;-1;0;1;0;0];[-1;2;-1;0;1;0];[0;-1;2;0;0;1]].
Compute qtest_gj' [[2;-1;0;1;0;0];[-1;2;-1;0;1;0];[0;-1;2;0;0;1]].
(* = [[〈1〉; 0; 0; 〈3╱4〉; 〈1╱2〉; 〈1╱4〉]; [0; 〈1〉; 0; 〈1╱2〉; 〈1〉; 〈1╱2〉];
      [0; 0; 〈1〉; 〈1╱4〉; 〈1╱2〉; 〈3╱4〉]] *)

Compute qtest_gj [[0;2;1;0];[-7;-3;0;1];[3;8;18;5]].
(* = [[〈1〉; 0; 0; 〈-13╱205〉]; [0; 〈1〉; 0; 〈-38╱205〉]; [0; 0; 〈1〉; 〈76╱205〉]] *)
Compute qtest_gj [[-7;-3;0;1];[3;8;18;5];[0;2;1;0]].
(* = [[〈1〉; 0; 0; 〈-13╱205〉]; [0; 〈1〉; 0; 〈-38╱205〉]; [0; 0; 〈1〉; 〈76╱205〉]] *)
Compute qtest_gj [[5;2;1;0];[-7;-3;0;1]].
(* = [[〈1〉; 0; 〈3〉; 〈2〉]; [0; 〈1〉; 〈-7〉; 〈-5〉]] *)
Compute qtest_gj [[-7;-3;0;1];[5;2;1;0]].
(* = [[〈1〉; 0; 〈3〉; 〈2〉]; [0; 〈1〉; 〈-7〉; 〈-5〉]] *)
Compute qtest_gj [[-3;-3;3];[3;-9;3];[6;-6;0]].
(*
     = [[〈1〉; 0; 〈-1╱2〉]; [0; 〈1〉; 〈-1╱2〉]; [0; 0; 0]]
   1 0 -1/2
   0 1 -1/2
   0 0  0
*)
Compute qtest_det [[-3;-3;3];[3;-9;3];[6;-6;0]].
Compute qtest_det_mf [[-3;-3;3];[3;-9;3];[6;-6;0]].
Compute qtest_gj [[3;-3;3];[3;-3;3];[6;-6;6]].
(*
     = ([[6; -6; 6]; [0; 0; 0]; [0; 0; 0]], 6)
*)
Compute qtest_gj [[1;-1;2;5];[3;2;1;10];[2;-3;-2;-10]].
(*
     = ([[4095; 0; 0; 4095]; [0; 4095; 0; 8190]; [0; 0; 4095; 12285]], 4095)
     = ([[1; 0; 0; 1]; [0; 1; 0; 2]; [0; 0; 1; 3]], 1)
*)
Compute qtest_gj [[1;2;2;-3;2;3];[2;4;1;0;-5;-6];[4;8;5;-6;-1;0];[-1;-2;-1;1;1;1]].
(*
     = ([[-24; -48; 0; -24; 96; 120]; [0; 0; -24; 48; -72; -96];
        [0; 0; 0; 0; 0; 0]; [0; 0; 0; 0; 0; 0]], -24)
*)

(* trying to find eigenvalues and eigenvector on an example *)
Compute qcp [[4;3];[-2;-3]].
(*
P=x²-x-6
Δ=1+24=25
r=(1±5)/2 (3 & -2)
P=(x-3)(x+2)
λ=3 or λ=-2
1/ λ=3
   λI-M=[[-1;-3];[2;6]]
*)
Compute qtest_gj [[-1;-3];[2;6]].
(*
     = [[〈1〉; 〈3〉]; [0; 0]]
x₁+3x₂=0
*)
Compute qresolve [[-1;-3];[2;6]] [0;0].
(* = [〈-3〉; 〈1〉] *)
Compute qtest_mul_m_v [[4;3];[-2;-3]] [-3;1].
(*
     = [〈-9〉; 〈3〉]
    Indeed, [-3;1] is an eigenvector
*)
Compute qtest_det [[-1;-3];[2;6]].
Compute qtest_det_mf [[-1;-3];[2;6]].
(*
2/ λ=-2
   λI-M=[[-6;-3];[2;1]]
*)
Compute qtest_gj [[-6;-3];[2;1]].
(*
     = [[〈1〉; 〈1╱2〉]; [0; 0]]
x₁+1/2x₂=0
*)
Compute qresolve [[-6;-3];[2;1]] [0;0].
(* = [〈-1╱2〉; 〈1〉] *)
Compute qtest_mul_m_v [[4;3];[-2;-3]] [-1/2;1].
(*
     = [〈1〉; 〈-2〉]
    Indeed, [-1/2;1] is an eigenvector
*)

(* non invertible; what if computing its "invert" by gauss-jordan? *)
Compute qtest_gj [[-6;-3;1;0];[2;1;0;1]].
(* = [[〈1〉; 〈1╱2〉; 0; 〈1╱2〉]; [0; 0; 〈1〉; 〈3〉]] *)
Compute list_list_of_mat (mat_mul (mat_of_list_list 0 [[-6;-3];[2;1]]) (mat_of_list_list 0 [[0;1/2];[1;3]])).
(* = [[〈-3〉; 〈-12〉]; [〈1〉; 〈4〉]] ok, instead of I *)

(* for an invertible matrix *)
Compute qtest_gj [[-7;-3;1;0];[2;1;0;1]].
(* = [[〈1〉; 0; 〈-1〉; 〈-3〉]; [0; 〈1〉; 〈2〉; 〈7〉]] *)
Compute list_list_of_mat (mat_mul (mat_of_list_list 0 [[-7;-3];[2;1]]) (mat_of_list_list 0 [[-1;-3];[2;7]])).
(* = [[〈1〉; 0]; [0; 〈1〉]] ok *)

(* https://en.wikipedia.org/wiki/Kernel_(linear_algebra)#Illustration *)
Compute qtest_gj [[2;3;5];[-4;2;3]].
(*
     = [[〈1〉; 0; 〈1╱16〉]; [0; 〈1〉; 〈13╱8〉]]

  Good! matches what is written in the wikipedia page.
*)

Compute qtest_gj [[1;2;2;2];[1;3;-2;-1];[3;5;8;8]].
Compute qtest_gj [[2;3;1;1];[3;1;5;2];[4;-1;-1;0]].
Compute qtest_gj [[2;3;1;1];[0;-7;7;1];[0;-7;-3;-2]].
Compute qtest_gj [[3;3;3;18];[-1;3;7;-10];[1;3;4;6]].
Compute qtest_gj [[0;0;2;-2;8;-6];[1;2;1;0;5;-1];[-2;-4;-1;0;-8;-1]].
Compute qtest_gj [[4;6;6];[1;3;2];[-1;-5;-2]].
Compute qcp [[4;6;6];[1;3;2];[-1;-5;-2]].
Compute qtest_mul_m_v [[4;6;6];[1;3;2];[-1;-5;-2]] [4;1;-3].
Compute qtest_mul_m_v [[4;6;6];[1;3;2];[-1;-5;-2]] [3;1;-2].
Compute qtest_gj [[3;6;6];[1;2;2];[-1;-5;-3]].
Compute qcp [[3;6;6];[1;2;2];[-1;-5;-3]].

Compute qcp [[5;0;1];[1;1;0];[-7;1;0]].
(* x³-6x²+12x-8 = (x-2)³*)
Compute qtest_gj [[-3;0;-1];[-1;1;0];[7;-1;2]].
Compute qtest_gj [[3;0;1];[1;-1;0];[-7;1;-2]].
(* dimension of eigenvectors is 1, even if the multiplicity of 2 is 3 *)

(* pourquoi il me demande Q_semiring_op comme paramètre, ce con ?
   pourquoi pas aussi Q_field_op et Q_ring_op, dans ce cas ? *)
Definition qtest_rs (ll : list (list Q)) v :=
  resolve_system Q_semiring_op (mat_of_list_list 0 ll) (vect_of_list 0 v).

Compute qtest_rs [[4;2];[3;-1]] [-1;2].
(*
     = [〈3╱10〉; 〈-11╱10〉]     ok
*)
Compute qtest_rs [[1;10;-3];[2;-1;2];[-1;1;1]] [5;2;-3].
(*
     = [〈2〉; 0; 〈-1〉]
*)
Compute qtest_rs [[3;2;-1];[2;-2;4];[-1;1/2;-1]] [1;-2;0].
(*
     = [〈1〉; 〈-2〉; 〈-2〉]      ok
*)

Compute list_list_of_mat (mat_id_add_rows_mul_scal_row Q_semiring_op (mat_of_list_list 0 [[1;2;3;4;5];[6;7;8;9;10];[11;12;13;14;15];[16;17;18;19;20];[21;22;23;23;25]]) 2%nat 4%nat).
(*
     = [[〈1〉; 0; 〈-5〉; 0; 0]; [0; 〈1〉; 〈-10〉; 0; 0];
       [0; 0; 〈1〉; 0; 0]; [0; 0; 〈-20〉; 〈1〉; 0]; [0; 0; 〈-25〉; 0; 〈1〉]]
*)

Compute list_list_of_mat (mat_id_add_rows_mul_scal_row Q_semiring_op (mat_of_list_list 0 [[1;2;3;4;5];[6;7;8;9;10];[11;12;13;14;15];[16;17;18;19;20];[21;22;23;23;25]]) 4%nat 0%nat).

Compute qresolve [[4;2];[3;-1]] [-1;2].
(*
     = [〈3╱10〉; 〈-11╱10〉]     ok
*)

(* *)
Compute qtest_gj [[1;3;1];[1;1;-1];[3;11;5]].
(*
     = [[〈1〉; 0; 〈-2〉]; [0; 〈1〉; 〈1〉]; [0; 0; 0]]
*)
Compute qtest_gjso [[1;3;1;9];[1;1;-1;1];[3;11;5;35]] 0 0 0.
(*
     = [[〈1〉; 0; 0]; [〈-1〉; 〈1〉; 0]; [〈-3〉; 0; 〈1〉]]
*)
Compute qtest_gjs [[1;3;1;9];[1;1;-1;1];[3;11;5;35]] 0 0 0.
(*
     = [[〈1〉; 〈3〉; 〈1〉; 〈9〉]; [0; 〈-2〉; 〈-2〉; 〈-8〉]; [0; 〈2〉; 〈2〉; 〈8〉]]
*)
Compute qtest_gj [[1;3;1;9];[1;1;-1;1];[3;11;5;35]].
(*
     = [[〈1〉; 0; 〈-2〉; 〈-3〉]; [0; 〈1〉; 〈1〉; 〈4〉]; [0; 0; 0; 0]]
*)
Compute qresolve [[1;3;1];[1;1;-1];[3;11;5]] [9;1;35].
(*
     = [〈-1〉; 〈3〉; 〈1〉]
*)
Compute qtest_mul_m_v [[1;3;1];[1;1;-1];[3;11;5]] [-1;3;1].
(*
     = [〈9〉; 〈1〉; 〈35〉]    ok
*)

Compute qresolve [[2; -1; 0]; [-1; 2; -1]; [0; -1; 2]] [3;4;5].
(*
     = [〈11╱2〉; 〈8〉; 〈13╱2〉]
*)
Compute qtest_mul_m_v [[2; -1; 0]; [-1; 2; -1]; [0; -1; 2]] [11/2;8;13/2].

Compute qresolve [[2; -1; 0]; [-1; 2; -1]; [0; -1; 2]] [3;4;6].
(* = [〈23╱4〉; 〈17╱2〉; 〈29╱4〉] *)
Compute qtest_mul_m_v [[2; -1; 0]; [-1; 2; -1]; [0; -1; 2]] [23/4;17/2;29/4].

Compute qresolve [[2; -1; 0]; [-1; 2; -1]; [0; -1; 2]] [3;1;4].
(* [〈15╱4〉; 〈9╱2〉; 〈17╱4〉] *)
Compute qtest_mul_m_v [[2; -1; 0]; [-1; 2; -1]; [0; -1; 2]] [15/4;9/2;17/4].

Compute qresolve [[2;1;-1];[-3;-1;2];[-2;1;2]] [8;-11;-3].
(* [2;3;-1] *)
Compute qtest_mul_m_v [[2;1;-1];[-3;-1;2];[-2;1;2]] [2;3;-1].
Compute qtest_gj [[1; 1; 1; 0]; [1; 1; 0; 1]].
