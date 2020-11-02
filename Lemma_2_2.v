(* Lemma 2.2 of the proof of the sensitivity conjecture *)
(* sequence A_n of matrices and the proof their square is "n * I_n" *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Misc Matrix BlockMat.
Require Import Semiring.
Require Import Rational.
(* required if reasoning with characteristic polynomial
   to find eigenvalues; but perhaps it is not necessary
Require Import SRproduct SRpolynomial CharacPolyn.
Import polynomial_Notations.
  end required *)
Import matrix_Notations.
Import bmatrix_Notations.

Section in_ring.

Context {T : Type}.
Context {ro : ring_op T}.
Context (so : semiring_op T).
Context {sp : semiring_prop T}.
Context {rp : ring_prop T}.
Context {sdp : sring_dec_prop T}.
(*
Context {acp : @algeb_closed_prop T so sdp}.
Existing Instance polyn_semiring_op.
*)

Add Parametric Relation : _ (@bmat_fit_for_add T)
 reflexivity proved by bmat_fit_for_add_refl
 symmetry proved by bmat_fit_for_add_symm
 transitivity proved by bmat_fit_for_add_trans
 as bmat_fit_for_add_equivalence.

(* sequence "An" *)

Fixpoint A n : bmatrix T :=
  match n with
  | 0 => BM_1 0%Srng
  | S n' =>
       BM_M
         (mat_of_list_list (BM_1 0%Srng)
            [[A n'; I_2_pow n'];
             [I_2_pow n'; bmat_opp (A n')]])
  end.

Theorem bmat_fit_for_add_IZ_A : ∀ u n,
  bmat_fit_for_add (IZ_2_pow u n) (A n).
Proof.
intros.
revert u.
induction n; intros; [ easy | cbn ].
split; [ easy | ].
split; [ easy | ].
intros * Hi Hj.
destruct i. {
  destruct j; [ apply IHn | ].
  destruct j; [ cbn | flia Hj ].
  apply bmat_fit_for_add_IZ_IZ.
}
destruct i; [ | flia Hi ].
destruct j; [ apply bmat_fit_for_add_IZ_IZ | ].
destruct j; [ cbn | flia Hj ].
transitivity (A n); [ easy | ].
apply bmat_fit_for_add_opp_r.
Qed.

Theorem sizes_of_bmatrix_A : ∀ n,
  sizes_of_bmatrix (A n) = repeat 2 n.
Proof.
intros.
induction n; [ easy | now cbn; f_equal ].
Qed.

Theorem A_is_square_bmat : ∀ n,
  is_square_bmat (A n).
Proof.
intros.
induction n; [ easy | cbn ].
split; [ easy | ].
split; [ easy | ].
intros i j Hi Hj.
destruct i; cbn. {
  destruct j; [ easy | cbn ].
  destruct j; [ | flia Hj ].
  rewrite sizes_of_bmatrix_A.
  rewrite <- (sizes_of_bmatrix_IZ n 1%Srng).
  apply IZ_is_square_bmat.
}
destruct i; [ cbn | flia Hi ].
destruct j; cbn. {
  rewrite sizes_of_bmatrix_A.
  rewrite <- (sizes_of_bmatrix_IZ n 1%Srng).
  apply IZ_is_square_bmat.
}
destruct j; [ | flia Hj ].
apply is_square_bmat_loop_opp.
apply IHn.
Qed.

Theorem bmat_zero_like_A_eq_Z :
  ∀ n, bmat_zero_like (A n) = Z_2_pow n.
Proof.
intros.
induction n; [ easy | cbn ].
f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros i j Hi Hj.
destruct i; cbn. {
  destruct j; cbn; [ easy | ].
  destruct j; [ cbn | flia Hj ].
  apply bmat_zero_like_IZ_eq_Z.
}
destruct i; [ cbn | flia Hi ].
destruct j; cbn. {
  apply bmat_zero_like_IZ_eq_Z.
}
destruct j; [ | flia Hj ].
rewrite bmat_zero_like_opp; [ easy | ].
apply A_is_square_bmat.
Qed.

Theorem Tr_A : ∀ n, Tr (A n) = 0%Srng.
Proof.
intros.
induction n; [ easy | cbn ].
rewrite IHn.
do 2 rewrite srng_add_0_l.
rewrite Tr_opp; [ | easy | easy | apply A_is_square_bmat ].
rewrite IHn.
apply rng_opp_0.
Qed.

(* "We prove by induction that A_n^2 = nI" *)

Theorem lemma_2_A_n_2_eq_n_I : ∀ n,
  (A n * A n = bmat_nat_mul_l n (I_2_pow n))%BM.
Proof.
intros.
induction n; intros; [ now cbn; rewrite srng_mul_0_l | ].
cbn; f_equal.
apply matrix_eq; cbn; [ easy | easy | ].
intros * Hi Hj.
destruct i. {
  destruct j. {
    cbn.
    rewrite bmat_nat_mul_l_succ; [ | easy ].
    rewrite <- IHn.
    rewrite bmat_mul_1_r; [ | easy | easy ].
    f_equal.
    rewrite <- bmat_zero_like_sqr; [ | apply A_is_square_bmat ].
    now apply bmat_add_0_l.
  }
  destruct j; [ cbn | flia Hj ].
  rewrite bmat_nat_mul_l_succ; [ | easy ].
  rewrite bmat_mul_1_r; [ | easy | ]. 2: {
    unfold I_2_pow.
    apply bmat_fit_for_add_IZ_A.
  }
  rewrite bmat_mul_1_l; [ | easy | ]. 2: {
    unfold I_2_pow.
    transitivity (A n); [ apply bmat_fit_for_add_IZ_A | ].
    apply bmat_fit_for_add_opp_r.
  }
  rewrite bmat_add_0_l; [ | easy ].
  rewrite bmat_add_opp_r; [ | easy | easy ].
  rewrite fold_Z_2_pow.
  rewrite old_bmat_add_0_r; [ | easy | ]. 2: {
    now apply bmat_fit_for_add_Z_2_pow_bmat_nat_mul_l.
  }
  rewrite bmat_nat_mul_0_r; [ | easy ].
  now apply bmat_zero_like_A_eq_Z.
}
destruct i; [ | flia Hi ].
destruct j; cbn. {
  rewrite bmat_mul_1_l; [ | easy | ]. 2: {
    apply bmat_fit_for_add_IZ_A.
  }
  rewrite bmat_mul_1_r; [ | easy | ]. 2: {
    transitivity (A n); [ | apply bmat_fit_for_add_opp_r ].
    apply bmat_fit_for_add_IZ_A.
  }
  rewrite bmat_add_0_l; [ | easy ].
  rewrite bmat_add_opp_r; [ | easy | easy ].
  rewrite bmat_nat_mul_l_succ; [ | easy ].
  rewrite fold_Z_2_pow.
  rewrite bmat_nat_mul_0_r; [ | easy ].
  rewrite old_bmat_add_0_r; [ | easy | easy ].
  now apply bmat_zero_like_A_eq_Z.
}
destruct j; [ cbn | flia Hj ].
rewrite bmat_mul_1_l; [ | easy | easy ].
rewrite bmat_mul_sqr_opp; [ | easy | easy | apply A_is_square_bmat ].
rewrite bmat_nat_mul_l_succ; [ | easy ].
rewrite <- IHn.
rewrite bmat_zero_like_A_eq_Z.
rewrite old_bmat_add_0_l; [ | easy | apply bmat_fit_for_add_IZ_IZ ].
apply bmat_add_comm; [ easy | ].
transitivity (A n). 2: {
  apply (is_square_bmat_fit_for_add (sizes_of_bmatrix (A n))). {
    apply A_is_square_bmat.
  }
  apply is_square_bmat_loop_mul; apply A_is_square_bmat.
}
apply bmat_fit_for_add_IZ_A.
Qed.

(* proof that the square of eigenvalues of An is n
   let V be an eigenvector associated with the eigenvalue λ; we have
       An V = λ V
   therefore
       An² V = An (λ V) = λ (An V) = λ² V
   but, by first part of lemma 2.2, we have
       An² = nI
   we can deduce that
       λ² V = n V
   since V ≠ 0
       λ² = n
 *)

(* donc il faut montrer qu'il existe des vecteurs propres; car,
   pour l'instant, les "valeurs propres" d'une matrice M sont
   définies comme étant les racines du polynôme caractéristique
   dét(xI-M); tout ce qu'on a montré, c'est que pour les racines
   (λi) de ce polynôme, on a
     dét(xI-M) = Π (i=1,n),(x-λi) *)

(* attempt by using roots of characteristic polynomial, as eigenvalues.
   Drawback: does not compute the eigenvectors which are however
   necessary for ending the lemma

Definition charac_polyn_of_roots M roots :=
  charac_polyn (mat_of_sqr_bmat M) =
    (Π (i = 1, sqr_bmat_size M),
       (_x - polyn_of_const (nth (i - 1) roots 0%Srng))%P)%Srng.

Theorem exists_A_charac_polyn_roots :
  ∀ n, ∃ roots, charac_polyn_of_roots (A n) roots.
Proof.
intros.
now apply exists_charac_polyn_roots.
Qed.

Theorem sqr_roots_A_eq_mat_sz : ∀ n roots,
  charac_polyn_of_roots (A n) roots
  → ∀ μ, μ ∈ roots → (μ * μ)%Srng = rng_mul_nat_l n 1%Srng.
Proof.
intros * Hcp * Hev.
unfold charac_polyn_of_roots in Hcp.
specialize (lemma_2_A_n_2_eq_n_I n) as Ha.
unfold charac_polyn in Hcp.
unfold xI_sub_M in Hcp.
unfold sqr_bmat_size in Hcp.
remember (mat_nrows (mat_of_sqr_bmat (A n))) as m eqn:Hm.
cbn in Hm.
rewrite Nat.sub_0_r in Hm.
rewrite sizes_of_bmatrix_A in Hm, Hcp.
rewrite repeat_length in Hm, Hcp.
replace n with (S n - 1) in Hm at 1 by flia.
rewrite fold_iter_seq in Hm.
rewrite <- Hm in Hcp.
...
*)

Definition rng_abs (lt : T → T → bool) x :=
  if lt x 0%Srng then (- x)%Rng else x.

(* https://fr.wikipedia.org/wiki/%C3%89limination_de_Gauss-Jordan#Algorithme *)

Fixpoint abs_max_in_col (lt : T → T → bool) (M : matrix T) it i j :=
  match it with
  | 0 => i
  | S it' =>
      let k := abs_max_in_col lt M it' (i + 1) j in
      if lt (rng_abs lt (mat_el M k j)) (rng_abs lt (mat_el M i j)) then i
      else k
  end.

(* Swap the positions of two rows *)
Definition swap_rows (A : matrix T) i' i'' :=
  mk_mat (λ i j,
    if Nat.eq_dec i i' then mat_el A i'' j
    else if Nat.eq_dec i i'' then mat_el A i' j
    else mat_el A i j) (mat_nrows A) (mat_ncols A).

(* Multiply a row by a non-zero scalar *)
Definition multiply_row_by_scalar A k s :=
  mk_mat (λ i j,
    if Nat.eq_dec i k then (s * mat_el A i j)%Rng
    else mat_el A i j)
    (mat_nrows A) (mat_ncols A).

(* Add to one row a scalar multiple of another *)
Definition add_one_row_scalar_multiple_another A i' s i'' :=
  mk_mat (λ i j,
    if Nat.eq_dec i i' then (mat_el A i j + s * mat_el A i'' j)%Rng
    else mat_el A i j)
    (mat_nrows A) (mat_ncols A).

(* return by Gauss-Jordan elimination the row echelon form of the
   matrix; actually, since there is no division in the present
   version of my code, it returns the pair of the echelon form
   multiplied by some constant d, and the constant d itself *)

Fixpoint rng_gauss_jordan_loop lt (A : matrix T) d r oj :=
  match oj with
  | 0 => (A, d)
  | S oj' =>
      let j := mat_ncols A - oj in
      let k := abs_max_in_col lt A (mat_nrows A - 1 - r) r j in
      if srng_eq_dec (mat_el A k j) 0 then
        rng_gauss_jordan_loop lt A d r oj'
      else
        let r := r + 1 in
        let dd := mat_el A k j in
        let A := swap_rows A (r - 1) k in
        let A :=
          fold_left
            (λ A i'',
               if Nat.eq_dec i'' (r - 1) then A
               else
                 let v := mat_el A i'' j in
                 let A := multiply_row_by_scalar A i'' dd in
                 add_one_row_scalar_multiple_another A i'' (- v)%Rng (r - 1))
            (seq 0 (mat_nrows A)) A
        in
        let A := multiply_row_by_scalar A (r - 1) d in
        rng_gauss_jordan_loop lt A (d * dd)%Srng r oj'
  end.

Definition rng_gauss_jordan lt (A : matrix T) :=
  rng_gauss_jordan_loop lt (A : matrix T) 1%Srng 0 (mat_ncols A).

(*
End in_ring.
Require Import ZArith.
Open Scope Z_scope.
Existing Instance Z_ring_op.
Existing Instance Z_semiring_op.
Existing Instance Z_sring_dec_prop.
Definition Z_gauss_jordan := rng_gauss_jordan Z.ltb.
Definition test ll :=
  let r := Z_gauss_jordan (mat_of_list_list 0 ll) in
  (list_list_of_mat (fst r), snd r).
Compute test [[2; -1; 0]; [-1; 2; -1]; [0; -1; 2]].
(*
     = ([[48; 0; 0]; [0; 48; 0]; [0; 0; 48]], 48)
*)
Compute test [[1;3;1;9];[1;1;-1;1];[3;11;5;35]].
(*
     = ([[-24; 0; 48; 72]; [0; -24; -24; -96]; [0; 0; 0; 0]], -24)
*)
Compute test [[2;1;-1;8];[-3;-1;2;-11];[-2;1;2;-3]].
(*
     = ([[45; 0; 0; 90]; [0; 45; 0; 135]; [0; 0; 45; -45]], 45)
*)
Compute test [[2;-1;0;1;0;0];[-1;2;-1;0;1;0];[0;-1;2;0;0;1]].
(*
     = ([[48; 0; 0; 36; 24; 12];
         [0; 48; 0; 24; 48; 24];
         [0; 0; 48; 12; 24; 36]], 48)
*)
Compute test [[5;2;1;0];[-7;-3;0;1]].
(*
     = ([[-7; 0; -21; -14]; [0; -7; 49; 35]], -7)
     = ([[1; 0; 3; 2]; [0; 1; -7; -5]], -7)
*)
Compute test [[-3;-3;3;0];[3;-9;3;0];[6;-6;0;0]].
(*
     = ([[-216; 0; 108; 0]; [0; -216; 108; 0]; [0; 0; 0; 0]], -216)
     = ([[1; 0; -1/2; 0]; [0; 1; -1/2; 0]; [0; 0; 0; 0]], 1)
   1 0 -1/2
   0 1 -1/2
   0 0  0
*)
Compute test [[3;-3;3;0];[3;-3;3;0];[6;-6;6;0]].
(*
     = ([[6; -6; 6; 0]; [0; 0; 0; 0]; [0; 0; 0; 0]], 6)
*)
Compute test [[1;-1;2;5];[3;2;1;10];[2;-3;-2;-10]].
(*
     = ([[4095; 0; 0; 4095]; [0; 4095; 0; 8190]; [0; 0; 4095; 12285]], 4095)
     = ([[1; 0; 0; 1]; [0; 1; 0; 2]; [0; 0; 1; 3]], 1)
*)
Compute test [[1;2;2;-3;2;3];[2;4;1;0;-5;-6];[4;8;5;-6;-1;0];[-1;-2;-1;1;1;1]].
(*
     = ([[-24; -48; 0; -24; 96; 120]; [0; 0; -24; 48; -72; -96];
        [0; 0; 0; 0; 0; 0]; [0; 0; 0; 0; 0; 0]], -24)
*)
*)

(* let's go for the fields *)

Class field_op T :=
  { (*fld_ring : ring_op T;*)
    fld_inv : T → T }.

Definition fld_div T {fo : field_op T} {so : semiring_op T} a b :=
  srng_mul a (fld_inv b).

Declare Scope field_scope.

Delimit Scope field_scope with F.
Notation "0" := srng_zero : field_scope.
Notation "1" := srng_one : field_scope.
Notation "- a" := (rng_opp a) : field_scope.
Notation "/ a" := (fld_inv a) : field_scope.
Notation "a + b" := (srng_add a b) : field_scope.
Notation "a - b" := (rng_sub a b) : field_scope.
Notation "a * b" := (srng_mul a b) : field_scope.
Notation "a / b" := (fld_div a b) : field_scope.

(*
Class field_prop A {so : ring_op A} :=
  { rng_add_opp_l : ∀ a : A, (- a + a = 0)%Rng }.
*)
Context {fo : field_op T}.

Fixpoint gauss_jordan_loop lt (A : matrix T) r oj :=
  match oj with
  | 0 => A
  | S oj' =>
      let j := mat_ncols A - oj in
      let k := abs_max_in_col lt A (mat_nrows A - 1 - r) r j in
      if srng_eq_dec (mat_el A k j) 0 then
        gauss_jordan_loop lt A r oj'
      else
        let r := r + 1 in
        let A := multiply_row_by_scalar A k (/ mat_el A k j)%F in
        let A := swap_rows A (r - 1) k in
        let A :=
          fold_left
            (λ A i'',
               if Nat.eq_dec i'' (r - 1) then A
               else
                 let v := mat_el A i'' j in
                 add_one_row_scalar_multiple_another A i'' (- v)%Rng (r - 1))
            (seq 0 (mat_nrows A)) A
        in
        gauss_jordan_loop lt A r oj'
  end.

Definition gauss_jordan lt (A : matrix T) :=
  gauss_jordan_loop lt (A : matrix T) 0 (mat_ncols A).

(**)
End in_ring.

Import Q.Notations.

Definition Q_semiring_op : semiring_op Q :=
  {| srng_zero := 0%Q;
     srng_one := 1%Q;
     srng_add := Q.add;
     srng_mul := Q.mul |}.

Definition Q_ring_op : ring_op Q :=
  {| rng_opp := Q.opp |}.

Canonical Structure Q_semiring_op.
Canonical Structure Q_ring_op.

Theorem Q_1_neq_0 : 1%Q ≠ 0%Q.
Proof. easy. Qed.

Definition Q_sring_dec_prop : sring_dec_prop Q :=
  {| srng_eq_dec := Q.eq_dec; srng_1_neq_0 := Q_1_neq_0 |}.

Definition Q_field_op : field_op Q :=
  {| fld_inv := Q.inv |}.

Existing Instance Q_ring_op.
Existing Instance Q_semiring_op.
Existing Instance Q_sring_dec_prop.
Existing Instance Q_field_op.
Definition Q_ltb a b :=
  match Q.compare a b with Lt => true | _ => false end.
Definition Q_gauss_jordan := gauss_jordan Q_ltb.
Definition qtest ll :=
  let r := Q_gauss_jordan (mat_of_list_list 0%Q ll) in
  list_list_of_mat r.
Require Import GQ PQ.
Import GQ_Notations PQ_Notations.
Compute qtest [[1]]%Q.
Compute qtest [[1; -1]; [1; 1]]%Q.
Compute qtest [[2; -1; 0]; [-1; 2; -1]; [0; -1; 2]]%Q.
(*
     = ([[48; 0; 0]; [0; 48; 0]; [0; 0; 48]], 48)
*)
Compute qtest [[2; -1; 0]; [-1; 2; -1]; [0; -1; 2]]%Q.
(*
     = ([[48; 0; 0]; [0; 48; 0]; [0; 0; 48]], 48)
*)
Compute qtest [[-3;-3;3;0];[3;-9;3;0];[6;-6;0;0]]%Q.
(*
     = ([[-216; 0; 108; 0]; [0; -216; 108; 0]; [0; 0; 0; 0]], -216)
     = ([[1; 0; -1/2; 0]; [0; 1; -1/2; 0]; [0; 0; 0; 0]], 1)
   1 0 -1/2
   0 1 -1/2
   0 0  0
*)
Compute qtest [[1;-1;2;5];[3;2;1;10];[2;-3;-2;-10]]%Q.
(*
     = ([[4095; 0; 0; 4095]; [0; 4095; 0; 8190]; [0; 0; 4095; 12285]], 4095)
     = ([[1; 0; 0; 1]; [0; 1; 0; 2]; [0; 0; 1; 3]], 1)
*)
(* comment faire pour que
     Pos {| PQ_of_GQ := 1; GQprop := eq_refl |}
   affiche
     1
   éventuellement
     1%Q
   ou alors
     1%QS
   (S pour "Spécial")
   Et que
     Pos {| PQ_of_GQ := {| PQnum1 := 0; PQden1 := 1 |}; GQprop := eq_refl |}
   affiche
     (1 // 2)%QS
*)
(*
Notation "a /// b" := (PQmake (a - 1) (b - 1)) (at level 32) : PQ_scope.
*)
Notation "a /// b" := (PQmake a b) (at level 32) : PQ_scope.
Compute (2 // 5)%Q.
(* bof, pas terrible, ça affiche évidemment 1 /// 4 mais pour faire
   afficher 2 /// 5, c'est plus compliqué... va falloir ajouter un
   Set Numeral Notation adapté, mais je suis pas sûr que ce soit
   possible. *)
