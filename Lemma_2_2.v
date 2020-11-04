(* Lemma 2.2 of the proof of the sensitivity conjecture *)
(* sequence A_n of matrices and the proof their square is "n * I_n" *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Misc Matrix BlockMat.
Require Import Semiring Field2.
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
Require Import ZArith Zring.
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
        let r' := r + 1 in
        let A' := multiply_row_by_scalar A k (/ mat_el A k j)%F in
        let A'' := swap_rows A' (r' - 1) k in
        let A''' :=
          fold_left
            (λ B i'',
               if Nat.eq_dec i'' (r' - 1) then B
               else
                 let v := mat_el B i'' j in
                 add_one_row_scalar_multiple_another B i'' (- v)%Rng (r' - 1))
            (seq 0 (mat_nrows A'')) A''
        in
        gauss_jordan_loop lt A''' r' oj'
  end.

Definition gauss_jordan lt (A : matrix T) :=
  gauss_jordan_loop lt (A : matrix T) 0 (mat_ncols A).

(*
End in_ring.
Require Import Qfield2.
Check Q_semiring_op.
Import Q.Notations.
Open Scope Q_scope.
Existing Instance Q_semiring_op.
Existing Instance Q_ring_op.
Existing Instance Q_sring_dec_prop.
Existing Instance Q_field_op.
Definition Q_ltb a b :=
  match Q.compare a b with Lt => true | _ => false end.
Definition Q_gauss_jordan := gauss_jordan Q_ltb.
Definition qtest ll :=
  let r := Q_gauss_jordan (mat_of_list_list 0%Q ll) in
  list_list_of_mat r.
Compute qtest [[1]].
Check (2 + 3//2).
Compute (2 + 3//2).
Compute (2 + 2).
Compute qtest [[2; -1; 0]; [-1; 2; -1]; [0; -1; 2]].
(*
     = ([[48; 0; 0]; [0; 48; 0]; [0; 0; 48]], 48)
*)
Compute qtest [[1;3;1;9];[1;1;-1;1];[3;11;5;35]].
(*
     = ([[-24; 0; 48; 72]; [0; -24; -24; -96]; [0; 0; 0; 0]], -24)
*)
Compute qtest [[2;1;-1;8];[-3;-1;2;-11];[-2;1;2;-3]].
(*
     = ([[45; 0; 0; 90]; [0; 45; 0; 135]; [0; 0; 45; -45]], 45)
*)
Compute qtest [[2;-1;0;1;0;0];[-1;2;-1;0;1;0];[0;-1;2;0;0;1]].
(*
     = ([[48; 0; 0; 36; 24; 12];
         [0; 48; 0; 24; 48; 24];
         [0; 0; 48; 12; 24; 36]], 48)
*)
Compute qtest [[5;2;1;0];[-7;-3;0;1]].
(*
     = ([[-7; 0; -21; -14]; [0; -7; 49; 35]], -7)
     = ([[1; 0; 3; 2]; [0; 1; -7; -5]], -7)
*)
Compute qtest [[-3;-3;3];[3;-9;3];[6;-6;0]].
(*
     = [[〈1〉; 0; 〈-1╱2〉]; [0; 〈1〉; 〈-1╱2〉]; [0; 0; 0]]
   1 0 -1/2
   0 1 -1/2
   0 0  0
*)
Compute qtest [[3;-3;3];[3;-3;3];[6;-6;6]].
(*
     = ([[6; -6; 6]; [0; 0; 0]; [0; 0; 0]], 6)
*)
Compute qtest [[1;-1;2;5];[3;2;1;10];[2;-3;-2;-10]].
(*
     = ([[4095; 0; 0; 4095]; [0; 4095; 0; 8190]; [0; 0; 4095; 12285]], 4095)
     = ([[1; 0; 0; 1]; [0; 1; 0; 2]; [0; 0; 1; 3]], 1)
*)
Compute qtest [[1;2;2;-3;2;3];[2;4;1;0;-5;-6];[4;8;5;-6;-1;0];[-1;-2;-1;1;1;1]].
(*
     = ([[-24; -48; 0; -24; 96; 120]; [0; 0; -24; 48; -72; -96];
        [0; 0; 0; 0; 0; 0]; [0; 0; 0; 0; 0; 0]], -24)
*)
Check (355//113)%Q.
Compute (355//113)%Q.
Require Import CharacPolyn.
Require Import SRpolynomial.
Definition Q_semiring_prop :=
  {| srng_add_comm := Q.add_comm;
     srng_add_assoc := Q.add_assoc;
     srng_add_0_l := Q.add_0_l;
     srng_mul_comm := Q.mul_comm;
     srng_mul_assoc := Q.mul_assoc;
     srng_mul_1_l := Q.mul_1_l;
     srng_mul_add_distr_l := Q.mul_add_distr_l;
     srng_mul_0_l := Q.mul_0_l |}.
Definition Q_ring_prop := {| rng_add_opp_l := Q.add_opp_diag_l |}.
Existing Instance Q_semiring_prop.
Existing Instance Q_ring_prop.

(* trying to find eigenvalues and eigenvector on an example *)
Definition qcp ll := polyn_list (charac_polyn (mat_of_list_list 0 ll)).
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
Compute qtest [[-1;-3];[2;6]].
(*
     = [[〈1〉; 〈3〉]; [0; 0]]
x₁+3x₂=0
I must resolve this system "by hand". Is there a general algorithm to
resolve it?
x₁=-3x₂
vector (-3, 1)
*)
Definition qtest_mul_m_v m v :=
  list_of_vect (mat_mul_vect_r (mat_of_list_list 0 m) (vect_of_list 0 v)).
Compute qtest_mul_m_v [[4;3];[-2;-3]] [-3;1].
(*
     = [〈-9〉; 〈3〉]
    Indeed, [-3;1] is an eigenvector
*)
(*
2/ λ=-2
   λI-M=[[-6;-3];[2;1]]
*)
Compute qtest [[-6;-3];[2;1]].
(*
     = [[〈1〉; 〈1╱2〉]; [0; 0]]
x₁+1/2x₂=0
I must resolve this system "by hand". Is there a general algorithm to
resolve it?
x₂=-2x₁
vector (1,-2)
*)
Compute qtest_mul_m_v [[4;3];[-2;-3]] [1;-2].
(*
     = [〈-2〉; 〈4〉]
    Indeed, [1;-2] is an eigenvector
*)

(* https://en.wikipedia.org/wiki/Kernel_(linear_algebra)#Illustration *)
Compute qtest [[2;3;5];[-4;2;3]].
(*
     = [[〈1〉; 0; 〈1╱16〉]; [0; 〈1〉; 〈13╱8〉]]

  Good! matches what is written in the wikipedia page.
*)

Compute qtest [[1;2;2;2];[1;3;-2;-1];[3;5;8;8]].
Compute qtest [[2;3;1;1];[3;1;5;2];[4;-1;-1;0]].
Compute qtest [[2;3;1;1];[0;-7;7;1];[0;-7;-3;-2]].
Compute qtest [[3;3;3;18];[-1;3;7;-10];[1;3;4;6]].
Compute qtest [[0;0;2;-2;8;-6];[1;2;1;0;5;-1];[-2;-4;-1;0;-8;-1]].
Compute qtest [[4;6;6];[1;3;2];[-1;-5;-2]].
Compute qcp [[4;6;6];[1;3;2];[-1;-5;-2]].
Compute qtest_mul_m_v [[4;6;6];[1;3;2];[-1;-5;-2]] [4;1;-3].
Compute qtest_mul_m_v [[4;6;6];[1;3;2];[-1;-5;-2]] [3;1;-2].
Compute qtest [[3;6;6];[1;2;2];[-1;-5;-3]].
Compute qcp [[3;6;6];[1;2;2];[-1;-5;-3]].

Compute qcp [[5;0;1];[1;1;0];[-7;1;0]].
(* x³-6x²+12x-8 = (x-2)³*)
Compute qtest [[-3;0;-1];[-1;1;0];[7;-1;2]].
Compute qtest [[3;0;1];[1;-1;0];[-7;1;-2]].
(* dimension of eigenvectors is 1, even if the multiplicity of 2 is 3 *)
*)

(* matrix whose k-th column is replaced by a vector *)

Definition mat_repl_vect k (M : matrix T) V :=
  mk_mat (λ i j, if Nat.eq_dec j k then vect_el V i else mat_el M i j)
    (mat_nrows M) (mat_ncols M).

(* resolve a system of n equations with n variables whose determinant
   is not zero; Cramer's method *)

Definition resolve_system (M : matrix T) (V : vector T) :=
  map (λ j, (determinant (mat_repl_vect j M V) / determinant M)%F)
    (seq 0 (mat_ncols M)).

(*
(* here, some tests on ℚ *)
End in_ring.
Require Import Qfield2.
Import Q.Notations.
Print Q.Notations.
Open Scope Q_scope.
Existing Instance Q_ring_op.
Existing Instance Q_semiring_op.
Existing Instance Q_field_op.

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
*)

(* closing the section and re-open it in order to generalize 'resolve_system'
   to any field T *)

End in_ring.

Section in_field.

Context {T : Type}.
Context {ro : ring_op T}.
Context (so : semiring_op T).
Context {sp : semiring_prop T}.
Context {rp : ring_prop T}.
Context {sdp : sring_dec_prop T}.
Context {fo : field_op T}.

Print resolve_system.

Definition vect_of_mat_col (M : matrix T) j :=
  mk_vect (λ i, mat_el M i j) (mat_nrows M).

Definition vect_add (U V : vector T) :=
  mk_vect (λ i, (vect_el U i + vect_el V i)%Srng) (vect_nrows V).
Definition vect_opp (V : vector T) :=
  mk_vect (λ i, (- vect_el V i)%Rng) (vect_nrows V).

Definition vect_sub (U V : vector T) := vect_add U (vect_opp V).

(* attempt to resolve a system of n equations with n variables even
   in the case the determinant is 0 *)

Fixpoint resolve_loop lt n (M : matrix T) (V : vector T) :=
  match n with
  | 0 => None
  | S n' =>
      let A := gauss_jordan lt M in
      if srng_eq_dec (determinant A) 0%Srng then
        (* deletion last row which contains only zeros (mat_nrows A - 1),
           and last variable becomes a constant (mat_ncols A - 1) *)
        let B := mk_mat (mat_el A) (mat_nrows A - 1) (mat_ncols A - 1) in
        resolve_loop lt n' B
          (vect_sub V
...
             (vect_mul_scalar_l (vect_of_mat_col M 0) _x))
      else
        (* resolve for example by Cramer the system of equations Mx=V *)
        Some (resolve_system so M V)
  end.

Set Printing All.
Print resolve_loop.
