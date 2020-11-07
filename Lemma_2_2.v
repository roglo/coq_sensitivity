(* Lemma 2.2 of the proof of the sensitivity conjecture *)
(* sequence A_n of matrices and the proof their square is "n * I_n" *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Misc Matrix BlockMat.
Require Import Semiring Field2.
Import matrix_Notations.
Import bmatrix_Notations.

Section in_ring.

Context {T : Type}.
Context (so : semiring_op T).
Context {ro : ring_op T}.
Context {sp : semiring_prop T}.
Context {rp : ring_prop T}.
Context {sdp : sring_dec_prop T}.
Context {fo : field_op T}.
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

(* https://fr.wikipedia.org/wiki/%C3%89limination_de_Gauss-Jordan#Algorithme *)
(* but taking any non zero value in the column instead of the maximum one
   in absolute value, because taking the maximum is just for computation,
   not for mathematics *)

Fixpoint first_non_zero_in_col (M : matrix T) it i j :=
  match it with
  | 0 => None
  | S it' =>
      if srng_eq_dec (mat_el M i j) 0 then
        first_non_zero_in_col M it' (i + 1) j
      else Some i
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

Definition gauss_jordan_step A i j k :=
  let A' := swap_rows A i k in
  let A'' := multiply_row_by_scalar A' i (/ mat_el A' i j)%F in
  fold_left
    (λ B i',
       if Nat.eq_dec i' i then B
       else
         let v := mat_el B i' j in
         add_one_row_scalar_multiple_another B i' (- v)%Rng i)
    (seq 0 (mat_nrows A'')) A''.

Fixpoint gauss_jordan_loop (A : matrix T) i j it :=
  match it with
  | 0 => A
  | S it' =>
      match first_non_zero_in_col A (mat_nrows A - i) i j with
      | Some k =>
          let A' := gauss_jordan_step A i j k in
          gauss_jordan_loop A' (i + 1) (j + 1) it'
      | None =>
          gauss_jordan_loop A i (j + 1) it'
      end
  end.

Definition gauss_jordan (A : matrix T) :=
  gauss_jordan_loop (A : matrix T) 0 0 (mat_ncols A).

(* matrix whose k-th column is replaced by a vector *)

Definition mat_repl_vect k (M : matrix T) V :=
  mk_mat (λ i j, if Nat.eq_dec j k then vect_el V i else mat_el M i j)
    (mat_nrows M) (mat_ncols M).

(* resolve a system of n equations with n variables whose determinant
   is not zero; Cramer's method *)

Definition resolve_system (M : matrix T) (V : vector T) :=
  map (λ j, (determinant (mat_repl_vect j M V) / determinant M)%F)
    (seq 0 (mat_ncols M)).

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

(* resolving a system of n equations with n variables even
   in the case when the determinant is 0 *)
(* returns one only solution (if any); to return the set of solutions,
   we must build a field holding constants a, b, c, etc.; polynomials
   could help but we need polynomials with several variables *)

Fixpoint resolve_loop n (M : matrix T) (V : vector T) :=
  match n with
  | 0 => []
  | S n' =>
      if srng_eq_dec (determinant M) 0%Srng then
        let MV := mat_vect_concat M V in
        let A := gauss_jordan MV in
        (* deletion last row which, normally, contains only zeros
           and the last variable is given the value 1 *)
        let B := mk_mat (mat_el A) (mat_nrows M - 1) (mat_ncols M - 1) in
        let U :=
          let rhs :=
            mk_vect (vect_el (vect_of_mat_col A (mat_ncols M)))
              (mat_nrows M - 1)
          in
          let last_col :=
            mk_vect (vect_el (vect_of_mat_col A (mat_ncols M - 1)))
              (mat_nrows M - 1)
          in
          vect_sub rhs last_col
        in
        resolve_loop n' B U ++ [1%Srng]
      else
        (* resolve for example by Cramer the system of equations Mx=V *)
        resolve_system so M V
  end.

Definition resolve (M : matrix T) V := resolve_loop (mat_nrows M) M V.

(* trucs à prouver:
   1/ que le résultat de gauss_jordan donne bien une matrice échelonnée
      réduite
   2/ que, pour un matrice carrée, si le déterminant est nul, alors la
      dernière ligne de son gauss_jordan est nulle; si la matrice est
      bien échelonnée réduite, la dernière ligne contient au moins n-1
      zéros; il resterait à prouver que le dernier coefficient est bien
      nul lui aussi
   3/ est-il possible que la réciproque soit vraie ? que si la dernière
      ligne n'est composée que de 0, alors c'est que le déterminant de
      la matrice initiale est nul ? *)

(* pivot *)

Fixpoint pivot_index_loop (M : matrix T) i j it :=
  match it with
  | 0 => j
  | S it' =>
      if srng_eq_dec (mat_el M i j) 0 then pivot_index_loop M i (j + 1) it'
      else j
  end.

Definition pivot_index (M : matrix T) i :=
  pivot_index_loop M i 0 (mat_ncols M).

(* row echelon form *)
(* a matrix is in row echelon form if the pivot shifts at each row *)

Definition in_row_echelon_form (M : matrix T) :=
  ∀ i, i < mat_nrows M - 1 → pivot_index M i < pivot_index M (i + 1).

(* reduced row echelon form *)
(* a matrix is in reduced row echelon form if
   1/ it is in row echelon form
   2/ the column of pivots hold 1 at pivot and 0 everywhere else
*)

Definition in_reduced_row_echelon_form (M : matrix T) :=
  in_row_echelon_form M ∧
  (∀ i, i < mat_nrows M → ∀ k, k < mat_nrows M →
   mat_el M k (pivot_index M i) = if Nat.eq_dec k i then 1%Srng else 0%Srng).

(* proof that Gauss-Jordan algorithm returns a matrix in row
   echelon form *)

(* to be moved to Misc.v *)
Theorem List_app_fold_left : ∀ A B x l (f : B → A → B) (g : B → A),
  (∀ y i, i ∈ l → g (f y i) = g y)
  → g (fold_left f l x) = g x.
Proof.
intros A * Hg.
revert x.
induction l as [| y]; intros; [ easy | cbn ].
rewrite IHl. 2: {
  intros z i Hi.
  now apply Hg; right.
}
now apply Hg; left.
Qed.

Theorem gauss_jordan_step_nrows : ∀ M i j k,
  mat_nrows (gauss_jordan_step so M i j k) = mat_nrows M.
Proof.
intros.
unfold gauss_jordan_step.
rewrite List_app_fold_left; [ easy | ].
intros A h Hh.
now destruct (Nat.eq_dec h i).
Qed.

Theorem gauss_jordan_loop_nrows : ∀ M i j it,
  mat_nrows (gauss_jordan_loop M i j it) = mat_nrows M.
Proof.
intros.
revert M i j.
induction it; intros; [ easy | ].
cbn - [ gauss_jordan_step ].
remember (first_non_zero_in_col _ _ _ _) as k eqn:Hk.
symmetry in Hk.
destruct k as [k| ]. {
  rewrite IHit.
  apply gauss_jordan_step_nrows.
}
apply IHit.
Qed.

Theorem gauss_jordan_nrows : ∀ M,
  mat_nrows (gauss_jordan M) = mat_nrows M.
Proof.
intros.
apply gauss_jordan_loop_nrows.
Qed.

Theorem gauss_jordan_in_reduced_row_echelon_form : ∀ (M : matrix T),
  mat_ncols M ≠ 0
  → in_reduced_row_echelon_form (gauss_jordan M).
Proof.
intros * Hcz.
split. 2: {
  intros i Hi k Hk.
  move k before i.
  rewrite gauss_jordan_nrows in Hi, Hk.
  destruct (Nat.eq_dec k i) as [Hki| Hki]. {
    subst k; clear Hk.
    unfold gauss_jordan.
    remember (mat_ncols M) as c eqn:Hc; symmetry in Hc.
    destruct c; [ easy | clear Hcz ].
    cbn - [ gauss_jordan_step ].
    rewrite Nat.sub_0_r.
    remember (mat_nrows M) as r eqn:Hr; symmetry in Hr.
    move Hr after Hc.
    destruct r; [ easy | ].
    cbn - [ gauss_jordan_step ].
    destruct (srng_eq_dec (mat_el M 0 0) 0) as [Hmz| Hmz]. {
      remember (first_non_zero_in_col _ _ _ _) as k eqn:Hk.
      symmetry in Hk.
      destruct k as [k| ]. {
        remember (gauss_jordan_loop _ _ _ _) as A eqn:HA.
        revert M A c i k Hi Hr Hc Hmz Hk HA.
        induction r; intros; [ easy | ].
        rename A0 into A.
        cbn in Hk.
        destruct (srng_eq_dec (mat_el M 1 0) 0) as [Hm1z| Hm1z]. {
          destruct i. {
            clear IHr Hi.
...

End in_field.
