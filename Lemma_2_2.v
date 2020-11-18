(* Lemma 2.2 of the proof of the sensitivity conjecture *)
(* sequence A_n of matrices and the proof their square is "n * I_n" *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Misc Matrix BlockMat.
Require Import Semiring Field2.
Require Import SRsummation SRproduct SRpolynomial.
Require Import CharacPolyn.
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

Add Parametric Relation : _ (@bmat_fit_for_add T)
 reflexivity proved by bmat_fit_for_add_refl
 symmetry proved by bmat_fit_for_add_symm
 transitivity proved by bmat_fit_for_add_trans
 as bmat_fit_for_add_equivalence.

(* sequence "An" *)

Fixpoint mA n : bmatrix T :=
  match n with
  | 0 => BM_1 0%Srng
  | S n' =>
       BM_M
         (mat_of_list_list (BM_1 0%Srng)
            [[mA n'; I_2_pow n'];
             [I_2_pow n'; bmat_opp (mA n')]])
  end.

Theorem bmat_fit_for_add_IZ_A : ∀ u n,
  bmat_fit_for_add (IZ_2_pow u n) (mA n).
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
transitivity (mA n); [ easy | ].
apply bmat_fit_for_add_opp_r.
Qed.

Theorem sizes_of_bmatrix_A : ∀ n,
  sizes_of_bmatrix (mA n) = repeat 2 n.
Proof.
intros.
induction n; [ easy | now cbn; f_equal ].
Qed.

Theorem A_is_square_bmat : ∀ n,
  is_square_bmat (mA n).
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
  ∀ n, bmat_zero_like (mA n) = Z_2_pow n.
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

Theorem Tr_A : ∀ n, Tr (mA n) = 0%Srng.
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
  (mA n * mA n = bmat_nat_mul_l n (I_2_pow n))%BM.
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
    transitivity (mA n); [ apply bmat_fit_for_add_IZ_A | ].
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
    transitivity (mA n); [ | apply bmat_fit_for_add_opp_r ].
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
transitivity (mA n). 2: {
  apply (is_square_bmat_fit_for_add (sizes_of_bmatrix (mA n))). {
    apply A_is_square_bmat.
  }
  apply is_square_bmat_loop_mul; apply A_is_square_bmat.
}
apply bmat_fit_for_add_IZ_A.
Qed.

Fixpoint first_non_zero_in_col (M : matrix T) it i j :=
  match it with
  | 0 => None
  | S it' =>
      if srng_eq_dec (mat_el M i j) 0 then
        first_non_zero_in_col M it' (i + 1) j
      else Some i
  end.

Theorem first_non_zero_Some : ∀ M it i j k,
  first_non_zero_in_col M it i j = Some k
  → k < i + it ∧
    (∀ h, i ≤ h < k → mat_el M h j = 0%Srng) ∧
    mat_el M k j ≠ 0%Srng.
Proof.
intros * Hk.
revert i j k Hk.
induction it; intros; [ easy | cbn ].
cbn in Hk.
destruct (srng_eq_dec (mat_el M i j) 0) as [Hmz| Hmz]. {
  specialize (IHit _ _ _ Hk) as H1.
  destruct H1 as (H1 & H2 & H3).
  rewrite <- Nat.add_assoc in H1.
  split; [ easy | ].
  split; [ | easy ].
  intros h Hh.
  destruct (Nat.eq_dec i h) as [Hih| Hih]; [ now subst h | ].
  apply H2; flia Hh Hih.
}
injection Hk; intros; subst k.
split; [ flia | ].
split; [ flia | easy ].
Qed.

Theorem first_non_zero_None : ∀ M it i j,
  mat_nrows M ≤ i + it
  → first_non_zero_in_col M it i j = None
  → ∀ h, i ≤ h < mat_nrows M → mat_el M h j = 0%Srng.
Proof.
intros * Hm Hz h Hh.
revert i j h Hz Hh Hm.
induction it; intros; [ flia Hh Hm | ].
cbn in Hz.
destruct (srng_eq_dec (mat_el M i j) 0) as [Hmz| Hmz]; [ | easy ].
destruct (Nat.eq_dec i h) as [Hih| Hih]; [ now subst h | ].
apply (IHit (i + 1)); [ easy | flia Hh Hih | flia Hm ].
Qed.

(* Matrix operator, swapping the rows i1 and i2 of a matrix.

   When multiplying this matrix with another matrix, it returns that
   other matrix where the rows i1 and i2 are swapped
     It is the identity matrix where the 1s at (i1,i1) and (i2,i2)
   are replaced by 0s, and the 0s at (i1,i2) and (i2,i1) are replaced
   by 1s.
     Example swapping rows 1 and 2 (indices start at 0) of a 5×5
   matrix
     1 0 0 0 0
     0 0 1 0 0
     0 1 0 0 0
     0 0 0 1 0
     0 0 0 0 1

   Works even if i1=i2; in that case it is the identity matrix *)

(* perhaps should be defined with "mat_swap_rows" of Matrix.v *)
Definition mat_id_swap_rows sz i1 i2 :=
  mk_mat
    (λ i j,
     if Nat.eq_dec i i1 then if Nat.eq_dec j i2 then 1%Srng else 0%Srng
     else if Nat.eq_dec i i2 then if Nat.eq_dec j i1 then 1%Srng else 0%Srng
     else if Nat.eq_dec i j then 1%Srng else 0%Srng)
    sz sz.

(* Matrix operator, multiplying row k of a matrix by a scalar s

   When multiplying this matrix with another matrix, it returns that
   other matrix where all coefficients in row k are multiplied by s.
     It is the identity matrix where the 1 at (k,k) is replaced by s.
     Example for row 3 (staring at 0) of a 5x5 matrix
       1 0 0 0 0
       0 1 0 0 0
       0 0 1 0 0
       0 0 0 s 0
       0 0 0 0 1
*)

(* perhaps redundant; see Matrix.v *)
Definition mat_id_mul_row_by_scal sz k s :=
  mk_mat
    (λ i j,
     if Nat.eq_dec i j then if Nat.eq_dec i k then s else 1%Srng
     else 0%Srng)
    sz sz.

Arguments mat_id_mul_row_by_scal sz k s%F.

(* Matrix operator, subtracting, to all rows k but row i, the row i multiplied
   by the coefficient in (k,j).

     When multiplying this matrix with another matrix, it returns that
   other matrix where all rows k (but row i) are replaced by themselves
   minus the value in row k of the same column times the value in (k,j).

     Example for row 2 column 4 where "*" contains the opposite of
   the value in the other matrix at its column 4
     1 0 * 0 0
     0 1 * 0 0
     0 0 1 0 0
     0 0 * 1 0
     0 0 * 0 1
*)

(* perhaps redundant; see Matrix.v *)
Definition mat_id_add_rows_mul_scal_row M i j :=
  mk_mat
    (λ i' j',
     if Nat.eq_dec i' j' then 1%Srng
     else if Nat.eq_dec j' i then (- mat_el M i' j)%Rng
     else 0%Srng)
   (mat_nrows M) (mat_nrows M).

(* Gauss-Jordan elimination *)

Definition gauss_jordan_step_op M i j k :=
  (mat_id_swap_rows (mat_nrows M) i k *
   mat_id_add_rows_mul_scal_row M k j *
   mat_id_mul_row_by_scal (mat_nrows M) k (/ mat_el M k j))%M.

Fixpoint gauss_jordan_loop (M : matrix T) i j it :=
  match it with
  | 0 => M
  | S it' =>
      match first_non_zero_in_col M (mat_nrows M - i) i j with
      | Some k =>
          let M' := (gauss_jordan_step_op M i j k * M)%M in
          gauss_jordan_loop M' (i + 1) (j + 1) it'
      | None =>
          gauss_jordan_loop M i (j + 1) it'
      end
  end.

Definition gauss_jordan (M : matrix T) :=
  gauss_jordan_loop (M : matrix T) 0 0 (mat_ncols M).

(* version returning the list of matrices whose product is the
   gauss-jordan elimination of the initial matrix *)

Definition gauss_jordan_step_list M i j k :=
  [mat_id_swap_rows (mat_nrows M) i k;
   mat_id_add_rows_mul_scal_row M k j;
   mat_id_mul_row_by_scal (mat_nrows M) k (/ mat_el M k j)%F].

Fixpoint gauss_jordan_list_loop (M : matrix T) i j it :=
  match it with
  | 0 => []
  | S it' =>
      match first_non_zero_in_col M (mat_nrows M - i) i j with
      | Some k =>
          let ml := gauss_jordan_step_list M i j k in
          let M' := fold_right mat_mul M ml in
          (i, j, k) :: gauss_jordan_list_loop M' (i + 1) (j + 1) it'
      | None =>
          gauss_jordan_list_loop M i (j + 1) it'
      end
  end.

Definition gauss_jordan_list (M : matrix T) :=
  gauss_jordan_list_loop M 0 0 (mat_ncols M).

Definition gauss_jordan' (M : matrix T) :=
  fold_left
    (λ A '(i, j, k),
     let ml := gauss_jordan_step_list A i j k in
     fold_right mat_mul A ml)
    (gauss_jordan_list M) M.

Theorem gauss_jordan_list_loop_gauss_jordan_loop : ∀ M i j it,
  fold_left
    (λ (A : matrix T) '(i, j, k),
       fold_right mat_mul A (gauss_jordan_step_list A i j k))
    (gauss_jordan_list_loop M i j it) M =
  gauss_jordan_loop M i j it.
Proof.
intros.
revert M i j.
induction it; intros; [ easy | ].
cbn - [ gauss_jordan_step_list ].
remember (first_non_zero_in_col M (mat_nrows M - i) i j) as k eqn:Hk.
symmetry in Hk.
destruct k as [k| ]; [ | apply IHit ].
cbn - [ gauss_jordan_step_list ].
rewrite IHit.
unfold gauss_jordan_step_op.
f_equal; cbn.
rewrite mat_mul_assoc; [ | easy ].
now apply mat_mul_assoc.
Qed.

Theorem gauss_jordan_list_gauss_jordan : ∀ (M : matrix T),
  gauss_jordan' M = gauss_jordan M.
Proof.
intros.
unfold gauss_jordan', gauss_jordan.
unfold gauss_jordan_list.
apply gauss_jordan_list_loop_gauss_jordan_loop.
Qed.

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

Arguments mat_id_swap_rows {T so}.
Arguments first_non_zero_in_col {T so sdp} M%M.
Arguments gauss_jordan_step_list {T so ro fo}.
Arguments gauss_jordan_step_op {T so ro fo}.
Arguments resolve_system {T so ro fo}.

Section in_field.

Context {T : Type}.
Context {ro : ring_op T}.
Context (so : semiring_op T).
Context {sp : semiring_prop T}.
Context {rp : ring_prop T}.
Context {sdp : sring_dec_prop T}.
Context {fo : field_op T}.
Context {fp : field_prop T}.

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
        resolve_system M V
  end.

Definition resolve (M : matrix T) V :=
  vect_of_list 0%Srng (resolve_loop (mat_nrows M) M V).

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

Definition pivot (M : matrix T) i :=
  mat_el M i (pivot_index M i).

Theorem fold_pivot : ∀ M i,
  mat_el M i (pivot_index M i) = pivot M i.
Proof. easy. Qed.

(* row echelon form *)
(* a matrix is in row echelon form if the pivot shifts at each row *)

Definition in_row_echelon_form (M : matrix T) :=
  ∀ i, i < mat_nrows M - 1 → pivot_index M (i + 1) < mat_ncols M →
  pivot_index M i < pivot_index M (i + 1).

(* reduced row echelon form *)
(* a matrix is in reduced row echelon form if
   1/ it is in row echelon form
   2/ the column of pivots hold 1 at pivot and 0 everywhere else
*)

Definition in_reduced_row_echelon_form (M : matrix T) :=
  in_row_echelon_form M ∧
  (∀ i, i < mat_nrows M → ∀ k, k < mat_nrows M →
   pivot_index M i < mat_ncols M
   → mat_el M k (pivot_index M i) = if Nat.eq_dec k i then 1%Srng else 0%Srng).

(* proof that Gauss-Jordan algorithm returns a matrix in row
   echelon form *)

Theorem gauss_jordan_step_op_nrows : ∀ M i j k,
  mat_nrows (gauss_jordan_step_op M i j k) = mat_nrows M.
Proof. easy. Qed.

Theorem gauss_jordan_step_op_ncols : ∀ M i j k,
  mat_ncols (gauss_jordan_step_op M i j k) = mat_nrows M.
Proof. easy. Qed.

Theorem gauss_jordan_loop_nrows : ∀ M i j it,
  mat_nrows (gauss_jordan_loop M i j it) = mat_nrows M.
Proof.
intros.
revert M i j.
induction it; intros; [ easy | ].
cbn - [ gauss_jordan_step_op ].
remember (first_non_zero_in_col _ _ _ _) as k eqn:Hk.
symmetry in Hk.
destruct k as [k| ]. {
  rewrite IHit.
  rewrite mat_mul_nrows.
  apply gauss_jordan_step_op_nrows.
}
apply IHit.
Qed.

Theorem gauss_jordan_loop_ncols : ∀ M i j it,
  mat_ncols (gauss_jordan_loop M i j it) = mat_ncols M.
Proof.
intros.
revert M i j.
induction it; intros; [ easy | ].
cbn - [ gauss_jordan_step_op ].
remember (first_non_zero_in_col _ _ _ _) as k eqn:Hk.
symmetry in Hk.
destruct k as [k| ]. {
  rewrite IHit.
  apply mat_mul_ncols.
}
apply IHit.
Qed.

Theorem gauss_jordan_nrows : ∀ M,
  mat_nrows (gauss_jordan M) = mat_nrows M.
Proof.
intros.
apply gauss_jordan_loop_nrows.
Qed.

Theorem gauss_jordan_ncols : ∀ M,
  mat_ncols (gauss_jordan M) = mat_ncols M.
Proof.
intros.
apply gauss_jordan_loop_ncols.
Qed.

Theorem mat_swap_row_mul_l_lemma : ∀ M i j sz,
  i < sz
  → (Σ (k = 0, sz - 1), (if Nat.eq_dec k i then 1 else 0) * mat_el M k j)%Rng
    = mat_el M i j.
Proof.
intros * His.
rewrite (srng_summation_split _ i); [ | flia His ].
rewrite srng_summation_split_last; [ | flia His ].
rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec (k - 1) i) as [H| H]; [ flia Hk H | clear H ].
  apply srng_mul_0_l.
}
rewrite srng_add_0_l.
destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
rewrite srng_mul_1_l.
rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec k i) as [H| H]; [ flia Hk H | clear H ].
  apply srng_mul_0_l.
}
apply srng_add_0_r.
Qed.

Theorem mat_id_swap_rows_mul_l : ∀ M sz i1 i2,
  sz = mat_nrows M
  → i1 < sz
  → i2 < sz
  → (mat_id_swap_rows sz i1 i2 * M)%M = mat_swap_rows M i1 i2.
Proof.
intros * Hsz Hi1s Hi2s.
apply matrix_eq; [ easy | easy | ].
cbn - [ Nat.eq_dec iter_seq ].
intros i j Hi Hj.
destruct (Nat.eq_dec i i1) as [Hii1| Hii1]. {
  now apply mat_swap_row_mul_l_lemma.
}
destruct (Nat.eq_dec i i2) as [Hii2| Hii2]. {
  now apply mat_swap_row_mul_l_lemma.
}
rewrite (srng_summation_split _ i); [ | flia Hi ].
rewrite srng_summation_split_last; [ | flia ].
destruct (Nat.eq_dec i i) as [H| H]; [ clear H | flia H ].
rewrite srng_mul_1_l.
rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec i (k - 1)) as [H| H]; [ flia Hk H | clear H ].
  apply srng_mul_0_l.
}
rewrite srng_add_0_l.
rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec i k) as [H| H]; [ flia Hk H | clear H ].
  apply srng_mul_0_l.
}
apply srng_add_0_r.
Qed.

(* Multiplicative factor for computing determinant from gauss-jordan form.
   We have
      det (M) = this_mult_fact * det (gauss_jordan M)
   We know that the determinant of a gauss_jordan form is 1 or 0.
 *)

Fixpoint det_mult_fact_from_gjl_loop (M : matrix T) i j it :=
  match it with
  | 0 => 1%Srng
  | S it' =>
      match first_non_zero_in_col M (mat_nrows M - i) i j with
      | Some k =>
          let ml := gauss_jordan_step_list M i j k in
          let M' := fold_right mat_mul M ml in
          let v :=
            ((if Nat.eq_dec i k then 1 else (- (1))) * mat_el M k j)%Rng
          in
          (v * det_mult_fact_from_gjl_loop M' (S i) (S j) it')%Srng
      | None =>
          det_mult_fact_from_gjl_loop M i (S j) it'
      end
  end.

Definition det_mult_fact_from_gjl M :=
  det_mult_fact_from_gjl_loop M 0 0 (mat_ncols M).

(* *)

Theorem resolved_with_det_neq_0 : ∀ M V R,
  is_square_mat M
  → mat_nrows M = vect_nrows R
  → determinant M ≠ 0%F
  → V = vect_of_list 0%F (resolve_system M R)
  → (M · V)%V = R.
Proof.
intros * Hsm Hmr Hdz Hv.
unfold is_square_mat in Hsm.
unfold resolve_system in Hv.
unfold mat_mul_vect_r.
apply vector_eq; [ easy | ].
cbn - [ iter_seq ].
intros i Hi.
subst V.
cbn - [ iter_seq ].
erewrite srng_summation_eq_compat; [ | easy | ]. 2: {
  intros j Hj.
  rewrite (List_map_nth_in _ 0); [ | rewrite seq_length; flia Hsm Hi Hj ].
  rewrite seq_nth; [ | flia Hsm Hi Hj ].
  rewrite Nat.add_0_l.
  easy.
}
cbn - [ iter_seq ].
(* should try to replace both determinants by a version going through
   column i0 instead of row 0: this way the sub-determinants are the
   same. *)
(* but in that case, I need that a determinant going through any row
   or any column are equal to the determinant I defined (going through
   the first row; I started that in Matrix.v, but I am blocked *)
(* well, I don't really need this theorem since my problem is about
   matrices the discriminants of which are equal to zero *)
(* but I wanted to prove it anyway, for the sport; I thought it was
   easy but it is not *)
Abort. (* for the moment
...
*)

Theorem resolved : ∀ M V R,
  is_square_mat M
  → mat_nrows M = vect_nrows R
  → V = resolve M R
  → (M · V)%V = R.
Proof.
intros * Hsm Hrr Hv.
unfold is_square_mat in Hsm.
unfold resolve in Hv.
remember (mat_nrows M) as r eqn:Hr; symmetry in Hr.
destruct r. {
  cbn in Hv.
  subst V.
  unfold mat_mul_vect_r.
  destruct R as (fr, rr).
  cbn in Hrr; subst rr; rewrite Hr.
  now apply vector_eq.
}
rename Hr into Hmr.
symmetry in Hsm, Hrr.
cbn in Hv.
destruct (srng_eq_dec (determinant M) 0) as [Hdz| Hdz]. 2: {
Abort. (* for the moment...
  apply resolved_with_det_neq_0.
...
remember (gauss_jordan_loop (mat_vect_concat M R) 0 0 (mat_ncols M + 1))
  as MGJ eqn:Hmgj.
remember
  {| mat_el :=
       mat_el (gauss_jordan_loop (mat_vect_concat M R) 0 0 (mat_ncols M + 1));
     mat_nrows := mat_nrows M - 1;
     mat_ncols := mat_ncols M - 1 |}
  as A eqn:Ha.
remember {|
             vect_el := λ i : nat,
                          mat_el
                            (gauss_jordan_loop (mat_vect_concat M R) 0 0
                               (mat_ncols M + 1)) i 
                            (mat_ncols M);
             vect_nrows := mat_nrows M - 1 |} as Vrhs eqn:Hvrhs.
remember {|
             vect_el := λ i : nat,
                          mat_el
                            (gauss_jordan_loop (mat_vect_concat M R) 0 0
                               (mat_ncols M + 1)) i 
                            (mat_ncols M - 1);
             vect_nrows := mat_nrows M - 1 |} as Vlast eqn:Hvlast.
Print resolve_loop.
...
*)

(* Eigenvector property: the fact that V is such that MV=λV *)

Definition eval_mat_polyn M x :=
  mk_mat (λ i j, eval_polyn (mat_el M i j) x) (mat_nrows M) (mat_ncols M).

Theorem eigenvector_prop : ∀ M μ V S,
  eval_polyn (charac_polyn M) μ = 0%Srng
  → S = eval_mat_polyn (xI_sub_M M) μ
  → V = resolve S (vect_zero (mat_ncols M))
  → (M · V = μ × V)%V ∧ V ≠ vect_zero (vect_nrows V).
Proof.
intros * Hμ Hs Hv.
unfold charac_polyn in Hμ.
Abort. (* for the moment...
...
specialize (resolved Hv) as H1.
...
*)

Theorem gauss_jordan_in_reduced_row_echelon_form : ∀ (M : matrix T),
  mat_ncols M ≠ 0
  → in_reduced_row_echelon_form (gauss_jordan M).
Proof.
intros * Hcz.
(*
split. {
  unfold in_row_echelon_form.
  intros i Hi Hp.
...
  Hcz : mat_ncols M ≠ 0
  Hi : i < mat_nrows (gauss_jordan M) - 1
  Hp : pivot_index (gauss_jordan M) (i + 1) < mat_ncols (gauss_jordan M)
  ============================
  pivot_index (gauss_jordan M) i < pivot_index (gauss_jordan M) (i + 1)
*)
split. 2: {
  intros i Hi k Hk Hp.
  move k before i.
  rewrite gauss_jordan_nrows in Hi, Hk.
  rewrite gauss_jordan_ncols in Hp.
  destruct (Nat.eq_dec k i) as [Hki| Hki]. {
    subst i; clear Hi.
    rewrite <- gauss_jordan_list_gauss_jordan in Hp |-*; [ | easy | easy ].
Abort. (* for the moment...
...
(*trying to prove it just for the upper left number of the matrix*)
destruct k. {
  unfold gauss_jordan in Hp |-*.
  unfold pivot_index in Hp |-*.
  rewrite gauss_jordan_loop_ncols in Hp |-*.
  remember (mat_ncols M) as it eqn:Hit; symmetry in Hit.
  destruct it; [ easy | clear Hcz ].
  cbn - [ gauss_jordan_step_op ] in Hp |-*.
  rewrite Nat.sub_0_r in Hp |-*.
  remember (first_non_zero_in_col _ _ _ _) as k1 eqn:Hk1.
  symmetry in Hk1.
  destruct k1 as [k1| ]. {
    remember (gauss_jordan_loop _ _ _ _) as A eqn:Ha.
    destruct (srng_eq_dec (mat_el A 0 0) 0) as [Hmz| Hmz]. {
      unfold gauss_jordan_step_op in Ha.
      specialize (first_non_zero_prop _ _ _ _ Hk1) as (H1 & H2 & H3).
      cbn in H1.
...
      remember (multiply_row_by_scalar _ _ _ _) as A' eqn:Ha'.
      remember (swap_rows M 0 k1) as A'' eqn:Ha''.
      assert (H4 : mat_el A'' 0 0 ≠ 0%Srng). {
        rewrite Ha''.
        cbn - [ iter_seq Nat.eq_dec ].
        rewrite srng_summation_split_first; [ | easy | flia H1 ].
        destruct (Nat.eq_dec 0 0) as [H| H]; [ clear H | easy ].
        destruct (Nat.eq_dec 0 k1) as [Hk1z| Hk1z]. {
          subst k1; rewrite srng_mul_1_l.
          rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
            intros i Hi.
            destruct (Nat.eq_dec i 0) as [Hiz| Hiz]; [ flia Hi Hiz | ].
            apply srng_mul_0_l.
          }
          now rewrite srng_add_0_r.
        }
        rewrite srng_mul_0_l, srng_add_0_l.
        rewrite (srng_summation_split _ k1); [ | flia H1 ].
        rewrite srng_summation_split_last; [ | flia Hk1z ].
        destruct (Nat.eq_dec k1 k1) as [H| H]; [ clear H | easy ].
        rewrite srng_mul_1_l.
        rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
          intros i Hi.
          destruct (Nat.eq_dec (i - 1) k1) as [H| H]; [ flia H Hi | ].
          apply srng_mul_0_l.
        }
        rewrite srng_add_0_l.
        rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
          intros i Hi.
          destruct (Nat.eq_dec i k1) as [H| H]; [ flia H Hi | ].
          apply srng_mul_0_l.
        }
        now rewrite srng_add_0_r.
      }
      assert (H5 : mat_el A' 0 0 = 1%Srng). {
        rewrite Ha', Ha''.
        cbn - [ iter_seq Nat.eq_dec ].
...
        apply fld_mul_inv_l.
        rewrite srng_summation_split_first; [ | easy | flia H1 ].
        destruct (Nat.eq_dec 0 0) as [H| H]; [ clear H | easy ].
...
        rewrite srng_mul_0_l, srng_add_0_l.
        erewrite srng_summation_eq_compat; [ | easy | ]. 2: {
          intros i Hi.
          destruct (Nat.eq_dec 0 i) as [H| H]; [ flia Hi H | clear H ].
          easy.
        }
        cbn - [ iter_seq Nat.eq_dec ].
        rewrite (srng_summation_split _ k1); [ | flia H1 ].
        destruct (Nat.eq_dec k1 0) as [Hk1z| Hk1z]. {
          exfalso; subst k1.
          (* mmm... pas si simple *)
...
        apply (first_non_zero_prop _ _ _ _ Hk1).
      }
      move Hmz at bottom.
      (* normalement, contradiction entre H4 et Hmz
         parce que gauss_jordan_loop ne modifie pas
         mat_el A' 0 0 *)
      rewrite Ha in Hmz.
      specialize (List_app_fold_left) as H5.
      specialize (H5 nat (matrix T) T A').
      specialize (H5 (seq 0 (mat_nrows M))).
      remember (λ (B : matrix T) (i' : nat),
               if Nat.eq_dec i' 0
               then B
               else
                add_one_row_scalar_multiple_another so B i'
                  (- mat_el B i' 0)%F 0) as f eqn:Hf.
      specialize (H5 f).
      specialize (H5 (λ A', mat_el (gauss_jordan_loop A' 1 1 it) 0 0)).
      cbn in H5.
      rewrite H5 in Hmz; [ clear H5 | ]. 2: {
        intros A''' i Hi.
        rewrite Hf.
        destruct (Nat.eq_dec i 0) as [Hiz| Hiz]; [ easy | ].
        destruct i; [ easy | clear Hiz ].
Theorem glop : ∀ A i j it,
  mat_el (gauss_jordan_loop A (S i) (S j) it) 0 0 = mat_el A 0 0.
Proof.
intros.
revert i j A.
induction it; intros; [ easy | ].
cbn - [ gauss_jordan_step ].
remember (first_non_zero_in_col A (mat_nrows A - S i) (S i) (S j)) as k eqn:Hk.
symmetry in Hk.
destruct k as [k| ]; [ | apply IHit ].
rewrite IHit.
unfold gauss_jordan_step.
rewrite multiply_row_by_scalar_nrows.
rewrite swap_rows_nrows.
remember (swap_rows _ _ _) as A' eqn:Ha'.
remember (multiply_row_by_scalar _ _ _ _) as A'' eqn:Ha''.
move A'' before A'.
remember (mat_nrows A) as r eqn:Hr; symmetry in Hr.
destruct r; [ easy | ].
rewrite <- (Nat.add_1_l r).
rewrite seq_app.
rewrite fold_left_app; cbn.
remember (add_one_row_scalar_multiple_another _ _ _ _ _) as A''' eqn:Ha'''.
move A''' before A''.
...
rewrite List_app_fold_left with
  (g := (λ f b c a, f a b c) (mat_el (T := T)) 0 0). 2: {
  intros A'''' i' Hi'.
  destruct (Nat.eq_dec i' (S i)) as [Hii| Hii]; [ easy | ].
  destruct i'. {
    cbn.
    rewrite <- srng_add_0_r.
    f_equal.
...
(*end trying to prove it for the upper left number of the matrix*)
...
    unfold gauss_jordan in Hp |-*.
    unfold pivot_index in Hp |-*.
    rewrite gauss_jordan_loop_ncols in Hp |-*.
    remember (mat_ncols M) as it eqn:Hit; symmetry in Hit.
    destruct it; [ easy | clear Hcz ].
    cbn - [ gauss_jordan_step ] in Hp |-*.
    rewrite Nat.sub_0_r in Hp |-*.
    remember (first_non_zero_in_col _ _ _ _) as k1 eqn:Hk1.
    symmetry in Hk1.
    destruct k1 as [k1| ]. {
      remember (gauss_jordan_loop _ _ _ _) as A eqn:Ha.
      destruct (srng_eq_dec (mat_el A k 0) 0) as [Hmz| Hmz]. {
        destruct it; [ cbn in Hp; flia Hp | ].
        cbn in Hp |-*.
        destruct (srng_eq_dec (mat_el A k 1) 0) as [Hm1z| Hm1z]. {
          destruct it; [ cbn in Hp; flia Hp | ].
          cbn in Hp |-*.
          destruct (srng_eq_dec (mat_el A k 2) 0) as [Hm2z| Hm2z]. {
            destruct it; [ cbn in Hp; flia Hp | ].
            cbn in Hp |-*.
            destruct (srng_eq_dec (mat_el A k 3) 0) as [Hm3z| Hm3z]. {
...
            }
            rewrite Ha.
            remember (S (S it)) as sit eqn:Hsit.
            cbn - [ gauss_jordan_step ].
            rewrite gauss_jordan_step_nrows.
            remember (gauss_jordan_step so M 0 0 k1) as A' eqn:Ha'.
            remember (first_non_zero_in_col A' _ 1 1) as k2 eqn:Hk2.
            symmetry in Hk2.
            move k2 before k1.
            move Hk2 before Hk1.
            move A before M; move A' before A.
            destruct k2 as [k2| ]. {
              remember (gauss_jordan_step so A' _ _ _) as A2 eqn:Ha2.
              remember (gauss_jordan_loop A2 _ _ _) as A'2 eqn:Ha'2.
              move A2 before A'; move A'2 before A2.
              move Ha2 before Ha; move Ha'2 before Ha2.
clear Hp.
rewrite Hsit in Ha'2.
(*
...
  Ha'2 : A'2 = gauss_jordan_loop A2 2 2 (S (S it))
  ============================
  mat_el A'2 k 3 = 1%F
...
*)
Theorem glop : ∀ A A' k j it i,
   A = gauss_jordan_loop A' i i (it + j)
  → pivot_index_loop A k (S j) it < it + S j
  → mat_el A k (pivot_index_loop A k (S j) it) = 1%Srng.
Proof.
intros A * Ha Hp.
revert A A' k j i Ha Hp.
induction it; intros A A' k j i Ha Hp; [ cbn in Hp; flia Hp | ].
cbn in Hp |-*.
destruct (srng_eq_dec (mat_el A k (S j)) 0) as [Hmjz| Hmjz]. {
  apply IHit with (A' := A') (i := i); [ | flia Hp ].
  now replace (it + (j + 1)) with (S it + j) by flia.
}
clear Hp.
cbn - [ gauss_jordan_step ] in Ha.
rewrite Ha.
remember (first_non_zero_in_col A' (mat_nrows A' - i) i i) as k1 eqn:Hk1.
symmetry in Hk1.
destruct k1 as [k1| ]. {
  remember (gauss_jordan_step so A' i i k1) as A'' eqn:Ha''.
  specialize (IHit A A'' 42 j (i + 1) Ha) as H1.
(* ouais, c'pas clair... *)
...
  Hmjz : mat_el A k (S j) ≠ 0%F
  ============================
  mat_el A k (S j) = 1%F
...
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
*)

(* here, I would like to prove that, knowing that An^2 = nI, the
   eigenvalues of An are √n and -√n, as the Lemma 2.2. claims *)

Arguments mat_of_sqr_bmat {T so}.
Arguments mA {T so ro}.

Fixpoint srng_of_nat n :=
  match n with
  | 0 => 0%Srng
  | S n' => (1 + srng_of_nat n')%Srng
  end.

Theorem A_eigenvalue : ∀ n μ,
  (μ * μ = srng_of_nat n)%Rng
  → ∃ V,
      V ≠ vect_zero (vect_nrows V) ∧
      (mat_of_sqr_bmat (mA n) · V = μ × V)%V.
Proof.
intros * Hμ2n.
specialize (lemma_2_A_n_2_eq_n_I n) as H1.
(* well, that formula is applied on block matrices, I should convert it
   (and prove) it on normal matrices *)
...

End in_field.
