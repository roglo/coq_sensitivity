(* Lemma 2.2 of the proof of the sensitivity conjecture *)
(* sequence A_n of matrices and the proof their square is "n * I_n" *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.
(*
Require Import Init.Nat.
Require Import Relations.
*)

Require Import Misc Matrix.
Require Import Semiring.
Require Import SRproduct.
Require Import SRpolynomial.
Require Import BlockMat CharacPolyn.
Import polynomial_Notations.
Import bmatrix_Notations.

Section in_ring.

Context {T : Type}.
Context {ro : ring_op T}.
Context (so := rng_semiring).
Context {sp : @semiring_prop T (@rng_semiring T ro)}.
Context {rp : @ring_prop T ro}.
Context {sdp : @sring_dec_prop T so}.
Context {acp : @algeb_closed_prop T so sdp}.
Existing Instance so.
Existing Instance polyn_semiring_op.

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
unfold so.
rewrite bmat_zero_like_opp; [ easy | ].
apply A_is_square_bmat.
Qed.

Theorem Tr_A : ∀ n, Tr (A n) = 0%Srng.
Proof.
intros.
(*
revert n.
apply nat_ind; [ | intros n IHn ]; [ easy | ].
*)
induction n; [ easy | cbn ].
rewrite IHn.
do 2 rewrite srng_add_0_l.
unfold so.
rewrite Tr_opp; [ | apply A_is_square_bmat ].
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
    rewrite bmat_nat_mul_l_succ.
    rewrite <- IHn.
    unfold so.
    rewrite bmat_mul_1_r; [ | easy ].
    f_equal.
    rewrite <- bmat_zero_like_sqr; [ | apply A_is_square_bmat ].
    apply bmat_add_0_l.
  }
  destruct j; [ cbn | flia Hj ].
  rewrite bmat_nat_mul_l_succ.
  unfold so.
  rewrite bmat_mul_1_r. 2: {
    unfold I_2_pow.
    apply bmat_fit_for_add_IZ_A.
  }
  rewrite bmat_mul_1_l. 2: {
    unfold I_2_pow.
    transitivity (A n); [ apply bmat_fit_for_add_IZ_A | ].
    apply bmat_fit_for_add_opp_r.
  }
  rewrite bmat_add_0_l.
  rewrite bmat_add_opp_r.
  rewrite fold_Z_2_pow.
  rewrite old_bmat_add_0_r. 2: {
    now apply bmat_fit_for_add_Z_2_pow_bmat_nat_mul_l.
  }
  rewrite bmat_nat_mul_0_r.
  now apply bmat_zero_like_A_eq_Z.
}
destruct i; [ | flia Hi ].
destruct j; cbn. {
  unfold so.
  rewrite bmat_mul_1_l. 2: {
    apply bmat_fit_for_add_IZ_A.
  }
  rewrite bmat_mul_1_r. 2: {
    transitivity (A n); [ | apply bmat_fit_for_add_opp_r ].
    apply bmat_fit_for_add_IZ_A.
  }
  rewrite bmat_add_0_l.
  rewrite bmat_add_opp_r.
  rewrite bmat_nat_mul_l_succ.
  rewrite fold_Z_2_pow.
  rewrite bmat_nat_mul_0_r.
  rewrite old_bmat_add_0_r; [ | easy ].
  now apply bmat_zero_like_A_eq_Z.
}
destruct j; [ cbn | flia Hj ].
unfold so.
rewrite bmat_mul_1_l; [ | easy ].
rewrite bmat_mul_sqr_opp; [ | apply A_is_square_bmat ].
rewrite bmat_nat_mul_l_succ.
rewrite <- IHn.
rewrite bmat_zero_like_A_eq_Z.
rewrite old_bmat_add_0_l; [ | apply bmat_fit_for_add_IZ_IZ ].
apply bmat_add_comm.
transitivity (A n). 2: {
  apply (is_square_bmat_fit_for_add (sizes_of_bmatrix (A n))). {
    apply A_is_square_bmat.
  }
  apply is_square_bmat_loop_mul; apply A_is_square_bmat.
}
apply bmat_fit_for_add_IZ_A.
Qed.

Theorem is_square_bmat_is_square_mat : ∀ BM,
  is_square_bmat BM → is_square_mat (mat_of_bmat BM).
Proof.
intros * Hsbm.
...

Theorem exists_A_eigenvalues : ∀ n,
  ∃ EVL,
  charac_polyn (mat_of_bmat (A n)) =
    (Π (i = 1, bmat_nrows (A n)),
       (_x - polyn_of_const (nth (i - 1) EVL 0%Srng))%P)%Srng.
Proof.
intros.
apply exists_eigenvalues.
...
unfold is_square_mat.
specialize (A_is_square_bmat n) as H1.
unfold is_square_bmat in H1.
Print is_square_bmat_loop.
Search A_is_square_bmat.
...
