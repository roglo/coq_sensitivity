(* Lemma 2.2 of the proof of the sensitivity conjecture *)
(* sequence A_n of matrices and the proof their square is "n * I_n" *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Misc Matrix BlockMat.
Require Import Semiring.
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
Context (so := rng_semiring).
Context {sp : @semiring_prop T (@rng_semiring T ro)}.
Context {rp : @ring_prop T ro}.
Context {sdp : @sring_dec_prop T so}.
(*
Context {acp : @algeb_closed_prop T so sdp}.
Existing Instance polyn_semiring_op.
*)
Existing Instance so.

Check srng_eq_dec.

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

Fixpoint abs_max_in_col (lt : T → T → bool) (abs : T → T)
    (M : matrix T) it i j :=
  match it with
  | 0 => i
  | S it' =>
      let k := abs_max_in_col lt abs M it' (i + 1) j in
      if lt (abs (mat_el M k j)) (abs (mat_el M i j)) then i else k
  end.

(*
Require Import ZArith.
Check Z.ltb.
Check Z.abs.
*)

Fixpoint gauss_jordan_loop lt abs (A : matrix T) d r oj :=
  match oj with
  | 0 => (A, d)
  | S oj' =>
      let j := mat_ncols A - oj in
      (*  Rechercher max(|M[i,j]|, r+1 ≤ i ≤ n).
          Noter k l'indice de ligne du maximum *)
      let k := abs_max_in_col lt abs A (mat_nrows A - 1 - r) r j in
      if srng_eq_dec (mat_el A k j) 0 then
        gauss_jordan_loop lt abs A d r oj'
      else
        let r := r + 1 in
        (* Diviser la ligne k par A[k,j] *)
        (* aïe... j'ai pas encore de division, bon, tant pis, on
           multiplie les autres et on divisera plus tard l'ensemble
           par A[k,j] *)
        let dd := mat_el A k j in
        let nd := (d * dd)%Srng in
        (* Si k≠r alors  Échanger les lignes k et r *)
        let A :=
          if Nat.eq_dec k (r - 1) then A
          else
            mk_mat (λ i j,
              if Nat.eq_dec i (r - 1) then mat_el A k j
              else if Nat.eq_dec i k then mat_el A (r - 1) j
              else mat_el A i j) (mat_nrows A) (mat_ncols A)
        in
        (* Pour i de 1 jusqu'à n
           Si i≠r alors
            Soustraire à la ligne i la ligne r multipliée par A[i,j]
            (de façon à annuler A[i,j]) *)
        let A :=
          mk_mat (λ i' j',
            if Nat.eq_dec i' (r - 1) then (mat_el A i' j' * d)%Rng
            else
              (mat_el A i' j' * dd - mat_el A i' j * mat_el A (r - 1) j')%Rng)
            (mat_nrows A) (mat_ncols A)
        in
        gauss_jordan_loop lt abs A nd r oj'
  end.

Definition gauss_jordan lt abs (A : matrix T) :=
  gauss_jordan_loop lt abs (A : matrix T) 1%Srng 0 (mat_ncols A).

End in_ring.
Require Import ZArith.
Open Scope Z_scope.
Existing Instance Z_ring_op.
Existing Instance Z_semiring_op.
Theorem Z_1_neq_0 : 1 ≠ 0.
Proof. easy. Qed.
Definition Z_sring_dec_prop :=
  {| srng_eq_dec := Z.eq_dec; srng_1_neq_0 := Z_1_neq_0 |}.
Existing Instance Z_sring_dec_prop.
Definition ex :=
  mat_of_list_list 0 [[2; -1; 0]; [-1; 2; -1]; [0; -1; 2]].
Compute list_list_of_mat ex.
Compute let r := gauss_jordan Z.ltb Z.abs ex in (list_list_of_mat (fst r), snd r).
