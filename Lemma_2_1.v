(* Lemma 2.1 of the proof of the sensitivity conjecture *)

(* Given a n×n matrix A, a principal submatrix of A is obtained by
   deleting the same set of rows and columns from A. *)

(* Lemma 2.1. (Cauchy’s Interlace Theorem) Let A be a symmetric n×n
   matrix, and B be a m×m principal submatrix of A, for some m < n.
   If the eigenvalues of A are λ1 ≥ λ2 ≥ ... ≥ λn, and the eigenvalues
   of B are μ1 ≥ μ2 ≥ ... ≥ μm, then for all 1 ≤ i ≤ m,
     λi ≥ μi ≥ λ_{i-n+m}
 *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Permutation Sorted.

Require Import Misc Matrix.
Require Import RingLike.
Require Import RLsummation.
Import matrix_Notations.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).

Definition is_symm_mat (A : matrix T) :=
  ∀ i j, i < mat_nrows A → j < mat_nrows A →
  mat_el A i j = mat_el A j i.

Definition is_symm_squ_mat n (A : square_matrix n) :=
  is_symm_mat (proj1_sig A).

Definition princ_subm_1 (A : matrix T) n := subm A n n.

Theorem princ_subm_1_preserves_symm : ∀ (A : matrix T) n,
  is_symm_mat A
  → is_symm_mat (princ_subm_1 A n).
Proof.
intros * Ha.
unfold is_symm_mat in Ha |-*; cbn.
intros i j Hi Hj.
destruct (lt_dec i n) as [Hin| Hin]. {
  destruct (lt_dec j n) as [Hjn| Hjn]. {
    apply Ha; [ flia Hi | flia Hj ].
  } {
    apply Ha; [ flia Hi | flia Hj ].
  }
} {
  destruct (lt_dec j n) as [Hjn| Hjn]. {
    apply Ha; [ flia Hi | flia Hj ].
  } {
    apply Ha; [ flia Hi | flia Hj ].
  }
}
Qed.

Definition mat_princ_subm (A : matrix T) l :=
  fold_left (λ a i, subm a i i) l A.

Theorem subm_z : ∀ f i j, subm (mk_mat f 0 0) i j = mZ 0.
Proof. now intros; apply matrix_eq. Qed.

Theorem squ_mat_subm_prop : ∀ n (A : @square_matrix T n) i j,
  ((mat_nrows (subm (proj1_sig A) i j) =? n - 1) &&
   (mat_ncols (subm (proj1_sig A) i j) =? n - 1))%bool = true.
Proof.
intros.
destruct A as (A, Ha); cbn in Ha |-*.
apply Bool.andb_true_iff in Ha.
destruct Ha as (Hra, Hca).
apply Nat.eqb_eq in Hra.
apply Nat.eqb_eq in Hca.
apply Bool.andb_true_iff.
now split; apply Nat.eqb_eq; cbn; f_equal.
Qed.

Definition squ_mat_subm n (A : square_matrix n) i j : square_matrix (n - 1) :=
  exist _ (subm (proj1_sig A) i j) (squ_mat_subm_prop A i j).

Theorem princ_subm_prop : ∀ n (A : square_matrix n) l,
  ((mat_nrows (mat_princ_subm (proj1_sig A) l) =? n - length l) &&
   (mat_ncols (mat_princ_subm (proj1_sig A) l) =? n - length l))%bool = true.
Proof.
intros.
apply Bool.andb_true_iff.
revert n A.
induction l as [| i]; intros. {
  cbn; rewrite Nat.sub_0_r.
  destruct A as (A, Ha); cbn in Ha |-*.
  apply Bool.andb_true_iff in Ha.
  destruct Ha as (Hra, Hca).
  apply Nat.eqb_eq in Hra.
  apply Nat.eqb_eq in Hca.
  now split; apply Nat.eqb_eq.
}
cbn.
unfold mat_princ_subm in IHl.
destruct n. {
  destruct A as (A, Ha); cbn in Ha |-*.
  apply Bool.andb_true_iff in Ha.
  destruct Ha as (Hra, Hca).
  apply Nat.eqb_eq in Hra.
  apply Nat.eqb_eq in Hca.
  destruct A as (fa, ra, ca).
  cbn in Hra, Hca.
  subst ra ca.
  rewrite subm_z.
  clear.
  replace (fold_left _ l (mZ 0)) with (mZ 0); [ easy | ].
  symmetry.
  induction l as [| i]; [ easy | cbn ].
  replace (subm (mZ 0) i i) with (mZ 0); [ easy | ].
  now apply matrix_eq.
}
rewrite Nat.sub_succ.
specialize (IHl _ (squ_mat_subm A i i)) as (H1, H2).
cbn in H1; rewrite Nat.sub_0_r in H1; rewrite H1.
cbn in H2; rewrite Nat.sub_0_r in H2; rewrite H2.
easy.
Qed.

Definition princ_subm n (A : square_matrix n) (l : list nat) :
   square_matrix (n - length l) :=
 exist _ (mat_princ_subm (proj1_sig A) l) (princ_subm_prop A l).

Definition eigenvalues M ev :=
  ∀ μ, μ ∈ ev → ∃ V, V ≠ vect_zero (mat_nrows M) ∧ (M · V = μ × V)%V.

Theorem glop :
  ∀ n m l (A : square_matrix n) (B : square_matrix (n - length l)) seva sevb,
  m = n - length l
  → m < n
  → is_symm_squ_mat A
  → B = princ_subm A l
  → eigenvalues (proj1_sig A) seva
  → eigenvalues (proj1_sig B) sevb
  → Sorted rngl_le seva
  → Sorted rngl_le sevb
  → ∀ i, 1 ≤ i ≤ m →
    (nth (i-n+m) seva 0%F ≤ nth i sevb 0%F ≤ nth i seva 0%F)%F.
Proof.
intros * Hm Hmn Hisa Hb Heva Hevb Hsa Hsb * Him.
...

End in_ring_like.
