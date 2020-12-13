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

Theorem princ_subm_prop : ∀ n (A : square_matrix n) l,
  ((mat_nrows (mat_princ_subm (proj1_sig A) l) =? n - length l) &&
   (mat_ncols (mat_princ_subm (proj1_sig A) l) =? n - length l))%bool = true.
Proof.
intros.
apply Bool.andb_true_iff.
split; apply Nat.eqb_eq. {
  revert n A.
  induction l as [| i]; intros. {
    cbn; rewrite Nat.sub_0_r.
    destruct A as (A, Ha); cbn in Ha |-*.
    apply Bool.andb_true_iff in Ha.
    destruct Ha as (Hra, Hca).
    now apply Nat.eqb_eq in Hra.
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
    induction l as [| i]; [ easy | cbn ].
Search (subm (mZ _)).
...

Definition princ_subm n (A : @square_matrix T n) (l : list nat) :
  @square_matrix T (n - length l).
Proof.
exists (mat_princ_subm (proj1_sig A) l).
...
apply princ_subm_prop.
Qed.

Definition eigenvalues M ev :=
  ∀ μ, μ ∈ ev → ∃ V, V ≠ vect_zero (mat_nrows M) ∧ (M · V = μ × V)%V.

Theorem glop :
  ∀ n m (A : square_matrix n) (B : square_matrix m) l eva evb seva sevb,
  m < n
  → is_symm_squ_mat A
  → B = princ_subm A l
  → eigenvalues A eva
  → eigenvalues B evb
  → Permutation eva seva
  → Permutation evb sevb
  → Sorted seva
  → Sorted sevb
  → squ_mat_mul A A = A ∧ squ_mat_mul B B = B.
Proof.
...

End in_ring_like.
