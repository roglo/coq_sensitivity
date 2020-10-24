(* matrices *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Init.Nat.

Require Import Misc.
Require Import SRpolynomial.
Import polynomial_Notations.

(* "Given a n×n matrix A, a principal submatrix of A is obtained by deleting
    the same set of rows and columns from A.

   Theorem 2.1. (Cauchy’s Interlace Theorem) Let A be a symmetric n×n matrix,
      and B be a m×m principal submatrix of A, for some m < n. If the
      eigenvalues of A are λ₁ ≥ λ₂ ≥ … ≥ λ_n, and the eigenvalues of B
      are µ₁ ≥ µ₂ ≥ … ≥ µ_m, then for all 1 ≤ i ≤ m,
              λ_i ≥ µ_i ≥ λ_{i+n-m}."
*)

Require Import Semiring SRsummation.

(* matrices *)

Record matrix T := mk_mat
  { mat_el : nat → nat → T;
    mat_nrows : nat;
    mat_ncols : nat }.

(* function extensionality required for matrices *)
Axiom matrix_eq : ∀ T (MA MB : matrix T),
  mat_nrows MA = mat_nrows MB
  → mat_ncols MA = mat_ncols MB
  → (∀ i j, i < mat_nrows MA → j < mat_ncols MB →
      mat_el MA i j = mat_el MB i j)
  → MA = MB.

Definition list_list_nrows T (ll : list (list T)) :=
  length ll.

Definition list_list_ncols T (ll : list (list T)) :=
  length (hd [] ll).

Definition list_list_of_mat T (M : matrix T) : list (list T) :=
  map (λ i, map (mat_el M i) (seq 0 (mat_ncols M))) (seq 0 (mat_nrows M)).

Definition list_list_el T d (ll : list (list T)) i j : T :=
  nth j (nth i ll []) d.

Definition mat_of_list_list T d (ll : list (list T)) :=
  mk_mat (list_list_el d ll) (list_list_nrows ll) (list_list_ncols ll).

(*
Compute (let (i, j) := (2, 0) in list_list_el 42 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] i j).
Compute (let (i, j) := (7, 0) in list_list_el 42 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] i j).
Compute (let (i, j) := (1, 3) in list_list_el 42 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]] i j).
Compute (list_list_of_mat (mat_of_list_list 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]])).
*)

Fixpoint concat_list_in_list {T} (ll1 ll2 : list (list T)) :=
  match ll1 with
  | [] => ll2
  | l1 :: ll1' =>
       match ll2 with
       | [] => ll1
       | l2 :: ll2' => app l1 l2 :: concat_list_in_list ll1' ll2'
       end
  end.

Definition concat_list_list_list {T} (lll : list (list (list T))) :=
  fold_left concat_list_in_list lll [].

Section in_ring.

Context {T : Type}.
Context {ro : ring_op T}.
Context (so := rng_semiring).
Context {sp : @semiring_prop T (@rng_semiring T ro)}.
Context {rp : @ring_prop T ro}.
Context {sdp : @sring_dec_prop T so}.
Existing Instance so.

(* addition *)

Definition mat_add {so : semiring_op T} (MA MB : matrix T) :=
  {| mat_el i j := (mat_el MA i j + mat_el MB i j)%Srng;
     mat_nrows := mat_nrows MA;
     mat_ncols := mat_ncols MA |}.

Definition nat_semiring_op : semiring_op nat :=
  {| srng_zero := 0;
     srng_one := 1;
     srng_add := Nat.add;
     srng_mul := Nat.mul |}.

(*
End in_ring.
Compute (list_list_of_mat (mat_add add (mat_of_list_list 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (mat_of_list_list 0 [[1; 2]; [3; 4]; [5; 6]; [7; 8]]))).
Compute (list_list_of_mat (mat_add add (mat_of_list_list 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (mat_of_list_list 0 [[1; 2]; [3; 4]; [5; 6]; [7; 8]]))).
*)

(* multiplication *)

Definition mat_mul {so : semiring_op T} (MA MB : matrix T) :=
  {| mat_el i k :=
       (Σ (j = 0, mat_ncols MA - 1), mat_el MA i j * mat_el MB j k)%Srng;
     mat_nrows := mat_nrows MA;
     mat_ncols := mat_ncols MB |}.

(*
End in_ring.
Compute (let _ := nat_semiring_op in list_list_of_mat (mat_mul (mat_of_list_list 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (mat_of_list_list 0 [[1; 2]; [3; 4]; [5; 6]; [7; 8]]))).
*)

(* opposite *)

Definition mat_opp M : matrix T :=
  {| mat_el i j := (- mat_el M i j)%Rng;
     mat_nrows := mat_nrows M;
     mat_ncols := mat_ncols M |}.

(* subtraction *)

Definition mat_sub MA MB :=
  mat_add MA (mat_opp MB).

(* *)

Definition is_square_mat (M : matrix T) := mat_nrows M = mat_ncols M.

(* vector *)

Record vector T := mk_vect
  { vect_el : nat → T;
    vect_nrows : nat }.

(* multiplication of a matrix by a vector *)

Definition mat_mul_vect_r M V :=
  mk_vect (λ i, (Σ (j = 0, mat_ncols M - 1), mat_el M i j * vect_el V j)%Srng)
    (mat_nrows M).

(* multiplication of a vector by a scalar *)

Definition vect_mul_scal_l μ V :=
  mk_vect (λ i, μ * vect_el V i)%Srng (vect_nrows V).

(* multiplication of a matrix by a scalar *)

Definition mat_mul_scal_l μ M :=
  mk_mat (λ i j, μ * mat_el M i j)%Srng (mat_nrows M) (mat_ncols M).

(* matrix without row i and column j *)

Definition subm (M : matrix T) i j :=
  mk_mat
    (λ k l,
       if lt_dec k i then
         if lt_dec l j then mat_el M k l
         else mat_el M k (l + 1)
       else
         if lt_dec l j then mat_el M (k + 1) l
         else mat_el M (k + 1) (l + 1))
    (mat_nrows M - 1)
    (mat_ncols M - 1).

(* (-1) ^ n *)

Definition minus_one_pow n :=
  match n mod 2 with
  | 0 => 1%Rng
  | _ => (- 1%Srng)%Rng
  end.

(* determinant *)

Fixpoint det_loop M n :=
  match n with
  | 0 => 1%Rng
  | S n' =>
      (Σ (j = 0, n'),
       minus_one_pow j * mat_el M 0 j * det_loop (subm M 0 j) n')%Rng
  end.

Definition determinant M := det_loop M (mat_nrows M).

(*
End in_ring.

Require Import ZArith.
Open Scope Z_scope.

Compute let ro := Z_ring_op in determinant (mat_of_list_list 0 [[1; 2]; [3; 4]]).
Compute let ro := Z_ring_op in determinant (mat_of_list_list 0 [[-2; 2; -3]; [-1; 1; 3]; [2; 0; -1]]). (* 18: seems good *)
*)

(* convertion matrix → matrix with monomials *)

Definition m2mm M : matrix (polynomial T) :=
  mk_mat (λ i j, polyn_of_list [mat_el M i j])
    (mat_nrows M) (mat_ncols M).

(* identity matrix of size n *)

Definition mI n : matrix T :=
  mk_mat (λ i j, if Nat.eq_dec i j then 1%Srng else 0%Srng) n n.

End in_ring.

Section in_ring.

Context {T : Type}.
Context {ro : ring_op T}.
Context (so := rng_semiring).
Context {sp : @semiring_prop T (@rng_semiring T ro)}.
Context {rp : @ring_prop T ro}.
Context {sdp : @sring_dec_prop T so}.
Existing Instance so.
Existing Instance polyn_semiring_op.
Existing Instance polyn_ring_op.
Existing Instance polyn_semiring_prop.
Existing Instance polyn_ring_prop.

Declare Scope M_scope.
Delimit Scope M_scope with M.

Notation "A + B" := (mat_add A B) : M_scope.
Notation "A - B" := (mat_sub A B) : M_scope.
Notation "A * B" := (mat_mul A B) : M_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.
Notation "- A" := (mat_opp A) : M_scope.

Arguments det_loop {T ro} M%M n%nat.
Arguments mat_nrows {T} m%M.
Arguments mat_ncols {T} m%M.
Arguments determinant {T ro} M%M.
Arguments subm {T} M%M i%nat j%nat.

(* determinant of a product *)

Theorem det_mul : ∀ A B,
  is_square_mat A
  → is_square_mat B
  → mat_nrows A = mat_nrows B
  → determinant (A * B) =  (determinant A * determinant B)%Srng.
Proof.
intros * Hca Hcb Hrb.
unfold determinant; cbn.
rewrite <- Hrb.
remember (mat_nrows A) as n eqn:Hra in |-*; symmetry in Hra.
unfold is_square_mat in Hca, Hcb.
symmetry in Hca, Hcb, Hrb.
rewrite Hra in Hca, Hrb.
rewrite Hrb in Hcb.
revert A B Hra Hrb Hca Hcb.
induction n; intros; [ now cbn; rewrite srng_mul_1_l | ].
cbn - [ iter_seq ].
rewrite Hca, Nat.sub_succ, Nat.sub_0_r.
Search ((Σ (_ = _, _), _) * (Σ (_ = _, _), _)).
...

(* combinations of submatrix and other *)

Theorem submatrix_sub : ∀ (MA MB : matrix T) i j,
  subm (MA - MB)%M i j = (subm MA i j - subm MB i j)%M.
Proof.
intros.
apply matrix_eq; cbn; [ easy | easy | ].
intros k l Hk Hl.
now destruct (lt_dec k i), (lt_dec l j).
Qed.

Theorem submatrix_mul_scal_l : ∀ (μ : T) M i j,
  subm (μ × M)%M i j = (μ × subm M i j)%M.
Proof.
intros.
apply matrix_eq; cbn; [ easy | easy | ].
intros k l Hk Hl.
now destruct (lt_dec k i), (lt_dec l j).
Qed.

Theorem submatrix_m2mm : ∀ (M : matrix T) i j,
  subm (m2mm M) i j = m2mm (subm M i j).
Proof.
intros.
apply matrix_eq; cbn; [ easy | easy | ].
intros k l Hk Hl.
now destruct (lt_dec k i), (lt_dec l j).
Qed.

Theorem submatrix_nrows : ∀ (M : matrix T) i j,
  mat_nrows (subm M i j) = mat_nrows M - 1.
Proof. easy. Qed.

Theorem submatrix_mI : ∀ i r,
 subm (mI (S r)) i i = mI r.
Proof.
intros.
apply matrix_eq; cbn. {
  now rewrite Nat.sub_0_r.
} {
  now rewrite Nat.sub_0_r.
}
intros k l Hk Hl.
destruct (lt_dec k i) as [Hki| Hki]. {
  destruct (lt_dec l i) as [Hli| Hli]; [ easy | ].
  apply Nat.nlt_ge in Hli.
  destruct (Nat.eq_dec k (l + 1)) as [Hkl1| Hkl1]. {
    flia Hki Hli Hkl1.
  }
  destruct (Nat.eq_dec k l) as [Hkl| Hkl]; [ | easy ].
  flia Hki Hli Hkl.
} {
  apply Nat.nlt_ge in Hki.
  destruct (lt_dec l i) as [Hli| Hli]. {
    destruct (Nat.eq_dec (k + 1) l) as [Hkl1| Hkl1]. {
      flia Hki Hli Hkl1.
    }
    destruct (Nat.eq_dec k l) as [Hkl| Hkl]; [ | easy ].
    flia Hki Hli Hkl.
  } {
    apply Nat.nlt_ge in Hli.
    destruct (Nat.eq_dec (k + 1) (l + 1)) as [Hkl1| Hkl1]. {
      destruct (Nat.eq_dec k l) as [Hkl| Hkl]; [ easy | ].
      flia Hkl1 Hkl.
    } {
      destruct (Nat.eq_dec k l) as [Hkl| Hkl]; [ | easy ].
      flia Hkl1 Hkl.
    }
  }
}
Qed.

Theorem polyn_degree_opp : ∀ P, polyn_degree (- P) = polyn_degree P.
Proof.
intros; cbn.
now rewrite map_length.
Qed.

End in_ring.

Section in_ring.

Context {T : Type}.
Context {ro : ring_op T}.
Context (so := rng_semiring).
Context {sp : @semiring_prop T (@rng_semiring T ro)}.
Context {rp : @ring_prop T ro}.
Context {sdp : @sring_dec_prop T so}.
Existing Instance so.
Existing Instance polyn_semiring_op.
Existing Instance polyn_ring_op.
Existing Instance polyn_semiring_prop.
Existing Instance polyn_ring_prop.
(*
Existing Instance polyn_sring_dec_prop.
Time Check polyn_degree.
*)

Theorem polyn_degree_minus_one_pow : ∀ i,
  polyn_degree (minus_one_pow i) = 0.
Proof.
intros.
unfold polyn_degree.
unfold polyn_degree_plus_1.
unfold minus_one_pow.
now destruct (i mod 2); cbn; rewrite if_1_eq_0.
Qed.

Theorem polyn_coeff_minus_one_pow : ∀ i,
  polyn_coeff (minus_one_pow i) 0 = minus_one_pow i.
Proof.
intros.
unfold minus_one_pow.
now destruct (i mod 2); cbn; rewrite if_1_eq_0.
Qed.

Theorem fold_determinant : ∀ T {ro : ring_op T} (M : matrix T),
  det_loop M (mat_nrows M) = determinant M.
Proof. easy. Qed.

End in_ring.

Module matrix_Notations.

Declare Scope M_scope.
Delimit Scope M_scope with M.

Notation "A + B" := (mat_add A B) : M_scope.
Notation "A - B" := (mat_sub A B) : M_scope.
Notation "A * B" := (mat_mul A B) : M_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.
Notation "- A" := (mat_opp A) : M_scope.

End matrix_Notations.
