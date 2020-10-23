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
Require Import Relations.

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

Module matrix_Notations.

Declare Scope M_scope.
Delimit Scope M_scope with M.

Notation "A + B" := (mat_add A B) : M_scope.
Notation "A - B" := (mat_sub A B) : M_scope.
Notation "A * B" := (mat_mul A B) : M_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.
Notation "- A" := (mat_opp A) : M_scope.

End matrix_Notations.

Import matrix_Notations.

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

(* characteristic polynomial = det(xI-M) *)

Definition xI_sub_M M := (_x × m2mm (mI (mat_nrows M)) - m2mm M)%M.
Definition charac_polyn (M : matrix T) := determinant (xI_sub_M M).

Theorem fold_xI_sub_M : ∀ M,
  (_x × m2mm (mI (mat_nrows M)) - m2mm M)%M = xI_sub_M M.
Proof. easy. Qed.

Theorem xI_sub_M_nrows : ∀ M,
  mat_nrows (xI_sub_M M) = mat_nrows M.
Proof. easy. Qed.

Theorem submatrix_xI_sub_M : ∀ M i,
  subm (xI_sub_M M) i i = xI_sub_M (subm M i i).
Proof.
intros.
unfold xI_sub_M; cbn.
rewrite submatrix_sub, <- submatrix_m2mm; f_equal.
rewrite submatrix_mul_scal_l.
rewrite submatrix_m2mm.
destruct (mat_nrows M) as [| r]. {
  now cbn; apply matrix_eq.
}
rewrite submatrix_mI.
now rewrite Nat.sub_succ, Nat.sub_0_r.
Qed.

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

Theorem mat_el_xI_sub_M : ∀ i j M,
  mat_el (xI_sub_M M) i j =
    if Nat.eq_dec i j then (_x - polyn_of_list [mat_el M i i])%P
    else (- polyn_of_list [mat_el M i j])%P.
Proof.
intros; cbn.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  now rewrite polyn_mul_1_r, Hij.
}
now rewrite polyn_of_list_0, polyn_mul_0_r, polyn_add_0_l.
Qed.

Theorem polyn_degree_mat_el_xI_sub_M_0_0 : ∀ M,
  polyn_degree (mat_el (xI_sub_M M) 0 0) = 1.
Proof.
intros.
rewrite mat_el_xI_sub_M.
apply polyn_degree_1.
rewrite polyn_degree_opp.
apply polyn_degree_of_single.
Qed.

Theorem polyn_coeff_mat_el_xI_sub_M_0_0 : ∀ M,
  polyn_coeff (mat_el (xI_sub_M M) 0 0) 1 = 1%Srng.
Proof.
intros.
cbn; rewrite if_1_eq_0; cbn.
cbn; rewrite if_1_eq_0; cbn.
rewrite srng_add_0_l, srng_mul_0_l, srng_mul_1_l.
rewrite srng_add_0_l, srng_mul_0_l.
rewrite if_1_eq_0; cbn.
destruct (srng_eq_dec (mat_el M 0 0)) as [Hmz| Hmz]. {
  now cbn; rewrite if_1_eq_0.
}
now cbn; rewrite if_1_eq_0.
Qed.

Theorem mat_el_xI_sub_M_0_succ : ∀ M i,
  mat_el (xI_sub_M M) 0 (S i) = (- polyn_of_list [mat_el M 0 (S i)])%P.
Proof.
intros.
apply mat_el_xI_sub_M.
Qed.

Theorem polyn_degree_mat_el_xI_sub_M_0_succ : ∀ M i,
  polyn_degree (mat_el (xI_sub_M M) 0 (S i)) = 0.
Proof.
intros.
rewrite mat_el_xI_sub_M_0_succ.
rewrite polyn_degree_opp.
apply polyn_degree_of_single.
Qed.

Theorem polyn_coeff_mat_el_xI_sub_M_0_succ : ∀ i M,
  polyn_coeff (mat_el (xI_sub_M M) 0 (S i)) 0 = (- mat_el M 0 (S i))%Rng.
Proof.
intros.
rewrite mat_el_xI_sub_M_0_succ.
rewrite polyn_coeff_opp.
f_equal.
apply polyn_coeff_of_single.
Qed.

Theorem polyn_degree_mat_el_subm_xI_sub_M_0_succ_0_0 : ∀ M i,
  polyn_degree (mat_el (subm (xI_sub_M M) 0 (S i)) 0 0) = 0.
Proof.
intros; cbn.
rewrite if_1_eq_0; cbn.
rewrite if_0_eq_0; cbn.
rewrite srng_add_0_l, srng_mul_0_l.
rewrite if_0_eq_0; cbn.
destruct (srng_eq_dec (mat_el M 1 0) 0) as [Hmz| Hmz]; [ easy | cbn ].
now destruct (srng_eq_dec (- mat_el M 1 0)%Rng 0).
Qed.

Theorem polyn_degree_mat_el_subm_subm_xI_sub_M_0_succ_0_0 : ∀ M i,
  polyn_degree (mat_el (subm (subm (xI_sub_M M) 0 (S i)) 0 0) 0 0) ≤ 1.
Proof.
intros; cbn.
rewrite srng_mul_1_r.
specialize (polyn_of_list_repeat_0s 1) as H.
cbn in H; rewrite H; clear H.
rewrite srng_mul_0_r, srng_add_0_l.
destruct (lt_dec 1 (S i)) as [H1i| H1i]. {
  rewrite polyn_degree_opp.
  rewrite polyn_degree_of_single.
  apply Nat.le_0_l.
}
rewrite polyn_degree_1; [ easy | ].
rewrite polyn_degree_opp.
now rewrite polyn_degree_of_single.
Qed.

Theorem polyn_coeff_mat_el_subm_xI_sub_M_succ_0_0_0 : ∀ M i,
  polyn_coeff (mat_el (subm (xI_sub_M M) 0 (S i)) 0 0) 0 =
    (- mat_el M 1 0)%Rng.
Proof.
intros; cbn.
rewrite if_1_eq_0; cbn.
rewrite if_0_eq_0; cbn.
rewrite srng_add_0_l, srng_mul_0_l.
rewrite if_0_eq_0; cbn.
destruct (srng_eq_dec (mat_el M 1 0) 0) as [Hmz| Hmz]. {
  cbn; symmetry.
  rewrite Hmz.
  apply rng_opp_0.
}
cbn.
now destruct (srng_eq_dec (- mat_el M 1 0)%Rng 0).
Qed.

Theorem fold_determinant : ∀ T {ro : ring_op T} (M : matrix T),
  det_loop M (mat_nrows M) = determinant M.
Proof. easy. Qed.

Fixpoint repeat_subm T (M : matrix T) l :=
  match l with
  | [] => M
  | i :: l' => subm (repeat_subm M l') 0 i
  end.

Theorem subm_repeat_subm : ∀ T (M : matrix T) l i,
  subm (repeat_subm M l) 0 i = repeat_subm M (i :: l).
Proof. easy. Qed.

Theorem polyn_degree_mat_el_repeat_subm_le_1 : ∀ M i j k l,
  polyn_degree (mat_el (repeat_subm (subm (xI_sub_M M) 0 i) l) k j) ≤ 1.
Proof.
intros.
revert j k.
induction l as [| m]; intros. {
  cbn.
  destruct (lt_dec j i) as [Hji| Hji]. {
    destruct (Nat.eq_dec (k + 1) j) as [Hkj| Hkj]. {
      rewrite polyn_mul_1_r.
      rewrite polyn_degree_1; [ easy | ].
      rewrite polyn_degree_opp.
      now rewrite polyn_degree_of_single.
    }
    rewrite polyn_of_list_0, polyn_mul_0_r, polyn_add_0_l.
    rewrite polyn_degree_opp.
    rewrite polyn_degree_of_single.
    apply Nat.le_0_l.
  }
  destruct (Nat.eq_dec (k + 1) (j + 1)) as [Hkj| Hkj]. {
    rewrite polyn_mul_1_r.
    rewrite polyn_degree_1; [ easy | ].
    rewrite polyn_degree_opp.
    now rewrite polyn_degree_of_single.
  }
  rewrite polyn_of_list_0, polyn_mul_0_r, polyn_add_0_l.
  rewrite polyn_degree_opp.
  rewrite polyn_degree_of_single.
  apply Nat.le_0_l.
}
cbn.
destruct (lt_dec j m) as [Hjm| Hjm]; [ apply IHl | ].
apply IHl.
Qed.

Theorem polyn_degree_det_loop_repeat_subm_le : ∀ l M i n,
  polyn_degree (det_loop (repeat_subm (subm (xI_sub_M M) 0 i) l) n) ≤ n.
Proof.
intros.
revert l.
induction n; intros; [ now cbn; rewrite if_1_eq_0 | ].
cbn - [ iter_seq repeat_subm ].
etransitivity; [ apply polyn_degree_summation_ub | ].
cbn - [ iter_seq polyn_degree xI_sub_M ].
apply Max_lub_le.
intros j (_, Hj).
move j before i.
rewrite <- polyn_mul_assoc.
etransitivity; [ apply polyn_degree_mul_le | ].
rewrite polyn_degree_minus_one_pow, Nat.add_0_l.
etransitivity; [ apply polyn_degree_mul_le | ].
etransitivity. {
  apply (Nat.add_le_mono_r _ 1).
  apply polyn_degree_mat_el_repeat_subm_le_1.
}
apply -> Nat.succ_le_mono.
rewrite subm_repeat_subm.
apply IHn.
Qed.

Theorem polyn_degree_det_loop_subm_xI_sub_M_le : ∀ i n M,
  polyn_degree (det_loop (subm (xI_sub_M M) 0 i) n) ≤ n.
Proof.
intros.
revert i M.
destruct n; intros; [ now cbn; rewrite if_1_eq_0; cbn | ].
cbn - [ iter_seq xI_sub_M ].
etransitivity; [ apply polyn_degree_summation_ub | ].
cbn - [ iter_seq polyn_degree xI_sub_M ].
apply Max_lub_le.
intros j (_, Hj).
move j before i.
rewrite <- polyn_mul_assoc.
etransitivity; [ apply polyn_degree_mul_le | ].
rewrite polyn_degree_minus_one_pow, Nat.add_0_l.
etransitivity; [ apply polyn_degree_mul_le | ].
etransitivity. {
  apply (Nat.add_le_mono_r _ 1).
  destruct (lt_dec j i) as [Hji| Hji]. {
    rewrite mat_el_xI_sub_M.
    destruct (Nat.eq_dec 1 j) as [H1j| H1j]. {
      unfold polyn_sub.
      rewrite polyn_degree_1; [ easy | ].
      rewrite polyn_degree_opp.
      apply polyn_degree_of_single.
    }
    rewrite polyn_degree_opp.
    rewrite polyn_degree_of_single.
    apply Nat.le_0_l.
  }
  apply Nat.nlt_ge in Hji.
  rewrite mat_el_xI_sub_M.
  destruct (Nat.eq_dec 1 (j + 1)) as [H1j| H1j]. {
    unfold polyn_sub.
    rewrite polyn_degree_1; [ easy | ].
    rewrite polyn_degree_opp.
    apply polyn_degree_of_single.
  }
  rewrite polyn_degree_opp.
  rewrite polyn_degree_of_single.
  apply Nat.le_0_l.
}
apply -> Nat.succ_le_mono.
revert i j M Hj.
induction n; intros; [ now cbn; rewrite if_1_eq_0 | ].
cbn - [ iter_seq xI_sub_M ].
etransitivity; [ apply polyn_degree_summation_ub | ].
cbn - [ iter_seq polyn_degree xI_sub_M ].
apply Max_lub_le.
intros k (_, Hk).
move k before j.
rewrite <- polyn_mul_assoc.
etransitivity; [ apply polyn_degree_mul_le | ].
rewrite polyn_degree_minus_one_pow, Nat.add_0_l.
etransitivity; [ apply polyn_degree_mul_le | ].
etransitivity. {
  apply (Nat.add_le_mono_r _ 1).
  destruct (lt_dec k j) as [Hkj| Hkj]. {
    destruct (lt_dec k i) as [Hki| Hki]. {
      rewrite mat_el_xI_sub_M.
      destruct (Nat.eq_dec 2 k) as [H2k| H2k]. {
        unfold polyn_sub.
        rewrite polyn_degree_1; [ easy | ].
        rewrite polyn_degree_opp.
        apply polyn_degree_of_single.
      }
      rewrite polyn_degree_opp.
      rewrite polyn_degree_of_single.
      apply Nat.le_0_l.
    }
    apply Nat.nlt_ge in Hki.
    rewrite mat_el_xI_sub_M.
    destruct (Nat.eq_dec 2 (k + 1)) as [H2k| H2k]. {
      unfold polyn_sub.
      rewrite polyn_degree_1; [ easy | ].
      rewrite polyn_degree_opp.
      apply polyn_degree_of_single.
    }
    rewrite polyn_degree_opp.
    rewrite polyn_degree_of_single.
    apply Nat.le_0_l.
  }
  apply Nat.nlt_ge in Hkj.
  destruct (lt_dec (k + 1) i) as [Hki| Hki]. {
    rewrite mat_el_xI_sub_M.
    destruct (Nat.eq_dec 2 (k + 1)) as [H2k| H2k]. {
      unfold polyn_sub.
      rewrite polyn_degree_1; [ easy | ].
      rewrite polyn_degree_opp.
      apply polyn_degree_of_single.
    }
    rewrite polyn_degree_opp.
    rewrite polyn_degree_of_single.
    apply Nat.le_0_l.
  }
  apply Nat.nlt_ge in Hki.
  rewrite mat_el_xI_sub_M.
  destruct (Nat.eq_dec 2 (k + 1 + 1)) as [H2k| H2k]. {
    unfold polyn_sub.
    rewrite polyn_degree_1; [ easy | ].
    rewrite polyn_degree_opp.
    apply polyn_degree_of_single.
  }
  rewrite polyn_degree_opp.
  rewrite polyn_degree_of_single.
  apply Nat.le_0_l.
}
apply -> Nat.succ_le_mono.
apply (polyn_degree_det_loop_repeat_subm_le [k; j]).
Qed.

Theorem polyn_degree_det_loop_xI_sub_M : ∀ n M,
  mat_nrows M = n
  → polyn_degree (det_loop (xI_sub_M M) n) = n.
Proof.
intros * Hr.
revert M Hr.
induction n; intros; [ now cbn; rewrite if_1_eq_0 | ].
cbn - [ iter_seq xI_sub_M ].
specialize (IHn (subm M 0 0)) as Hpd.
rewrite submatrix_nrows, Hr, Nat.sub_succ, Nat.sub_0_r in Hpd.
specialize (Hpd eq_refl).
rewrite <- submatrix_xI_sub_M in Hpd.
rewrite srng_summation_split_first; [ | apply Nat.le_0_l ].
remember (det_loop (subm (xI_sub_M M) 0 0) n) as P eqn:HP.
cbn - [ polyn_degree xI_sub_M iter_seq ].
rewrite srng_mul_1_l.
rewrite polyn_degree_lt_add. 2: {
  eapply le_lt_trans; [ apply polyn_degree_summation_ub | ].
  cbn - [ iter_seq polyn_degree mat_el ].
  apply le_lt_trans with
    (m := Max (i = 1, n), polyn_degree (det_loop (subm (xI_sub_M M) 0 i) n)).
  {
    apply Max_le_compat.
    intros i Hi.
    rewrite <- polyn_mul_assoc.
    etransitivity; [ apply polyn_degree_mul_le | ].
    rewrite polyn_degree_minus_one_pow, Nat.add_0_l.
    etransitivity; [ apply polyn_degree_mul_le | ].
    destruct i; [ flia Hi | ].
    rewrite polyn_degree_mat_el_xI_sub_M_0_succ, Nat.add_0_l.
    easy.
  }
  apply Max_lub_lt. {
    destruct n. {
      cbn in HP; rewrite HP.
      rewrite polyn_mul_1_r.
      rewrite polyn_degree_mat_el_xI_sub_M_0_0.
      apply Nat.lt_0_1.
    }
    rewrite polyn_degree_mul. 2: {
      rewrite polyn_degree_mat_el_xI_sub_M_0_0.
      rewrite polyn_coeff_mat_el_xI_sub_M_0_0, srng_mul_1_l.
      apply polyn_highest_coeff_neq_0.
      unfold so.
      now rewrite Hpd.
    }
    rewrite polyn_degree_mat_el_xI_sub_M_0_0.
    flia.
  }
  intros i Hi.
  rewrite polyn_degree_mul. 2: {
    rewrite polyn_degree_mat_el_xI_sub_M_0_0.
    rewrite polyn_coeff_mat_el_xI_sub_M_0_0, srng_mul_1_l.
    apply polyn_highest_coeff_neq_0.
    unfold so.
    rewrite Hpd; flia Hi.
  }
  rewrite Hpd.
  rewrite polyn_degree_mat_el_xI_sub_M_0_0, Nat.add_1_l.
  apply Nat.lt_succ_r.
  apply polyn_degree_det_loop_subm_xI_sub_M_le.
}
rewrite polyn_degree_mul. 2: {
  rewrite polyn_degree_mat_el_xI_sub_M_0_0.
  rewrite polyn_coeff_mat_el_xI_sub_M_0_0.
  rewrite srng_mul_1_l.
  destruct n. {
    cbn in HP; subst P; cbn.
    rewrite if_1_eq_0; cbn.
    apply srng_1_neq_0.
  }
  apply polyn_highest_coeff_neq_0.
  unfold so.
  now rewrite Hpd.
}
rewrite polyn_degree_mat_el_xI_sub_M_0_0.
destruct n. {
  subst P; cbn.
  now rewrite if_1_eq_0.
}
now rewrite Hpd.
Qed.

Theorem polyn_coeff_det_loop_xI_sub_M : ∀ n M,
  mat_nrows M = n
  → polyn_coeff (det_loop (xI_sub_M M) n) n = 1%Srng.
Proof.
intros * Hr.
revert M Hr.
induction n; intros; [ now cbn; rewrite if_1_eq_0 | ].
cbn - [ iter_seq xI_sub_M ].
specialize (IHn (subm M 0 0)) as Hpc.
rewrite submatrix_nrows, Hr, Nat.sub_succ, Nat.sub_0_r in Hpc.
specialize (Hpc eq_refl).
rewrite <- submatrix_xI_sub_M in Hpc.
rewrite srng_summation_split_first; [ | apply Nat.le_0_l ].
remember (det_loop (subm (xI_sub_M M) 0 0) n) as P eqn:HP.
cbn - [ polyn_coeff xI_sub_M iter_seq ].
rewrite srng_mul_1_l.
rewrite polyn_coeff_add, srng_add_comm.
rewrite polyn_coeff_overflow. 2: {
  eapply le_lt_trans; [ apply polyn_degree_summation_ub | ].
  cbn - [ iter_seq polyn_degree xI_sub_M ].
  apply Max_lub_lt; [ apply Nat.lt_0_succ | ].
  intros i Hi.
  eapply le_lt_trans; [ apply polyn_degree_mul_le | ].
  rewrite <- Nat.add_1_l.
  apply Nat.add_lt_le_mono. {
    eapply le_lt_trans; [ apply polyn_degree_mul_le |].
    rewrite polyn_degree_minus_one_pow.
    destruct i; [ easy | ].
    rewrite polyn_degree_mat_el_xI_sub_M_0_succ.
    apply Nat.lt_0_succ.
  }
  destruct i; [ easy | ].
  apply polyn_degree_det_loop_subm_xI_sub_M_le.
}
rewrite srng_add_0_l.
rewrite polyn_coeff_mul.
rewrite srng_summation_split_first; [ | apply Nat.le_0_l ].
rewrite Nat.sub_0_r.
rewrite srng_summation_split_first; [ | flia ].
rewrite Nat.sub_succ, Nat.sub_0_r, Hpc, srng_mul_1_r.
rewrite polyn_coeff_mat_el_xI_sub_M_0_0.
rewrite (polyn_coeff_overflow P). 2: {
  rewrite HP.
  apply Nat.lt_succ_r.
  apply polyn_degree_det_loop_subm_xI_sub_M_le.
}
rewrite srng_mul_0_r, srng_add_0_l.
rewrite all_0_srng_summation_0. 2: {
  intros i Hi.
  rewrite mat_el_xI_sub_M.
  destruct (Nat.eq_dec 0 0) as [H| H]; [ clear H | easy ].
  rewrite polyn_coeff_overflow. 2: {
    unfold polyn_sub.
    rewrite polyn_degree_1; [ easy | ].
    rewrite polyn_degree_opp.
    apply polyn_degree_of_single.
  }
  apply srng_mul_0_l.
}
apply srng_add_0_r.
Qed.

(* the degree of the caracteristic polynomial is the size of the matrix *)

Theorem charac_polyn_degree : ∀ M,
  polyn_degree (charac_polyn M) = mat_nrows M.
Proof.
intros.
unfold charac_polyn.
unfold determinant; cbn.
now apply polyn_degree_det_loop_xI_sub_M.
Qed.

(* the caracteristic polynomial of a matrix is monic, i.e. its
   leading coefficient is 1 *)

Theorem charac_polyn_is_monic : ∀ M,
  is_monic_polyn (charac_polyn M).
Proof.
intros.
unfold is_monic_polyn.
rewrite charac_polyn_degree.
unfold charac_polyn.
unfold determinant; cbn.
now apply polyn_coeff_det_loop_xI_sub_M.
Qed.

...

(* the list of coefficients of the characteristic polynomial of a matrix M
   has length "nrows(M) + 1"
   e.g. matrix
        (a b)
        (c d)
   characteristic polynomial = determinant of
        (x-a -b )
        (-c  x-d)
   which is
        (x-a)(x-d)-cb = x²-(a+d)x+(ad-bc)
   list of its coefficients
        [ad-bc; -(a+d); 1]
   whose length is 3 = nrows(M)+1
 *)

Theorem charac_polyn_list_length : ∀ M,
  length (polyn_list (charac_polyn M)) = mat_nrows M + 1.
Proof.
intros.
cbn.
...

(* eigenvalues and eigenvectors *)

Theorem exists_eigenvalues : ∀ (acp : algeb_closed_prop) (M : matrix T),
  mat_nrows M ≠ 0
  → is_square_mat M
  → ∃ EVL, length EVL = mat_nrows M ∧
     (∀ μ V, (μ, V) ∈ EVL ↔ mat_mul_vect_r M V = vect_mul_scal_l μ V).
Proof.
intros acp M Hrz HM.
destruct acp as (Hroots).
specialize (Hroots (charac_polyn M)) as H1.
...
assert (H2 : polyn_el (charac_polyn M) (mat_nrows M) = 1%Srng). {
  now apply charac_polyn_higher_coeff.
}
assert (H3 : polyn_degree (charac_polyn M) = mat_nrows M). {
...

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
