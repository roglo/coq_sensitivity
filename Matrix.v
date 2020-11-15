(* matrices *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Init.Nat.

Require Import Misc.
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
Context (so : semiring_op T).
Context {sp : semiring_prop T}.
Context {rp : ring_prop T}.

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

Theorem mat_mul_nrows : ∀ A B, mat_nrows (mat_mul A B) = mat_nrows A.
Proof. easy. Qed.

Theorem mat_mul_ncols : ∀ A B, mat_ncols (mat_mul A B) = mat_ncols B.
Proof. easy. Qed.

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

(* function extensionality required for vectors *)
Axiom vector_eq : ∀ T (VA VB : vector T),
  vect_nrows VA = vect_nrows VB
  → (∀ i, i < vect_nrows VA → vect_el VA i = vect_el VB i)
  → VA = VB.

Definition vect_of_list {T} d (l : list T) :=
  mk_vect (λ i, nth i l d) (length l).
Definition list_of_vect {T} (v : vector T) :=
  map (vect_el v) (seq 0 (vect_nrows v)).

Definition vect_zero n := mk_vect (λ _, 0%Srng) n.

(* addition, subtraction of vector *)

Definition vect_add (U V : vector T) :=
  mk_vect (λ i, (vect_el U i + vect_el V i)%Srng) (vect_nrows V).
Definition vect_opp (V : vector T) :=
  mk_vect (λ i, (- vect_el V i)%Rng) (vect_nrows V).

Definition vect_sub (U V : vector T) := vect_add U (vect_opp V).

(* vector from a matrix column *)

Definition vect_of_mat_col (M : matrix T) j :=
  mk_vect (λ i, mat_el M i j) (mat_nrows M).

(* concatenation of a matrix and a vector *)

Definition mat_vect_concat (M : matrix T) V :=
  mk_mat
    (λ i j, if Nat.eq_dec j (mat_ncols M) then vect_el V i else mat_el M i j)
    (mat_nrows M) (mat_ncols M + 1).

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

Fixpoint det_from_row_loop M i j :=
  match j with
  | 0 => 1%Rng
  | S j' =>
      (minus_one_pow j * mat_el M i j * determinant (subm M i j') +
       det_from_row_loop M i j')
  end.
...

Fixpoint det_from_row_loop M i n :=
  match n with
  | 0 => 1%Rng
  | S n' =>
      (Σ (j = 0, n'),
       minus_one_pow j * mat_el M i j *
       det_from_row_loop (subm M i j) i n')%Rng
  end.

      (Σ (j = 0, n'),
       minus_one_pow j * mat_el M i j *
       det_from_row_loop (subm M i j) i n')%Rng

...

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
Existing Instance Z_ring_op.
Compute determinant (mat_of_list_list 0 [[1; 2]; [3; 4]]).
Compute determinant (mat_of_list_list 0 [[-2; 2; -3]; [-1; 1; 3]; [2; 0; -1]]). (* 18: seems good *)
*)

(* identity matrix of size n *)

Definition mI n : matrix T :=
  mk_mat (λ i j, if Nat.eq_dec i j then 1%Srng else 0%Srng) n n.

End in_ring.

Section in_ring.

Context {T : Type}.
Context {ro : ring_op T}.
Context (so : semiring_op T).
Context {sp : semiring_prop T}.
Context {rp : ring_prop T}.

Declare Scope M_scope.
Delimit Scope M_scope with M.

Arguments det_loop {T ro so} M%M n%nat.
Arguments mat_mul_scal_l {T so} _ M%M.
Arguments mat_nrows {T} m%M.
Arguments mat_ncols {T} m%M.
Arguments mat_sub {T ro so} MA%M MB%M.
Arguments mI {T so} n%nat.
Arguments minus_one_pow {T ro so}.
Arguments determinant {T ro so} M%M.
Arguments subm {T} M%M i%nat j%nat.

Notation "A + B" := (mat_add A B) : M_scope.
Notation "A - B" := (mat_sub A B) : M_scope.
Notation "A * B" := (mat_mul A B) : M_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.
Notation "- A" := (mat_opp A) : M_scope.

(* associativity of multiplication *)

Theorem mat_mul_assoc : ∀ MA MB MC, (MA * (MB * MC))%M = ((MA * MB) * MC)%M.
Proof.
intros.
apply matrix_eq; [ easy | easy | ].
intros i j Hi Hj.
cbn - [ iter_seq ].
cbn in Hi, Hj.
remember (mat_ncols MA) as ca eqn:Hca.
remember (mat_ncols MB) as cb eqn:Hcb.
move cb before ca.
erewrite srng_summation_eq_compat; [ | easy | ]. 2: {
  intros k Hk.
  now apply srng_mul_summation_distr_l.
}
cbn - [ iter_seq ].
rewrite srng_summation_summation_exch'; [ | easy ].
apply srng_summation_eq_compat; [ easy | ].
intros k Hk.
erewrite srng_summation_eq_compat; [ | easy | ]. 2: {
  intros l Hl.
  now rewrite srng_mul_assoc.
}
cbn - [ iter_seq ].
symmetry.
now apply srng_mul_summation_distr_r.
Qed.

(* comatrix *)

Definition comatrix M : matrix T :=
  {| mat_el i j := (minus_one_pow (i + j) * determinant (subm M i j))%Srng;
     mat_nrows := mat_nrows M;
     mat_ncols := mat_ncols M |}.

(* matrix transpose *)

Definition mat_transp (M : matrix T) :=
  {| mat_el i j := mat_el M j i;
     mat_nrows := mat_ncols M;
     mat_ncols := mat_nrows M |}.

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

Definition sqr_mat_zero n :=
  mk_mat (λ i j, 0%Srng) n n.
Definition sqr_mat_one n :=
  mk_mat (λ i j, if Nat.eq_dec i j then 1%Srng else 0%Srng) n n.

Definition sqr_mat_semiring_op n : semiring_op (matrix T) :=
  {| srng_zero := sqr_mat_zero n;
     srng_one := sqr_mat_one n;
     srng_add := mat_add;
     srng_mul := mat_mul |}.

End in_ring.

Section in_ring.

Context {T : Type}.
Context {ro : ring_op T}.
Context (so : semiring_op T).
Context {sp : semiring_prop T}.
Context {rp : ring_prop T}.

Arguments det_loop {T ro so} M n%nat.
Arguments determinant {T ro so} M.

Theorem fold_determinant :
  ∀ T {ro : ring_op T} {so : semiring_op T} (M : matrix T),
  det_loop M (mat_nrows M) = determinant M.
Proof. easy. Qed.

End in_ring.

Module matrix_Notations.

Declare Scope M_scope.
Declare Scope V_scope.
Delimit Scope M_scope with M.
Delimit Scope V_scope with V.

Arguments det_loop {T ro so} M%M n%nat.
Arguments determinant {T ro so} M%M.
Arguments mat_mul_scal_l {T so} _ M%M.
Arguments mat_mul_vect_r {T so}.
Arguments mat_nrows {T} m%M.
Arguments mat_ncols {T} m%M.
Arguments mat_sub {T ro so} MA%M MB%M.
Arguments mI {T so} n%nat.
Arguments minus_one_pow {T ro so}.
Arguments sqr_mat_one {T so}.
Arguments sqr_mat_zero {T so}.
Arguments sqr_mat_semiring_op {T so}.
Arguments subm {T} M%M i%nat j%nat.
Arguments vect_sub {T ro so}.
Arguments vect_mul_scal_l {T so} _%Srng _%V.
Arguments vect_zero {T so}.

Notation "A + B" := (mat_add A B) : M_scope.
Notation "A - B" := (mat_sub A B) : M_scope.
Notation "A * B" := (mat_mul A B) : M_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.
Notation "- A" := (mat_opp A) : M_scope.

Notation "U + V" := (vect_add U V) : V_scope.
Notation "U - V" := (vect_sub U V) : V_scope.
Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.
Notation "A · V" := (mat_mul_vect_r A V) (at level 40) : V_scope.

End matrix_Notations.
