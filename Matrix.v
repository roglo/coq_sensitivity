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
Context {scp : sring_comm_prop T}.
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

Canonical Structure nat_semiring_op.

Definition nat_semiring_prop : semiring_prop nat :=
  {| srng_add_comm := Nat.add_comm;
     srng_add_assoc := Nat.add_assoc;
     srng_add_0_l := Nat.add_0_l;
     srng_mul_assoc := Nat.mul_assoc;
     srng_mul_1_l := Nat.mul_1_l;
     srng_mul_add_distr_l := Nat.mul_add_distr_l;
     srng_mul_0_l := Nat.mul_0_l |}.

Definition nat_sring_comm_prop : sring_comm_prop nat :=
  {| srng_c_mul_comm := Nat.mul_comm |}.

Canonical Structure nat_semiring_prop.
Canonical Structure nat_sring_comm_prop.

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

(* matrix whose k-th column is replaced by a vector *)

Definition mat_repl_vect k (M : matrix T) V :=
  mk_mat (λ i j, if Nat.eq_dec j k then vect_el V i else mat_el M i j)
    (mat_nrows M) (mat_ncols M).

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

Definition determinant M := det_loop M (mat_ncols M).

(* *)

Declare Scope V_scope.
Delimit Scope V_scope with V.

Notation "U + V" := (vect_add U V) : V_scope.
Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.

Theorem determinant_multilinear : ∀ M i a b U V,
  determinant (mat_repl_vect i M (a × U + b × V)%V) =
    (a * determinant (mat_repl_vect i M U) +
     b * determinant (mat_repl_vect i M V))%Rng.
Proof.
intros.
...

(* the following versions of computing the determinant should
   (to be proven) be equivalent; perhaps could help for proving
   Cramer's rule of resolving equations *)

Definition det_from_row M i :=
  (minus_one_pow i *
   Σ (j = 0, mat_ncols M - 1),
     minus_one_pow j * mat_el M i j * determinant (subm M i j))%Rng.

Definition det_from_col M j :=
  (minus_one_pow j *
   Σ (i = 0, mat_nrows M - 1),
     minus_one_pow i * mat_el M i j * determinant (subm M i j))%Rng.

(* *)

Definition mat_mul_row_0_by_scal M s :=
  mk_mat
    (λ i j,
     if Nat.eq_dec i 0 then (s * mat_el M i j)%Srng else mat_el M i j)
    (mat_nrows M) (mat_ncols M).

Definition mat_swap_rows (M : matrix T) i1 i2 :=
  mk_mat
    (λ i j,
     if Nat.eq_dec i i1 then mat_el M i2 j
     else if Nat.eq_dec i i2 then mat_el M i1 j
     else mat_el M i j) (mat_nrows M) (mat_ncols M).

Definition mat_add_row_mul_scal_row M i1 v i2 :=
  mk_mat
    (λ i j,
     if Nat.eq_dec i i1 then (mat_el M i1 j + v * mat_el M i2 j)%Srng
     else mat_el M i j)
   (mat_nrows M) (mat_nrows M).

(* If we multiply a row (column) of A by a number, the determinant of
   A will be multiplied by the same number. *)
(* https://math.vanderbilt.edu/sapirmv/msapir/proofdet1.html *)

(* Well, since my definition of the discriminant only covers the
   row 0, we can prove that only when i=0; this will able us to
   prove next theorems, swapping rows by going via row 0 *)

Theorem det_mul_row_0_by_scal : ∀ A v,
  mat_ncols A ≠ 0
  → determinant (mat_mul_row_0_by_scal A v) = (v * determinant A)%Srng.
Proof.
intros * Hcz.
unfold determinant; cbn.
remember (mat_ncols A) as c eqn:Hc; symmetry in Hc.
destruct c; [ easy | clear Hcz ].
cbn - [ iter_seq ].
rewrite srng_mul_summation_distr_l; [ | easy | easy ].
apply srng_summation_eq_compat.
intros j Hj.
rewrite (srng_c_mul_comm (minus_one_pow j)).
do 2 rewrite <- srng_mul_assoc.
f_equal.
rewrite (srng_c_mul_comm (mat_el A 0 j)).
do 2 rewrite <- srng_mul_assoc.
f_equal.
rewrite srng_c_mul_comm; f_equal.
f_equal.
apply matrix_eq; [ easy | easy | cbn ].
rename j into k; rename Hj into Hk.
intros i j Hi Hj.
destruct (Nat.eq_dec (i + 1) 0) as [H| H]; [ flia H | easy ].
Qed.


(* If the i-th row (column) in A is a sum of the i-th row (column) of
   a matrix B and the i-th row (column) of a matrix C and all other
   rows in B and C are equal to the corresponding rows in A (that is B
   and C differ from A by one row only), then det(A)=det(B)+det(C). *)
(* https://math.vanderbilt.edu/sapirmv/msapir/proofdet1.html *)

(* Well, since my definition of the discriminant only covers the
   row 0, we can prove that only when i=0; this will able us to
   prove the next theorem, swapping rows by going via row 0 *)

Theorem det_sum_row_row : ∀ A B C n,
  n ≠ 0
  → mat_nrows A = n
  → mat_nrows B = n
  → mat_nrows C = n
  → mat_ncols A = n
  → mat_ncols B = n
  → mat_ncols C = n
  → (∀ j, mat_el A 0 j = (mat_el B 0 j + mat_el C 0 j)%Srng)
  → (∀ i j, i ≠ 0 → mat_el B i j = mat_el A i j)
  → (∀ i j, i ≠ 0 → mat_el C i j = mat_el A i j)
  → determinant A = (determinant B + determinant C)%Srng.
Proof.
intros * Hnz Hra Hrb Hrc Hca Hcb Hcc Hbc Hb Hc.
unfold determinant.
rewrite Hca, Hcb, Hcc.
destruct n; [ easy | clear Hnz ].
cbn - [ iter_seq ].
assert (Hab : ∀ j, subm A 0 j = subm B 0 j). {
  intros.
  apply matrix_eq; cbn; [ now rewrite Hra, Hrb | now rewrite Hca, Hcb | ].
  intros i j' Hi Hj'.
  destruct (lt_dec j' j); symmetry; apply Hb; flia.
}
assert (Hac : ∀ j, subm A 0 j = subm C 0 j). {
  intros.
  apply matrix_eq; cbn; [ now rewrite Hra, Hrc | now rewrite Hca, Hcc | ].
  intros i j' Hi Hj'.
  destruct (lt_dec j' j); symmetry; apply Hc; flia.
}
erewrite srng_summation_eq_compat. 2: {
  intros j Hj.
  rewrite Hbc.
  rewrite srng_mul_add_distr_l.
  rewrite srng_mul_add_distr_r.
  rewrite Hab at 1.
  rewrite Hac at 1.
  easy.
}
cbn - [ iter_seq ].
now apply srng_summation_add_distr.
Qed.

(* If two rows (columns) in A are equal then det(A)=0. *)
(* https://math.vanderbilt.edu/sapirmv/msapir/proofdet1.html *)
(* doing it only when the first row is 0; can be generalized later *)

Theorem det_two_rows_are_eq : ∀ A i,
  is_square_mat A
  → 0 < i < mat_nrows A
  → mat_ncols A ≠ 0
  → (∀ j, mat_el A i j = mat_el A 0 j)
  → determinant A = 0%Srng.
Proof.
intros * Hsm Hiz Hcz Ha.
unfold is_square_mat in Hsm.
unfold determinant.
rewrite Hsm in Hiz.
remember (mat_ncols A) as n eqn:Hn; symmetry in Hn.
destruct n; [ easy | clear Hcz ].
cbn - [ iter_seq ].
(**)
destruct n; [ flia Hiz | ].
cbn - [ iter_seq ].
rewrite (srng_summation_split _ i); [ | flia Hiz ].
rewrite srng_summation_split_last; [ | flia ].
rewrite srng_summation_shift; [ | flia Hiz ].
erewrite srng_summation_eq_compat. 2: {
  intros j Hj.
  now rewrite Nat.add_comm, Nat.add_sub.
}
cbn - [ iter_seq ].
...
(* blocked by the present implementation of discriminant
erewrite srng_summation_eq_compat; [ | easy | ]. 2: {  
  intros j Hj.
  rewrite (srng_summation_split _ (i - 1)); [ | flia Hiz ].
  rewrite Nat.sub_add; [ | easy ].
  easy.
}
cbn - [ iter_seq ].
...
rewrite srng_summation_split_first; [ | easy | flia ].
cbn - [ iter_seq ].
rewrite srng_mul_1_l.
rewrite (srng_summation_split _ i); [ | flia Hiz ].
rewrite srng_summation_split_last;[ | easy ].
...
rewrite all_0_srng_summation_0; [ | easy | ]. 2: {
  intros k Hk.
...
*)

(* If we add a row (column) of A multiplied by a scalar k to another
   row (column) of A, then the determinant will not change. *)
(* https://math.vanderbilt.edu/sapirmv/msapir/proofdet1.html *)
(* doing it only when the first row is 0; can be generalized later *)

Theorem det_add_row_mul_scal_row : ∀ M v k,
  is_square_mat M
  → mat_nrows M ≠ 0
  → determinant (mat_add_row_mul_scal_row M 0 v k) = determinant M.
Proof.
intros * Hsm Hrz.
unfold is_square_mat in Hsm.
remember
  (mk_mat
     (λ i j,
      if Nat.eq_dec i 0 then (v * mat_el M k j)%Srng else mat_el M i j)
     (mat_nrows M) (mat_ncols M)) as C eqn:Hc.
rewrite (det_sum_row_row _ M C Hrz); cycle 7. {
  now intros; rewrite Hc.
} {
  intros i j Hi.
  now cbn; destruct (Nat.eq_dec i 0).
} {
  intros i j Hi; rewrite Hc; cbn.
  now destruct (Nat.eq_dec i 0).
} {
  remember
    (mk_mat (λ i j, if Nat.eq_dec i 0 then mat_el M k j else mat_el M i j)
       (mat_nrows M) (mat_ncols M)) as D eqn:Hd.
  specialize (det_mul_row_0_by_scal D v) as H1.
  assert (H : mat_ncols D ≠ 0); [ subst D; cbn; congruence | ].
  specialize (H1 H); clear H.
  assert (H : mat_mul_row_0_by_scal D v = C). {
    unfold mat_mul_row_0_by_scal; rewrite Hc, Hd; cbn.
    apply matrix_eq; [ easy | easy | cbn ].
    intros i j Hi Hj.
    now destruct (Nat.eq_dec i 0).
  }
  rewrite H in H1; clear H.
  assert (H : determinant D = 0%Srng). {
    rewrite Hd.
Abort. (* blocked because needs the previous lemma
...
*)

(* proof that the swapping two rows negates the determinant  *)

Theorem det_swap_rows : ∀ M i j,
  is_square_mat M
  → i ≠ j
  → i < mat_nrows M
  → j < mat_nrows M
  → determinant (mat_swap_rows M i j) = (- determinant M)%Rng.
Proof.
intros * Hsm Hij Hi Hj.
(* look point 5 at
https://math.vanderbilt.edu/sapirmv/msapir/proofdet1.html
*)
Abort. (*
...
intros * Hsm Hij Hi Hj.
unfold is_square_mat in Hsm.
unfold determinant; cbn.
remember (mat_ncols M) as c eqn:Hc; symmetry in Hc.
rename Hsm into Hr.
destruct c; [ flia Hr Hi | ].
remember (mat_swap_rows M i j) as M' eqn:HM'.
cbn - [ iter_seq ].
rewrite rng_opp_summation; [ | easy | easy ].
destruct (Nat.eq_dec i 0) as [Hiz| Hiz]. {
  subst i.
  destruct c; [ flia Hr Hij Hj | ].
(**)
  symmetry.
  rewrite srng_summation_split_first; [ | easy | flia ].
  rewrite (srng_summation_split _ j); [ | flia Hr Hj ].
  rewrite srng_summation_split_last; [ | flia Hij ].
  cbn - [ iter_seq mat_el ].
  rewrite srng_mul_1_l.
  remember
    (Σ (j0 = 0, c),
     minus_one_pow j0 * mat_el (subm M 0 0) 0 j0 *
     det_loop (subm (subm M 0 0) 0 j0) c)%Rng as K5.
  remember
    (Σ (i = 2, j),
     - (minus_one_pow (i - 1) * mat_el M 0 (i - 1) *
        (Σ (j0 = 0, c),
         minus_one_pow j0 * mat_el (subm M 0 (i - 1)) 0 j0 *
         det_loop (subm (subm M 0 (i - 1)) 0 j0) c)))%Rng as K6.
  remember
    (Σ (j0 = 0, c),
     minus_one_pow j0 * mat_el (subm M 0 j) 0 j0 *
     det_loop (subm (subm M 0 j) 0 j0) c)%Rng as K7.
  remember
    (Σ (i = j + 1, S c),
     - (minus_one_pow i * mat_el M 0 i *
        (Σ (j0 = 0, c),
         minus_one_pow j0 * mat_el (subm M 0 i) 0 j0 *
         det_loop (subm (subm M 0 i) 0 j0) c)))%Rng as K8.
(* I should isolate "mat_el M j j" from K5 in order to get its
   product with "mat_el M 0 0", the rest being a sub-discriminant
   which is supposed to be equal to the equivalent in M' in the
   rhs *)
...
  symmetry.
...
  rewrite srng_summation_split_first; [ symmetry | easy | flia ].
  rewrite srng_summation_split_first; [ symmetry | easy | flia ].
  rewrite (srng_summation_split _ j); [ symmetry | flia Hr Hj ].
  rewrite (srng_summation_split _ j); [ symmetry | flia Hr Hj ].
  rewrite srng_summation_split_last; [ symmetry | flia Hij ].
  rewrite srng_summation_split_last; [ symmetry | flia Hij ].
  cbn - [ iter_seq mat_el ].
  do 2 rewrite srng_mul_1_l.
  remember
     (Σ (j0 = 0, c),
      minus_one_pow j0 * mat_el (subm M' 0 0) 0 j0 *
      det_loop (subm (subm M' 0 0) 0 j0) c)%Rng as K1.
  remember
    (Σ (i = 2, j),
     minus_one_pow (i - 1) * mat_el M' 0 (i - 1) *
     (Σ (j0 = 0, c),
      minus_one_pow j0 * mat_el (subm M' 0 (i - 1)) 0 j0 *
      det_loop (subm (subm M' 0 (i - 1)) 0 j0) c))%Rng as
      K2.
  remember
    (Σ (j0 = 0, c),
     minus_one_pow j0 * mat_el (subm M' 0 j) 0 j0 *
     det_loop (subm (subm M' 0 j) 0 j0) c)%Rng as K3.
  remember
    (Σ (i = j + 1, S c),
     minus_one_pow i * mat_el M' 0 i *
     (Σ (j0 = 0, c),
      minus_one_pow j0 * mat_el (subm M' 0 i) 0 j0 *
      det_loop (subm (subm M' 0 i) 0 j0) c))%Rng as K4.
  remember
    (Σ (j0 = 0, c),
     minus_one_pow j0 * mat_el (subm M 0 0) 0 j0 *
     det_loop (subm (subm M 0 0) 0 j0) c)%Rng as K5.
  remember
    (Σ (i = 2, j),
     - (minus_one_pow (i - 1) * mat_el M 0 (i - 1) *
        (Σ (j0 = 0, c),
         minus_one_pow j0 * mat_el (subm M 0 (i - 1)) 0 j0 *
         det_loop (subm (subm M 0 (i - 1)) 0 j0) c)))%Rng as K6.
  remember
    (Σ (j0 = 0, c),
     minus_one_pow j0 * mat_el (subm M 0 j) 0 j0 *
     det_loop (subm (subm M 0 j) 0 j0) c)%Rng as K7.
  remember
    (Σ (i = j + 1, S c),
     - (minus_one_pow i * mat_el M 0 i *
        (Σ (j0 = 0, c),
         minus_one_pow j0 * mat_el (subm M 0 i) 0 j0 *
         det_loop (subm (subm M 0 i) 0 j0) c)))%Rng as K8.
...
*)

(* proof that det_from_row is equal to determinant *)

Theorem det_from_row_is_det : ∀ M i,
  mat_ncols M ≠ 0
  → det_from_row M i = determinant M.
Proof.
intros * Hcz.
destruct (Nat.eq_dec i 0) as [Hiz| Hiz]. {
  subst i.
  unfold determinant, det_from_row.
  cbn - [ iter_seq ].
  rewrite srng_mul_1_l.
  remember (mat_ncols M) as c eqn:Hc; symmetry in Hc.
  destruct c; [ easy | clear Hcz ].
  now rewrite Nat.sub_succ, Nat.sub_0_r.
}
apply not_eq_sym in Hiz.
Abort. (*
...
specialize (det_swap_rows M Hiz) as H.
apply (f_equal rng_opp) in H.
rewrite rng_opp_involutive in H.
rewrite <- H; clear H.
apply not_eq_sym in Hiz.
unfold det_from_row, determinant.
cbn - [ iter_seq ].
remember (mat_ncols M) as c eqn:Hc; symmetry in Hc.
destruct c; [ easy | clear Hcz ].
rewrite Nat.sub_succ, Nat.sub_0_r.
cbn - [ iter_seq ].
rewrite srng_mul_summation_distr_l; [ | easy ].
rewrite rng_opp_summation; [ | easy | easy ].
apply srng_summation_eq_compat; [ easy | ].
intros j Hj.
rewrite srng_mul_comm.
rewrite <- srng_mul_assoc.
rewrite <- rng_mul_opp_r.
f_equal.
rewrite srng_mul_comm; symmetry.
apply rng_opp_inj.
rewrite rng_opp_involutive.
...
*)

(*
End in_ring.
Require Import ZArith.
Open Scope Z_scope.
Existing Instance Z_ring_op.
Compute determinant (mat_of_list_list 0 [[1; 2]; [3; 4]]).
Compute determinant (mat_of_list_list 0 [[-2; 2; -3]; [-1; 1; 3]; [2; 0; -1]]). (* 18: seems good *)
*)

(* identity matrix of dimension n *)

Definition mI n : matrix T :=
  mk_mat (λ i j, if Nat.eq_dec i j then 1%Srng else 0%Srng) n n.

End in_ring.

Section in_ring.

Context {T : Type}.
Context {ro : ring_op T}.
Context (so : semiring_op T).
Context {sp : semiring_prop T}.
Context {scp : sring_comm_prop T}.
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
erewrite srng_summation_eq_compat. 2: {
  intros k Hk.
  now apply srng_mul_summation_distr_l.
}
cbn - [ iter_seq ].
rewrite srng_summation_summation_exch'; [ | easy ].
apply srng_summation_eq_compat.
intros k Hk.
erewrite srng_summation_eq_compat. 2: {
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

Definition squ_mat_zero n :=
  mk_mat (λ i j, 0%Srng) n n.
Definition squ_mat_one n :=
  mk_mat (λ i j, if Nat.eq_dec i j then 1%Srng else 0%Srng) n n.

Definition squ_mat_semiring_op n : semiring_op (matrix T) :=
  {| srng_zero := squ_mat_zero n;
     srng_one := squ_mat_one n;
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
  det_loop M (mat_ncols M) = determinant M.
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
Arguments squ_mat_one {T so}.
Arguments squ_mat_zero {T so}.
Arguments squ_mat_semiring_op {T so}.
Arguments subm {T} M%M i%nat j%nat.
Arguments vect_add {T so} U%V V%V.
Arguments vect_sub {T ro so} U%V V%V.
Arguments vect_opp {T ro} V%V.
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
Notation "- V" := (vect_opp V) : V_scope.

End matrix_Notations.
