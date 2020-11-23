(* matrices *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Init.Nat.

Require Import Misc.
Require Import Semiring SRsummation.

(* matrices *)

Record matrix (m n : nat) T := mk_mat0
  { mat_el : nat → nat → T }.

Definition mk_mat {T} (f : nat → nat → T) m n := mk_mat0 m n f.
Definition mat_nrows {m n T} (M : matrix m n T) := m.
Definition mat_ncols {m n T} (M : matrix m n T) := n.

(* function extensionality required for matrices *)
Axiom matrix_eq : ∀ m n T (MA MB : matrix m n T),
  (∀ i j, i < mat_nrows MA → j < mat_ncols MB →
   mat_el MA i j = mat_el MB i j)
  → MA = MB.

Definition list_list_nrows T (ll : list (list T)) :=
  length ll.

Definition list_list_ncols T (ll : list (list T)) :=
  length (hd [] ll).

Definition list_list_of_mat m n T (M : matrix m n T) : list (list T) :=
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

Context {m n p : nat}.
Context {T : Type}.
Context {ro : ring_op T}.
Context (so : semiring_op T).
Context {sp : semiring_prop T}.
Context {rp : ring_prop T}.

(* addition *)

Definition mat_add {so : semiring_op T} (MA MB : matrix m n T) :
  matrix m n T :=
  {| mat_el i j := (mat_el MA i j + mat_el MB i j)%Srng |}.

(* qu'est-ce que ça fout là, ça ? faudrait que je le mette ailleurs
   dans Semiring.v, par exemple, ou chais pas *)

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
     srng_mul_comm := Nat.mul_comm;
     srng_mul_assoc := Nat.mul_assoc;
     srng_mul_1_l := Nat.mul_1_l;
     srng_mul_add_distr_l := Nat.mul_add_distr_l;
     srng_mul_0_l := Nat.mul_0_l |}.

(*
End in_ring.
Compute (list_list_of_mat (mat_add add (mat_of_list_list 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (mat_of_list_list 0 [[1; 2]; [3; 4]; [5; 6]; [7; 8]]))).
Compute (list_list_of_mat (mat_add add (mat_of_list_list 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (mat_of_list_list 0 [[1; 2]; [3; 4]; [5; 6]; [7; 8]]))).
*)

(* multiplication *)

Definition mat_mul {so : semiring_op T}
     (MA : matrix m n T) (MB : matrix n p T) : matrix m p T :=
  {| mat_el i k :=
       (Σ (j = 0, mat_ncols MA - 1), mat_el MA i j * mat_el MB j k)%Srng |}.

(*
End in_ring.
Compute (let _ := nat_semiring_op in list_list_of_mat (mat_mul (mat_of_list_list 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (mat_of_list_list 0 [[1; 2]; [3; 4]; [5; 6]; [7; 8]]))).
*)

Theorem mat_mul_nrows : ∀ (A : matrix m n T) (B : matrix n p T),
  mat_nrows (mat_mul A B) = mat_nrows A.
Proof. easy. Qed.

Theorem mat_mul_ncols : ∀ (A : matrix m n T) (B : matrix n p T),
  mat_ncols (mat_mul A B) = mat_ncols B.
Proof. easy. Qed.

(* opposite *)

Definition mat_opp (M : matrix m n T) : matrix m n T :=
  {| mat_el i j := (- mat_el M i j)%Rng |}.

(* subtraction *)

Definition mat_sub MA MB :=
  mat_add MA (mat_opp MB).

(* *)

Definition is_square_mat {m n} (M : matrix m n T) :=
  mat_nrows M = mat_ncols M.

(* vector *)

Record vector (m : nat) T := mk_vect0
  { vect_el : nat → T }.

Definition mk_vect {T} (f : nat → T) m := mk_vect0 m f.
Definition vect_nrows {m T} (V : vector m T) := m.

(* function extensionality required for vectors *)
Axiom vector_eq : ∀ m T (VA VB : vector m T),
  (∀ i, i < vect_nrows VA → vect_el VA i = vect_el VB i)
  → VA = VB.

Definition vect_of_list {T} d (l : list T) :=
  mk_vect (λ i, nth i l d) (length l).
Definition list_of_vect {m T} (v : vector m T) :=
  map (vect_el v) (seq 0 (vect_nrows v)).

Definition vect_zero n := mk_vect (λ _, 0%Srng) n.

(* addition, subtraction of vector *)

Definition vect_add (U V : vector m T) :=
  mk_vect (λ i, (vect_el U i + vect_el V i)%Srng) m.
Definition vect_opp (V : vector m T) :=
  mk_vect (λ i, (- vect_el V i)%Rng) m.

Definition vect_sub (U V : vector m T) := vect_add U (vect_opp V).

(* vector from a matrix column *)

Definition vect_of_mat_col (M : matrix m n T) j :=
  mk_vect (λ i, mat_el M i j) m.

(* concatenation of a matrix and a vector *)

Definition mat_vect_concat (M : matrix m n T) (V : vector m T) :=
  mk_mat
    (λ i j, if Nat.eq_dec j (mat_ncols M) then vect_el V i else mat_el M i j)
    m (n + 1).

(* multiplication of a matrix by a vector *)

Definition mat_mul_vect_r (M : matrix m n T) (V : vector m T) :=
  mk_vect (λ i, (Σ (j = 0, mat_ncols M - 1), mat_el M i j * vect_el V j)%Srng)
    n.

(* multiplication of a vector by a scalar *)

Definition vect_mul_scal_l μ (V : vector m T) :=
  mk_vect (λ i, μ * vect_el V i)%Srng m.

(* multiplication of a matrix by a scalar *)

Definition mat_mul_scal_l μ (M : matrix m n _) :=
  mk_mat (λ i j, μ * mat_el M i j)%Srng m n.

(* matrix without row i and column j *)

Definition subm {m n} (M : matrix m n T) i j :=
  mk_mat
    (λ k l,
       if lt_dec k i then
         if lt_dec l j then mat_el M k l
         else mat_el M k (l + 1)
       else
         if lt_dec l j then mat_el M (k + 1) l
         else mat_el M (k + 1) (l + 1))
    (m - 1) (n - 1).

(* (-1) ^ n *)

Definition minus_one_pow n :=
  match n mod 2 with
  | 0 => 1%Rng
  | _ => (- 1%Srng)%Rng
  end.

(* determinant *)

Fixpoint det_loop {m n} (M : matrix m n T) k :=
  match k with
  | 0 => 1%Rng
  | S k' =>
      (Σ (j = 0, k'),
       minus_one_pow j * mat_el M 0 j * det_loop (subm M 0 j) k')%Rng
  end.

Definition determinant {m n} (M : matrix m n T) := det_loop M n.

(* the following versions of computing the determinant should
   (to be proven) be equivalent; perhaps could help for proving
   Cramer's rule of resolving equations *)

Definition det_from_row (M : matrix m n T) i :=
  (minus_one_pow i *
   Σ (j = 0, mat_ncols M - 1),
     minus_one_pow j * mat_el M i j * determinant (subm M i j))%Rng.

Definition det_from_col (M : matrix m n T) j :=
  (minus_one_pow j *
   Σ (i = 0, mat_nrows M - 1),
     minus_one_pow i * mat_el M i j * determinant (subm M i j))%Rng.

(* *)

Definition mat_mul_row_0_by_scal {m n} (M : matrix m n T) s :=
  mk_mat
    (λ i j,
     if Nat.eq_dec i 0 then (s * mat_el M i j)%Srng else mat_el M i j)
    m n.

Definition mat_swap_rows {m n} (M : matrix m n T) i1 i2 :=
  mk_mat
    (λ i j,
     if Nat.eq_dec i i1 then mat_el M i2 j
     else if Nat.eq_dec i i2 then mat_el M i1 j
     else mat_el M i j) m n.

Definition mat_add_row_mul_scal_row {m n} (M : matrix m n T) i1 v i2 :=
  mk_mat
    (λ i j,
     if Nat.eq_dec i i1 then (mat_el M i1 j + v * mat_el M i2 j)%Srng
     else mat_el M i j)
   m n.

(* If we multiply a row (column) of A by a number, the determinant of
   A will be multiplied by the same number. *)
(* https://math.vanderbilt.edu/sapirmv/msapir/proofdet1.html *)

(* Well, since my definition of the discriminant only covers the
   row 0, we can prove that only when i=0; this will able us to
   prove next theorems, swapping rows by going via row 0 *)

Theorem det_mul_row_0_by_scal : ∀ {m n} (A : matrix m n T) v,
  mat_ncols A ≠ 0
  → determinant (mat_mul_row_0_by_scal A v) = (v * determinant A)%Srng.
Proof.
clear m n.
intros * Hcz.
unfold determinant; cbn.
remember (mat_ncols A) as c eqn:Hc; symmetry in Hc.
destruct c; [ easy | clear Hcz ].
unfold mat_ncols in Hc; subst n.
cbn - [ iter_seq ].
rewrite srng_mul_summation_distr_l; [ | easy ].
apply srng_summation_eq_compat; [ easy | ].
intros j Hj.
rewrite (srng_mul_comm (minus_one_pow j)).
do 2 rewrite <- srng_mul_assoc.
f_equal.
rewrite (srng_mul_comm (mat_el A 0 j)).
do 2 rewrite <- srng_mul_assoc.
f_equal.
rewrite srng_mul_comm; f_equal.
f_equal.
apply matrix_eq; cbn.
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

Theorem det_sum_row_row : ∀ (A B C : matrix n n T),
  n ≠ 0
  → (∀ j, mat_el A 0 j = (mat_el B 0 j + mat_el C 0 j)%Srng)
  → (∀ i j, i ≠ 0 → mat_el B i j = mat_el A i j)
  → (∀ i j, i ≠ 0 → mat_el C i j = mat_el A i j)
  → determinant A = (determinant B + determinant C)%Srng.
Proof.
intros * Hnz Hbc Hb Hc.
unfold determinant.
destruct n; [ easy | clear Hnz ].
cbn - [ iter_seq ].
assert (Hab : ∀ j, subm A 0 j = subm B 0 j). {
  intros.
  apply matrix_eq; cbn.
  intros i j' Hi Hj'.
  destruct (lt_dec j' j); symmetry; apply Hb; flia.
}
assert (Hac : ∀ j, subm A 0 j = subm C 0 j). {
  intros.
  apply matrix_eq; cbn.
  intros i j' Hi Hj'.
  destruct (lt_dec j' j); symmetry; apply Hc; flia.
}
erewrite srng_summation_eq_compat; [ | easy | ]. 2: {
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

Theorem det_two_rows_are_eq : ∀ (A : matrix n n T) i,
  0 < i < mat_nrows A
  → mat_ncols A ≠ 0
  → (∀ j, mat_el A i j = mat_el A 0 j)
  → determinant A = 0%Srng.
Proof.
intros * Hiz Hcz Ha.
unfold mat_nrows in Hiz.
unfold determinant.
(*
rewrite Hsm in Hiz.
remember (mat_ncols A) as n eqn:Hn; symmetry in Hn.
*)
destruct n; [ easy | clear Hcz ].
cbn - [ iter_seq ].
(**)
Abort.
(* blocked by the present implementation of discriminant
destruct n; [ flia Hiz | ].
cbn - [ iter_seq ].
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

Theorem det_add_row_mul_scal_row : ∀ (M : matrix n n T) v k,
  mat_nrows M ≠ 0
  → determinant (mat_add_row_mul_scal_row M 0 v k) = determinant M.
Proof.
intros * Hrz.
remember
  (mk_mat
     (λ i j,
      if Nat.eq_dec i 0 then (v * mat_el M k j)%Srng else mat_el M i j)
     (mat_nrows M) (mat_ncols M)) as C eqn:Hc.
rewrite (det_sum_row_row _ M C Hrz); cycle 7. {
  intros i j Hi.
  cbn; destruct (Nat.eq_dec i 0).
Abort. (* blocked because needs the previous lemma
          and because of change of type matrix that
          includes now its dimensions
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
...
*)

(* proof that the swapping two rows negates the determinant  *)

Theorem det_swap_rows : ∀ (M : matrix n n T) i j,
  i ≠ j
  → i < mat_nrows M
  → j < mat_nrows M
  → determinant (mat_swap_rows M i j) = (- determinant M)%Rng.
Proof.
intros * Hij Hi Hj.
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
Abort. (*
  now rewrite Nat.sub_succ, Nat.sub_0_r.
}
apply not_eq_sym in Hiz.
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

(* identity matrix of size n *)

Definition mI n : matrix n n T :=
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

Arguments det_loop {T ro so m n} M%M k%nat.
Arguments mat_mul_scal_l {m n T so} _ M%M.
Arguments mat_nrows {m n T} M%M.
Arguments mat_ncols {m n T} M%M.
Arguments mat_sub {m n T ro so} MA%M MB%M.
Arguments mI {T so} n%nat.
Arguments minus_one_pow {T ro so}.
Arguments determinant {T ro so m n} M%M.
Arguments subm {T m n} M%M i%nat j%nat.

Notation "A + B" := (mat_add A B) : M_scope.
Notation "A - B" := (mat_sub A B) : M_scope.
Notation "A * B" := (mat_mul A B) : M_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.
Notation "- A" := (mat_opp A) : M_scope.

(* associativity of multiplication *)

Theorem mat_mul_assoc {m n p q} :
  ∀ (MA : matrix m n T) (MB : matrix n p T) (MC : matrix p q T),
  (MA * (MB * MC))%M = ((MA * MB) * MC)%M.
Proof.
intros.
apply matrix_eq.
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
unfold mat_ncols in Hcb |-*; subst cb.
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

Definition comatrix {m n} (M : matrix m n T) : matrix m n T :=
  {| mat_el i j := (minus_one_pow (i + j) * determinant (subm M i j))%Srng |}.

(* matrix transpose *)

Definition mat_transp {m n} (M : matrix m n T) : matrix n m T :=
  {| mat_el i j := mat_el M j i |}.

(* combinations of submatrix and other *)

Theorem submatrix_sub {m n} : ∀ (MA MB : matrix m n T) i j,
  subm (MA - MB)%M i j = (subm MA i j - subm MB i j)%M.
Proof.
intros.
apply matrix_eq; cbn.
intros k l Hk Hl.
now destruct (lt_dec k i), (lt_dec l j).
Qed.

Theorem submatrix_mul_scal_l {m n} : ∀ (μ : T) (M : matrix m n T) i j,
  subm (μ × M)%M i j = (μ × subm M i j)%M.
Proof.
intros.
apply matrix_eq; cbn.
intros k l Hk Hl.
now destruct (lt_dec k i), (lt_dec l j).
Qed.

Theorem submatrix_nrows {m n} : ∀ (M : matrix m n T) i j,
  mat_nrows (subm M i j) = mat_nrows M - 1.
Proof. easy. Qed.

... (* faut voir... c'est utilisé dans CharacPolyn.v *)

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
