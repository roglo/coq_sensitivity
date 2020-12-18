(* matrices *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Bool.
Import List List.ListNotations.
Require Import Init.Nat.

Require Import Misc.
Require Import RingLike RLsummation.

(* matrices *)

Record matrix (m n : nat) T := mk_mat
  { mat_el : nat → nat → T }.

(*
Definition mat_nrows {m n T} (M : matrix m n T) := m.
Definition mat_ncols {m n T} (M : matrix m n T) := n.
*)

(* function extensionality required for matrices *)
Axiom matrix_eq : ∀ m n T (MA MB : matrix m n T),
  (∀ i j, i < m → j < n → mat_el MA i j = mat_el MB i j)
  → MA = MB.

Theorem matrix_neq : ∀ m n T (MA MB : matrix m n T),
  ¬ (∀ i j, i < m → j < n → mat_el MA i j = mat_el MB i j)
  → MA ≠ MB.
Proof.
intros * Hab.
intros H.
subst MB.
now apply Hab.
Qed.

Definition list_list_nrows T (ll : list (list T)) :=
  length ll.

Definition list_list_ncols T (ll : list (list T)) :=
  length (hd [] ll).

Definition list_list_of_mat m n T (M : matrix m n T) : list (list T) :=
  map (λ i, map (mat_el M i) (seq 0 m)) (seq 0 n).

Definition list_list_el T d (ll : list (list T)) i j : T :=
  nth j (nth i ll []) d.

Definition mat_of_list_list T d (ll : list (list T)) :
  matrix (list_list_nrows ll) (list_list_ncols ll) T :=
  mk_mat (list_list_nrows ll) (list_list_ncols ll) (list_list_el d ll).

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

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.

(* addition *)

Definition mat_add {ro : ring_like_op T} {m n} (MA MB : matrix m n T) :
  matrix m n T :=
  {| mat_el i j := (mat_el MA i j + mat_el MB i j)%F |}.

(* multiplication *)

Definition mat_mul {ro : ring_like_op T} {m n p}
    (MA : matrix m n T) (MB : matrix n p T) : matrix m p T :=
  {| mat_el i k := (Σ (j = 0, n - 1), mat_el MA i j * mat_el MB j k)%F |}.

(*
Theorem mat_mul_nrows {m n p} : ∀ (A : matrix T m n) (B : matrix T n p),
  mat_nrows (mat_mul A B) = mat_nrows A.
Proof. easy. Qed.

Theorem mat_mul_ncols : ∀ A B, mat_ncols (mat_mul A B) = mat_ncols B.
Proof. easy. Qed.
*)

(* opposite *)

Definition mat_opp {ro : ring_like_op T} {m n} (M : matrix m n T) :
  matrix m n T :=
  {| mat_el i j := (- mat_el M i j)%F |}.

(* subtraction *)

Definition mat_sub {m n} (MA MB : matrix m n T) :=
  mat_add MA (mat_opp MB).

(* *)

(*
Definition is_square_mat {m n} (M : matrix m n T) := m = n.
*)

(* vector *)

Record vector (n : nat) T := mk_vect
  { vect_el : nat → T }.

(* function extensionality required for vectors *)
Axiom vector_eq : ∀ n T (VA VB : vector n T),
  (∀ i, i < n → vect_el VA i = vect_el VB i)
  → VA = VB.

Definition vect_of_list {T} d (l : list T) :=
  mk_vect (length l) (λ i, nth i l d).
Definition list_of_vect {n T} (v : vector n T) :=
  map (vect_el v) (seq 0 n).

Definition vect_zero n := mk_vect n (λ _, 0%F).

(* addition, subtraction of vector *)

Definition vect_add {n} (U V : vector n T) :=
  mk_vect n (λ i, (vect_el U i + vect_el V i)%F).
Definition vect_opp {n} (V : vector n T) :=
  mk_vect n (λ i, (- vect_el V i)%F).

Definition vect_sub {n} (U V : vector n T) := vect_add U (vect_opp V).

(* vector from a matrix column *)

Definition vect_of_mat_col {m n} (M : matrix m n T) j :=
  mk_vect m (λ i, mat_el M i j).

(* concatenation of a matrix and a vector *)

Definition mat_vect_concat {m n} (M : matrix m n T) (V : vector m T) :
  matrix m (n + 1) T :=
  mk_mat m (n + 1)
    (λ i j, if Nat.eq_dec j n then vect_el V i else mat_el M i j).

(* multiplication of a matrix by a vector *)

Definition mat_mul_vect_r {m n} (M : matrix m n T) (V : vector n T) :=
  mk_vect m (λ i, (Σ (j = 0, n - 1), mat_el M i j * vect_el V j)%F).

(* multiplication of a vector by a scalar *)

Definition vect_mul_scal_l s {n} (V : vector n T) :=
  mk_vect n (λ i, s * vect_el V i)%F.

(* dot product *)

Definition vect_dot_product {n} (U V : vector n T) :=
  (Σ (i = 0, n - 1), vect_el U i * vect_el V i)%F.

(* multiplication of a matrix by a scalar *)

Definition mat_mul_scal_l {m n} s (M : matrix m n T) :=
  mk_mat m n (λ i j, s * mat_el M i j)%F.

(* matrix without row i and column j *)

Definition subm {m n} (M : matrix m n T) i j :=
  mk_mat (m - 1) (n - 1)
    (λ k l,
       if lt_dec k i then
         if lt_dec l j then mat_el M k l
         else mat_el M k (l + 1)
       else
         if lt_dec l j then mat_el M (k + 1) l
         else mat_el M (k + 1) (l + 1)).

(* matrix whose k-th column is replaced by a vector *)

Definition mat_repl_vect {m n} k (M : matrix m n T) (V : vector m T) :=
  mk_mat m n (λ i j, if Nat.eq_dec j k then vect_el V i else mat_el M i j).

(* (-1) ^ n *)

Definition minus_one_pow n :=
  match n mod 2 with
  | 0 => 1%F
  | _ => (- 1%F)%F
  end.

(* determinant *)

Fixpoint det_loop {n} (M : matrix n n T) i :=
  match i with
  | 0 => 1%F
  | S i' =>
      (Σ (j = 0, i'),
       minus_one_pow j * mat_el M 0 j * det_loop (subm M 0 j) i')%F
  end.

Definition determinant {n} (M : matrix n n T) := det_loop M n.

(* *)

Declare Scope V_scope.
Delimit Scope V_scope with V.

Arguments vect_el {n}%nat {T} v%V.

Notation "U + V" := (vect_add U V) : V_scope.
Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.

(* the following versions of computing the determinant should
   (to be proven) be equivalent; perhaps could help for proving
   Cramer's rule of resolving equations *)

Definition det_from_row {n} (M : matrix n n T) i :=
  (minus_one_pow i *
   Σ (j = 0, n - 1),
     minus_one_pow j * mat_el M i j * determinant (subm M i j))%F.

Definition det_from_col {n} (M : matrix n n T) j :=
  (minus_one_pow j *
   Σ (i = 0, n - 1),
     minus_one_pow i * mat_el M i j * determinant (subm M i j))%F.

(* *)

(* to be updated to new definition matrix m n T  if I need them ...

Definition mat_mul_row_by_scal k M s :=
  mk_mat
    (λ i j,
     if Nat.eq_dec i k then (s * mat_el M i j)%F else mat_el M i j)
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
     if Nat.eq_dec i i1 then (mat_el M i1 j + v * mat_el M i2 j)%F
     else mat_el M i j)
   (mat_nrows M) (mat_nrows M).

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
  → (∀ j, mat_el A 0 j = (mat_el B 0 j + mat_el C 0 j)%F)
  → (∀ i j, i ≠ 0 → mat_el B i j = mat_el A i j)
  → (∀ i j, i ≠ 0 → mat_el C i j = mat_el A i j)
  → determinant A = (determinant B + determinant C)%F.
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
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite Hbc.
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_add_distr_r.
  rewrite Hab at 1.
  rewrite Hac at 1.
  easy.
}
cbn - [ iter_seq ].
now apply rngl_summation_add_distr.
Qed.
*)

(* null matrix of dimension m × n *)

Definition mZ m n : matrix m n T :=
  mk_mat m n (λ i j, 0%F).

(* identity square matrix of dimension n *)

Definition mI n : matrix n n T :=
  mk_mat n n (λ i j, if Nat.eq_dec i j then 1%F else 0%F).

End a.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.

Declare Scope M_scope.
Delimit Scope M_scope with M.

Arguments det_loop {T ro} {n}%nat M%M i%nat.
(*
Arguments is_square_mat {T} M%M.
*)
Arguments mat_mul_scal_l {T ro m n} s%F M%M.
(*
Arguments mat_nrows {T} m%M.
Arguments mat_ncols {T} m%M.
*)
Arguments mat_sub {T ro m n} MA%M MB%M.
Arguments mI {T ro} n%nat.
Arguments mZ {T ro} (m n)%nat.
Arguments minus_one_pow {T ro}.
Arguments determinant {T ro n} M%M.
Arguments subm {T m n} M%M i%nat j%nat.
Arguments vect_zero {T ro} n%nat.

Notation "A + B" := (mat_add A B) : M_scope.
Notation "A - B" := (mat_sub A B) : M_scope.
Notation "A * B" := (mat_mul A B) : M_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.
Notation "- A" := (mat_opp A) : M_scope.

Declare Scope V_scope.
Delimit Scope V_scope with V.

Arguments mat_mul_vect_r {T ro m n} M%M V%V.
Arguments vect_mul_scal_l {T ro} s%F {n}%nat V%V.
Arguments vect_dot_product {T}%type {ro n} (U V)%V.
Arguments vect_el {n}%nat {T}%type v%V.

Notation "A • V" := (mat_mul_vect_r A V) (at level 40) : V_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.
Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.
Notation "U · V" := (vect_dot_product U V) (at level 40) : V_scope.

(* *)

Theorem mat_fold_sub : ∀ {m n} (MA MB : matrix m n T),
  (MA + - MB = MA - MB)%M.
Proof. easy. Qed.

(* commutativity of addition *)

Theorem mat_add_comm : ∀ {m n} (MA MB : matrix m n T), (MA + MB = MB + MA)%M.
Proof.
intros.
apply matrix_eq.
intros * Hi Hj.
apply rngl_add_comm.
Qed.

(* associativity of addition *)

Theorem mat_add_add_swap : ∀ {m n} (MA MB MC : matrix m n T),
  (MA + MB + MC = MA + MC + MB)%M.
Proof.
intros.
apply matrix_eq.
intros i j Hi Hj.
apply rngl_add_add_swap.
Qed.

Theorem mat_add_assoc : ∀ {m n} (MA MB MC : matrix m n T),
  (MA + (MB + MC) = (MA + MB) + MC)%M.
Proof.
intros.
apply matrix_eq.
intros i j Hi Hj.
apply rngl_add_assoc.
Qed.

(* addition to zero *)

Theorem mat_add_0_l : ∀ {m n} (M : matrix m n T), (mZ m n + M)%M = M.
Proof.
intros.
apply matrix_eq.
intros * Hi Hj.
apply rngl_add_0_l.
Qed.

(* addition left and right with opposite *)

Theorem mat_add_opp_l {m n} :
  rngl_has_opp = true →
  ∀ (M : matrix m n T), (- M + M = mZ m n)%M.
Proof.
intros Hro *.
apply matrix_eq.
intros * Hi Hj.
now apply rngl_add_opp_l.
Qed.

Theorem mat_add_opp_r :
  rngl_has_opp = true →
  ∀ {m n} (M : matrix m n T),
  (M - M = mZ m n)%M.
Proof.
intros Hro *.
apply matrix_eq.
intros * Hi Hj.
specialize rngl_add_opp_r as H.
cbn; unfold rngl_sub in H.
rewrite Hro in H.
apply H.
Qed.

(*
(* multiplication of a square matrix by a scalar is square *)

Theorem mat_mul_scal_l_is_square : ∀ a M,
  is_square_mat M
  → is_square_mat (a × M).
Proof. intros. easy. Qed.
*)

(* multiplication left and right with identity *)

Theorem mat_mul_1_l : ∀ {n} (M : matrix n n T), (mI n * M)%M = M.
Proof.
intros.
apply matrix_eq.
cbn - [ iter_seq ].
intros * Hi Hj.
rewrite (rngl_summation_split _ i); [ | flia Hi ].
rewrite rngl_summation_split_last; [ | flia ].
destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
rewrite rngl_mul_1_l.
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec i (k - 1)) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_l.
}
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec i k) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_l.
}
now rewrite rngl_add_0_l, rngl_add_0_r.
Qed.

Theorem mat_mul_1_r : ∀ {n} (M : matrix n n T), (M * mI n)%M = M.
Proof.
intros.
apply matrix_eq.
cbn - [ iter_seq ].
intros * Hi Hj.
rewrite (rngl_summation_split _ j); [ | flia Hj ].
rewrite rngl_summation_split_last; [ | flia ].
destruct (Nat.eq_dec j j) as [H| H]; [ clear H | easy ].
rewrite rngl_mul_1_r.
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec (k - 1) j) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_r.
}
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec k j) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_r.
}
now rewrite rngl_add_0_l, rngl_add_0_r.
Qed.

Theorem vect_mul_1_l : ∀ {n} (V : vector n T), (mI n • V)%V = V.
Proof.
intros.
apply vector_eq.
cbn - [ iter_seq ].
intros * Hi.
rewrite (rngl_summation_split _ i); [ | flia Hi ].
rewrite rngl_summation_split_last; [ | flia ].
destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
rewrite rngl_mul_1_l.
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec i (k - 1)) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_l.
}
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec i k) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_l.
}
now rewrite rngl_add_0_l, rngl_add_0_r.
Qed.

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
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  now apply rngl_mul_summation_distr_l.
}
cbn - [ iter_seq ].
rewrite rngl_summation_summation_exch'; [ | easy ].
apply rngl_summation_eq_compat.
intros k Hk.
erewrite rngl_summation_eq_compat. 2: {
  intros l Hl.
  now rewrite rngl_mul_assoc.
}
cbn - [ iter_seq ].
symmetry.
now apply rngl_mul_summation_distr_r.
Qed.

(* left distributivity of multiplication over addition *)

Theorem mat_mul_add_distr_l {m n p} :
  ∀ (MA : matrix m n T) (MB : matrix n p T) (MC : matrix n p T),
  (MA * (MB + MC) = MA * MB + MA * MC)%M.
Proof.
intros.
apply matrix_eq.
intros i j Hi Hj.
cbn - [ iter_seq ].
cbn in Hi, Hj.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  apply rngl_mul_add_distr_l.
}
cbn - [ iter_seq ].
now apply rngl_summation_add_distr.
Qed.

(* right distributivity of multiplication over addition *)

Theorem mat_mul_add_distr_r {m n p} :
  ∀ (MA : matrix m n T) (MB : matrix m n T) (MC : matrix n p T),
  ((MA + MB) * MC = MA * MC + MB * MC)%M.
Proof.
intros.
apply matrix_eq.
intros i j Hi Hj.
cbn - [ iter_seq ].
cbn in Hi, Hj.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  apply rngl_mul_add_distr_r.
}
cbn - [ iter_seq ].
now rewrite rngl_summation_add_distr.
Qed.

(* left distributivity of multiplication by scalar over addition *)

Theorem mat_mul_scal_l_add_distr_r {m n} : ∀ a b (M : matrix m n T),
  ((a + b)%F × M)%M = (a × M + b × M)%M.
Proof.
intros.
apply matrix_eq.
intros * Hi Hj; cbn.
apply rngl_mul_add_distr_r.
Qed.

(* associativity of multiplication by scalar *)

Theorem mat_mul_scal_l_mul_assoc {m n} : ∀ a b (M : matrix m n T),
  (a × (b × M))%M = ((a * b)%F × M)%M.
Proof.
intros.
apply matrix_eq.
intros * Hi Hj; cbn.
apply rngl_mul_assoc.
Qed.

Theorem vect_mul_scal_l_mul_assoc {n} : ∀ a b (V : vector n T),
  (a × (b × V))%V = ((a * b)%F × V)%V.
Proof.
intros.
apply vector_eq.
intros * Hi; cbn.
apply rngl_mul_assoc.
Qed.

Theorem vect_mul_scal_reg_r :
  rngl_has_dec_eq = true →
  rngl_has_inv = true ∨ rngl_has_no_inv_but_div = true →
  ∀ {n} (V : vector n T) a b,
  V ≠ vect_zero n
  → (a × V = b × V)%V
  → a = b.
Proof.
intros Hde Hii * Hvz Hab.
assert (Hiv : ∀ i, vect_el (a × V)%V i = vect_el (b × V)%V i). {
  intros i.
  now rewrite Hab.
}
unfold vect_mul_scal_l in Hiv.
cbn in Hiv.
assert (Hn : ¬ ∀ i, i < n → vect_el V i = 0%F). {
  intros H; apply Hvz.
  apply vector_eq.
  cbn; intros * Hi.
  now apply H.
}
assert (∃ i, vect_el V i ≠ 0%F). {
  specialize rngl_opt_eq_dec as rngl_eq_dec.
  rewrite Hde in rngl_eq_dec.
  apply (not_forall_in_interv_imp_exist (a:=0) (b:=n-1));
    cycle 1. {
    flia.
  } {
    intros Hnv.
    apply Hn.
    intros i Hi.
    specialize (Hnv i).
    assert (H : 0 ≤ i ≤ n - 1) by flia Hi.
    specialize (Hnv H).
    now destruct (rngl_eq_dec (vect_el V i) 0%F).
  }
  intros k.
  unfold Decidable.decidable.
  specialize (rngl_eq_dec (vect_el V k) 0%F) as [Hvnz| Hvnz]. {
    now right.
  } {
    now left.
  }
}
move Hiv at bottom.
destruct H as (i, Hi).
specialize (Hiv i).
now apply rngl_mul_reg_r in Hiv.
Qed.

Theorem mat_mul_mul_scal_l :
  rngl_is_comm = true →
  ∀ {m n p} a (MA : matrix m n T) (MB : matrix n p T),
  (MA * (a × MB) = a × (MA * MB))%M.
Proof.
intros Hic *.
specialize rngl_opt_mul_comm as rngl_mul_comm.
rewrite Hic in rngl_mul_comm.
apply matrix_eq.
intros * Hi Hj.
cbn - [ iter_seq ].
rewrite rngl_mul_summation_distr_l.
apply rngl_summation_eq_compat.
intros k Hk.
rewrite rngl_mul_comm.
rewrite <- rngl_mul_assoc.
f_equal.
apply rngl_mul_comm.
Qed.

Theorem mat_mul_scal_add_distr_l : ∀ {m n} a (MA MB : matrix m n T),
  (a × (MA + MB) = (a × MA + a × MB))%M.
Proof.
intros.
apply matrix_eq.
intros * Hi Hj.
apply rngl_mul_add_distr_l.
Qed.

(* associativity with multiplication with vector *)

Theorem mat_vect_mul_assoc_as_sums :
  ∀ {m n p} (A : matrix m n T) (B : matrix n p T) (V : vector p T) i,
  i < m
  → (Σ (j = 0, n - 1),
       mat_el A i j *
       (Σ (k = 0, p - 1), mat_el B j k * vect_el V k))%F =
    (Σ (j = 0, p - 1),
       (Σ (k = 0, n - 1), mat_el A i k * mat_el B k j) *
       vect_el V j)%F.
Proof.
intros * Hi.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  now rewrite rngl_mul_summation_distr_l.
}
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  now rewrite rngl_mul_summation_distr_r.
}
symmetry.
cbn - [ iter_seq ].
rewrite rngl_summation_summation_exch'; [ | easy ].
apply rngl_summation_eq_compat.
intros j Hj.
apply rngl_summation_eq_compat.
intros k Hk.
apply rngl_mul_assoc.
Qed.

Theorem mat_vect_mul_assoc {m n p} :
  ∀ (A : matrix m n T) (B : matrix n p T) (V : vector p T),
  (A • (B • V) = (A * B) • V)%V.
Proof.
intros.
apply vector_eq.
intros i Hi.
cbn in Hi.
unfold mat_mul_vect_r.
unfold mat_mul.
cbn - [ iter_seq ].
now apply mat_vect_mul_assoc_as_sums.
Qed.

Theorem mat_mul_scal_vect_assoc {m n} :
  ∀ a (MA : matrix m n T) (V : vector n T), (a × (MA • V) = (a × MA) • V)%V.
Proof.
intros.
apply vector_eq.
intros i Hi.
cbn in Hi.
cbn - [ iter_seq ].
rewrite rngl_mul_summation_distr_l.
apply rngl_summation_eq_compat.
intros j Hj.
apply rngl_mul_assoc.
Qed.

Theorem mat_mul_scal_vect_comm :
  rngl_is_comm = true →
  ∀ {m n} a (MA : matrix m n T) V, (a × (MA • V) = MA • (a × V))%V.
Proof.
intros Hic *.
apply vector_eq.
intros i Hi.
cbn in Hi.
cbn - [ iter_seq ].
rewrite rngl_mul_summation_distr_l.
apply rngl_summation_eq_compat.
intros j Hj.
do 2 rewrite rngl_mul_assoc.
f_equal.
specialize rngl_opt_mul_comm as rngl_mul_comm.
rewrite Hic in rngl_mul_comm.
apply rngl_mul_comm.
Qed.

Theorem vect_dot_mul_scal_mul_comm :
  rngl_is_comm = true →
  ∀ {n} (a : T) (U V : vector n T),
  (U · (a × V) = (a * (U · V))%F)%V.
Proof.
intros Hic *.
unfold vect_dot_product.
rewrite rngl_mul_summation_distr_l.
apply rngl_summation_eq_compat.
intros j Hj; cbn.
do 2 rewrite rngl_mul_assoc.
f_equal.
specialize rngl_opt_mul_comm as rngl_mul_comm.
rewrite Hic in rngl_mul_comm.
apply rngl_mul_comm.
Qed.

Theorem vect_scal_mul_dot_mul_comm : ∀ {n} (a : T) (U V : vector n T),
  ((a × U) · V = (a * (U · V))%F)%V.
Proof.
intros.
unfold vect_dot_product.
rewrite rngl_mul_summation_distr_l.
apply rngl_summation_eq_compat.
intros j Hj; cbn.
symmetry; apply rngl_mul_assoc.
Qed.

(* comatrix *)

Definition comatrix {n} (M : matrix n n T) : matrix n n T :=
  {| mat_el i j := (minus_one_pow (i + j) * determinant (subm M i j))%F |}.

(* matrix transpose *)

Definition mat_transp {m n} (M : matrix m n T) : matrix n m T :=
  {| mat_el i j := mat_el M j i |}.

(* combinations of submatrix and other *)

Theorem submatrix_sub {m n} : ∀ (MA MB : matrix m n T) i j,
  subm (MA - MB)%M i j = (subm MA i j - subm MB i j)%M.
Proof.
intros.
apply matrix_eq.
intros k l Hk Hl; cbn.
now destruct (lt_dec k i), (lt_dec l j).
Qed.

Theorem submatrix_mul_scal_l {m n} : ∀ (μ : T) (M : matrix m n T) i j,
  subm (μ × M)%M i j = (μ × subm M i j)%M.
Proof.
intros.
apply matrix_eq.
intros k l Hk Hl; cbn.
now destruct (lt_dec k i), (lt_dec l j).
Qed.

Theorem submatrix_mI : ∀ i r, subm (mI r) i i = mI (r - 1).
Proof.
intros.
apply matrix_eq.
intros k l Hk Hl; cbn.
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

Theorem mat_mul_scal_1_l {m n} : ∀ (M : matrix m n T), (1 × M = M)%M.
Proof.
intros.
apply matrix_eq; cbn.
intros * Hi Hj.
apply rngl_mul_1_l.
Qed.

(* square matrices should not be required now

Definition is_square_mat_bool (M : matrix T) :=
  Nat.eqb (mat_nrows M) (mat_ncols M).

Definition compatible_square_matrices_bool (ML : list (matrix T)) :=
  (forallb is_square_mat_bool ML &&
   forallb
     (λ M,
        let sz1 := mat_nrows M in
        let sz2 := mat_nrows (hd M ML) in
        Nat.eqb sz1 sz2)
     ML)%bool.

Definition square_matrix n :=
  {M : matrix T | Nat.eqb (mat_nrows M) n && Nat.eqb (mat_ncols M) n = true}.

Definition mat_of_squ_mat n (M : square_matrix n) : matrix T := proj1_sig M.
Definition squ_mat_el n (M : square_matrix n) := mat_el (mat_of_squ_mat M).

Theorem square_matrix_eq : ∀ n (MA MB : square_matrix n),
  mat_of_squ_mat MA = mat_of_squ_mat MB
  → MA = MB.
Proof.
intros  * Hab.
destruct MA as (A, ma).
destruct MB as (B, mb).
cbn in Hab.
apply eq_exist_uncurried.
exists Hab.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Theorem square_matrix_neq : ∀ n (MA MB : square_matrix n),
  mat_of_squ_mat MA ≠ mat_of_squ_mat MB
  → MA ≠ MB.
Proof.
intros * Hab H.
apply Hab.
now destruct H.
Qed.

Theorem mZ_prop n : (mat_nrows (mZ n) =? n) && (mat_ncols (mZ n) =? n) = true.
Proof.
apply andb_true_intro.
now split; apply Nat.eqb_eq.
Qed.

Theorem mI_prop n : (mat_nrows (mI n) =? n) && (mat_ncols (mI n) =? n) = true.
Proof.
apply andb_true_intro.
now split; apply Nat.eqb_eq.
Qed.

Definition squ_mat_zero n : square_matrix n := exist _ (mZ n) (mZ_prop n).
Definition squ_mat_one n : square_matrix n := exist _ (mI n) (mI_prop n).

Theorem squ_mat_add_prop : ∀ n (MA MB : square_matrix n),
  (mat_nrows (mat_of_squ_mat MA + mat_of_squ_mat MB) =? n) &&
  (mat_ncols (mat_of_squ_mat MA + mat_of_squ_mat MB) =? n) = true.
Proof.
intros.
destruct MA as (A, Hap).
destruct MB as (B, Hbp); cbn.
apply andb_true_intro.
apply andb_true_iff in Hap.
apply andb_true_iff in Hbp.
easy.
Qed.

Definition squ_mat_add n (MA MB : square_matrix n) : square_matrix n :=
  exist _ (mat_of_squ_mat MA + mat_of_squ_mat MB)%M (squ_mat_add_prop MA MB).

Definition squ_mat_mul_vect_r n (M : square_matrix n) V :=
  (mat_of_squ_mat M • V)%V.

Theorem squ_mat_mul_prop : ∀ n (MA MB : square_matrix n),
  (mat_nrows (mat_of_squ_mat MA * mat_of_squ_mat MB) =? n) &&
  (mat_ncols (mat_of_squ_mat MA * mat_of_squ_mat MB) =? n) = true.
Proof.
intros.
destruct MA as (A, Hap).
destruct MB as (B, Hbp); cbn.
apply andb_true_intro.
apply andb_true_iff in Hap.
apply andb_true_iff in Hbp.
easy.
Qed.

Definition squ_mat_mul n (MA MB : square_matrix n) : square_matrix n :=
  exist _ (mat_of_squ_mat MA * mat_of_squ_mat MB)%M (squ_mat_mul_prop MA MB).

Theorem squ_mat_opp_prop : ∀ n (M : square_matrix n),
  (mat_nrows (- mat_of_squ_mat M)%M =? n) &&
  (mat_ncols (- mat_of_squ_mat M)%M =? n) = true.
Proof.
intros.
now destruct M as (A, Hap).
Qed.

Definition squ_mat_opp n (M : square_matrix n) : square_matrix n :=
  exist _ (- mat_of_squ_mat M)%M (squ_mat_opp_prop M).

Definition phony_squ_mat_le n (MA MB : square_matrix n) := True.
Definition phony_squ_mat_sub n (MA MB : square_matrix n) := MA.
Definition phony_squ_mat_div n (MA MB : square_matrix n) := MA.
Definition phony_squ_mat_inv n (M : square_matrix n) := M.

Canonical Structure squ_mat_ring_like_op n : ring_like_op (square_matrix n) :=
  {| rngl_has_opp := true;
     rngl_has_inv := false;
     rngl_has_no_inv_but_div := false;
     rngl_is_ordered := false;
     rngl_zero := squ_mat_zero n;
     rngl_one := squ_mat_one n;
     rngl_add := @squ_mat_add n;
     rngl_mul := @squ_mat_mul n;
     rngl_opp := @squ_mat_opp n;
     rngl_inv := @phony_squ_mat_inv n;
     rngl_le := @phony_squ_mat_le n;
     rngl_opt_sub := @phony_squ_mat_sub n;
     rngl_opt_div := @phony_squ_mat_div n |}.

Existing Instance squ_mat_ring_like_op.
*)

Definition phony_squ_mat_le n (MA MB : matrix n n T) := True.
Definition phony_squ_mat_sub n (MA MB : matrix n n T) := MA.
Definition phony_squ_mat_div n (MA MB : matrix n n T) := MA.
Definition phony_squ_mat_inv n (M : matrix n n T) := M.

Definition at_least_1 n := S (n - 1).

Canonical Structure mat_ring_like_op n :
  ring_like_op (matrix n n T) :=
  {| rngl_has_opp := rngl_has_opp;
     rngl_has_inv := false;
     rngl_has_no_inv_but_div := false;
     rngl_is_ordered := false;
     rngl_zero := mZ n n;
     rngl_one := mI n;
     rngl_add := @mat_add T _ n n;
     rngl_mul := @mat_mul T _ n n n;
     rngl_opp := @mat_opp T _ n n;
     rngl_inv := @phony_squ_mat_inv n;
     rngl_le := @phony_squ_mat_le n;
     rngl_opt_sub := @phony_squ_mat_sub n;
     rngl_opt_div := @phony_squ_mat_div n |}.

(*
Existing Instance mat_ring_like_op.
*)

(*
Declare Scope SM_scope.
Delimit Scope SM_scope with SM.

Arguments squ_mat_mul_vect_r {n}%nat M%SM V%V.

Notation "A * B" := (squ_mat_mul A B) : SM_scope.
Notation "A + B" := (squ_mat_add A B) : SM_scope.
Notation "A • V" := (squ_mat_mul_vect_r A V) (at level 40) : SM_scope.
Notation "- A" := (squ_mat_opp A) : SM_scope.

Theorem squ_mat_add_comm : ∀ n (MA MB : square_matrix n),
  (MA + MB = MB + MA)%SM.
Proof.
intros.
apply square_matrix_eq; cbn.
destruct MA as (A, Ha).
destruct MB as (B, Hb); cbn.
apply Bool.andb_true_iff in Ha.
apply Bool.andb_true_iff in Hb.
destruct Ha as (Hra, Hca).
destruct Hb as (Hrb, Hcb).
apply Nat.eqb_eq in Hra.
apply Nat.eqb_eq in Hca.
apply Nat.eqb_eq in Hrb.
apply Nat.eqb_eq in Hcb.
apply mat_add_comm; congruence.
Qed.

Theorem squ_mat_add_assoc : ∀ n (MA MB MC : square_matrix n),
  (MA + (MB + MC) = (MA + MB) + MC)%SM.
Proof.
intros.
apply square_matrix_eq; cbn.
destruct MA as (A, Ha).
destruct MB as (B, Hb).
destruct MC as (C, Hc); cbn.
apply Bool.andb_true_iff in Ha.
apply Bool.andb_true_iff in Hb.
apply Bool.andb_true_iff in Hc.
destruct Ha as (Hra, Hca).
destruct Hb as (Hrb, Hcb).
destruct Hc as (Hrc, Hcc).
apply Nat.eqb_eq in Hra.
apply Nat.eqb_eq in Hca.
apply Nat.eqb_eq in Hrb.
apply Nat.eqb_eq in Hcb.
apply Nat.eqb_eq in Hrc.
apply Nat.eqb_eq in Hcc.
apply mat_add_assoc; congruence.
Qed.

Theorem squ_mat_add_0_l : ∀ n (MA : square_matrix n),
  (squ_mat_zero n + MA)%SM = MA.
Proof.
intros.
destruct MA as (A, Ha).
apply square_matrix_eq; cbn.
apply Bool.andb_true_iff in Ha.
destruct Ha as (Hra, Hca).
apply Nat.eqb_eq in Hra.
apply Nat.eqb_eq in Hca.
apply mat_add_0_l; congruence.
Qed.

Theorem squ_mat_mul_assoc : ∀ n (MA MB MC : square_matrix n),
  (MA * (MB * MC) = (MA * MB) * MC)%SM.
Proof.
intros.
apply square_matrix_eq; cbn.
destruct MA as (A, Ha).
destruct MB as (B, Hb).
destruct MC as (C, Hc); cbn.
apply Bool.andb_true_iff in Ha.
apply Bool.andb_true_iff in Hb.
apply Bool.andb_true_iff in Hc.
destruct Ha as (Hra, Hca).
destruct Hb as (Hrb, Hcb).
destruct Hc as (Hrc, Hcc).
apply Nat.eqb_eq in Hra.
apply Nat.eqb_eq in Hca.
apply Nat.eqb_eq in Hrb.
apply Nat.eqb_eq in Hcb.
apply Nat.eqb_eq in Hrc.
apply Nat.eqb_eq in Hcc.
apply mat_mul_assoc; congruence.
Qed.

Theorem squ_mat_mul_1_l : ∀ n (MA : square_matrix n),
  (squ_mat_one n * MA)%SM = MA.
Proof.
intros.
destruct MA as (A, Ha).
apply square_matrix_eq; cbn.
apply Bool.andb_true_iff in Ha.
destruct Ha as (Hra, Hca).
apply Nat.eqb_eq in Hra.
apply Nat.eqb_eq in Hca.
apply mat_mul_1_l; congruence.
Qed.

Theorem squ_mat_mul_add_distr_l : ∀ n (MA MB MC : square_matrix n),
  (MA * (MB + MC) = MA * MB + MA * MC)%SM.
Proof.
intros.
apply square_matrix_eq.
destruct MA as (A, Ha).
destruct MB as (B, Hb).
destruct MC as (C, Hc); cbn.
apply Bool.andb_true_iff in Ha.
apply Bool.andb_true_iff in Hb.
apply Bool.andb_true_iff in Hc.
destruct Ha as (Hra, Hca).
destruct Hb as (Hrb, Hcb).
destruct Hc as (Hrc, Hcc).
apply Nat.eqb_eq in Hra.
apply Nat.eqb_eq in Hca.
apply Nat.eqb_eq in Hrb.
apply Nat.eqb_eq in Hcb.
apply Nat.eqb_eq in Hrc.
apply Nat.eqb_eq in Hcc.
apply mat_mul_add_distr_l; congruence.
Qed.

Theorem squ_mat_mul_1_r : ∀ n (MA : square_matrix n),
  (MA * squ_mat_one n)%SM = MA.
Proof.
intros.
destruct MA as (A, Ha).
apply square_matrix_eq; cbn.
apply Bool.andb_true_iff in Ha.
destruct Ha as (Hra, Hca).
apply Nat.eqb_eq in Hra.
apply Nat.eqb_eq in Hca.
apply mat_mul_1_r; congruence.
Qed.

Theorem squ_mat_mul_add_distr_r : ∀ n (MA MB MC : square_matrix n),
  ((MA + MB) * MC = MA * MC + MB * MC)%SM.
Proof.
intros.
apply square_matrix_eq.
destruct MA as (A, Ha).
destruct MB as (B, Hb).
destruct MC as (C, Hc); cbn.
apply Bool.andb_true_iff in Ha.
apply Bool.andb_true_iff in Hb.
apply Bool.andb_true_iff in Hc.
destruct Ha as (Hra, Hca).
destruct Hb as (Hrb, Hcb).
destruct Hc as (Hrc, Hcc).
apply Nat.eqb_eq in Hra.
apply Nat.eqb_eq in Hca.
apply Nat.eqb_eq in Hrb.
apply Nat.eqb_eq in Hcb.
apply Nat.eqb_eq in Hrc.
apply Nat.eqb_eq in Hcc.
apply mat_mul_add_distr_r; congruence.
Qed.

Context {Hro : @rngl_has_opp T ro = true}.

Theorem squ_mat_add_opp_l : ∀ n,
  if @rngl_has_opp (square_matrix n) _ then
    ∀ a : square_matrix n, (- a + a)%F = 0%F
  else True.
Proof.
intros.
remember rngl_has_opp as x eqn:Hx in |-*; symmetry in Hx.
destruct x; [ | easy ].
intros MA.
destruct MA as (A, Ha).
apply square_matrix_eq; cbn.
apply Bool.andb_true_iff in Ha.
destruct Ha as (Hra, Hca).
apply Nat.eqb_eq in Hra.
apply Nat.eqb_eq in Hca.
rewrite mat_add_opp_l with (n := n); congruence.
Qed.

Theorem squ_mat_1_neq_0 : ∀ n, squ_mat_one n ≠ squ_mat_zero n.
Proof.
intros.
unfold squ_mat_one, squ_mat_zero.
intros H.
injection H; clear H; intros H.
set (f := λ i j, if Nat.eq_dec i j then 1%F else 0%F) in H.
set (g := λ _ _, 0%F) in H.
assert (H1 : ∀ i j, f i j = g i j) by now rewrite H.
specialize (H1 0 0).
unfold f, g in H1; cbn in H1.
now apply rngl_1_neq_0 in H1.
Qed.

Theorem mat_of_squ_mat_squ_mat_of_nat : ∀ n i,
  mat_of_squ_mat (rngl_of_nat i : square_matrix n) = (rngl_of_nat i × mI n)%M.
Proof.
intros.
induction i. {
  cbn - [ "mod" ].
  apply matrix_eq; [ easy | easy | cbn ].
  intros * Hi Hj; symmetry.
  apply rngl_mul_0_l.
}
cbn - [ "mod" ].
rewrite IHi.
rewrite mat_mul_scal_l_add_distr_r.
f_equal; symmetry.
apply mat_mul_scal_1_l.
Qed.

Theorem squ_mat_characteristic_prop : ∀ n,
  match
    (if Nat.eq_dec n 0 then 1 else rngl_characteristic)
  with
  | 0 => ∀ i : nat, rngl_of_nat (S i) ≠ squ_mat_zero n
  | S _ =>
      rngl_of_nat (if Nat.eq_dec n 0 then 1 else rngl_characteristic) =
      squ_mat_zero n
  end.
Proof.
intros; cbn.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  apply square_matrix_eq; cbn.
  now apply matrix_eq.
}
remember rngl_characteristic as c eqn:Hc.
symmetry in Hc.
specialize (rngl_characteristic_prop) as Hcp.
rewrite Hc in Hcp.
destruct c. {
  intros.
  apply square_matrix_neq; cbn.
  rewrite mat_of_squ_mat_squ_mat_of_nat.
  apply matrix_neq; cbn.
  right; right.
  intros H.
  destruct n; [ easy | ].
  specialize (H 0 0 (Nat.lt_0_succ _) (Nat.lt_0_succ _)).
  cbn in H.
  rewrite rngl_mul_1_r in H.
  now specialize (Hcp i).
}
cbn in Hcp |-*.
apply square_matrix_eq; cbn.
apply matrix_eq; [ easy | easy | cbn ].
intros * Hi Hn.
rewrite mat_of_squ_mat_squ_mat_of_nat; cbn.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  now rewrite rngl_mul_1_r.
}
rewrite rngl_mul_0_r.
apply rngl_add_0_l.
Qed.

Theorem matrix_eq_dec : ∀ n (MA MB : matrix T),
  (∀ a b : T, {a = b} + {a ≠ b})
  → mat_nrows MA = n
  → mat_ncols MA = n
  → mat_nrows MB = n
  → mat_ncols MB = n
  → {MA = MB} + {MA ≠ MB}.
Proof.
intros * Hab Hra Hca Hrb Hcb.
destruct MA as (fa, ra, ca).
destruct MB as (fb, rb, cb).
cbn in Hra, Hca, Hrb, Hcb.
subst ra ca rb cb.
assert (∀ i j, {fa i j = fb i j} + {fa i j ≠ fb i j}). {
  intros.
  apply Hab.
}
induction n; intros; [ now left; apply matrix_eq | ].
destruct IHn as [IHn| IHn]. {
  injection IHn; clear IHn; intros IHn.
  now left; subst fb.
} {
  right.
  intros H1; apply IHn; clear IHn.
  injection H1; clear H1; intros H1.
  now subst fb.
}
Qed.

Theorem squ_mat_opt_eq_dec : ∀ n,
  if rngl_has_dec_eq then ∀ a b : square_matrix n, {a = b} + {a ≠ b}
  else True.
Proof.
intros.
specialize rngl_opt_eq_dec as rngl_eq_dec.
remember rngl_has_dec_eq as x eqn:Hde; symmetry in Hde.
destruct x; [ | easy ].
destruct a as (a, Ha).
destruct b as (b, Hb).
move b before a.
assert (H : {a = b} + {a ≠ b}). {
  apply Bool.andb_true_iff in Ha.
  apply Bool.andb_true_iff in Hb.
  destruct Ha as (Hra, Hca).
  destruct Hb as (Hrb, Hcb).
  apply Nat.eqb_eq in Hra.
  apply Nat.eqb_eq in Hca.
  apply Nat.eqb_eq in Hrb.
  apply Nat.eqb_eq in Hcb.
  now apply (@matrix_eq_dec n).
}
destruct H as [H| H]. {
  now left; apply square_matrix_eq.
} {
  now right; apply square_matrix_neq.
}
Qed.

Definition squ_mat_ring_like_prop (n : nat) :
    ring_like_prop (square_matrix n) :=
  {| rngl_is_comm := false;
     rngl_has_dec_eq := @rngl_has_dec_eq T ro rp;
     rngl_has_dec_le := false;
     rngl_is_integral := false;
     rngl_characteristic := if Nat.eq_dec n 0 then 1 else rngl_characteristic;
     rngl_add_comm := @squ_mat_add_comm n;
     rngl_add_assoc := @squ_mat_add_assoc n;
     rngl_add_0_l := @squ_mat_add_0_l n;
     rngl_mul_assoc := @squ_mat_mul_assoc n;
     rngl_mul_1_l := @squ_mat_mul_1_l n;
     rngl_mul_add_distr_l := @squ_mat_mul_add_distr_l n;
     rngl_1_neq_0 := @squ_mat_1_neq_0 n;
     rngl_opt_mul_comm := I;
     rngl_opt_mul_1_r := @squ_mat_mul_1_r n;
     rngl_opt_mul_add_distr_r := @squ_mat_mul_add_distr_r n;
     rngl_opt_add_opp_l := @squ_mat_add_opp_l n;
     rngl_opt_add_sub := I;
     rngl_opt_mul_0_l := I;
     rngl_opt_mul_0_r := I;
     rngl_opt_mul_inv_l := I;
     rngl_opt_mul_inv_r := I;
     rngl_opt_mul_div_l := I;
     rngl_opt_mul_div_r := I;
     rngl_opt_eq_dec := @squ_mat_opt_eq_dec n;
     rngl_opt_le_dec := I;
     rngl_opt_integral := I;
     rngl_characteristic_prop := @squ_mat_characteristic_prop n;
     rngl_opt_le_refl := I;
     rngl_opt_le_antisymm := I;
     rngl_opt_le_trans := I;
     rngl_opt_add_le_compat := I;
     rngl_opt_mul_le_compat_nonneg := I;
     rngl_opt_mul_le_compat_nonpos := I;
     rngl_opt_mul_le_compat := I;
     rngl_opt_not_le := I |}.
*)

(*
Theorem mat_1_neq_0 :
  ∀ n, mI (at_least_1 n) ≠ mZ (at_least_1 n) (at_least_1 n).
Proof.
intros.
unfold mI, mZ.
(**)
apply matrix_neq.
unfold at_least_1.
cbn; intros H.
specialize (H 0 0 (Nat.lt_0_succ _) (Nat.lt_0_succ _)).
destruct (Nat.eq_dec 0 0); [ | easy ].
now apply rngl_1_neq_0 in H.
Qed.
*)

(*
Theorem mat_add_opp_l' : ∀ n,
  if
    @rngl_has_opp
      (matrix (at_least_1 (at_least_1 n)) (at_least_1 (at_least_1 n)) T)
      (mat_ring_like_op (at_least_1 n))
  then
    ∀ a : matrix (at_least_1 (at_least_1 n)) (at_least_1 (at_least_1 n)) T,
    @eq (matrix (at_least_1 (at_least_1 n)) (at_least_1 (at_least_1 n)) T)
      (@rngl_add
         (matrix (at_least_1 (at_least_1 n)) (at_least_1 (at_least_1 n)) T)
         (mat_ring_like_op (at_least_1 n))
         (@rngl_opp
            (matrix (at_least_1 (at_least_1 n)) (at_least_1 (at_least_1 n)) T)
            (mat_ring_like_op (at_least_1 n)) a) a)
      (@rngl_zero
         (matrix (at_least_1 (at_least_1 n)) (at_least_1 (at_least_1 n)) T)
         (mat_ring_like_op (at_least_1 n)))
  else True.
Proof.
intros.
remember rngl_has_opp as x eqn:Hx.
destruct x; [ | easy ].
intros MA.
apply matrix_eq; cbn.
intros * Hi Hj.
...
Search (- _ + _)%F.
...
specialize @rngl_opt_add_opp_l as rngl_add_opp_l.
specialize (rngl_add_opp_l _ (mat_ring_like_op n)).
specialize
  (rngl_add_opp_l
     (matrix (at_least_1 (at_least_1 n)) (at_least_1 (at_least_1 n)) T)).
specialize (rngl_add_opp_l (mat_ring_like_op (at_least_1 n))).
rewrite <- Hx in rngl_add_opp_l.
rewrite rngl_add_opp_l.
Set Printing All.
apply rngl_add_opp_l.
...

apply rngl_add_opp_l.


apply Bool.andb_true_iff in Ha.
destruct Ha as (Hra, Hca).
apply Nat.eqb_eq in Hra.
apply Nat.eqb_eq in Hca.
rewrite mat_add_opp_l with (n := n); congruence.
Qed.
*)

Theorem mat_opt_add_opp_l : ∀ n (ro := mat_ring_like_op n),
  if rngl_has_opp then
    ∀ a : matrix n n T, (- a + a)%F = 0%F
  else True.
Proof.
intros.
specialize (@mat_add_opp_l n n) as H.
remember rngl_has_opp as x eqn:Hx; symmetry in Hx.
destruct x; [ | easy ].
now apply H.
Qed.

Theorem mat_opt_add_sub : ∀ n (ro := mat_ring_like_op n),
  if rngl_has_opp then True else ∀ a b : matrix n n T, (a + b - b)%F = a.
Proof.
intros.
remember rngl_has_opp as x eqn:Hx; symmetry in Hx.
destruct x; [ easy | ].
intros MA MB.
apply matrix_eq.
intros * Hi Hj.
cbn.
Search ((_ + _) - _)%M.
...
now apply H.
Qed.
...

Definition squ_mat_ring_like_prop (n : nat) :
  ring_like_prop (matrix n n T) :=
  {| rngl_is_comm := false;
     rngl_has_dec_eq := @rngl_has_dec_eq T ro rp;
     rngl_has_dec_le := false;
     rngl_is_integral := false;
     rngl_characteristic := if Nat.eq_dec n 0 then 1 else rngl_characteristic;
     rngl_add_comm := mat_add_comm;
     rngl_add_assoc := mat_add_assoc;
     rngl_add_0_l := mat_add_0_l;
     rngl_mul_assoc := mat_mul_assoc;
     rngl_mul_1_l := mat_mul_1_l;
     rngl_mul_add_distr_l := mat_mul_add_distr_l;
     rngl_1_neq_0 := rngl_1_neq_0;
     rngl_opt_mul_comm := I;
     rngl_opt_mul_1_r := mat_mul_1_r;
     rngl_opt_mul_add_distr_r := mat_mul_add_distr_r;
     rngl_opt_add_opp_l := mat_opt_add_opp_l n;
     rngl_opt_add_sub := mat_opt_add_sub n;
     rngl_opt_mul_0_l := I;
     rngl_opt_mul_0_r := I;
     rngl_opt_mul_inv_l := I;
     rngl_opt_mul_inv_r := I;
     rngl_opt_mul_div_l := I;
     rngl_opt_mul_div_r := I;
     rngl_opt_eq_dec := 42;
(*
     rngl_opt_eq_dec := @squ_mat_opt_eq_dec n;
*)
     rngl_opt_le_dec := I;
     rngl_opt_integral := I;
     rngl_characteristic_prop := 42;
(*
     rngl_characteristic_prop := @mat_characteristic_prop n;
*)
     rngl_opt_le_refl := I;
     rngl_opt_le_antisymm := I;
     rngl_opt_le_trans := I;
     rngl_opt_add_le_compat := I;
     rngl_opt_mul_le_compat_nonneg := I;
     rngl_opt_mul_le_compat_nonpos := I;
     rngl_opt_mul_le_compat := I;
     rngl_opt_not_le := I |}.

...

Theorem squ_mat_mul_scal_vect_comm :
  rngl_is_comm = true →
  ∀ n (M : square_matrix n) c V,
  (c × (M • V)%SM)%V = (M • (c × V))%SM.
Proof.
intros Hic *.
apply vector_eq; [ easy | ].
intros * Hi.
cbn in Hi.
cbn - [ iter_seq ].
rewrite rngl_mul_summation_distr_l.
apply rngl_summation_eq_compat.
intros j Hj.
do 2 rewrite rngl_mul_assoc.
f_equal.
specialize rngl_opt_mul_comm as rngl_mul_comm.
rewrite Hic in rngl_mul_comm.
apply rngl_mul_comm.
Qed.

Theorem vect_eq_dec :
  rngl_has_dec_eq = true →
  ∀ n (U V : vector T),
  vect_nrows U = n
  → vect_nrows V = n
  → {U = V} + {U ≠ V}.
Proof.
intros Hed * Hru Hrv.
specialize rngl_opt_eq_dec as rngl_eq_dec.
rewrite Hed in rngl_eq_dec.
destruct U as (fu, ru).
destruct V as (fv, rv).
cbn in Hru, Hrv; subst ru rv.
assert (H : ∀ i, {fu i = fv i} + {fu i ≠ fv i}). {
  intros.
  apply rngl_eq_dec.
}
induction n; intros; [ now left; apply vector_eq | ].
destruct IHn as [IHn| IHn]. {
  injection IHn; clear IHn; intros IHn.
  now left; subst fv.
} {
  right.
  intros H1; apply IHn; clear IHn.
  injection H1; clear H1; intros H1.
  now subst fv.
}
Qed.

Theorem squ_mat_subm_prop : ∀ n (A : square_matrix n) i j,
  ((mat_nrows (subm (mat_of_squ_mat A) i j) =? n - 1) &&
   (mat_ncols (subm (mat_of_squ_mat A) i j) =? n - 1))%bool = true.
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
  exist _ (subm (mat_of_squ_mat A) i j) (squ_mat_subm_prop A i j).

Theorem squ_mat_transp_prop : ∀ n (M : square_matrix n),
  ((mat_nrows (mat_transp (mat_of_squ_mat M)) =? n) &&
   (mat_ncols (mat_transp (mat_of_squ_mat M)) =? n))%bool = true.
Proof.
intros.
destruct M as (M, Hm); cbn.
now rewrite Bool.andb_comm.
Qed.

Definition squ_mat_transp n (M : square_matrix n) : square_matrix n :=
  exist _ (mat_transp (mat_of_squ_mat M)) (squ_mat_transp_prop M).

Theorem mat_nrows_of_squ_mat : ∀ n (M : square_matrix n),
  mat_nrows (mat_of_squ_mat M) = n.
Proof.
intros.
destruct M as (M, Hm); cbn.
apply Bool.andb_true_iff in Hm.
destruct Hm as (H1, H2).
now apply Nat.eqb_eq in H1.
Qed.

Theorem mat_ncols_of_squ_mat : ∀ n (M : square_matrix n),
  mat_ncols (mat_of_squ_mat M) = n.
Proof.
intros.
destruct M as (M, Hm); cbn.
apply Bool.andb_true_iff in Hm.
destruct Hm as (H1, H2).
now apply Nat.eqb_eq in H2.
Qed.

(* *)

Theorem fold_determinant :
  ∀ T {ro : ring_like_op T} {so : ring_like_op T} (M : matrix T),
  det_loop M (mat_ncols M) = determinant M.
Proof. easy. Qed.

End a.

Module matrix_Notations.

Declare Scope M_scope.
Declare Scope V_scope.
Declare Scope SM_scope.
Delimit Scope M_scope with M.
Delimit Scope V_scope with V.
Delimit Scope SM_scope with SM.

Arguments det_loop {T ro} M%M n%nat.
Arguments determinant {T ro} M%M.
Arguments is_square_mat {T} M%M.
Arguments mat_add_opp_r {T}%type {ro rp} Hro M%M n%nat.
Arguments mat_mul_mul_scal_l {T}%type {ro rp} Hic a%F MA%M.
Arguments mat_mul_scal_l {T ro} _ M%M.
Arguments mat_mul_vect_r {T ro} M%M V%V.
Arguments mat_mul_scal_vect_comm {T}%type {ro rp} Hic a%F MA%M V%V.
Arguments mat_mul_scal_vect_assoc {T}%type {ro rp} a%F MA%M V%V.
Arguments mat_vect_mul_assoc {T}%type {ro rp} (A B)%M V%V.
Arguments mat_mul_1_l {T}%type {ro rp} M%M n%nat.
Arguments mat_mul_1_r {T}%type {ro rp} M%M n%nat.
Arguments mat_nrows {T} m%M.
Arguments mat_ncols {T} m%M.
Arguments mat_sub {T ro} MA%M MB%M.
Arguments mI {T ro} n%nat.
Arguments mZ {T ro} n%nat.
Arguments minus_one_pow {T ro}.
Arguments squ_mat_zero {T}%type {ro} n%nat.
Arguments squ_mat_one {T}%type {ro} n%nat.
Arguments squ_mat_add {T}%type {ro} {n%nat} MA MB.
Arguments squ_mat_mul {T}%type {ro} {n%nat} MA MB.
Arguments squ_mat_ring_like_op {T ro}.
Arguments squ_mat_mul_vect_r {T}%type {ro} [n]%nat M%SM V%V.
Arguments squ_mat_mul_scal_vect_comm {T}%type {ro rp} Hic n M%M c%F V%V.
Arguments subm {T} M%M i%nat j%nat.
Arguments vect_add {T ro} U%V V%V.
Arguments vect_sub {T ro} U%V V%V.
Arguments vect_opp {T ro} V%V.
Arguments vect_mul_scal_l {T ro} s%F V%V.
Arguments vect_mul_scal_reg_r {T}%type {ro rp} Hde Hii V%V (a b)%F.
Arguments vect_mul_1_l {T}%type {ro rp} V%V n%nat.
Arguments vect_zero {T ro}.
Arguments vect_dot_product {T}%type {ro} (U V)%V.
Arguments vect_dot_mul_scal_mul_comm {T}%type {ro rp} Hic a%F (U V)%V.
Arguments vect_scal_mul_dot_mul_comm {T}%type {ro rp} a%F (U V)%V.
Arguments vect_eq_dec {T}%type {ro rp} _ n%nat U%V V%V.
Arguments vect_el {T}%type v%V c%nat.

Notation "A + B" := (mat_add A B) : M_scope.
Notation "A - B" := (mat_sub A B) : M_scope.
Notation "A * B" := (mat_mul A B) : M_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.
Notation "- A" := (mat_opp A) : M_scope.
Notation "A ⁺" := (mat_transp A) (at level 1, format "A ⁺") : M_scope.

Notation "A * B" := (squ_mat_mul A B) : SM_scope.
Notation "A + B" := (squ_mat_add A B) : SM_scope.
Notation "A • V" := (squ_mat_mul_vect_r A V) (at level 40) : SM_scope.
Notation "- A" := (squ_mat_opp A) : SM_scope.
Notation "A ⁺" := (squ_mat_transp A) (at level 1, format "A ⁺") : SM_scope.

Notation "U + V" := (vect_add U V) : V_scope.
Notation "U - V" := (vect_sub U V) : V_scope.
Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.
Notation "A • V" := (mat_mul_vect_r A V) (at level 40) : V_scope.
Notation "U · V" := (vect_dot_product U V) (at level 40) : V_scope.
Notation "- V" := (vect_opp V) : V_scope.

End matrix_Notations.
