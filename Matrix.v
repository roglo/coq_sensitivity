(* matrices *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Bool.
Import List List.ListNotations.
Require Import Init.Nat.

Require Import Misc.
Require Import RingLike RLsummation RLproduct.
Require Import MyVector.

(* matrices *)

Record matrix (m n : nat) T := mk_mat
  { mat_el : Fin.t m → Fin.t n → T }.

(* function extensionality for matrices *)
Theorem matrix_eq : ∀ m n T (MA MB : matrix m n T),
  (∀ i j, mat_el MA i j = mat_el MB i j)
  → MA = MB.
Proof.
intros * Hab.
destruct MA as (f).
destruct MB as (g).
cbn in Hab; f_equal.
apply fin_fun_ext.
intros i.
now apply fin_fun_ext.
Qed.

Theorem matrix_neq : ∀ m n T (MA MB : matrix m n T),
  ¬ (∀ i j, mat_el MA i j = mat_el MB i j)
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
  map (λ i, map (mat_el M i) (Fin_seq 0 n)) (Fin_seq 0 m).

Definition list_list_el m n T d (ll : list (list T))
    (i : Fin.t m) (j : Fin.t n) : T :=
  nth (proj1_sig (Fin.to_nat j)) (nth (proj1_sig (Fin.to_nat i)) ll []) d.

Definition mat_of_list_list T d (ll : list (list T)) :
  matrix (list_list_nrows ll) (list_list_ncols ll) T :=
  mk_mat (list_list_el d ll).

(*
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
  {| mat_el i k := Σ (j ∈ Fin_seq 0 n), mat_el MA i j * mat_el MB j k |}.

(* opposite *)

Definition mat_opp {m n} (M : matrix m n T) : matrix m n T :=
  {| mat_el i j := (- mat_el M i j)%F |}.

(* subtraction *)

Definition mat_sub {m n} (MA MB : matrix m n T) :=
  mat_add MA (mat_opp MB).

(* vector from a matrix column *)

Definition vect_of_mat_col {m n} (M : matrix m n T) j :=
  mk_vect (λ i, mat_el M i j).

(* concatenation of a matrix and a vector *)

Definition Fin_nat n (i : Fin.t n) : nat := proj1_sig (Fin.to_nat i).

Theorem Fin_ub : ∀ n (i : Fin.t n), proj1_sig (Fin.to_nat i) < n.
Proof.
intros.
destruct n; [ easy | ].
specialize (@Fin_inv n i) as H2.
destruct H2 as [H2| H2]. {
  subst i.
  apply Nat.lt_0_succ.
}
destruct H2 as (j, Hj).
subst i; cbn.
destruct (Fin.to_nat j) as (k, Hk); cbn.
now apply Nat.succ_lt_mono in Hk.
Qed.

(*
Definition Fin_fun_app A n : (Fin.t n → A) → A → (Fin.t (S n) → A).
Proof.
intros f a i.
destruct (Nat.eq_dec (Fin_nat i) n) as [H1| H1]; [ apply a | ].
apply f.
assert (H2 : Fin_nat i < n). {
  unfold Fin_nat in H1 |-*.
  specialize (Fin_ub i) as H2.
  apply Nat.succ_le_mono in H2.
  now apply Nat_le_neq_lt.
}
apply (Fin.of_nat_lt H2).
Defined.
*)

Definition Fin_fun_app A n : (Fin.t n → A) → A → (Fin.t (S n) → A) :=
  λ f a i,
  match Nat.eq_dec (Fin_nat i) n with
  | left _ => a
  | right Hne =>
      f (let Hin :=
           match Nat.succ_le_mono (proj1_sig (Fin.to_nat i)) n with
           | conj _ H => H (Fin_ub i)
           end
         in
         Fin.of_nat_lt (Nat_le_neq_lt Hin Hne))
  end.

(*
Check (@Fin_nat 12).
Check (Fin_fun_app (@Fin_nat 12)) 17.
Compute map ((Fin_fun_app (@Fin_nat 12)) 17) (Fin_seq 0 13).
*)

Definition lfln a l : list (Fin.t (fold_left (λ c i : nat, max c i) l a + 1)).
Proof.
revert a.
induction l as [| b]; intros; [ apply [] | ].
apply cons. {
  cbn.
  apply (@Fin.of_nat_lt b).
  clear.
  revert a.
  induction l as [| c]; intros; cbn. {
    rewrite Nat.add_1_r.
    apply -> Nat.succ_le_mono.
    apply Nat.le_max_r.
  }
  rewrite <- Nat.max_assoc.
  rewrite (Nat.max_comm b).
  rewrite Nat.max_assoc.
  apply IHl.
}
cbn.
apply IHl.
Defined.

Definition list_Fin_of_list_nat l : list (Fin.t (Max (i ∈ l), i + 1)) :=
  lfln 0 l.

(*
Compute (list_Fin_of_list_nat [3;7;1;8;0;9] : list (Fin.t 10)).
Compute map (@Fin_nat 10) (list_Fin_of_list_nat [3;7;1;8;0;9]).
*)

Definition mat_vect_concat {A m n} d (M : matrix m n A) V :=
  mk_mat
    (λ i j,
     if Nat.eq_dec (proj1_sig (Fin.to_nat j)) n then vect_el V i
     else Fin_fun_app (mat_el M i) d j).

Compute (list_list_of_mat (mat_vect_concat 37 (mat_of_list_list 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (vect_of_list 0 [43; 12; 29]))).

(* multiplication of a matrix by a vector *)

Definition mat_mul_vect_r {m n} (M : matrix m n T) (V : vector n T) :=
  mk_vect (λ i, Σ (j ∈ Fin_seq 0 n), mat_el M i j * vect_el V j).

(* multiplication of a matrix by a scalar *)

Definition mat_mul_scal_l {m n} s (M : matrix m n T) :=
  mk_mat (λ i j, s * mat_el M i j)%F.

(* matrix whose k-th column is replaced by a vector *)

Definition mat_repl_vect {m n} k (M : matrix m n T) (V : vector m T) :=
  mk_mat (λ i j, if Fin.eq_dec j k then vect_el V i else mat_el M i j).

(* null matrix of dimension m × n *)

Definition mZ m n : matrix m n T :=
  mk_mat (λ i j, 0%F).

(* identity square matrix of dimension n *)

Definition mI n : matrix n n T :=
  mk_mat (λ i j, if Fin.eq_dec i j then 1%F else 0%F).

End a.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.
Context {Hro : @rngl_has_opp T ro = true}.

Declare Scope M_scope.
Delimit Scope M_scope with M.

Arguments mat_mul_scal_l {T ro m n} s%F M%M.
Arguments mat_opp {T}%type {ro} {m n}%nat.
Arguments mat_sub {T ro m n} MA%M MB%M.
Arguments mI {T ro} n%nat.
Arguments mZ {T ro} (m n)%nat.
Arguments minus_one_pow {T ro}.
Arguments vect_zero {T ro} n%nat.

Notation "A + B" := (mat_add A B) : M_scope.
Notation "A - B" := (mat_sub A B) : M_scope.
Notation "A * B" := (mat_mul A B) : M_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.
Notation "- A" := (mat_opp A) : M_scope.

Arguments mat_mul_vect_r {T ro m n} M%M V%V.

Notation "A • V" := (mat_mul_vect_r A V) (at level 40) : M_scope.
Notation "A • V" := (mat_mul_vect_r A V) (at level 40) : V_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.

Theorem fold_mat_sub : ∀ m n (MA MB : matrix m n T), (MA + - MB = MA - MB)%M.
Proof. easy. Qed.

(* commutativity of addition *)

Theorem mat_add_comm : ∀ {m n} (MA MB : matrix m n T), (MA + MB = MB + MA)%M.
Proof.
intros.
apply matrix_eq.
intros.
apply rngl_add_comm.
Qed.

(* associativity of addition *)

Theorem mat_add_add_swap : ∀ {m n} (MA MB MC : matrix m n T),
  (MA + MB + MC = MA + MC + MB)%M.
Proof.
intros.
apply matrix_eq.
intros.
apply rngl_add_add_swap.
Qed.

Theorem mat_add_assoc : ∀ {m n} (MA MB MC : matrix m n T),
  (MA + (MB + MC) = (MA + MB) + MC)%M.
Proof.
intros.
apply matrix_eq.
intros.
apply rngl_add_assoc.
Qed.

(* addition to zero *)

Theorem mat_add_0_l : ∀ {m n} (M : matrix m n T), (mZ m n + M)%M = M.
Proof.
intros.
apply matrix_eq.
intros.
apply rngl_add_0_l.
Qed.

(* addition left and right with opposite *)

Theorem mat_add_opp_l {m n} :
  ∀ (M : matrix m n T), (- M + M = mZ m n)%M.
Proof.
intros.
apply matrix_eq; cbn.
intros.
now apply rngl_add_opp_l.
Qed.

Theorem mat_add_opp_r {m n} :
  ∀ (M : matrix m n T), (M - M = mZ m n)%M.
Proof.
intros.
apply matrix_eq; cbn.
intros.
rewrite fold_rngl_sub; [ | easy ].
now apply rngl_sub_diag; left.
Qed.

(* multiplication left and right with identity *)

Theorem mat_mul_1_l : ∀ {n} (M : matrix n n T), (mI n * M)%M = M.
Proof.
intros.
apply matrix_eq.
cbn.
intros.
rewrite rngl_summation_list_split with (n0 := Fin_nat i).
destruct n; [ easy | ].
destruct (Nat.eq_dec (Fin_nat i) 0) as [Hiz| Hiz]. {
  rewrite Hiz; cbn.
  unfold iter_list at 1; cbn.
  rewrite rngl_add_0_l.
  rewrite rngl_summation_list_cons.
  destruct (Fin.eq_dec i Fin.F1) as [H1| H1]. {
    rewrite rngl_mul_1_l.
    rewrite all_0_rngl_summation_list_0. 2: {
      intros k Hk.
      destruct (Fin.eq_dec i k) as [Hik| Hik]. {
        subst i k; exfalso.
        clear - Hk.
...
        destruct n; [ easy | ].
        cbn in Hk.
        destruct Hk as [| Hk]; [ easy | ].
...
        remember (Fin_seq 1 n) as l eqn:Hl; clear Hl.
        induction n. {
          cbn in l, Hk.
        induction n; [ easy | ].
        cbn in Hk.
        destruct Hk as [| Hk]; [ easy | ].

        destruct n; [ easy | ].
        destruct n; [ now destruct Hk | ].
        destruct n. {
          cbn in Hk.
          destruct Hk as [| Hk]; [ easy | now destruct Hk ].
        }
        destruct n. {
          cbn in Hk.
          destruct Hk as [| Hk]; [ easy | ].
          destruct Hk as [| Hk]; [ easy | ].
          destruct Hk as [| Hk]; [ easy | ].
          easy.
        }
...

rewrite rngl_summation_list_split_last with (d := i). 2: {


...
destruct (Nat.eq_dec (Fin_nat i) 0) as [Hiz| Hiz]. {
  rewrite Hiz; cbn.
  unfold iter_list at 1; cbn.
  rewrite rngl_add_0_l.
...
  rewrite all_0_rngl_summation_list_0.
...
...
rewrite rngl_summation_list_split_last with (d := i). 2: {
  destruct n; [ easy | ].
...
}
...
specialize @rngl_summation_list_split_last as H1.


Check @rngl_summation_list_split_last.
...
rewrite rngl_summation_list_split_last with (d := Fin.F1).
...
destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
rewrite rngl_mul_1_l.
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec i (k - 1)) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_l; left.
}
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec i k) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_l; left.
}
now rewrite rngl_add_0_l, rngl_add_0_r.
...
intros.
apply matrix_eq.
cbn.
intros * Hi Hj.
rewrite (rngl_summation_split _ i); [ | flia Hi ].
rewrite rngl_summation_split_last; [ | flia ].
destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
rewrite rngl_mul_1_l.
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec i (k - 1)) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_l; left.
}
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec i k) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_l; left.
}
now rewrite rngl_add_0_l, rngl_add_0_r.
Qed.

Theorem mat_mul_1_r : ∀ {n} (M : matrix n n T), (M * mI n)%M = M.
Proof.
intros.
apply matrix_eq.
cbn.
intros * Hi Hj.
rewrite (rngl_summation_split _ j); [ | flia Hj ].
rewrite rngl_summation_split_last; [ | flia ].
destruct (Nat.eq_dec j j) as [H| H]; [ clear H | easy ].
rewrite rngl_mul_1_r.
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec (k - 1) j) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_r; left.
}
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec k j) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_r; left.
}
now rewrite rngl_add_0_l, rngl_add_0_r.
Qed.

Theorem vect_mul_1_l : ∀ {n} (V : vector n T), (mI n • V)%M = V.
Proof.
intros.
apply vector_eq; cbn.
intros * Hi.
rewrite (rngl_summation_split _ i); [ | flia Hi ].
rewrite rngl_summation_split_last; [ | flia ].
destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
rewrite rngl_mul_1_l.
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec i (k - 1)) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_l; left.
}
rewrite all_0_rngl_summation_0; [ | easy | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec i k) as [H| H]; [ flia H Hk | ].
  now apply rngl_mul_0_l; left.
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
cbn.
cbn in Hi, Hj.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  now apply rngl_mul_summation_distr_l; left.
}
cbn.
rewrite rngl_summation_summation_exch'; [ | easy ].
apply rngl_summation_eq_compat.
intros k Hk.
erewrite rngl_summation_eq_compat. 2: {
  intros l Hl.
  now rewrite rngl_mul_assoc.
}
cbn.
symmetry.
now apply rngl_mul_summation_distr_r; left.
Qed.

(* left distributivity of multiplication over addition *)

Theorem mat_mul_add_distr_l {m n p} :
  ∀ (MA : matrix m n T) (MB : matrix n p T) (MC : matrix n p T),
  (MA * (MB + MC) = MA * MB + MA * MC)%M.
Proof.
intros.
apply matrix_eq.
intros i j Hi Hj.
cbn.
cbn in Hi, Hj.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  apply rngl_mul_add_distr_l.
}
cbn.
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
cbn.
cbn in Hi, Hj.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  apply rngl_mul_add_distr_r.
}
cbn.
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

Theorem mat_mul_scal_l_mul :
  ∀ {m n p} a (MA : matrix m n T) (MB : matrix n p T),
  (a × MA * MB = a × (MA * MB))%M.
Proof.
intros *.
apply matrix_eq.
intros * Hi Hj.
cbn.
rewrite rngl_mul_summation_distr_l; [ | now left ].
apply rngl_summation_eq_compat.
intros k Hk.
now rewrite <- rngl_mul_assoc.
Qed.

Theorem mat_mul_mul_scal_l :
  rngl_is_comm = true →
  ∀ {m n p} a (MA : matrix m n T) (MB : matrix n p T),
  (MA * (a × MB) = a × (MA * MB))%M.
Proof.
intros Hic *.
apply matrix_eq.
intros * Hi Hj.
cbn.
rewrite rngl_mul_summation_distr_l; [ | now left ].
apply rngl_summation_eq_compat.
intros k Hk.
rewrite rngl_mul_comm; [ | easy ].
rewrite <- rngl_mul_assoc.
f_equal.
now apply rngl_mul_comm.
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
  → Σ (j = 0, n - 1),
       mat_el A i j *
       (Σ (k = 0, p - 1), mat_el B j k * vect_el V k) =
     Σ (j = 0, p - 1),
       (Σ (k = 0, n - 1), mat_el A i k * mat_el B k j) *
        vect_el V j.
Proof.
intros * Hi.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite rngl_mul_summation_distr_l; [ easy | now left ].
}
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite rngl_mul_summation_distr_r; [ easy | now left ].
}
symmetry.
cbn.
rewrite rngl_summation_summation_exch'; [ | easy ].
apply rngl_summation_eq_compat.
intros j Hj.
apply rngl_summation_eq_compat.
intros k Hk.
apply rngl_mul_assoc.
Qed.

Theorem mat_vect_mul_assoc {m n p} :
  ∀ (A : matrix m n T) (B : matrix n p T) (V : vector p T),
  (A • (B • V) = (A * B) • V)%M.
Proof.
intros.
apply vector_eq.
intros i Hi.
cbn in Hi.
unfold mat_mul_vect_r.
unfold mat_mul.
cbn.
now apply mat_vect_mul_assoc_as_sums.
Qed.

Theorem mat_mul_scal_vect_assoc {m n} :
  ∀ a (MA : matrix m n T) (V : vector n T),
  (a × (MA • V))%V = ((a × MA) • V)%M.
Proof.
intros.
apply vector_eq.
intros i Hi.
cbn in Hi.
cbn.
rewrite rngl_mul_summation_distr_l; [ | now left ].
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
cbn.
rewrite rngl_mul_summation_distr_l; [ | now left ].
apply rngl_summation_eq_compat.
intros j Hj.
do 2 rewrite rngl_mul_assoc.
f_equal.
now apply rngl_mul_comm.
Qed.

(* matrix transpose *)

Definition mat_transp {m n} (M : matrix m n T) : matrix n m T :=
  {| mat_el i j := mat_el M j i |}.

(* matrix without row i and column j *)

Definition subm {m n} (M : matrix m n T) i j :=
  mk_mat (m - 1) (n - 1)
    (λ k l, mat_el M (k + Nat.b2n (i <=? k)) (l + Nat.b2n (j <=? l))).

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
remember (i <=? k) as ki eqn:Hki; symmetry in Hki.
remember (i <=? l) as li eqn:Hli; symmetry in Hli.
destruct ki; cbn. {
  destruct li; cbn. {
    destruct (Nat.eq_dec (k + 1) (l + 1)) as [Hkl1| Hkl1]. {
      destruct (Nat.eq_dec k l) as [Hkl| Hkl]; [ easy | flia Hkl1 Hkl ].
    } {
      destruct (Nat.eq_dec k l) as [Hkl| Hkl]; [ flia Hkl1 Hkl | easy ].
    }
  } {
    rewrite Nat.add_0_r.
    apply Nat.leb_le in Hki; apply Nat.leb_nle in Hli.
    destruct (Nat.eq_dec (k + 1) l) as [Hkl1| Hkl1]; [ flia Hki Hli Hkl1 | ].
    destruct (Nat.eq_dec k l) as [Hkl| Hkl]; [ flia Hki Hli Hkl | easy ].
  }
} {
  rewrite Nat.add_0_r.
  destruct li; cbn. {
    apply Nat.leb_nle in Hki; apply Nat.leb_le in Hli.
    destruct (Nat.eq_dec k (l + 1)) as [Hkl1| Hkl1]; [ flia Hki Hli Hkl1 | ].
    destruct (Nat.eq_dec k l) as [Hkl| Hkl]; [ flia Hki Hli Hkl | easy ].
  } {
    now rewrite Nat.add_0_r.
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

Definition phony_mat_le n (MA MB : matrix n n T) := True.

Definition at_least_1 n := S (n - 1).

Canonical Structure mat_ring_like_op n :
  ring_like_op (matrix n n T) :=
  {| rngl_zero := mZ n n;
     rngl_one := mI n;
     rngl_add := @mat_add T _ n n;
     rngl_mul := @mat_mul T _ n n n;
     rngl_opt_opp := Some (@mat_opp T _ n n);
     rngl_opt_inv := None;
     rngl_opt_sous := None;
     rngl_opt_quot := None;
     rngl_le := @phony_mat_le n |}.

(**)
Existing Instance mat_ring_like_op.
(**)

Theorem mat_opt_add_opp_l : ∀ n,
  if @rngl_has_opp (matrix n n T) _ then
    ∀ a : matrix n n T, (- a + a)%F = 0%F
  else True.
Proof.
intros.
remember rngl_has_opp as x eqn:Hx in |-*; symmetry in Hx.
destruct x; [ | easy ].
intros MA.
now apply mat_add_opp_l.
Qed.

Theorem mat_characteristic_prop : ∀ n,
  match
    match Nat.eq_dec n O return nat with
    | left _ => S O
    | right x => rngl_characteristic
    end return Prop
  with
  | O =>
      forall i : nat,
      not
        (@eq (matrix n n T) (@rngl_of_nat (matrix n n T) (mat_ring_like_op n) (S i))
           (@rngl_zero (matrix n n T) (mat_ring_like_op n)))
  | S _ =>
      @eq (matrix n n T)
        (@rngl_of_nat (matrix n n T) (mat_ring_like_op n)
           match Nat.eq_dec n O return nat with
           | left _ => S O
           | right x => rngl_characteristic
           end) (@rngl_zero (matrix n n T) (mat_ring_like_op n))
  end.
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  now apply matrix_eq.
}
remember rngl_characteristic as c eqn:Hc.
symmetry in Hc.
specialize (rngl_characteristic_prop) as Hcp.
rewrite Hc in Hcp.
destruct c. {
  intros.
  apply matrix_neq; cbn.
  intros H.
  destruct n; [ easy | ].
(*
  specialize (H 0 0 (Nat.lt_0_succ _) (Nat.lt_0_succ _)).
*)
  specialize (H 0 0).
(**)
  cbn in H.
  replace
    (@mat_el (S n) (S n) T
       (@rngl_of_nat (matrix (S n) (S n) T) (mat_ring_like_op (S n)) i)
       0 0)%F
  with (@rngl_of_nat T ro i) in H. 2: {
    clear H.
    induction i; [ easy | cbn ].
    now rewrite <- IHi.
  }
  now specialize (Hcp i).
}
cbn in Hcp |-*.
apply matrix_eq; cbn.
intros * Hi Hn.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  subst j.
  replace
    (@mat_el n n T (@rngl_of_nat (matrix n n T) (mat_ring_like_op n) c) i i)%F
  with (@rngl_of_nat T ro c). 2: {
    clear Hc.
    clear Hcp.
    induction c; [ easy | cbn ].
    destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
    now rewrite <- IHc.
  }
  easy.
}
rewrite rngl_add_0_l.
clear Hc Hcp.
induction c; [ easy | cbn ].
destruct (Nat.eq_dec i j) as [H| H]; [ easy | clear H ].
now rewrite rngl_add_0_l.
Qed.

Theorem mat_opt_eq_dec : ∀ n,
  if rngl_has_dec_eq then ∀ a b : matrix n n T, {a = b} + {a ≠ b}
  else not_applicable.
Proof.
intros.
remember rngl_has_dec_eq as de eqn:Hde; symmetry in Hde.
destruct de; [ | easy ].
intros MA MB.
destruct MA as (fa).
destruct MB as (fb).
assert (∀ i j, {fa i j = fb i j} + {fa i j ≠ fb i j}). {
  intros.
  now apply rngl_eq_dec.
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

Theorem mat_1_neq_0 : ∀ n,
  if rngl_has_1_neq_0 && negb (n =? 0) then @mI T ro n ≠ mZ n n
  else not_applicable.
Proof.
intros.
remember (rngl_has_1_neq_0 && negb (n =? 0)) as b eqn:Hb.
symmetry in Hb.
destruct b; [ | easy ].
apply Bool.andb_true_iff in Hb.
destruct Hb as (H10, Hb).
apply Bool.negb_true_iff in Hb.
apply Nat.eqb_neq in Hb.
apply matrix_neq.
intros H; cbn in H.
destruct n; [ easy | ].
specialize (H 0 0); cbn in H.
now apply rngl_1_neq_0 in H.
Qed.

Theorem mat_consistent : ∀ n,
  let TM := matrix n n T in
  let rom := mat_ring_like_op n in
  (rngl_has_opp = false ∨ rngl_has_sous = false) ∧
  (rngl_has_inv = false ∨ rngl_has_quot = false).
Proof. now intros; split; right. Qed.

Definition mat_ring_like_prop (n : nat) :
  ring_like_prop (matrix n n T) :=
  {| rngl_is_comm := false;
     rngl_has_dec_eq := @rngl_has_dec_eq T ro rp;
     rngl_has_dec_le := false;
     rngl_has_1_neq_0 := (rngl_has_1_neq_0 && negb (Nat.eqb n 0))%bool;
     rngl_is_ordered := false;
     rngl_is_integral := false;
     rngl_characteristic := if Nat.eq_dec n 0 then 1 else rngl_characteristic;
     rngl_add_comm := mat_add_comm;
     rngl_add_assoc := mat_add_assoc;
     rngl_add_0_l := mat_add_0_l;
     rngl_mul_assoc := mat_mul_assoc;
     rngl_mul_1_l := mat_mul_1_l;
     rngl_mul_add_distr_l := mat_mul_add_distr_l;
     rngl_opt_1_neq_0 := @mat_1_neq_0 n;
     rngl_opt_mul_comm := NA;
     rngl_opt_mul_1_r := mat_mul_1_r;
     rngl_opt_mul_add_distr_r := mat_mul_add_distr_r;
     rngl_opt_add_opp_l := @mat_opt_add_opp_l n;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_sub_sub_add := NA;
     rngl_opt_mul_sub_distr_l := NA;
     rngl_opt_mul_sub_distr_r := NA;
     rngl_opt_mul_inv_l := NA;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_mul_quot_l := NA;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_eq_dec := mat_opt_eq_dec n;
     rngl_opt_le_dec := NA;
     rngl_opt_integral := NA;
     rngl_characteristic_prop := @mat_characteristic_prop n;
     rngl_opt_le_refl := NA;
     rngl_opt_le_antisymm := NA;
     rngl_opt_le_trans := NA;
     rngl_opt_add_le_compat := NA;
     rngl_opt_mul_le_compat_nonneg := NA;
     rngl_opt_mul_le_compat_nonpos := NA;
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := NA;
     rngl_consistent := mat_consistent n |}.

Theorem mat_vect_mul_0_r : ∀ m n (M : matrix m n T),
  (M • vect_zero _ = vect_zero _)%V.
Proof.
intros.
apply vector_eq.
intros i Hi.
cbn.
rewrite <- rngl_mul_summation_distr_r; [ | now left ].
now apply rngl_mul_0_r; left.
Qed.

(* *)

End a.

Module matrix_Notations.

Declare Scope M_scope.
Delimit Scope M_scope with M.

Arguments mat_el [m n]%nat [T]%type M%M (i j)%nat : rename.
Arguments mat_add_opp_r {T}%type {ro rp} Hro {m n}%nat M%M.
Arguments mat_mul_scal_l_mul {T}%type {ro rp} Hro {m n p}%nat a%F (MA MB)%M.
Arguments mat_mul_mul_scal_l {T}%type {ro rp} Hro Hic {m n p}%nat a%F (MA MB)%M.
Arguments mat_mul_scal_l {T ro} {m n}%nat s%F M%M.
Arguments mat_mul_vect_r {T ro} {m n}%nat M%M V%V.
Arguments mat_mul_scal_vect_comm {T}%type {ro rp} Hro Hic {m n}%nat a%F MA%M V%V.
Arguments mat_mul_scal_vect_assoc {T}%type {ro rp} Hro {m n}%nat a%F MA%M V%V.
Arguments mat_vect_mul_assoc {T}%type {ro rp} Hro {m n p}%nat (A B)%M V%V.
Arguments mat_mul_1_l {T}%type {ro rp} Hro {n}%nat M%M.
Arguments mat_mul_1_r {T}%type {ro rp} Hro {n}%nat M%M.
Arguments mat_opp {T ro} {m n}%nat M%M.
Arguments mat_sub {T ro} {m n}%nat MA%M MB%M.
Arguments mI {T ro} n%nat.
Arguments mZ {T ro} (m n)%nat.
Arguments minus_one_pow {T ro}.
Arguments subm {T} {m n}%nat M%M i%nat j%nat.
Arguments vect_mul_1_l {T}%type {ro rp} Hro {n}%nat V%V.

Notation "A + B" := (mat_add A B) : M_scope.
Notation "A - B" := (mat_sub A B) : M_scope.
Notation "A * B" := (mat_mul A B) : M_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.
Notation "- A" := (mat_opp A) : M_scope.
Notation "A ⁺" := (mat_transp A) (at level 1, format "A ⁺") : M_scope.
Notation "A • V" := (mat_mul_vect_r A V) (at level 40) : M_scope.
Notation "A • V" := (mat_mul_vect_r A V) (at level 40) : V_scope.

End matrix_Notations.
