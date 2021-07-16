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

Record matrix T := mk_mat
  { mat_list_list : list (list T) }.

Theorem matrix_eq : ∀ T (MA MB : matrix T),
  (Forall2 (Forall2 eq) (mat_list_list MA) (mat_list_list MB))
  → MA = MB.
Proof.
intros * Hab.
destruct MA as (lla).
destruct MB as (llb).
cbn in Hab; f_equal.
induction Hab; [ easy | ].
subst l'; f_equal.
induction H; [ easy | ].
now subst x l0.
Qed.

Definition mat_of_list_list {T} (l : list (list T)) : matrix T :=
  mk_mat l.

Definition list_list_of_mat {T} (M : matrix T) :=
  mat_list_list M.

Definition mat_nrows {T} (M : matrix T) := length (mat_list_list M).
Definition mat_ncols {T} (M : matrix T) := length (hd [] (mat_list_list M)).

Definition mat_el {T} {ro : ring_like_op T} (M : matrix T) i j :=
  nth j (nth i (mat_list_list M) []) 0%F.

(*
Theorem matrix_eq : ∀ T (MA MB : matrix T),
  (∀ i j, mat_el MA i j = mat_el MB i j)
  → MA = MB.

Theorem vector_eq {T} (U V : vector T) :
  (∀ i, nth_error (vect_list U) i = nth_error (vect_list V) i)
  → U = V.
Proof.
*)

(*
Theorem matrix_neq : ∀ m n T (MA MB : matrix m n T),
  ¬ (∀ i j, mat_el MA i j = mat_el MB i j)
  → MA ≠ MB.
Proof.
intros * Hab.
intros H.
subst MB.
now apply Hab.
Qed.
*)

(*
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
*)

(*
Compute (list_list_of_mat (mat_of_list_list 0 [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]])).
*)

Theorem fold_mat_nrows {T} : ∀ (M : matrix T),
  length (mat_list_list M) = mat_nrows M.
Proof. easy. Qed.

Theorem fold_mat_ncols {T} : ∀ (M : matrix T),
  length (hd [] (mat_list_list M)) = mat_ncols M.
Proof. easy. Qed.

Theorem fold_mat_el {T} {ro : ring_like_op T} : ∀ (M : matrix T) i j,
  nth j (nth i (mat_list_list M) []) 0%F = mat_el M i j.
Proof. easy. Qed.

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

Definition mat_add (MA MB : matrix T) : matrix T :=
  mk_mat (map2 (map2 rngl_add) (mat_list_list MA) (mat_list_list MB)).

(*
End a.

Require Import Nrl.
Print Nrl.
Check nat_ring_like_op.
Compute (mat_add nat_ring_like_op (mat_of_list_list [[2;3;5]; [3;8;17]]) (mat_of_list_list [[17;22;3]; [12;0;13]])).
*)

(* multiplication *)

Definition mat_mul_el MA MB i k :=
   Σ (j = 0, mat_ncols MA - 1), mat_el MA i j * mat_el MB j k.

Definition mat_mul (MA MB : matrix T) : matrix T :=
  mk_mat
    (map (λ i, map (mat_mul_el MA MB i) (seq 0 (mat_ncols MB)))
       (seq 0 (mat_nrows MA))).

(*
End a.

Require Import Nrl.
Compute (mat_mul nat_ring_like_op (mat_of_list_list [[2;3;5]; [3;8;17]]) (mat_of_list_list [[17;22;3;5]; [12;0;13;0]; [7;15;3;2]])).
     = {| mat_list_list := [[105; 119; 60; 20]; [266; 321; 164; 49]] |}
*)

(*
Fixpoint mul_row_mat (ncols : nat) cnt k MB (MA_row : list T) :=
  match cnt with
  | 0 => []
  | S cnt' =>
      Σ (j = 0, ncols - 1), nth j MA_row 0 * mat_el MB j k ::
      mul_row_mat ncols cnt' (S k) MB MA_row
  end.

Definition mat_mul (MA : matrix T) (MB : matrix T) : matrix T :=
  mk_mat (map (mul_row_mat (mat_ncols MA) (mat_ncols MB) 0 MB)
    (mat_list_list MA)).
*)

(* opposite *)

Definition mat_opp (M : matrix T) : matrix T :=
  mk_mat (map (map rngl_opp) (mat_list_list M)).

(* subtraction *)

Definition mat_sub (MA MB : matrix T) :=
  mat_add MA (mat_opp MB).

(* vector from a matrix column *)

Definition vect_of_mat_col (M : matrix T) j :=
  mk_vect (map (λ row, nth j row 0%F) (mat_list_list M)).

(* concatenation of a matrix and a column vector *)

Definition mat_vect_concat (M : matrix T) V :=
  mk_mat (map2 (λ row e, row ++ [e]) (mat_list_list M) (vect_list V)).

(*
End a.
Compute (list_list_of_mat (mat_vect_concat (mat_of_list_list [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (vect_of_list [43; 12; 29]))).
*)

(* multiplication of a matrix by a vector *)

Definition mat_mul_vect_r (M : matrix T) (V : vector T) :=
  mk_vect (map (λ row, vect_dot_mul (mk_vect row) V) (mat_list_list M)).

(*
End a.
Require Import Nrl.
Compute (list_of_vect (mat_mul_vect_r nat_ring_like_op (mat_of_list_list [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (vect_of_list [43; 12; 29]))).
Compute (1*43+2*12+3*29).
Compute (5*43+6*12+7*29).
Compute (9*43+10*12+11*29).
*)

(* multiplication of a matrix by a scalar *)

Definition mat_mul_scal_l s (M : matrix T) :=
  mk_mat (map (map (rngl_mul s)) (mat_list_list M)).

(* matrix whose k-th column is replaced by a vector *)

Definition mat_repl_vect k (M : matrix T) (V : vector T) :=
  mk_mat
    (map2 (λ row e, firstn k row ++ e :: skipn (S k) row) (mat_list_list M)
       (vect_list V)).

(*
End a.
Compute (list_list_of_mat (mat_repl_vect 2 (mat_of_list_list [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (vect_of_list [43; 12; 29]))).
Compute (list_list_of_mat (mat_repl_vect 0 (mat_of_list_list [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (vect_of_list [43; 12; 29]))).
Compute (list_list_of_mat (mat_repl_vect 15 (mat_of_list_list [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (vect_of_list [43; 12; 29]))).
*)

(* null matrix of dimension m × n *)

Definition mZ m n : matrix T :=
  mk_mat (repeat (repeat 0%F n) m).

(*
End a.
Require Import Nrl.
Compute (mZ nat_ring_like_op 2 7).
Compute (mZ nat_ring_like_op 7 2).
*)

(* identity square matrix of dimension n *)

Definition mI n : matrix T :=
  mk_mat (map (λ i, map (λ j, if Nat.eqb i j then 1%F else 0%F) (seq 0 n)) (seq 0 n)).

(*
End a.
Require Import Nrl.
Compute (mI nat_ring_like_op 2).
Compute (mI nat_ring_like_op 7).
*)

End a.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.
Context {Hro : @rngl_has_opp T ro = true}.

Declare Scope M_scope.
Delimit Scope M_scope with M.

Arguments mat_add {T ro} MA%M MB%M.
Arguments mat_mul {T ro} MA%M MB%M.
Arguments mat_mul_el {T}%type {ro} (MA MB)%M (i k)%nat.
Arguments mat_mul_scal_l {T ro} s%F M%M.
Arguments mat_opp {T}%type {ro}.
Arguments mat_sub {T ro} MA%M MB%M.
Arguments mI {T ro} n%nat.
Arguments mZ {T ro} (m n)%nat.
Arguments minus_one_pow {T ro}.
Arguments vect_zero {T ro} n%nat.

Notation "A + B" := (mat_add A B) : M_scope.
Notation "A - B" := (mat_sub A B) : M_scope.
Notation "A * B" := (mat_mul A B) : M_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.
Notation "- A" := (mat_opp A) : M_scope.

Arguments mat_mul_vect_r {T ro} M%M V%V.

Notation "A • V" := (mat_mul_vect_r A V) (at level 40) : M_scope.
Notation "A • V" := (mat_mul_vect_r A V) (at level 40) : V_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.

Theorem fold_mat_sub : ∀ (MA MB : matrix T), (MA + - MB = MA - MB)%M.
Proof. easy. Qed.

(* commutativity of addition *)

Theorem mat_add_comm : ∀ (MA MB : matrix T), (MA + MB = MB + MA)%M.
Proof.
intros.
unfold mat_add; f_equal.
remember (mat_list_list MA) as lla eqn:Hlla.
remember (mat_list_list MB) as llb eqn:Hllb.
clear MA MB Hlla Hllb.
revert llb.
induction lla as [| la]; intros; [ now destruct llb | cbn ].
destruct llb as [| lb]; [ easy | cbn ].
rewrite IHlla; f_equal.
revert lb.
induction la as [| a]; intros; [ now destruct lb | cbn ].
destruct lb as [| b]; [ easy | cbn ].
now rewrite rngl_add_comm, IHla.
Qed.

(* associativity of addition *)

Theorem mat_add_add_swap : ∀ (MA MB MC : matrix T),
  (MA + MB + MC = MA + MC + MB)%M.
Proof.
intros.
unfold mat_add; f_equal; cbn.
remember (mat_list_list MA) as lla eqn:Hlla.
remember (mat_list_list MB) as llb eqn:Hllb.
remember (mat_list_list MC) as llc eqn:Hllc.
clear MA MB MC Hlla Hllb Hllc.
revert llb llc.
induction lla as [| la]; intros; [ easy | cbn ].
destruct llb as [| lb]; [ now destruct llc | cbn ].
destruct llc as [| lc]; [ easy | cbn ].
rewrite IHlla; f_equal.
revert lb lc.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ now destruct lc | cbn ].
destruct lc as [| c]; [ easy | cbn ].
now rewrite rngl_add_add_swap, IHla.
Qed.

Theorem mat_add_assoc : ∀ (MA MB MC : matrix T),
  (MA + (MB + MC) = (MA + MB) + MC)%M.
Proof.
intros.
rewrite mat_add_comm.
rewrite mat_add_add_swap.
f_equal.
apply mat_add_comm.
Qed.

Definition is_correct_matrix (M : matrix T) :=
  (mat_nrows M = 0 ↔ mat_ncols M = 0) ∧
  ∀ l, l ∈ mat_list_list M → length l = mat_ncols M.

(* addition to zero *)

Theorem mat_add_0_l : ∀ (M : matrix T),
  is_correct_matrix M
  → (mZ (mat_nrows M) (mat_ncols M) + M)%M = M.
Proof.
intros * HM.
unfold is_correct_matrix in HM.
destruct HM as (_, HM).
unfold mZ, "+"%M, mat_nrows, mat_ncols.
unfold mat_ncols in HM.
destruct M as (ll); cbn in HM |-*; f_equal.
remember (length (hd [] ll)) as ncols eqn:H.
clear H.
revert ncols HM.
induction ll as [| la]; intros; [ easy | cbn ].
rewrite IHll. 2: {
  intros l Hl.
  now apply HM; right.
}
f_equal.
specialize (HM la (or_introl eq_refl)).
clear - rp HM.
revert ncols HM.
induction la as [| a]; intros; [ now destruct ncols | cbn ].
destruct ncols; [ easy | cbn ].
rewrite rngl_add_0_l; f_equal.
apply IHla.
cbn in HM.
now apply Nat.succ_inj in HM.
Qed.

(* addition left and right with opposite *)

Theorem mat_add_opp_l : ∀ (M : matrix T),
  is_correct_matrix M
  → (- M + M = mZ (mat_nrows M) (mat_ncols M))%M.
Proof.
intros * HM.
unfold is_correct_matrix in HM.
destruct HM as (_, HM).
unfold "+"%M, mZ, mat_nrows, mat_ncols; cbn; f_equal.
unfold mat_ncols in HM.
destruct M as (ll); cbn in HM |-*.
remember (length (hd [] ll)) as ncols eqn:H; clear H.
induction ll as [| la]; [ easy | cbn ].
rewrite IHll. 2: {
  intros * Hl.
  now apply HM; right.
}
f_equal.
clear IHll.
specialize (HM la (or_introl eq_refl)).
revert ncols HM.
induction la as [| a]; intros; cbn; [ now rewrite <- HM | ].
rewrite rngl_add_opp_l; [ | easy ].
destruct ncols; [ easy | ].
cbn; f_equal.
cbn in HM.
apply Nat.succ_inj in HM.
now apply IHla.
Qed.

Theorem mat_add_opp_r : ∀ (M : matrix T),
  is_correct_matrix M
  → (M - M = mZ (mat_nrows M) (mat_ncols M))%M.
Proof.
intros * HM.
unfold mat_sub.
rewrite mat_add_comm.
now apply mat_add_opp_l.
Qed.

Theorem mI_nrows : ∀ n, mat_nrows (mI n) = n.
Proof.
intros.
destruct n; cbn - [ "=?" ]; [ easy | ].
now rewrite map_length, seq_length.
Qed.

Theorem mI_ncols : ∀ n, mat_ncols (mI n) = n.
Proof.
intros.
destruct n; cbn - [ "=?" ]; [ easy | ].
now rewrite map_length, seq_length.
Qed.

Theorem mat_el_mI_ndiag : ∀ n i j, i ≠ j → mat_el (mI n) i j = 0%F.
Proof.
intros * Hij.
unfold mat_el, mI; cbn.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  now destruct i, j.
}
apply Nat.neq_0_lt_0 in Hnz.
destruct (lt_dec i n) as [Hin| Hin]. {
  rewrite List_map_nth_in with (a := 0); [ | now rewrite seq_length ].
  destruct (lt_dec j n) as [Hjn| Hjn]. {
    rewrite List_map_nth_in with (a := 0); [ | now rewrite seq_length ].
    rewrite seq_nth; [ | easy ].
    rewrite seq_nth; [ cbn | easy ].
    rewrite if_eqb_eq_dec.
    now destruct (Nat.eq_dec i j).
  }
  apply Nat.nlt_ge in Hjn.
  apply nth_overflow.
  now rewrite map_length, seq_length.
}
apply Nat.nlt_ge in Hin.
apply nth_overflow.
rewrite nth_overflow; [ cbn; flia | ].
now rewrite map_length, seq_length.
Qed.

Theorem mat_el_mI_diag : ∀ n i, i < n → mat_el (mI n) i i = 1%F.
Proof.
intros * Hin.
unfold mat_el, mI; cbn.
rewrite List_map_nth_in with (a := 0); [ | now rewrite seq_length ].
rewrite List_map_nth_in with (a := 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
now rewrite Nat.eqb_refl.
Qed.

(* multiplication left and right with identity *)

Theorem mat_mul_1_l : ∀ (M : matrix T),
  is_correct_matrix M
  → (mI (mat_nrows M) * M)%M = M.
Proof.
intros * HM.
unfold is_correct_matrix, mat_ncols in HM.
destruct HM as (_, HM).
unfold "*"%M.
rewrite mI_nrows.
destruct M as (ll); cbn in HM |-*.
f_equal.
unfold mat_ncols; cbn.
remember (length (hd [] ll)) as ncols eqn:H; clear H.
remember (map _ _) as x.
rewrite List_eq_map_seq with (d := []); subst x.
apply map_ext_in.
intros i Hi.
remember (nth i ll []) as la eqn:Hla.
rewrite List_eq_map_seq with (d := 0%F).
rewrite (HM la). 2: {
  rewrite Hla.
  apply nth_In.
  now apply in_seq in Hi.
}
apply map_ext_in.
intros j Hj.
unfold mat_mul_el.
rewrite rngl_summation_split with (j0 := i). 2: {
  split; [ flia | ].
  apply -> Nat.succ_le_mono.
  apply in_seq in Hi.
  rewrite mI_ncols; flia Hi.
}
rewrite rngl_summation_split_last; [ | flia ].
rewrite all_0_rngl_summation_0. 2: {
  intros k Hk.
  rewrite mat_el_mI_ndiag; [ | flia Hk ].
  now apply rngl_mul_0_l; left.
}
rewrite rngl_add_0_l.
apply in_seq in Hi.
rewrite mat_el_mI_diag; [ | easy ].
rewrite rngl_mul_1_l.
remember (Σ (k = _, _), _) as x; cbn; subst x.
rewrite <- Hla.
rewrite all_0_rngl_summation_0. 2: {
  intros k Hk.
  rewrite mat_el_mI_ndiag; [ | flia Hk ].
  now apply rngl_mul_0_l; left.
}
apply rngl_add_0_r.
Qed.

Theorem mat_mul_1_r : ∀ (M : matrix T),
  is_correct_matrix M
  → (M * mI (mat_ncols M))%M = M.
Proof.
intros * HM.
unfold is_correct_matrix, mat_ncols in HM.
destruct HM as (_, HM).
unfold "*"%M.
rewrite mI_ncols.
destruct M as (ll); cbn in HM |-*.
f_equal.
unfold mat_ncols; cbn.
remember (length (hd [] ll)) as ncols eqn:H; clear H.
remember (map _ _) as x.
rewrite List_eq_map_seq with (d := []); subst x.
apply map_ext_in.
intros i Hi.
remember (nth i ll []) as la eqn:Hla.
rewrite List_eq_map_seq with (d := 0%F).
rewrite (HM la). 2: {
  rewrite Hla.
  apply nth_In.
  now apply in_seq in Hi.
}
apply map_ext_in.
intros j Hj.
unfold mat_mul_el.
unfold mat_ncols at 1.
cbn - [ mat_el ].
destruct ll as [| lb]. {
  subst la.
  cbn - [ mat_el nth ].
  rewrite rngl_summation_only_one.
  replace (mat_el _ _ _) with 0%F by now destruct i.
  rewrite rngl_mul_0_l; [ | now left ].
  now destruct i.
}
cbn - [ mat_el ].
rewrite (HM lb (or_introl eq_refl)).
rewrite rngl_summation_split with (j0 := j). 2: {
  split; [ flia | ].
  apply -> Nat.succ_le_mono.
  apply in_seq in Hj.
  flia Hj.
}
rewrite rngl_summation_split_last; [ | flia ].
rewrite all_0_rngl_summation_0. 2: {
  intros k Hk.
  rewrite mat_el_mI_ndiag; [ | flia Hk ].
  now apply rngl_mul_0_r; left.
}
rewrite rngl_add_0_l.
apply in_seq in Hj.
rewrite mat_el_mI_diag; [ | easy ].
rewrite rngl_mul_1_r.
rewrite all_0_rngl_summation_0. 2: {
  intros k Hk.
  rewrite mat_el_mI_ndiag; [ | flia Hk ].
  now apply rngl_mul_0_r; left.
}
rewrite rngl_add_0_r.
subst la; cbn.
now destruct i, j.
Qed.

Theorem mat_vect_mul_1_l : ∀ (V : vector T), (mI (vect_size V) • V)%M = V.
Proof.
intros.
apply vector_eq.
intros i.
remember (nth_error _ _) as x eqn:Hx in |-*; symmetry in Hx.
remember (nth_error _ _) as y eqn:Hy in |-*; symmetry in Hy.
move y before x.
destruct x as [x| ]. {
  apply List_nth_error_Some_iff with (d := 0%F) in Hx.
  destruct Hx as (Hx, Hii).
  cbn in Hii.
  rewrite map_length, map_length, seq_length in Hii.
  destruct y as [y| ]. {
    apply List_nth_error_Some_iff with (d := 0%F) in Hy.
    destruct Hy as (Hy, Hiv).
    f_equal.
    subst x y; cbn.
    rewrite List_map_nth_in with (a := []). 2: {
      now rewrite map_length, seq_length.
    }
    unfold vect_size in Hii.
    clear Hii.
    destruct V as (la).
    cbn in Hiv; cbn.
    unfold vect_dot_mul; cbn.
    rewrite List_map_nth_in with (a := 0); [ | now rewrite seq_length ].
    rewrite map2_map_l.
    rewrite seq_nth; [ cbn | easy ].
    rewrite rngl_summation_list_split with (n := i).
    rewrite all_0_rngl_summation_list_0. 2: {
      intros j Hj.
      rewrite firstn_map2 in Hj.
      rewrite List_firstn_seq in Hj.
      rewrite Nat.min_l in Hj; [ | flia Hiv ].
      apply in_map2_iff in Hj.
      destruct Hj as (k & Hkm & a & b & Hk).
      subst j.
      rewrite seq_length, firstn_length in Hkm.
      rewrite Nat.min_assoc in Hkm.
      rewrite Nat.min_id in Hkm.
      apply Nat.min_glb_lt_iff in Hkm.
      rewrite seq_nth; [ | easy ].
      rewrite if_eqb_eq_dec, Nat.add_0_l.
      destruct (Nat.eq_dec i k) as [H| H]; [ flia Hkm H | clear H ].
      now apply rngl_mul_0_l; left.
    }
    rewrite rngl_add_0_l.
    rewrite skipn_map2.
    rewrite List_skipn_seq; [ cbn | flia Hiv ].
    revert i Hiv.
    induction la as [| a]; intros; [ easy | ].
    destruct i. {
      cbn.
      rewrite rngl_mul_1_l.
      rewrite rngl_summation_list_cons.
      rewrite all_0_rngl_summation_list_0. 2: {
        intros i Hi.
        rewrite <- seq_shift in Hi.
        rewrite map2_map_l in Hi.
        apply in_map2_iff in Hi.
        destruct Hi as (k & Hkm & a' & b & Hk).
        rewrite rngl_mul_0_l in Hk; [ easy | now left ].
      }
      apply rngl_add_0_r.
    }
    cbn - [ "=?" ].
    rewrite <- seq_shift.
    rewrite map2_map_l.
    cbn in Hiv.
    apply Nat.succ_lt_mono in Hiv.
    erewrite map2_ext_in; [ | now intros j k Hj Hk; cbn ].
    now apply IHla.
  } {
    exfalso.
    apply nth_error_None in Hy.
    now apply Nat.nlt_ge in Hy.
  }
}
destruct y as [y| ]; [ | easy ].
exfalso.
apply nth_error_None in Hx.
cbn in Hx.
rewrite map_length, map_length, seq_length in Hx.
apply List_nth_error_Some_iff with (d := 0%F) in Hy.
now apply Nat.nlt_ge in Hx.
Qed.

(* associativity of multiplication *)

Theorem mat_mul_assoc :
  ∀ (MA : matrix T) (MB : matrix T) (MC : matrix T),
  mat_nrows MB ≠ 0
  → mat_ncols MB ≠ 0
  → mat_ncols MA = mat_nrows MB
  → (MA * (MB * MC))%M = ((MA * MB) * MC)%M.
Proof.
intros * Hrbz Hcbz Hcarb.
unfold "*"%M.
f_equal.
unfold mat_nrows at 5; cbn.
rewrite map_length, seq_length.
apply map_ext_in.
intros i Hi.
unfold mat_ncols at 2; cbn.
rewrite List_hd_nth_0.
rewrite List_map_nth_in with (a := 0). 2: {
  rewrite seq_length; flia Hrbz.
}
rewrite map_length, seq_length.
apply map_ext_in.
intros j Hj.
move j before i.
unfold mat_mul_el.
unfold mat_ncols at 4.
rewrite List_hd_nth_0; cbn.
rewrite List_map_nth_in with (a := 0). 2: {
  rewrite seq_length.
  destruct (Nat.eq_dec (mat_nrows MA) 0) as [Hraz| Hraz]. {
    now rewrite Hraz in Hi.
  }
  flia Hraz.
}
rewrite map_length, seq_length.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  rewrite List_map_nth_in with (a := 0). 2: {
    rewrite seq_length.
    rewrite Hcarb in Hk.
    flia Hrbz Hk.
  }
  rewrite List_map_nth_in with (a := 0). 2: {
    rewrite seq_length.
    now apply in_seq in Hj.
  }
  erewrite rngl_summation_eq_compat. 2: {
    intros m Hm.
    rewrite seq_nth; [ | rewrite Hcarb in Hk; flia Hrbz Hk ].
    rewrite seq_nth; [ | now apply in_seq in Hj ].
    easy.
  }
  rewrite rngl_mul_summation_distr_l; [ | now left ].
  erewrite rngl_summation_eq_compat. 2: {
    intros m Hm.
    now rewrite rngl_mul_assoc.
  }
  easy.
}
cbn.
erewrite rngl_summation_eq_compat with (k := mat_ncols MB - 1). 2: {
  intros k Hk.
  rewrite List_map_nth_in with (a := 0). 2: {
    rewrite seq_length.
    now apply in_seq in Hi.
  }
  rewrite List_map_nth_in with (a := 0). 2: {
    rewrite seq_length.
    flia Hcbz Hk.
  }
  erewrite rngl_summation_eq_compat. 2: {
    intros m Hm.
    rewrite seq_nth; [ | now apply in_seq in Hi ].
    rewrite seq_nth; [ | flia Hcbz Hk ].
    easy.
  }
  rewrite rngl_mul_summation_distr_r; [ | now left ].
  easy.
}
cbn.
apply rngl_summation_summation_exch'.
Qed.

(* left distributivity of multiplication over addition *)

Theorem mat_mul_add_distr_l :
  ∀ (MA : matrix T) (MB : matrix T) (MC : matrix T),
  is_correct_matrix MB
  → is_correct_matrix MC
  → mat_nrows MB ≠ 0
  → mat_ncols MA = mat_nrows MB
  → mat_nrows MB = mat_nrows MC
  → mat_ncols MB = mat_ncols MC
  → (MA * (MB + MC) = MA * MB + MA * MC)%M.
Proof.
intros * Hb Hc Hrbz Hcarb Hcrbc Hcbc.
unfold "*"%M, "+"%M.
f_equal; cbn.
rewrite map2_map_l, map2_map_r, map2_diag.
apply map_ext_in.
intros i Hi.
rewrite map2_map_l, map2_map_r, <- Hcbc, map2_diag.
unfold mat_ncols at 1; cbn.
rewrite List_hd_nth_0.
rewrite map2_nth with (a := []) (b := []); cycle 1. {
  rewrite fold_mat_nrows; flia Hrbz.
} {
  rewrite fold_mat_nrows; flia Hrbz Hcrbc.
}
rewrite map2_length; cbn.
do 2 rewrite <- List_hd_nth_0.
do 2 rewrite fold_mat_ncols.
rewrite <- Hcbc, Nat.min_id.
apply map_ext_in.
intros j Hj.
unfold mat_mul_el; cbn.
rewrite <- rngl_summation_add_distr.
apply rngl_summation_eq_compat.
intros k Hk.
rewrite <- rngl_mul_add_distr_l.
f_equal.
rewrite map2_nth with (a := []) (b := []); cycle 1. {
  rewrite fold_mat_nrows.
  rewrite Hcarb in Hk; flia Hrbz Hk.
} {
  rewrite fold_mat_nrows.
  rewrite Hcarb, Hcrbc in Hk.
  flia Hrbz Hcrbc Hk.
}
rewrite map2_nth with (a := 0%F) (b := 0%F); cycle 1. {
  unfold is_correct_matrix in Hb.
  destruct Hb as (_, Hb).
  apply in_seq in Hj.
  rewrite Hb; [ easy | ].
  apply nth_In.
  rewrite fold_mat_nrows.
  rewrite Hcarb in Hk.
  flia Hrbz Hk.
} {
  unfold is_correct_matrix in Hc.
  destruct Hc as (_, Hc).
  apply in_seq in Hj.
  rewrite Hc; [ now rewrite <- Hcbc | ].
  apply nth_In.
  rewrite fold_mat_nrows, <- Hcrbc.
  rewrite Hcarb in Hk.
  flia Hrbz Hk.
}
now do 2 rewrite fold_mat_el.
Qed.

(* right distributivity of multiplication over addition *)

Theorem mat_mul_add_distr_r :
  ∀ (MA : matrix T) (MB : matrix T) (MC : matrix T),
  is_correct_matrix MA
  → is_correct_matrix MB
  → mat_nrows MA ≠ 0
  → mat_nrows MA = mat_nrows MB
  → mat_ncols MA = mat_ncols MB
  → ((MA + MB) * MC = MA * MC + MB * MC)%M.
Proof.
intros * Ha Hb Hraz Hrarb Hcacb.
assert (Hcaz : mat_ncols MA ≠ 0). {
  destruct Ha as (Ha, _).
  intros H; apply Hraz.
  now apply Ha.
}
unfold "*"%M, "+"%M.
f_equal; cbn.
rewrite map2_length.
do 2 rewrite fold_mat_nrows.
rewrite map2_map_l, map2_map_r, <- Hrarb, map2_diag.
rewrite Nat.min_id.
apply map_ext_in.
intros i Hi.
rewrite map2_map_l, map2_map_r, map2_diag.
apply map_ext_in.
intros j Hj.
unfold mat_mul_el; cbn.
rewrite <- Hcacb.
rewrite <- rngl_summation_add_distr.
unfold mat_ncols at 1; cbn.
rewrite List_hd_nth_0.
rewrite map2_nth with (a := []) (b := []); cycle 1. {
  rewrite fold_mat_nrows; flia Hraz.
} {
  rewrite fold_mat_nrows, <- Hrarb; flia Hraz.
}
rewrite map2_length.
do 2 rewrite <- List_hd_nth_0.
do 2 rewrite fold_mat_ncols.
rewrite <- Hcacb, Nat.min_id.
apply rngl_summation_eq_compat.
intros k Hk.
rewrite map2_nth with (a := []) (b := []); cycle 1. {
  rewrite fold_mat_nrows.
  now apply in_seq in Hi.
} {
  rewrite fold_mat_nrows, <- Hrarb.
  now apply in_seq in Hi.
}
rewrite map2_nth with (a := 0%F) (b := 0%F); cycle 1. {
  unfold is_correct_matrix in Ha.
  destruct Ha as (_, Ha).
  rewrite Ha; [ flia Hcaz Hk | ].
  apply nth_In.
  rewrite fold_mat_nrows.
  now apply in_seq in Hi.
} {
  unfold is_correct_matrix in Hb.
  destruct Hb as (_, Hb).
  rewrite Hb; [ rewrite <- Hcacb; flia Hcaz Hk | ].
  apply in_seq in Hi.
  apply nth_In.
  now rewrite fold_mat_nrows, <- Hrarb.
}
do 2 rewrite fold_mat_el.
apply rngl_mul_add_distr_r.
Qed.

(* left distributivity of multiplication by scalar over addition *)

Theorem mat_mul_scal_l_add_distr_r : ∀ a b (M : matrix T),
  ((a + b)%F × M)%M = (a × M + b × M)%M.
Proof.
intros.
unfold "+"%M, "×"%M.
cbn; f_equal.
rewrite map2_map_l, map2_map_r.
rewrite map2_diag.
apply map_ext_in.
intros la Hla.
rewrite map2_map_l, map2_map_r.
rewrite map2_diag.
apply map_ext_in.
intros c Hc.
apply rngl_mul_add_distr_r.
Qed.

(* associativity of multiplication by scalar *)

Theorem mat_mul_scal_l_mul_assoc : ∀ a b (M : matrix T),
  (a × (b × M))%M = ((a * b)%F × M)%M.
Proof.
intros.
unfold "*"%M, "×"%M.
cbn; f_equal.
rewrite map_map.
apply map_ext_in.
intros la Hla.
rewrite map_map.
apply map_ext_in.
intros i Hi.
apply rngl_mul_assoc.
Qed.

Theorem mat_mul_scal_l_mul :
  ∀ a (MA : matrix T) (MB : matrix T),
  is_correct_matrix MA
  → (a × MA * MB = a × (MA * MB))%M.
Proof.
intros * Ha.
unfold "*"%M, "×"%M.
cbn; f_equal.
rewrite map_length; cbn.
rewrite fold_mat_nrows.
rewrite map_map.
apply map_ext_in.
intros i Hi.
destruct (Nat.eq_dec (mat_nrows MA) 0) as [Hraz| Hraz]. {
  now rewrite Hraz in Hi.
}
rewrite map_map.
apply map_ext_in.
intros j Hj.
unfold mat_mul_el; cbn.
unfold mat_ncols at 1; cbn.
rewrite List_hd_nth_0.
rewrite List_map_nth_in with (a := []). 2: {
  rewrite fold_mat_nrows; flia Hraz.
}
rewrite map_length.
rewrite <- List_hd_nth_0.
rewrite fold_mat_ncols.
rewrite rngl_mul_summation_distr_l; [ | now left ].
apply rngl_summation_eq_compat.
intros k Hk.
rewrite List_map_nth_in with (a := []). 2: {
  rewrite fold_mat_nrows.
  now apply in_seq in Hi.
}
rewrite List_map_nth_in with (a := 0%F). 2: {
  destruct Ha as (Harc, Ha).
  rewrite Ha. 2: {
    apply nth_In.
    rewrite fold_mat_nrows.
    now apply in_seq in Hi.
  }
  assert (Hcaz : mat_ncols MA ≠ 0). {
    intros H; apply Hraz.
    now apply Harc.
  }
  flia Hk Hcaz.
}
rewrite fold_mat_el.
symmetry.
apply rngl_mul_assoc.
Qed.

Theorem mat_mul_mul_scal_l :
  rngl_is_comm = true →
  ∀ a (MA : matrix T) (MB : matrix T),
  (MA * (a × MB) = a × (MA * MB))%M.
Proof.
intros Hic *.
...
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
Arguments mat_vect_mul_1_l {T}%type {ro rp} Hro {n}%nat V%V.

Notation "A + B" := (mat_add A B) : M_scope.
Notation "A - B" := (mat_sub A B) : M_scope.
Notation "A * B" := (mat_mul A B) : M_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.
Notation "- A" := (mat_opp A) : M_scope.
Notation "A ⁺" := (mat_transp A) (at level 1, format "A ⁺") : M_scope.
Notation "A • V" := (mat_mul_vect_r A V) (at level 40) : M_scope.
Notation "A • V" := (mat_mul_vect_r A V) (at level 40) : V_scope.

End matrix_Notations.
