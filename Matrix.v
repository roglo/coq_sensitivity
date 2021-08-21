(* matrices *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Bool.
Import List List.ListNotations.
Require Import Init.Nat.

Require Import Misc.
Require Import RingLike RLsummation RLproduct.
Require Import MyVector.

Notation "'⋀' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, (c && g)) true)
  (at level 45, i at level 0, l at level 60).

Definition nth_nth_error A (ll : list (list A)) (i j : nat) := 
  match nth_error ll i with
  | None => None
  | Some l => Some (nth_error l j)
  end.

(* matrices *)

Record matrix T := mk_mat
  { mat_list_list : list (list T) }.

Theorem matrix_eq : ∀ T (ro : ring_like_op T) (MA MB : matrix T),
  (∀ i j,
   nth_nth_error (mat_list_list MA) i j =
   nth_nth_error (mat_list_list MB) i j)
  → MA = MB.
Proof.
intros * ro * Hab.
destruct MA as (lla).
destruct MB as (llb).
cbn in Hab; f_equal.
remember (length lla) as len eqn:Hlen.
symmetry in Hlen.
revert lla llb Hab Hlen.
induction len; intros. {
  apply length_zero_iff_nil in Hlen.
  subst lla.
  destruct llb as [| lb]; [ easy | exfalso ].
  now specialize (Hab 0 0).
}
destruct lla as [| la]; [ easy | ].
cbn in Hlen.
apply Nat.succ_inj in Hlen.
destruct llb as [| lb]; [ now specialize (Hab 0 0) | ].
f_equal. {
  specialize (Hab 0); cbn in Hab.
  revert lb Hab.
  induction la as [| a]; intros. {
    destruct lb as [| b]; [ easy | ].
    now specialize (Hab 0).
  }
  destruct lb as [| b]; [ now specialize (Hab 0) | ].
  f_equal. {
    specialize (Hab 0); cbn in Hab.
    now injection Hab.
  }
  apply IHla.
  intros j.
  now specialize (Hab (S j)).
} {
  apply IHlen; [ | easy ].
  intros i j.
  now specialize (Hab (S i) j).
}
Qed.

Definition mat_of_list_list {T} (l : list (list T)) : matrix T :=
  mk_mat l.

Definition list_list_of_mat {T} (M : matrix T) :=
  mat_list_list M.

Definition mat_nrows {T} (M : matrix T) := length (mat_list_list M).
Definition mat_ncols {T} (M : matrix T) := length (hd [] (mat_list_list M)).

Definition mat_el {T} {ro : ring_like_op T} (M : matrix T) i j :=
  nth j (nth i (mat_list_list M) []) 0%F.

Theorem fold_mat_nrows {T} : ∀ (M : matrix T),
  length (mat_list_list M) = mat_nrows M.
Proof. easy. Qed.

Theorem fold_mat_ncols {T} : ∀ (M : matrix T),
  length (hd [] (mat_list_list M)) = mat_ncols M.
Proof. easy. Qed.

Theorem fold_mat_el {T} {ro : ring_like_op T} : ∀ (M : matrix T) i j,
  nth j (nth i (mat_list_list M) []) 0%F = mat_el M i j.
Proof. easy. Qed.

Theorem eq_mat_nrows_0 {T} : ∀ M : matrix T,
  mat_nrows M = 0
  → mat_list_list M = [].
Proof.
intros * Hr.
unfold mat_nrows in Hr.
now apply length_zero_iff_nil in Hr.
Qed.

(* correct_matrix: matrix whose list list is made of non
   empty lists (rows) of same length *)
(* this definition should (if it could) be defined like
   is_square_matrix below, to allow property to be
   unique *)

Definition is_correct_matrix {T} (M : matrix T) :=
  (mat_ncols M = 0 → mat_nrows M = 0) ∧
  ∀ l, l ∈ mat_list_list M → length l = mat_ncols M.

Record correct_matrix T := mk_cm
  { cm_mat : matrix T;
    cm_prop : is_correct_matrix cm_mat }.

Theorem fold_corr_mat_ncols {T} : ∀ (M : matrix T) d,
  is_correct_matrix M
  → ∀ i, i < mat_nrows M
  → length (nth i (mat_list_list M) d) = mat_ncols M.
Proof.
intros * Hm * Him.
destruct Hm as (Hcr, Hc).
apply Hc.
apply nth_In.
now rewrite fold_mat_nrows.
Qed.

(* square_matrix *)

Definition is_square_matrix {T} n (M : matrix T) :=
  (mat_nrows M =? n) &&
  ((negb (mat_ncols M =? 0)) || (mat_nrows M =? 0)) &&
  ⋀ (l ∈ mat_list_list M), (length l =? n).

Record square_matrix n T :=
  { sm_mat : matrix T;
    sm_prop : is_square_matrix n sm_mat = true }.

Theorem square_matrix_eq {n T} : ∀ (MA MB : square_matrix n T),
  sm_mat MA = sm_mat MB
  → MA = MB.
Proof.
intros * Hab.
destruct MA as (MA, Ha).
destruct MB as (MB, Hb).
cbn in Hab.
destruct Hab.
f_equal.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

(* is_square_matrix (a bool) easier to use with Prop *)

Theorem is_sm_mat_iff {T} n : ∀ (M : matrix T),
  is_square_matrix n M = true ↔
  mat_nrows M = n ∧
  (mat_ncols M = 0 → mat_nrows M = 0) ∧
  ∀ l, l ∈ mat_list_list M → length l = n.
Proof.
intros.
unfold is_square_matrix.
split; intros Hm. {
  apply Bool.andb_true_iff in Hm.
  destruct Hm as (Hm, Hc).
  apply Bool.andb_true_iff in Hm.
  destruct Hm as (Hr, Hrc).
  apply Bool.orb_true_iff in Hrc.
  apply Nat.eqb_eq in Hr.
  split; [ easy | ].
  split. {
    intros Hcz.
    destruct Hrc as [Hrc| Hrc]. {
      apply negb_true_iff in Hrc.
      now apply Nat.eqb_neq in Hrc.
    } {
      now apply Nat.eqb_eq in Hrc.
    }
  }
  intros l Hl.
  remember (mat_list_list M) as ll eqn:Hll.
  clear Hll.
  induction ll as [| la]; [ easy | cbn ].
  rewrite iter_list_cons in Hc; cycle 1; try easy. {
    intros b; apply andb_true_r.
  } {
    intros; apply andb_assoc.
  }
  apply Bool.andb_true_iff in Hc.
  destruct Hc as (Hla, Hc).
  apply Nat.eqb_eq in Hla.
  destruct Hl as [Hl| Hl]; [ now subst l | ].
  now apply IHll.
} {
  destruct Hm as (Hr & Hrc & Hc).
  apply Bool.andb_true_iff.
  split. {
    apply Bool.andb_true_iff.
    split; [ now apply Nat.eqb_eq in Hr | ].
    apply Bool.orb_true_iff.
    destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
      move Hnz at top; subst n.
      right.
      now apply Nat.eqb_eq.
    }
    left.
    rewrite <- Hr in Hnz.
    apply negb_true_iff.
    apply Nat.eqb_neq.
    intros H.
    now apply Hnz, Hrc.
  }
  remember (mat_list_list M) as ll eqn:Hll.
  clear Hll.
  induction ll as [| la]; [ easy | ].
  rewrite iter_list_cons; cycle 1; try easy. {
    intros b; apply andb_true_r.
  } {
    intros; apply andb_assoc.
  }
  apply Bool.andb_true_iff.
  split; [ now apply Nat.eqb_eq, Hc; left | ].
  apply IHll.
  intros l Hl.
  now apply Hc; right.
}
Qed.

Theorem square_matrix_nrows {n T} : ∀ (M : matrix T),
  is_square_matrix n M = true
  → mat_nrows M = n.
Proof.
intros * Hm.
now apply is_sm_mat_iff in Hm.
Qed.

Theorem square_matrix_ncols {n T} : ∀ (M : matrix T),
  is_square_matrix n M = true
  → mat_ncols M = n.
Proof.
intros * Hm.
apply is_sm_mat_iff in Hm.
destruct Hm as (Hr & Hcr & Hc).
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  unfold mat_nrows in Hr.
  apply length_zero_iff_nil in Hr.
  unfold mat_ncols.
  now rewrite Hr.
}
apply Nat.neq_0_lt_0 in Hnz.
apply Hc.
rewrite List_hd_nth_0.
apply nth_In.
now rewrite fold_mat_nrows, Hr.
Qed.

Theorem squ_mat_is_corr {n T} : ∀ (M : matrix T),
  is_square_matrix n M = true
  → is_correct_matrix M.
Proof.
intros * Hsm.
specialize (square_matrix_ncols _ Hsm) as Hc.
apply is_sm_mat_iff in Hsm.
split; [ easy | ].
intros l Hl.
destruct Hsm as (Hr & Hcr & Hc').
now rewrite Hc'.
Qed.

(* *)

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
   ∑ (j = 0, mat_ncols MA - 1), mat_el MA i j * mat_el MB j k.

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
  mk_mat (map2 (replace_at k) (mat_list_list M) (vect_list V)).

(*
End a.
Compute (list_list_of_mat (mat_repl_vect 2 (mat_of_list_list [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (vect_of_list [43; 12; 29]))).
Compute (list_list_of_mat (mat_repl_vect 0 (mat_of_list_list [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (vect_of_list [43; 12; 29]))).
Compute (list_list_of_mat (mat_repl_vect 15 (mat_of_list_list [[1; 2; 3; 4]; [5; 6; 7; 8]; [9; 10; 11; 12]]) (vect_of_list [43; 12; 29]))).
*)

Theorem mat_el_repl_vect : ∀ (M : matrix T) V i j k,
  is_correct_matrix M
  → i < vect_size V
  → i < mat_nrows M
  → j < mat_ncols M
  → k < mat_ncols M
  → mat_el (mat_repl_vect k M V) i j =
    if Nat.eq_dec j k then vect_el V i else mat_el M i j.
Proof.
intros * Hm His Hir Hjc Hkc; cbn.
rewrite map2_nth with (a := []) (b := 0%F); cycle 1. {
  now rewrite fold_mat_nrows.
} {
  now rewrite fold_vect_size.
}
unfold replace_at.
destruct (Nat.eq_dec j k) as [Hjk| Hjk]. {
  subst k.
  rewrite app_nth2. 2: {
    rewrite firstn_length.
    rewrite fold_corr_mat_ncols; [ | easy | easy ].
    rewrite Nat.min_l; [ | flia Hjc ].
    now unfold "≥".
  }
  rewrite firstn_length.
  rewrite fold_corr_mat_ncols; [ | easy | easy ].
  rewrite Nat.min_l; [ | flia Hjc ].
  now rewrite Nat.sub_diag.
}
destruct (lt_dec j k) as [Hljk| Hljk]. {
  rewrite app_nth1. 2: {
    rewrite firstn_length.
    rewrite fold_corr_mat_ncols; [ | easy | easy ].
    rewrite Nat.min_l; [ easy | flia Hkc ].
  }
  rewrite List_nth_firstn; [ | easy ].
  now rewrite fold_mat_el.
} {
  apply Nat.nlt_ge in Hljk.
  rewrite app_nth2. 2: {
    rewrite firstn_length.
    rewrite fold_corr_mat_ncols; [ | easy | easy ].
    rewrite Nat.min_l; [ easy | flia Hkc ].
  }
  rewrite firstn_length.
  rewrite fold_corr_mat_ncols; [ | easy | easy ].
  rewrite Nat.min_l; [ | flia Hkc ].
  replace (j - k) with (S (j - k - 1)) by flia Hjk Hljk.
  cbn - [ skipn ].
  rewrite List_nth_skipn.
  rewrite <- (Nat.add_1_l k), Nat.add_assoc.
  rewrite Nat.sub_add; [ | flia Hjk Hljk ].
  now rewrite Nat.sub_add.
}
Qed.

Theorem mat_repl_vect_nrows : ∀ k (M : matrix T) V,
  vect_size V = mat_nrows M
  → mat_nrows (mat_repl_vect k M V) = mat_nrows M.
Proof.
intros * Hv; cbn.
rewrite map2_length.
rewrite fold_mat_nrows, fold_vect_size, Hv.
apply Nat.min_id.
Qed.

Theorem mat_repl_vect_ncols : ∀ k (M : matrix T) V,
  k < mat_ncols M
  → vect_size V = mat_ncols M
  → mat_ncols (mat_repl_vect k M V) = mat_ncols M.
Proof.
intros * Hkc Hv.
(* works with nrows=0 *)
destruct (Nat.eq_dec (mat_nrows M) 0) as [Hrz| Hrz]. {
  unfold mat_nrows in Hrz.
  apply length_zero_iff_nil in Hrz.
  unfold mat_ncols; cbn.
  now rewrite Hrz.
}
apply Nat.neq_0_lt_0 in Hrz.
(* works with ncols=0 *)
destruct (Nat.eq_dec (mat_ncols M) 0) as [Hcz| Hcz]. {
  rewrite Hcz in Hv.
  unfold vect_size in Hv.
  apply length_zero_iff_nil in Hv.
  unfold mat_ncols in Hcz.
  apply length_zero_iff_nil in Hcz.
  unfold mat_ncols; cbn.
  rewrite Hv.
  now rewrite map2_nil_r, Hcz.
}
apply Nat.neq_0_lt_0 in Hcz.
unfold mat_ncols.
cbn - [ skipn ].
rewrite List_hd_nth_0.
rewrite map2_nth with (a := []) (b := 0%F); cycle 1. {
  now rewrite fold_mat_nrows.
} {
  now rewrite fold_vect_size, Hv.
}
unfold replace_at.
rewrite app_length.
rewrite firstn_length.
rewrite <- List_hd_nth_0.
rewrite fold_mat_ncols.
rewrite List_length_cons.
rewrite skipn_length.
rewrite fold_mat_ncols.
flia Hkc.
Qed.

Theorem mat_repl_vect_is_square : ∀ n k (M : matrix T) V,
  k < mat_ncols M
  → vect_size V = n
  → is_square_matrix n M = true
  → is_square_matrix n (mat_repl_vect k M V) = true.
Proof.
intros * Hkc Hv Hm.
specialize (square_matrix_ncols _ Hm) as Hcn.
apply is_sm_mat_iff in Hm.
apply is_sm_mat_iff.
destruct Hm as (Hr & Hcr & Hc).
rewrite mat_repl_vect_nrows; [ | congruence ].
split; [ easy | ].
split. {
  destruct (lt_dec k (mat_ncols M)) as [Hkm| Hkm]. {
    rewrite mat_repl_vect_ncols; [ easy | easy | congruence ].
  }
  apply Nat.nlt_ge in Hkm.
  rewrite mat_repl_vect_ncols; [ easy | easy | congruence ].
} {
  intros la Hla.
  cbn - [ skipn ] in Hla.
  apply in_map2_iff in Hla.
  destruct Hla as (i & Hi & lb & a & Hla).
  rewrite fold_mat_nrows, fold_vect_size, Hr, Hv in Hi.
  rewrite Nat.min_id in Hi.
  subst la.
  unfold replace_at.
  rewrite app_length.
  rewrite firstn_length.
  cbn - [ skipn ].
  rewrite skipn_length.
  rewrite fold_corr_mat_ncols; [ | | now rewrite Hr ]. 2: {
    split; [ easy | now rewrite Hcn ].
  }
  rewrite Nat.min_l; [ | flia Hkc ].
  rewrite Hcn in Hkc |-*.
  flia Hkc.
}
Qed.

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

Definition δ i j := if i =? j then 1%F else 0%F.
Definition mI n : matrix T := mk_mat (map (λ i, map (δ i) (seq 0 n)) (seq 0 n)).

Theorem δ_comm : ∀ i j, δ i j = δ j i.
Proof.
intros.
unfold δ.
now rewrite Nat.eqb_sym.
Qed.

Theorem δ_diag : ∀ i, δ i i = 1%F.
Proof.
intros.
unfold δ.
now rewrite Nat.eqb_refl.
Qed.

Theorem δ_ndiag : ∀ i j, i ≠ j → δ i j = 0%F.
Proof.
intros * Hij.
unfold δ.
rewrite if_eqb_eq_dec.
now destruct (Nat.eq_dec i j).
Qed.

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

Arguments δ {T ro} (i j)%nat.

Arguments matrix_eq {T}%type {ro} (MA MB)%M.
Arguments mat_add {T ro} MA%M MB%M.
Arguments mat_mul {T ro} MA%M MB%M.
Arguments mat_mul_el {T}%type {ro} (MA MB)%M (i k)%nat.
Arguments mat_mul_scal_l {T ro} s%F M%M.
Arguments mat_list_list [T]%type m%M.
Arguments mat_nrows {T}%type M%M.
Arguments mat_ncols {T}%type M%M.
Arguments mat_el {T}%type {ro} M%M (i j)%nat.
Arguments mat_opp {T}%type {ro}.
Arguments mat_sub {T ro} MA%M MB%M.
Arguments mI {T ro} n%nat.
Arguments mZ {T ro} (m n)%nat.
Arguments minus_one_pow {T ro}.
Arguments vect_zero {T ro} n%nat.
Arguments is_correct_matrix {T}%type M%M.
Arguments is_square_matrix {T}%type n%nat M%M.

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

(* addition to zero *)

Theorem mat_add_0_l {m n} : ∀ (M : matrix T),
  is_correct_matrix M
  → m = mat_nrows M
  → n = mat_ncols M
  → (mZ m n + M)%M = M.
Proof.
intros * HM Hr Hc.
subst m n.
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

Theorem mat_add_0_r {m n} : ∀ (M : matrix T),
  is_correct_matrix M
  → m = mat_nrows M
  → n = mat_ncols M
  → (M + mZ m n)%M = M.
Proof.
intros * HM Hr Hc.
rewrite mat_add_comm.
now apply mat_add_0_l.
Qed.

(* addition left and right with opposite *)

Theorem mat_add_opp_l {m n} : ∀ (M : matrix T),
  is_correct_matrix M
  → m = mat_nrows M
  → n = mat_ncols M
  → (- M + M = mZ m n)%M.
Proof.
intros * HM Hr Hc.
subst m n.
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

Theorem mat_add_sub :
  ∀ MA MB : matrix T,
  is_correct_matrix MA
  → is_correct_matrix MB
  → mat_nrows MA = mat_nrows MB
  → mat_ncols MA = mat_ncols MB
  → (MA + MB - MB)%M = MA.
Proof.
intros * Ha Hb Hrab Hcab.
unfold mat_sub.
rewrite <- mat_add_assoc.
rewrite fold_mat_sub.
rewrite mat_add_opp_r; [ | easy ].
now rewrite mat_add_0_r.
Qed.

Theorem mZ_nrows : ∀ m n, mat_nrows (mZ m n) = m.
Proof.
intros; cbn.
apply repeat_length.
Qed.

Theorem mZ_ncols : ∀ m n, m ≠ 0 → mat_ncols (mZ m n) = n.
Proof.
intros * Hmz.
unfold mZ, mat_ncols; cbn.
destruct m; [ easy | cbn ].
apply repeat_length.
Qed.

Theorem map_seq_length : ∀ A (f : _ → A) a len,
  length (map f (seq a len)) = len.
Proof.
intros.
now rewrite map_length, seq_length.
Qed.

Theorem mI_nrows : ∀ n, mat_nrows (mI n) = n.
Proof.
intros.
destruct n; cbn - [ "=?" ]; [ easy | ].
now rewrite map_seq_length.
Qed.

Theorem mI_ncols : ∀ n, mat_ncols (mI n) = n.
Proof.
intros.
destruct n; cbn - [ "=?" ]; [ easy | ].
now rewrite map_seq_length.
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
  rewrite List_map_nth' with (a := 0); [ | now rewrite seq_length ].
  destruct (lt_dec j n) as [Hjn| Hjn]. {
    rewrite List_map_nth' with (a := 0); [ | now rewrite seq_length ].
    rewrite seq_nth; [ | easy ].
    rewrite seq_nth; [ cbn | easy ].
    unfold δ.
    rewrite if_eqb_eq_dec.
    now destruct (Nat.eq_dec i j).
  }
  apply Nat.nlt_ge in Hjn.
  apply nth_overflow.
  now rewrite map_seq_length.
}
apply Nat.nlt_ge in Hin.
apply nth_overflow.
rewrite nth_overflow; [ cbn; flia | ].
now rewrite map_seq_length.
Qed.

Theorem mat_el_mI_diag : ∀ n i, i < n → mat_el (mI n) i i = 1%F.
Proof.
intros * Hin.
unfold mat_el, mI; cbn.
rewrite List_map_nth' with (a := 0); [ | now rewrite seq_length ].
rewrite List_map_nth' with (a := 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
unfold δ.
now rewrite Nat.eqb_refl.
Qed.

(* multiplication left and right with identity *)

Theorem mat_mul_1_l {n} : ∀ (M : matrix T),
  is_correct_matrix M
  → n = mat_nrows M
  → (mI n * M)%M = M.
Proof.
intros * HM Hn; subst n.
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
rewrite rngl_summation_split3 with (j0 := i). 2: {
  split; [ flia | ].
  apply Nat.succ_le_mono.
  apply in_seq in Hi.
  rewrite mI_ncols; flia Hi.
}
rewrite all_0_rngl_summation_0. 2: {
  intros k Hk.
  rewrite mat_el_mI_ndiag; [ | flia Hk ].
  now apply rngl_mul_0_l; left.
}
rewrite rngl_add_0_l.
apply in_seq in Hi.
rewrite mat_el_mI_diag; [ | easy ].
rewrite rngl_mul_1_l.
remember (∑ (k = _, _), _) as x; cbn; subst x.
rewrite <- Hla.
rewrite all_0_rngl_summation_0. 2: {
  intros k Hk.
  rewrite mat_el_mI_ndiag; [ | flia Hk ].
  now apply rngl_mul_0_l; left.
}
apply rngl_add_0_r.
Qed.

Theorem mat_mul_1_r {n} : ∀ (M : matrix T),
  is_correct_matrix M
  → n = mat_ncols M
  → (M * mI n)%M = M.
Proof.
intros * HM H; subst n.
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
(* rather use more modern rngl_summation_split3... *)
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

Theorem mat_vect_mul_1_l : ∀ n (V : vector T),
  n = vect_size V
  → (mI n • V)%M = V.
Proof.
intros * Hn; subst n.
apply vector_eq.
intros i.
remember (nth_error _ _) as x eqn:Hx in |-*; symmetry in Hx.
remember (nth_error _ _) as y eqn:Hy in |-*; symmetry in Hy.
move y before x.
destruct x as [x| ]. {
  apply List_nth_error_Some_iff with (d := 0%F) in Hx.
  destruct Hx as (Hx, Hii).
  cbn in Hii.
  rewrite map_length, map_seq_length in Hii.
  destruct y as [y| ]. {
    apply List_nth_error_Some_iff with (d := 0%F) in Hy.
    destruct Hy as (Hy, Hiv).
    f_equal.
    subst x y; cbn.
    rewrite List_map_nth' with (a := []). 2: {
      now rewrite map_seq_length.
    }
    unfold vect_size in Hii.
    clear Hii.
    destruct V as (la).
    cbn in Hiv; cbn.
    unfold vect_dot_mul; cbn.
    rewrite List_map_nth' with (a := 0); [ | now rewrite seq_length ].
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
      unfold δ.
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
        unfold δ in Hk; cbn in Hk.
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
rewrite map_length, map_seq_length in Hx.
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
rewrite map_seq_length.
apply map_ext_in.
intros i Hi.
unfold mat_ncols at 2; cbn.
rewrite List_map_hd with (a := 0). 2: {
  now intros H; apply List_seq_eq_nil in H.
}
rewrite map_seq_length.
apply map_ext_in.
intros j Hj.
move j before i.
unfold mat_mul_el.
unfold mat_ncols at 4.
cbn.
rewrite List_map_hd with (a := 0). 2: {
  intros H; apply List_seq_eq_nil in H.
  now rewrite H in Hi.
}
rewrite map_seq_length.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  rewrite List_map_nth' with (a := 0). 2: {
    rewrite seq_length.
    rewrite Hcarb in Hk.
    flia Hrbz Hk.
  }
  rewrite List_map_nth' with (a := 0). 2: {
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
  rewrite List_map_nth' with (a := 0). 2: {
    rewrite seq_length.
    now apply in_seq in Hi.
  }
  rewrite List_map_nth' with (a := 0). 2: {
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
  apply in_seq in Hj.
  rewrite fold_corr_mat_ncols; [ now rewrite <- Hcbc | easy | ].
  rewrite <- Hcrbc.
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
  apply in_seq in Hi.
  rewrite fold_corr_mat_ncols; [ flia Hcaz Hk | easy | easy ].
} {
  apply in_seq in Hi.
  rewrite Hrarb in Hi.
  rewrite fold_corr_mat_ncols; [ | easy | easy ].
  rewrite <- Hcacb; flia Hcaz Hk.
}
do 2 rewrite fold_mat_el.
apply rngl_mul_add_distr_r.
Qed.

(* *)

Theorem mat_mul_scal_l_nrows : ∀ M μ, mat_nrows (μ × M) = mat_nrows M.
Proof. now intros; cbn; rewrite map_length. Qed.

Theorem mat_mul_scal_l_ncols : ∀ M μ, mat_ncols (μ × M) = mat_ncols M.
Proof.
intros.
unfold mat_ncols; cbn.
destruct (Nat.eq_dec (mat_nrows M) 0) as [Hrz| Hrz]. {
  unfold mat_nrows in Hrz.
  apply length_zero_iff_nil in Hrz.
  now rewrite Hrz.
}
apply Nat.neq_0_lt_0 in Hrz.
rewrite List_hd_nth_0.
rewrite (List_map_nth' []); [ | now rewrite fold_mat_nrows ].
rewrite map_length.
now rewrite List_hd_nth_0.
Qed.

Theorem is_correct_matrix_mul_scal_l : ∀ M μ,
  is_correct_matrix M
  → is_correct_matrix (μ × M).
Proof.
intros * Hm.
destruct Hm as (Hcr, Hc).
split. {
  unfold mat_ncols; cbn.
  rewrite map_length, fold_mat_nrows.
  rewrite List_hd_nth_0.
  intros Hc'.
  destruct (Nat.eq_dec (mat_nrows M) 0) as [Hrz| Hrz]; [ easy | ].
  rewrite (List_map_nth' []) in Hc'. 2: {
    rewrite fold_mat_nrows.
    now apply Nat.neq_0_lt_0 in Hrz.
  }
  rewrite map_length in Hc'.
  rewrite <- List_hd_nth_0 in Hc'.
  rewrite fold_mat_ncols in Hc'.
  now apply Hcr.
} {
  intros la Hla.
  cbn in Hla.
  apply in_map_iff in Hla.
  destruct Hla as (lb & Hla & Hlb).
  subst la.
  rewrite map_length.
  rewrite mat_mul_scal_l_ncols.
  now apply Hc.
}
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
rewrite List_map_hd with (a := []). 2: {
  intros H; apply Hraz; unfold mat_nrows.
  now rewrite H.
}
rewrite map_length.
rewrite fold_mat_ncols.
rewrite rngl_mul_summation_distr_l; [ | now left ].
apply rngl_summation_eq_compat.
intros k Hk.
rewrite List_map_nth' with (a := []). 2: {
  rewrite fold_mat_nrows.
  now apply in_seq in Hi.
}
rewrite List_map_nth' with (a := 0%F). 2: {
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
  is_correct_matrix MB
  → mat_ncols MA ≠ 0
  → mat_ncols MA = mat_nrows MB
  → (MA * (a × MB) = a × (MA * MB))%M.
Proof.
intros Hic * Hb Hcaz Hcarb.
apply Nat.neq_0_lt_0 in Hcaz.
unfold "*"%M, "×"%M; cbn.
f_equal.
rewrite map_map.
apply map_ext_in.
intros i Hi.
unfold mat_ncols at 1; cbn.
rewrite List_map_hd with (a := []). 2: {
  intros H; unfold mat_nrows in Hcarb.
  rewrite H in Hcarb.
  now rewrite Hcarb in Hcaz.
}
rewrite map_length.
rewrite fold_mat_ncols.
rewrite map_map.
apply map_ext_in.
intros j Hj.
unfold mat_mul_el; cbn.
rewrite rngl_mul_summation_distr_l; [ | now left ].
apply rngl_summation_eq_compat.
intros k Hk.
rewrite List_map_nth' with (a := []). 2: {
  rewrite fold_mat_nrows, <- Hcarb.
  flia Hcaz Hk.
}
rewrite List_map_nth' with (a := 0%F). 2: {
  destruct Hb as (Hbzz, Hb).
  rewrite Hb; [ now apply in_seq in Hj | ].
  apply nth_In.
  rewrite fold_mat_nrows, <- Hcarb.
  flia Hcaz Hk.
}
rewrite fold_mat_el.
rewrite rngl_mul_comm; [ | easy ].
rewrite <- rngl_mul_assoc.
f_equal.
now apply rngl_mul_comm.
Qed.

Theorem mat_mul_scal_l_add_distr_l : ∀ a (MA MB : matrix T),
  (a × (MA + MB) = (a × MA + a × MB))%M.
Proof.
intros.
unfold "+"%M, "×"%M; cbn.
f_equal.
rewrite map2_map_l, map2_map_r, map_map2.
apply map2_ext_in.
rename a into c.
intros la lb Hla Hlb.
rewrite map2_map_l, map2_map_r, map_map2.
apply map2_ext_in.
intros a b Ha Hb.
apply rngl_mul_add_distr_l.
Qed.

(* associativity with multiplication with vector *)

Theorem mat_vect_mul_assoc_as_sums :
  ∀ (A : matrix T) (B : matrix T) (V : vector T) i,
  i < mat_nrows A
  → ∑ (j = 0, mat_ncols A - 1),
       mat_el A i j *
       (∑ (k = 0, vect_size V - 1), mat_el B j k * vect_el V k) =
     ∑ (j = 0, vect_size V - 1),
       (∑ (k = 0, mat_ncols A - 1), mat_el A i k * mat_el B k j) *
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
rewrite rngl_summation_summation_exch'.
apply rngl_summation_eq_compat.
intros j Hj.
apply rngl_summation_eq_compat.
intros k Hk.
apply rngl_mul_assoc.
Qed.

Theorem mat_vect_mul_assoc :
  ∀ (A : matrix T) (B : matrix T) (V : vector T),
  is_correct_matrix A
  → is_correct_matrix B
  → mat_ncols A = mat_nrows B
  → mat_ncols B = vect_size V
  → (A • (B • V) = (A * B) • V)%M.
Proof.
intros * Ha Hb Hcarb Hcbv.
unfold "•"%M, "*"%M; cbn.
unfold vect_dot_mul; cbn.
f_equal.
rewrite map_map.
rewrite List_map_map_seq with (d := []).
apply map_ext_in.
intros i Hi.
rewrite map2_map_r.
rewrite map2_map2_seq_l with (d := 0%F).
rewrite map2_map2_seq_r with (d := []).
destruct Ha as (Harc, Ha).
rewrite Ha. 2: {
  apply nth_In.
  rewrite fold_mat_nrows.
  now apply in_seq in Hi.
}
rewrite fold_mat_nrows.
symmetry.
rewrite map2_map2_seq_r with (d := 0%F).
rewrite fold_vect_size.
symmetry.
rewrite <- Hcarb.
rewrite map2_diag.
rewrite rngl_summation_map_seq.
rewrite rngl_summation_seq_summation. 2: {
  intros H; apply Harc in H.
  now rewrite H in Hi.
}
cbn.
destruct Hb as (Hbrc, Hb).
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite fold_mat_el.
  rewrite map2_map2_seq_l with (d := 0%F).
  rewrite Hb with (l := nth j (mat_list_list B) []). 2: {
    apply nth_In.
    rewrite fold_mat_nrows.
    rewrite <- Hcarb.
    destruct Hj as (_, Hj).
    apply Nat.lt_succ_r in Hj.
    rewrite <- Nat.sub_succ_l in Hj. 2: {
      apply Nat.le_succ_l.
      apply Nat.neq_0_lt_0.
      intros H.
      apply Harc in H.
      now rewrite H in Hi.
    }
    now rewrite Nat.sub_succ, Nat.sub_0_r in Hj.
  }
  rewrite map2_map2_seq_r with (d := 0%F).
  rewrite fold_vect_size.
  rewrite Hcbv.
  rewrite map2_diag.
  rewrite rngl_summation_map_seq.
  rewrite rngl_summation_seq_summation. 2: {
    intros H; rewrite <- Hcbv in H.
    apply Hbrc in H.
    rewrite <- Hcarb in H.
    apply Harc in H.
    now rewrite H in Hi.
  }
  erewrite rngl_summation_eq_compat. 2: {
    intros k Hk.
    now rewrite fold_mat_el.
  }
  easy.
}
cbn.
rewrite Hcbv.
rewrite map2_map_l.
rewrite map2_diag.
rewrite rngl_summation_map_seq.
rewrite rngl_summation_seq_summation. 2: {
  intros H; rewrite <- Hcbv in H.
  apply Hbrc in H.
  rewrite <- Hcarb in H.
  apply Harc in H.
  now rewrite H in Hi.
}
apply in_seq in Hi.
now apply mat_vect_mul_assoc_as_sums.
Qed.

Theorem mat_mul_scal_vect_assoc :
  ∀ a (MA : matrix T) (V : vector T),
  is_correct_matrix MA
  → mat_ncols MA = vect_size V
  → (a × (MA • V))%V = ((a × MA) • V)%M.
Proof.
intros * Ha Hcav.
unfold "×"%V, "×"%M, "•"%V; cbn.
f_equal.
do 2 rewrite map_map.
rewrite List_map_map_seq with (d := []).
rewrite fold_mat_nrows.
rewrite List_map_map_seq with (d := []).
rewrite fold_mat_nrows.
apply map_ext_in.
intros i Hi.
unfold vect_dot_mul; cbn.
rewrite map2_map_l.
rewrite rngl_mul_summation_list_distr_l; [ | now left ].
rewrite map2_map2_seq_l with (d := 0%F).
destruct Ha as (Harc, Ha).
rewrite Ha. 2: {
  apply nth_In.
  rewrite fold_mat_nrows.
  now apply in_seq in Hi.
}
rewrite map2_map2_seq_r with (d := 0%F).
rewrite fold_vect_size, Hcav.
rewrite map2_diag.
rewrite rngl_summation_map_seq.
rewrite rngl_summation_seq_summation. 2: {
  rewrite <- Hcav; intros H.
  apply Harc in H.
  now rewrite H in Hi.
}
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite fold_mat_el.
  now rewrite fold_vect_el.
}
rewrite map2_map2_seq_l with (d := 0%F).
rewrite Ha. 2: {
  apply nth_In.
  rewrite fold_mat_nrows.
  now apply in_seq in Hi.
}
rewrite map2_map2_seq_r with (d := 0%F).
rewrite fold_vect_size, Hcav.
rewrite map2_diag.
rewrite rngl_summation_map_seq.
rewrite rngl_summation_seq_summation. 2: {
  rewrite <- Hcav; intros H.
  apply Harc in H.
  now rewrite H in Hi.
}
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite fold_mat_el.
  now rewrite fold_vect_el.
}
symmetry.
apply rngl_summation_eq_compat.
intros j Hj.
apply rngl_mul_assoc.
Qed.

Theorem mat_mul_scal_vect_comm :
  rngl_is_comm = true →
  ∀ a (MA : matrix T) V,
  is_correct_matrix MA
  → mat_ncols MA = vect_size V
  → (a × (MA • V) = MA • (a × V))%V.
Proof.
intros Hic * Ha Hcav.
unfold "×"%V, "•"%M; cbn.
f_equal.
rewrite map_map.
do 2 rewrite List_map_map_seq with (d := []).
rewrite fold_mat_nrows.
apply map_ext_in.
intros i Hi.
unfold vect_dot_mul; cbn.
rewrite rngl_mul_summation_list_distr_l; [ | now left ].
rewrite map2_map_r.
rewrite map2_map2_seq_l with (d := 0%F).
rewrite map2_map2_seq_r with (d := 0%F).
rewrite fold_vect_size.
destruct Ha as (Harc, Ha).
rewrite Ha. 2: {
  apply nth_In.
  rewrite fold_mat_nrows.
  now apply in_seq in Hi.
}
symmetry.
rewrite map2_map2_seq_l with (d := 0%F).
rewrite map2_map2_seq_r with (d := 0%F).
rewrite fold_vect_size.
rewrite Ha. 2: {
  apply nth_In.
  rewrite fold_mat_nrows.
  now apply in_seq in Hi.
}
rewrite Hcav.
do 2 rewrite map2_diag.
do 2 rewrite rngl_summation_map_seq.
assert (Hvz : vect_size V ≠ 0). {
  intros H; rewrite <- Hcav in H.
  apply Harc in H.
  now rewrite H in Hi.
}
rewrite rngl_summation_seq_summation; [ | easy ].
rewrite rngl_summation_seq_summation; [ | easy ].
apply rngl_summation_eq_compat.
intros j Hj.
rewrite fold_mat_el, fold_vect_el.
do 2 rewrite rngl_mul_assoc.
f_equal.
now apply rngl_mul_comm.
Qed.

(* matrix transpose *)

Definition mat_transp (M : matrix T) : matrix T :=
  mk_mat
    (map (λ j, map (λ i, mat_el M i j) (seq 0 (mat_nrows M)))
       (seq 0 (mat_ncols M))).

(*
End a.
Require Import Nrl.
Compute (mat_transp nat_ring_like_op (mk_mat [[3;2];[5;1];[8;9]])).
Compute (mat_transp nat_ring_like_op (mk_mat [[3;5;8];[2;1;9];[10;11;12]])).
*)

(* matrix without row i and column j *)

Definition subm (M : matrix T) i j :=
  mk_mat (map (butn j) (butn i (mat_list_list M))).

(*
End a.
Compute subm (mk_mat [[3;5;8];[2;1;9];[10;11;12]]) 0 0.
Compute subm (mk_mat [[3;5;8];[2;1;9];[10;11;12]]) 0 1.
Compute subm (mk_mat [[3;5;8];[2;1;9];[10;11;12]]) 0 2.
Compute subm (mk_mat [[3;5;8];[2;1;9];[10;11;12]]) 1 0.
Compute subm (mk_mat [[3;5;8];[2;1;9];[10;11;12]]) 1 1.
Compute subm (mk_mat [[3;5;8];[2;1;9];[10;11;12]]) 1 2.
*)

(* alternative definition *)
Definition subm' (M : matrix T) u v :=
  mk_mat
    (map
       (λ i,
          map
            (λ j, mat_el M (i + Nat.b2n (u <=? i)) (j + Nat.b2n (v <=? j)))
            (seq 0 (mat_ncols M - 1)))
       (seq 0 (mat_nrows M - 1))).

(* equivalence between subm and subm' *)

Theorem subm_subm' : ∀ (M : matrix T) i j, subm M i j = subm' M i j.
Proof.
intros.
unfold subm, subm'.
f_equal.
rewrite (List_eq_map_seq (mat_list_list M) []) at 1.
rewrite fold_mat_nrows.
rewrite map_butn.
rewrite map_map.
rewrite <- map_butn.
erewrite map_ext_in. 2: {
  intros u Hu.
  rewrite (List_eq_map_seq (nth u (mat_list_list M) []) 0%F).
  rewrite <- map_butn.
  erewrite map_ext_in. 2: {
    intros v Hv.
    now rewrite fold_mat_el.
  }
  easy.
}
Search (map _ (butn _ _)).
Theorem map_butn_seq : ∀ A (f : _ → A) n sta len,
  sta ≤ n < sta + len
  → map f (butn n (seq sta len)) =
    map (λ i, if lt_dec i n then f (i - 1) else f i) (seq (sta + 1) len).
Proof.
intros * Hn.
revert n sta Hn.
induction len; intros; [ now rewrite butn_nil | ].
destruct n. {
  cbn.
  destruct Hn as (Hs, _).
  apply Nat.le_0_r in Hs; subst sta.
  cbn.
  destruct len.
  cbn.
...
  symmetry.
  rewrite <- seq_shift.
  rewrite map_map.
  rewrite Nat.add_1_r.
Search (seq (S _)).
rewrite cons_seq.

  rewrite <- cons_seq.
Search (butn _ (_ :: _)).
  cbn.
Search (seq (S _)).
...
rewrite seq_S.

rewrite Nat.add_1_r.
rewrite <- seq_shift, map_map.
revert sta.
induction len; intros; cbn. {
  destruct n; [ easy | cbn ].
...
rewrite map_butn_seq.
...
unfold mat_ncols; cbn.
(*
*)
rewrite <- map_butn.
(*
rewrite map_seq_length.
*)
symmetry.
erewrite map_ext_in. 2: {
  intros u Hu.
  apply in_seq in Hu.
  rewrite List_hd_nth_0.
...
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length.
    unfold Nat.b2n.
    rewrite if_leb_le_dec.
    destruct (le_dec i u); flia Hu.
  }
  rewrite seq_nth. 2: {
    unfold Nat.b2n.
    rewrite if_leb_le_dec.
    destruct (le_dec i u); flia Hu.
  }
  rewrite Nat.add_0_l.
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length.
    flia Hu.
  }
  rewrite seq_nth; [ | flia Hu ].
  cbn.
  rewrite <- List_hd_nth_0.
  easy.
}
symmetry.
Print subm'.
...
unfold mat_ncols; cbn.
induction ll as [| la]; [ now rewrite butn_nil | ].
destruct i. {
  cbn.
...

(* combinations of submatrix and other operations *)

Theorem mat_el_subm : ∀ (M : matrix T) i j u v,
  is_correct_matrix M
  → u ≤ mat_nrows M
  → v ≤ mat_ncols M
  → i < mat_nrows M - 1
  → j < mat_ncols M - 1
  → mat_el (subm M u v) i j =
      mat_el M (i + Nat.b2n (u <=? i)) (j + Nat.b2n (v <=? j)).
Proof.
intros * Hcm Hu Hv Hi Hj.
unfold Nat.b2n.
do 2 rewrite if_leb_le_dec.
unfold mat_el, subm; cbn.
unfold butn.
rewrite map_app.
destruct (le_dec u i) as [Hui| Hui]. {
  rewrite app_nth2. 2: {
    rewrite map_length, firstn_length, fold_mat_nrows.
    unfold ge.
    rewrite Nat.min_l; [ easy | flia Hi Hui ].
  }
  rewrite map_length, firstn_length.
  rewrite fold_mat_nrows.
  rewrite Nat.min_l; [ | flia Hi Hui ].
  rewrite <- skipn_map.
  rewrite List_nth_skipn.
  replace (i - u + S u) with (i + 1) by flia Hui.
  rewrite (List_map_nth' []). 2: {
    rewrite fold_mat_nrows.
    flia Hi.
  }
  destruct (le_dec v j) as [Hvj| Hvj]. {
    rewrite app_nth2; [ | rewrite firstn_length; flia Hvj ].
    rewrite firstn_length.
    rewrite Nat.min_l. 2: {
      rewrite fold_corr_mat_ncols; [ easy | easy | flia Hi ].
    }
    rewrite List_nth_skipn.
    now replace (j - v + S v) with (j + 1) by flia Hvj.
  } {
    rewrite Nat.add_0_r.
    apply Nat.nle_gt in Hvj.
    rewrite app_nth1. 2: {
      rewrite firstn_length.
      rewrite fold_corr_mat_ncols; [ | easy | flia Hi ].
      now rewrite Nat.min_l.
    }
    now rewrite List_nth_firstn.
  }
} {
  rewrite Nat.add_0_r.
  apply Nat.nle_gt in Hui.
  rewrite app_nth1. 2: {
    rewrite map_length, firstn_length, fold_mat_nrows.
    now rewrite Nat.min_l.
  }
  rewrite (List_map_nth' []). 2: {
    rewrite firstn_length, fold_mat_nrows.
    now rewrite Nat.min_l.
  }
  rewrite List_nth_firstn; [ | easy ].
  destruct (le_dec v j) as [Hvj| Hvj]. {
    rewrite app_nth2; [ | rewrite firstn_length; flia Hvj ].
    rewrite firstn_length.
    rewrite fold_corr_mat_ncols; [ | easy | flia Hi ].
    rewrite Nat.min_l; [ | easy ].
    rewrite List_nth_skipn.
    now replace (j - v + S v) with (j + 1) by flia Hvj.
  } {
    rewrite Nat.add_0_r.
    apply Nat.nle_gt in Hvj.
    rewrite app_nth1. 2: {
      rewrite firstn_length.
      rewrite fold_corr_mat_ncols; [ | easy | flia Hi ].
      now rewrite Nat.min_l.
    }
    now rewrite List_nth_firstn.
  }
}
Qed.

Theorem mat_nrows_subm : ∀ (M : matrix T) i j,
  i < mat_nrows M
  → mat_nrows (subm M i j) = mat_nrows M - 1.
Proof.
intros * Hir.
destruct M as (ll); cbn.
rewrite map_length.
cbn in Hir.
now apply butn_length.
Qed.

Theorem mat_ncols_subm : ∀ (M : matrix T) i j,
  is_correct_matrix M
  → 1 < mat_nrows M
  → j < mat_ncols M
  → mat_ncols (subm M i j) = mat_ncols M - 1.
Proof.
intros * Hcm H1r Hic.
destruct (le_dec (mat_ncols M) 1) as [H1c| H1c]. {
  destruct (Nat.eq_dec (mat_ncols M) 0) as [H| H]; [ flia Hic H | ].
  assert (Hc1 : mat_ncols M = 1) by flia H1c H; clear H1c H.
  rewrite Hc1 in Hic |-*.
  apply Nat.lt_1_r in Hic; subst j.
  unfold mat_ncols, subm; cbn.
  unfold mat_ncols in Hc1.
  destruct M as (ll).
  cbn in Hc1 |-*.
  destruct ll as [| la1]; [ easy | ].
  cbn in H1r, Hc1 |-*.
  apply Nat.succ_lt_mono in H1r.
  destruct ll as [| la2]; [ easy | ].
  destruct i. {
    cbn.
    destruct la2 as [| a2]; [ easy | ].
    destruct Hcm as (Hcr, Hc).
    cbn in Hc.
    specialize (Hc (a2 :: la2) (or_intror (or_introl eq_refl))).
    rewrite Hc1 in Hc; cbn in Hc.
    now apply Nat.succ_inj in Hc.
  }
  cbn.
  destruct la1 as [| a1]; [ easy | cbn in Hc1 ].
  now apply Nat.succ_inj in Hc1.
}
apply Nat.nle_gt in H1c.
unfold mat_ncols in H1c, Hic |-*.
destruct M as (ll); cbn in *.
destruct ll as [| l]; [ easy | ].
destruct ll as [| l']; [ cbn in H1r; flia H1r | ].
clear H1r.
cbn in H1c, Hic.
destruct Hcm as (Hcr, Hcm).
cbn in Hcr |-*.
unfold mat_ncols in Hcm; cbn in Hcm.
destruct i. {
  specialize (Hcm l' (or_intror (or_introl eq_refl))) as H1.
  now cbn; rewrite butn_length; rewrite H1.
}
now cbn; rewrite butn_length.
Qed.

Theorem is_squ_mat_subm : ∀ n (M : matrix T) i j,
  n ≠ 0
  → i ≤ n
  → j ≤ n
  → is_square_matrix (S n) M = true
  → is_square_matrix n (subm M i j) = true.
Proof.
intros * Hnz Hi Hj Hm.
apply is_sm_mat_iff.
specialize (square_matrix_ncols _ Hm) as Hcm.
split. {
  apply is_sm_mat_iff in Hm.
  destruct Hm as (Hr & Hcr & Hc).
  rewrite mat_nrows_subm; [ | flia Hr Hi ].
  now rewrite Hr, Nat.sub_succ, Nat.sub_0_r.
}
split. {
  intros Hcs.
  rewrite mat_ncols_subm in Hcs; cycle 1. {
    now apply (@squ_mat_is_corr (S n)).
  } {
    apply is_sm_mat_iff in Hm.
    destruct Hm as (Hr & Hcr & Hc).
    rewrite Hr; flia Hnz.
  } {
    rewrite Hcm; flia Hj.
  }
  rewrite Hcm in Hcs; flia Hnz Hcs.
} {
  intros l Hl.
  apply is_sm_mat_iff in Hm.
  destruct Hm as (Hr & Hcr & Hc).
  clear Hcr Hr Hcm Hnz.
  destruct M as (ll).
  cbn in Hc.
  cbn - [ butn ] in Hl.
  revert ll Hc Hl.
  induction i; intros. {
    apply in_map_iff in Hl.
    destruct Hl as (la & Hl & Hla); subst l.
    cbn in Hla, Hc.
    destruct ll as [| l']; [ easy | ].
    rewrite butn_length. {
      rewrite Hc; [ flia | now right ].
    }
    rewrite Hc; [ flia Hj | now right ].
  }
  destruct ll as [| l']; [ easy | ].
  rewrite butn_cons in Hl.
  cbn in Hl.
  destruct Hl as [Hl| Hl]. {
    subst l.
    rewrite butn_length. {
      rewrite Hc; [ flia | now left ].
    }
    rewrite Hc; [ flia Hj | now left ].
  }
  apply IHi with (ll := ll); [ flia Hi | | easy ].
  intros l'' Hl''.
  now apply Hc; right.
}
Qed.

Theorem subm_is_corr_mat : ∀ (A : matrix T) i j,
  mat_ncols A ≠ 1
  → is_correct_matrix A
  → is_correct_matrix (subm A i j).
Proof.
intros * Hc1 Ha.
split. {
  destruct (lt_dec i (mat_nrows A)) as [Hir| Hir]. {
    rewrite mat_nrows_subm; [ | easy ].
    destruct (lt_dec j (mat_ncols A)) as [Hjc| Hjc]. {
      destruct (lt_dec 1 (mat_nrows A)) as [H1r| H1r]. {
        rewrite mat_ncols_subm; [ | easy | easy | easy ].
        destruct Ha as (Hcr, Hc).
        destruct (Nat.eq_dec (mat_ncols A) 0) as [Hcz| Hcz]. {
          flia Hjc Hcz.
        }
        intros H; flia Hc1 Hcz H.
      }
      apply Nat.nlt_ge in H1r.
      flia H1r Hir.
    }
    apply Nat.nlt_ge in Hjc.
    unfold mat_ncols, subm; cbn.
    rewrite map_butn_out. 2: {
      intros la Hla.
      destruct Ha as (Hcr, Hc).
      rewrite Hc; [ easy | ].
      now apply in_butn in Hla.
    }
    rewrite List_hd_nth_0.
    destruct A as (ll).
    destruct ll as [| la]; [ easy | ].
    destruct Ha as (Hcr, Hc).
    cbn in *.
    destruct i. {
      destruct ll as [| lb]; [ easy | cbn ].
      intros H; exfalso.
      rewrite Hc in H; [ | now right; left ].
      now specialize (Hcr H).
    }
    rewrite Hc; [ now intros H; specialize (Hcr H) | ].
    now left.
  }
  apply Nat.nlt_ge in Hir.
  unfold mat_nrows; cbn.
  rewrite map_length.
  rewrite butn_out; [ | easy ].
  rewrite fold_mat_nrows.
  unfold mat_ncols; cbn.
  rewrite butn_out; [ | easy ].
  destruct Ha as (Hcr, Hc).
  intros H1.
  destruct (lt_dec j (mat_ncols A)) as [Hjc| Hjc]. 2: {
    apply Nat.nlt_ge in Hjc.
    rewrite map_butn_out in H1. 2: {
      intros l Hl.
      now rewrite Hc.
    }
    now apply Hcr.
  }
  apply length_zero_iff_nil in H1.
  destruct A as (ll); cbn in *.
  destruct ll as [| la]; [ easy | exfalso ].
  cbn in *.
  destruct la as [| a]; [ easy | ].
  destruct la as [| b]; [ easy | ].
  clear Hc1; cbn in *.
  now destruct j.
} {
  intros l Hl.
  destruct (le_dec (mat_nrows A) 1) as [H1r| H1r]. {
    apply Nat.le_1_r in H1r.
    destruct H1r as [H1r| H1r]. {
      unfold mat_nrows in H1r.
      apply length_zero_iff_nil in H1r.
      unfold subm in Hl; cbn in Hl.
      rewrite H1r in Hl.
      now rewrite butn_nil in Hl.
    }
    unfold mat_nrows in H1r.
    destruct A as (ll); cbn in *.
    destruct ll as [| la]; [ easy | ].
    destruct ll; [ clear H1r | easy ].
    cbn in Hc1.
    unfold subm, mat_ncols; cbn.
    destruct i; [ easy | cbn ].
    rewrite butn_cons in Hl.
    cbn in Hl.
    destruct Hl as [Hl| Hl]; [ now subst l | ].
    now rewrite butn_nil in Hl.
  }
  apply Nat.nle_gt in H1r.
  unfold subm in Hl; cbn in Hl.
  apply in_map_iff in Hl.
  destruct Hl as (la & Hl & Hla).
  subst l.
  destruct Ha as (Hcr, Hc).
  specialize (in_butn _ _ _ Hla) as H.
  specialize (Hc _ H) as H1; clear H.
  destruct (lt_dec j (mat_ncols A)) as [Hjc| Hjc]. {
    rewrite mat_ncols_subm; [ | easy | easy | easy ].
    rewrite butn_length; [ | congruence ].
    now rewrite H1.
  }
  apply Nat.nlt_ge in Hjc.
  unfold butn.
  rewrite app_length.
  rewrite firstn_length, skipn_length.
  rewrite H1.
  rewrite Nat.min_r; [ | easy ].
  rewrite (proj2 (Nat.sub_0_le (mat_ncols A) (S j))); [ | flia Hjc ].
  rewrite Nat.add_0_r.
  unfold mat_ncols; cbn.
  symmetry.
  rewrite Hc; [ easy | ].
  rewrite map_butn_out. 2: {
    intros lb Hlb.
    rewrite Hc; [ easy | ].
    now apply in_butn in Hlb.
  }
  rewrite List_hd_nth_0.
  destruct (Nat.eq_dec i 0) as [Hiz| Hiz]. {
    rewrite nth_butn_before; [ cbn | flia Hiz ].
    now apply nth_In.
  } {
    rewrite nth_butn_after; [ cbn | flia Hiz ].
    apply nth_In; rewrite fold_mat_nrows; flia H1r.
  }
}
Qed.

Theorem submatrix_sub : ∀ (MA MB : matrix T) i j,
  subm (MA - MB)%M i j = (subm MA i j - subm MB i j)%M.
Proof.
intros.
unfold subm, mat_sub, "+"%M, mat_opp; cbn.
f_equal.
rewrite map2_map_l.
do 3 rewrite map2_map_r.
rewrite map_butn, map2_butn.
f_equal; clear i.
rewrite map_map2.
apply map2_ext_in.
intros la lb Hla Hlb.
rewrite map2_map_r.
rewrite map_butn.
rewrite map2_butn.
f_equal.
now rewrite map2_map_r.
Qed.

Theorem submatrix_mul_scal_l : ∀ (μ : T) (M : matrix T) i j,
  subm (μ × M)%M i j = (μ × subm M i j)%M.
Proof.
intros.
unfold subm, "×"%M; cbn.
f_equal.
do 3 rewrite map_butn.
do 2 rewrite map_map.
f_equal; clear i.
apply map_ext_in.
intros la Hla.
symmetry.
apply map_butn.
Qed.

Theorem submatrix_mI : ∀ i n, i < n → subm (mI n) i i = mI (n - 1).
Proof.
intros * Hnr.
unfold subm, mI; cbn.
f_equal.
destruct n; [ easy | ].
rewrite Nat.sub_succ, Nat.sub_0_r.
rewrite <- map_butn.
rewrite map_map.
erewrite map_ext_in. 2: {
  intros j Hj.
  now rewrite <- map_butn.
}
unfold butn at 2.
rewrite List_firstn_seq.
rewrite Nat.min_l; [ | flia Hnr ].
rewrite List_skipn_seq; [ | easy ].
cbn - [ seq ].
replace n with (i + (n - i)) at 2 by flia Hnr.
rewrite seq_app.
cbn - [ seq ].
do 2 rewrite map_app.
unfold butn.
rewrite List_firstn_seq.
rewrite Nat.min_l; [ | flia Hnr ].
rewrite List_skipn_seq; [ cbn | easy ].
rewrite <- seq_shift.
rewrite map_map.
f_equal. {
  apply map_ext_in.
  intros j Hj.
  replace n with (i + (n - i)) at 2 by flia Hnr.
  rewrite seq_app.
  do 2 rewrite map_app.
  f_equal; cbn.
  rewrite map_map.
  apply map_ext_in.
  intros k Hk.
  apply in_seq in Hj.
  apply in_seq in Hk.
  unfold δ.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec j (S k)) as [H| H]; [ flia Hj Hk H | clear H ].
  destruct (Nat.eq_dec j k) as [H| H]; [ flia Hj Hk H | easy ].
} {
  apply map_ext_in.
  intros j Hj.
  replace n with (i + (n - i)) at 2 by flia Hnr.
  rewrite seq_app.
  do 2 rewrite map_app; cbn.
  f_equal; [ | now rewrite map_map ].
  apply map_ext_in.
  intros k Hk.
  apply in_seq in Hj.
  apply in_seq in Hk.
  unfold δ.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (S j) k) as [H| H]; [ flia Hj Hk H | clear H ].
  destruct (Nat.eq_dec j k) as [H| H]; [ flia Hj Hk H | easy ].
}
Qed.

Theorem mat_mul_scal_1_l : ∀ (M : matrix T), (1 × M = M)%M.
Proof.
intros.
unfold "×"%M.
destruct M as (ll).
f_equal; cbn.
induction ll as [| la]; [ easy | cbn ].
rewrite IHll; f_equal.
induction la as [| a]; [ easy | cbn ].
now rewrite rngl_mul_1_l, IHla.
Qed.

(* ring of square matrices *)

Theorem squ_mat_nrows : ∀ n (M : square_matrix n T),
  mat_nrows (sm_mat M) = n.
Proof.
intros.
destruct M as (M & Hmp); cbn.
now apply is_sm_mat_iff in Hmp.
Qed.

Theorem squ_mat_ncols : ∀ n (M : square_matrix n T),
  mat_ncols (sm_mat M) = n.
Proof.
intros.
destruct M as (M, Hmp); cbn.
apply is_sm_mat_iff in Hmp.
destruct Hmp as (Hr, Hc).
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  unfold mat_ncols.
  unfold mat_nrows in Hr.
  apply length_zero_iff_nil in Hr.
  now rewrite Hr.
}
unfold mat_ncols.
apply Hc.
rewrite List_hd_nth_0.
apply nth_In.
unfold mat_nrows in Hr.
rewrite Hr.
now apply Nat.neq_0_lt_0.
Qed.

Theorem mZ_is_square_matrix : ∀ n, is_square_matrix n (mZ n n) = true.
Proof.
intros.
apply is_sm_mat_iff.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  now subst n; cbn.
}
split; [ now cbn; rewrite repeat_length | ].
split; [ now rewrite mZ_nrows, mZ_ncols | ].
intros la Hla.
cbn in Hla.
apply repeat_spec in Hla; subst la.
apply repeat_length.
Qed.

Definition smZ n : square_matrix n T :=
  {| sm_mat := mZ n n;
     sm_prop := mZ_is_square_matrix n |}.

Theorem mI_is_square_matrix : ∀ n, is_square_matrix n (mI n) = true.
Proof.
intros.
apply is_sm_mat_iff.
split; [ now cbn; rewrite map_seq_length | ].
rewrite mI_nrows, mI_ncols.
split; [ easy | ].
intros la Hla.
cbn in Hla.
apply in_map_iff in Hla.
destruct Hla as (i & Hin & Hi).
subst la.
now rewrite map_seq_length.
Qed.

Theorem mI_is_correct_matrix : ∀ n, is_correct_matrix (mI n).
Proof.
intros.
apply is_sm_mat_iff.
rewrite mI_ncols.
apply mI_is_square_matrix.
Qed.

Theorem mZ_is_correct_matrix : ∀ m n,
  n ≠ 0
  → is_correct_matrix (mZ m n).
Proof.
intros * Hnz.
destruct (Nat.eq_dec m 0) as [Hmz| Hmz]; [ now subst m | ].
split. {
  intros Hc.
  now rewrite mZ_ncols in Hc.
}
intros l Hl.
rewrite mZ_ncols; [ | easy ].
cbn in Hl.
apply repeat_spec in Hl.
subst l.
apply repeat_length.
Qed.

Theorem mat_opp_is_correct : ∀ M,
  is_correct_matrix M
  → is_correct_matrix (- M).
Proof.
intros * Hm.
destruct Hm as (Hcr, Hc).
destruct (Nat.eq_dec (mat_nrows M) 0) as [Hrz| Hrz]. {
  apply eq_mat_nrows_0 in Hrz.
  unfold is_correct_matrix.
  unfold mat_ncols, mat_nrows; cbn.
  now rewrite Hrz; cbn.
}
apply Nat.neq_0_lt_0 in Hrz.
unfold is_correct_matrix.
unfold mat_ncols, mat_nrows; cbn.
rewrite List_hd_nth_0.
rewrite (List_map_nth' []); [ | easy ].
do 2 rewrite map_length.
rewrite <- List_hd_nth_0.
rewrite fold_mat_nrows, fold_mat_ncols.
split; [ easy | ].
intros la Hla.
apply in_map_iff in Hla.
destruct Hla as (lb & Hla & Hlb); subst la.
rewrite map_length.
now apply Hc.
Qed.

Definition smI n : square_matrix n T :=
  {| sm_mat := mI n;
     sm_prop := mI_is_square_matrix n |}.

Theorem squ_mat_add_is_squ : ∀ n (MA MB : matrix T),
  is_square_matrix n MA = true
  → is_square_matrix n MB = true
  → is_square_matrix n (MA + MB) = true.
Proof.
intros * Ha Hb.
apply is_sm_mat_iff; cbn.
apply is_sm_mat_iff in Ha.
apply is_sm_mat_iff in Hb.
destruct Ha as (Hra & Hcra & Hca).
destruct Hb as (Hrb & Hcrb & Hcb).
split. {
  rewrite map2_length.
  do 2 rewrite fold_mat_nrows.
  rewrite Hra, Hrb.
  apply Nat.min_id.
}
split. {
  intros Hc.
  rewrite map2_length.
  do 2 rewrite fold_mat_nrows.
  rewrite Hra, Hrb, Nat.min_id.
  unfold mat_ncols in Hc; cbn in Hc.
  apply length_zero_iff_nil in Hc.
  rewrite List_hd_nth_0 in Hc.
  destruct n; [ easy | exfalso ].
  rewrite map2_nth with (a := []) (b := []) in Hc; cycle 1. {
    rewrite fold_mat_nrows, Hra; flia.
  } {
    rewrite fold_mat_nrows, Hrb; flia.
  }
  apply map2_eq_nil in Hc.
  do 2 rewrite <- List_hd_nth_0 in Hc.
  destruct Hc as [Hc| Hc]. {
    apply (f_equal length) in Hc; cbn in Hc.
    rewrite fold_mat_ncols in Hc.
    apply Hcra in Hc.
    flia Hra Hc.
  } {
    apply (f_equal length) in Hc; cbn in Hc.
    rewrite fold_mat_ncols in Hc.
    apply Hcrb in Hc.
    flia Hrb Hc.
  }
} {
  intros l Hl.
  apply in_map2_iff in Hl.
  destruct Hl as (i & Him & a & b & Hl).
  subst l.
  rewrite map2_length.
  cbn in Him |-*.
  do 2 rewrite fold_mat_nrows in Him.
  rewrite Hra, Hrb in Him.
  rewrite Nat.min_id in Him.
  rewrite Hca; [ | now apply nth_In; rewrite fold_mat_nrows, Hra ].
  rewrite Hcb; [ | now apply nth_In; rewrite fold_mat_nrows, Hrb ].
  apply Nat.min_id.
}
Qed.

Theorem square_matrix_add_is_square : ∀ n (MA MB : square_matrix n T),
  is_square_matrix n (sm_mat MA + sm_mat MB)%M = true.
Proof.
intros.
destruct MA as (MA & Ha).
destruct MB as (MB & Hb).
now apply squ_mat_add_is_squ.
Qed.

Theorem squ_mat_mul_scal_l_is_squ : ∀ n (M : matrix T) μ,
  is_square_matrix n M = true
  → is_square_matrix n (μ × M) = true.
Proof.
intros * Hm.
apply is_sm_mat_iff in Hm.
apply is_sm_mat_iff.
destruct Hm as (Hr & Hcr & Hc).
cbn; rewrite map_length, fold_mat_nrows.
split; [ easy | ].
split. {
  intros H1.
  destruct (Nat.eq_dec (mat_nrows M) 0) as [Hrz| Hrz]; [ easy | ].
  apply Nat.neq_0_lt_0 in Hrz.
  apply Hcr.
  unfold mat_ncols in H1 |-*; cbn in H1 |-*.
  rewrite List_hd_nth_0 in H1 |-*.
  rewrite (List_map_nth' []) in H1; [ | easy ].
  now rewrite map_length in H1.
}
intros la Hla.
apply in_map_iff in Hla.
destruct Hla as (lb & Hla & Hi); subst la.
rewrite map_length.
now apply Hc.
Qed.

Definition square_matrix_add {n} (MA MB : square_matrix n T) :
  square_matrix n T :=
  {| sm_mat := (sm_mat MA + sm_mat MB)%M;
     sm_prop := square_matrix_add_is_square MA MB |}.

Theorem square_matrix_mul_is_square : ∀ n (MA MB : square_matrix n T),
  is_square_matrix n (sm_mat MA * sm_mat MB)%M = true.
Proof.
intros.
apply is_sm_mat_iff.
split; cbn. {
  rewrite map_seq_length.
  apply squ_mat_nrows.
}
split. {
  intros Hc.
  rewrite map_seq_length.
  destruct MA as (MA & Ha).
  destruct MB as (MB & Hb).
  move MB before MA; cbn in Hc |-*.
  apply is_sm_mat_iff in Ha.
  apply is_sm_mat_iff in Hb.
  destruct Ha as (Hra & Hcra & Hca).
  destruct Hb as (Hrb & Hcrb & Hcb).
  move Hrb before Hra.
  move Hcrb before Hcra.
  unfold mat_ncols in Hc; cbn in Hc.
  apply length_zero_iff_nil in Hc.
  rewrite List_hd_nth_0 in Hc.
  destruct n; [ easy | exfalso ].
  rewrite List_map_nth' with (a := 0) in Hc. 2: {
    rewrite seq_length, Hra; flia.
  }
  apply map_eq_nil in Hc.
  apply List_seq_eq_nil in Hc.
  apply Hcrb in Hc.
  flia Hrb Hc.
} {
  intros l Hl.
  apply in_map_iff in Hl.
  destruct Hl as (i & Him & Hl).
  subst l.
  rewrite map_seq_length.
  apply squ_mat_ncols.
}
Qed.

Definition square_matrix_mul {n} (MA MB : square_matrix n T) :
  square_matrix n T :=
  {| sm_mat := (sm_mat MA * sm_mat MB)%M;
     sm_prop := square_matrix_mul_is_square MA MB |}.

Theorem square_matrix_opp_is_square : ∀ n (M : square_matrix n T),
  is_square_matrix n (- sm_mat M)%M = true.
Proof.
intros.
apply is_sm_mat_iff.
split; cbn. {
  rewrite map_length.
  rewrite fold_mat_nrows.
  apply squ_mat_nrows.
}
split. {
  intros Hco.
  rewrite map_length.
  rewrite fold_mat_nrows.
  destruct M as (M & Ha); cbn in Hco |-*.
  apply is_sm_mat_iff in Ha.
  destruct Ha as (Hr & Hcr & Hc).
  unfold mat_ncols in Hco; cbn in Hco.
  apply length_zero_iff_nil in Hco.
  rewrite List_hd_nth_0 in Hco.
  destruct n; [ easy | exfalso ].
  rewrite List_map_nth' with (a := []) in Hco. 2: {
    rewrite fold_mat_nrows, Hr; flia.
  }
  apply map_eq_nil in Hco.
  apply (f_equal length) in Hco; cbn in Hco.
  rewrite <- List_hd_nth_0 in Hco.
  rewrite fold_mat_ncols in Hco.
  apply Hcr in Hco.
  flia Hr Hco.
} {
  intros l Hl.
  destruct M as (M & Hrc).
  cbn in Hl.
  apply is_sm_mat_iff in Hrc.
  destruct Hrc as (Hr, Hc).
  apply in_map_iff in Hl.
  destruct Hl as (la & Hlm & Hla).
  subst l.
  cbn in Hla.
  rewrite map_length.
  now apply Hc.
}
Qed.

Definition square_matrix_opp {n} (M : square_matrix n T) :
  square_matrix n T :=
  {| sm_mat := (- sm_mat M)%M;
     sm_prop := square_matrix_opp_is_square M |}.

Definition phony_mat_le {n} (MA MB : square_matrix n T) := True.

Canonical Structure mat_ring_like_op n : ring_like_op (square_matrix n T) :=
  {| rngl_zero := smZ n;
     rngl_one := smI n;
     rngl_add := square_matrix_add;
     rngl_mul := square_matrix_mul;
     rngl_opt_opp := Some square_matrix_opp;
     rngl_opt_inv := None;
     rngl_opt_sous := None;
     rngl_opt_quot := None;
     rngl_le := phony_mat_le |}.

Existing Instance mat_ring_like_op.

(*
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
*)

Theorem squ_mat_add_comm {n} : ∀ (MA MB : square_matrix n T),
  (MA + MB)%F = (MB + MA)%F.
Proof.
intros.
apply square_matrix_eq.
apply mat_add_comm.
Qed.

Theorem squ_mat_add_assoc {n} : ∀ (MA MB MC : square_matrix n T),
  (MA + (MB + MC) = (MA + MB) + MC)%F.
Proof.
intros.
apply square_matrix_eq.
apply mat_add_assoc.
Qed.

Theorem square_matrix_is_correct : ∀ n (M : square_matrix n T),
  is_correct_matrix (sm_mat M).
Proof.
intros.
destruct M as (M, Hm); cbn.
apply is_sm_mat_iff in Hm.
destruct Hm as (Hr & Hcr & Hc).
split; [ now intros H; apply Hcr in H | ].
intros l Hl.
unfold mat_ncols.
rewrite Hc with (l := hd _ _). 2: {
  rewrite List_hd_nth_0.
  apply nth_In.
  destruct (mat_list_list M); [ easy | cbn; flia ].
}
now apply Hc.
Qed.

Theorem squ_mat_add_0_l {n} : ∀ M : square_matrix n T, (0 + M)%F = M.
Proof.
intros.
apply square_matrix_eq.
cbn.
apply mat_add_0_l; cycle 1. {
  symmetry; apply squ_mat_nrows.
} {
  symmetry; apply squ_mat_ncols.
}
apply square_matrix_is_correct.
Qed.

Theorem squ_mat_mul_assoc {n} : ∀ (MA MB MC : square_matrix n T),
  (MA * (MB * MC) = (MA * MB) * MC)%F.
Proof.
intros.
apply square_matrix_eq.
destruct MA as (MA & Ha).
destruct MB as (MB & Hb).
destruct MC as (MC & Hc); cbn.
move MB before MA; move MC before MB.
apply is_sm_mat_iff in Ha.
apply is_sm_mat_iff in Hb.
apply is_sm_mat_iff in Hc.
destruct Ha as (Hra & Hcra & Hca).
destruct Hb as (Hrb & Hcrb & Hcb).
destruct Hc as (Hrc & Hcrc & Hcc).
move Hrb before Hra; move Hrc before Hrb.
move Hcrb before Hcra; move Hcrc before Hcrb.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n; cbn.
  unfold "*"%M; cbn.
  now rewrite Hra, Hrb.
}
apply mat_mul_assoc. {
  now rewrite Hrb.
} {
  intros H; apply Hnz.
  apply Hcrb in H.
  rewrite <- Hrb; apply H.
} {
  rewrite Hrb.
  unfold mat_ncols.
  apply Hca.
  rewrite List_hd_nth_0.
  apply nth_In, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hra.
}
Qed.

Theorem squ_mat_mul_1_l {n} : ∀ M : square_matrix n T, (1 * M)%F = M.
Proof.
intros.
apply square_matrix_eq; cbn.
apply mat_mul_1_l; [ | symmetry; apply squ_mat_nrows ].
apply square_matrix_is_correct.
Qed.

Theorem squ_mat_mul_1_r {n} : ∀ M : square_matrix n T, (M * 1)%F = M.
Proof.
intros.
apply square_matrix_eq; cbn.
apply mat_mul_1_r; [ | symmetry; apply squ_mat_ncols ].
apply square_matrix_is_correct.
Qed.

Theorem squ_mat_mul_add_distr_l {n} : ∀ (MA MB MC : square_matrix n T),
  (MA * (MB + MC) = MA * MB + MA * MC)%F.
Proof.
intros.
apply square_matrix_eq.
destruct MA as (MA & Ha).
destruct MB as (MB & Hb).
destruct MC as (MC & Hc); cbn.
move MB before MA; move MC before MB.
apply is_sm_mat_iff in Ha.
apply is_sm_mat_iff in Hb.
apply is_sm_mat_iff in Hc.
destruct Ha as (Hra & Hcra & Hca).
destruct Hb as (Hrb & Hcrb & Hcb).
destruct Hc as (Hrc & Hcrc & Hcc).
move Hrb before Hra; move Hrc before Hrb.
move Hcrb before Hcra; move Hcrc before Hcrb.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n; cbn.
  unfold "*"%M, "+"%M; cbn.
  now rewrite Hra.
}
apply mat_mul_add_distr_l. {
  split; [ easy | ].
  intros l Hl.
  rewrite Hcb; [ | easy ].
  symmetry; apply Hcb.
  rewrite List_hd_nth_0.
  apply nth_In, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hrb.
} {
  split; [ easy | ].
  intros l Hl.
  rewrite Hcc; [ | easy ].
  symmetry; apply Hcc.
  rewrite List_hd_nth_0.
  apply nth_In, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hrc.
} {
  now rewrite Hrb.
} {
  rewrite Hrb; unfold mat_ncols.
  apply Hca.
  rewrite List_hd_nth_0.
  apply nth_In, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hra.
} {
  congruence.
} {
  unfold mat_ncols.
  rewrite Hcb. 2: {
    rewrite List_hd_nth_0.
    apply nth_In, Nat.neq_0_lt_0.
    now rewrite fold_mat_nrows, Hrb.
  }
  rewrite Hcc. 2: {
    rewrite List_hd_nth_0.
    apply nth_In, Nat.neq_0_lt_0.
    now rewrite fold_mat_nrows, Hrc.
  }
  easy.
}
Qed.

Theorem squ_mat_mul_add_distr_r {n} : ∀ (MA MB MC : square_matrix n T),
  ((MA + MB) * MC = MA * MC + MB * MC)%F.
Proof.
intros.
apply square_matrix_eq.
destruct MA as (MA & Ha).
destruct MB as (MB & Hb).
destruct MC as (MC & Hc); cbn.
move MB before MA; move MC before MB.
apply is_sm_mat_iff in Ha.
apply is_sm_mat_iff in Hb.
apply is_sm_mat_iff in Hc.
destruct Ha as (Hra & Hcra & Hca).
destruct Hb as (Hrb & Hcrb & Hcb).
destruct Hc as (Hrc & Hcrc & Hcc).
move Hrb before Hra; move Hrc before Hrb.
move Hcrb before Hcra; move Hcrc before Hcrb.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n; cbn.
  unfold "*"%M, "+"%M; cbn.
  rewrite map2_length; cbn.
  do 2 rewrite fold_mat_nrows.
  now rewrite Hra.
}
apply mat_mul_add_distr_r. {
  split; [ easy | ].
  intros l Hl.
  rewrite Hca; [ | easy ].
  symmetry; apply Hca.
  rewrite List_hd_nth_0.
  apply nth_In, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hra.
} {
  split; [ easy | ].
  intros l Hl.
  rewrite Hcb; [ | easy ].
  symmetry; apply Hcb.
  rewrite List_hd_nth_0.
  apply nth_In, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hrb.
} {
  now rewrite Hra.
} {
  congruence.
} {
  unfold mat_ncols.
  rewrite Hca. 2: {
    rewrite List_hd_nth_0.
    apply nth_In, Nat.neq_0_lt_0.
    now rewrite fold_mat_nrows, Hra.
  }
  rewrite Hcb. 2: {
    rewrite List_hd_nth_0.
    apply nth_In, Nat.neq_0_lt_0.
    now rewrite fold_mat_nrows, Hrb.
  }
  easy.
}
Qed.

Theorem squ_mat_opt_1_neq_0 {n} :
  if rngl_has_1_neq_0 && negb (n =? 0) then
    @rngl_one (square_matrix n T) (mat_ring_like_op n) ≠
    @rngl_zero (square_matrix n T) (mat_ring_like_op n)
  else not_applicable.
(*
  if rngl_has_1_neq_0 && negb (n =? 0) then 1%F ≠ 0%F else not_applicable.
*)
Proof.
remember (rngl_has_1_neq_0 && negb (n =? 0)) as b eqn:Hb.
symmetry in Hb.
destruct b; [ | easy ].
apply Bool.andb_true_iff in Hb.
destruct Hb as (H10, Hb).
apply Bool.negb_true_iff in Hb.
apply Nat.eqb_neq in Hb.
intros H; cbn in H.
unfold smI, smZ in H.
injection H; clear H; intros H.
destruct n; [ easy | ].
cbn in H.
injection H; intros H1 H2.
now apply rngl_1_neq_0.
Qed.

Theorem squ_mat_opt_add_opp_l {n} :
  if @rngl_has_opp (square_matrix n T) (mat_ring_like_op n) then
    ∀ M : square_matrix n T, (- M + M)%F = 0%F
  else not_applicable.
(*
  if rngl_has_opp then ∀ M : square_matrix n T, (- M + M)%F = 0%F
  else not_applicable.
*)
Proof.
remember (@rngl_has_opp (square_matrix n T) (mat_ring_like_op n)) as b eqn:Hb.
symmetry in Hb.
destruct b; [ | easy ].
intros M; cbn.
apply square_matrix_eq; cbn.
destruct M as (M & Hs); cbn.
apply is_sm_mat_iff in Hs.
destruct Hs as (Hr & Hcr & Hc).
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n; cbn.
  unfold mat_opp, "+"%M, mZ; cbn.
  apply length_zero_iff_nil in Hr.
  now rewrite Hr.
}
apply mat_add_opp_l; [ | easy | ]. 2: {
  unfold mat_ncols.
  symmetry; apply Hc.
  rewrite List_hd_nth_0.
  apply nth_In, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hr.
}
split; [ easy | ].
intros l Hl.
unfold mat_ncols.
rewrite Hc; [ | easy ].
symmetry; apply Hc.
rewrite List_hd_nth_0.
apply nth_In, Nat.neq_0_lt_0.
now rewrite fold_mat_nrows, Hr.
Qed.

Theorem mat_opt_eq_dec :
  if rngl_has_dec_eq then ∀ MA MB : matrix T, {MA = MB} + {MA ≠ MB}
  else not_applicable.
Proof.
remember rngl_has_dec_eq as de eqn:Hde; symmetry in Hde.
destruct de; [ | easy ].
intros MA MB.
destruct MA as (lla).
destruct MB as (llb).
specialize (list_eq_dec (list_eq_dec (rngl_eq_dec Hde)) lla llb) as H1.
destruct H1 as [H1| H1]; [ now subst lla; left | ].
right.
intros H; apply H1; clear H1.
now injection H.
Qed.

Theorem mat_eq_dec :
  rngl_has_dec_eq = true
  → ∀ MA MB : matrix T, {MA = MB} + {MA ≠ MB}.
Proof.
intros * Hde *.
specialize mat_opt_eq_dec as H1.
rewrite Hde in H1.
apply H1.
Qed.

Theorem squ_mat_opt_eq_dec {n} :
  if rngl_has_dec_eq then ∀ MA MB : square_matrix n T, {MA = MB} + {MA ≠ MB}
  else not_applicable.
Proof.
remember rngl_has_dec_eq as b eqn:Hed; symmetry in Hed.
destruct b; [ | easy ].
intros.
destruct MA as (MA & Ha).
destruct MB as (MB & Hb).
move MB before MA.
destruct (mat_eq_dec Hed MA MB) as [Hab| Hab]. {
  left; subst MB.
  now apply square_matrix_eq.
} {
  right; intros H; apply Hab; clear Hab.
  now injection H.
}
Qed.

Theorem mat_add_nrows : ∀ MA MB : matrix T,
  mat_nrows (MA + MB) = min (mat_nrows MA) (mat_nrows MB).
Proof.
intros.
unfold mZ, "+"%M, mat_nrows.
destruct MA as (lla).
destruct MB as (llb); cbn.
apply map2_length.
Qed.

Theorem mat_add_ncols : ∀ MA MB : matrix T,
  mat_ncols (MA + MB) = min (mat_ncols MA) (mat_ncols MB).
Proof.
intros.
unfold mZ, "+"%M, mat_ncols.
destruct MA as (lla).
destruct MB as (llb); cbn.
destruct lla as [| la]; [ easy | cbn ].
destruct llb as [| lb]; cbn; [ symmetry; apply Nat.min_r; flia | ].
apply map2_length.
Qed.

Theorem mat_nrows_of_nat {n} : ∀ i,
  mat_nrows (@sm_mat n T (rngl_of_nat i)) = n.
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n; destruct i | ].
induction i; [ now apply mZ_nrows | cbn ].
rewrite map2_length.
rewrite map_seq_length.
rewrite fold_mat_nrows, IHi.
apply Nat.min_id.
Qed.

Theorem mat_ncols_of_nat {n} : ∀ i,
  mat_ncols (@sm_mat n T (rngl_of_nat i)) = n.
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n; destruct i | ].
induction i; [ now apply mZ_ncols | cbn ].
rewrite mat_add_ncols.
rewrite mI_ncols, IHi.
apply Nat.min_id.
Qed.

Theorem mat_el_add : ∀ (MA MB : matrix T) i j,
  is_correct_matrix MA
  → is_correct_matrix MB
  → i < mat_nrows MA
  → i < mat_nrows MB
  → j < mat_ncols MA
  → j < mat_ncols MB
  → mat_el (MA + MB) i j = (mat_el MA i j + mat_el MB i j)%F.
Proof.
intros * Ha Hb Hia Hib Hja Hjb.
unfold "+"%M; cbn.
rewrite map2_nth with (a := []) (b := []); cycle 1. {
  now rewrite fold_mat_nrows.
} {
  now rewrite fold_mat_nrows.
}
rewrite map2_nth with (a := 0%F) (b := 0%F); cycle 1. {
  destruct Ha as (Hcra & Hca).
  rewrite Hca; [ easy | ].
  apply nth_In.
  now rewrite fold_mat_nrows.
} {
  destruct Hb as (Hcrb & Hcb).
  rewrite Hcb; [ easy | ].
  apply nth_In.
  now rewrite fold_mat_nrows.
}
easy.
Qed.

Theorem mat_add_is_correct : ∀ MA MB : matrix T,
  is_correct_matrix MA
  → is_correct_matrix MB
  → is_correct_matrix (MA + MB).
Proof.
intros * Ha Hb.
destruct Ha as (Hcra, Hca).
destruct Hb as (Hcrb, Hcb).
move Hcrb before Hcra.
destruct (Nat.eq_dec (mat_nrows MA) 0) as [Hraz| Hraz]. {
  unfold mat_nrows in Hraz.
  apply length_zero_iff_nil in Hraz.
  now destruct MA as (lla); cbn in Hraz |-*; subst lla.
}
destruct (Nat.eq_dec (mat_nrows MB) 0) as [Hrbz| Hrbz]. {
  unfold mat_nrows in Hrbz.
  apply length_zero_iff_nil in Hrbz.
  destruct MB as (llb); cbn in Hrbz |-*; subst llb.
  now rewrite mat_add_comm.
}
apply Nat.neq_0_lt_0 in Hraz, Hrbz.
split. {
  unfold mat_ncols, mat_nrows; cbn.
  intros Hab.
  apply length_zero_iff_nil in Hab.
  apply length_zero_iff_nil.
  remember (map2 _ _ _) as ll eqn:Hll.
  symmetry in Hll.
  destruct ll as [| l]; [ easy | exfalso ].
  cbn in Hab; subst l.
  apply (f_equal (hd [])) in Hll.
  cbn in Hll.
  rewrite List_hd_nth_0 in Hll.
  rewrite map2_nth with (a := []) (b := []) in Hll; [ | easy | easy ].
  apply map2_eq_nil in Hll.
  destruct Hll as [Hll| Hll]. {
    apply (f_equal length) in Hll; cbn in Hll.
    rewrite <- List_hd_nth_0 in Hll.
    rewrite fold_mat_ncols in Hll.
    apply Hcra in Hll.
    now rewrite Hll in Hraz.
  } {
    apply (f_equal length) in Hll; cbn in Hll.
    rewrite <- List_hd_nth_0 in Hll.
    rewrite fold_mat_ncols in Hll.
    apply Hcrb in Hll.
    now rewrite Hll in Hrbz.
  }
} {
  intros l Hl.
  rewrite mat_add_ncols.
  cbn in Hl.
  apply in_map2_iff in Hl.
  destruct Hl as (i & Him & la & lb & Hab).
  do 2 rewrite fold_mat_nrows in Him.
  subst l.
  rewrite map2_length.
  rewrite Hca. 2: {
    apply nth_In.
    rewrite fold_mat_nrows.
    now apply Nat.min_glb_lt_iff in Him.
  }
  rewrite Hcb. 2: {
    apply nth_In.
    rewrite fold_mat_nrows.
    now apply Nat.min_glb_lt_iff in Him.
  }
  easy.
}
Qed.

Theorem List_repeat_as_map : ∀ A (a : A) n,
  repeat a n = map (λ _, a) (seq 0 n).
Proof.
intros.
induction n; [ easy | cbn ].
f_equal.
now rewrite <- seq_shift, map_map.
Qed.

Theorem sm_mat_of_nat :
  @rngl_has_opp T ro = true ∨ @rngl_has_sous T ro = true
  → ∀ n m,
     sm_mat (rngl_of_nat m : square_matrix n T) = (rngl_of_nat m × mI n)%M.
(*
  rngl_has_opp = true ∨ rngl_has_sous = true
  → ∀ n m : nat, sm_mat (rngl_of_nat m) = (rngl_of_nat m × mI n)%M
*)
Proof.
cbn.
intros Hop; cbn.
induction m; cbn. {
  unfold "×"%M, mZ, mI.
  f_equal; cbn.
  rewrite map_map.
  rewrite List_repeat_as_map.
  apply map_ext_in.
  intros i Hi.
  rewrite List_repeat_as_map.
  rewrite map_map.
  apply map_ext_in.
  intros j Hj.
  now symmetry; apply rngl_mul_0_l.
}
rewrite mat_mul_scal_l_add_distr_r.
now rewrite mat_mul_scal_1_l, IHm.
Qed.

Theorem mat_el_of_nat_diag {n} : ∀ m i,
  i < n
  → mat_el
      (sm_mat
         (@rngl_of_nat (square_matrix n T) (mat_ring_like_op n) m)) i i =
    rngl_of_nat m.
(*
  ∀ m i : nat, i < n → mat_el (sm_mat (rngl_of_nat m)) i i = rngl_of_nat m
*)
Proof.
intros * Hin.
rewrite sm_mat_of_nat; [ | now left ].
cbn.
rewrite map_map.
rewrite List_map_nth' with (a := 0); [ | now rewrite seq_length ].
rewrite List_map_nth' with (a := 0%F). 2: {
  now rewrite map_seq_length.
}
rewrite List_map_nth' with (a := 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ cbn | easy ].
unfold δ.
now rewrite Nat.eqb_refl, rngl_mul_1_r.
Qed.

Theorem rngl_of_nat_is_correct_matrix {n} :
  rngl_characteristic = 0
  → ∀ i, is_correct_matrix (@sm_mat n T (rngl_of_nat i)).
Proof.
intros Hch *.
split. {
  intros Hc.
  destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
    now subst n; destruct i.
  }
  destruct (Nat.eq_dec i 0) as [Hiz| Hiz]. {
    subst i; cbn in Hc |-*.
    now rewrite mZ_ncols in Hc.
  }
  unfold mat_ncols in Hc.
  unfold mat_nrows.
  apply length_zero_iff_nil in Hc.
  apply length_zero_iff_nil.
  remember (mat_list_list _) as lla eqn:Hlla.
  symmetry in Hlla.
  apply (f_equal (λ ll, nth 0 (nth 0 ll []) 0%F)) in Hlla.
  rewrite fold_mat_el in Hlla.
  rewrite List_hd_nth_0 in Hc.
  rewrite Hc in Hlla; cbn in Hlla.
  exfalso; clear lla Hc.
  destruct i; [ easy | clear Hiz ].
  cbn - [ mat_el ] in Hlla.
  apply Nat.neq_0_lt_0 in Hnz.
  rewrite mat_el_add in Hlla; cycle 1. {
    apply mI_is_correct_matrix.
  } {
    apply square_matrix_is_correct.
  } {
    now rewrite mI_nrows.
  } {
    now rewrite squ_mat_nrows.
  } {
    now rewrite mI_ncols.
  } {
    now rewrite squ_mat_ncols.
  }
  rewrite mat_el_mI_diag in Hlla; [ | easy ].
  rewrite mat_el_of_nat_diag in Hlla; [ | easy ].
  specialize rngl_characteristic_prop as H1.
  rewrite Hch in H1; cbn in H1.
  now apply (H1 i).
} {
  intros l Hl.
  rewrite mat_ncols_of_nat.
  remember (rngl_of_nat i) as M eqn:HM.
  destruct M as (M, Hm); cbn in Hl.
  clear HM.
  apply is_sm_mat_iff in Hm.
  destruct Hm as (Hr & Hcr & Hc).
  now apply Hc.
}
Qed.

Theorem squ_mat_characteristic_prop {n} :
  if (if n =? 0 then 1 else rngl_characteristic) =? 0
  then ∀ i, @rngl_of_nat (square_matrix n T) (mat_ring_like_op n) (S i) ≠ 0%F
  else
    @rngl_of_nat (square_matrix n T) (mat_ring_like_op n)
      (if n =? 0 then 1 else rngl_characteristic) = 0%F.
Proof.
rewrite (if_eqb_eq_dec n).
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  now apply square_matrix_eq.
}
apply Nat.neq_0_lt_0 in Hnz.
specialize @rngl_characteristic_prop as H1.
specialize (H1 T ro rp).
rewrite if_eqb_eq_dec in H1 |-*.
destruct (Nat.eq_dec rngl_characteristic 0) as [Hch| Hcn]. {
  intros i Hi.
  apply (f_equal (λ M, mat_el (sm_mat M) 0 0)) in Hi.
  cbn in Hi.
  rewrite List_nth_repeat in Hi.
  destruct (lt_dec 0 n) as [H| H]; [ clear H | flia Hnz H ].
  rewrite List_nth_repeat in Hi.
  destruct (lt_dec 0 n) as [H| H]; [ clear H | flia Hnz H ].
  rewrite map2_map_l in Hi.
  rewrite map2_nth with (a := 0) (b := []) in Hi; cycle 1. {
    now rewrite seq_length.
  } {
    rewrite fold_mat_nrows.
    clear Hi.
    induction i; cbn; [ now rewrite repeat_length | ].
    rewrite map2_length, map_seq_length.
    rewrite fold_mat_nrows.
    flia Hnz IHi.
  }
  rewrite map2_nth with (a := 0%F) (b := 0%F) in Hi; cycle 1. {
    now rewrite map_seq_length.
  } {
    rewrite <- List_hd_nth_0, fold_mat_ncols.
    now rewrite mat_ncols_of_nat.
  }
  rewrite List_map_nth' with (a := 0) in Hi; [ | now rewrite seq_length ].
  rewrite seq_nth in Hi; [ cbn in Hi | easy ].
  rewrite fold_mat_el in Hi.
  replace (mat_el (sm_mat (rngl_of_nat i)) 0 0) with
    (@rngl_of_nat T ro i) in Hi. 2: {
    symmetry.
    clear Hi.
    induction i. {
      cbn.
      rewrite List_nth_repeat.
      destruct (lt_dec 0 n) as [H| H]; [ clear H | flia Hnz H ].
      rewrite List_nth_repeat.
      now destruct (lt_dec 0 n).
    }
    cbn - [ mat_el ].
    rewrite mat_el_add; cycle 1. {
      apply mI_is_correct_matrix.
    } {
      now apply rngl_of_nat_is_correct_matrix.
    } {
      now rewrite mI_nrows.
    } {
      now rewrite squ_mat_nrows.
    } {
      now rewrite mI_ncols.
    } {
      now rewrite squ_mat_ncols.
    }
    rewrite mat_el_mI_diag; [ | easy ].
    now rewrite IHi.
  }
  now specialize (H1 i); cbn in H1.
}
cbn.
apply square_matrix_eq; cbn.
rewrite sm_mat_of_nat; [ | now left ].
unfold "×"%M, mZ.
f_equal; rewrite H1.
destruct n; [ flia Hnz | clear Hnz ].
cbn.
f_equal. {
  f_equal; [ now apply rngl_mul_0_l; left | ].
  rewrite <- seq_shift.
  rewrite map_map, map_map.
  rewrite List_repeat_as_map.
  apply map_ext_in.
  intros i Hi.
  now apply rngl_mul_0_l; left.
}
rewrite <- seq_shift.
rewrite map_map, map_map.
rewrite List_repeat_as_map.
apply map_ext_in.
intros i Hi.
rewrite map_map; cbn.
rewrite rngl_mul_0_l; [ | now left ].
f_equal.
rewrite List_repeat_as_map.
rewrite map_map.
apply map_ext_in.
intros j Hj.
now apply rngl_mul_0_l; left.
Qed.

Theorem squ_mat_consistent {n} :
  (@rngl_has_opp (square_matrix n T) (mat_ring_like_op n) = false
   ∨ @rngl_has_sous (square_matrix n T) (mat_ring_like_op n) = false)
  ∧ (@rngl_has_inv (square_matrix n T) (mat_ring_like_op n) = false
     ∨ @rngl_has_quot (square_matrix n T) (mat_ring_like_op n) = false).
(*
  (rngl_has_opp = false ∨ rngl_has_sous = false) ∧
  (rngl_has_inv = false ∨ rngl_has_quot = false)
*)
Proof.
now split; right.
Qed.

Definition mat_ring_like_prop (n : nat) :
  ring_like_prop (square_matrix n T) :=
  {| rngl_is_comm := false;
     rngl_has_dec_eq := @rngl_has_dec_eq T ro rp;
     rngl_has_dec_le := false;
     rngl_has_1_neq_0 := (rngl_has_1_neq_0 && negb (Nat.eqb n 0))%bool;
     rngl_is_ordered := false;
     rngl_is_integral := false;
     rngl_characteristic := if n =? 0 then 1 else rngl_characteristic;
     rngl_add_comm := squ_mat_add_comm;
     rngl_add_assoc := squ_mat_add_assoc;
     rngl_add_0_l := squ_mat_add_0_l;
     rngl_mul_assoc := squ_mat_mul_assoc;
     rngl_mul_1_l := squ_mat_mul_1_l;
     rngl_mul_add_distr_l := squ_mat_mul_add_distr_l;
     rngl_opt_1_neq_0 := squ_mat_opt_1_neq_0;
     rngl_opt_mul_comm := NA;
     rngl_opt_mul_1_r := squ_mat_mul_1_r;
     rngl_opt_mul_add_distr_r := squ_mat_mul_add_distr_r;
     rngl_opt_add_opp_l := squ_mat_opt_add_opp_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_sub_sub_add := NA;
     rngl_opt_mul_sub_distr_l := NA;
     rngl_opt_mul_sub_distr_r := NA;
     rngl_opt_mul_inv_l := NA;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_mul_quot_l := NA;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_eq_dec := squ_mat_opt_eq_dec;
     rngl_opt_le_dec := NA;
     rngl_opt_integral := NA;
     rngl_characteristic_prop := squ_mat_characteristic_prop;
     rngl_opt_le_refl := NA;
     rngl_opt_le_antisymm := NA;
     rngl_opt_le_trans := NA;
     rngl_opt_add_le_compat := NA;
     rngl_opt_mul_le_compat_nonneg := NA;
     rngl_opt_mul_le_compat_nonpos := NA;
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := NA;
     rngl_consistent := squ_mat_consistent |}.

Theorem mat_vect_mul_0_r : ∀ m n (M : matrix T),
  m = mat_nrows M
  → n = mat_ncols M
  → (M • vect_zero n = vect_zero m)%V.
Proof.
intros * Hr Hc.
subst m n.
unfold "•"%V, vect_zero; cbn; f_equal.
unfold vect_dot_mul; cbn.
rewrite (List_repeat_as_map _ (mat_nrows _)).
destruct M as (lla); cbn.
rewrite (List_eq_map_seq lla) with (d := []) at 1.
rewrite map_map.
apply map_ext_in.
intros i Hi.
apply all_0_rngl_summation_list_0.
intros j Hj.
unfold mat_ncols in Hj; cbn in Hj.
apply in_map2_iff in Hj.
destruct Hj as (k & Hkm & a & b & Hk).
subst j.
rewrite List_nth_repeat; cbn.
rewrite repeat_length in Hkm.
apply Nat.min_glb_lt_iff in Hkm.
destruct (lt_dec k (length (hd [] lla))) as [H| H]; [ | flia Hkm H ].
now apply rngl_mul_0_r; left.
Qed.

(* *)

End a.

Module matrix_Notations.

Declare Scope M_scope.
Delimit Scope M_scope with M.

Arguments mat_el {T}%type {ro} M%M (i j)%nat.
Arguments mat_add {T}%type {ro} (MA MB)%M.
Arguments mat_add_0_r {T}%type {ro rp} {m n}%nat M%M.
Arguments mat_add_add_swap {T}%type {ro rp} (MA MB MC)%M.
Arguments mat_add_assoc {T}%type {ro rp} (MA MB MC)%M.
Arguments mat_add_comm {T}%type {ro rp} (MA MB)%M.
Arguments mat_add_opp_r {T}%type {ro rp} Hro M%M.
Arguments mat_add_sub {T}%type {ro rp} Hro (MA MB)%M.
Arguments mat_mul {T}%type {ro} (MA MB)%M.
Arguments mat_mul_add_distr_l {T}%type {ro rp} (MA MB MC)%M.
Arguments mat_mul_el {T}%type {ro} (MA MB)%M (i k)%nat.
Arguments mat_mul_scal_l_add_distr_l {T}%type {ro rp} a%F (MA MB)%M.
Arguments mat_mul_scal_l_add_distr_r {T}%type {ro rp} (a b)%F M%M.
Arguments mat_mul_scal_1_l {T}%type {ro rp} M%M.
Arguments mat_mul_scal_l_mul {T}%type {ro rp} Hro a%F (MA MB)%M.
Arguments mat_mul_scal_l_mul_assoc {T}%type {ro rp} (a b)%F M%M.
Arguments mat_mul_mul_scal_l {T}%type {ro rp} Hro Hic a%F (MA MB)%M.
Arguments mat_mul_scal_l {T ro} s%F M%M.
Arguments mat_mul_vect_r {T ro} M%M V%V.
Arguments mat_mul_scal_vect_comm {T}%type {ro rp} Hro Hic a%F MA%M V%V.
Arguments mat_mul_scal_vect_assoc {T}%type {ro rp} Hro a%F MA%M V%V.
Arguments mat_nrows {T}%type M%M.
Arguments mat_ncols {T}%type M%M.
Arguments mat_vect_mul_assoc {T}%type {ro rp} Hro (A B)%M V%V.
Arguments mat_mul_1_l {T}%type {ro rp} Hro {n}%nat M%M.
Arguments mat_mul_1_r {T}%type {ro rp} Hro {n}%nat M%M.
Arguments mat_opp {T ro} M%M.
Arguments mat_repl_vect_is_square {T}%type {ro} [n k]%nat.
Arguments mat_sub {T ro} MA%M MB%M.
Arguments mI {T ro} n%nat.
Arguments mZ {T ro} (m n)%nat.
Arguments minus_one_pow {T ro}.
Arguments subm {T} M%M i%nat j%nat.
Arguments mat_vect_mul_1_l {T}%type {ro rp} Hro {n}%nat V%V.
Arguments δ {T}%type {ro} (i j)%nat.
Arguments matrix_eq {T}%type {ro} (MA MB)%M.
Arguments is_correct_matrix {T}%type M%M.
Arguments is_square_matrix {T}%type n%nat M%M.
Arguments mI_is_correct_matrix {T}%type {ro} n%nat.

Notation "A + B" := (mat_add A B) : M_scope.
Notation "A - B" := (mat_sub A B) : M_scope.
Notation "A * B" := (mat_mul A B) : M_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.
Notation "- A" := (mat_opp A) : M_scope.
Notation "A ⁺" := (mat_transp A) (at level 1, format "A ⁺") : M_scope.
Notation "A • V" := (mat_mul_vect_r A V) (at level 40) : M_scope.
Notation "A • V" := (mat_mul_vect_r A V) (at level 40) : V_scope.

End matrix_Notations.
