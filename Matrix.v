(* matrices *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Bool.
Import List List.ListNotations.
Require Import Init.Nat.

Require Import Misc.
Require Import RingLike IterAdd IterMul IterAnd.
Require Import MyVector Signature.

Definition nth_nth_error A (ll : list (list A)) (i j : nat) := 
  match nth_error ll i with
  | None => None
  | Some l => Some (nth_error l j)
  end.

(* matrices *)

Record matrix T := mk_mat
  { mat_list_list : list (list T) }.

Definition mat_nrows {T} (M : matrix T) := length (mat_list_list M).
Definition mat_ncols {T} (M : matrix T) := length (hd [] (mat_list_list M)).
Definition mat_el {T} {ro : ring_like_op T} (M : matrix T) i j :=
  nth j (nth i (mat_list_list M) []) 0%F.

(* correct_matrix: matrix whose list list is made of non
   empty lists (rows) of same length *)

Definition is_correct_matrix {T} (M : matrix T) :=
  (mat_ncols M = 0 → mat_nrows M = 0) ∧
  ∀ l, l ∈ mat_list_list M → length l = mat_ncols M.

Theorem tail_is_correct_matrix : ∀ {A} (M : matrix A),
  is_correct_matrix M
  → is_correct_matrix (mk_mat (tl (mat_list_list M))).
Proof.
intros * Hcm.
destruct Hcm as (Hcr, Hcl).
split. {
  unfold mat_ncols; cbn.
  intros Hr.
  apply length_zero_iff_nil in Hr.
  unfold mat_ncols in Hcr, Hcl.
  destruct M as (ll); cbn in *.
  destruct ll as [| la]; [ easy | ].
  cbn in Hr |-*.
  destruct ll as [| la']; [ easy | ].
  cbn in Hr; subst la'; exfalso.
  cbn in Hcr.
  specialize (Hcl [] (or_intror (or_introl eq_refl))) as H1.
  cbn in H1; symmetry in H1.
  now specialize (Hcr H1).
} {
  intros l Hl; cbn in Hl.
  unfold mat_ncols; cbn.
  rewrite Hcl. 2: {
    destruct M as (ll); cbn in Hl |-*.
    destruct ll as [| la]; [ easy | ].
    now right.
  }
  symmetry.
  rewrite Hcl. 2: {
    destruct M as (ll); cbn in Hl |-*.
    destruct ll as [| la]; [ easy | ].
    destruct ll as [| la']; [ easy | ].
    cbn in Hl |-*.
    now right; left.
  }
  easy.
}
Qed.

Theorem matrix_eq' : ∀ T (ro : ring_like_op T) MA MB,
  (∀ i j, i < mat_nrows MA → j < mat_ncols MB → mat_el MA i j = mat_el MB i j)
  → is_correct_matrix MA
  → is_correct_matrix MB
  → mat_nrows MA = mat_nrows MB
  → mat_ncols MA = mat_ncols MB
  → MA = MB.
Proof.
intros * Hij Ha Hb Hrr Hcc.
destruct MA as (lla).
destruct MB as (llb).
f_equal.
cbn in *.
remember (length lla) as len eqn:Hr; symmetry in Hr.
rename Hrr into Hc; symmetry in Hc; move Hc before Hr.
revert lla llb Hr Hc Hij Hcc Ha Hb.
induction len; intros. {
  apply length_zero_iff_nil in Hr, Hc; congruence.
}
destruct lla as [| la]; [ easy | ].
destruct llb as [| lb]; [ easy | ].
cbn in Hr, Hc, Hcc.
apply Nat.succ_inj in Hr, Hc.
f_equal. {
  apply nth_ext with (d := 0%F) (d' := 0%F); [ easy | ].
  intros i Hi.
  unfold mat_ncols in Hij.
  cbn - [ nth ] in Hij.
  apply (Hij 0 i (Nat.lt_0_succ _)).
  congruence.
}
apply IHlen; [ easy | easy | | | | ]; cycle 1. {
  destruct Ha as (Ha1, Ha2).
  destruct Hb as (Hb1, Hb2).
  unfold mat_ncols; cbn.
  specialize (Ha2 (hd [] lla)).
  specialize (Hb2 (hd [] llb)).
  cbn - [ In ] in Ha2, Hb2.
  destruct lla as [| la']. {
    cbn in Hr; subst len.
    now apply length_zero_iff_nil in Hc; subst llb.
  }
  destruct llb as [| lb']. {
    now cbn in Hc; move Hc at top; subst len.
  }
  cbn in Ha2, Hb2 |-*.
  specialize (Ha2 (or_intror (or_introl eq_refl))).
  specialize (Hb2 (or_intror (or_introl eq_refl))).
  congruence.
} {
  now apply tail_is_correct_matrix in Ha.
} {
  now apply tail_is_correct_matrix in Hb.
}
intros * Hi Hj.
unfold mat_ncols in Hij, Hj.
cbn - [ nth ] in Hij.
cbn in Hj.
specialize (Hij (S i) j) as H1.
assert (H : S i < S len) by now apply Nat.succ_lt_mono in Hi.
specialize (H1 H); clear H.
cbn in H1.
apply H1.
destruct Hb as (Hb1, Hb2).
unfold mat_ncols in Hb2; cbn in Hb2.
destruct llb as [| lb']; [ easy | ].
cbn in Hj.
specialize (Hb2 lb' (or_intror (or_introl eq_refl))).
congruence.
Qed.

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

Definition mat_nth_ncols {T} n (M : matrix T) :=
  length (nth n (mat_list_list M) []).

Theorem fold_mat_nrows {T} : ∀ (M : matrix T),
  length (mat_list_list M) = mat_nrows M.
Proof. easy. Qed.

Theorem fold_mat_ncols {T} : ∀ (M : matrix T),
  length (hd [] (mat_list_list M)) = mat_ncols M.
Proof. easy. Qed.

Theorem fold_mat_nth_ncols {T} : ∀ i (M : matrix T),
  length (nth i (mat_list_list M) []) = mat_nth_ncols i M.
Proof. easy. Qed.

Theorem fold_mat_el {T} {ro : ring_like_op T} : ∀ (M : matrix T) i j,
  nth j (nth i (mat_list_list M) []) 0%F = mat_el M i j.
Proof. easy. Qed.

Theorem mat_eq_map_seq : ∀ T (M : matrix T),
  M =
  mk_mat (map (λ i, nth i (mat_list_list M) []) (seq 0 (mat_nrows M))).
Proof.
intros.
rewrite <- List_map_nth_seq.
now destruct M.
Qed.

Theorem eq_mat_nrows_0 {T} : ∀ M : matrix T,
  mat_nrows M = 0
  → mat_list_list M = [].
Proof.
intros * Hr.
unfold mat_nrows in Hr.
now apply length_zero_iff_nil in Hr.
Qed.

Theorem fold_left_mat_fold_left_list_list : ∀ T A (M : matrix T) (l : list A) f,
  fold_left f l M =
  mk_mat
    (fold_left (λ ll k, mat_list_list (f (mk_mat ll) k)) l (mat_list_list M)).
Proof.
intros.
revert M.
induction l as [| a]; intros; [ now destruct M | cbn ].
rewrite IHl; cbn.
now destruct M.
Qed.

(* this definition should (if it could) be defined like
   is_square_matrix below, to allow property to be
   unique *)

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

Definition is_square_matrix {T} (M : matrix T) :=
  ((mat_ncols M ≠? 0) || (mat_nrows M =? 0)) &&
  (⋀ (l ∈ mat_list_list M), (length l =? mat_nrows M)).

Record square_matrix n T :=
  { sm_mat : matrix T;
    sm_prop : (mat_nrows sm_mat =? n) && is_square_matrix sm_mat = true }.

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

Theorem is_sm_mat_iff {T} : ∀ (M : matrix T),
  is_square_matrix M = true ↔
  (mat_ncols M = 0 → mat_nrows M = 0) ∧
  ∀ l, l ∈ mat_list_list M → length l = mat_nrows M.
Proof.
intros.
unfold is_square_matrix.
split; intros Hm. {
  apply Bool.andb_true_iff in Hm.
  destruct Hm as (Hrc, Hc).
  apply Bool.orb_true_iff in Hrc.
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
  destruct Hm as (Hrc & Hc).
  apply Bool.andb_true_iff.
  split. {
    apply Bool.orb_true_iff.
    destruct (Nat.eq_dec (mat_nrows M) 0) as [Hnz| Hnz]. {
      now right; apply Nat.eqb_eq.
    }
    left.
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

(*
Theorem square_matrix_nrows {n T} : ∀ (M : matrix T),
  is_square_matrix M = true
  → mat_nrows M = n.
Proof.
intros * Hm.
now apply is_sm_mat_iff in Hm.
Qed.
*)

Theorem square_matrix_ncols {T} : ∀ (M : matrix T),
  is_square_matrix M = true
  → mat_ncols M = mat_nrows M.
Proof.
intros * Hm.
apply is_sm_mat_iff in Hm.
destruct Hm as (Hcr & Hc).
destruct (Nat.eq_dec (mat_nrows M) 0) as [Hnz| Hnz]. {
  unfold mat_nrows, mat_ncols in Hnz |-*.
  now apply length_zero_iff_nil in Hnz; rewrite Hnz.
}
apply Nat.neq_0_lt_0 in Hnz.
now apply Hc, List_hd_in.
Qed.

Theorem squ_mat_is_corr {T} : ∀ (M : matrix T),
  is_square_matrix M = true
  → is_correct_matrix M.
Proof.
intros * Hsm.
specialize (square_matrix_ncols _ Hsm) as Hc.
apply is_sm_mat_iff in Hsm.
split; [ easy | ].
intros l Hl.
destruct Hsm as (Hcr & Hc').
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
    if Nat.eq_dec j k then vect_el 0%F V i else mat_el M i j.
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

Theorem mat_repl_vect_is_square : ∀ k (M : matrix T) V,
  k < mat_ncols M
  → vect_size V = mat_nrows M
  → is_square_matrix M = true
  → is_square_matrix (mat_repl_vect k M V) = true.
Proof.
intros * Hkc Hv Hm.
specialize (square_matrix_ncols _ Hm) as Hcn.
apply is_sm_mat_iff in Hm.
apply is_sm_mat_iff.
destruct Hm as (Hcr & Hc).
rewrite mat_repl_vect_nrows; [ | congruence ].
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
  rewrite fold_mat_nrows, fold_vect_size, Hv in Hi.
  rewrite Nat.min_id in Hi.
  subst la.
  unfold replace_at.
  rewrite app_length.
  rewrite firstn_length.
  cbn - [ skipn ].
  rewrite skipn_length.
  rewrite fold_corr_mat_ncols; [ | | easy ]. 2: {
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
Arguments is_square_matrix {T}%type M%M.
Arguments Build_square_matrix n%nat [T]%type sm_mat%M.

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

Theorem mI_nrows : ∀ n, mat_nrows (mI n) = n.
Proof.
intros.
destruct n; cbn - [ "=?" ]; [ easy | ].
now rewrite List_map_seq_length.
Qed.

Theorem mI_ncols : ∀ n, mat_ncols (mI n) = n.
Proof.
intros.
destruct n; cbn - [ "=?" ]; [ easy | ].
now rewrite List_map_seq_length.
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
  now rewrite List_map_seq_length.
}
apply Nat.nlt_ge in Hin.
apply nth_overflow.
rewrite nth_overflow; [ cbn; flia | ].
now rewrite List_map_seq_length.
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
rewrite List_map_nth_seq with (d := []); subst x.
apply map_ext_in.
intros i Hi.
remember (nth i ll []) as la eqn:Hla.
rewrite List_map_nth_seq with (d := 0%F).
rewrite (HM la). 2: {
  rewrite Hla.
  apply nth_In.
  now apply in_seq in Hi.
}
apply map_ext_in.
intros j Hj.
unfold mat_mul_el.
rewrite rngl_summation_split3 with (j0 := i). 2: {
  split; [ easy | ].
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
rewrite List_map_nth_seq with (d := []); subst x.
apply map_ext_in.
intros i Hi.
remember (nth i ll []) as la eqn:Hla.
rewrite List_map_nth_seq with (d := 0%F).
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
  split; [ easy | ].
  apply -> Nat.succ_le_mono.
  apply in_seq in Hj.
  flia Hj.
}
rewrite rngl_summation_split_last; [ | easy ].
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
  rewrite map_length, List_map_seq_length in Hii.
  destruct y as [y| ]. {
    apply List_nth_error_Some_iff with (d := 0%F) in Hy.
    destruct Hy as (Hy, Hiv).
    f_equal.
    subst x y; cbn.
    rewrite List_map_nth' with (a := []). 2: {
      now rewrite List_map_seq_length.
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
rewrite map_length, List_map_seq_length in Hx.
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
rewrite List_map_seq_length.
apply map_ext_in.
intros i Hi.
unfold mat_ncols at 2; cbn.
rewrite (List_map_hd 0). 2: {
  now rewrite seq_length; apply Nat.neq_0_lt_0.
}
rewrite List_map_seq_length.
apply map_ext_in.
intros j Hj.
move j before i.
unfold mat_mul_el.
unfold mat_ncols at 4.
cbn.
rewrite (List_map_hd 0). 2: {
  rewrite seq_length; apply Nat.neq_0_lt_0.
  now intros H; rewrite H in Hi.
}
rewrite List_map_seq_length.
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
rewrite (List_map_hd []); [ | now rewrite fold_mat_nrows ].
apply map_length.
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
  intros Hc'.
  destruct (Nat.eq_dec (mat_nrows M) 0) as [Hrz| Hrz]; [ easy | ].
  rewrite (List_map_hd []) in Hc'. 2: {
    rewrite fold_mat_nrows.
    now apply Nat.neq_0_lt_0 in Hrz.
  }
  rewrite map_length in Hc'.
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
rewrite (List_map_hd []). 2: {
  now rewrite fold_mat_nrows; apply Nat.neq_0_lt_0.
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
rewrite (List_map_hd []); [ | now rewrite fold_mat_nrows, <- Hcarb ].
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
       (∑ (k = 0, vect_size V - 1), mat_el B j k * vect_el 0%F V k) =
     ∑ (j = 0, vect_size V - 1),
       (∑ (k = 0, mat_ncols A - 1), mat_el A i k * mat_el B k j) *
        vect_el 0%F V j.
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
    now rewrite Nat_sub_succ_1 in Hj.
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
erewrite rngl_summation_eq_compat; [ | easy ].
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
erewrite rngl_summation_eq_compat; [ | easy ].
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

Theorem fold_mat_transp : ∀ M,
  mk_mat
    (map (λ j, map (λ i, mat_el M i j) (seq 0 (mat_nrows M)))
       (seq 0 (mat_ncols M))) =
  mat_transp M.
Proof. easy. Qed.

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

Theorem subm_subm' : ∀ (M : matrix T) i j,
  is_correct_matrix M
  → i < mat_nrows M
  → j < mat_ncols M
  → subm M i j = subm' M i j.
Proof.
intros * Hm Hi Hj.
unfold subm, subm'.
f_equal.
rewrite (List_map_nth_seq (mat_list_list M) []) at 1.
rewrite fold_mat_nrows.
rewrite <- map_butn, map_map.
rewrite map_butn_seq.
unfold Nat.b2n at 2.
rewrite if_ltb_lt_dec.
destruct (lt_dec i (mat_nrows M)) as [H| H]; [ clear H | flia Hi H ].
apply map_ext_in.
intros u Hu.
apply in_seq in Hu; cbn.
unfold Nat.b2n at 1; rewrite if_leb_le_dec.
destruct (le_dec i u) as [Hui| Hui]. 2: {
  apply Nat.nle_gt in Hui.
  rewrite (List_map_nth_seq _ 0%F).
  rewrite butn_length.
  rewrite fold_corr_mat_ncols; [ | easy | flia Hu ].
  unfold Nat.b2n.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec j (mat_ncols M)) as [H| H]; [ clear H | flia Hj H ].
  apply map_ext_in.
  intros v Hv.
  unfold Nat.b2n.
  do 2 rewrite if_leb_le_dec.
  destruct (le_dec i u) as [H| H]; [ flia Hui H | clear H ].
  rewrite Nat.add_0_r.
  destruct (le_dec j v) as [Hvj| Hjv]. {
    now rewrite nth_butn_before.
  } {
    apply Nat.nle_gt in Hjv.
    rewrite nth_butn_after; [ | easy ].
    now rewrite Nat.add_0_r.
  }
} {
  unfold Nat.b2n.
  rewrite if_leb_le_dec.
  destruct (le_dec i u) as [H| H]; [ clear H | flia Hui H ].
  rewrite (List_map_nth_seq _ 0%F).
  rewrite butn_length.
  unfold Nat.b2n; rewrite if_ltb_lt_dec.
  rewrite fold_corr_mat_ncols; [ | easy | flia Hu ].
  destruct (lt_dec j (mat_ncols M)) as [H| H]; [ clear H | flia Hj H ].
  apply map_ext_in.
  intros v Hv.
  apply in_seq in Hv.
  unfold Nat.b2n.
  rewrite if_leb_le_dec.
  destruct (le_dec j v) as [Hjv| Hjv]. {
    now rewrite nth_butn_before.
  } {
    apply Nat.nle_gt in Hjv.
    rewrite Nat.add_0_r.
    now rewrite nth_butn_after.
  }
}
Qed.

(* combinations of submatrix and other operations *)

Theorem mat_nrows_subm : ∀ (M : matrix T) i j,
  mat_nrows (subm M i j) = mat_nrows M - Nat.b2n (i <? mat_nrows M).
Proof.
intros.
destruct M as (ll); cbn - [ "<?" ].
rewrite map_length.
now rewrite butn_length.
Qed.

Theorem mat_el_subm : ∀ (M : matrix T) i j u v,
  is_correct_matrix M
  → i < mat_nrows M - 1
  → j < mat_ncols M - 1
  → mat_el (subm M u v) i j =
      mat_el M (i + Nat.b2n (u <=? i)) (j + Nat.b2n (v <=? j)).
Proof.
intros * Hcm Hi Hj.
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
      rewrite fold_corr_mat_ncols; [ | easy | flia Hi ].
      flia Hvj Hj.
    }
    rewrite List_nth_skipn.
    now replace (j - v + S v) with (j + 1) by flia Hvj.
  } {
    rewrite Nat.add_0_r.
    apply Nat.nle_gt in Hvj.
    rewrite app_nth1. 2: {
      rewrite firstn_length.
      rewrite fold_corr_mat_ncols; [ | easy | flia Hi ].
      apply Nat.min_glb_lt; [ easy | flia Hj ].
    }
    now rewrite List_nth_firstn.
  }
} {
  rewrite Nat.add_0_r.
  apply Nat.nle_gt in Hui.
  rewrite app_nth1. 2: {
    rewrite map_length, firstn_length, fold_mat_nrows.
    apply Nat.min_glb_lt; [ easy | flia Hi ].
  }
  rewrite (List_map_nth' []). 2: {
    rewrite firstn_length, fold_mat_nrows.
    apply Nat.min_glb_lt; [ easy | flia Hi ].
  }
  rewrite List_nth_firstn; [ | easy ].
  destruct (le_dec v j) as [Hvj| Hvj]. {
    rewrite app_nth2; [ | rewrite firstn_length; flia Hvj ].
    rewrite firstn_length.
    rewrite fold_corr_mat_ncols; [ | easy | flia Hi ].
    rewrite Nat.min_l; [ | flia Hvj Hj ].
    rewrite List_nth_skipn.
    now replace (j - v + S v) with (j + 1) by flia Hvj.
  } {
    rewrite Nat.add_0_r.
    apply Nat.nle_gt in Hvj.
    rewrite app_nth1. 2: {
      rewrite firstn_length.
      rewrite fold_corr_mat_ncols; [ | easy | flia Hi ].
      apply Nat.min_glb_lt; [ easy | flia Hj ].
    }
    now rewrite List_nth_firstn.
  }
}
Qed.

Theorem subm_subm_r_r : ∀ i j k (M : matrix T),
  i ≤ k → subm (subm M i j) k j = subm (subm M (k + 1) j) i j.
Proof.
intros * Hik.
unfold subm; f_equal; cbn.
do 6 rewrite map_butn.
now rewrite butn_butn.
Qed.

Theorem subm_subm_l_l : ∀ i j k (M : matrix T),
  j ≤ k → subm (subm M i j) i k = subm (subm M i (k + 1)) i j.
Proof.
intros * Hkj.
unfold subm; f_equal; cbn.
do 6 rewrite map_butn.
f_equal; f_equal.
do 2 rewrite map_map.
apply map_ext_in.
intros la Hla.
now rewrite butn_butn.
Qed.

Theorem subm_subm_exch : ∀ i j k l (M : matrix T),
  k < i → j ≤ l → subm (subm M i j) k l = subm (subm M k (l + 1)) (i - 1) j.
Proof.
intros * Hki Hjl.
unfold subm; f_equal; cbn.
do 6 rewrite map_butn.
do 2 rewrite map_map.
destruct (le_dec k (i - 1)) as [Hki1| Hki1]. {
  symmetry.
  rewrite butn_butn; [ | easy ].
  rewrite Nat.sub_add; [ | flia Hki ].
  f_equal; f_equal.
  apply map_ext_in.
  intros la Hla.
  symmetry.
  now rewrite butn_butn.
}
replace i with (k + 1) by flia Hki Hki1.
clear i Hki Hki1.
rename k into i.
rewrite Nat.add_sub.
symmetry.
rewrite butn_butn; [ | easy ].
f_equal; f_equal.
apply map_ext_in.
intros la Hla.
symmetry.
now apply butn_butn.
Qed.

Theorem subm_subm_exch' : ∀ i j k l (M : matrix T),
  k < i → l < j → subm (subm M i j) k l = subm (subm M k l) (i - 1) (j - 1).
Proof.
intros * Hki Hlj.
unfold subm; f_equal; cbn.
do 6 rewrite map_butn.
do 2 rewrite map_map.
destruct (le_dec k (i - 1)) as [Hki1| Hki1]. {
  symmetry.
  rewrite butn_butn; [ | easy ].
  rewrite Nat.sub_add; [ | flia Hki ].
  f_equal; f_equal.
  apply map_ext_in.
  intros la Hla.
  rewrite butn_butn; [ | flia Hlj ].
  rewrite Nat.sub_add; [ easy | flia Hlj ].
}
replace i with (k + 1) by flia Hki Hki1.
clear i Hki Hki1.
rename k into i.
rewrite Nat.add_sub.
symmetry.
rewrite butn_butn; [ | easy ].
f_equal; f_equal.
apply map_ext_in.
intros la Hla.
destruct (lt_dec l (j - 1)) as [Hlj1| Hlj1]. {
  rewrite butn_butn; [ | flia Hlj1 ].
  rewrite Nat.sub_add; [ easy | flia Hlj ].
}
replace j with (l + 1) by flia Hlj Hlj1.
rewrite Nat.add_sub.
now rewrite butn_butn.
Qed.

Theorem subm_subm_exch'' : ∀ i j k (M : matrix T),
  i ≤ j → subm (subm M i (k + 1)) j k = subm (subm M (j + 1) k) i k.
Proof.
intros * Hij.
unfold subm; f_equal; cbn.
do 6 rewrite map_butn.
do 2 rewrite map_map.
rewrite butn_butn; [ | easy ].
f_equal; f_equal.
apply map_ext_in.
intros l Hl.
now symmetry; apply butn_butn.
Qed.

Theorem subm_out_l : ∀ i j (M : matrix T),
  mat_nrows M ≤ i
  → mat_nrows M ≤ j
  → ∀ k, subm M i k = subm M j k.
Proof.
intros * Hi Hj *.
unfold subm; f_equal.
do 2 rewrite map_butn.
rewrite butn_out; [ | now rewrite map_length, fold_mat_nrows ].
rewrite butn_out; [ | now rewrite map_length, fold_mat_nrows ].
easy.
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
  cbn; rewrite butn_length; rewrite H1.
  unfold Nat.b2n; rewrite if_ltb_lt_dec.
  now destruct (lt_dec j (length l)).
}
cbn; rewrite butn_length.
unfold Nat.b2n; rewrite if_ltb_lt_dec.
now destruct (lt_dec j (length l)).
Qed.

Theorem is_squ_mat_subm : ∀ (M : matrix T) i j,
  i < mat_nrows M
  → j < mat_nrows M
  → is_square_matrix M = true
  → is_square_matrix (subm M i j) = true.
Proof.
intros * Hi Hj Hm.
apply is_sm_mat_iff.
specialize (square_matrix_ncols _ Hm) as Hcm.
destruct (Nat.eq_dec (mat_nrows M) 1) as [Hr1| Hr1]. {
  rewrite Hr1 in Hi, Hj.
  apply Nat.lt_1_r in Hi, Hj.
  subst i j.
  destruct M as (ll); cbn in Hr1 |-*.
  destruct ll as [| l]; [ easy | ].
  now destruct ll.
}
split. {
  intros Hcs.
  rewrite <- Hcm in Hj.
  rewrite mat_ncols_subm in Hcs; [ | | flia Hi Hr1 | easy ]. 2: {
    now apply squ_mat_is_corr.
  }
  flia Hcs Hj Hcm Hr1.
} {
  intros l Hl.
  apply is_sm_mat_iff in Hm.
  destruct Hm as (Hcr & Hc).
  clear Hcr Hcm Hr1.
  rewrite mat_nrows_subm.
  apply Nat.ltb_lt in Hi; rewrite Hi.
  apply Nat.ltb_lt in Hi; cbn.
  destruct M as (ll).
  cbn in Hc, Hi, Hj |-*.
  cbn - [ butn ] in Hl.
  rewrite map_butn in Hl.
  apply in_butn in Hl.
  apply in_map_iff in Hl.
  destruct Hl as (l' & Hjl & Hl).
  rewrite <- Hjl.
  rewrite butn_length.
  unfold Nat.b2n.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec j (length l')) as [Hljl| Hljl]. {
    f_equal.
    now apply Hc.
  }
  apply Nat.nlt_ge in Hljl.
  rewrite butn_out in Hjl; [ | easy ].
  subst l'.
  rewrite Hc in Hljl; [ | easy ].
  flia Hj Hljl.
}
Qed.

Theorem subm_is_corr_mat : ∀ (A : matrix T) i j,
  mat_ncols A ≠ 1
  → is_correct_matrix A
  → is_correct_matrix (subm A i j).
Proof.
intros * Hc1 Ha.
split. {
  rewrite mat_nrows_subm.
  unfold Nat.b2n; rewrite if_ltb_lt_dec.
  destruct (lt_dec i (mat_nrows A)) as [Hir| Hir]. {
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
  rewrite Nat.sub_0_r.
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
    rewrite butn_length.
    unfold Nat.b2n; rewrite if_ltb_lt_dec, H1.
    destruct (lt_dec j (mat_ncols A)) as [H| H]; [ easy | flia Hjc H ].
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
rewrite Nat_sub_succ_1.
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
apply Bool.andb_true_iff in Hmp.
destruct Hmp as (Hr & Hmp).
now apply Nat.eqb_eq in Hr.
Qed.

Theorem squ_mat_ncols : ∀ n (M : square_matrix n T),
  mat_ncols (sm_mat M) = n.
Proof.
intros.
destruct M as (M, Hmp); cbn.
apply Bool.andb_true_iff in Hmp.
destruct Hmp as (Hr, Hmp).
apply Nat.eqb_eq in Hr.
apply is_sm_mat_iff in Hmp.
destruct Hmp as (Hrc, Hc).
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  unfold mat_ncols.
  unfold mat_nrows in Hr.
  apply length_zero_iff_nil in Hr.
  now rewrite Hr.
}
unfold mat_ncols.
rewrite <- Hr.
apply Hc.
apply List_hd_in.
unfold mat_nrows in Hr.
rewrite Hr.
now apply Nat.neq_0_lt_0.
Qed.

Theorem mZ_is_square_matrix : ∀ n,
  (mat_nrows (mZ n n) =? n) && is_square_matrix (mZ n n) = true.
Proof.
intros.
apply Bool.andb_true_iff.
split. {
  cbn; rewrite repeat_length.
  apply Nat.eqb_refl.
}
apply is_sm_mat_iff.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n; cbn | ].
split; [ now rewrite mZ_nrows, mZ_ncols | ].
intros la Hla.
cbn in Hla.
apply repeat_spec in Hla; subst la.
now cbn; do 2 rewrite repeat_length.
Qed.

Definition smZ n : square_matrix n T :=
  {| sm_mat := mZ n n;
     sm_prop := mZ_is_square_matrix n |}.

Theorem mI_is_square_matrix : ∀ n, is_square_matrix (mI n) = true.
Proof.
intros.
apply is_sm_mat_iff.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
apply Nat.neq_0_lt_0 in Hnz.
split. {
  unfold mat_ncols.
  cbn; rewrite map_length, seq_length.
  rewrite (List_map_hd 0); [ | now rewrite seq_length ].
  now rewrite map_length, seq_length.
}
intros la Hla.
cbn in Hla.
apply in_map_iff in Hla.
destruct Hla as (i & Hin & Hi).
subst la; cbn.
now do 2 rewrite List_map_seq_length.
Qed.

Theorem mI_is_correct_matrix : ∀ n, is_correct_matrix (mI n).
Proof.
intros.
apply squ_mat_is_corr, mI_is_square_matrix.
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
rewrite (List_map_hd []); [ | easy ].
do 2 rewrite map_length.
rewrite fold_mat_nrows, fold_mat_ncols.
split; [ easy | ].
intros la Hla.
apply in_map_iff in Hla.
destruct Hla as (lb & Hla & Hlb); subst la.
rewrite map_length.
now apply Hc.
Qed.

Theorem mI_square_matrix_prop : ∀ n,
  (mat_nrows (mI n) =? n) && is_square_matrix (mI n) = true.
Proof.
intros.
apply Bool.andb_true_iff.
split; [ | apply mI_is_square_matrix ].
cbn; rewrite List_map_seq_length.
apply Nat.eqb_refl.
Qed.

Definition smI n : square_matrix n T :=
  {| sm_mat := mI n;
     sm_prop := mI_square_matrix_prop n |}.

Theorem squ_mat_add_is_squ : ∀ (MA MB : matrix T),
  is_square_matrix MA = true
  → is_square_matrix MB = true
  → is_square_matrix (MA + MB) = true.
Proof.
intros * Ha Hb.
apply is_sm_mat_iff; cbn.
apply is_sm_mat_iff in Ha.
apply is_sm_mat_iff in Hb.
destruct Ha as (Hcra & Hca).
destruct Hb as (Hcrb & Hcb).
split. {
  intros Hcc.
  rewrite map2_length.
  do 2 rewrite fold_mat_nrows.
  unfold mat_ncols in Hcc; cbn in Hcc.
  destruct (Nat.eq_dec (mat_nrows MA) 0) as [Hraz| Hraz]. {
    now rewrite Hraz, Nat.min_0_l.
  }
  destruct (Nat.eq_dec (mat_nrows MB) 0) as [Hrbz| Hrbz]. {
    now rewrite Hrbz, Nat.min_0_r.
  }
  apply Nat.neq_0_lt_0 in Hraz, Hrbz.
  rewrite List_hd_nth_0 in Hcc.
  rewrite map2_nth with (a := []) (b := []) in Hcc; [ | easy | easy ].
  rewrite map2_length in Hcc.
  do 2 rewrite <- List_hd_nth_0 in Hcc.
  do 2 rewrite fold_mat_ncols in Hcc.
  apply Nat.le_0_r, Nat.min_le in Hcc.
  destruct Hcc as [Hc| Hc]; apply Nat.le_0_r in Hc. {
    now rewrite Hcra in Hraz.
  } {
    now rewrite Hcrb in Hrbz.
  }
} {
  intros l Hl.
  apply in_map2_iff in Hl.
  destruct Hl as (i & Him & a & b & Hl).
  subst l.
  do 2 rewrite map2_length.
  do 2 rewrite fold_mat_nrows in Him |-*.
  apply Nat.min_glb_lt_iff in Him.
  rewrite Hca; [ | now apply nth_In; rewrite fold_mat_nrows ].
  rewrite Hcb; [ | now apply nth_In; rewrite fold_mat_nrows ].
  easy.
}
Qed.

Theorem square_matrix_add_is_square : ∀ n (MA MB : square_matrix n T),
  is_square_matrix (sm_mat MA + sm_mat MB)%M = true.
Proof.
intros.
destruct MA as (MA & Ha).
destruct MB as (MB & Hb); cbn.
apply Bool.andb_true_iff in Ha, Hb.
now apply squ_mat_add_is_squ.
Qed.

Theorem square_matrix_add_prop : ∀ n (MA MB : square_matrix n T),
  (mat_nrows (sm_mat MA + sm_mat MB) =? n) &&
  is_square_matrix (sm_mat MA + sm_mat MB) = true.
Proof.
intros.
apply Bool.andb_true_iff.
split; [ | apply square_matrix_add_is_square ].
apply Nat.eqb_eq; cbn.
rewrite map2_length.
do 2 rewrite fold_mat_nrows.
do 2 rewrite squ_mat_nrows.
apply Nat.min_id.
Qed.

Definition square_matrix_add {n} (MA MB : square_matrix n T) :
  square_matrix n T :=
  {| sm_mat := (sm_mat MA + sm_mat MB);
     sm_prop := square_matrix_add_prop MA MB |}.

Theorem square_matrix_mul_is_square : ∀ n (MA MB : square_matrix n T),
  is_square_matrix (sm_mat MA * sm_mat MB) = true.
Proof.
intros.
apply is_sm_mat_iff.
(*
split; cbn. {
  rewrite List_map_seq_length.
Check squ_mat_nrows.
  apply squ_mat_nrows.
}
*)
split. {
  intros Hc; cbn.
  rewrite List_map_seq_length.
  destruct MA as (MA & Ha).
  destruct MB as (MB & Hb).
  move MB before MA; cbn in Hc |-*.
  apply Bool.andb_true_iff in Ha, Hb.
  destruct Ha as (Hra, Ha).
  destruct Hb as (Hrb, Hb).
  move Hrb before Hra.
  apply Nat.eqb_eq in Hra, Hrb.
  apply is_sm_mat_iff in Ha.
  apply is_sm_mat_iff in Hb.
  destruct Ha as (Hcra & Hca).
  destruct Hb as (Hcrb & Hcb).
  move Hcrb before Hcra.
  unfold mat_ncols in Hc; cbn in Hc.
  apply length_zero_iff_nil in Hc.
  destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
  apply Nat.neq_0_lt_0 in Hnz.
  rewrite (List_map_hd 0) in Hc. 2: {
    now rewrite seq_length, Hra.
  }
  apply map_eq_nil in Hc.
  apply List_seq_eq_nil in Hc.
  apply Hcrb in Hc.
  now rewrite <- Hrb, Hc in Hnz.
} {
  intros l Hl.
  unfold mat_nrows; cbn.
  apply in_map_iff in Hl.
  destruct Hl as (i & Him & Hl).
  subst l.
  do 2 rewrite List_map_seq_length.
  now rewrite squ_mat_nrows, squ_mat_ncols.
}
Qed.

Theorem square_matrix_mul_prop : ∀ n (MA MB : square_matrix n T),
  (mat_nrows (sm_mat MA * sm_mat MB) =? n) &&
  is_square_matrix (sm_mat MA * sm_mat MB) = true.
Proof.
intros.
apply Bool.andb_true_iff.
split; [ | apply square_matrix_mul_is_square ].
apply Nat.eqb_eq; cbn.
rewrite List_map_seq_length.
apply squ_mat_nrows.
Qed.

Definition square_matrix_mul {n} (MA MB : square_matrix n T) :
  square_matrix n T :=
  {| sm_mat := sm_mat MA * sm_mat MB;
     sm_prop := square_matrix_mul_prop MA MB |}.

Theorem square_matrix_opp_is_square : ∀ n (M : square_matrix n T),
  is_square_matrix (- sm_mat M)%M = true.
Proof.
intros.
apply is_sm_mat_iff.
split. {
  intros Hco; cbn.
  rewrite map_length.
  rewrite fold_mat_nrows.
  rewrite squ_mat_nrows.
  destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ easy | exfalso ].
  apply Nat.neq_0_lt_0 in Hnz.
  unfold mat_ncols in Hco.
  cbn in Hco.
  apply length_zero_iff_nil in Hco.
  rewrite (List_map_hd []) in Hco. 2: {
    now rewrite fold_mat_nrows, squ_mat_nrows.
  }
  apply map_eq_nil in Hco.
  apply (f_equal length) in Hco.
  rewrite fold_mat_ncols in Hco.
  rewrite squ_mat_ncols in Hco.
  now rewrite Hco in Hnz.
} {
  intros l Hl.
  destruct M as (M & Hrc); cbn in Hl |-*.
  apply Bool.andb_true_iff in Hrc.
  destruct Hrc as (Hr, Hsm).
  apply Nat.eqb_eq in Hr.
  apply is_sm_mat_iff in Hsm.
  destruct Hsm as (Hrc, Hc).
  rewrite Hr in Hrc, Hc.
  rewrite map_length, fold_mat_nrows, Hr.
  apply in_map_iff in Hl.
  destruct Hl as (la & Hlm & Hla).
  subst l.
  rewrite map_length.
  now apply Hc.
}
Qed.

Theorem square_matrix_opp_prop : ∀ n (M : square_matrix n T),
  (mat_nrows (- sm_mat M) =? n) && is_square_matrix (- sm_mat M) = true.
Proof.
intros.
apply Bool.andb_true_iff.
split; [ | apply square_matrix_opp_is_square ].
apply Nat.eqb_eq; cbn.
rewrite map_length.
apply squ_mat_nrows.
Qed.

Definition square_matrix_opp {n} (M : square_matrix n T) :
  square_matrix n T :=
  {| sm_mat := - sm_mat M;
     sm_prop := square_matrix_opp_prop M |}.

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

Theorem squ_mat_mul_scal_l_is_squ : ∀ (M : matrix T) μ,
  is_square_matrix M = true
  → is_square_matrix (μ × M) = true.
Proof.
intros * Hm.
apply is_sm_mat_iff in Hm.
apply is_sm_mat_iff.
destruct Hm as (Hcr & Hc).
cbn; rewrite map_length, fold_mat_nrows.
split. {
  intros H1.
  destruct (Nat.eq_dec (mat_nrows M) 0) as [Hrz| Hrz]; [ easy | ].
  apply Nat.neq_0_lt_0 in Hrz.
  apply Hcr.
  unfold mat_ncols in H1 |-*; cbn in H1 |-*.
  rewrite (List_map_hd []) in H1; [ | easy ].
  now rewrite map_length in H1.
}
intros la Hla.
apply in_map_iff in Hla.
destruct Hla as (lb & Hla & Hi); subst la.
rewrite map_length.
now apply Hc.
Qed.

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
  if rngl_has_1_neq_0 && (n ≠? 0) then @mI T ro n ≠ mZ n n
  else not_applicable.
Proof.
intros.
remember (rngl_has_1_neq_0 && n ≠? 0) as b eqn:Hb.
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
apply Bool.andb_true_iff in Hm.
destruct Hm as (Hr, Hm).
now apply squ_mat_is_corr.
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
apply Bool.andb_true_iff in Ha, Hb, Hc.
destruct Ha as (Hra, Ha).
destruct Hb as (Hrb, Hb).
destruct Hc as (Hrc, Hc).
apply Nat.eqb_eq in Hra, Hrb, Hrc.
move MB before MA; move MC before MB.
move Hrb before Hra; move Hrc before Hrb.
apply is_sm_mat_iff in Ha.
apply is_sm_mat_iff in Hb.
apply is_sm_mat_iff in Hc.
destruct Ha as (Hcra & Hca).
destruct Hb as (Hcrb & Hcb).
destruct Hc as (Hcrc & Hcc).
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
  rewrite Hra in Hca.
  apply Hca.
  apply List_hd_in, Nat.neq_0_lt_0.
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
apply Bool.andb_true_iff in Ha, Hb, Hc.
destruct Ha as (Hra, Ha).
destruct Hb as (Hrb, Hb).
destruct Hc as (Hrc, Hc).
apply Nat.eqb_eq in Hra, Hrb, Hrc.
move MB before MA; move MC before MB.
move Hrb before Hra; move Hrc before Hrb.
apply is_sm_mat_iff in Ha.
apply is_sm_mat_iff in Hb.
apply is_sm_mat_iff in Hc.
destruct Ha as (Hcra & Hca).
destruct Hb as (Hcrb & Hcb).
destruct Hc as (Hcrc & Hcc).
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
  apply List_hd_in, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hrb.
} {
  split; [ easy | ].
  intros l Hl.
  rewrite Hcc; [ | easy ].
  symmetry; apply Hcc.
  apply List_hd_in, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hrc.
} {
  now rewrite Hrb.
} {
  rewrite Hrb; unfold mat_ncols.
  rewrite Hra in Hca.
  apply Hca.
  apply List_hd_in, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hra.
} {
  congruence.
} {
  unfold mat_ncols.
  rewrite Hcb. 2: {
    apply List_hd_in, Nat.neq_0_lt_0.
    now rewrite fold_mat_nrows, Hrb.
  }
  rewrite Hcc. 2: {
    apply List_hd_in, Nat.neq_0_lt_0.
    now rewrite fold_mat_nrows, Hrc.
  }
  congruence.
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
apply Bool.andb_true_iff in Ha, Hb, Hc.
destruct Ha as (Hra, Ha).
destruct Hb as (Hrb, Hb).
destruct Hc as (Hrc, Hc).
apply Nat.eqb_eq in Hra, Hrb, Hrc.
move MB before MA; move MC before MB.
move Hrb before Hra; move Hrc before Hrb.
apply is_sm_mat_iff in Ha.
apply is_sm_mat_iff in Hb.
apply is_sm_mat_iff in Hc.
destruct Ha as (Hcra & Hca).
destruct Hb as (Hcrb & Hcb).
destruct Hc as (Hcrc & Hcc).
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
  apply List_hd_in, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hra.
} {
  split; [ easy | ].
  intros l Hl.
  rewrite Hcb; [ | easy ].
  symmetry; apply Hcb.
  apply List_hd_in, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hrb.
} {
  now rewrite Hra.
} {
  congruence.
} {
  unfold mat_ncols.
  rewrite Hca. 2: {
    apply List_hd_in, Nat.neq_0_lt_0.
    now rewrite fold_mat_nrows, Hra.
  }
  rewrite Hcb. 2: {
    apply List_hd_in, Nat.neq_0_lt_0.
    now rewrite fold_mat_nrows, Hrb.
  }
  congruence.
}
Qed.

Theorem squ_mat_opt_1_neq_0 {n} :
  if rngl_has_1_neq_0 && (n ≠? 0) then
    @rngl_one (square_matrix n T) (mat_ring_like_op n) ≠
    @rngl_zero (square_matrix n T) (mat_ring_like_op n)
  else not_applicable.
(*
  if rngl_has_1_neq_0 && negb (n =? 0) then 1%F ≠ 0%F else not_applicable.
*)
Proof.
remember (rngl_has_1_neq_0 && (n ≠? 0)) as b eqn:Hb.
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
apply Bool.andb_true_iff in Hs.
destruct Hs as (Hr, Hs).
apply Nat.eqb_eq in Hr.
apply is_sm_mat_iff in Hs.
destruct Hs as (Hcr & Hc).
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n; cbn.
  unfold mat_opp, "+"%M, mZ; cbn.
  apply length_zero_iff_nil in Hr.
  now rewrite Hr.
}
apply mat_add_opp_l; [ | easy | ]. 2: {
  unfold mat_ncols.
  rewrite Hr in Hc.
  symmetry; apply Hc.
  apply List_hd_in, Nat.neq_0_lt_0.
  now rewrite fold_mat_nrows, Hr.
}
split; [ easy | ].
intros l Hl.
unfold mat_ncols.
rewrite Hc; [ | easy ].
symmetry; apply Hc.
apply List_hd_in, Nat.neq_0_lt_0.
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
rewrite List_map_seq_length.
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
  now rewrite List_map_seq_length.
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
  apply Bool.andb_true_iff in Hm.
  destruct Hm as (Hr, Hm).
  apply Nat.eqb_eq in Hr.
  apply is_sm_mat_iff in Hm.
  destruct Hm as (Hcr & Hc).
  rewrite Hr in Hc.
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
    rewrite map2_length, List_map_seq_length.
    rewrite fold_mat_nrows.
    flia Hnz IHi.
  }
  rewrite map2_nth with (a := 0%F) (b := 0%F) in Hi; cycle 1. {
    now rewrite List_map_seq_length.
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
     rngl_has_1_neq_0 := rngl_has_1_neq_0 && (n ≠? 0);
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
rewrite (List_map_nth_seq lla) with (d := []) at 1.
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
Arguments mat_list_list {T}%type m%M.
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
Arguments mat_repl_vect_is_square {T}%type {ro} [k]%nat M%M V%V.
Arguments mat_sub {T ro} MA%M MB%M.
Arguments mat_transp {T ro} M%M.
Arguments mI {T ro} n%nat.
Arguments mZ {T ro} (m n)%nat.
Arguments minus_one_pow {T ro}.
Arguments subm {T} M%M i%nat j%nat.
Arguments subm_subm' {T}%type {ro} M%M (i j)%nat.
Arguments mat_vect_mul_1_l {T}%type {ro rp} Hro {n}%nat V%V.
Arguments δ {T}%type {ro} (i j)%nat.
Arguments matrix_eq {T ro} (MA MB)%M.
Arguments matrix_eq' {T ro} (MA MB)%M.
Arguments is_correct_matrix {T}%type M%M.
Arguments is_square_matrix {T}%type M%M.
Arguments mI_is_correct_matrix {T}%type {ro} n%nat.
Arguments square_matrix_ncols {T}%type M%M.
Arguments Build_square_matrix n%nat [T]%type sm_mat%M.

Notation "A + B" := (mat_add A B) : M_scope.
Notation "A - B" := (mat_sub A B) : M_scope.
Notation "A * B" := (mat_mul A B) : M_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.
Notation "- A" := (mat_opp A) : M_scope.
Notation "A ⁺" := (mat_transp A) (at level 1, format "A ⁺") : M_scope.
Notation "A • V" := (mat_mul_vect_r A V) (at level 40) : M_scope.
Notation "A • V" := (mat_mul_vect_r A V) (at level 40) : V_scope.

End matrix_Notations.
