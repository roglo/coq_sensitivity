(* matrices *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Bool.
Import List List.ListNotations.
Require Import Init.Nat.

Require Import Misc.
Require Import RingLike IterAdd IterMul IterAnd.
Require Import MyVector Signature.

(* matrices *)

Record matrix T := mk_mat
  { mat_list_list : list (list T) }.

Definition mat_nrows {T} (M : matrix T) := length (mat_list_list M).
Definition mat_ncols {T} (M : matrix T) := length (hd [] (mat_list_list M)).
Definition mat_el {T} {ro : ring_like_op T} (M : matrix T) i j :=
  nth (j - 1) (nth (i - 1) (mat_list_list M) []) 0%L.

(* *)

Definition mat_eqb {T} (eqb : T → T → bool) (A B : matrix T) :=
  list_eqv (list_eqv eqb) (mat_list_list A) (mat_list_list B).

(* correct_matrix: matrix whose list list is made of non
   empty lists (rows) of same length *)

Definition is_correct_matrix {T} (M : matrix T) :=
  ((mat_ncols M ≠? 0) || (mat_nrows M =? 0)) &&
  (⋀ (l ∈ mat_list_list M), (length l =? mat_ncols M)).

(* square_matrix: matrix whose list list is mode of non
   empty lists of same length as the list list  *)

Definition is_square_matrix {T} (M : matrix T) :=
  ((mat_ncols M ≠? 0) || (mat_nrows M =? 0)) &&
  (⋀ (l ∈ mat_list_list M), (length l =? mat_nrows M)).

(* mat_eqb is an equality *)

Theorem mat_eqb_eq : ∀ T (eqb : T → T → bool),
  equality eqb →
  ∀ (A B : matrix T),
  mat_eqb eqb A B = true ↔ A = B.
Proof.
intros * Heqb *.
split; intros Hab. {
  unfold mat_eqb in Hab.
  apply list_eqb_eq in Hab; [ | now apply -> equality_list_eqv ].
  destruct A as (lla).
  destruct B as (llb).
  now cbn in Hab; f_equal.
} {
  subst B.
  apply list_eqb_eq; [ | easy ].
  now apply -> equality_list_eqv.
}
Qed.

(* is_correct_matrix (a bool) easier to use with Prop *)

Theorem is_scm_mat_iff {T} : ∀ f (M : matrix T),
  ((mat_ncols M ≠? 0) || (mat_nrows M =? 0)) &&
  (⋀ (l ∈ mat_list_list M), (length l =? f)) = true ↔
  (mat_ncols M = 0 → mat_nrows M = 0) ∧
  ∀ l, l ∈ mat_list_list M → length l = f.
Proof.
intros.
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
  rewrite and_list_cons in Hc.
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
  rewrite and_list_cons.
  apply Bool.andb_true_iff.
  split; [ now apply Nat.eqb_eq, Hc; left | ].
  apply IHll.
  intros l Hl.
  now apply Hc; right.
}
Qed.

Theorem tail_is_correct_matrix : ∀ {A} (M : matrix A),
  is_correct_matrix M = true
  → is_correct_matrix (mk_mat (tl (mat_list_list M))) = true.
Proof.
intros * Hcm.
apply is_scm_mat_iff in Hcm.
apply is_scm_mat_iff.
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

Theorem matrix_eq : ∀ T (ro : ring_like_op T) MA MB,
  (∀ i j, 1 ≤ i ≤ mat_nrows MA → 1 ≤ j ≤ mat_ncols MB →
   mat_el MA i j = mat_el MB i j)
  → is_correct_matrix MA = true
  → is_correct_matrix MB = true
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
  apply nth_ext with (d := 0%L) (d' := 0%L); [ easy | ].
  intros i Hi.
  unfold mat_ncols in Hij.
  cbn - [ nth ] in Hij.
  specialize (Hij 1 (i + 1)).
  rewrite Nat.add_sub, Nat.sub_diag in Hij; cbn in Hij.
  apply Hij. {
    split; [ easy | ].
    now apply -> Nat.succ_le_mono.
  }
  rewrite Nat.add_1_r.
  split; [ now apply -> Nat.succ_le_mono | ].
  now rewrite <- Hcc.
}
apply IHlen; [ easy | easy | | | | ]; cycle 1. {
  apply is_scm_mat_iff in Ha.
  apply is_scm_mat_iff in Hb.
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
assert (H : 1 ≤ S i ≤ S len). {
  now split; apply -> Nat.succ_le_mono.
}
specialize (H1 H); clear H.
destruct i; [ easy | ].
rewrite Nat_sub_succ_1 in H1 |-*.
rewrite List_nth_succ_cons in H1.
apply H1.
split; [ easy | ].
apply is_scm_mat_iff in Hb.
destruct Hb as (Hb1, Hb2).
unfold mat_ncols in Hb2; cbn in Hb2.
destruct llb as [| lb']; cbn in Hj; [ flia Hj | ].
specialize (Hb2 lb' (or_intror (or_introl eq_refl))).
now rewrite Hb2 in Hj.
Qed.

Theorem fold_mat_nrows {T} : ∀ (M : matrix T),
  length (mat_list_list M) = mat_nrows M.
Proof. easy. Qed.

Theorem fold_mat_ncols {T} : ∀ (M : matrix T),
  length (hd [] (mat_list_list M)) = mat_ncols M.
Proof. easy. Qed.

Theorem fold_mat_el {T} {ro : ring_like_op T} : ∀ (M : matrix T) i j,
  nth j (nth i (mat_list_list M) []) 0%L = mat_el M (S i) (S j).
Proof.
intros.
unfold mat_el.
now do 2 rewrite Nat_sub_succ_1.
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

Record correct_matrix T := mk_cm
  { cm_mat : matrix T;
    cm_prop : is_correct_matrix cm_mat = true }.

Theorem fold_corr_mat_ncols {T} : ∀ (M : matrix T) d,
  is_correct_matrix M = true
  → ∀ i, i < mat_nrows M
  → length (nth i (mat_list_list M) d) = mat_ncols M.
Proof.
intros * Hm * Him.
apply is_scm_mat_iff in Hm.
destruct Hm as (Hcr, Hc).
apply Hc.
apply nth_In.
now rewrite fold_mat_nrows.
Qed.

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

Theorem square_matrix_ncols {T} : ∀ (M : matrix T),
  is_square_matrix M = true
  → mat_ncols M = mat_nrows M.
Proof.
intros * Hm.
apply is_scm_mat_iff in Hm.
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
  → is_correct_matrix M = true.
Proof.
intros * Hsm.
specialize (square_matrix_ncols _ Hsm) as Hc.
apply is_scm_mat_iff in Hsm.
apply is_scm_mat_iff.
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

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.

(* addition *)

Definition mat_add (MA MB : matrix T) : matrix T :=
  mk_mat (map2 (map2 rngl_add) (mat_list_list MA) (mat_list_list MB)).

(* multiplication *)

Definition mat_mul_el MA MB i k :=
   ∑ (j = 1, mat_ncols MA), mat_el MA i j * mat_el MB j k.

Definition mat_mul (MA MB : matrix T) : matrix T :=
  mk_mat
    (map (λ i, map (mat_mul_el MA MB i) (seq 1 (mat_ncols MB)))
       (seq 1 (mat_nrows MA))).

(* opposite *)

Definition mat_opp (M : matrix T) : matrix T :=
  mk_mat (map (map rngl_opp) (mat_list_list M)).

(* subtraction *)

Definition mat_sub (MA MB : matrix T) :=
  mat_add MA (mat_opp MB).

(* vector as a matrix nx1 *)

Definition mat_of_vert_vect (V : vector T) :=
  mk_mat (map (λ i, [i]) (vect_list V)).

(* vector as a matrix 1xn *)

Definition mat_of_horiz_vect (V : vector T) :=
  mk_mat [vect_list V].

(* concatenation of a matrix and a column vector *)

Definition mat_vect_concat (M : matrix T) V :=
  mk_mat (map2 (λ row e, row ++ [e]) (mat_list_list M) (vect_list V)).

(* multiplication of a matrix and a vector *)

Definition mat_mul_vect_r (M : matrix T) (V : vector T) :=
  mk_vect (map (λ row, vect_dot_mul (mk_vect row) V) (mat_list_list M)).

(*
Definition mat_mul_vect_r' (M : matrix T) (V : vector T) :=
  mk_vect
    match vect_list V with
    | nil => []
    | cons d _ => map (hd d) (mat_list_list (mat_mul M (mat_of_vert_vect V)))
  end.
*)

(* multiplication of a vector and a matrix *)

(* to be analyzed and completed
Definition mat_mul_vect_l (V : vector T) (M : matrix T) :=
  mk_vect (map (λ row, vect_dot_mul (mk_vect row) V) (mat_list_list M)).
*)

(* multiplication of a matrix by a scalar *)

Definition mat_mul_scal_l s (M : matrix T) :=
  mk_mat (map (map (rngl_mul s)) (mat_list_list M)).

(* matrix whose k-th column is replaced by a vector *)

Definition mat_repl_vect' k (M : matrix T) (V : vector T) :=
  mk_mat (map2 (replace_at (k - 1)) (mat_list_list M) (vect_list V)).

Theorem mat_el_repl_vect : ∀ (M : matrix T) V i j k,
  is_correct_matrix M = true
  → i ≤ vect_size V
  → 1 ≤ i ≤ mat_nrows M
  → 1 ≤ j ≤ mat_ncols M
  → 1 ≤ k ≤ mat_ncols M
  → mat_el (mat_repl_vect' k M V) i j =
    if Nat.eq_dec j k then vect_el V i else mat_el M i j.
Proof.
intros * Hm His Hir Hjc Hkc; cbn.
rewrite map2_nth with (a := []) (b := 0%L); cycle 1. {
  rewrite fold_mat_nrows.
  now apply Nat_1_le_sub_lt.
} {
  rewrite fold_vect_size.
  now apply Nat_1_le_sub_lt.
}
unfold replace_at.
destruct (Nat.eq_dec j k) as [Hjk| Hjk]. {
  subst k.
  rewrite app_nth2. 2: {
    rewrite firstn_length.
    rewrite fold_corr_mat_ncols; [ | easy | now apply Nat_1_le_sub_lt ].
    unfold ge.
    rewrite Nat.min_l; [ easy | flia Hjc ].
  }
  rewrite firstn_length.
  rewrite fold_corr_mat_ncols; [ | easy | now apply Nat_1_le_sub_lt ].
  rewrite Nat.min_l; [ | flia Hjc ].
  now rewrite Nat.sub_diag.
}
destruct (lt_dec j k) as [Hljk| Hljk]. {
  rewrite app_nth1. 2: {
    rewrite firstn_length.
    rewrite fold_corr_mat_ncols; [ | easy | now apply Nat_1_le_sub_lt ].
    rewrite Nat.min_l; [ | flia Hkc ].
    apply Nat_1_le_sub_lt.
    split; [ easy | flia Hjk Hljk ].
  }
  rewrite List_nth_firstn; [ easy | flia Hjc Hljk ].
} {
  apply Nat.nlt_ge in Hljk.
  rewrite app_nth2. 2: {
    rewrite firstn_length.
    rewrite fold_corr_mat_ncols; [ | easy | now apply Nat_1_le_sub_lt ].
    rewrite Nat.min_l; [ flia Hjc Hljk | flia Hkc ].
  }
  rewrite firstn_length.
  rewrite fold_corr_mat_ncols; [ | easy | now apply Nat_1_le_sub_lt ].
  rewrite Nat.min_l; [ | flia Hkc ].
  rewrite Nat_succ_sub_succ_r; [ | flia Hkc Hjk Hljk ].
  cbn - [ skipn ].
  rewrite List_nth_skipn.
  rewrite Nat.sub_add; [ easy | flia Hkc Hjk Hljk ].
}
Qed.

Theorem mat_repl_vect_nrows : ∀ k (M : matrix T) V,
  vect_size V = mat_nrows M
  → mat_nrows (mat_repl_vect' k M V) = mat_nrows M.
Proof.
intros * Hv; cbn.
rewrite map2_length.
rewrite fold_mat_nrows, fold_vect_size, Hv.
apply Nat.min_id.
Qed.

Theorem mat_repl_vect_ncols : ∀ k (M : matrix T) V,
  1 ≤ k ≤ mat_ncols M
  → vect_size V = mat_ncols M
  → mat_ncols (mat_repl_vect' k M V) = mat_ncols M.
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
rewrite map2_nth with (a := []) (b := 0%L); cycle 1. {
  now rewrite fold_mat_nrows.
} {
  now rewrite fold_vect_size, Hv.
}
unfold replace_at.
rewrite app_length.
rewrite firstn_length.
rewrite <- List_hd_nth_0.
rewrite fold_mat_ncols.
rewrite List_cons_length.
rewrite skipn_length.
rewrite fold_mat_ncols.
flia Hkc.
Qed.

Theorem mat_repl_vect_is_square : ∀ k (M : matrix T) V,
  1 ≤ k ≤ mat_ncols M
  → vect_size V = mat_nrows M
  → is_square_matrix M = true
  → is_square_matrix (mat_repl_vect' k M V) = true.
Proof.
intros * Hkc Hv Hm.
specialize (square_matrix_ncols _ Hm) as Hcn.
apply is_scm_mat_iff in Hm.
apply is_scm_mat_iff.
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
    apply is_scm_mat_iff.
    split; [ easy | now rewrite Hcn ].
  }
  rewrite Nat.min_l; [ | flia Hkc ].
  rewrite Hcn in Hkc |-*.
  flia Hkc.
}
Qed.

(* null matrix of dimension m × n *)

Definition mZ m n : matrix T :=
  mk_mat (repeat (repeat 0%L n) m).

(* identity square matrix of dimension n *)

Definition δ i j := if i =? j then 1%L else 0%L.
Definition mI n : matrix T := mk_mat (map (λ i, map (δ i) (seq 0 n)) (seq 0 n)).

Theorem δ_diag : ∀ i, δ i i = 1%L.
Proof.
intros.
unfold δ.
now rewrite Nat.eqb_refl.
Qed.

Theorem δ_ndiag : ∀ i j, i ≠ j → δ i j = 0%L.
Proof.
intros * Hij.
unfold δ.
rewrite if_eqb_eq_dec.
now destruct (Nat.eq_dec i j).
Qed.

Theorem mI_any_seq_start : ∀ sta len,
  mI len = mk_mat (map (λ i, map (δ i) (seq sta len)) (seq sta len)).
Proof.
intros.
unfold mI; f_equal.
symmetry.
rewrite List_map_seq.
apply map_ext_in.
intros i Hi.
rewrite List_map_seq.
apply map_ext_in.
intros j Hj.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  now subst j; do 2 rewrite δ_diag.
}
rewrite δ_ndiag; [ | flia Hij ].
now rewrite δ_ndiag.
Qed.

End a.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.
Context {Hop : @rngl_has_opp T ro = true}.

Declare Scope M_scope.
Delimit Scope M_scope with M.

Arguments δ {T ro} (i j)%nat.

Arguments matrix_eq {T}%type {ro} (MA MB)%M.
Arguments mat_add {T ro} MA%M MB%M.
Arguments mat_mul {T ro} MA%M MB%M.
Arguments mat_mul_el {T}%type {ro} (MA MB)%M (i k)%nat.
Arguments mat_mul_scal_l {T ro} s%L M%M.
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
  is_correct_matrix M = true
  → m = mat_nrows M
  → n = mat_ncols M
  → (mZ m n + M)%M = M.
Proof.
intros * HM Hr Hc.
subst m n.
apply is_scm_mat_iff in HM.
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
  is_correct_matrix M = true
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
  is_correct_matrix M = true
  → m = mat_nrows M
  → n = mat_ncols M
  → (- M + M = mZ m n)%M.
Proof.
intros * HM Hr Hc.
subst m n.
apply is_scm_mat_iff in HM.
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
  is_correct_matrix M = true
  → (M - M = mZ (mat_nrows M) (mat_ncols M))%M.
Proof.
intros * HM.
unfold mat_sub.
rewrite mat_add_comm.
now apply mat_add_opp_l.
Qed.

Theorem mat_add_sub :
  ∀ MA MB : matrix T,
  is_correct_matrix MA = true
  → is_correct_matrix MB = true
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

Theorem mat_el_mI_ndiag : ∀ n i j,
  1 ≤ i
  → 1 ≤ j
  → i ≠ j
  → mat_el (mI n) i j = 0%L.
Proof.
intros * Hi Hj Hij.
unfold mat_el, mI; cbn.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  rewrite Tauto_match_nat_same.
  now rewrite List_nth_nil.
}
apply Nat.neq_0_lt_0 in Hnz.
destruct (le_dec i n) as [Hin| Hin]. {
  rewrite List_map_nth' with (a := 0); [ | rewrite seq_length; flia Hi Hin ].
  destruct (le_dec j n) as [Hjn| Hjn]. {
    rewrite List_map_nth' with (a := 0). 2: {
      rewrite seq_length; flia Hj Hjn.
    }
    rewrite seq_nth; [ | flia Hi Hin ].
    rewrite seq_nth; [ cbn | flia Hj Hjn ].
    unfold δ.
    rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec (i - 1) (j - 1)) as [H| ]; [ | easy ].
    flia Hi Hj Hij H.
  }
  apply Nat.nle_gt in Hjn.
  apply nth_overflow.
  rewrite List_map_seq_length.
  flia Hjn.
}
apply Nat.nle_gt in Hin.
apply nth_overflow.
rewrite nth_overflow; [ cbn; flia | ].
rewrite List_map_seq_length.
flia Hin.
Qed.

Theorem mat_el_mI_diag : ∀ n i, 1 ≤ i ≤ n → mat_el (mI n) i i = 1%L.
Proof.
intros * Hin.
unfold mat_el, mI; cbn.
rewrite List_map_nth' with (a := 0). 2: {
  now rewrite seq_length; apply Nat_1_le_sub_lt.
}
rewrite List_map_nth' with (a := 0). 2: {
  now rewrite seq_length; apply Nat_1_le_sub_lt.
}
rewrite seq_nth; [ | now apply Nat_1_le_sub_lt ].
unfold δ.
now rewrite Nat.eqb_refl.
Qed.

(* *)

Theorem mat_mul_nrows : ∀ MA MB, mat_nrows (MA * MB) = mat_nrows MA.
Proof.
intros; cbn.
now rewrite List_map_seq_length.
Qed.

Theorem mat_mul_ncols : ∀ MA MB,
  mat_nrows MA ≠ 0
  → mat_ncols (MA * MB) = mat_ncols MB.
Proof.
intros * Hraz; unfold mat_ncols; cbn.
rewrite (List_map_hd 0). 2: {
  rewrite seq_length.
  now apply Nat.neq_0_lt_0.
}
now rewrite map_length, seq_length.
Qed.

Theorem mat_el_mul : ∀ MA MB i j,
  1 ≤ i ≤ mat_nrows (MA * MB)
  → 1 ≤ j ≤ mat_ncols (MA * MB)
  → mat_el (MA * MB) i j =
    ∑ (k = 1, mat_ncols MA), mat_el MA i k * mat_el MB k j.
Proof.
intros * Hir Hjc; cbn.
rewrite mat_mul_nrows in Hir.
rewrite mat_mul_ncols in Hjc; [ | flia Hir ].
rewrite (List_map_nth' 0). 2: {
  now rewrite seq_length; apply Nat_1_le_sub_lt.
}
rewrite (List_map_nth' 0). 2: {
  now rewrite seq_length; apply Nat_1_le_sub_lt.
}
rewrite seq_nth; [ | now apply Nat_1_le_sub_lt ].
rewrite seq_nth; [ | now apply Nat_1_le_sub_lt ].
rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
easy.
Qed.

(* multiplication left and right with identity *)

Theorem mat_mul_1_l {n} : ∀ (M : matrix T),
  is_correct_matrix M = true
  → n = mat_nrows M
  → (mI n * M)%M = M.
Proof.
intros * HM Hn; subst n.
specialize (proj2 rngl_has_opp_or_sous_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
apply is_scm_mat_iff in HM.
destruct HM as (_, HM).
unfold "*"%M.
rewrite mI_nrows.
destruct M as (ll); cbn in HM |-*.
f_equal.
unfold mat_ncols; cbn.
remember (length (hd [] ll)) as ncols eqn:Hc.
remember (map _ _) as x.
rewrite List_map_nth_seq with (d := []); subst x.
rewrite <- seq_shift.
rewrite <- seq_shift, map_map.
apply map_ext_in.
intros i Hi.
remember (nth i ll []) as la eqn:Hla.
rewrite List_map_nth_seq with (d := 0%L).
rewrite (HM la). 2: {
  rewrite Hla.
  apply nth_In.
  now apply in_seq in Hi.
}
unfold mat_ncols; cbn.
rewrite <- Hc.
rewrite map_map.
apply map_ext_in.
intros j Hj.
unfold mat_mul_el.
rewrite rngl_summation_split3 with (j := S i). 2: {
  split; [ now apply -> Nat.succ_le_mono | ].
  apply in_seq in Hi.
  rewrite mI_ncols; flia Hi.
}
rewrite all_0_rngl_summation_0. 2: {
  intros k Hk.
  rewrite mat_el_mI_ndiag; [ | flia Hk | flia Hk | flia Hk ].
  now apply rngl_mul_0_l.
}
rewrite rngl_add_0_l.
apply in_seq in Hi.
rewrite mat_el_mI_diag; [ | flia Hi ].
rewrite rngl_mul_1_l.
remember (∑ (k = _, _), _) as x; cbn; subst x.
do 2 rewrite Nat.sub_0_r.
rewrite <- Hla.
rewrite all_0_rngl_summation_0. 2: {
  intros k Hk.
  rewrite mat_el_mI_ndiag; [ | flia Hk | flia Hk | flia Hk ].
  now apply rngl_mul_0_l.
}
apply rngl_add_0_r.
Qed.

Theorem mat_mul_1_r {n} : ∀ (M : matrix T),
  is_correct_matrix M = true
  → n = mat_ncols M
  → (M * mI n)%M = M.
Proof.
intros * HM H; subst n.
specialize (proj2 rngl_has_opp_or_sous_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
apply is_scm_mat_iff in HM.
destruct HM as (_, HM).
unfold "*"%M.
rewrite mI_ncols.
destruct M as (ll); cbn in HM |-*.
f_equal.
unfold mat_ncols; cbn.
remember (length (hd [] ll)) as ncols eqn:Hc.
remember (map _ _) as x.
rewrite List_map_nth_seq with (d := []); subst x.
rewrite <- seq_shift, <- seq_shift, map_map.
apply map_ext_in.
intros i Hi.
remember (nth i ll []) as la eqn:Hla.
rewrite List_map_nth_seq with (d := 0%L).
rewrite (HM la). 2: {
  rewrite Hla.
  apply nth_In.
  now apply in_seq in Hi.
}
unfold mat_ncols; cbn.
rewrite <- Hc, map_map.
apply map_ext_in.
intros j Hj.
unfold mat_mul_el.
unfold mat_ncols at 1.
cbn - [ mat_el ].
destruct ll as [| lb]; [ easy | ].
cbn - [ mat_el ].
rewrite (HM lb (or_introl eq_refl)).
(* rather use more modern rngl_summation_split3... *)
rewrite rngl_summation_split with (j := S j). 2: {
  split; [ now apply -> Nat.succ_le_mono | ].
  apply -> Nat.succ_le_mono.
  apply in_seq in Hj.
  cbn in Hc |-*; rewrite <- Hc.
  flia Hj.
}
rewrite rngl_summation_split_last; [ | now apply -> Nat.succ_le_mono ].
rewrite all_0_rngl_summation_0. 2: {
  intros k Hk.
  rewrite mat_el_mI_ndiag; [ | flia Hk | flia | flia Hk ].
  now apply rngl_mul_0_r.
}
rewrite rngl_add_0_l.
apply in_seq in Hj.
rewrite mat_el_mI_diag; [ | flia Hj ].
rewrite rngl_mul_1_r.
rewrite all_0_rngl_summation_0. 2: {
  intros k Hk.
  rewrite mat_el_mI_ndiag; [ | flia Hk | flia | flia Hk ].
  now apply rngl_mul_0_r.
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
specialize (proj2 rngl_has_opp_or_sous_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
apply vector_eq. 2: {
  now cbn; do 2 rewrite map_length; rewrite seq_length.
}
cbn; do 2 rewrite map_length; rewrite seq_length.
intros i Hi.
rewrite (List_map_nth' []). 2: {
  rewrite List_map_seq_length.
  now apply Nat_1_le_sub_lt.
}
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  now apply Nat_1_le_sub_lt.
}
rewrite seq_nth; [ cbn | now apply Nat_1_le_sub_lt ].
unfold vect_dot_mul; cbn.
destruct V as (l); cbn in Hi |-*.
rewrite map2_map_l.
destruct i; [ easy | ].
rewrite Nat_sub_succ_1.
rewrite (List_seq_cut i); [ cbn | now apply in_seq ].
rewrite Nat.sub_0_r.
rewrite map2_app_l.
rewrite seq_length.
erewrite map2_ext_in. 2: {
  intros j k Hj Hk; apply in_seq in Hj.
  destruct Hj as (_, Hj); cbn in Hj.
  rewrite δ_ndiag; [ | flia Hj ].
  now rewrite rngl_mul_0_l.
}
rewrite rngl_summation_list_app.
rewrite all_0_rngl_summation_list_0. 2: {
  intros j Hj.
  apply in_map2_iff in Hj.
  destruct Hj as (k & Hki & u & v & Hu).
  easy.
}
rewrite rngl_add_0_l.
remember (skipn i l) as l' eqn:Hl'.
symmetry in Hl'.
destruct l' as [| a']. {
  exfalso.
  revert l Hi Hl'.
  induction i; intros; [ now cbn in Hl'; subst l | ].
  destruct l as [| a]; [ easy | ].
  cbn in Hi, Hl'.
  apply (IHi l); [ flia Hi | easy ].
}
cbn.
rewrite δ_diag.
rewrite rngl_mul_1_l.
erewrite map2_ext_in. 2: {
  intros j k Hj Hk; apply in_seq in Hj.
  destruct Hj as (Hj, _).
  rewrite δ_ndiag; [ | flia Hj ].
  now rewrite rngl_mul_0_l.
}
rewrite rngl_summation_list_cons.
rewrite all_0_rngl_summation_list_0. 2: {
  intros j Hj.
  apply in_map2_iff in Hj.
  destruct Hj as (k & Hki & u & v & Hu).
  easy.
}
rewrite rngl_add_0_r.
revert l Hl' Hi.
induction i; intros; [ now cbn in Hl'; subst l | ].
destruct l as [| b]; [ easy | ].
cbn in Hi, Hl' |-*.
apply IHi; [ easy | flia Hi ].
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
specialize (proj2 rngl_has_opp_or_sous_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
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
rewrite (rngl_summation_shift 1); [ | flia Hcarb Hrbz ].
rewrite Nat.sub_diag.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  rewrite List_map_nth' with (a := 0). 2: {
    rewrite seq_length.
    rewrite Hcarb in Hk.
    flia Hrbz Hk.
  }
  rewrite List_map_nth' with (a := 0). 2: {
    rewrite seq_length.
    apply in_seq in Hj.
    apply Nat_1_le_sub_lt.
    flia Hj.
  }
  rewrite (rngl_summation_shift 1); [ | flia Hcbz ].
  rewrite Nat.sub_diag.
  erewrite rngl_summation_eq_compat. 2: {
    intros m Hm.
    rewrite seq_nth; [ | rewrite Hcarb in Hk; flia Hrbz Hk ].
    rewrite seq_nth. 2: {
      apply in_seq in Hj.
      apply Nat_1_le_sub_lt.
      flia Hj.
    }
    easy.
  }
  rewrite rngl_mul_summation_distr_l; [ | easy ].
  erewrite rngl_summation_eq_compat. 2: {
    intros m Hm.
    now rewrite rngl_mul_assoc.
  }
  rewrite Nat.add_comm, Nat.add_sub, Nat.add_1_r.
  apply in_seq in Hj.
  rewrite (Nat.add_comm 1 (j - 1)), Nat.sub_add; [ | easy ].
  easy.
}
cbn.
symmetry.
rewrite (rngl_summation_shift 1); [ | flia Hcbz ].
rewrite Nat.sub_diag.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  rewrite Nat.add_comm, Nat.add_sub.
  rewrite List_map_nth' with (a := 0). 2: {
    rewrite seq_length.
    apply in_seq in Hi; flia Hi.
  }
  rewrite List_map_nth' with (a := 0). 2: {
    rewrite seq_length.
    flia Hcbz Hk.
  }
  rewrite (rngl_summation_shift 1); [ | flia Hcarb Hrbz ].
  rewrite Nat.sub_diag.
  erewrite rngl_summation_eq_compat. 2: {
    intros m Hm.
    rewrite seq_nth; [ | now apply in_seq in Hi; flia Hi ].
    rewrite seq_nth; [ | flia Hcbz Hk ].
    easy.
  }
  rewrite rngl_mul_summation_distr_r; [ | easy ].
  apply in_seq in Hi.
  rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
  rewrite Nat.add_1_r.
  easy.
}
cbn.
symmetry.
apply rngl_summation_summation_list_swap.
Qed.

(* left distributivity of multiplication over addition *)

Theorem mat_mul_add_distr_l :
  ∀ (MA : matrix T) (MB : matrix T) (MC : matrix T),
  is_correct_matrix MB = true
  → is_correct_matrix MC = true
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
rewrite map2_nth with (a := 0%L) (b := 0%L); cycle 1. {
  apply is_scm_mat_iff in Hb.
  destruct Hb as (_, Hb).
  apply in_seq in Hj.
  rewrite Hb; [ flia Hj | ].
  apply nth_In.
  rewrite fold_mat_nrows.
  rewrite Hcarb in Hk.
  flia Hrbz Hk.
} {
  apply in_seq in Hj.
  rewrite fold_corr_mat_ncols; [ now rewrite <- Hcbc; flia Hj | easy | ].
  rewrite <- Hcrbc.
  rewrite Hcarb in Hk.
  flia Hrbz Hk.
}
do 2 rewrite fold_mat_el.
apply in_seq in Hj.
rewrite <- Nat.sub_succ_l; [ | easy ].
rewrite <- Nat.sub_succ_l; [ | easy ].
now do 2 rewrite Nat_sub_succ_1.
Qed.

(* right distributivity of multiplication over addition *)

Theorem mat_mul_add_distr_r :
  ∀ (MA : matrix T) (MB : matrix T) (MC : matrix T),
  is_correct_matrix MA = true
  → is_correct_matrix MB = true
  → mat_nrows MA ≠ 0
  → mat_nrows MA = mat_nrows MB
  → mat_ncols MA = mat_ncols MB
  → ((MA + MB) * MC = MA * MC + MB * MC)%M.
Proof.
intros * Ha Hb Hraz Hrarb Hcacb.
assert (Hcaz : mat_ncols MA ≠ 0). {
  apply is_scm_mat_iff in Ha.
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
  apply in_seq in Hi; flia Hi.
} {
  rewrite fold_mat_nrows, <- Hrarb.
  apply in_seq in Hi; flia Hi.
}
rewrite map2_nth with (a := 0%L) (b := 0%L); cycle 1. {
  apply in_seq in Hi.
  rewrite fold_corr_mat_ncols; [ flia Hcaz Hk | easy | flia Hi ].
} {
  apply in_seq in Hi.
  rewrite Hrarb in Hi.
  rewrite fold_corr_mat_ncols; [ | easy | flia Hi ].
  rewrite <- Hcacb; flia Hcaz Hk.
}
do 2 rewrite fold_mat_el.
apply in_seq in Hi.
rewrite <- Nat.sub_succ_l; [ | easy ].
rewrite <- Nat.sub_succ_l; [ | easy ].
do 2 rewrite Nat_sub_succ_1.
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
  is_correct_matrix M = true
  → is_correct_matrix (μ × M) = true.
Proof.
intros * Hm.
apply is_scm_mat_iff in Hm.
apply is_scm_mat_iff.
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
  ((a + b)%L × M)%M = (a × M + b × M)%M.
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
  (a × (b × M))%M = ((a * b)%L × M)%M.
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
  is_correct_matrix MA = true
  → (a × MA * MB = a × (MA * MB))%M.
Proof.
intros * Ha.
specialize (proj2 rngl_has_opp_or_sous_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
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
rewrite rngl_mul_summation_distr_l; [ | easy ].
apply rngl_summation_eq_compat.
intros k Hk.
rewrite List_map_nth' with (a := []). 2: {
  rewrite fold_mat_nrows.
  apply in_seq in Hi; flia Hi.
}
rewrite List_map_nth' with (a := 0%L). 2: {
  apply is_scm_mat_iff in Ha.
  destruct Ha as (Harc, Ha).
  rewrite Ha. 2: {
    apply nth_In.
    rewrite fold_mat_nrows.
    apply in_seq in Hi; flia Hi.
  }
  assert (Hcaz : mat_ncols MA ≠ 0). {
    intros H; apply Hraz.
    now apply Harc.
  }
  flia Hk Hcaz.
}
rewrite fold_mat_el.
symmetry.
apply in_seq in Hi.
rewrite <- Nat.sub_succ_l; [ | easy ].
rewrite <- Nat.sub_succ_l; [ | easy ].
do 2 rewrite Nat_sub_succ_1.
apply rngl_mul_assoc.
Qed.

Theorem mat_mul_mul_scal_l :
  rngl_mul_is_comm = true →
  ∀ a (MA : matrix T) (MB : matrix T),
  is_correct_matrix MB = true
  → mat_ncols MA ≠ 0
  → mat_ncols MA = mat_nrows MB
  → (MA * (a × MB) = a × (MA * MB))%M.
Proof.
intros Hic * Hb Hcaz Hcarb.
specialize (proj2 rngl_has_opp_or_sous_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
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
rewrite rngl_mul_summation_distr_l; [ | easy ].
apply rngl_summation_eq_compat.
intros k Hk.
rewrite List_map_nth' with (a := []). 2: {
  rewrite fold_mat_nrows, <- Hcarb.
  flia Hcaz Hk.
}
rewrite List_map_nth' with (a := 0%L). 2: {
  apply is_scm_mat_iff in Hb.
  destruct Hb as (Hbzz, Hb).
  rewrite Hb; [ apply in_seq in Hj; flia Hj | ].
  apply nth_In.
  rewrite fold_mat_nrows, <- Hcarb.
  flia Hcaz Hk.
}
rewrite fold_mat_el.
rewrite rngl_mul_comm; [ | easy ].
rewrite <- rngl_mul_assoc.
f_equal.
apply in_seq in Hj.
rewrite <- Nat.sub_succ_l; [ | easy ].
rewrite <- Nat.sub_succ_l; [ | easy ].
do 2 rewrite Nat_sub_succ_1.
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
  1 ≤ i ≤ mat_nrows A
  → ∑ (j = 1, mat_ncols A),
       mat_el A i j *
       (∑ (k = 1, vect_size V), mat_el B j k * vect_el V k) =
     ∑ (j = 1, vect_size V),
       (∑ (k = 1, mat_ncols A), mat_el A i k * mat_el B k j) *
        vect_el V j.
Proof.
intros * Hi.
specialize (proj2 rngl_has_opp_or_sous_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
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
cbn.
unfold iter_seq at 1 2.
rewrite rngl_summation_summation_list_swap.
rewrite fold_iter_seq.
apply rngl_summation_eq_compat.
intros j Hj.
apply rngl_summation_eq_compat.
intros k Hk.
apply rngl_mul_assoc.
Qed.

Theorem mat_vect_mul_assoc :
  ∀ (A : matrix T) (B : matrix T) (V : vector T),
  is_correct_matrix A = true
  → is_correct_matrix B = true
  → mat_ncols A = mat_nrows B
  → mat_ncols B = vect_size V
  → (A • (B • V) = (A * B) • V)%M.
Proof.
intros * Ha Hb Hcarb Hcbv.
specialize (proj2 rngl_has_opp_or_sous_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
unfold "•"%M, "*"%M; cbn.
f_equal.
rewrite map_map.
rewrite List_map_map_seq with (d := []).
rewrite fold_mat_nrows.
(**)
symmetry.
remember (seq 1 (mat_nrows A)) as x eqn:Hx.
rewrite <- seq_shift in Hx; subst x.
rewrite map_map.
symmetry.
(**)
apply map_ext_in.
intros i Hi.
unfold vect_dot_mul; cbn.
rewrite map2_map_r.
rewrite map2_map2_seq_l with (d := 0%L).
rewrite map2_map2_seq_r with (d := []).
apply is_scm_mat_iff in Ha.
destruct Ha as (Harc, Ha).
rewrite Ha. 2: {
  apply nth_In.
  rewrite fold_mat_nrows.
  now apply in_seq in Hi.
}
rewrite fold_mat_nrows.
symmetry.
rewrite map2_map2_seq_r with (d := 0%L).
rewrite fold_vect_size.
symmetry.
rewrite <- Hcarb.
rewrite map2_diag.
rewrite rngl_summation_list_map.
rewrite rngl_summation_seq_summation. 2: {
  intros H; apply Harc in H.
  now rewrite H in Hi.
}
cbn.
apply is_scm_mat_iff in Hb.
destruct Hb as (Hbrc, Hb).
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite fold_mat_el.
  unfold vect_dot_mul; cbn.
  rewrite map2_map2_seq_l with (d := 0%L).
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
  rewrite map2_map2_seq_r with (d := 0%L).
  rewrite fold_vect_size.
  rewrite Hcbv.
  rewrite map2_diag.
  rewrite rngl_summation_list_map.
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
(**)
rewrite <- seq_shift.
rewrite map2_map_l.
rewrite map2_diag.
rewrite rngl_summation_list_map.
rewrite rngl_summation_seq_summation. 2: {
  intros H; rewrite <- Hcbv in H.
  apply Hbrc in H.
  rewrite <- Hcarb in H.
  apply Harc in H.
  now rewrite H in Hi.
}
apply in_seq in Hi.
rewrite rngl_summation_rshift.
rewrite <- Nat.sub_succ_l. 2: {
  destruct (mat_ncols A); [ | flia ].
  now rewrite Harc in Hi.
}
rewrite Nat_sub_succ_1.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite rngl_summation_rshift.
  rewrite <- Nat.sub_succ_l; [ | easy ].
  rewrite Nat_sub_succ_1.
  rewrite <- Hcbv.
  rewrite <- Nat.sub_succ_l. 2: {
    remember (mat_ncols B) as c eqn:Hc; symmetry in Hc.
    destruct c; [ exfalso | flia ].
    rewrite Hbrc in Hcarb; [ | easy ].
    rewrite Hcarb in Hj; flia Hj.
  }
  rewrite Nat_sub_succ_1.
  erewrite rngl_summation_eq_compat. 2: {
    intros k Hk.
    rewrite <- Nat.sub_succ_l; [ | easy ].
    rewrite Nat_sub_succ_1.
    easy.
  }
  easy.
}
rewrite Hcbv.
rewrite mat_vect_mul_assoc_as_sums; [ | flia Hi ].
remember (vect_size V) as s eqn:Hs; symmetry in Hs.
destruct s. {
  rewrite rngl_summation_empty; [ | easy ].
  rewrite rngl_summation_only_one; cbn.
  rewrite Hbrc in Hcarb; [ | easy ].
  destruct A as (lla).
  destruct B as (llb).
  unfold mat_mul_el; cbn.
  rewrite Hcarb.
  rewrite rngl_summation_empty; [ | easy ].
  symmetry.
  now apply rngl_mul_0_l.
}
rewrite (rngl_summation_shift 1). 2: {
  split; [ easy | flia ].
}
rewrite Nat.sub_diag, Nat.add_0_l, Nat_sub_succ_1.
apply rngl_summation_eq_compat.
intros j Hj.
f_equal.
unfold vect_el.
now rewrite Nat.add_comm, Nat.add_sub.
Qed.

Theorem mat_mul_scal_vect_assoc :
  ∀ a (MA : matrix T) (V : vector T),
  is_correct_matrix MA = true
  → mat_ncols MA = vect_size V
  → (a × (MA • V))%V = ((a × MA) • V)%M.
Proof.
intros * Ha Hcav.
specialize (proj2 rngl_has_opp_or_sous_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
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
rewrite rngl_mul_summation_list_distr_l; [ | easy ].
rewrite map2_map2_seq_l with (d := 0%L).
apply is_scm_mat_iff in Ha.
destruct Ha as (Harc, Ha).
rewrite Ha. 2: {
  apply nth_In.
  rewrite fold_mat_nrows.
  now apply in_seq in Hi.
}
rewrite map2_map2_seq_r with (d := 0%L).
rewrite fold_vect_size, Hcav.
rewrite map2_diag.
rewrite rngl_summation_list_map.
rewrite rngl_summation_seq_summation. 2: {
  rewrite <- Hcav; intros H.
  apply Harc in H.
  now rewrite H in Hi.
}
erewrite rngl_summation_eq_compat; [ | easy ].
rewrite map2_map2_seq_l with (d := 0%L).
rewrite Ha. 2: {
  apply nth_In.
  rewrite fold_mat_nrows.
  now apply in_seq in Hi.
}
rewrite map2_map2_seq_r with (d := 0%L).
rewrite fold_vect_size, Hcav.
rewrite map2_diag.
rewrite rngl_summation_list_map.
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
  rngl_mul_is_comm = true →
  ∀ a (MA : matrix T) V,
  is_correct_matrix MA = true
  → mat_ncols MA = vect_size V
  → (a × (MA • V) = MA • (a × V))%V.
Proof.
intros Hic * Ha Hcav.
specialize (proj2 rngl_has_opp_or_sous_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
unfold "×"%V, "•"%M; cbn.
f_equal.
rewrite map_map.
do 2 rewrite List_map_map_seq with (d := []).
rewrite fold_mat_nrows.
apply map_ext_in.
intros i Hi.
unfold vect_dot_mul; cbn.
rewrite rngl_mul_summation_list_distr_l; [ | easy ].
rewrite map2_map_r.
rewrite map2_map2_seq_l with (d := 0%L).
rewrite map2_map2_seq_r with (d := 0%L).
rewrite fold_vect_size.
apply is_scm_mat_iff in Ha.
destruct Ha as (Harc, Ha).
rewrite Ha. 2: {
  apply nth_In.
  rewrite fold_mat_nrows.
  now apply in_seq in Hi.
}
symmetry.
rewrite map2_map2_seq_l with (d := 0%L).
rewrite map2_map2_seq_r with (d := 0%L).
rewrite fold_vect_size.
rewrite Ha. 2: {
  apply nth_In.
  rewrite fold_mat_nrows.
  now apply in_seq in Hi.
}
rewrite Hcav.
do 2 rewrite map2_diag.
do 2 rewrite rngl_summation_list_map.
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
    (map (λ j, map (λ i, mat_el M i j) (seq 1 (mat_nrows M)))
       (seq 1 (mat_ncols M))).

Notation "A ⁺" := (mat_transp A) (at level 1, format "A ⁺") : M_scope.

Theorem fold_mat_transp : ∀ M,
  mk_mat
    (map (λ j, map (λ i, mat_el M i j) (seq 1 (mat_nrows M)))
       (seq 1 (mat_ncols M))) =
  mat_transp M.
Proof. easy. Qed.

Theorem mat_transp_nrows : ∀ M, mat_nrows M⁺ = mat_ncols M.
Proof.
intros.
unfold mat_ncols; cbn.
now rewrite map_length, seq_length.
Qed.

Theorem mat_transp_ncols : ∀ M,
  mat_ncols M⁺ = if mat_ncols M =? 0 then 0 else mat_nrows M.
Proof.
intros.
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec (mat_ncols M) 0) as [Hcz| Hcz]. {
  now unfold mat_ncols; cbn; rewrite Hcz.
}
apply Nat.neq_0_lt_0 in Hcz.
unfold mat_ncols; cbn.
rewrite (List_map_hd 0); [ | now rewrite seq_length ].
now rewrite List_map_seq_length.
Qed.

Theorem mat_transp_is_corr : ∀ M,
  is_correct_matrix M = true
  → is_correct_matrix M⁺ = true.
Proof.
intros * Hcm.
apply is_scm_mat_iff in Hcm.
destruct Hcm as (H1, H2).
destruct (Nat.eq_dec (mat_ncols M) 0) as [Hcz| Hcz]. {
  specialize (H1 Hcz).
  unfold mat_transp.
  now rewrite H1, Hcz.
}
apply is_scm_mat_iff.
rewrite mat_transp_ncols.
apply Nat.eqb_neq in Hcz; rewrite Hcz.
apply Nat.eqb_neq in Hcz.
split. {
  intros Hr.
  unfold mat_nrows in Hr.
  unfold mat_ncols in Hcz.
  apply length_zero_iff_nil in Hr.
  now rewrite Hr in Hcz.
} {
  intros l Hl.
  unfold mat_transp in Hl; cbn in Hl.
  apply in_map_iff in Hl.
  destruct Hl as (j & Hjl & Hj).
  now rewrite <- Hjl, List_map_seq_length.
}
Qed.

Theorem mat_mul_is_corr : ∀ A B,
  is_correct_matrix A = true
  → is_correct_matrix B = true
  → mat_nrows B ≠ 0
  → is_correct_matrix (A * B) = true.
Proof.
intros * Ha Hb Hbz.
destruct (Nat.eq_dec (mat_nrows A) 0) as [Haz| Haz]. {
  unfold mat_nrows in Haz.
  apply length_zero_iff_nil in Haz.
  now destruct A as (lla); cbn in Haz; subst lla.
}
apply Nat.neq_0_lt_0 in Haz, Hbz.
apply is_scm_mat_iff in Ha.
apply is_scm_mat_iff in Hb.
apply is_scm_mat_iff.
destruct Ha as (Hacr & Hac).
destruct Hb as (Hbcr & Hbc).
split. {
  intros Hab.
  unfold mat_ncols in Hab.
  cbn in Hab |-*.
  rewrite List_map_seq_length.
  rewrite (List_map_hd 0) in Hab; [ | now rewrite seq_length ].
  rewrite List_map_seq_length in Hab.
  now rewrite Hbcr in Hbz.
} {
  intros lab Hlab.
  unfold mat_ncols; cbn.
  rewrite (List_map_hd 0); [ | now rewrite seq_length ].
  rewrite List_map_seq_length.
  cbn in Hlab.
  apply in_map_iff in Hlab.
  destruct Hlab as (x & Hlab & Hx).
  now rewrite <- Hlab, List_map_seq_length.
}
Qed.

Theorem mat_transp_el : ∀ M i j,
  is_correct_matrix M = true
  → i ≠ 0
  → j ≠ 0
  → mat_el M⁺ i j = mat_el M j i.
Proof.
intros * Hcm Hiz Hjz.
unfold mat_el; cbn.
destruct (le_dec i (mat_ncols M)) as [Hic| Hic]. 2: {
  apply Nat.nle_gt in Hic.
  rewrite nth_overflow. 2: {
    rewrite nth_overflow; [ easy | ].
    rewrite List_map_seq_length.
    flia Hic.
  }
  rewrite nth_overflow; [ easy | ].
  destruct (le_dec j (mat_nrows M)) as [Hjr| Hjr]. {
    apply is_scm_mat_iff in Hcm.
    destruct Hcm as (H1, H2).
    rewrite H2; [ flia Hic | ].
    apply nth_In; rewrite fold_mat_nrows.
    flia Hjz Hjr.
  }
  apply Nat.nle_gt in Hjr.
  rewrite nth_overflow; [ easy | ].
  rewrite fold_mat_nrows.
  flia Hjz Hjr.
}
rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hiz Hic ].
destruct (le_dec j (mat_nrows M)) as [Hjr| Hjr]. {
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hjz Hjr ].
  unfold mat_el.
  rewrite seq_nth; [ cbn | flia Hiz Hic ].
  rewrite seq_nth; [ cbn | flia Hjz Hjr ].
  do 2 rewrite Nat.sub_0_r.
  easy.
}
apply Nat.nle_gt in Hjr.
rewrite nth_overflow; [ | rewrite List_map_seq_length; flia Hjr ].
rewrite nth_overflow; [ easy | ].
destruct i; [ easy | cbn ].
rewrite Nat.sub_0_r.
rewrite nth_overflow; [ easy | ].
rewrite fold_mat_nrows; flia Hjz Hjr.
Qed.

Theorem mat_transp_mul :
  rngl_mul_is_comm = true →
  ∀ (MA : matrix T) (MB : matrix T),
  is_correct_matrix MA = true
  → is_correct_matrix MB = true
  → mat_nrows MA ≠ 0
  → mat_nrows MB ≠ 0
  → mat_ncols MA = mat_nrows MB
  → ((MA * MB)⁺ = MB⁺ * MA⁺)%M.
Proof.
intros Hic * Ha Hb Haz Hbz Hcarb.
apply matrix_eq; cycle 1. {
  apply mat_transp_is_corr.
  now apply mat_mul_is_corr.
} {
  apply mat_mul_is_corr. {
    now apply mat_transp_is_corr.
  } {
    now apply mat_transp_is_corr.
  }
  rewrite mat_transp_nrows.
  intros H.
  apply is_scm_mat_iff in Ha.
  destruct Ha as (Hcra, Hcla).
  now apply Hcra in H.
} {
  cbn.
  unfold mat_ncols; cbn.
  do 3 rewrite List_map_seq_length.
  rewrite (List_map_hd 0); [ | now rewrite seq_length; apply Nat.neq_0_lt_0 ].
  now rewrite List_map_seq_length.
} {
  unfold mat_ncols; cbn.
  do 2 rewrite List_map_seq_length.
  rewrite (List_map_hd 0). 2: {
    rewrite seq_length.
    unfold mat_ncols; cbn.
    rewrite (List_map_hd 0). 2: {
      rewrite seq_length.
      now apply Nat.neq_0_lt_0.
    }
    rewrite List_map_seq_length.
    apply Nat.neq_0_lt_0.
    intros H.
    apply is_scm_mat_iff in Hb.
    now apply Hb in H.
  }
  rewrite List_map_seq_length.
  rewrite (List_map_hd 0). 2: {
    rewrite seq_length.
    apply Nat.neq_0_lt_0.
    intros H.
    apply is_scm_mat_iff in Hb.
    now apply Hb in H.
  }
  rewrite List_map_seq_length.
  rewrite mat_transp_ncols.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec _ _) as [Hacz| Hacz]; [ | easy ].
  apply is_scm_mat_iff in Ha.
  now apply Ha.
}
intros i j Hi Hj.
rewrite mat_transp_nrows in Hi.
rewrite mat_transp_el; [ | now apply mat_mul_is_corr | flia Hi | flia Hj ].
rewrite mat_mul_ncols in Hi; [ | easy ].
rewrite mat_mul_ncols in Hj; [ | rewrite mat_transp_nrows; flia Hi ].
rewrite mat_transp_ncols in Hj.
rewrite if_eqb_eq_dec in Hj.
destruct (Nat.eq_dec (mat_ncols MA) 0) as [H1| H1]; [ flia Hj | ].
rewrite mat_el_mul; cycle 1. {
  now rewrite mat_mul_nrows.
} {
  now rewrite mat_mul_ncols.
}
rewrite mat_el_mul; cycle 1. {
  now rewrite mat_mul_nrows, mat_transp_nrows.
} {
  rewrite mat_mul_ncols, mat_transp_ncols. 2: {
    rewrite mat_transp_nrows; flia Hi.
  }
  now apply Nat.eqb_neq in H1; rewrite H1.
}
rewrite mat_transp_ncols.
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec (mat_ncols MB) 0) as [H2| H2]; [ flia Hi H2 | ].
rewrite <- Hcarb; symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  rewrite rngl_mul_comm; [ | easy ].
  rewrite mat_transp_el; [ | easy | flia Hk | flia Hj ].
  easy.
}
cbn - [ mat_el ].
apply rngl_summation_eq_compat.
intros k Hk.
f_equal.
unfold mat_transp; cbn.
unfold mat_el.
rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hi ].
rewrite (List_map_nth' 0); [ | rewrite seq_length ]. 2: {
  rewrite <- Hcarb; flia Hk.
}
rewrite seq_nth; [ | flia Hi ].
rewrite seq_nth; [ | flia Hk Hcarb ].
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_comm, Nat.add_sub.
easy.
Qed.

(* matrix without row i and column j *)

Definition subm i j (M : matrix T) :=
  mk_mat (map (butn (j - 1)) (butn (i - 1) (mat_list_list M))).

(* combinations of submatrix and other operations *)

Theorem mat_nrows_subm : ∀ (M : matrix T) i j,
  mat_nrows (subm i j M) = mat_nrows M - Nat.b2n (i <=? mat_nrows M).
Proof.
intros.
destruct M as (ll); cbn - [ "<?" ].
rewrite map_length, butn_length.
unfold Nat.b2n.
rewrite if_ltb_lt_dec, if_leb_le_dec.
destruct (lt_dec _ _) as [H1| H1]. {
  destruct (le_dec _ _) as [H2| H2]; [ easy | flia H1 H2 ].
}
destruct (le_dec _ _) as [H2| H2]; [ flia H1 H2 | easy ].
Qed.

Theorem mat_ncols_subm : ∀ (M : matrix T) i j,
  is_correct_matrix M = true
  → 1 ≤ i ≤ mat_nrows M
  → 1 ≤ j ≤ mat_ncols M
  → mat_ncols (subm i j M) = if mat_nrows M =? 1 then 0 else mat_ncols M - 1.
Proof.
intros * Hcm Hi Hj.
destruct M as (ll); cbn in Hi, Hj.
unfold mat_ncols in Hj |-*; cbn in Hj |-*.
destruct i; [ easy | ].
destruct j; [ easy | ].
destruct Hi as (_, Hi).
destruct Hj as (_, Hj).
apply -> Nat.le_succ_l in Hi.
apply -> Nat.le_succ_l in Hj.
do 2 rewrite Nat_sub_succ_1.
apply is_scm_mat_iff in Hcm.
unfold mat_ncols in Hcm; cbn in Hcm.
destruct Hcm as (_, Hcl).
destruct ll as [| la]; intros; [ easy | ].
cbn in Hi, Hj |-*.
cbn - [ In ] in Hcl.
assert (H : ∀ l, l ∈ ll → length l = length la). {
  intros l Hl.
  now apply Hcl; right.
}
move H before Hcl; clear Hcl; rename H into Hcl.
apply Nat.le_succ_l in Hi.
apply Nat.succ_le_mono in Hi.
destruct ll as [| lb]. {
  now apply Nat.le_0_r in Hi; subst i; cbn.
}
cbn in Hi |-*.
destruct i. {
  cbn; rewrite butn_length.
  rewrite Hcl; [ | now left ].
  now apply Nat.ltb_lt in Hj; rewrite Hj.
}
apply Nat.succ_le_mono in Hi.
cbn; rewrite butn_length.
now apply Nat.ltb_lt in Hj; rewrite Hj.
Qed.

Theorem is_squ_mat_subm : ∀ (M : matrix T) i j,
  1 ≤ i ≤ mat_nrows M
  → 1 ≤ j ≤ mat_nrows M
  → is_square_matrix M = true
  → is_square_matrix (subm i j M) = true.
Proof.
intros * Hi Hj Hm.
apply is_scm_mat_iff.
specialize (square_matrix_ncols _ Hm) as Hcm.
destruct (Nat.eq_dec (mat_nrows M) 1) as [Hr1| Hr1]. {
  rewrite Hr1 in Hi, Hj.
  replace i with 1 by flia Hi.
  replace j with 1 by flia Hj.
  cbn.
  destruct M as (ll); cbn in Hr1 |-*.
  destruct ll as [| l]; [ easy | ].
  now destruct ll.
}
split. {
  intros Hcs.
  rewrite <- Hcm in Hj.
  rewrite mat_ncols_subm in Hcs; [ | | easy | easy ]. 2: {
    now apply squ_mat_is_corr.
  }
  apply Nat.eqb_neq in Hr1; rewrite Hr1 in Hcs.
  apply Nat.eqb_neq in Hr1.
  flia Hj Hcm Hr1 Hcs.
} {
  intros l Hl.
  apply is_scm_mat_iff in Hm.
  destruct Hm as (_ & Hc).
  clear Hcm Hr1.
  rewrite mat_nrows_subm.
  generalize Hi; intros (_, H).
  apply Nat.leb_le in H; rewrite H; clear H; cbn.
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
  destruct (lt_dec _ (length l')) as [Hljl| Hljl]. {
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
  → is_correct_matrix A = true
  → 1 ≤ i ≤ mat_nrows A
  → 1 ≤ j ≤ mat_ncols A
  → is_correct_matrix (subm i j A) = true.
Proof.
intros * Hc1 Ha Hi Hj.
apply is_scm_mat_iff.
split. {
  rewrite mat_nrows_subm.
  generalize Hi; intros (_, H).
  apply Nat.leb_le in H; rewrite H; clear H; cbn.
  rewrite mat_ncols_subm; [ | easy | easy | easy ].
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (mat_nrows A) 1) as [Hr1| Hr1]; [ now rewrite Hr1 | ].
  intros H.
  flia Hc1 H Hj.
} {
  intros l Hl.
  rewrite mat_ncols_subm; [ | easy | easy | easy ].
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec _ _) as [Hr1| Hr1]. {
    destruct A as (ll).
    cbn - [ butn ] in *.
    destruct ll as [| lb]; [ easy | ].
    destruct ll; [ | easy ].
    cbn in Hi.
    now replace i with 1 in Hl by flia Hi.
  }
  move Hr1 after Hc1.
  cbn in Hl.
  apply in_map_iff in Hl.
  destruct Hl as (la & Hl & Hla).
  subst l.
  rewrite butn_length.
  unfold Nat.b2n.
  rewrite if_ltb_lt_dec.
  apply is_scm_mat_iff in Ha.
  destruct Ha as (_, Hcl).
  apply in_butn in Hla.
  specialize (Hcl _ Hla).
  destruct (lt_dec _ _) as [Hja| Hja]; [ now rewrite Hcl | ].
  rewrite Nat.nlt_ge in Hja.
  rewrite Hcl in Hja.
  flia Hj Hja.
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
apply is_scm_mat_iff in Hmp.
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

Theorem mI_is_square_matrix : ∀ n, is_square_matrix (mI n) = true.
Proof.
intros.
apply is_scm_mat_iff.
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

Theorem mI_is_correct_matrix : ∀ n, is_correct_matrix (mI n) = true.
Proof.
intros.
apply squ_mat_is_corr, mI_is_square_matrix.
Qed.

Theorem mZ_is_correct_matrix : ∀ m n,
  n ≠ 0
  → is_correct_matrix (mZ m n) = true.
Proof.
intros * Hnz.
destruct (Nat.eq_dec m 0) as [Hmz| Hmz]; [ now subst m | ].
apply is_scm_mat_iff.
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
  is_correct_matrix M = true
  → is_correct_matrix (- M) = true.
Proof.
intros * Hm.
apply is_scm_mat_iff in Hm.
apply is_scm_mat_iff.
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

Theorem squ_mat_add_is_squ : ∀ (MA MB : matrix T),
  is_square_matrix MA = true
  → is_square_matrix MB = true
  → is_square_matrix (MA + MB) = true.
Proof.
intros * Ha Hb.
apply is_scm_mat_iff; cbn.
apply is_scm_mat_iff in Ha.
apply is_scm_mat_iff in Hb.
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

Theorem squ_mat_mul_is_squ : ∀ (MA MB : matrix T),
  is_square_matrix MA = true
  → is_square_matrix MB = true
  → mat_nrows MA = mat_nrows MB
  → is_square_matrix (MA * MB) = true.
Proof.
intros * Ha Hb Hrab.
apply is_scm_mat_iff; cbn.
rewrite List_map_seq_length.
rewrite (square_matrix_ncols MB); [ | easy ].
split. {
  intros Hcc.
  unfold mat_ncols in Hcc; cbn in Hcc.
  rewrite square_matrix_ncols in Hcc; [ | easy ].
  rewrite <- Hrab in Hcc.
  apply length_zero_iff_nil in Hcc.
  destruct (Nat.eq_dec (mat_nrows MA) 0) as [Hrz| Hrz]; [ easy | ].
  apply Nat.neq_0_lt_0 in Hrz.
  rewrite (List_map_hd 0) in Hcc; [ | now rewrite seq_length ].
  apply map_eq_nil in Hcc.
  now apply List_seq_eq_nil in Hcc.
} {
  intros l Hl.
  apply in_map_iff in Hl.
  destruct Hl as (i & Hil & Hi).
  subst l.
  now rewrite List_map_seq_length.
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

Theorem square_matrix_mul_is_square : ∀ n (MA MB : square_matrix n T),
  is_square_matrix (sm_mat MA * sm_mat MB) = true.
Proof.
intros.
destruct MA as (MA & Ha).
destruct MB as (MB & Hb); cbn.
apply Bool.andb_true_iff in Ha, Hb.
apply squ_mat_mul_is_squ; [ easy | easy | ].
destruct Ha as (Ha, _).
destruct Hb as (Hb, _).
apply Nat.eqb_eq in Ha.
apply Nat.eqb_eq in Hb.
congruence.
Qed.

Theorem square_matrix_opp_is_square : ∀ n (M : square_matrix n T),
  is_square_matrix (- sm_mat M)%M = true.
Proof.
intros.
apply is_scm_mat_iff.
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
  apply is_scm_mat_iff in Hsm.
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

Theorem squ_mat_mul_scal_l_is_squ : ∀ (M : matrix T) μ,
  is_square_matrix M = true
  → is_square_matrix (μ × M) = true.
Proof.
intros * Hm.
apply is_scm_mat_iff in Hm.
apply is_scm_mat_iff.
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

Theorem square_matrix_is_correct : ∀ n (M : square_matrix n T),
  is_correct_matrix (sm_mat M) = true.
Proof.
intros.
destruct M as (M, Hm); cbn.
apply Bool.andb_true_iff in Hm.
destruct Hm as (Hr, Hm).
now apply squ_mat_is_corr.
Qed.

(*
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
*)

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

Theorem mat_el_add : ∀ (MA MB : matrix T) i j,
  is_correct_matrix MA = true
  → is_correct_matrix MB = true
  → 1 ≤ i ≤ mat_nrows MA
  → 1 ≤ i ≤ mat_nrows MB
  → 1 ≤ j ≤ mat_ncols MA
  → 1 ≤ j ≤ mat_ncols MB
  → mat_el (MA + MB) i j = (mat_el MA i j + mat_el MB i j)%L.
Proof.
intros * Ha Hb Hia Hib Hja Hjb.
unfold "+"%M; cbn.
rewrite map2_nth with (a := []) (b := []); cycle 1. {
  rewrite fold_mat_nrows; flia Hia.
} {
  rewrite fold_mat_nrows; flia Hib.
}
rewrite map2_nth with (a := 0%L) (b := 0%L); cycle 1. {
  apply is_scm_mat_iff in Ha.
  destruct Ha as (Hcra & Hca).
  rewrite Hca; [ flia Hja | ].
  apply nth_In.
  rewrite fold_mat_nrows; flia Hia.
} {
  apply is_scm_mat_iff in Hb.
  destruct Hb as (Hcrb & Hcb).
  rewrite Hcb; [ flia Hjb | ].
  apply nth_In.
  rewrite fold_mat_nrows; flia Hib.
}
easy.
Qed.

Theorem List_repeat_as_map : ∀ A (a : A) n,
  repeat a n = map (λ _, a) (seq 0 n).
Proof.
intros.
induction n; [ easy | cbn ].
f_equal.
now rewrite <- seq_shift, map_map.
Qed.

Theorem mat_vect_mul_0_r : ∀ m n (M : matrix T),
  m = mat_nrows M
  → n = mat_ncols M
  → (M • vect_zero n = vect_zero m)%V.
Proof.
intros * Hr Hc.
specialize (proj2 rngl_has_opp_or_sous_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
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
now apply rngl_mul_0_r.
Qed.

Notation "A ⁺" := (mat_transp A) (at level 1, format "A ⁺") : M_scope.

Theorem mat_subm_transp :
  ∀ i j (M : matrix T),
  is_square_matrix M = true
  → 1 ≤ i ≤ mat_ncols M
  → 1 ≤ j ≤ mat_nrows M
  → ((subm j i M)⁺ = subm i j M⁺)%M.
Proof.
intros * Hsm Hi Hj.
specialize (square_matrix_ncols _ Hsm) as Hcr.
destruct (Nat.eq_dec (mat_ncols M) 1) as [Hc1| Hc1]. {
  rewrite Hc1 in Hi.
  rewrite <- Hcr, Hc1 in Hj.
  replace i with 1 by flia Hi.
  replace j with 1 by flia Hj.
  clear i j Hi Hj.
  unfold subm, mat_transp.
  rewrite Nat.sub_diag.
  cbn - [ butn ].
  f_equal.
  rewrite map_length.
  rewrite butn_length.
  rewrite fold_mat_nrows, <- Hcr, Hc1.
  cbn - [ butn ].
  destruct M as (ll); cbn.
  destruct ll as [| l]; [ easy | ].
  cbn in Hc1.
  destruct ll as [| l']; [ easy | ].
  cbn.
  destruct l as [| a]; [ easy | ].
  destruct l; [ | easy ].
  cbn in Hcr; flia Hcr.
}
assert (Hcm : is_correct_matrix M = true) by now apply squ_mat_is_corr.
assert (Hcmt : is_correct_matrix M⁺ = true) by now apply mat_transp_is_corr.
assert (Hit : 1 ≤ i ≤ mat_nrows M⁺) by now rewrite mat_transp_nrows.
assert (Hjt : 1 ≤ j ≤ mat_ncols M⁺). {
  rewrite mat_transp_ncols.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (mat_ncols M) 0) as [H| H]; [ | easy ].
  flia H Hi.
}
apply matrix_eq; cycle 1. {
  apply mat_transp_is_corr, subm_is_corr_mat; try easy.
} {
  apply subm_is_corr_mat; [ | easy | easy | easy ].
  rewrite mat_transp_ncols.
  rewrite if_eqb_eq_dec.
  rewrite Hcr in Hc1.
  now destruct (Nat.eq_dec (mat_ncols M) 0).
} {
  rewrite mat_transp_nrows.
  rewrite mat_nrows_subm.
  rewrite mat_ncols_subm; [ | easy | easy | easy ].
  generalize Hc1; intros H.
  rewrite Hcr in H.
  apply Nat.eqb_neq in H; rewrite H; clear H.
  rewrite mat_transp_nrows; cbn.
  generalize Hi; intros (_, H).
  now apply Nat.leb_le in H; rewrite H.
} {
  rewrite mat_transp_ncols.
  rewrite mat_ncols_subm; [ | easy | easy | easy ].
  generalize Hc1; intros H.
  rewrite Hcr in H.
  apply Nat.eqb_neq in H; rewrite H; clear H.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (mat_ncols M - 1) 0) as [H| H]; [ flia Hi H Hc1 | ].
  clear H.
  rewrite mat_ncols_subm; [ | easy | easy | easy ].
  rewrite mat_transp_nrows.
  generalize Hc1; intros H.
  apply Nat.eqb_neq in H; rewrite H; clear H.
  rewrite mat_transp_ncols.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (mat_ncols M) 0) as [H| H]; [ flia Hi H Hc1 | ].
  clear H.
  rewrite mat_nrows_subm.
  generalize Hj; intros (_, H).
  now apply Nat.leb_le in H; rewrite H.
}
intros u v Hu Hv.
rewrite mat_transp_el; [ | now apply subm_is_corr_mat | flia Hu | flia Hv ].
unfold mat_transp; cbn.
rewrite (List_map_nth' []). 2: {
  rewrite butn_length.
  rewrite fold_mat_nrows.
  rewrite mat_ncols_subm in Hv; [ | easy | easy | easy ].
  rewrite mat_transp_nrows in Hv.
  rewrite mat_transp_ncols in Hv.
  enough (H : v < mat_nrows M). {
    destruct v; [ easy | ].
    destruct (mat_nrows M); [ easy | ].
    rewrite Nat_sub_succ_1.
    apply Nat.succ_lt_mono in H.
    unfold Nat.b2n.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec (j - 1) (S n)); flia H.
  }
  generalize Hc1; intros H.
  apply Nat.eqb_neq in H; rewrite H in Hv; clear H.
  rewrite if_eqb_eq_dec in Hv.
  destruct (Nat.eq_dec (mat_ncols M) 0) as [H| H]; [ flia Hi H | ].
  flia Hv.
}
rewrite (List_map_nth' []). 2: {
  rewrite butn_length.
  rewrite List_map_seq_length.
  rewrite mat_transp_nrows in Hu.
  rewrite mat_ncols_subm in Hu; [ | easy | easy | easy ].
  enough (H : u < mat_ncols M). {
    destruct u; [ easy | ].
    destruct (mat_ncols M); [ easy | ].
    rewrite Nat_sub_succ_1.
    apply Nat.succ_lt_mono in H.
    unfold Nat.b2n.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec (i - 1) (S n)); flia H.
  }
  generalize Hc1; intros H.
  rewrite Hcr in H.
  apply Nat.eqb_neq in H; rewrite H in Hu; clear H.
  flia Hu.
}
do 4 rewrite nth_butn.
rewrite mat_transp_nrows in Hu.
rewrite mat_ncols_subm in Hu; [ | easy | easy | easy ].
rewrite mat_ncols_subm in Hv; [ | easy | easy | easy ].
rewrite mat_transp_nrows in Hv.
rewrite mat_transp_ncols in Hv.
assert (H : (mat_nrows M =? 1) = false) by (apply Nat.eqb_neq; congruence).
rewrite H in Hu; clear H.
assert (H : (mat_ncols M =? 1) = false) by now apply Nat.eqb_neq.
rewrite H in Hv; clear H.
assert (H : (mat_ncols M =? 0) = false) by (apply Nat.eqb_neq; flia Hi).
rewrite H in Hv; clear H.
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  unfold Nat.b2n; rewrite if_leb_le_dec.
  destruct (le_dec (i - 1) (u - 1)); flia Hu.
}
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  unfold Nat.b2n; rewrite if_leb_le_dec.
  destruct (le_dec (j - 1) (v - 1)); flia Hv.
}
rewrite seq_nth. 2: {
  unfold Nat.b2n; rewrite if_leb_le_dec.
  destruct (le_dec (j - 1) (v - 1)); flia Hv.
}
rewrite seq_nth. 2: {
  unfold Nat.b2n; rewrite if_leb_le_dec.
  destruct (le_dec (i - 1) (u - 1)); flia Hu.
}
unfold mat_el.
rewrite Nat.add_assoc, (Nat.add_comm 1 (u - 1)).
rewrite Nat.sub_add; [ | easy ].
rewrite Nat.add_sub_swap; [ | easy ].
f_equal.
rewrite Nat.add_assoc, (Nat.add_comm 1 (v - 1)).
rewrite Nat.sub_add; [ | easy ].
rewrite Nat.add_sub_swap; [ | easy ].
easy.
Qed.

Theorem mat_transp_is_square : ∀ M,
  is_square_matrix M = true
  → is_square_matrix M⁺ = true.
Proof.
intros * Hsm.
specialize (square_matrix_ncols _ Hsm) as Hc.
apply is_scm_mat_iff in Hsm.
apply is_scm_mat_iff.
destruct Hsm as (Hcr & Hcl).
cbn; rewrite List_map_seq_length.
split. {
  intros Hct.
  destruct (Nat.eq_dec (mat_ncols M) 0) as [Hcz| Hcz]; [ easy | ].
  rewrite mat_transp_ncols in Hct.
  apply Nat.eqb_neq in Hcz; rewrite Hcz in Hct.
  congruence.
} {
  intros l Hl.
  apply in_map_iff in Hl.
  destruct Hl as (i & Hi & Hic).
  now rewrite <- Hi, map_length, seq_length.
}
Qed.

Theorem mat_transp_involutive : ∀ M,
  is_correct_matrix M = true
  → (M⁺⁺)%M = M.
Proof.
intros * Hcm.
destruct (Nat.eq_dec (mat_ncols M) 0) as [Hcz| Hcz]. {
  destruct M as (ll); cbn.
  unfold mat_ncols in Hcz; cbn in Hcz.
  apply length_zero_iff_nil in Hcz.
  destruct ll as [| l]; [ easy | ].
  cbn in Hcz; subst l; cbn.
  unfold mat_transp, mat_ncols; cbn; f_equal.
  apply is_scm_mat_iff in Hcm.
  unfold mat_ncols in Hcm; cbn in Hcm.
  destruct Hcm as (Hcr, _).
  now specialize (Hcr eq_refl).
}
destruct M as (ll); cbn.
unfold mat_transp, mat_ncols; cbn; f_equal.
rewrite (List_map_nth_seq ll []) at 2.
rewrite List_map_seq_length.
rewrite (List_map_hd 0). 2: {
  rewrite seq_length.
  unfold mat_ncols in Hcz.
  cbn in Hcz.
  now apply Nat.neq_0_lt_0.
}
rewrite List_map_seq_length.
rewrite <- seq_shift, map_map.
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
destruct Hi as (_, Hi); cbn in Hi.
erewrite map_ext_in. 2: {
  intros j Hj; apply in_seq in Hj.
  cbn in Hj.
  rewrite Nat_sub_succ_1.
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hj ].
  rewrite (List_map_nth' 0); [ | now rewrite List_map_seq_length ].
  rewrite seq_shift.
  rewrite seq_nth; [ | flia Hj ].
  rewrite seq_nth; [ | easy ].
  now do 2 rewrite Nat.add_comm, Nat.add_sub.
}
destruct ll as [| l]; [ easy | ].
unfold mat_ncols in Hcz; cbn in Hcz.
cbn - [ nth ].
rewrite (List_map_nth_seq (nth i (l :: ll) []) 0%L) at 1.
apply is_scm_mat_iff in Hcm.
unfold mat_ncols in Hcm; cbn - [ In ] in Hcm.
destruct Hcm as (_, Hcl).
rewrite <- seq_shift, map_map.
erewrite map_ext_in. 2: {
  now intros; rewrite Nat_sub_succ_1.
}
symmetry.
rewrite Hcl; [ easy | ].
now apply nth_In.
Qed.

End a.

Module matrix_Notations.

Declare Scope M_scope.
Delimit Scope M_scope with M.

Arguments Build_square_matrix n%nat [T]%type sm_mat%M.
Arguments is_correct_matrix {T}%type M%M.
Arguments is_square_matrix {T}%type M%M.
Arguments mat_add_0_l {T}%type {ro rp} {m n}%nat M%M.
Arguments mat_add_0_r {T}%type {ro rp} {m n}%nat M%M.
Arguments mat_add_add_swap {T}%type {ro rp} (MA MB MC)%M.
Arguments mat_add_assoc {T}%type {ro rp} (MA MB MC)%M.
Arguments mat_add_comm {T}%type {ro rp} (MA MB)%M.
Arguments mat_add_opp_r {T}%type {ro rp} Hop M%M.
Arguments mat_add_sub {T}%type {ro rp} Hop (MA MB)%M.
Arguments mat_add {T}%type {ro} (MA MB)%M.
Arguments mat_el {T}%type {ro} M%M (i j)%nat.
Arguments mat_list_list {T}%type m%M.
Arguments mat_mul_1_l {T}%type {ro rp} Hop {n}%nat M%M.
Arguments mat_mul_1_r {T}%type {ro rp} Hop {n}%nat M%M.
Arguments mat_mul_add_distr_l {T}%type {ro rp} (MA MB MC)%M.
Arguments mat_mul_assoc {T}%type {ro rp} Hop (MA MB MC)%M.
Arguments mat_mul_el {T}%type {ro} (MA MB)%M (i k)%nat.
Arguments mat_mul_mul_scal_l {T}%type {ro rp} Hop Hic a%L (MA MB)%M.
Arguments mat_mul_scal_1_l {T}%type {ro rp} M%M.
Arguments mat_mul_scal_l_add_distr_l {T}%type {ro rp} a%L (MA MB)%M.
Arguments mat_mul_scal_l_add_distr_r {T}%type {ro rp} (a b)%L M%M.
Arguments mat_mul_scal_l_mul_assoc {T}%type {ro rp} (a b)%L M%M.
Arguments mat_mul_scal_l_mul {T}%type {ro rp} Hop a%L (MA MB)%M.
Arguments mat_mul_scal_l {T ro} s%L M%M.
Arguments mat_mul_scal_vect_assoc {T}%type {ro rp} Hop a%L MA%M V%V.
Arguments mat_mul_scal_vect_comm {T}%type {ro rp} Hop Hic a%L MA%M V%V.
Arguments mat_mul {T}%type {ro} (MA MB)%M.
Arguments mat_mul_vect_r {T ro} M%M V%V.
Arguments mat_ncols {T}%type M%M.
Arguments mat_nrows {T}%type M%M.
Arguments mat_opp {T ro} M%M.
Arguments mat_repl_vect_is_square {T}%type {ro} [k]%nat M%M V%V.
Arguments matrix_eq {T ro} (MA MB)%M.
Arguments mat_subm_transp {T ro} [i j]%nat.
Arguments mat_sub {T ro} MA%M MB%M.
Arguments mat_transp_is_square {T ro} M%M.
Arguments mat_transp_mul {T ro rp} _ (MA MB)%M.
Arguments mat_transp_nrows {T}%type {ro} M%M.
Arguments mat_transp {T ro} M%M.
Arguments mat_vect_mul_0_r {T}%type {ro rp} Hop [m n]%nat M%M.
Arguments mat_vect_mul_1_l {T}%type {ro rp} Hop {n}%nat V%V.
Arguments mat_vect_mul_assoc {T}%type {ro rp} Hop (A B)%M V%V.
Arguments mI_any_seq_start {T ro} (sta len)%nat.
Arguments mI_is_correct_matrix {T}%type {ro} n%nat.
Arguments minus_one_pow {T ro}.
Arguments mI {T ro} n%nat.
Arguments mZ {T ro} (m n)%nat.
Arguments square_matrix_ncols {T}%type M%M.
Arguments subm {T} i%nat j%nat M%M.
Arguments δ {T}%type {ro} (i j)%nat.

Notation "A + B" := (mat_add A B) : M_scope.
Notation "A - B" := (mat_sub A B) : M_scope.
Notation "A * B" := (mat_mul A B) : M_scope.
Notation "μ × A" := (mat_mul_scal_l μ A) (at level 40) : M_scope.
Notation "- A" := (mat_opp A) : M_scope.
Notation "A ⁺" := (mat_transp A) (at level 1, format "A ⁺") : M_scope.
Notation "A • V" := (mat_mul_vect_r A V) (at level 40) : M_scope.
Notation "A • V" := (mat_mul_vect_r A V) (at level 40) : V_scope.

End matrix_Notations.
