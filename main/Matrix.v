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
  nth j (nth i (mat_list_list M) []) 0%F.

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
  (∀ i j, i < mat_nrows MA → j < mat_ncols MB → mat_el MA i j = mat_el MB i j)
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
  apply nth_ext with (d := 0%F) (d' := 0%F); [ easy | ].
  intros i Hi.
  unfold mat_ncols in Hij.
  cbn - [ nth ] in Hij.
  apply (Hij 0 i (Nat.lt_0_succ _)).
  congruence.
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
assert (H : S i < S len) by now apply Nat.succ_lt_mono in Hi.
specialize (H1 H); clear H.
cbn in H1.
apply H1.
apply is_scm_mat_iff in Hb.
destruct Hb as (Hb1, Hb2).
unfold mat_ncols in Hb2; cbn in Hb2.
destruct llb as [| lb']; [ easy | ].
cbn in Hj.
specialize (Hb2 lb' (or_intror (or_introl eq_refl))).
congruence.
Qed.

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
   ∑ (j = 0, mat_ncols MA - 1), mat_el MA i j * mat_el MB j k.

Definition mat_mul (MA MB : matrix T) : matrix T :=
  mk_mat
    (map (λ i, map (mat_mul_el MA MB i) (seq 0 (mat_ncols MB)))
       (seq 0 (mat_nrows MA))).

(* opposite *)

Definition mat_opp (M : matrix T) : matrix T :=
  mk_mat (map (map rngl_opp) (mat_list_list M)).

(* subtraction *)

Definition mat_sub (MA MB : matrix T) :=
  mat_add MA (mat_opp MB).

(* concatenation of a matrix and a column vector *)

Definition mat_vect_concat (M : matrix T) V :=
  mk_mat (map2 (λ row e, row ++ [e]) (mat_list_list M) (vect_list V)).

(* multiplication of a matrix by a vector *)

Definition mat_mul_vect_r (M : matrix T) (V : vector T) :=
  mk_vect (map (λ row, vect_dot_mul (mk_vect row) V) (mat_list_list M)).

(* multiplication of a matrix by a scalar *)

Definition mat_mul_scal_l s (M : matrix T) :=
  mk_mat (map (map (rngl_mul s)) (mat_list_list M)).

(* matrix whose k-th column is replaced by a vector *)

Definition mat_repl_vect k (M : matrix T) (V : vector T) :=
  mk_mat (map2 (replace_at k) (mat_list_list M) (vect_list V)).

Theorem mat_el_repl_vect : ∀ (M : matrix T) V i j k,
  is_correct_matrix M = true
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

Theorem mat_repl_vect_is_square : ∀ k (M : matrix T) V,
  k < mat_ncols M
  → vect_size V = mat_nrows M
  → is_square_matrix M = true
  → is_square_matrix (mat_repl_vect k M V) = true.
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
  mk_mat (repeat (repeat 0%F n) m).

(* identity square matrix of dimension n *)

Definition δ i j := if i =? j then 1%F else 0%F.
Definition mI n : matrix T := mk_mat (map (λ i, map (δ i) (seq 0 n)) (seq 0 n)).

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
  i < mat_nrows (MA * MB)
  → j < mat_ncols (MA * MB)
  → mat_el (MA * MB) i j =
    ∑ (k = 0, mat_ncols MA - 1), mat_el MA i k * mat_el MB k j.
Proof.
intros * Hir Hjc; cbn.
rewrite mat_mul_nrows in Hir.
rewrite mat_mul_ncols in Hjc; [ | flia Hir ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
rewrite seq_nth; [ | easy ].
easy.
Qed.

(* multiplication left and right with identity *)

Theorem mat_mul_1_l {n} : ∀ (M : matrix T),
  is_correct_matrix M = true
  → n = mat_nrows M
  → (mI n * M)%M = M.
Proof.
intros * HM Hn; subst n.
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
apply map_ext_in.
intros i Hi.
remember (nth i ll []) as la eqn:Hla.
rewrite List_map_nth_seq with (d := 0%F).
rewrite (HM la). 2: {
  rewrite Hla.
  apply nth_In.
  now apply in_seq in Hi.
}
unfold mat_ncols; cbn.
rewrite <- Hc.
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
  is_correct_matrix M = true
  → n = mat_ncols M
  → (M * mI n)%M = M.
Proof.
intros * HM H; subst n.
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
apply map_ext_in.
intros i Hi.
remember (nth i ll []) as la eqn:Hla.
rewrite List_map_nth_seq with (d := 0%F).
rewrite (HM la). 2: {
  rewrite Hla.
  apply nth_In.
  now apply in_seq in Hi.
}
unfold mat_ncols; cbn.
rewrite <- Hc.
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
  cbn in Hc |-*; rewrite <- Hc.
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
apply vector_eq. 2: {
  now cbn; do 2 rewrite map_length; rewrite seq_length.
}
cbn; do 2 rewrite map_length; rewrite seq_length.
intros i Hi.
rewrite (List_map_nth' []); [ | now rewrite List_map_seq_length ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ cbn | easy ].
unfold vect_dot_mul; cbn.
destruct V as (l); cbn in Hi |-*.
rewrite map2_map_l.
rewrite (List_seq_cut i); [ cbn | now apply in_seq ].
rewrite Nat.sub_0_r.
rewrite map2_app_l.
rewrite seq_length.
erewrite map2_ext_in. 2: {
  intros j k Hj Hk; apply in_seq in Hj.
  destruct Hj as (_, Hj); cbn in Hj.
  rewrite δ_ndiag; [ | flia Hj ].
  rewrite rngl_mul_0_l; [ easy | now left ].
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
  cbn in Hi.
  apply Nat.succ_lt_mono in Hi.
  cbn in Hl'.
  now apply (IHi l).
}
cbn.
rewrite δ_diag.
rewrite rngl_mul_1_l.
erewrite map2_ext_in. 2: {
  intros j k Hj Hk; apply in_seq in Hj.
  destruct Hj as (Hj, _).
  rewrite δ_ndiag; [ | flia Hj ].
  rewrite rngl_mul_0_l; [ easy | now left ].
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
apply Nat.succ_lt_mono in Hi.
now apply IHi.
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
rewrite map2_nth with (a := 0%F) (b := 0%F); cycle 1. {
  apply is_scm_mat_iff in Hb.
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
  is_correct_matrix MA = true
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
  apply is_scm_mat_iff in Ha.
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
  is_correct_matrix MB = true
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
  apply is_scm_mat_iff in Hb.
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
  is_correct_matrix A = true
  → is_correct_matrix B = true
  → mat_ncols A = mat_nrows B
  → mat_ncols B = vect_size V
  → (A • (B • V) = (A * B) • V)%M.
Proof.
intros * Ha Hb Hcarb Hcbv.
unfold "•"%M, "*"%M; cbn.
f_equal.
rewrite map_map.
rewrite List_map_map_seq with (d := []).
apply map_ext_in.
intros i Hi.
unfold vect_dot_mul; cbn.
rewrite map2_map_r.
rewrite map2_map2_seq_l with (d := 0%F).
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
apply is_scm_mat_iff in Hb.
destruct Hb as (Hbrc, Hb).
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite fold_mat_el.
  unfold vect_dot_mul; cbn.
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
  is_correct_matrix MA = true
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
apply is_scm_mat_iff in Ha.
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
  is_correct_matrix MA = true
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
apply is_scm_mat_iff in Ha.
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

Notation "A ⁺" := (mat_transp A) (at level 1, format "A ⁺") : M_scope.

Theorem fold_mat_transp : ∀ M,
  mk_mat
    (map (λ j, map (λ i, mat_el M i j) (seq 0 (mat_nrows M)))
       (seq 0 (mat_ncols M))) =
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
  → mat_el M⁺ i j = mat_el M j i.
Proof.
intros * Hcm.
unfold mat_el; cbn.
destruct (lt_dec i (mat_ncols M)) as [Hic| Hic]. 2: {
  apply Nat.nlt_ge in Hic.
  rewrite nth_overflow. 2: {
    rewrite nth_overflow; [ easy | ].
    now rewrite map_length, seq_length.
  }
  rewrite nth_overflow; [ easy | ].
  destruct (lt_dec j (mat_nrows M)) as [Hjr| Hjr]. {
    apply is_scm_mat_iff in Hcm.
    destruct Hcm as (H1, H2).
    rewrite H2; [ easy | ].
    now apply nth_In; rewrite fold_mat_nrows.
  }
  apply Nat.nlt_ge in Hjr.
  now rewrite nth_overflow.
}
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
destruct (lt_dec j (mat_nrows M)) as [Hjr| Hjr]. {
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  unfold mat_el.
  rewrite seq_nth; [ cbn | easy ].
  rewrite seq_nth; [ cbn | easy ].
  easy.
}
apply Nat.nlt_ge in Hjr.
rewrite nth_overflow; [ | now rewrite List_map_seq_length ].
rewrite (nth_overflow _ _ Hjr).
now destruct i.
Qed.

Theorem mat_transp_mul :
  rngl_is_comm = true →
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
rewrite mat_transp_el; [ | now apply mat_mul_is_corr ].
rewrite mat_mul_ncols in Hi; [ | easy ].
rewrite mat_mul_ncols in Hj; [ | rewrite mat_transp_nrows; flia Hi ].
rewrite mat_transp_ncols in Hj.
rewrite if_eqb_eq_dec in Hj.
destruct (Nat.eq_dec (mat_ncols MA) 0) as [H1| H1]; [ easy | ].
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
  intros k (_, Hk).
  rewrite rngl_mul_comm; [ | easy ].
  rewrite mat_transp_el; [ | easy ].
  rewrite mat_transp_el; [ | easy ].
  easy.
}
easy.
Qed.

(* matrix without row i and column j *)

Definition subm (M : matrix T) i j :=
  mk_mat (map (butn j) (butn i (mat_list_list M))).

(* combinations of submatrix and other operations *)

Theorem mat_nrows_subm : ∀ (M : matrix T) i j,
  mat_nrows (subm M i j) = mat_nrows M - Nat.b2n (i <? mat_nrows M).
Proof.
intros.
destruct M as (ll); cbn - [ "<?" ].
rewrite map_length.
now rewrite butn_length.
Qed.

Theorem mat_ncols_subm : ∀ (M : matrix T) i j,
  is_correct_matrix M = true
  → mat_ncols (subm M i j) =
   match mat_nrows M with
   | 0 => 0
   | 1 => if i =? 0 then 0 else mat_ncols M - Nat.b2n (j <? mat_ncols M)
   | _ => mat_ncols M - Nat.b2n (j <? mat_ncols M)
   end.
Proof.
intros * Hcm.
remember (mat_nrows M) as r eqn:Hr; symmetry in Hr.
destruct r. {
  unfold mat_nrows in Hr.
  apply length_zero_iff_nil in Hr.
  unfold mat_ncols; cbn; rewrite Hr; cbn.
  now rewrite butn_nil.
}
destruct r. {
  rewrite if_eqb_eq_dec.
  destruct M as (ll); cbn - [ "<?" ] in Hr |-*.
  destruct ll as [| l]; [ easy | ].
  destruct ll; [ clear Hr | easy ].
  destruct (Nat.eq_dec i 0) as [Hiz| Hiz]; [ now subst i | ].
  destruct i; [ easy | clear Hiz ].
  cbn - [ "<?" ].
  apply butn_length.
}
destruct (lt_dec j (mat_ncols M)) as [Hjc| Hjc]. {
  apply Nat.ltb_lt in Hjc; rewrite Hjc; cbn.
  apply Nat.ltb_lt in Hjc.
  unfold mat_ncols in Hjc |-*.
  destruct M as (ll); cbn in Hr, Hjc |-*.
  apply is_scm_mat_iff in Hcm.
  unfold mat_ncols in Hcm; cbn in Hcm.
  destruct Hcm as (_, Hcl).
  rewrite (List_map_hd []). 2: {
    rewrite butn_length.
    unfold Nat.b2n.
    rewrite if_ltb_lt_dec.
    rewrite Hr.
    destruct (lt_dec i (S (S r))); cbn; flia.
  }
  rewrite butn_length.
  unfold Nat.b2n.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec j (length (hd [] (butn i ll)))) as [Hjc'| Hjc']. {
    rewrite List_hd_nth_0.
    rewrite nth_butn, Nat.add_0_l.
    unfold Nat.b2n.
    rewrite if_leb_le_dec.
    destruct (le_dec i 0) as [Hiz| Hiz]. {
      rewrite Hcl; [ easy | ].
      apply nth_In; rewrite Hr; flia.
    }
    now rewrite List_hd_nth_0.
  }
  apply Nat.nlt_ge in Hjc'.
  rewrite Nat.sub_0_r.
  rewrite List_hd_nth_0.
  rewrite nth_butn.
  rewrite Nat.add_0_l.
  unfold Nat.b2n.
  rewrite if_leb_le_dec.
  destruct (le_dec i 0) as [Hiz| Hiz]. {
    apply Nat.le_0_r in Hiz; subst i; cbn.
    destruct ll; [ easy | ].
    destruct ll; [ easy | ].
    cbn in Hcl, Hjc, Hjc' |-*.
    rewrite Hcl in Hjc'; [ | now right; left ].
    now apply Nat.nle_gt in Hjc'.
  }
  apply Nat.nle_gt in Hiz.
  rewrite List_hd_nth_0 in Hjc'.
  destruct i; [ flia Hiz | ].
  destruct ll; [ easy | ].
  cbn in Hjc, Hjc'.
  now apply Nat.nlt_ge in Hjc'.
}
apply Nat.ltb_nlt in Hjc; rewrite Hjc, Nat.sub_0_r.
apply Nat.ltb_ge in Hjc.
unfold mat_ncols, subm; cbn.
destruct M as (ll).
cbn in Hr, Hjc |-*.
destruct (lt_dec i (length ll)) as [Hir| Hir]. {
  rewrite (List_map_hd []). 2: {
    rewrite butn_length.
    apply Nat.ltb_lt in Hir; rewrite Hir.
    destruct ll; [ easy | ].
    destruct ll; [ easy | cbn; flia ].
  }
  rewrite butn_length.
  unfold mat_ncols in Hjc; cbn in Hjc.
  rewrite List_hd_nth_0.
  rewrite nth_butn, Nat.add_0_l.
  unfold Nat.b2n.
  rewrite if_leb_le_dec.
  destruct (le_dec i 0) as [Hiz| Hiz]. {
    rewrite if_ltb_lt_dec.
    destruct (lt_dec j (length (nth 1 ll []))) as [Hjl| Hjl]. {
      destruct ll; [ easy | ].
      cbn in Hjl |-*.
      destruct ll; [ easy | ].
      cbn in Hjc, Hjl.
      apply is_scm_mat_iff in Hcm.
      unfold mat_ncols in Hcm; cbn in Hcm.
      destruct Hcm as (_, Hcl).
      rewrite Hcl in Hjl; [ | now right; left ].
      now apply Nat.nlt_ge in Hjc.
    }
    rewrite Nat.sub_0_r.
    destruct ll; [ easy | ].
    destruct ll; [ easy | cbn ].
    apply is_scm_mat_iff in Hcm.
    unfold mat_ncols in Hcm; cbn in Hcm.
    destruct Hcm as (_, Hcl).
    now apply Hcl; right; left.
  }
  clear i Hir Hiz.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec j (length (nth 0 ll []))) as [Hjl| Hjl]. {
    destruct ll; [ easy | ].
    cbn in Hjc, Hjl.
    now apply Nat.nlt_ge in Hjc.
  }
  rewrite Nat.sub_0_r.
  now destruct ll.
}
apply Nat.nlt_ge in Hir.
rewrite butn_out; [ | easy ].
destruct ll; [ easy | cbn ].
rewrite butn_length.
unfold mat_ncols in Hjc; cbn in Hjc.
apply Nat.ltb_ge in Hjc.
now rewrite Hjc, Nat.sub_0_r.
Qed.

Theorem is_squ_mat_subm : ∀ (M : matrix T) i j,
  i < mat_nrows M
  → j < mat_nrows M
  → is_square_matrix M = true
  → is_square_matrix (subm M i j) = true.
Proof.
intros * Hi Hj Hm.
apply is_scm_mat_iff.
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
  rewrite mat_ncols_subm in Hcs. 2: {
    now apply squ_mat_is_corr.
  }
  remember (mat_nrows M) as r eqn:Hr; symmetry in Hr.
  destruct r; [ easy | ].
  destruct r; [ easy | ].
  apply Nat.ltb_lt in Hj; rewrite Hj in Hcs; cbn in Hcs.
  now rewrite Hcm in Hcs.
} {
  intros l Hl.
  apply is_scm_mat_iff in Hm.
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
  → is_correct_matrix A = true
  → is_correct_matrix (subm A i j) = true.
Proof.
intros * Hc1 Ha.
apply is_scm_mat_iff.
split. {
  rewrite mat_nrows_subm.
  unfold Nat.b2n; rewrite if_ltb_lt_dec.
  destruct (lt_dec i (mat_nrows A)) as [Hir| Hir]. {
    destruct (lt_dec j (mat_ncols A)) as [Hjc| Hjc]. {
      destruct (lt_dec 1 (mat_nrows A)) as [H1r| H1r]. {
        rewrite mat_ncols_subm; [ | easy ].
        remember (mat_nrows A) as r eqn:Hr; symmetry in Hr.
        destruct r; [ easy | ].
        destruct r; [ easy | ].
        apply Nat.ltb_lt in Hjc; rewrite Hjc.
        apply Nat.ltb_lt in Hjc.
        intros H; cbn in H.
        destruct (Nat.eq_dec (mat_ncols A) 0) as [Hcz| Hcz]. {
          flia Hjc Hcz.
        }
        flia Hc1 Hcz H.
      }
      apply Nat.nlt_ge in H1r.
      flia H1r Hir.
    }
    apply Nat.nlt_ge in Hjc.
    unfold mat_ncols, subm; cbn.
    rewrite map_butn_out. 2: {
      intros la Hla.
      apply is_scm_mat_iff in Ha.
      destruct Ha as (Hcr, Hc).
      rewrite Hc; [ easy | ].
      now apply in_butn in Hla.
    }
    destruct A as (ll).
    destruct ll as [| la]; [ easy | ].
    apply is_scm_mat_iff in Ha.
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
  apply is_scm_mat_iff in Ha.
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
  apply is_scm_mat_iff in Ha.
  destruct Ha as (Hcr, Hc).
  specialize (in_butn _ _ _ Hla) as H.
  specialize (Hc _ H) as H1; clear H.
  destruct (lt_dec j (mat_ncols A)) as [Hjc| Hjc]. {
    rewrite mat_ncols_subm; [ | now apply is_scm_mat_iff ].
    replace (mat_nrows A) with (S (S (mat_nrows A - 2))) by flia H1r.
    now rewrite butn_length, H1.
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

Theorem mI_transp_idemp : ∀ n, ((mI n)⁺)%M = mI n.
Proof.
intros.
apply matrix_eq; cycle 1. {
  apply mat_transp_is_corr.
  apply mI_is_correct_matrix.
} {
  apply mI_is_correct_matrix.
} {
  rewrite mat_transp_nrows.
  now rewrite mI_nrows, mI_ncols.
} {
  rewrite mat_transp_ncols.
  rewrite mI_nrows, mI_ncols.
  now destruct n.
}
rewrite mat_transp_nrows, mI_ncols.
intros * Hi Hj.
rewrite mat_transp_el; [ | apply mI_is_correct_matrix ].
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  now subst i; destruct (Nat.eq_dec j j).
} {
  rewrite mat_el_mI_ndiag; [ | now apply Nat.neq_sym ].
  rewrite mat_el_mI_ndiag; [ | easy ].
  easy.
}
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
apply is_scm_mat_iff.
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
  apply is_scm_mat_iff in Ha.
  apply is_scm_mat_iff in Hb.
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
  apply is_scm_mat_iff in Ha.
  destruct Ha as (Hcra & Hca).
  rewrite Hca; [ easy | ].
  apply nth_In.
  now rewrite fold_mat_nrows.
} {
  apply is_scm_mat_iff in Hb.
  destruct Hb as (Hcrb & Hcb).
  rewrite Hcb; [ easy | ].
  apply nth_In.
  now rewrite fold_mat_nrows.
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
Arguments mat_add_0_l {T}%type {ro rp} {m n}%nat M%M.
Arguments mat_add_0_r {T}%type {ro rp} {m n}%nat M%M.
Arguments mat_add_add_swap {T}%type {ro rp} (MA MB MC)%M.
Arguments mat_add_assoc {T}%type {ro rp} (MA MB MC)%M.
Arguments mat_add_comm {T}%type {ro rp} (MA MB)%M.
Arguments mat_add_opp_r {T}%type {ro rp} Hop M%M.
Arguments mat_add_sub {T}%type {ro rp} Hop (MA MB)%M.
Arguments mat_list_list {T}%type m%M.
Arguments mat_mul {T}%type {ro} (MA MB)%M.
Arguments mat_mul_add_distr_l {T}%type {ro rp} (MA MB MC)%M.
Arguments mat_mul_assoc {T}%type {ro rp} Hop (MA MB MC)%M.
Arguments mat_mul_el {T}%type {ro} (MA MB)%M (i k)%nat.
Arguments mat_mul_scal_l_add_distr_l {T}%type {ro rp} a%F (MA MB)%M.
Arguments mat_mul_scal_l_add_distr_r {T}%type {ro rp} (a b)%F M%M.
Arguments mat_mul_scal_1_l {T}%type {ro rp} M%M.
Arguments mat_mul_scal_l_mul {T}%type {ro rp} Hop a%F (MA MB)%M.
Arguments mat_mul_scal_l_mul_assoc {T}%type {ro rp} (a b)%F M%M.
Arguments mat_mul_mul_scal_l {T}%type {ro rp} Hop Hic a%F (MA MB)%M.
Arguments mat_mul_scal_l {T ro} s%F M%M.
Arguments mat_mul_vect_r {T ro} M%M V%V.
Arguments mat_mul_scal_vect_comm {T}%type {ro rp} Hop Hic a%F MA%M V%V.
Arguments mat_mul_scal_vect_assoc {T}%type {ro rp} Hop a%F MA%M V%V.
Arguments mat_nrows {T}%type M%M.
Arguments mat_ncols {T}%type M%M.
Arguments mat_vect_mul_assoc {T}%type {ro rp} Hop (A B)%M V%V.
Arguments mat_mul_1_l {T}%type {ro rp} Hop {n}%nat M%M.
Arguments mat_mul_1_r {T}%type {ro rp} Hop {n}%nat M%M.
Arguments mat_opp {T ro} M%M.
Arguments mat_repl_vect_is_square {T}%type {ro} [k]%nat M%M V%V.
Arguments mat_sub {T ro} MA%M MB%M.
Arguments mat_transp {T ro} M%M.
Arguments mat_transp_nrows {T}%type {ro} M%M.
Arguments mI {T ro} n%nat.
Arguments mZ {T ro} (m n)%nat.
Arguments minus_one_pow {T ro}.
Arguments subm {T} M%M i%nat j%nat.
Arguments mat_vect_mul_0_r {T}%type {ro rp} Hop [m n]%nat M%M.
Arguments mat_vect_mul_1_l {T}%type {ro rp} Hop {n}%nat V%V.
Arguments δ {T}%type {ro} (i j)%nat.
Arguments matrix_eq {T ro} (MA MB)%M.
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
