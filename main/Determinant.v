(* determinant *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Require Import Permutation.
Import List List.ListNotations.

Require Import Misc RingLike IterAdd IterMul.
Require Import MyVector Matrix PermutSeq Signature.
Import matrix_Notations.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

(*
   det n M recursively computes determinant

      0     n-1
      |     |
      v     v
     ---------    ---------   ---------   ---------
0    |x      |    | x     |   |  x    |   |   x   |
     | ......| -  |. .....| + |.. ....| - |... ...| + etc.
     | ......|    |. .....|   |.. ....|   |... ...|
n-1  | ......|    |. .....|   |.. ....|   |... ...|
     ---------    ---------   ---------   ---------

   each term is the term "x" multiplied by det (n-1) of
   the sub-matrix represented by the dots. The "x" goes through
   the first row.
*)

Fixpoint determinant_loop n (M : matrix T) :=
  (match n with
   | 0 => λ _, 1%F
   | S n' =>
       λ M' : matrix T,
       ∑ (j = 0, n'),
       minus_one_pow j * mat_el M' 0 j * determinant_loop n' (subm M' 0 j)
   end) M.

Definition det M := determinant_loop (mat_nrows M) M.
Arguments det M%M.

Theorem fold_det : ∀ M, determinant_loop (mat_nrows M) M = det M.
Proof. easy. Qed.

Theorem determinant_zero : ∀ (M : matrix T),
  determinant_loop 0 M = 1%F.
Proof. easy. Qed.

Theorem determinant_succ : ∀ n (M : matrix T),
  determinant_loop (S n) M =
     ∑ (j = 0, n),
     minus_one_pow j * mat_el M 0 j * determinant_loop n (subm M 0 j).
Proof. easy. Qed.

(* Alternative version of the determinant: sum of product of the
   factors a_{i,σ(i)} where σ goes through all permutations of
   the naturals of the interval [0, n-1].
   The permutations generated are in the same order as the
   terms generated by the determinant defined by induction on
   the size of the matrix.
     The order happens to be the canonical (alphabetical) order.
   Example for n=3
     = [[0; 1; 2]; [0; 2; 1]; [1; 0; 2]; [1; 2; 0]; [2; 0; 1]; [2; 1; 0]]
   Having the same terms order, the proof of equality of both definitions
   of both determinants is easy.
   See PermutSeq.v *)

(* definition of determinant by sum of products involving all
   permutations *)
(* known as "Leibniz formula" *)

Definition det' n (M : matrix T) :=
  ∑ (k = 0, fact n - 1),
    ε (canon_sym_gr_list n k) *
    ∏ (i = 1, n), mat_el M (i - 1) (ff_app (canon_sym_gr_list n k) (i - 1)).

Arguments det' n%nat M%M.

(* Proof that both definitions of determinants are equal *)

Theorem det_is_det_by_canon_permut :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  ∀ (M : matrix T),
  is_square_matrix M = true
  → det M = det' (mat_nrows M) M.
Proof.
intros Hic Hop Hin H10 * Hm.
unfold det'.
remember (mat_nrows M) as n eqn:Hr; symmetry in Hr.
unfold det.
rewrite Hr.
revert M Hm Hr.
induction n; intros. {
  cbn.
  rewrite rngl_summation_only_one.
  unfold ε, iter_seq, iter_list; cbn.
  symmetry; apply rngl_mul_1_l.
}
rewrite determinant_succ.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  rewrite rngl_summation_only_one; cbn.
  rewrite rngl_summation_only_one; cbn.
  rewrite rngl_product_only_one; cbn.
  unfold ε.
  do 2 rewrite rngl_product_only_one; cbn.
  now rewrite rngl_mul_1_r.
}
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite IHn; cycle 1. {
    apply is_squ_mat_subm; [ now rewrite Hr | rewrite Hr; flia Hi | easy ].
  } {
    rewrite mat_nrows_subm, Hr; cbn.
    apply Nat.sub_0_r.
  }
  easy.
}
cbn - [ canon_sym_gr_list fact nth ].
clear IHn.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_mul_summation_distr_l; [ | now left ].
  easy.
}
cbn - [ canon_sym_gr_list fact nth ].
rewrite rngl_summation_summation_distr.
rewrite <- Nat.sub_succ_l; [ | apply Nat.neq_0_lt_0, fact_neq_0 ].
rewrite Nat_sub_succ_1.
rewrite <- Nat_fact_succ.
apply rngl_summation_eq_compat.
intros k Hk.
(* elimination of "mat_el M 0 (k / (n!)" *)
symmetry.
rewrite rngl_product_split_first; [ | flia ].
rewrite Nat.sub_diag.
cbn [ canon_sym_gr_list nth ].
remember (mat_el M 0 _) as x eqn:Hx.
rewrite rngl_mul_comm; [ | easy ].
symmetry.
rewrite <- rngl_mul_assoc.
rewrite rngl_mul_comm; [ | easy ].
do 3 rewrite <- rngl_mul_assoc.
f_equal.
(* elimination done *)
(* separation factors "∏" and "ε" *)
rewrite rngl_mul_comm; [ | easy ].
rewrite <- rngl_mul_assoc.
f_equal. {
  (* equality of the two "∏" *)
  rewrite rngl_product_shift; [ | flia Hnz ].
  rewrite (rngl_product_shift _ 2); [ | flia Hnz ].
  rewrite Nat.sub_succ.
  apply rngl_product_eq_compat.
  intros i Hi.
  rewrite Nat.add_comm, Nat.add_sub.
  replace (2 + i - 1) with (S i) by flia.
  unfold mat_el.
  unfold ff_app.
  cbn - [ subm fact ].
  rewrite (List_map_nth' 0); [ | rewrite length_canon_sym_gr_list; flia Hi Hnz ].
  cbn - [ butn ].
  rewrite (List_map_nth' []). 2: {
    apply is_scm_mat_iff in Hm.
    destruct Hm as (Hcr & Hc).
    rewrite butn_length, fold_mat_nrows, Hr.
    cbn; flia Hi Hnz.
  }
  unfold succ_when_ge, Nat.b2n.
  rewrite if_leb_le_dec.
  destruct (le_dec (k / n!) _) as [H1| H1]. {
    rewrite nth_butn_before; [ | easy ].
    rewrite nth_butn_before; [ | easy ].
    now rewrite (Nat.add_1_r i).
  } {
    apply Nat.nle_gt in H1.
    rewrite Nat.add_0_r.
    rewrite nth_butn_after; [ | easy ].
    rewrite nth_butn_before; [ | easy ].
    now rewrite Nat.add_1_r.
  }
  (* end proof equality of the two "∏" *)
}
(* equality of the two "ε" *)
symmetry.
apply ε_of_sym_gr_permut_succ; try easy.
apply (le_lt_trans _ ((S n)! - 1)); [ easy | ].
apply Nat.sub_lt; [ | easy ].
apply Nat.le_succ_l, Nat.neq_0_lt_0, fact_neq_0.
Qed.

(* multilinearity *)

Theorem determinant_multilinear :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  ∀ n (M : matrix T) i a b U V,
  is_square_matrix M = true
  → mat_nrows M = n
  → vect_size U = n
  → vect_size V = n
  → i < n
  → det (mat_repl_vect i M (a × U + b × V)%V) =
       (a * det (mat_repl_vect i M U) +
        b * det (mat_repl_vect i M V))%F.
Proof.
intros Hic Hop Hin H10 * Hsm Hr Hu Hv Hi.
specialize (square_matrix_ncols _ Hsm) as Hcn.
(* using the snd version of determinants: determinant' *)
rewrite det_is_det_by_canon_permut; try easy. 2: {
  apply mat_repl_vect_is_square; [ congruence | cbn | easy ].
  rewrite map2_length.
  do 2 rewrite map_length, fold_vect_size.
  rewrite Hu, Hv.
  now rewrite Nat.min_id.
}
rewrite det_is_det_by_canon_permut; try easy. 2: {
  apply mat_repl_vect_is_square; [ congruence | congruence | easy ].
}
rewrite det_is_det_by_canon_permut; try easy. 2: {
  apply mat_repl_vect_is_square; [ congruence | congruence | easy ].
}
unfold det'.
(* simplification of the lhs *)
remember (a × U + b × V)%V as UV eqn:HUV.
assert (Hvm : vect_size UV = mat_nrows M). {
  rewrite Hr, HUV; cbn.
  rewrite map2_length.
  do 2 rewrite map_length.
  do 2 rewrite fold_vect_size.
  rewrite Hu, Hv.
  apply Nat.min_id.
}
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  assert (Hkn : k < n!). {
    eapply le_lt_trans; [ apply Hk | ].
    rewrite mat_repl_vect_nrows; [ | easy ].
    rewrite Hr.
    apply Nat.sub_lt; [ | flia ].
    apply Nat.neq_0_lt_0, fact_neq_0.
  }
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite HUV in Hj; cbn in Hj.
    do 2 rewrite map2_length in Hj.
    do 2 rewrite map_length in Hj.
    do 2 rewrite fold_vect_size in Hj.
    rewrite fold_mat_nrows, Hr, Hu, Hv in Hj.
    do 2 rewrite Nat.min_id in Hj.
    rewrite mat_el_repl_vect; cycle 1. {
      now apply squ_mat_is_corr.
    } {
      subst UV; cbn.
      rewrite map2_length.
      do 2 rewrite map_length.
      do 2 rewrite fold_vect_size.
      rewrite Hu, Hv, Nat.min_id.
      flia Hj.
    } {
      rewrite Hr; flia Hj.
    } {
      unfold ff_app.
      rewrite Hcn.
      rewrite mat_repl_vect_nrows; [ | easy ].
      rewrite Hr.
      apply canon_sym_gr_list_ub; [ easy | flia Hj ].
    } {
      now rewrite Hcn, Hr.
    }
    unfold vect_el, ff_app.
    cbn - [ Nat.eq_dec ].
    rewrite map2_length, fold_mat_nrows, fold_vect_size.
    rewrite Hvm, Hr, Nat.min_id.
    easy.
  }
  easy.
}
cbn - [ mat_el ].
(* put a and b inside the sigma in the rhs *)
rewrite rngl_mul_summation_distr_l; [ | now left ].
rewrite rngl_mul_summation_distr_l; [ | now left ].
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  rewrite map2_length, fold_mat_nrows, fold_vect_size in Hk |-*.
  rewrite Hr, Hu, Nat.min_id in Hk |-*.
  assert (Hkn : k < fact n). {
    specialize (fact_neq_0 n) as Hnz.
    flia Hk Hnz.
  }
  rewrite rngl_mul_assoc.
  rewrite (rngl_mul_comm Hic a).
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite mat_el_repl_vect; cycle 1. {
      now apply squ_mat_is_corr.
    } {
      rewrite Hu; flia Hj.
    } {
      rewrite Hr; flia Hj.
    } {
      cbn.
      rewrite Hcn, Hr.
      apply canon_sym_gr_list_ub; [ easy | flia Hj ].
    } {
      now rewrite Hcn, Hr.
    }
    now unfold vect_el, ff_app; cbn.
  }
  easy.
}
do 3 rewrite map2_length, fold_mat_nrows, fold_vect_size.
rewrite Hvm, Hr, Hu, Hv, Nat.min_id.
rewrite rngl_add_comm.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  assert (Hkn : k < fact n). {
    specialize (fact_neq_0 n) as Hnz.
    flia Hk Hnz.
  }
  rewrite rngl_mul_assoc.
  rewrite (rngl_mul_comm Hic b).
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite mat_el_repl_vect; cycle 1. {
      now apply squ_mat_is_corr.
    } {
      rewrite Hv; flia Hj.
    } {
      rewrite Hr; flia Hj.
    } {
      rewrite Hcn, Hr.
      apply canon_sym_gr_list_ub; [ easy | flia Hj ].
    } {
      now rewrite Hcn, Hr.
    }
    now unfold vect_el, ff_app; cbn.
  }
  easy.
}
rewrite rngl_add_comm.
(* make one summation *)
rewrite <- rngl_summation_add_distr.
apply rngl_summation_eq_compat.
intros k Hk.
do 2 rewrite <- rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_l.
(* elimination of the ε-s *)
f_equal.
(* *)
assert (Hkn : k < fact n). {
  specialize (fact_neq_0 n) as Hnz.
  flia Hk Hnz.
}
specialize (canon_sym_gr_surjective Hkn Hi) as Hp.
destruct Hp as (p & Hp & Hpp).
rewrite (rngl_product_split (p + 1)); [ | flia Hp ].
rewrite rngl_product_split_last; [ | flia ].
erewrite rngl_product_eq_compat. 2: {
  intros j Hj.
  replace (j - 1 - 1) with (j - 2) by flia.
  destruct (Nat.eq_dec (nth (j - 2) (canon_sym_gr_list n k) 0) i)
    as [Hpj| Hpj]. {
    exfalso.
    rewrite <- Hpp in Hpj.
    apply nth_canon_sym_gr_list_inj1 in Hpj; [ | easy | flia Hp Hj | easy ].
    flia Hj Hpj.
  }
  easy.
}
rewrite (rngl_mul_comm Hic (iter_seq _ _ _ _)).
rewrite rngl_add_comm.
rewrite (rngl_product_split (p + 1)); [ | flia Hp ].
rewrite rngl_product_split_last; [ | flia ].
erewrite rngl_product_eq_compat. 2: {
  intros j Hj.
  replace (j - 1 - 1) with (j - 2) by flia.
  destruct (Nat.eq_dec (nth (j - 2) (canon_sym_gr_list n k) 0) i)
    as [Hpj| Hpj]. {
    exfalso.
    rewrite <- Hpp in Hpj.
    apply nth_canon_sym_gr_list_inj1 in Hpj; [ | easy | flia Hp Hj | easy ].
    flia Hj Hpj.
  }
  easy.
}
rewrite (rngl_mul_comm Hic (iter_seq _ _ _ _)).
rewrite rngl_add_comm.
symmetry.
rewrite (rngl_product_split (p + 1)); [ | flia Hp ].
rewrite rngl_product_split_last; [ | flia ].
erewrite rngl_product_eq_compat. 2: {
  intros j Hj.
  replace (j - 1 - 1) with (j - 2) by flia.
  destruct (Nat.eq_dec (nth (j - 2) (canon_sym_gr_list n k) 0) i)
    as [Hpj| Hpj]. {
    exfalso.
    rewrite <- Hpp in Hpj.
    apply nth_canon_sym_gr_list_inj1 in Hpj; [ | easy | flia Hp Hj | easy ].
    flia Hj Hpj.
  }
  easy.
}
rewrite (rngl_mul_comm Hic (iter_seq _ _ _ _)).
rewrite Nat.add_sub.
unfold ff_app in Hpp.
rewrite Hpp.
destruct (Nat.eq_dec i i) as [H| H]; [ clear H | easy ].
do 4 rewrite rngl_mul_assoc.
subst UV.
cbn - [ mat_el ].
rewrite map2_nth with (a := 0%F) (b := 0%F); cycle 1. {
  now rewrite map_length, fold_vect_size, Hu.
} {
  now rewrite map_length, fold_vect_size, Hv.
}
rewrite (List_map_nth' 0%F); [ | now rewrite fold_vect_size, Hu ].
rewrite (List_map_nth' 0%F); [ | now rewrite fold_vect_size, Hv ].
do 2 rewrite fold_vect_el.
(* elimination of the following term (q) *)
remember
  (∏ (i0 = 2, p + 1),
   mat_el M (i0 - 2) (nth (i0 - 2) (canon_sym_gr_list n k) O))
  as q eqn:Hq.
rewrite (rngl_mul_mul_swap Hic _ _ q).
do 3 rewrite (rngl_mul_comm Hic _ q).
do 5 rewrite <- rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_l.
f_equal.
clear q Hq.
erewrite rngl_product_eq_compat. 2: {
  intros j Hj.
  destruct (Nat.eq_dec (nth (j - 1) (canon_sym_gr_list n k) 0) i)
    as [Hpj| Hpj]. {
    rewrite <- Hpp in Hpj.
    apply nth_canon_sym_gr_list_inj1 in Hpj; [ | easy | flia Hp Hj | easy ].
    flia Hj Hpj.
  }
  easy.
}
symmetry.
erewrite rngl_product_eq_compat. 2: {
  intros j Hj.
  destruct (Nat.eq_dec (nth (j - 1) (canon_sym_gr_list n k) 0) i)
    as [Hpj| Hpj]. {
    rewrite <- Hpp in Hpj.
    apply nth_canon_sym_gr_list_inj1 in Hpj; [ | easy | flia Hp Hj | easy ].
    flia Hj Hpj.
  }
  easy.
}
rewrite rngl_add_comm.
erewrite rngl_product_eq_compat. 2: {
  intros j Hj.
  destruct (Nat.eq_dec (nth (j - 1) (canon_sym_gr_list n k) 0) i)
    as [Hpj| Hpj]. {
    rewrite <- Hpp in Hpj.
    apply nth_canon_sym_gr_list_inj1 in Hpj; [ | easy | flia Hp Hj | easy ].
    flia Hj Hpj.
  }
  easy.
}
cbn.
rewrite rngl_add_comm.
do 2 rewrite rngl_mul_assoc.
now rewrite <- rngl_mul_add_distr_r.
Qed.

Definition mat_swap_rows i1 i2 (M : matrix T) :=
  mk_mat (list_swap_elem [] (mat_list_list M) i1 i2).

Theorem mat_swap_rows_is_square : ∀ (M : matrix T) p q,
  p < mat_nrows M
  → q < mat_nrows M
  → is_square_matrix M = true
  → is_square_matrix (mat_swap_rows p q M) = true.
Proof.
intros * Hp Hq Hsm.
remember (mat_nrows M) as n eqn:Hr.
symmetry in Hr.
specialize (square_matrix_ncols _ Hsm) as Hcn.
specialize (squ_mat_is_corr M Hsm) as Hco.
apply is_scm_mat_iff in Hsm.
apply is_scm_mat_iff.
destruct Hsm as (Hcr & Hc).
cbn; unfold list_swap_elem.
rewrite List_map_seq_length.
unfold mat_swap_rows, list_swap_elem; cbn.
split. {
  unfold mat_ncols; cbn.
  rewrite fold_mat_nrows; rewrite Hr.
  rewrite (List_map_hd 0); [ | rewrite seq_length; flia Hp ].
  rewrite List_seq_hd; [ | flia Hp ].
  rewrite Hc; [ now intros Hn; subst n | ].
  apply nth_In; rewrite fold_mat_nrows; rewrite Hr.
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec 0 p); [ easy | ].
  destruct (Nat.eq_dec 0 q); [ easy | ].
  flia Hp.
} {
  intros la Hla.
  apply in_map_iff in Hla.
  rewrite fold_mat_nrows, Hr in Hla.
  destruct Hla as (a & Ha & Hla).
  apply in_seq in Hla; subst la.
  rewrite fold_corr_mat_ncols; [ easy | easy | rewrite Hr ].
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec a p); [ easy | ].
  destruct (Nat.eq_dec a q); [ easy | ].
  easy.
}
Qed.

Theorem mat_swap_rows_nrows : ∀ (M : matrix T) p q,
  mat_nrows (mat_swap_rows p q M) = mat_nrows M.
Proof.
intros.
unfold mat_swap_rows; cbn.
unfold list_swap_elem.
rewrite map_length.
now rewrite seq_length.
Qed.

Theorem nth_transposition_canon_sym_gr_list_inj : ∀ n k p q i j,
  k < n!
  → p < n
  → q < n
  → i < n
  → j < n
  → nth (transposition p q i) (canon_sym_gr_list n k) 0 =
    nth (transposition p q j) (canon_sym_gr_list n k) 0
  → i = j.
Proof.
intros * Hkn Hpn Hqn Hin Hjn Hij.
unfold transposition in Hij.
do 4 rewrite if_eqb_eq_dec in Hij.
destruct (Nat.eq_dec i p) as [Hip| Hip]. {
  destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ congruence | ].
  destruct (Nat.eq_dec j q) as [Hjq| Hjq]. {
    apply nth_canon_sym_gr_list_inj1 in Hij; [ | easy | easy | easy ].
    congruence.
  }
  apply Nat.neq_sym in Hjq.
  now apply nth_canon_sym_gr_list_inj1 in Hij.
}
destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
  destruct (Nat.eq_dec j p) as [Hjp| Hjp]. {
    apply nth_canon_sym_gr_list_inj1 in Hij; [ | easy | easy | easy ].
    congruence.
  }
  destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ congruence | ].
  apply Nat.neq_sym in Hjp.
  now apply nth_canon_sym_gr_list_inj1 in Hij.
}
destruct (Nat.eq_dec j p) as [Hjp| Hjp]. {
  now apply nth_canon_sym_gr_list_inj1 in Hij.
}
destruct (Nat.eq_dec j q) as [Hjq| Hjq]. {
  now apply nth_canon_sym_gr_list_inj1 in Hij.
}
now apply nth_canon_sym_gr_list_inj1 in Hij.
Qed.

Theorem determinant_alternating : in_charac_0_field →
  ∀ (M : matrix T) p q,
  p ≠ q
  → p < mat_nrows M
  → q < mat_nrows M
  → is_square_matrix M = true
  → det (mat_swap_rows p q M) = (- det M)%F.
Proof.
intros Hif * Hpq Hp Hq Hsm.
remember (mat_nrows M) as n eqn:Hr; symmetry in Hr.
rewrite det_is_det_by_canon_permut; try now destruct Hif. 2: {
  rewrite <- Hr in Hp, Hq.
  now apply mat_swap_rows_is_square.
}
unfold det'.
rewrite mat_swap_rows_nrows.
rewrite Hr.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  rewrite rngl_product_shift; [ | flia Hp ].
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  easy.
}
cbn - [ mat_swap_rows ].
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  rewrite rngl_product_change_var with
    (g := transposition p q) (h := transposition p q). 2: {
    intros i Hi.
    apply transposition_involutive.
  }
  rewrite Nat.sub_0_r.
  rewrite <- Nat.sub_succ_l; [ | flia Hp ].
  rewrite Nat_sub_succ_1.
  easy.
}
cbn - [ mat_swap_rows ].
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  destruct Hif as (Hic & Hop & Hin & H10 & Hit & Hde & Hch) in Hsm.
  rewrite rngl_product_list_permut with (l2 := seq 0 n); [ | easy | ]. 2: {
    apply permut_list_Permutation.
    now apply transposition_is_permut.
  }
  easy.
}
cbn - [ mat_swap_rows ].
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  assert (Hkn : k < n!). {
    specialize (fact_neq_0 n) as Hn.
    flia Hk Hn.
  }
  erewrite rngl_product_list_eq_compat. 2: {
    intros i Hi.
    replace (mat_el _ _ _) with
      (mat_el M i
         (ff_app (canon_sym_gr_list n k) (transposition p q i))). 2: {
      unfold ff_app; cbn.
      unfold mat_el; f_equal.
      unfold list_swap_elem.
      rewrite (List_map_nth' 0). 2: {
        rewrite seq_length.
        rewrite fold_mat_nrows, Hr.
        apply in_seq in Hi.
        now apply transposition_lt.
      }
      rewrite fold_mat_nrows, Hr.
      unfold transposition.
      do 2 rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec i p) as [Hip| Hip]. {
        subst i.
        rewrite seq_nth; [ | easy ].
        rewrite Nat.add_0_l.
        rewrite Nat.eqb_refl.
        apply Nat.neq_sym in Hpq.
        now destruct (Nat.eq_dec q p).
      }
      rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
        subst i.
        rewrite seq_nth; [ | easy ].
        rewrite Nat.add_0_l.
        rewrite <- if_eqb_eq_dec.
        now rewrite Nat.eqb_refl.
      }
      apply in_seq in Hi.
      rewrite seq_nth; [ | easy ].
      rewrite Nat.add_0_l.
      rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec i p) as [H| H]; [ easy | clear H ].
      now destruct (Nat.eq_dec i q).
    }
    easy.
  }
  easy.
}
cbn.
set (f := λ k, list_swap_elem 0 (canon_sym_gr_list n k) p q).
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  erewrite rngl_product_list_eq_compat. 2: {
    intros i Hi.
    apply in_seq in Hi.
    replace (ff_app _ _) with
       (ff_app (list_swap_elem 0 (canon_sym_gr_list n k) p q) i). 2: {
(* lemme à faire *)
      unfold list_swap_elem.
      unfold ff_app.
      rewrite (List_map_nth' 0). 2: {
        now rewrite seq_length, length_canon_sym_gr_list.
      }
      rewrite seq_nth; [ easy | now rewrite length_canon_sym_gr_list ].
    }
    fold (f k).
    easy.
  }
  easy.
}
cbn.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  assert (Hkn : k < n!). {
    specialize (fact_neq_0 n) as Hn.
    flia Hk Hn.
  }
  erewrite rngl_product_seq_product; [ | flia Hp ].
  rewrite Nat.add_0_l.
  replace (canon_sym_gr_list n k) with
     (map (λ i, ff_app (f k) (transposition p q i)) (seq 0 n)). 2: {
    rewrite List_map_nth_seq with (d := 0).
    rewrite length_canon_sym_gr_list.
    apply map_ext_in.
    intros i Hi; cbn.
    apply in_seq in Hi.
    unfold ff_app, f, list_swap_elem.
    rewrite (List_map_nth' 0). 2: {
      rewrite seq_length, length_canon_sym_gr_list.
      now apply transposition_lt.
    }
    rewrite seq_nth. 2: {
      rewrite length_canon_sym_gr_list.
      now apply transposition_lt.
    }
    rewrite Nat.add_0_l.
    now rewrite transposition_involutive.
  }
  replace (map (λ i, ff_app (f k) (transposition p q i)) (seq 0 n))
  with (f k ° map (λ i, transposition p q i) (seq 0 n)). 2: {
    unfold "°"; cbn.
    now rewrite map_map.
  }
  rewrite signature_comp with (n0 := n); [ easy | easy | | ]. {
    split. 2: {
      unfold f.
      rewrite length_list_swap_elem.
      apply length_canon_sym_gr_list.
    }
    split. {
      intros i Hi.
      apply In_nth with (d := 0) in Hi.
      destruct Hi as (j & Hj & Hji).
      rewrite <- Hji.
      apply permut_list_ub; [ | easy ].
      unfold f.
      apply list_swap_elem_is_permut_list. {
        now rewrite length_canon_sym_gr_list.
      } {
        now rewrite length_canon_sym_gr_list.
      } {
        now apply canon_sym_gr_list_is_permut.
      }
    }
    unfold f, ff_app.
    rewrite length_list_swap_elem.
    rewrite length_canon_sym_gr_list.
    intros i j Hi Hj Hij.
(* lemme à faire ? *)
    unfold list_swap_elem in Hij.
    rewrite (List_map_nth' 0) in Hij. 2: {
      now rewrite seq_length, length_canon_sym_gr_list.
    }
    rewrite (List_map_nth' 0) in Hij. 2: {
      now rewrite seq_length, length_canon_sym_gr_list.
    }
    rewrite seq_nth in Hij; [ | now rewrite length_canon_sym_gr_list ].
    rewrite seq_nth in Hij; [ | now rewrite length_canon_sym_gr_list ].
    cbn in Hij.
    now apply nth_transposition_canon_sym_gr_list_inj in Hij.
  }
  now apply transposition_is_permut.
}
cbn.
erewrite rngl_summation_eq_compat. 2: {
  intros k (_, Hk).
  destruct Hif as (Hic & Hop & Hin & H10 & Hit & Hde & Hch) in Hsm.
  rewrite (rngl_mul_comm Hic (ε (f k))).
  rewrite <- rngl_mul_assoc.
  now rewrite transposition_signature.
}
cbn - [ f ].
rewrite <- rngl_mul_summation_distr_l; [ | now destruct Hif; left ].
rewrite rngl_mul_opp_l; [ | now destruct Hif ].
f_equal.
rewrite rngl_mul_1_l.
symmetry.
set (g := λ k, canon_sym_gr_list_inv n (f k)).
rewrite rngl_summation_change_var with (g0 := g) (h := g). 2: {
  intros k (_, Hk).
  assert (Hkn : k < n!). {
    specialize (fact_neq_0 n) as Hn.
    flia Hk Hn.
  }
  unfold g, f.
  unfold list_swap_elem.
  do 2 rewrite length_canon_sym_gr_list.
  erewrite map_ext_in. 2: {
    intros i Hi; apply in_seq in Hi.
    rewrite permut_in_canon_sym_gr_of_its_rank. 2: {
(* lemme à faire ? *)
      split; [ | now rewrite map_length, seq_length ].
      split. {
        intros j Hj.
        rewrite map_length, seq_length.
        apply in_map_iff in Hj.
        destruct Hj as (m & Hmj & Hm).
        apply in_seq in Hm.
        rewrite <- Hmj.
        apply canon_sym_gr_list_ub; [ easy | ].
        now apply transposition_lt.
      } {
        rewrite map_length, seq_length.
        intros u v Hu Hv.
        unfold ff_app.
        rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
        rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
        rewrite seq_nth; [ | easy ].
        rewrite seq_nth; [ | easy ].
        do 2 rewrite Nat.add_0_l.
        intros Huv.
        now apply nth_transposition_canon_sym_gr_list_inj in Huv.
      }
    }
    rewrite (List_map_nth' 0). 2: {
      now rewrite seq_length; apply transposition_lt.
    }
    rewrite seq_nth; [ | now apply transposition_lt ].
    rewrite Nat.add_0_l.
    rewrite transposition_involutive.
    easy.
  }
  rewrite <- List_map_nth_seq'; [ | now rewrite length_canon_sym_gr_list ].
  now apply canon_sym_gr_inv_of_canon_sym_gr.
}
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | apply Nat.neq_0_lt_0, fact_neq_0 ].
rewrite Nat_sub_succ_1.
rewrite rngl_summation_list_permut with (l2 := seq 0 n!). 2: {
  apply permut_list_Permutation.
(* lemma to do? *)
  unfold g, f.
  split; [ | now rewrite map_length, seq_length ].
  split. {
    intros i Hi.
    rewrite map_length, seq_length.
    apply in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj).
    apply in_seq in Hj.
    rewrite <- Hji.
    apply canon_sym_gr_list_inv_ub.
    apply list_swap_elem_is_permut; [ easy | easy | ].
    now apply canon_sym_gr_list_is_permut.
  } {
    rewrite map_length, seq_length.
    intros i j Hi Hj Hij.
    unfold ff_app in Hij.
    rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
    rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
    rewrite seq_nth in Hij; [ | easy ].
    rewrite seq_nth in Hij; [ | easy ].
    do 2 rewrite Nat.add_0_l in Hij.
(* lemme à faire ? *)
    apply rank_of_permut_in_canon_gr_list_inj in Hij; cycle 1. {
      apply list_swap_elem_is_permut; [ easy | easy | ].
      now apply canon_sym_gr_list_is_permut.
    } {
      apply list_swap_elem_is_permut; [ easy | easy | ].
      now apply canon_sym_gr_list_is_permut.
    }
(* lemme à faire ? *)
    unfold list_swap_elem in Hij.
    do 2 rewrite length_canon_sym_gr_list in Hij.
    apply nth_canon_sym_gr_list_inj2 with (n := n); [ easy | easy | ].
    intros k Hkn.
    apply ext_in_map with (a := transposition p q k) in Hij. 2: {
      apply in_seq.
      split; [ flia | ].
      now apply transposition_lt.
    }
    now rewrite transposition_involutive in Hij.
  }
}
rewrite det_is_det_by_canon_permut; try now destruct Hif.
rewrite Hr.
unfold det'.
rewrite rngl_summation_seq_summation; [ | apply fact_neq_0 ].
rewrite Nat.add_0_l.
apply rngl_summation_eq_compat.
intros k Hk.
assert (Hkn : k < n!). {
  specialize (fact_neq_0 n) as Hn.
  flia Hk Hn.
}
assert (Hc : canon_sym_gr_list n k = f (g k)). {
  unfold g, f.
  rewrite permut_in_canon_sym_gr_of_its_rank. 2: {
    apply list_swap_elem_is_permut; [ easy | easy | ].
    now apply canon_sym_gr_list_is_permut.
  }
  rewrite list_swap_elem_involutive; [ easy | | ]. {
    now rewrite length_canon_sym_gr_list.
  } {
    now rewrite length_canon_sym_gr_list.
  }
}
f_equal; [ now rewrite Hc | ].
rewrite rngl_product_shift; [ | flia Hp ].
apply rngl_product_eq_compat.
intros i Hi.
rewrite Nat.add_comm, Nat.add_sub.
now rewrite Hc.
Qed.

Theorem determinant_same_rows : in_charac_0_field →
  ∀ (M : matrix T) p q,
  is_square_matrix M = true
  → p ≠ q
  → p < mat_nrows M
  → q < mat_nrows M
  → (∀ j, mat_el M p j = mat_el M q j)
  → det M = 0%F.
Proof.
intros (Hic & Hop & Hin & H10 & Hit & Hde & Hch) * Hsm Hpq Hpn Hqn Hjpq.
remember (mat_nrows M) as n eqn:Hr; symmetry in Hr.
specialize (square_matrix_ncols M Hsm) as Hc.
assert (HM : det M = (- det M)%F). {
  rewrite <- Hr in Hpn, Hqn.
  rewrite <- determinant_alternating with (p := p) (q := q); try easy.
  f_equal.
  destruct M as (ll); cbn in *.
  unfold mat_swap_rows; cbn; f_equal.
  rewrite (List_map_nth_seq ll) with (d := []) at 1.
  apply map_ext_in.
  intros i Hi; apply in_seq in Hi.
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec i p) as [Hip| Hip]. {
    subst i.
    rewrite List_map_nth_seq with (d := 0%F); symmetry.
    rewrite List_map_nth_seq with (d := 0%F); symmetry.
    apply is_scm_mat_iff in Hsm.
    cbn in Hsm.
    destruct Hsm as (Hcz, Hsm).
    rewrite Hsm; [ | now apply nth_In ].
    rewrite Hsm; [ | now apply nth_In ].
    apply map_ext_in.
    intros j Hj.
    apply Hjpq.
  }
  destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
    subst i.
    rewrite List_map_nth_seq with (d := 0%F); symmetry.
    rewrite List_map_nth_seq with (d := 0%F); symmetry.
    apply is_scm_mat_iff in Hsm.
    cbn in Hsm.
    destruct Hsm as (Hcz, Hsm).
    rewrite Hsm; [ | now apply nth_In ].
    rewrite Hsm; [ | now apply nth_In ].
    apply map_ext_in.
    intros j Hj.
    symmetry; apply Hjpq.
  }
  easy.
}
apply rngl_add_move_0_r in HM; [ | easy ].
apply eq_rngl_add_same_0 in HM; try easy; [ now left | ].
apply Bool.orb_true_iff.
now left.
Qed.

(* transpositions list of permutation *)

Fixpoint first_non_fixpoint it i σ :=
  match it with
  | 0 => None
  | S it' => if i =? σ i then first_non_fixpoint it' (i + 1) σ else Some i
  end.

Fixpoint tlopf_loop it n (σ : nat → nat) :=
  match it with
  | 0 => []
  | S it' =>
      match first_non_fixpoint n 0 σ with
      | None => []
      | Some i =>
          let σ' := comp (transposition i (σ i)) σ in
          (i, σ i) :: tlopf_loop it' n σ'
      end
  end.

(* *)

Definition mat_mul_row_by_scal n k (M : matrix T) s :=
  mk_mat
    (map
       (λ i,
        map
          (λ j, if Nat.eq_dec i k then (s * mat_el M i j)%F else mat_el M i j)
          (seq 0 n))
       (seq 0 n)).

(* If we multiply a row (column) of A by a number, the determinant of
   A will be multiplied by the same number. *)
(* https://math.vanderbilt.edu/sapirmv/msapir/proofdet1.html
   point 1 *)

(* If the i-th row (column) in A is a sum of the i-th row (column) of
   a matrix B and the i-th row (column) of a matrix C and all other
   rows in B and C are equal to the corresponding rows in A (that is B
   and C differ from A by one row only), then det(A)=det(B)+det(C). *)
(* https://math.vanderbilt.edu/sapirmv/msapir/proofdet1.html
   point 2 *)

(* Well, since my definition of the discriminant only covers the
   row 0, we can prove that only when i=0; this will able us to
   prove the next theorem, swapping rows by going via row 0 *)

Theorem det_add_row_row : ∀ n (A B C : matrix T),
  n ≠ 0
  → mat_nrows A = n
  → mat_nrows B = n
  → mat_nrows C = n
  → is_square_matrix A = true
  → is_square_matrix B = true
  → is_square_matrix C = true
  → (∀ j, mat_el A 0 j = (mat_el B 0 j + mat_el C 0 j)%F)
  → (∀ i j, i ≠ 0 → mat_el B i j = mat_el A i j)
  → (∀ i j, i ≠ 0 → mat_el C i j = mat_el A i j)
  → det A = (det B + det C)%F.
Proof.
intros * Hnz Hra Hrb Hrc Hsma Hsmb Hsmc Hbc Hb Hc.
specialize (square_matrix_ncols _ Hsma) as Hca.
specialize (square_matrix_ncols _ Hsmb) as Hcb.
rewrite Hra in Hca.
rewrite Hrb in Hcb.
destruct n; [ easy | clear Hnz; cbn ].
assert (Hab : ∀ j, subm A 0 j = subm B 0 j). {
  intros.
  destruct A as (lla).
  destruct B as (llb).
  cbn in *.
  unfold subm; f_equal.
  cbn - [ butn ].
  rewrite (List_map_nth_seq lla []).
  rewrite (List_map_nth_seq llb []).
  rewrite Hra, Hrb.
  do 2 rewrite <- map_butn.
  do 2 rewrite map_map.
  apply map_ext_in.
  intros u Hu.
  destruct (Nat.eq_dec u 0) as [Huz| Huz]. {
    subst u; cbn in Hu.
    now apply in_seq in Hu.
  }
  rewrite (List_map_nth_seq (nth u lla []) 0%F).
  rewrite (List_map_nth_seq (nth u llb []) 0%F).
  apply is_scm_mat_iff in Hsma.
  destruct Hsma as (_ & Hca').
  apply in_butn, in_seq in Hu.
  rewrite Hca'. 2: {
    cbn; apply nth_In.
    now rewrite Hra.
  }
  apply is_scm_mat_iff in Hsmb.
  destruct Hsmb as (_ & Hcb').
  rewrite Hcb'. 2: {
    cbn; apply nth_In.
    now rewrite Hrb.
  }
  f_equal; cbn; rewrite Hra, Hrb.
  apply map_ext_in.
  intros v Hv.
  apply in_seq in Hv.
  now symmetry; apply Hb.
}
assert (Hac : ∀ j, subm A 0 j = subm C 0 j). {
  intros.
  intros.
  destruct A as (lla).
  destruct C as (llc).
  cbn in *.
  unfold subm; f_equal.
  cbn - [ butn ].
  rewrite (List_map_nth_seq lla []).
  rewrite (List_map_nth_seq llc []).
  rewrite Hra, Hrc.
  do 2 rewrite <- map_butn.
  do 2 rewrite map_map.
  apply map_ext_in.
  intros u Hu.
  destruct (Nat.eq_dec u 0) as [Huz| Huz]. {
    subst u; cbn in Hu.
    now apply in_seq in Hu.
  }
  rewrite (List_map_nth_seq (nth u lla []) 0%F).
  rewrite (List_map_nth_seq (nth u llc []) 0%F).
  apply is_scm_mat_iff in Hsma.
  destruct Hsma as (_ & Hca').
  apply in_butn, in_seq in Hu.
  rewrite Hca'. 2: {
    cbn; apply nth_In.
    now rewrite Hra.
  }
  apply is_scm_mat_iff in Hsmc.
  destruct Hsmc as (_ & Hcc').
  rewrite Hcc'. 2: {
    cbn; apply nth_In.
    now rewrite Hrc.
  }
  f_equal; cbn; rewrite Hra, Hrc.
  apply map_ext_in.
  intros v Hv.
  apply in_seq in Hv.
  now symmetry; apply Hc.
}
unfold det; rewrite Hra, Hrb, Hrc.
cbn.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite Hbc.
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_add_distr_r.
  rewrite Hab at 1.
  rewrite Hac at 1.
  easy.
}
cbn.
now apply rngl_summation_add_distr.
Qed.

End a.

Arguments det {T ro} M%M.
Arguments det' {T}%type {ro} n%nat M%M.
Arguments determinant_alternating {T}%type {ro rp} _ M%M [p q]%nat.
Arguments determinant_loop {T}%type {ro} n%nat M%M.
Arguments determinant_same_rows {T}%type {ro rp} _ M%M [p q]%nat.
Arguments det_is_det_by_canon_permut {T}%type {ro rp} _ M%M.
Arguments subm {T} M%M i%nat j%nat.
