(* comatrices *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Import List.ListNotations.

Require Import Misc RingLike IterAdd IterMul Pigeonhole.
Require Import PermutationFun SortingFun SortRank.
Require Import Matrix PermutSeq Signature Determinant.
Require Import MyVector.
Import matrix_Notations.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Definition com (M : matrix T) : matrix T :=
  mk_mat
    (List.map
      (λ i,
       List.map (λ j, (minus_one_pow (i + j) * det (subm i j M))%L)
         (List.seq 1 (mat_ncols M)))
      (List.seq 1 (mat_nrows M))).

Theorem mat_swap_same_rows : ∀ (M : matrix T) i,
  mat_swap_rows i i M = M.
Proof.
intros.
destruct M as (ll); cbn.
unfold mat_swap_rows; f_equal.
cbn - [ list_swap_elem ].
rewrite (List_map_nth_seq (List.nth i ll []) ll) at 2.
unfold list_swap_elem.
apply List.map_ext_in.
intros j Hj; apply List.in_seq in Hj.
rewrite transposition_id.
now apply List.nth_indep.
Qed.

Theorem mat_swap_rows_comm : ∀ (M : matrix T) p q,
  mat_swap_rows p q M = mat_swap_rows q p M.
Proof.
intros.
unfold mat_swap_rows; f_equal; cbn.
unfold list_swap_elem.
apply List.map_ext_in.
intros i Hi; apply List.in_seq in Hi.
now rewrite transposition_comm.
Qed.

Theorem subm_mat_swap_rows_lt_lt : ∀ (M : matrix T) p q r j,
  p < q < r
  → subm r j (mat_swap_rows p q M) = mat_swap_rows p q (subm r j M).
Proof.
intros * (Hpq, Hq).
destruct M as (ll); cbn.
unfold subm, mat_swap_rows; cbn; f_equal.
rewrite List.length_map.
rewrite List_length_butn.
rewrite <- List_map_butn, List.map_map.
rewrite List_map_butn_seq.
rewrite Nat.add_0_l.
apply List.map_ext_in.
intros i Hi; apply List.in_seq in Hi.
unfold Nat.b2n.
rewrite if_leb_le_dec.
destruct Hi as (_, Hi).
destruct (le_dec (r - 1) i) as [Hir| Hir]. 2: {
  apply Nat.nle_gt in Hir.
  rewrite Nat.add_0_r.
  destruct (Nat.eq_dec i (p - 1)) as [Hip| Hip]. {
    subst i; clear Hir.
    rewrite transposition_1.
    destruct (lt_dec (q - 1) (length (List_butn (r - 1) ll)))
        as [Hqrl| Hqrl]. {
      rewrite (List_map_nth' []); [ | easy ].
      rewrite List_nth_butn_after; [ easy | flia Hpq Hq ].
    }
    apply Nat.nlt_ge in Hqrl.
    symmetry.
    rewrite List.nth_overflow; [ | now rewrite List.length_map ].
    rewrite List_length_butn in Hqrl.
    destruct (le_dec (length ll) (q - 1)) as [Hlq| Hlq]. {
      rewrite List.nth_overflow; [ | easy ].
      now rewrite List_butn_nil.
    }
    apply Nat.nle_gt in Hlq.
    unfold Nat.b2n in Hi, Hqrl.
    rewrite if_ltb_lt_dec in Hi, Hqrl.
    destruct (lt_dec (r - 1) (length ll)) as [Hrl| Hrl]; [ | flia Hqrl Hlq ].
    flia Hq Hrl Hi Hqrl.
  }
  destruct (Nat.eq_dec i (q - 1)) as [Hiq| Hiq]. {
    subst i; clear Hir.
    rewrite transposition_2.
    destruct (lt_dec (p - 1) (length (List_butn (r - 1) ll)))
        as [Hprl| Hprl]. {
      rewrite (List_map_nth' []); [ | easy ].
      rewrite List_nth_butn_after; [ easy | flia Hpq Hq ].
    }
    apply Nat.nlt_ge in Hprl.
    rewrite List_length_butn in Hprl.
    flia Hpq Hi Hprl.
  }
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec i (p - 1)) as [H| H]; [ easy | clear H ].
  destruct (Nat.eq_dec i (q - 1)) as [H| H]; [ easy | clear H ].
  rewrite List_map_butn.
  rewrite List_nth_butn_after; [ | easy ].
  rewrite (List_map_nth' []); [ easy | flia Hi ].
}
unfold transposition.
do 4 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec i (p - 1)) as [H| H]; [ flia Hpq Hq Hir H | clear H ].
destruct (Nat.eq_dec i (q - 1)) as [H| H]; [ flia Hpq Hq Hir H | clear H ].
destruct (Nat.eq_dec (i + 1) (p - 1)) as [H| H]; [ flia Hpq Hq Hir H | ].
clear H.
destruct (Nat.eq_dec (i + 1) (q - 1)) as [H| H]; [ flia Hq Hir H | clear H ].
rewrite List_map_butn.
rewrite List_nth_butn_before; [ | easy ].
rewrite (List_map_nth' []); [ easy | ].
unfold Nat.b2n in Hi.
rewrite if_ltb_lt_dec in Hi.
destruct (lt_dec (r - 1) (length ll)) as [Hrl| Hrl]; [ flia Hi Hir | ].
flia Hrl Hi Hir.
Qed.

Theorem subm_mat_swap_rows_lt : ∀ (M : matrix T) p q r j,
  p < r
  → q < r
  → subm r j (mat_swap_rows p q M) = mat_swap_rows p q (subm r j M).
Proof.
intros * Hp Hq.
destruct (lt_dec p q) as [Hpq| Hpq]; [ now apply subm_mat_swap_rows_lt_lt | ].
do 2 rewrite mat_swap_rows_comm with (p := p).
destruct (lt_dec q p) as [Hqp| Hqp]; [ now apply subm_mat_swap_rows_lt_lt | ].
replace q with p by flia Hpq Hqp.
now do 2 rewrite mat_swap_same_rows.
Qed.

Theorem mat_el_mat_swap_rows : ∀ (M : matrix T) p q j,
  1 ≤ q ≤ mat_nrows M
  → mat_el (mat_swap_rows p q M) q j = mat_el M p j.
Proof.
intros * Hql; cbn.
destruct M as (ll); cbn in Hql |-*.
f_equal; clear j.
rewrite (List_map_nth' 0); [ | rewrite List.length_seq; flia Hql ].
rewrite List.seq_nth; [ | flia Hql ].
rewrite Nat.add_0_l.
now rewrite transposition_2.
Qed.

Theorem length_fold_left_map_transp : ∀ A (ll : list A) sta len f g d,
  length
    (List.fold_left
       (λ ll' k,
        List.map (λ i, List.nth (transposition (f k) (g k) i) ll' d)
          (List.seq 0 (length ll')))
       (List.seq sta len) ll) = length ll.
Proof.
intros.
induction len; [ easy | ].
rewrite List.seq_S.
rewrite List.fold_left_app; cbn.
rewrite List_length_map_seq.
apply IHlen.
Qed.

Theorem mat_nrows_fold_left_swap : ∀ (M : matrix T) p q f g,
  mat_nrows
    (List.fold_left (λ M' k, mat_swap_rows (f k) (g k) M') (List.seq p q) M) =
  mat_nrows M.
Proof.
intros.
unfold mat_nrows.
rewrite fold_left_mat_fold_left_list_list.
apply length_fold_left_map_transp.
Qed.

Theorem nth_fold_left_map_transp_1 : ∀ A (la : list A) i sta len d,
  i < length la
  → i < sta ∨ sta + len < i
  → List.nth i
      (List.fold_left
         (λ la' k,
            List.map (λ j, List.nth (transposition k (k + 1) j) la' d)
              (List.seq 0 (length la')))
         (List.seq sta len) la) d =
    List.nth i la d.
Proof.
intros * Hi Hip.
induction len; [ easy | ].
rewrite List.seq_S; cbn.
rewrite List.fold_left_app; cbn.
rewrite (List_map_nth' 0). 2: {
  rewrite List.length_seq.
  now rewrite length_fold_left_map_transp.
}
rewrite List.seq_nth. 2: {
  now rewrite length_fold_left_map_transp.
}
rewrite Nat.add_0_l.
unfold transposition.
do 2 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec i (sta + len)) as [His| His]; [ flia His Hip | ].
destruct (Nat.eq_dec i (sta + len + 1)) as [Hip1| Hip1]; [ flia Hip Hip1 | ].
apply IHlen.
flia Hip His.
Qed.

Theorem nth_fold_left_seq_gen : ∀ A (u : list A) i d n sta,
  sta + n ≤ length u
  → sta ≤ i < sta + n - 1
  → List.nth i
      (List.fold_left
         (λ la' k,
            List.map (λ j, List.nth (transposition k (k + 1) j) la' d)
              (List.seq 0 (length la')))
         (List.seq sta n) u) d =
     List.nth (i + 1) u d.
Proof.
intros * Hn Hi.
revert i Hi.
induction n; intros; [ flia Hi  | ].
assert (H : sta + n ≤ length u) by flia Hn.
specialize (IHn H); clear H.
rewrite <- Nat.add_sub_assoc in Hi; [ | flia ].
rewrite Nat_sub_succ_1 in Hi.
rewrite List.seq_S.
rewrite List.fold_left_app.
destruct (Nat.eq_dec i (sta + n - 1)) as [Hin| Hin]. {
  subst i.
  rewrite Nat.sub_add; [ | flia Hi ].
  cbn.
  rewrite length_fold_left_map_transp.
  rewrite (List_map_nth' 0); [ | rewrite List.length_seq; flia Hn ].
  rewrite List.seq_nth; [ | flia Hn ].
  rewrite transposition_out; [ cbn | flia Hi | flia ].
  destruct n; [ flia Hi | ].
  rewrite <- Nat.add_sub_assoc; [ | flia ].
  rewrite Nat_sub_succ_1.
  rewrite List.seq_S; cbn.
  rewrite List.fold_left_app; cbn.
  rewrite length_fold_left_map_transp.
  rewrite (List_map_nth' 0); [ | rewrite List.length_seq; flia Hn ].
  rewrite List.seq_nth; [ | flia Hn ].
  rewrite transposition_1.
  rewrite Nat.add_1_r.
  rewrite nth_fold_left_map_transp_1; [ | flia Hn | right; flia ].
  now rewrite <- Nat.add_succ_comm.
}
cbn.
rewrite length_fold_left_map_transp.
rewrite (List_map_nth' 0); [ | rewrite List.length_seq; flia Hn Hi ].
rewrite List.seq_nth; [ | flia Hn Hi ].
rewrite transposition_out; [ cbn | flia Hi | flia Hi Hin ].
apply IHn.
flia Hi Hin.
Qed.

Theorem nth_fold_left_map_transp : ∀ A (la : list A) i sta len d,
  List.nth i
    (List.fold_left
       (λ la' k,
          List.map (λ j, List.nth (transposition k (k + 1) j) la' d)
            (List.seq 0 (length la')))
       (List.seq sta len) la) d =
  if le_dec (length la) i then d
  else if Nat.eq_dec i (sta + len) then List.nth sta la d
  else if le_dec (length la) sta then List.nth i la d
  else if le_dec (length la) (sta + len) then
    List.nth i
      (List.fold_left
         (λ la' k,
          List.map (λ j, List.nth (transposition k (k + 1) j) la' d)
            (List.seq 0 (length la)))
         (List.seq sta (length la - sta)) la) d
  else
    List.nth (i + Nat.b2n ((sta <=? i) && (i <=? sta + len))) la d.
Proof.
intros.
destruct (le_dec (length la) i) as [Hi| Hi]. {
  rewrite List.nth_overflow; [ easy | ].
  now rewrite length_fold_left_map_transp.
}
apply Nat.nle_gt in Hi.
destruct (Nat.eq_dec i (sta + len)) as [Hisl| Hisl]. {
  subst i.
  revert la sta d Hi.
  induction len; intros. {
    rewrite Nat.add_0_r in Hi |-*.
    now destruct la.
  }
  cbn.
  rewrite <- Nat.add_succ_comm in Hi.
  rewrite <- Nat.add_succ_comm.
  rewrite IHlen; [ | now rewrite List_length_map_seq ].
  rewrite (List_map_nth' 0); [ | rewrite List.length_seq; flia Hi ].
  rewrite List.seq_nth; [ | flia Hi ].
  rewrite Nat.add_0_l, Nat.add_1_r.
  now rewrite transposition_2.
}
unfold Nat.b2n, "&&", negb.
destruct (le_dec (length la) sta) as [Hsla| Hsla]. {
  rewrite List_fold_left_map_nth_len.
  erewrite List_fold_left_ext_in. 2: {
    intros j v Hj; apply List.in_seq in Hj.
    erewrite List.map_ext_in. 2: {
      intros k Hk; apply List.in_seq in Hk.
      rewrite transposition_out; [ | flia Hsla Hj Hk | flia Hsla Hj Hk ].
      easy.
    }
    easy.
  }
  specialize (List_seq_shift' sta 0 len) as H1; rewrite Nat.add_0_r in H1.
  rewrite <- H1. clear H1.
  rewrite List_fold_left_map.
  rewrite <- List_fold_left_map_nth_len.
  rewrite List_fold_left_nop_r.
  rewrite List.length_seq.
  rewrite List_repeat_apply_id. 2: {
    intros u.
    symmetry; apply List_map_nth_seq.
  }
  easy.
}
apply Nat.nle_gt in Hsla.
destruct (le_dec (length la) (sta + len)) as [Hsl| Hsl]. {
  replace len with (length la - sta + (sta + len - length la)) at 1
    by flia Hsla Hsl.
  rewrite List.seq_app.
  rewrite List.fold_left_app.
  rewrite Nat.add_comm, Nat.sub_add; [ | flia Hsla ].
  rewrite List_fold_left_map_nth_len.
  erewrite List_fold_left_ext_in. 2: {
    intros j v Hj; apply List.in_seq in Hj.
    erewrite List.map_ext_in. 2: {
      intros k Hk; apply List.in_seq in Hk.
      rewrite length_fold_left_map_transp in Hk.
      rewrite transposition_out; [ | flia Hsla Hj Hk | flia Hsla Hj Hk ].
      easy.
    }
    easy.
  }
  rewrite <- List_fold_left_map_nth_len.
  rewrite List_fold_left_nop_r.
  rewrite List.length_seq.
  rewrite List_repeat_apply_id. 2: {
    intros u.
    symmetry; apply List_map_nth_seq.
  }
  now rewrite <- List_fold_left_map_nth_len.
}
apply Nat.nle_gt in Hsl.
rewrite if_leb_le_dec.
destruct (le_dec sta i) as [Hip| Hip]. 2: {
  apply Nat.nle_gt in Hip.
  rewrite Nat.add_0_r.
  apply nth_fold_left_map_transp_1; [ easy | now left ].
}
rewrite if_leb_le_dec.
destruct (le_dec i (sta + len)) as [Hip'| Hip']. 2: {
  apply Nat.nle_gt in Hip'.
  rewrite Nat.add_0_r.
  apply nth_fold_left_map_transp_1; [ easy | now right ].
}
assert (H : i < sta + len) by flia Hisl Hip'.
clear Hisl Hip'; rename H into Hisl.
destruct (Nat.eq_dec i (length la - 1)) as [Hila| Hila]. {
  flia Hsl Hisl Hila.
}
destruct (Nat.eq_dec i (sta + len - 1)) as [Hisl1| Hisl1]. 2: {
  rewrite nth_fold_left_seq_gen; [ easy | flia Hsl | flia Hip Hisl Hisl1 ].
}
rewrite Hisl1.
rewrite Nat.sub_add; [ | flia Hisl ].
destruct len; [ flia Hip Hisl | ].
rewrite List.seq_S.
rewrite List.fold_left_app; cbn.
rewrite <- Nat.add_sub_assoc; [ | flia ].
rewrite Nat_sub_succ_1.
rewrite length_fold_left_map_transp.
rewrite (List_map_nth' 0); [ | rewrite List.length_seq; flia Hsl ].
rewrite List.seq_nth; [ | flia Hsl ].
rewrite transposition_1.
rewrite <- Nat.add_assoc, Nat.add_1_r.
apply nth_fold_left_map_transp_1; [ easy | right; flia ].
Qed.

Theorem nth_fold_left_map_transp' : ∀ A (la : list A) i len d,
  i + 1 < length la
  → i < len
  → List.nth i
      (List.fold_left
         (λ la' k,
            List.map (λ j, List.nth (transposition k (k + 1) j) la' d)
              (List.seq 0 (length la'))) 
         (List.seq 0 len) la) d =
    List.nth (i + 1) la d.
Proof.
intros * Hi Hpi.
rewrite nth_fold_left_map_transp; cbn.
rewrite Nat.sub_0_r.
destruct (le_dec (length la) i) as [H| H]; [ flia Hi H | clear H ].
destruct (Nat.eq_dec i len) as [H| H]; [ flia Hpi H | clear H ].
destruct (le_dec (length la) 0) as [H| H]; [ flia Hi H | clear H ].
destruct (le_dec (length la) len) as [Hll| Hll]. 2: {
  apply Nat.nle_gt in Hll.
  unfold Nat.b2n.
  rewrite if_leb_le_dec.
  destruct (le_dec i len) as [H| H]; [ easy | flia Hpi H ].
}
clear len Hpi Hll.
rewrite <- List_fold_left_map_nth_len.
rewrite nth_fold_left_seq_gen; [ easy | easy | flia Hi ].
Qed.

Theorem subm_mat_swap_rows_circ : ∀ (M : matrix T) p q,
  1 ≤ p ≤ mat_nrows M
  → subm 1 q (mat_swap_rows 1 p M) =
    subm p q
      (List.fold_left (λ M' k, mat_swap_rows (k + 1) (k + 2) M')
         (List.seq 0 (p - 2)) M).
Proof.
intros * Hp.
destruct M as (ll); cbn in Hp |-*.
unfold subm; f_equal.
cbn - [ List_butn ].
f_equal; clear q.
rewrite fold_left_mat_fold_left_list_list.
cbn - [ List_butn ].
rewrite List_map_nth_seq with (d := []); symmetry.
rewrite List_map_nth_seq with (d := []); symmetry.
rewrite List_length_butn, List.length_map, List.length_seq.
rewrite List_length_butn.
rewrite length_fold_left_map_transp.
unfold Nat.b2n.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec 0 (length ll)) as [H| H]; [ clear H | flia H Hp ].
destruct (lt_dec (p - 1) (length ll)) as [H| H]; [ clear H | flia H Hp ].
apply List.map_ext_in.
intros i Hi; apply List.in_seq in Hi.
cbn in Hi.
rewrite <- List_map_butn.
rewrite (List_map_nth' 0). 2: {
  rewrite List_length_butn, List.length_seq.
  unfold Nat.b2n.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec 0 (length ll)) as [H| H]; [ easy | flia Hp H ].
}
rewrite List_nth_butn_before; [ | flia ].
rewrite List.seq_nth; [ cbn | flia Hi ].
erewrite List_fold_left_ext_in. 2: {
  intros j ll' Hj.
  erewrite List.map_ext_in. 2: {
    intros k Hk.
    now rewrite Nat.add_sub, Nat.add_succ_r, Nat_sub_succ_1.
  }
  easy.
}
destruct (le_dec (p - 1) i) as [Hpi| Hpi]. 2: {
  apply Nat.nle_gt in Hpi.
  rewrite List_nth_butn_after; [ | easy ].
  rewrite nth_fold_left_map_transp; cbn.
  rewrite Nat.sub_0_r.
  destruct (le_dec (length ll) i) as [H| H]; [ flia Hi H | clear H ].
  destruct (Nat.eq_dec i (p - 2)) as [Hip1| Hip1]. {
    rewrite Hip1.
    replace (p - 2 + 1) with (p - 1) by flia Hpi.
    now rewrite transposition_2.
  }
  destruct (le_dec (length ll) 0) as [H| H]; [ flia Hp H | clear H ].
  destruct (le_dec (length ll) (p - 2)) as [H| H]; [ flia Hp H | clear H ].
  unfold transposition.
  unfold Nat.b2n.
  do 2 rewrite if_eqb_eq_dec.
  rewrite if_leb_le_dec.
  rewrite Nat.add_1_r.
  destruct (Nat.eq_dec (S i) 0) as [H| H]; [ easy | clear H ].
  destruct (Nat.eq_dec (S i) (p - 1)) as [H| H]; [ flia Hip1 H | clear H ].
  destruct (le_dec i (p - 2)) as [H| H]; [ | flia Hpi H ].
  now rewrite Nat.add_1_r.
}
rewrite transposition_out; [ | flia | flia Hpi ].
rewrite List_nth_butn_before; [ | easy ].
symmetry.
rewrite nth_fold_left_map_transp; cbn; rewrite Nat.sub_0_r.
destruct (le_dec (length ll) (i + 1)) as [H| H]; [ flia Hi H | clear H ].
destruct (Nat.eq_dec (i + 1) (p - 2)) as [H| H]; [ flia Hpi H | clear H ].
destruct (le_dec (length ll) 0) as [H| H]; [ flia Hp H | clear H ].
destruct (le_dec (length ll) (p - 2)) as [H| H]; [ flia Hp H | clear H ].
unfold Nat.b2n.
rewrite if_leb_le_dec.
destruct (le_dec (i + 1) (p - 2)) as [H| H]; [ flia Hpi H | clear H ].
now rewrite Nat.add_0_r.
Qed.

Theorem subm_fold_left_lt : ∀ (M : matrix T) i j m,
  m < i - 1
  → subm i j
      (List.fold_left (λ M' k, mat_swap_rows (k + 1) (k + 2) M')
         (List.seq 0 m) M) =
    List.fold_left
      (λ M' k, mat_swap_rows (k + 1) (k + 2) M')
      (List.seq 0 m) (subm i j M).
Proof.
intros * Hmi.
revert i Hmi.
induction m; intros; [ easy | ].
rewrite List.seq_S; cbn.
do 2 rewrite List.fold_left_app; cbn.
rewrite <- IHm; [ | flia Hmi ].
apply subm_mat_swap_rows_lt; flia Hmi.
Qed.

Theorem determinant_circular_shift_rows :
  rngl_has_1 T = true →
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  ∀ (M : matrix T) i,
  i < mat_nrows M
  → is_square_matrix M = true
  → det
      (List.fold_left (λ M' k, mat_swap_rows (k + 1) (k + 2) M')
         (List.seq 0 i) M) =
    (minus_one_pow i * det M)%L.
Proof.
intros Hon Hic Hop * Hin Hsm.
remember (mat_nrows M) as n eqn:Hr; symmetry in Hr.
revert M Hsm Hr.
induction i; intros; [ now cbn; rewrite (rngl_mul_1_l Hon) | ].
assert (H : i < n) by flia Hin.
specialize (IHi H); clear H.
rewrite List.seq_S; cbn.
rewrite List.fold_left_app; cbn - [ det ].
rewrite determinant_alternating; [ | easy | easy | easy | flia | | | ];
cycle 1. {
  rewrite mat_nrows_fold_left_swap, Hr; flia Hin.
} {
  rewrite mat_nrows_fold_left_swap, Hr; flia Hin.
} {
  specialize (squ_mat_ncols _ Hsm) as Hc1.
  apply is_scm_mat_iff.
  apply is_scm_mat_iff in Hsm.
  destruct Hsm as (Hcr & Hc).
  rewrite Hr in Hc1.
  rewrite mat_nrows_fold_left_swap.
  split. {
    intros Hc'.
    unfold mat_ncols in Hc'.
    rewrite fold_left_mat_fold_left_list_list in Hc'.
    cbn in Hc'.
    erewrite List_fold_left_ext_in in Hc'. 2: {
      intros j ll' Hj.
      erewrite List.map_ext_in. 2: {
        intros k Hk.
        now rewrite Nat.add_sub, Nat.add_succ_r, Nat_sub_succ_1.
      }
      easy.
    }
    apply List.length_zero_iff_nil in Hc'.
    rewrite List_hd_nth_0 in Hc'.
    rewrite nth_fold_left_map_transp in Hc'.
    rewrite fold_mat_nrows in Hc'.
    do 2 rewrite Nat.add_0_l in Hc'.
    destruct (le_dec (mat_nrows M) 0) as [Hlz| Hlz]. {
      now apply Nat.le_0_r in Hlz.
    }
    apply Nat.nle_gt in Hlz.
    destruct (Nat.eq_dec 0 i) as [Hiz| Hiz]. {
      subst i.
      apply Hcr.
      unfold mat_ncols.
      rewrite List_hd_nth_0.
      now rewrite Hc'.
    }
    rewrite Nat.sub_0_r in Hc'.
    destruct (le_dec (mat_nrows M) i) as [Hri| Hri]. {
      unfold mat_nrows in Hc'.
      rewrite <- List_fold_left_map_nth_len in Hc'.
      rewrite nth_fold_left_map_transp' in Hc'; cycle 1. {
        rewrite fold_mat_nrows.
        flia Hin Hr.
      } {
        now rewrite fold_mat_nrows.
      }
      cbn in Hc'.
      apply (f_equal (λ l, length l)) in Hc'.
      rewrite Hc in Hc'. 2: {
        apply List.nth_In.
        rewrite fold_mat_nrows.
        flia Hr Hin.
      }
      easy.
    }
    apply Nat.nle_gt in Hri.
    cbn in Hc'.
    apply (f_equal (λ l, length l)) in Hc'.
    rewrite Hc in Hc'. 2: {
      apply List.nth_In.
      rewrite fold_mat_nrows.
      flia Hr Hin.
    }
    easy.
  }
  intros la Hla.
  rewrite fold_left_mat_fold_left_list_list in Hla.
  cbn in Hla.
  apply List.In_nth with (d := []) in Hla.
  rewrite length_fold_left_map_transp, fold_mat_nrows in Hla.
  destruct Hla as (j & Hj & Hla).
  erewrite List_fold_left_ext_in in Hla. 2: {
    intros k ll' Hk.
    erewrite List.map_ext_in. 2: {
      intros l Hl.
      now rewrite Nat.add_sub, Nat.add_succ_r, Nat_sub_succ_1.
    }
    easy.
  }
  rewrite nth_fold_left_map_transp in Hla.
  rewrite fold_mat_nrows in Hla.
  rewrite Nat.add_0_l in Hla.
  destruct (le_dec (mat_nrows M) j) as [H| H]; [ flia Hj H | clear H ].
  destruct (Nat.eq_dec j i) as [Hji| Hji]. {
    subst la.
    apply Hc, List.nth_In.
    rewrite fold_mat_nrows; flia Hj.
  }
  destruct (le_dec (mat_nrows M) 0) as [H| H]; [ flia Hj H | clear H ].
  destruct (le_dec (mat_nrows M) i) as [H| H]; [ flia Hin Hr H | clear H ].
  subst la.
  unfold Nat.b2n.
  rewrite Bool.andb_if.
  do 2 rewrite if_leb_le_dec.
  destruct (le_dec 0 j) as [Hjz| Hjz]. {
    destruct (le_dec j i) as [Hji'| Hji']. {
      apply Hc, List.nth_In.
      rewrite fold_mat_nrows.
      rewrite Hr in Hj |-*.
      flia Hji' Hin.
    }
    apply Nat.nle_gt in Hji'.
    rewrite Nat.add_0_r.
    apply Hc, List.nth_In.
    now rewrite fold_mat_nrows.
  }
  now apply Nat.nle_gt in Hjz.
}
rewrite IHi; [ | easy | easy ].
rewrite minus_one_pow_succ; [ | easy ].
now symmetry; apply rngl_mul_opp_l.
Qed.

Theorem determinant_subm_mat_swap_rows_0_i :
  rngl_has_1 T = true →
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  ∀ (M : matrix T) i j,
  is_square_matrix M = true
  → 1 < i ≤ mat_nrows M
  → 1 ≤ j ≤ mat_nrows M
  → det (subm 1 j (mat_swap_rows 1 i M)) =
    (minus_one_pow i * det (subm i j M))%L.
Proof.
intros Hon Hic Hop * Hsm (Hiz, Hin) Hjn.
rewrite subm_mat_swap_rows_circ. 2: {
  split; [ flia Hiz | easy ].
}
destruct i; [ flia Hiz | ].
rewrite (minus_one_pow_succ Hop).
replace (S i - 2) with (i - 1) by flia.
rewrite subm_fold_left_lt; [ | flia Hiz ].
rewrite (determinant_circular_shift_rows Hon); [ | easy | easy | | ]. {
  destruct i; [ flia Hiz | ].
  rewrite Nat_sub_succ_1.
  rewrite minus_one_pow_succ; [ | easy ].
  now rewrite rngl_opp_involutive.
} {
  rewrite mat_nrows_subm.
  generalize Hin; intros H.
  apply Nat.leb_le in H; rewrite H; clear H; cbn.
  flia Hin Hiz.
}
apply is_squ_mat_subm; [ flia Hin | flia Hjn | easy ].
Qed.

(* Laplace formulas *)

Theorem laplace_formula_on_rows :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  ∀ (M : matrix T) i,
  is_square_matrix M = true
  → 1 ≤ i ≤ mat_nrows M
  → det M = ∑ (j = 1, mat_ncols M), mat_el M i j * mat_el (com M) i j.
Proof.
intros Hon Hop Hic * Hsm Hlin.
specialize (squ_mat_ncols M Hsm) as Hc.
rewrite Hc.
specialize (proj1 (is_scm_mat_iff _ M) Hsm) as H1.
destruct H1 as (Hcr & Hc').
destruct (Nat.eq_dec (mat_nrows M) 0) as [Hnz| Hnz]. {
  rewrite Hnz in Hlin; flia Hlin.
}
destruct (Nat.eq_dec i 1) as [Hi1| Hi1]. {
  subst i; cbn.
  symmetry.
  unfold det.
  replace (mat_nrows M) with (S (mat_nrows M - 1)) by flia Hnz.
  cbn - [ List_butn ].
  apply rngl_summation_eq_compat.
  intros j Hj.
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_mul_swap; [ | easy ].
  rewrite (List_map_nth' 0); [ | rewrite List.length_seq, Hc; flia Hj Hnz ].
  rewrite List.seq_nth; [ | rewrite Hc; flia Hj Hnz ].
  rewrite List.length_map.
  cbn - [ List_butn ].
  rewrite <- Nat.sub_succ_l; [ | easy ].
  rewrite Nat_sub_succ_1.
  f_equal; f_equal.
  rewrite List_length_butn, fold_mat_nrows.
  apply Nat.neq_0_lt_0, Nat.ltb_lt in Hnz.
  now rewrite Hnz.
}
unfold det.
replace (mat_nrows M) with (S (mat_nrows M - 1)) by flia Hnz.
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1.
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  cbn.
  rewrite (List_map_nth' 0); [ | rewrite List.length_seq; flia Hlin ].
  rewrite (List_map_nth' 0); [ | rewrite List.length_seq, Hc; flia Hj Hnz ].
  rewrite List.seq_nth; [ | flia Hlin ].
  rewrite List.seq_nth; [ | flia Hj Hc Hnz ].
  rewrite (Nat.add_comm 1), Nat.sub_add; [ | flia Hlin ].
  rewrite (Nat.add_comm 1), Nat.sub_add; [ | easy ].
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_mul_swap; [ | easy ].
  easy.
}
cbn.
rename i into p.
remember (mat_swap_rows 1 p M) as M'.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite List.length_map, List_length_butn, fold_mat_nrows.
  rewrite rngl_mul_mul_swap; [ | easy ].
  rewrite Nat.add_comm.
  rewrite (minus_one_pow_add Hon Hop).
  do 2 rewrite <- rngl_mul_assoc.
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_assoc.
  specialize (determinant_subm_mat_swap_rows_0_i Hon Hic Hop) as H1.
  specialize (H1 M p j Hsm).
  cbn - [ List_butn ] in H1.
  rewrite List.length_map, List_map_butn, List_length_butn in H1.
  rewrite list_swap_elem_length, fold_mat_nrows in H1.
  rewrite List_length_butn, List.length_map, fold_mat_nrows in H1.
  apply Nat.neq_0_lt_0, Nat.ltb_lt in Hnz.
  rewrite Hnz in H1; cbn - [ "<?" ] in H1.
  apply Nat.ltb_lt in Hnz.
  rewrite <- H1; [ | flia Hi1 Hlin | flia Hj Hnz ].
  clear H1.
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_assoc, rngl_mul_mul_swap; [ | easy ].
  replace (mat_el M p j) with (mat_el (mat_swap_rows 1 p M) 0 j). 2: {
    unfold mat_swap_rows.
    cbn; unfold list_swap_elem.
    rewrite fold_mat_nrows.
    rewrite (List_map_nth' 0); [ | now rewrite List.length_seq ].
    rewrite List.seq_nth; [ | easy ].
    rewrite Nat.add_0_r, transposition_1.
    easy.
  }
  rewrite <- HeqM'.
  easy.
}
cbn.
subst M'.
rewrite <- rngl_opp_involutive; [ | easy ].
rewrite fold_det.
assert (H1 : 1 ≠ p) by flia Hlin Hi1.
assert (H2 : p - 1 < mat_nrows M) by flia Hlin.
apply Nat.neq_0_lt_0 in Hnz.
rewrite <- (determinant_alternating Hon Hic Hop M H1);
  [ | easy | easy | easy ].
unfold det.
rewrite mat_swap_rows_nrows.
remember (determinant_loop (mat_nrows M)) as x eqn:Hx.
replace (mat_nrows M) with (S (mat_nrows M - 1)) in Hx by flia Hlin.
subst x.
rewrite determinant_succ.
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1.
rewrite rngl_opp_summation; [ | easy ].
apply rngl_summation_eq_compat.
intros i Hi.
rewrite <- rngl_mul_opp_l; [ | easy ].
rewrite <- rngl_mul_opp_l; [ | easy ].
rewrite minus_one_pow_succ; [ | easy ].
rewrite rngl_opp_involutive; [ | easy ].
easy.
Qed.

Theorem map_permut_seq_permut_seq_with_len : ∀ n σ,
  permut_seq_with_len n σ
  → permut_seq_with_len n (List.map (λ i, List.nth i σ 0) (List.seq 0 n)).
Proof.
intros * Hσ.
split; [ | now rewrite List_length_map_seq ].
apply permut_seq_iff.
split. {
  intros i Hi.
  apply List.in_map_iff in Hi.
  destruct Hi as (j & Hji & Hj).
  apply List.in_seq in Hj.
  rewrite List_length_map_seq.
  rewrite <- Hji.
  destruct Hσ as (H1, H2).
  rewrite <- H2 in Hj |-*.
  apply permut_seq_ub; [ easy | now apply List.nth_In ].
} {
  apply (NoDup_map_iff 0).
  rewrite List.length_seq.
  intros i j Hi Hj Hij.
  rewrite List.seq_nth in Hij; [ | easy ].
  rewrite List.seq_nth in Hij; [ | easy ].
  do 2 rewrite Nat.add_0_l in Hij.
  destruct Hσ as (Hσa, Hσl).
  apply permut_seq_iff in Hσa.
  destruct Hσa as (Hσa, Hσn).
  apply (NoDup_nat _ Hσn); [ congruence | congruence | easy ].
}
Qed.

(* https://proofwiki.org/wiki/Permutation_of_Determinant_Indices *)

Theorem comatrix_nrows : ∀ M, mat_nrows (com M) = mat_nrows M.
Proof.
intros.
unfold com; cbn.
now rewrite List_length_map_seq.
Qed.

Theorem comatrix_ncols : ∀ M, mat_ncols (com M) = mat_ncols M.
Proof.
intros.
unfold com.
unfold mat_ncols; cbn.
destruct (Nat.eq_dec (mat_nrows M) 0) as [Hrz| Hrz]. {
  rewrite Hrz; cbn.
  unfold mat_nrows in Hrz.
  now apply List.length_zero_iff_nil in Hrz; rewrite Hrz.
}
apply Nat.neq_0_lt_0 in Hrz.
rewrite (List_map_hd 0); [ | now rewrite List.length_seq ].
now rewrite List_length_map_seq.
Qed.

Theorem comatrix_is_square : ∀ M,
  is_square_matrix M = true
  → is_square_matrix (com M) = true.
Proof.
intros * Hsm.
specialize (squ_mat_ncols _ Hsm) as Hc.
apply is_scm_mat_iff in Hsm.
apply is_scm_mat_iff.
rewrite comatrix_ncols.
rewrite comatrix_nrows.
split; [ easy | ].
intros l Hl.
apply List.in_map_iff in Hl.
destruct Hl as (i & Hil & Hi).
now rewrite <- Hil; rewrite List_length_map_seq.
Qed.

Theorem comatrix_is_correct : ∀ M,
  is_correct_matrix M = true
  → is_correct_matrix (com M) = true.
Proof.
intros * Hsm.
apply is_scm_mat_iff in Hsm.
apply is_scm_mat_iff.
rewrite comatrix_ncols.
rewrite comatrix_nrows.
split; [ easy | ].
intros l Hl.
apply List.in_map_iff in Hl.
destruct Hl as (i & Hil & Hi).
now rewrite <- Hil; rewrite List_length_map_seq.
Qed.

Theorem comatrix_transpose :
  rngl_has_1 T = true →
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  ∀ M,
  is_square_matrix M = true
  → com M⁺ = (com M)⁺%M.
Proof.
intros Hon Hic Hop H10 * Hsm.
destruct (Nat.eq_dec (mat_ncols M) 0) as [Hcz| Hcz]. {
  unfold mat_transp, com; cbn - [ det ].
  rewrite Hcz; cbn.
  unfold mat_ncols; cbn.
  destruct (Nat.eq_dec (mat_nrows M) 0) as [Hrz| Hrz]; [ now rewrite Hrz | ].
  now replace (mat_nrows M) with (S (mat_nrows M - 1)) by flia Hrz.
}
destruct (Nat.eq_dec (mat_nrows M) 0) as [Hrz| Hrz]. {
  unfold mat_ncols in Hcz.
  unfold mat_nrows in Hrz.
  apply List.length_zero_iff_nil in Hrz.
  now rewrite Hrz in Hcz.
}
apply Nat.neq_0_lt_0 in Hcz, Hrz.
unfold mat_transp, com, mat_ncols; cbn - [ det ].
f_equal.
rewrite (List_map_hd 0); [ | now rewrite List.length_seq ].
rewrite (List_map_hd 0); [ | now rewrite List.length_seq ].
do 4 rewrite List.length_map.
do 2 rewrite List.length_seq.
rewrite fold_mat_ncols.
apply List.map_ext_in.
intros i Hi; apply List.in_seq in Hi.
assert (H : 1 ≤ i ≤ mat_ncols M) by flia Hi.
clear Hi; rename H into Hi.
apply List.map_ext_in.
intros j Hj; apply List.in_seq in Hj.
assert (H : 1 ≤ j ≤ mat_nrows M) by flia Hj.
clear Hj; rename H into Hj.
assert (Hi' : i - 1 < mat_ncols M) by flia Hi.
assert (Hj' : j - 1 < mat_nrows M) by flia Hj.
move j before i.
rewrite (List_map_nth' 0); [ | now rewrite List.length_seq ].
rewrite (List_map_nth' 0); [ | now rewrite List.length_seq ].
rewrite List.seq_nth; [ | easy ].
rewrite List.seq_nth; [ | easy ].
rewrite (Nat.add_comm 1 (j - 1)), Nat.sub_add; [ | easy ].
rewrite (Nat.add_comm 1 (i - 1)), Nat.sub_add; [ | easy ].
rewrite Nat.add_comm; f_equal; symmetry.
specialize (@fold_mat_transp T ro M) as H1.
now apply (det_subm_transp Hon Hic Hop H10).
Qed.

Theorem laplace_formula_on_cols :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_characteristic T ≠ 1 →
  ∀ (M : matrix T) j,
  is_square_matrix M = true
  → 1 ≤ j ≤ mat_ncols M
  → det M = ∑ (i = 1, mat_nrows M), mat_el M i j * mat_el (com M) i j.
Proof.
intros Hon Hop Hic H10 * Hsm Hj.
rewrite <- (determinant_transpose Hon Hic Hop H10); [ | easy ].
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite <- mat_transp_el; [ | | flia Hj | flia Hi ]. 2: {
    now apply squ_mat_is_corr.
  }
  easy.
}
cbn - [ det mat_el ].
specialize (@laplace_formula_on_rows Hon Hop Hic (M⁺)%M j) as H1.
assert (H : is_square_matrix M⁺ = true) by now apply mat_transp_is_square.
specialize (H1 H); clear H.
rewrite mat_transp_nrows in H1.
rewrite mat_transp_ncols in H1.
rewrite if_eqb_eq_dec in H1.
destruct (Nat.eq_dec (mat_ncols M) 0) as [Hcz| Hcz]. {
  rewrite Hcz in Hj; flia Hj.
}
specialize (H1 Hj).
rewrite H1.
apply rngl_summation_eq_compat.
intros i Hi.
f_equal.
symmetry.
rewrite (comatrix_transpose Hon Hic Hop H10); [ | easy ].
symmetry.
apply mat_transp_el; [ | flia Hj | flia Hi ].
apply comatrix_is_correct.
now apply squ_mat_is_corr.
Qed.

(*
The following two theorems, "determinant_with_row" and
determinant_with_bad_row have some similitudes.
  The theorem "determinant_with_row" says that we can compute the determinant
by going through any row (not necessarily the 0th one). Here, row "i".
  The theorem "determinant_with_bad_row" says that if we go through another
row "k" different from "i", the same formula (where "M i j" is replaced
with "M k j") returns 0. It is what I call a "bad determinant formula".

determinant_with_row
  ∀ (i n : nat) (M : matrix (S n) (S n) T),
  i ≤ n
  → ∑ (j = 1, n), minus_one_pow (i + j) * M i j * det (subm M i j) = det M

determinant_with_bad_row
  ∀ (i k n : nat) (M : matrix (S n) (S n) T),
  i ≤ n → k ≤ n → i ≠ k
  → ∑ (j = 1, n), minus_one_pow (i + j) * M k j * det (subm M i j) = 0%L
*)

Theorem determinant_with_row :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  ∀ i (M : matrix T),
  is_square_matrix M = true
  → 1 ≤ i ≤ mat_nrows M
  → det M =
    ∑ (j = 1, mat_nrows M),
    minus_one_pow (i + j) * mat_el M i j * det (subm i j M).
Proof.
intros Hon Hop Hic * Hsm Hir.
destruct (Nat.eq_dec i 1) as [Hi1| Hi1]. {
  subst i; cbn - [ det ].
  unfold det.
  erewrite rngl_summation_eq_compat. 2: {
    intros i Hi.
    rewrite mat_nrows_subm.
    easy.
  }
  cbn.
  replace (mat_nrows M) with (S (mat_nrows M - 1)) by flia Hir.
  rewrite determinant_succ.
  now cbn; rewrite Nat.sub_0_r.
}
apply rngl_opp_inj; [ easy | ].
rewrite <- (determinant_alternating Hon Hic Hop M Hi1);
  [ | easy | flia Hir | easy ].
unfold det at 1.
rewrite mat_swap_rows_nrows.
replace (mat_nrows M) with (S (mat_nrows M - 1)) at 1 by flia Hir.
rewrite determinant_succ.
rewrite <- Nat.sub_succ_l; [ | flia Hir ].
rewrite Nat_sub_succ_1.
rewrite rngl_opp_summation; [ | easy ].
apply rngl_summation_eq_compat.
intros j Hj.
rewrite <- rngl_mul_assoc; symmetry.
rewrite <- rngl_mul_opp_r; [ | easy ].
rewrite (Nat.add_comm i j).
rewrite (minus_one_pow_add Hon); [ | easy ].
rewrite rngl_mul_opp_r; [ | easy ].
rewrite <- rngl_mul_opp_l; [ | easy ].
rewrite <- rngl_mul_opp_l; [ | easy ].
rewrite <- rngl_mul_opp_l; [ | easy ].
do 2 rewrite <- rngl_mul_assoc.
rewrite minus_one_pow_succ; [ | easy ].
f_equal.
rewrite (minus_one_pow_mul_comm Hon Hop).
rewrite <- rngl_mul_assoc.
rewrite mat_el_mat_swap_rows; [ | flia Hj ].
f_equal.
rewrite <- (minus_one_pow_mul_comm Hon Hop).
symmetry.
rewrite mat_swap_rows_comm.
rewrite <- determinant_subm_mat_swap_rows_0_i; try easy; [ | flia Hir Hi1 ].
unfold det.
rewrite mat_nrows_subm.
rewrite mat_swap_rows_nrows.
assert (H : 1 ≤ mat_nrows M) by flia Hir.
now apply Nat.leb_le in H; rewrite H.
Qed.

Theorem determinant_with_bad_row :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_characteristic _ = 0 →
  (rngl_is_integral_domain T || rngl_has_inv_or_quot T)%bool = true →
  ∀ i k (M : matrix T),
  is_square_matrix M = true
  → 1 ≤ i ≤ mat_nrows M
  → 1 ≤ k ≤ mat_nrows M
  → i ≠ k
  → ∑ (j = 1, mat_nrows M),
    minus_one_pow (i + j) * mat_el M k j * det (subm i j M) = 0%L.
Proof.
intros Hon Hop Hic Hch Hii * Hsm Hir Hkr Hik.
specialize (squ_mat_ncols _ Hsm) as Hc.
remember
  (mk_mat
     (List.map
        (λ p,
         List.map (λ q, mat_el M (if p =? i then k else p) q)
           (List.seq 1 (mat_ncols M)))
        (List.seq 1 (mat_nrows M))))
  as A eqn:HA.
assert (Hasm : is_square_matrix A = true). {
  subst A.
  apply is_scm_mat_iff; cbn.
  unfold mat_ncols; cbn.
  rewrite List_length_map_seq.
  rewrite (List_map_hd 0); [ | rewrite List.length_seq; flia Hir ].
  rewrite List_length_map_seq.
  rewrite fold_mat_ncols.
  apply is_scm_mat_iff in Hsm.
  split; [ easy | ].
  intros l Hl.
  apply List.in_map_iff in Hl.
  destruct Hl as (j & Hjl & Hj).
  apply List.in_seq in Hj.
  now rewrite <- Hjl, List_length_map_seq.
}
assert (Hira : mat_nrows A = mat_nrows M). {
  now subst A; cbn; rewrite List_length_map_seq.
}
assert (H1 : det A = 0%L). {
  apply (determinant_same_rows Hon Hic Hop Hch Hii) with (p := i) (q := k). {
    easy.
  } {
    easy.
  } {
    now rewrite Hira.
  } {
    now rewrite Hira.
  }
  intros j; subst A; cbn.
  rewrite (List_map_nth' 0); [ | rewrite List.length_seq; flia Hir ].
  symmetry.
  rewrite (List_map_nth' 0); [ | rewrite List.length_seq; flia Hkr ].
  f_equal.
  apply List.map_ext_in.
  intros u Hu; apply List.in_seq in Hu.
  rewrite List.seq_nth; [ | flia Hkr ].
  rewrite List.seq_nth; [ | flia Hir ].
  rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
  rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
  cbn; rewrite Nat.eqb_refl.
  apply Nat.neq_sym, Nat.eqb_neq in Hik.
  now rewrite Hik.
}
rewrite (determinant_with_row Hon Hop Hic) with (i := i) in H1;
  [ | easy | ]. 2: {
  now rewrite Hira.
}
rewrite <- H1 at 2.
rewrite Hira.
apply rngl_summation_eq_compat.
intros j Hj.
do 2 rewrite <- rngl_mul_assoc.
f_equal; f_equal. {
  rewrite HA; cbn.
  rewrite (List_map_nth' 0); [ | rewrite List.length_seq; flia Hir ].
  rewrite (List_map_nth' 0); [ | rewrite List.length_seq, Hc; flia Hj Hir ].
  rewrite List.seq_nth; [ | flia Hir ].
  rewrite List.seq_nth; [ | rewrite Hc; flia Hj Hir ].
  rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
  rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
  now rewrite Nat.eqb_refl.
}
(* lemma? *)
unfold subm; cbn.
do 2 rewrite List.length_map.
do 2 rewrite List_length_butn.
do 2 rewrite fold_mat_nrows.
rewrite Hira.
f_equal; f_equal; f_equal.
rewrite HA; cbn.
destruct M as (ll); cbn in Hir, Hj |-*.
unfold mat_ncols; cbn.
remember (List.seq 1 (length (List.hd [] ll))) as x eqn:Hx.
rewrite (List_seq_cut3 i); [ subst x | apply List.in_seq; flia Hir ].
rewrite Nat.sub_succ.
do 2 rewrite List.map_app; cbn.
rewrite Nat.eqb_refl.
erewrite List.map_ext_in. 2: {
  intros u Hu; apply List.in_seq in Hu.
  replace (u =? i) with false. 2: {
    symmetry; apply Nat.eqb_neq; flia Hu.
  }
  easy.
}
erewrite List.map_ext_in with (l := List.seq (S i) _). 2: {
  intros u Hu; apply List.in_seq in Hu.
  replace (u =? i) with false. 2: {
    symmetry; apply Nat.eqb_neq; flia Hu.
  }
  easy.
}
rewrite List_map_nth_seq with (la := ll) (d := []) at 1.
rewrite List_seq_cut3 with (i := i - 1); [ | apply List.in_seq; flia Hir ].
rewrite <- Nat.sub_succ_l; [ | easy ].
rewrite Nat_sub_succ_1, Nat.add_0_l, Nat.sub_0_r.
do 2 rewrite List.map_app.
do 3 rewrite List_butn_app.
do 2 rewrite List_length_map_seq.
rewrite Nat.ltb_irrefl.
rewrite Nat.sub_diag.
rewrite List.length_map.
replace (0 <? length [i - 1]) with true by easy.
rewrite <- List_map_butn.
rewrite List.app_nil_l.
remember (List_butn 0 _) as x; cbn in Heqx; subst x.
f_equal. {
  rewrite <- (List.seq_shift (i - 1)), List.map_map.
  apply List.map_ext_in.
  intros u Hu; apply List.in_seq in Hu.
  rewrite Nat_sub_succ_1.
  rewrite List_map_nth_seq with (d := 0%L) (la := List.nth u ll []).
  apply is_scm_mat_iff in Hsm.
  destruct Hsm as (Hcr, Hcl).
  cbn in Hcl.
  rewrite List_hd_nth_0.
  rewrite Hcl; [ | apply List.nth_In; flia Hu Hir ].
  rewrite Hcl; [ | apply List.nth_In; flia Hu Hir ].
  rewrite <- (List.seq_shift (length ll) 0), List.map_map.
  apply List.map_ext_in.
  intros v Hv; apply List.in_seq in Hv.
  rewrite Nat_sub_succ_1.
  rewrite List_map_nth_seq with (la := List.nth u ll []) (d := 0%L) at 1.
  f_equal; f_equal; f_equal.
  apply Hcl, List.nth_In; flia Hu Hir.
} {
  rewrite <- (List.seq_shift _ i), List.map_map.
  apply List.map_ext_in.
  intros u Hu; apply List.in_seq in Hu.
  rewrite Nat_sub_succ_1.
  rewrite List_map_nth_seq with (d := 0%L) (la := List.nth u ll []).
  apply is_scm_mat_iff in Hsm.
  destruct Hsm as (Hcr, Hcl).
  cbn in Hcl.
  rewrite List_hd_nth_0.
  rewrite Hcl; [ | apply List.nth_In; flia Hu ].
  rewrite Hcl; [ | apply List.nth_In; flia Hu ].
  rewrite <- (List.seq_shift _ 0), List.map_map.
  apply List.map_ext_in.
  intros v Hv; apply List.in_seq in Hv.
  rewrite Nat_sub_succ_1.
  rewrite List_map_nth_seq with (la := List.nth u ll []) (d := 0%L) at 1.
  f_equal; f_equal; f_equal.
  apply Hcl, List.nth_In; flia Hu.
}
Qed.

Theorem matrix_comatrix_transp_mul :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_characteristic T = 0 →
  (rngl_is_integral_domain T || rngl_has_inv_or_quot T)%bool = true →
  ∀ (M : matrix T),
  is_square_matrix M = true
  → (M * (com M)⁺ = det M × mI (mat_nrows M))%M.
Proof.
intros Hon Hop Hic Hch Hii * Hsm.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
destruct M as (ll); cbn - [ det ].
unfold "*"%M, "×"%M, mat_nrows; cbn - [ det ]; f_equal.
rewrite List.map_map.
rewrite <- (List.seq_shift (length ll)).
rewrite List.map_map.
apply List.map_ext_in.
intros i Hi; apply List.in_seq in Hi.
assert (Hll : 0 < length ll) by flia Hi.
rewrite laplace_formula_on_rows with (i := S i); try easy. 2: {
  cbn; flia Hi.
}
cbn - [ mat_el ].
rewrite mat_transp_ncols.
rewrite comatrix_nrows, comatrix_ncols.
unfold mat_ncols.
cbn - [ mat_el mat_nrows com ].
apply is_scm_mat_iff in Hsm.
destruct Hsm as (Hcr, Hcl).
cbn in Hcl.
rewrite Hcl; [ | now apply List_hd_in ].
apply Nat.neq_0_lt_0 in Hll.
apply Nat.eqb_neq in Hll; rewrite Hll.
apply Nat.eqb_neq in Hll.
apply Nat.neq_0_lt_0 in Hll.
rewrite List.map_map.
rewrite <- List.seq_shift, List.map_map.
apply List.map_ext_in.
intros j Hj; apply List.in_seq in Hj.
move j before i.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  assert (Hkc : k - 1 < mat_ncols {| mat_list_list := ll |}). {
    unfold mat_ncols; cbn.
    rewrite Hcl; [ flia Hk Hll | ].
    now apply List_hd_in.
  }
  cbn - [ det ].
  rewrite Nat.sub_0_r.
  rewrite (List_map_nth' 0); [ | now rewrite List.length_seq ].
  rewrite (List_map_nth' 0); [ | now rewrite List.length_seq ].
  rewrite List.seq_nth; [ | easy ].
  rewrite List.seq_nth; [ | easy ].
  rewrite (Nat.add_comm 1 (k - 1)).
  rewrite Nat.sub_add; [ | easy ].
  rewrite rngl_mul_assoc.
  easy.
}
cbn - [ det ].
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  (* diagonal *)
  subst j; rewrite δ_diag, (rngl_mul_1_r Hon).
  unfold mat_mul_el.
  unfold mat_ncols.
  rewrite Hcl; [ | now apply List_hd_in ].
  apply rngl_summation_eq_compat.
  intros k Hk.
  unfold mat_el.
  rewrite Nat_sub_succ_1.
  rewrite <- rngl_mul_assoc; f_equal.
  cbn - [ det ].
  rewrite List_length_map_seq.
  rewrite (List_map_nth' 0). 2: {
    rewrite List.length_seq.
    unfold mat_ncols; cbn.
    rewrite (List_map_hd 0); [ | now rewrite List.length_seq ].
    rewrite List_length_map_seq.
    unfold mat_ncols.
    rewrite Hcl; [ flia Hk Hll | ].
    now apply List_hd_in.
  }
  rewrite (List_map_nth' 0); [ | now rewrite List.length_seq ].
  rewrite List.seq_nth. 2: {
    rewrite comatrix_ncols.
    unfold mat_ncols; cbn.
    rewrite Hcl; [ flia Hk Hll | ].
    now apply List_hd_in.
  }
  rewrite (List_map_nth' 0). 2: {
    rewrite List.length_seq, List.seq_nth; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  rewrite Nat.add_comm, Nat.add_sub.
  rewrite (List_map_nth' 0). 2: {
    unfold mat_ncols.
    rewrite List.length_seq; cbn.
    rewrite Hcl; [ flia Hk Hll | ].
    now apply List_hd_in.
  }
  rewrite List.seq_nth. 2: {
    rewrite List.seq_nth; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  rewrite List.seq_nth; [ | easy ].
  rewrite List.seq_nth. 2: {
    unfold mat_ncols; rewrite Hcl; [ flia Hk Hll | ].
    now apply List_hd_in.
  }
  rewrite (Nat.add_comm 1 i), Nat.add_sub.
  now rewrite (Nat.add_comm 1 (k - 1)), Nat.sub_add.
} {
  (* not on diagonal: zeroes *)
  rewrite δ_ndiag; [ | easy ].
  rewrite rngl_mul_0_r; [ | easy ].
  unfold mat_transp.
  unfold mat_mul_el.
  cbn - [ com ].
  erewrite rngl_summation_eq_compat. 2: {
    intros k Hk.
    unfold mat_ncols in Hk; cbn in Hk.
    rewrite Hcl in Hk; [ | now apply List_hd_in ].
    rewrite (List_map_nth' 0). 2: {
      rewrite List.length_seq, comatrix_ncols.
      unfold mat_ncols.
      rewrite Hcl; [ flia Hk Hi | ].
      now apply List_hd_in.
    }
    do 2 rewrite Nat.sub_0_r.
    rewrite (List_map_nth' 0). 2: {
      now rewrite comatrix_nrows, List.length_seq.
    }
    rewrite List.seq_nth; [ | now rewrite comatrix_nrows ].
    rewrite List.seq_nth. 2: {
      rewrite comatrix_ncols; unfold mat_ncols; cbn.
      rewrite Hcl; [ flia Hk Hi | now apply List_hd_in ].
    }
    cbn - [ com ].
    easy.
  }
  cbn - [ com ].
  unfold mat_ncols.
  rewrite Hcl; [ | now apply List_hd_in ].
  remember (mk_mat ll) as M eqn:HM.
  erewrite rngl_summation_eq_compat. 2: {
    intros k Hk.
    rewrite HM at 1.
    cbn - [ det ].
    do 2 rewrite Nat.sub_0_r.
    rewrite (List_map_nth' 0); [ | now rewrite List.length_seq ].
    rewrite (List_map_nth' 0). 2: {
      rewrite List.length_seq; unfold mat_ncols.
      rewrite Hcl; [ flia Hk Hll | ].
      now apply List_hd_in.
    }
    rewrite List.seq_nth; [ | easy ].
    rewrite List.seq_nth. 2: {
      unfold mat_ncols.
      rewrite Hcl; [ flia Hk Hll | ].
      now apply List_hd_in.
    }
    cbn - [ det ].
    rewrite rngl_mul_comm; [ | easy ].
    rewrite rngl_mul_mul_swap; [ | easy ].
    replace ll with (mat_list_list M) at 1 by now rewrite HM.
    rewrite fold_mat_el.
    rewrite <- HM.
    easy.
  }
  cbn - [ det ].
  replace (length ll) with (mat_nrows M) in Hi, Hj, Hcl |-* by now rewrite HM.
  apply Nat.neq_sym in Hij.
  erewrite rngl_summation_eq_compat. 2: {
    intros k Hk.
    rewrite <- Nat.sub_succ_l; [ | easy ].
    now rewrite Nat_sub_succ_1.
  }
  cbn - [ det ].
  specialize (determinant_with_bad_row Hon Hop Hic Hch Hii) as H1.
  specialize (H1 (S j) (S i) M).
  apply H1; [ | flia Hj | flia Hi | flia Hij ].
  apply is_scm_mat_iff; cbn.
  split; [ easy | ].
  intros l Hl; rewrite HM in Hl; cbn in Hl.
  now apply Hcl.
}
Qed.

Theorem comatrix_transp_matrix_mul :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_characteristic T = 0 →
  (rngl_is_integral_domain T || rngl_has_inv_or_quot T)%bool = true →
  ∀ (M : matrix T),
  is_square_matrix M = true
  → ((com M)⁺ * M = det M × mI (mat_nrows M))%M.
Proof.
intros Hon Hop Hic Hch Hii * Hsm.
assert (H10 : rngl_characteristic T ≠ 1) by now rewrite Hch.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
destruct M as (ll); cbn - [ det ].
destruct (Nat.eq_dec (length ll) 0) as [Hlz| Hlz]. {
  apply List.length_zero_iff_nil in Hlz; subst ll; cbn.
  unfold "*"%M, mI; cbn; symmetry.
  apply (mat_mul_scal_1_l Hon).
}
apply Nat.neq_0_lt_0 in Hlz.
destruct (Nat.eq_dec (length ll) 1) as [Hl1| Hl1]. {
  destruct ll as [| l]; [ easy | ].
  destruct ll; [ clear Hl1 | easy ].
  apply is_scm_mat_iff in Hsm.
  unfold mat_ncols in Hsm; cbn - [ List.In ] in Hsm.
  destruct Hsm as (_, Hcl).
  progress unfold "*"%M, "×"%M, mat_transp, mat_mul_el, com; cbn.
  rewrite Hcl; [ cbn | now left ].
  progress unfold mat_mul_el.
  do 2 rewrite rngl_summation_only_one; cbn.
  now do 3 rewrite (rngl_mul_1_r Hon).
}
unfold "*"%M, "×"%M, mat_nrows; cbn - [ det ]; f_equal.
rewrite List.map_map.
rewrite List_length_map_seq.
rewrite comatrix_ncols.
generalize Hsm; intros Hsm_v.
apply is_scm_mat_iff in Hsm.
cbn in Hsm.
destruct Hsm as (Hcr, Hcl).
unfold mat_ncols at 2.
rewrite Hcl; [ | now apply List_hd_in ].
rewrite <- (List.seq_shift (length ll)), List.map_map.
apply List.map_ext_in.
intros i Hi; apply List.in_seq in Hi.
unfold mat_ncols.
rewrite Hcl; [ | now apply List_hd_in ].
rewrite List.map_map.
rewrite <- List.seq_shift, List.map_map.
apply List.map_ext_in.
intros j Hj; apply List.in_seq in Hj.
move j before i.
rewrite laplace_formula_on_cols with (j := S j); try easy. 2: {
  rewrite squ_mat_ncols; [ cbn | easy ].
  flia Hj.
}
unfold mat_mul_el.
rewrite mat_transp_ncols.
rewrite comatrix_ncols.
unfold mat_ncols.
rewrite Hcl; [ | now apply List_hd_in ].
rewrite comatrix_nrows.
cbn - [ mat_el com ].
apply Nat.neq_0_lt_0 in Hlz.
apply Nat.eqb_neq in Hlz; rewrite Hlz.
apply Nat.eqb_neq, Nat.neq_0_lt_0 in Hlz.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  (* diagonal *)
  subst j; rewrite δ_diag, (rngl_mul_1_r Hon).
  erewrite rngl_summation_eq_compat. 2: {
    intros k Hk.
    rewrite rngl_mul_comm; [ | easy ].
    easy.
  }
  cbn - [ mat_el com ].
  apply rngl_summation_eq_compat.
  intros k Hk.
  symmetry; f_equal; rewrite mat_transp_el; [ easy | | easy | flia Hk ].
  apply squ_mat_is_corr.
  now apply comatrix_is_square.
} {
  (* not on diagonal: zeroes *)
  rewrite δ_ndiag; [ | easy ].
  rewrite rngl_mul_0_r; [ | easy ].
  unfold mat_transp.
  cbn - [ com ].
  erewrite rngl_summation_eq_compat. 2: {
    intros k Hk.
    rewrite (List_map_nth' 0). 2: {
      rewrite List.length_seq, comatrix_ncols.
      unfold mat_ncols.
      rewrite Hcl; [ flia Hk Hi | ].
      now apply List_hd_in.
    }
    rewrite (List_map_nth' 0). 2: {
      rewrite List.length_seq, comatrix_nrows; cbn.
      flia Hk Hlz.
    }
    rewrite List.seq_nth; [ | rewrite comatrix_nrows; cbn; flia Hk Hlz ].
    rewrite List.seq_nth. 2: {
      rewrite comatrix_ncols; unfold mat_ncols; cbn.
      rewrite Hcl; [ flia Hk Hi | now apply List_hd_in ].
    }
    cbn - [ com ].
    easy.
  }
  cbn - [ com ].
  remember (mk_mat ll) as M eqn:HM.
  erewrite rngl_summation_eq_compat. 2: {
    intros k Hk.
    do 2 rewrite Nat.sub_0_r.
    rewrite <- Nat.sub_succ_l; [ | easy ].
    rewrite Nat_sub_succ_1.
    rewrite HM at 1.
    cbn - [ det ].
    rewrite Nat.sub_0_r.
    rewrite (List_map_nth' 0); [ | rewrite List.length_seq; flia Hk Hlz ].
    rewrite (List_map_nth' 0). 2: {
      rewrite List.length_seq; unfold mat_ncols.
      rewrite Hcl; [ easy | ].
      now apply List_hd_in.
    }
    rewrite List.seq_nth; [ | flia Hk Hlz ].
    rewrite (Nat.add_comm 1 (k - 1)), Nat.sub_add; [ | easy ].
    rewrite List.seq_nth. 2: {
      unfold mat_ncols.
      rewrite Hcl; [ easy | ].
      now apply List_hd_in.
    }
    cbn - [ det ].
    rewrite rngl_mul_mul_swap; [ | easy ].
    replace ll with (mat_list_list M) at 1 by now rewrite HM.
    rewrite fold_mat_el.
    rewrite <- HM.
    easy.
  }
  cbn - [ det ].
  replace (length ll) with (mat_nrows M) in Hi, Hj, Hcl |-* by now rewrite HM.
  destruct Hi as (_, Hi); cbn in Hi.
  destruct Hj as (_, Hj); cbn in Hj.
  (* perhaps all of this below would be a "determinant_with_bad_col":
     perhaps a cool lemma to do? *)
  specialize (determinant_with_bad_row Hon Hop Hic Hch Hii) as H1.
  specialize (H1 (S i) (S j) (M⁺)%M).
  assert (Hsmt : is_square_matrix M⁺ = true). {
    now apply mat_transp_is_square.
  }
  specialize (H1 Hsmt).
  rewrite mat_transp_nrows in H1.
  rewrite squ_mat_ncols in H1; [ | easy ].
  assert (H : 1 ≤ S i ≤ mat_nrows M) by flia Hi.
  specialize (H1 H); clear H.
  assert (H : 1 ≤ S j ≤ mat_nrows M) by flia Hj.
  specialize (H1 H); clear H.
  assert (H : S i ≠ S j) by flia Hij.
  specialize (H1 H); clear H.
  erewrite rngl_summation_eq_compat in H1. 2: {
    intros k Hk.
    rewrite <- (determinant_transpose Hon Hic Hop H10). 2: {
      apply is_squ_mat_subm. {
        rewrite mat_transp_nrows, squ_mat_ncols; [ | easy ].
        flia Hk Hi.
      } {
        rewrite mat_transp_nrows, squ_mat_ncols; [ | easy ].
        flia Hk Hi.
      }
      now apply mat_transp_is_square.
    }
    rewrite mat_subm_transp; cycle 1. {
      now apply mat_transp_is_square.
    } {
      rewrite mat_transp_ncols.
      assert (H : (mat_ncols M =? 0) = false). {
        rewrite squ_mat_ncols; [ | easy ].
        apply Nat.eqb_neq; flia Hi.
      }
      now rewrite H.
    } {
      rewrite mat_transp_nrows.
      split; [ flia | ].
      rewrite squ_mat_ncols; [ | easy ].
      flia Hi.
    }
    rewrite mat_transp_involutive. 2: {
      now apply squ_mat_is_corr.
    } 
    rewrite mat_transp_el; [ | now apply squ_mat_is_corr | easy | flia Hk ].
    rewrite Nat.add_comm.
    easy.
  }
  cbn - [ det ] in H1.
  erewrite rngl_summation_eq_compat. 2: {
    intros k Hk.
    rewrite <- Nat.sub_succ_l; [ | easy ].
    now rewrite Nat_sub_succ_1.
  }
  easy.
}
Qed.

Definition mat_inv (M : matrix T) := ((det M)⁻¹ × (com M)⁺)%M.

Theorem mat_mul_inv_diag_r :
  charac_0_field T →
  ∀ (M : matrix T),
  is_square_matrix M = true
  → det M ≠ 0%L
  → (M * mat_inv M = mI (mat_nrows M))%M.
Proof.
intros Hif * Hsm Hdz.
destruct Hif as (Hon, Hic, Hop, Hin, Hde, Hch).
destruct (Nat.eq_dec (mat_nrows M) 0) as [Hrz| Hrz]. {
  rewrite Hrz; cbn.
  unfold mat_nrows in Hrz.
  apply List.length_zero_iff_nil in Hrz.
  now destruct M as (ll); cbn in Hrz; subst ll.
}
unfold mat_inv.
rewrite (mat_mul_mul_scal_l Hop Hic); cycle 1. {
  apply squ_mat_is_corr.
  apply mat_transp_is_square.
  now apply comatrix_is_square.
} {
  apply is_scm_mat_iff in Hsm.
  destruct Hsm as (Hcr, Hcl).
  now intros H; apply Hrz, Hcr.
} {
  rewrite mat_transp_nrows; symmetry.
  apply comatrix_ncols.
}
rewrite (matrix_comatrix_transp_mul Hon Hop Hic Hch); [ | | easy ]. 2: {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_or_quot_iff; left.
}
rewrite mat_mul_scal_l_mul_assoc.
rewrite rngl_mul_inv_diag_l; [ | easy | easy | easy ].
now apply mat_mul_scal_1_l.
Qed.

Theorem mat_mul_inv_diag_l :
  charac_0_field T →
  ∀ (M : matrix T),
  is_square_matrix M = true
  → det M ≠ 0%L
  → (mat_inv M * M = mI (mat_nrows M))%M.
Proof.
intros Hif * Hsm Hdz.
destruct Hif as (Hon, Hic, Hop, Hin, Hde, Hch).
unfold mat_inv.
rewrite mat_mul_scal_l_mul; [ | easy | ]. 2: {
  apply squ_mat_is_corr.
  apply mat_transp_is_square.
  now apply comatrix_is_square.
}
rewrite (comatrix_transp_matrix_mul Hon Hop Hic Hch); [ | | easy ]. 2: {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_or_quot_iff; left.
}
rewrite mat_mul_scal_l_mul_assoc.
rewrite rngl_mul_inv_diag_l; [ | easy | easy | easy ].
now apply mat_mul_scal_1_l.
Qed.

Notation "A ⁻¹" := (mat_inv A) (at level 1, format "A ⁻¹") : M_scope.

Theorem mat_inv_nrows : ∀ M, mat_nrows M⁻¹ = mat_ncols M.
Proof.
intros.
unfold mat_inv.
rewrite mat_mul_scal_l_nrows.
rewrite mat_transp_nrows.
apply comatrix_ncols.
Qed.

Theorem mat_inv_ncols : ∀ M,
  mat_ncols M⁻¹ = if mat_ncols M =? 0 then 0 else mat_nrows M.
Proof.
intros.
unfold mat_inv.
rewrite mat_mul_scal_l_ncols.
rewrite mat_transp_ncols.
now rewrite comatrix_ncols, comatrix_nrows.
Qed.

Theorem mat_inv_is_corr : ∀ M,
  is_correct_matrix M = true
  → is_correct_matrix M⁻¹ = true.
Proof.
intros * Hcm.
unfold mat_inv.
apply is_correct_matrix_mul_scal_l.
apply mat_transp_is_corr.
now apply comatrix_is_correct.
Qed.

Theorem mat_inv_det_comm :
  charac_0_field T →
  ∀ M,
  is_square_matrix M = true
  → det M ≠ 0%L
  → (M⁻¹ = (1%L / det M) × (com M)⁺)%M.
Proof.
intros Hif * Hsm Hmz.
generalize Hif; intros H.
destruct H as (Hon, Hic, Hop, Hin, Hde, Hch).
specialize (matrix_comatrix_transp_mul Hon Hop Hic Hch) as H1.
assert (Hiq : rngl_has_inv_or_quot T = true). {
  now apply rngl_has_inv_or_quot_iff; left.
}
specialize (H1 (proj2 (Bool.orb_true_iff _ _) (or_intror Hiq))).
specialize (H1 M Hsm).
specialize (mat_mul_inv_diag_l Hif M Hsm Hmz) as H3.
apply (f_equal (mat_mul M⁻¹)) in H1.
destruct (Nat.eq_dec (mat_nrows M) 0) as [Hrz| Hrz]. {
  destruct M as (ll).
  cbn in Hrz.
  apply List.length_zero_iff_nil in Hrz; subst ll.
  cbn.
  unfold mat_transp, mat_inv, com; cbn.
  unfold mat_transp; cbn.
  rewrite rngl_inv_1; [ | easy | easy | now rewrite Hch ].
  rewrite (rngl_div_1_r Hon); cycle 1. {
    now apply rngl_has_inv_or_quot_iff; left.
  } {
    now rewrite Hch.
  }
  easy.
}
assert (Hcz : mat_ncols M ≠ 0). {
  now rewrite (squ_mat_ncols _ Hsm).
}
rewrite mat_mul_assoc in H1; [ | easy | easy | easy | ]. 2: {
  rewrite mat_inv_ncols.
  rewrite if_eqb_eq_dec.
  now destruct (Nat.eq_dec _ _).
}
rewrite H3 in H1.
rewrite (mat_mul_1_l Hon) in H1; [ | easy | | ]; cycle 1. {
  apply mat_transp_is_corr.
  apply comatrix_is_correct.
  now apply squ_mat_is_corr.
} {
  rewrite mat_transp_nrows.
  rewrite comatrix_ncols.
  symmetry; apply (squ_mat_ncols _ Hsm).
}
rewrite (mat_mul_mul_scal_l Hop Hic) in H1; cycle 1. {
  apply mI_is_correct_matrix.
} {
  rewrite mat_inv_ncols.
  rewrite if_eqb_eq_dec.
  now destruct (Nat.eq_dec _ _).
} {
  rewrite mat_inv_ncols.
  rewrite mI_nrows.
  rewrite if_eqb_eq_dec.
  now destruct (Nat.eq_dec _ _).
}
rewrite (mat_mul_1_r Hon Hop) in H1; cycle 1. {
  apply mat_inv_is_corr.
  now apply squ_mat_is_corr.
} {
  rewrite mat_inv_ncols.
  rewrite if_eqb_eq_dec.
  now destruct (Nat.eq_dec _ _).
}
rewrite H1.
rewrite mat_mul_scal_l_mul_assoc.
rewrite (rngl_div_1_l Hon); [ | easy ].
rewrite (rngl_mul_inv_diag_l Hon); [ | easy | easy ].
symmetry; apply (mat_mul_scal_1_l Hon).
Qed.

Theorem vect_el_mul_scal_l : ∀ μ V i,
  1 ≤ i ≤ vect_size V
  → vect_el (μ × V) i = (μ * vect_el V i)%L.
Proof.
intros * Hi; cbn.
apply (List_map_nth' 0%L).
rewrite fold_vect_size.
flia Hi.
Qed.

Theorem vect_size_mat_mul_vect_r : ∀ A V, vect_size (A • V) = mat_nrows A.
Proof.
intros; cbn.
now rewrite List.length_map.
Qed.

Theorem det_mat_repl_vect :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_characteristic T ≠ 1 →
  ∀ M V,
  is_square_matrix M = true
  → vect_size V = mat_nrows M
  → ∀ k, 1 ≤ k ≤ mat_ncols M
  → det (mat_repl_vect k M V) = vect_el ((com M)⁺ • V) k.
Proof.
intros Hon Hop Hic H10 * Hsm Hvm * Hk.
specialize (squ_mat_is_corr _ Hsm) as Hcm.
move Hcm before Hsm.
assert (Hk' : k - 1 < mat_ncols M) by flia Hk.
rewrite (laplace_formula_on_cols Hon Hop Hic H10) with (j := k); cycle 1. {
  now apply mat_repl_vect_is_square.
} {
  rewrite <- (squ_mat_ncols _ Hsm) in Hvm.
  now rewrite mat_repl_vect_ncols.
}
rewrite mat_repl_vect_nrows; [ | easy ].
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite mat_el_repl_vect; [ | easy | now rewrite Hvm | easy | easy | easy ].
  now rewrite <- if_eqb_eq_dec, Nat.eqb_refl.
}
cbn - [ mat_el vect_el ].
unfold mat_mul_vect_r.
cbn - [ mat_el com ].
rewrite comatrix_ncols.
rewrite (List_map_nth' []); [ | now rewrite List_length_map_seq ].
unfold vect_dot_mul.
cbn - [ mat_el com ].
rewrite (List_map_nth' 0); [ | now rewrite List.length_seq ].
rewrite List_map2_map_l.
rewrite List_map2_map2_seq_l with (d := 0).
rewrite List_map2_map2_seq_r with (d := 0%L).
rewrite List.length_seq.
rewrite fold_vect_size, Hvm.
rewrite comatrix_nrows.
rewrite List_map2_diag.
rewrite rngl_summation_list_map.
rewrite rngl_summation_seq_summation. 2: {
  rewrite <- (squ_mat_ncols _ Hsm); flia Hk.
}
symmetry.
rewrite rngl_summation_rshift.
rewrite Nat.add_0_l.
rewrite <- Nat_succ_sub_succ_r. 2: {
  rewrite <- (squ_mat_ncols _ Hsm); flia Hk.
}
rewrite Nat.sub_0_r.
apply rngl_summation_eq_compat.
intros i Hi.
assert (Hi' : i - 1 < mat_nrows M) by flia Hi.
rewrite fold_vect_el.
rewrite <- Nat_succ_sub_succ_r; [ | flia Hi ].
rewrite Nat.sub_0_r.
rewrite rngl_mul_comm; [ | easy ].
f_equal.
unfold com.
cbn - [ det ].
rewrite List.seq_nth; [ | easy ].
rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
rewrite (List.seq_nth _ _ Hi').
rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
rewrite (List_map_nth' 0); [ | now rewrite List.length_seq ].
rewrite (List.seq_nth _ _ Hi').
rewrite (List_map_nth' 0); [ | now rewrite List.length_seq ].
rewrite (List.seq_nth _ _ Hk').
rewrite (List_map_nth' 0). 2: {
  rewrite List.length_seq, List_length_map2.
  rewrite fold_mat_nrows, fold_vect_size, Hvm.
  now rewrite Nat.min_id.
}
rewrite List.seq_nth. 2: {
  rewrite List_length_map2.
  rewrite fold_mat_nrows, fold_vect_size, Hvm.
  now rewrite Nat.min_id.
}
rewrite (List_map_nth' 0). 2: {
  rewrite List.length_seq, mat_repl_vect_ncols; [ easy | easy | ].
  now rewrite (squ_mat_ncols _ Hsm).
}
rewrite List.seq_nth. 2: {
  rewrite mat_repl_vect_ncols; [ easy | easy | ].
  now rewrite (squ_mat_ncols _ Hsm).
}
f_equal.
rewrite (Nat.add_comm _ (i - 1)), Nat.sub_add; [ | easy ].
rewrite (Nat.add_comm _ (k - 1)), Nat.sub_add; [ | easy ].
unfold mat_repl_vect.
unfold subm.
cbn - [ det ].
rewrite List_map_butn.
rewrite List_map_butn.
rewrite List_map_map2.
rewrite List_map2_map2_seq_l with (d := []).
rewrite List_map2_map2_seq_r with (d := 0%L).
rewrite fold_mat_nrows.
rewrite fold_vect_size.
rewrite Hvm.
rewrite List_map2_diag.
symmetry.
erewrite List.map_ext_in. 2: {
  intros j Hj.
  apply List.in_seq in Hj.
  unfold replace_at.
  rewrite List_butn_app.
  rewrite List.length_firstn.
  rewrite fold_corr_mat_ncols; [ | easy | easy ].
  rewrite min_l; [ | flia Hk ].
  rewrite Nat.ltb_irrefl.
  rewrite Nat.sub_diag.
  rewrite List_butn_0_cons.
  now rewrite List_fold_butn.
}
unfold mat_nrows.
now rewrite <- List_map_map_seq.
Qed.

(* Cramer's rule *)

Theorem cramer's_rule_by_mul :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_characteristic T = 0 →
  (rngl_is_integral_domain T || rngl_has_inv_or_quot T)%bool = true →
  ∀ [M : matrix T] [U V : vector T],
  is_square_matrix M = true
  → vect_size U = mat_nrows M
  → (M • U)%V = V
  → ∀ [i], 1 ≤ i ≤ mat_nrows M →
  (det M * vect_el U i)%L = det (mat_repl_vect i M V).
Proof.
intros Hon Hop Hic Hch Hii * Hsm Hum Hmuv k Hk.
assert (H10 : rngl_characteristic T ≠ 1) by now rewrite Hch.
assert (Huv : vect_size V = vect_size U). {
  rewrite <- Hmuv; cbn.
  now rewrite List.length_map.
}
rewrite <- (squ_mat_ncols _ Hsm) in Hk.
rewrite (det_mat_repl_vect Hon Hop Hic H10); [ | easy | congruence | easy ].
rewrite <- Hmuv.
rewrite (mat_vect_mul_assoc Hop); cycle 1. {
  apply mat_transp_is_corr.
  apply comatrix_is_correct.
  now apply squ_mat_is_corr.
} {
  now apply squ_mat_is_corr.
} {
  symmetry.
  rewrite mat_transp_ncols.
  rewrite comatrix_ncols.
  rewrite comatrix_nrows.
  rewrite squ_mat_ncols; [ | easy ].
  rewrite if_eqb_eq_dec.
  now destruct (Nat.eq_dec _ _).
} {
  rewrite squ_mat_ncols; [ congruence | easy ].
}
rewrite (comatrix_transp_matrix_mul Hon Hop Hic Hch Hii); [ | easy ].
rewrite <- (mat_mul_scal_vect_assoc Hop); cycle 1. {
  apply mI_is_correct_matrix.
} {
  rewrite mI_ncols; congruence.
}
rewrite vect_el_mul_scal_l. 2: {
  split; [ easy | ].
  rewrite vect_size_mat_mul_vect_r.
  rewrite mI_nrows.
  now rewrite <- squ_mat_ncols.
}
f_equal.
now rewrite mat_vect_mul_1_l.
Qed.

Theorem cramer's_rule :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_has_inv_or_quot T = true →
  rngl_characteristic T = 0 →
  ∀ (M : matrix T) (U V : vector T),
  is_square_matrix M = true
  → vect_size U = mat_nrows M
 → det M ≠ 0%L
  → (M • U)%V = V
  → ∀ i, 1 ≤ i ≤ mat_nrows M →
  vect_el U i = (det (mat_repl_vect i M V) / det M)%L.
Proof.
intros Hon Hop Hic Hiq Hch * Hsm Hum Hmz Hmuv k Hk.
assert (Hi1 : rngl_has_inv_and_1_or_quot T = true). {
  apply rngl_has_inv_or_quot_iff in Hiq.
  apply rngl_has_inv_and_1_or_quot_iff.
  now destruct Hiq; [ left | right ].
}
assert
  (Hii : (rngl_is_integral_domain T || rngl_has_inv_or_quot T)%bool = true). {
  rewrite Hiq.
  now apply Bool.orb_true_iff; right.
}
rewrite <- (cramer's_rule_by_mul Hon Hop Hic Hch Hii Hsm Hum Hmuv Hk).
rewrite (rngl_mul_comm Hic).
symmetry.
apply (rngl_mul_div Hi1 _ _ Hmz).
Qed.

End a.

Notation "A ⁻¹" := (mat_inv A) (at level 1, format "A ⁻¹") : M_scope.

(* tests
Require Import RnglAlg.Qrl.
Require Import RnglAlg.Rational.
Import Q.Notations.
Open Scope Q_scope.
Compute 3.
Compute
  (let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1];[18;3;2;1]] in
   (det M, mat_inv M)).
Compute
  (let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1];[18;3;2;1]] in
   (M * mat_inv M)%M).
Compute
  (let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1];[18;3;2;1]] in
   (mat_inv M * M)%M).
Compute
  (let M := mk_mat [[3;0;0;1];[0;0;2;7];[1;0;1;1];[18;0;2;1]] in
   (det M, com M)).
Compute
  (let M := mk_mat [[3;0;0;1];[0;0;2;7];[1;0;1;1];[18;0;2;1]] in
   (det M, (M * com M)%M, (com M * M)%M)).
*)
