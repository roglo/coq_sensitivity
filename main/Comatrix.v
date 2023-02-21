(* comatrices *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Misc RingLike IterAdd IterMul Pigeonhole.
Require Import PermutationFun SortingFun SortRank.
Require Import Matrix PermutSeq Signature Determinant.
Require Import MyVector.
Import matrix_Notations.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

Definition com (M : matrix T) : matrix T :=
  mk_mat
    (map
      (λ i,
       map (λ j, (minus_one_pow (i + j) * det (subm i j M))%L)
         (seq 1 (mat_ncols M)))
      (seq 1 (mat_nrows M))).

Arguments com M%M.

Theorem mat_swap_same_rows : ∀ (M : matrix T) i,
  mat_swap_rows i i M = M.
Proof.
intros.
destruct M as (ll); cbn.
unfold mat_swap_rows; f_equal.
cbn - [ list_swap_elem ].
rewrite (List_map_nth_seq ll (nth i ll [])) at 2.
unfold list_swap_elem.
apply map_ext_in.
intros j Hj; apply in_seq in Hj.
rewrite transposition_id.
now apply nth_indep.
Qed.

Theorem mat_swap_rows_comm : ∀ (M : matrix T) p q,
  mat_swap_rows p q M = mat_swap_rows q p M.
Proof.
intros.
unfold mat_swap_rows; f_equal; cbn.
unfold list_swap_elem.
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
now rewrite transposition_comm.
Qed.

Theorem subm_mat_swap_rows_lt_lt : ∀ (M : matrix T) p q r j,
  p < q < r
  → subm r j (mat_swap_rows p q M) = mat_swap_rows p q (subm r j M).
Proof.
intros * (Hpq, Hq).
destruct M as (ll); cbn.
unfold subm, mat_swap_rows; cbn; f_equal.
rewrite map_length.
rewrite butn_length.
rewrite <- map_butn, map_map.
rewrite map_butn_seq.
rewrite Nat.add_0_l.
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
unfold Nat.b2n.
rewrite if_leb_le_dec.
destruct Hi as (_, Hi).
destruct (le_dec (r - 1) i) as [Hir| Hir]. 2: {
  apply Nat.nle_gt in Hir.
  rewrite Nat.add_0_r.
  destruct (Nat.eq_dec i (p - 1)) as [Hip| Hip]. {
    subst i; clear Hir.
    rewrite transposition_1.
    destruct (lt_dec (q - 1) (length (butn (r - 1) ll))) as [Hqrl| Hqrl]. {
      rewrite (List_map_nth' []); [ | easy ].
      rewrite nth_butn_after; [ easy | flia Hpq Hq ].
    }
    apply Nat.nlt_ge in Hqrl.
    symmetry.
    rewrite nth_overflow; [ | now rewrite map_length ].
    rewrite butn_length in Hqrl.
    destruct (le_dec (length ll) (q - 1)) as [Hlq| Hlq]. {
      rewrite nth_overflow; [ | easy ].
      now rewrite butn_nil.
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
    destruct (lt_dec (p - 1) (length (butn (r - 1) ll))) as [Hprl| Hprl]. {
      rewrite (List_map_nth' []); [ | easy ].
      rewrite nth_butn_after; [ easy | flia Hpq Hq ].
    }
    apply Nat.nlt_ge in Hprl.
    rewrite butn_length in Hprl.
    flia Hpq Hi Hprl.
  }
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec i (p - 1)) as [H| H]; [ easy | clear H ].
  destruct (Nat.eq_dec i (q - 1)) as [H| H]; [ easy | clear H ].
  rewrite map_butn.
  rewrite nth_butn_after; [ | easy ].
  rewrite (List_map_nth' []); [ easy | flia Hi ].
}
unfold transposition.
do 4 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec i (p - 1)) as [H| H]; [ flia Hpq Hq Hir H | clear H ].
destruct (Nat.eq_dec i (q - 1)) as [H| H]; [ flia Hpq Hq Hir H | clear H ].
destruct (Nat.eq_dec (i + 1) (p - 1)) as [H| H]; [ flia Hpq Hq Hir H | clear H ].
destruct (Nat.eq_dec (i + 1) (q - 1)) as [H| H]; [ flia Hq Hir H | clear H ].
rewrite map_butn.
rewrite nth_butn_before; [ | easy ].
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
rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hql ].
rewrite seq_nth; [ | flia Hql ].
rewrite Nat.add_0_l.
now rewrite transposition_2.
Qed.

Theorem length_fold_left_map_transp : ∀ A (ll : list A) sta len f g d,
  length
    (fold_left
       (λ ll' k,
        map (λ i, nth (transposition (f k) (g k) i) ll' d)
          (seq 0 (length ll')))
       (seq sta len) ll) = length ll.
Proof.
intros.
induction len; [ easy | ].
rewrite seq_S.
rewrite fold_left_app; cbn.
rewrite List_map_seq_length.
apply IHlen.
Qed.

Theorem mat_nrows_fold_left_swap : ∀ (M : matrix T) p q f g,
  mat_nrows (fold_left (λ M' k, mat_swap_rows (f k) (g k) M') (seq p q) M) =
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
  → nth i
      (fold_left
         (λ la' k,
            map (λ j, nth (transposition k (k + 1) j) la' d)
              (seq 0 (length la')))
         (seq sta len) la) d =
    nth i la d.
Proof.
intros * Hi Hip.
induction len; [ easy | ].
rewrite seq_S; cbn.
rewrite fold_left_app; cbn.
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  now rewrite length_fold_left_map_transp.
}
rewrite seq_nth. 2: {
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
  → nth i
      (fold_left
         (λ la' k,
            map (λ j, nth (transposition k (k + 1) j) la' d)
              (seq 0 (length la')))
         (seq sta n) u) d =
     nth (i + 1) u d.
Proof.
intros * Hn Hi.
revert i Hi.
induction n; intros; [ flia Hi  | ].
assert (H : sta + n ≤ length u) by flia Hn.
specialize (IHn H); clear H.
rewrite <- Nat.add_sub_assoc in Hi; [ | flia ].
rewrite Nat_sub_succ_1 in Hi.
rewrite seq_S.
rewrite fold_left_app.
destruct (Nat.eq_dec i (sta + n - 1)) as [Hin| Hin]. {
  subst i.
  rewrite Nat.sub_add; [ | flia Hi ].
  cbn.
  rewrite length_fold_left_map_transp.
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hn ].
  rewrite seq_nth; [ | flia Hn ].
  rewrite transposition_out; [ cbn | flia Hi | flia ].
  destruct n; [ flia Hi | ].
  rewrite <- Nat.add_sub_assoc; [ | flia ].
  rewrite Nat_sub_succ_1.
  rewrite seq_S; cbn.
  rewrite fold_left_app; cbn.
  rewrite length_fold_left_map_transp.
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hn ].
  rewrite seq_nth; [ | flia Hn ].
  rewrite transposition_1.
  rewrite Nat.add_1_r.
  rewrite nth_fold_left_map_transp_1; [ | flia Hn | right; flia ].
  now rewrite <- Nat.add_succ_comm.
}
cbn.
rewrite length_fold_left_map_transp.
rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hn Hi ].
rewrite seq_nth; [ | flia Hn Hi ].
rewrite transposition_out; [ cbn | flia Hi | flia Hi Hin ].
apply IHn.
flia Hi Hin.
Qed.

Theorem nth_fold_left_map_transp : ∀ A (la : list A) i sta len d,
  nth i
    (fold_left
       (λ la' k,
          map (λ j, nth (transposition k (k + 1) j) la' d)
            (seq 0 (length la')))
       (seq sta len) la) d =
  if le_dec (length la) i then d
  else if Nat.eq_dec i (sta + len) then nth sta la d
  else if le_dec (length la) sta then nth i la d
  else if le_dec (length la) (sta + len) then
    nth i
      (fold_left
         (λ la' k,
          map (λ j, nth (transposition k (k + 1) j) la' d)
            (seq 0 (length la)))
         (seq sta (length la - sta)) la) d
  else
    nth (i + Nat.b2n ((sta <=? i) && (i <=? sta + len))) la d.
Proof.
intros.
destruct (le_dec (length la) i) as [Hi| Hi]. {
  rewrite nth_overflow; [ easy | ].
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
  rewrite IHlen; [ | now rewrite List_map_seq_length ].
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hi ].
  rewrite seq_nth; [ | flia Hi ].
  rewrite Nat.add_0_l, Nat.add_1_r.
  now rewrite transposition_2.
}
unfold Nat.b2n, "&&", negb.
destruct (le_dec (length la) sta) as [Hsla| Hsla]. {
  rewrite List_fold_left_map_nth_len.
  erewrite List_fold_left_ext_in. 2: {
    intros j v Hj; apply in_seq in Hj.
    erewrite map_ext_in. 2: {
      intros k Hk; apply in_seq in Hk.
      rewrite transposition_out; [ | flia Hsla Hj Hk | flia Hsla Hj Hk ].
      easy.
    }
    easy.
  }
  rewrite <- (List_seq_shift' len).
  rewrite List_fold_left_map.
  rewrite <- List_fold_left_map_nth_len.
  rewrite List_fold_left_nop_r.
  rewrite seq_length.
  rewrite repeat_apply_id. 2: {
    intros u.
    symmetry; apply List_map_nth_seq.
  }
  easy.
}
apply Nat.nle_gt in Hsla.
destruct (le_dec (length la) (sta + len)) as [Hsl| Hsl]. {
  replace len with (length la - sta + (sta + len - length la)) at 1
    by flia Hsla Hsl.
  rewrite seq_app.
  rewrite fold_left_app.
  rewrite Nat.add_comm, Nat.sub_add; [ | flia Hsla ].
  rewrite List_fold_left_map_nth_len.
  erewrite List_fold_left_ext_in. 2: {
    intros j v Hj; apply in_seq in Hj.
    erewrite map_ext_in. 2: {
      intros k Hk; apply in_seq in Hk.
      rewrite length_fold_left_map_transp in Hk.
      rewrite transposition_out; [ | flia Hsla Hj Hk | flia Hsla Hj Hk ].
      easy.
    }
    easy.
  }
  rewrite <- List_fold_left_map_nth_len.
  rewrite List_fold_left_nop_r.
  rewrite seq_length.
  rewrite repeat_apply_id. 2: {
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
rewrite seq_S.
rewrite fold_left_app; cbn.
rewrite <- Nat.add_sub_assoc; [ | flia ].
rewrite Nat_sub_succ_1.
rewrite length_fold_left_map_transp.
rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hsl ].
rewrite seq_nth; [ | flia Hsl ].
rewrite transposition_1.
rewrite <- Nat.add_assoc, Nat.add_1_r.
apply nth_fold_left_map_transp_1; [ easy | right; flia ].
Qed.

Theorem nth_fold_left_map_transp' : ∀ A (la : list A) i len d,
  i + 1 < length la
  → i < len
  → nth i
      (fold_left
         (λ la' k,
            map (λ j, nth (transposition k (k + 1) j) la' d)
              (seq 0 (length la'))) 
         (seq 0 len) la) d =
    nth (i + 1) la d.
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
      (fold_left (λ M' k, mat_swap_rows (k + 1) (k + 2) M')
         (seq 0 (p - 2)) M).
Proof.
intros * Hp.
destruct M as (ll); cbn in Hp |-*.
unfold subm; f_equal.
cbn - [ butn ].
f_equal; clear q.
rewrite fold_left_mat_fold_left_list_list.
cbn - [ butn ].
rewrite List_map_nth_seq with (d := []); symmetry.
rewrite List_map_nth_seq with (d := []); symmetry.
rewrite butn_length, map_length, seq_length.
rewrite butn_length.
rewrite length_fold_left_map_transp.
unfold Nat.b2n.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec 0 (length ll)) as [H| H]; [ clear H | flia H Hp ].
destruct (lt_dec (p - 1) (length ll)) as [H| H]; [ clear H | flia H Hp ].
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
cbn in Hi.
rewrite <- map_butn.
rewrite (List_map_nth' 0). 2: {
  rewrite butn_length, seq_length.
  unfold Nat.b2n.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec 0 (length ll)) as [H| H]; [ easy | flia Hp H ].
}
rewrite nth_butn_before; [ | flia ].
rewrite seq_nth; [ cbn | flia Hi ].
erewrite List_fold_left_ext_in. 2: {
  intros j ll' Hj.
  erewrite map_ext_in. 2: {
    intros k Hk.
    now rewrite Nat.add_sub, Nat.add_succ_r, Nat_sub_succ_1.
  }
  easy.
}
destruct (le_dec (p - 1) i) as [Hpi| Hpi]. 2: {
  apply Nat.nle_gt in Hpi.
  rewrite nth_butn_after; [ | easy ].
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
rewrite nth_butn_before; [ | easy ].
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
      (fold_left (λ M' k, mat_swap_rows (k + 1) (k + 2) M')
         (seq 0 m) M) =
    fold_left
      (λ M' k, mat_swap_rows (k + 1) (k + 2) M')
      (seq 0 m) (subm i j M).
Proof.
intros * Hmi.
revert i Hmi.
induction m; intros; [ easy | ].
rewrite seq_S; cbn.
do 2 rewrite fold_left_app; cbn.
rewrite <- IHm; [ | flia Hmi ].
apply subm_mat_swap_rows_lt; flia Hmi.
Qed.

Theorem determinant_circular_shift_rows : in_charac_0_field →
  ∀ (M : matrix T) i,
  i < mat_nrows M
  → is_square_matrix M = true
  → det (fold_left (λ M' k, mat_swap_rows (k + 1) (k + 2) M') (seq 0 i) M) =
    (minus_one_pow i * det M)%L.
Proof.
intros Hif * Hin Hsm.
destruct Hif as (Hic, Hop, Hiv, Hit, Hde, Hch).
remember (mat_nrows M) as n eqn:Hr; symmetry in Hr.
revert M Hsm Hr.
induction i; intros; [ now cbn; rewrite rngl_mul_1_l | ].
assert (H : i < n) by flia Hin.
specialize (IHi H); clear H.
rewrite seq_S; cbn.
rewrite fold_left_app; cbn - [ det ].
rewrite determinant_alternating; [ | easy | flia | | | ]; cycle 1. {
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
      erewrite map_ext_in. 2: {
        intros k Hk.
        now rewrite Nat.add_sub, Nat.add_succ_r, Nat_sub_succ_1.
      }
      easy.
    }
    apply length_zero_iff_nil in Hc'.
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
      apply (f_equal length) in Hc'.
      rewrite Hc in Hc'. 2: {
        apply nth_In.
        rewrite fold_mat_nrows.
        flia Hr Hin.
      }
      easy.
    }
    apply Nat.nle_gt in Hri.
    cbn in Hc'.
    apply (f_equal length) in Hc'.
    rewrite Hc in Hc'. 2: {
      apply nth_In.
      rewrite fold_mat_nrows.
      flia Hr Hin.
    }
    easy.
  }
  intros la Hla.
  rewrite fold_left_mat_fold_left_list_list in Hla.
  cbn in Hla.
  apply In_nth with (d := []) in Hla.
  rewrite length_fold_left_map_transp, fold_mat_nrows in Hla.
  destruct Hla as (j & Hj & Hla).
  erewrite List_fold_left_ext_in in Hla. 2: {
    intros k ll' Hk.
    erewrite map_ext_in. 2: {
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
    apply Hc, nth_In.
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
      apply Hc, nth_In.
      rewrite fold_mat_nrows.
      rewrite Hr in Hj |-*.
      flia Hji' Hin.
    }
    apply Nat.nle_gt in Hji'.
    rewrite Nat.add_0_r.
    apply Hc, nth_In.
    now rewrite fold_mat_nrows.
  }
  now apply Nat.nle_gt in Hjz.
}
rewrite IHi; [ | easy | easy ].
rewrite minus_one_pow_succ; [ | easy ].
now symmetry; apply rngl_mul_opp_l.
Qed.

Theorem determinant_subm_mat_swap_rows_0_i : in_charac_0_field →
  ∀ (M : matrix T) i j,
  is_square_matrix M = true
  → 1 < i ≤ mat_nrows M
  → 1 ≤ j ≤ mat_nrows M
  → det (subm 1 j (mat_swap_rows 1 i M)) =
    (minus_one_pow i * det (subm i j M))%L.
Proof.
intros Hif * Hsm (Hiz, Hin) Hjn.
destruct Hif as (Hic, Hop, Hiv, Hit, Hde, Hch).
rewrite subm_mat_swap_rows_circ. 2: {
  split; [ flia Hiz | easy ].
}
destruct i; [ flia Hiz | ].
rewrite minus_one_pow_succ; [ | easy ].
replace (S i - 2) with (i - 1) by flia.
rewrite subm_fold_left_lt; [ | flia Hiz ].
rewrite determinant_circular_shift_rows; [ | easy | | ]. {
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

(* to be completed
Theorem glop_laplace_formula_on_rows :
  rngl_has_opp = true →
  ∀ (M : matrix T) i,
  is_square_matrix M = true
  → 1 ≤ i ≤ mat_nrows M
  → det M = ∑ (j = 1, mat_ncols M), mat_el M i j * mat_el (com M) i j.
Proof.
intros Hop * Hsm Hlin.
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
  cbn - [ butn ].
  apply rngl_summation_eq_compat.
  intros j Hj.
  rewrite (List_map_nth' 0); [ | rewrite seq_length, Hc; flia Hj Hnz ].
  rewrite seq_nth; [ | rewrite Hc; flia Hj Hnz ].
  rewrite map_length.
  cbn - [ butn ].
  rewrite <- Nat.sub_succ_l; [ | easy ].
  rewrite Nat_sub_succ_1.
  rewrite butn_length, fold_mat_nrows.
  apply Nat.neq_0_lt_0, Nat.ltb_lt in Hnz.
  rewrite Hnz.
  rewrite rngl_mul_assoc.
  f_equal.
...
(* faire un lemme qui prouve que mimus_one_pow commute si rngl_has_opp *)
  unfold minus_one_pow.
  remember (S j mod 2) as k eqn:Hk; symmetry in Hk.
  destruct k. {
    now rewrite rngl_mul_1_r, rngl_mul_1_l.
  }
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_opp_r Hop).
  now rewrite rngl_mul_1_l, rngl_mul_1_r.
}
unfold det.
replace (mat_nrows M) with (S (mat_nrows M - 1)) by flia Hnz.
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1.
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj; cbn.
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hlin ].
  rewrite (List_map_nth' 0); [ | rewrite seq_length, Hc; flia Hj Hnz ].
  rewrite seq_nth; [ | flia Hlin ].
  rewrite seq_nth; [ | flia Hj Hc Hnz ].
  rewrite (Nat.add_comm 1), Nat.sub_add; [ | flia Hlin ].
  rewrite (Nat.add_comm 1), Nat.sub_add; [ | easy ].
  rewrite map_length, butn_length, fold_mat_nrows.
  assert (H : i - 1 < mat_nrows M) by flia Hlin.
  apply Nat.ltb_lt in H; rewrite H; cbn.
  easy.
}
cbn.
rename i into p.
remember (mat_swap_rows 1 p M) as M'.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
...
  rewrite rngl_mul_mul_swap; [ | now destruct Hif ].
  rewrite Nat.add_comm.
  rewrite minus_one_pow_add_r; [ | now destruct Hif ].
  do 2 rewrite <- rngl_mul_assoc.
  rewrite rngl_mul_comm; [ | now destruct Hif ].
  rewrite rngl_mul_assoc.
  specialize determinant_subm_mat_swap_rows_0_i as H1.
  specialize (H1 Hif).
  specialize (H1 M p j Hsm).
  cbn - [ butn ] in H1.
  rewrite map_length, map_butn, butn_length in H1.
  rewrite list_swap_elem_length, fold_mat_nrows in H1.
  rewrite butn_length, map_length, fold_mat_nrows in H1.
  apply Nat.neq_0_lt_0, Nat.ltb_lt in Hnz.
  rewrite Hnz in H1; cbn - [ "<?" ] in H1.
  apply Nat.ltb_lt in Hnz.
  rewrite <- H1; [ | flia Hi1 Hlin | flia Hj Hnz ].
  clear H1.
  rewrite rngl_mul_comm; [ | now destruct Hif ].
  rewrite rngl_mul_assoc, rngl_mul_mul_swap; [ | now destruct Hif ].
  replace (mat_el M p j) with (mat_el (mat_swap_rows 1 p M) 0 j). 2: {
    unfold mat_swap_rows.
    cbn; unfold list_swap_elem.
    rewrite fold_mat_nrows.
    rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
    rewrite seq_nth; [ | easy ].
    rewrite Nat.add_0_r, transposition_1.
    easy.
  }
  rewrite <- HeqM'.
  easy.
}
cbn.
subst M'.
rewrite <- rngl_opp_involutive; [ | now destruct Hif ].
rewrite fold_det.
assert (H1 : 1 ≠ p) by flia Hlin Hi1.
assert (H2 : p - 1 < mat_nrows M) by flia Hlin.
apply Nat.neq_0_lt_0 in Hnz.
rewrite <- (determinant_alternating Hif M H1); [ | easy | easy | easy ].
unfold det.
rewrite mat_swap_rows_nrows.
remember (determinant_loop (mat_nrows M)) as x eqn:Hx.
replace (mat_nrows M) with (S (mat_nrows M - 1)) in Hx by flia Hlin.
subst x.
rewrite determinant_succ.
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1.
rewrite rngl_opp_summation; [ | now destruct Hif ].
apply rngl_summation_eq_compat.
intros i Hi.
rewrite <- rngl_mul_opp_l; [ | now destruct Hif ].
rewrite <- rngl_mul_opp_l; [ | now destruct Hif ].
rewrite minus_one_pow_succ; [ | now destruct Hif ].
rewrite rngl_opp_involutive; [ | now destruct Hif ].
easy.
Qed.
*)

Theorem laplace_formula_on_rows : in_charac_0_field →
  ∀ (M : matrix T) i,
  is_square_matrix M = true
  → 1 ≤ i ≤ mat_nrows M
  → det M = ∑ (j = 1, mat_ncols M), mat_el M i j * mat_el (com M) i j.
Proof.
intros Hif * Hsm Hlin.
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
  cbn - [ butn ].
  apply rngl_summation_eq_compat.
  intros j Hj.
  destruct Hif as (Hic, Hop, Hin, Hit, Hde, Hch).
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_mul_swap; [ | easy ].
  rewrite (List_map_nth' 0); [ | rewrite seq_length, Hc; flia Hj Hnz ].
  rewrite seq_nth; [ | rewrite Hc; flia Hj Hnz ].
  rewrite map_length.
  cbn - [ butn ].
  rewrite <- Nat.sub_succ_l; [ | easy ].
  rewrite Nat_sub_succ_1.
  f_equal; f_equal.
  rewrite butn_length, fold_mat_nrows.
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
  destruct Hif as (Hic, Hop, Hin, Hit, Hde, Hch) in Hj.
  cbn.
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hlin ].
  rewrite (List_map_nth' 0); [ | rewrite seq_length, Hc; flia Hj Hnz ].
  rewrite seq_nth; [ | flia Hlin ].
  rewrite seq_nth; [ | flia Hj Hc Hnz ].
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
  rewrite map_length, butn_length, fold_mat_nrows.
  rewrite rngl_mul_mul_swap; [ | now destruct Hif ].
  rewrite Nat.add_comm.
  rewrite minus_one_pow_add_r; [ | now destruct Hif ].
  do 2 rewrite <- rngl_mul_assoc.
  rewrite rngl_mul_comm; [ | now destruct Hif ].
  rewrite rngl_mul_assoc.
  specialize determinant_subm_mat_swap_rows_0_i as H1.
  specialize (H1 Hif).
  specialize (H1 M p j Hsm).
  cbn - [ butn ] in H1.
  rewrite map_length, map_butn, butn_length in H1.
  rewrite list_swap_elem_length, fold_mat_nrows in H1.
  rewrite butn_length, map_length, fold_mat_nrows in H1.
  apply Nat.neq_0_lt_0, Nat.ltb_lt in Hnz.
  rewrite Hnz in H1; cbn - [ "<?" ] in H1.
  apply Nat.ltb_lt in Hnz.
  rewrite <- H1; [ | flia Hi1 Hlin | flia Hj Hnz ].
  clear H1.
  rewrite rngl_mul_comm; [ | now destruct Hif ].
  rewrite rngl_mul_assoc, rngl_mul_mul_swap; [ | now destruct Hif ].
  replace (mat_el M p j) with (mat_el (mat_swap_rows 1 p M) 0 j). 2: {
    unfold mat_swap_rows.
    cbn; unfold list_swap_elem.
    rewrite fold_mat_nrows.
    rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
    rewrite seq_nth; [ | easy ].
    rewrite Nat.add_0_r, transposition_1.
    easy.
  }
  rewrite <- HeqM'.
  easy.
}
cbn.
subst M'.
rewrite <- rngl_opp_involutive; [ | now destruct Hif ].
rewrite fold_det.
assert (H1 : 1 ≠ p) by flia Hlin Hi1.
assert (H2 : p - 1 < mat_nrows M) by flia Hlin.
apply Nat.neq_0_lt_0 in Hnz.
rewrite <- (determinant_alternating Hif M H1); [ | easy | easy | easy ].
unfold det.
rewrite mat_swap_rows_nrows.
remember (determinant_loop (mat_nrows M)) as x eqn:Hx.
replace (mat_nrows M) with (S (mat_nrows M - 1)) in Hx by flia Hlin.
subst x.
rewrite determinant_succ.
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1.
rewrite rngl_opp_summation; [ | now destruct Hif ].
apply rngl_summation_eq_compat.
intros i Hi.
rewrite <- rngl_mul_opp_l; [ | now destruct Hif ].
rewrite <- rngl_mul_opp_l; [ | now destruct Hif ].
rewrite minus_one_pow_succ; [ | now destruct Hif ].
rewrite rngl_opp_involutive; [ | now destruct Hif ].
easy.
Qed.

Theorem map_permut_seq_permut_seq_with_len : ∀ n σ,
  permut_seq_with_len n σ
  → permut_seq_with_len n (map (λ i, nth i σ 0) (seq 0 n)).
Proof.
intros * Hσ.
split; [ | now rewrite List_map_seq_length ].
apply permut_seq_iff.
split. {
  intros i Hi.
  apply in_map_iff in Hi.
  destruct Hi as (j & Hji & Hj).
  apply in_seq in Hj.
  rewrite List_map_seq_length.
  rewrite <- Hji.
  destruct Hσ as (H1, H2).
  rewrite <- H2 in Hj |-*.
  apply permut_list_ub; [ easy | now apply nth_In ].
} {
  apply (NoDup_map_iff 0).
  rewrite seq_length.
  intros i j Hi Hj Hij.
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
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
now rewrite List_map_seq_length.
Qed.

Theorem comatrix_ncols : ∀ M, mat_ncols (com M) = mat_ncols M.
Proof.
intros.
unfold com.
unfold mat_ncols; cbn.
destruct (Nat.eq_dec (mat_nrows M) 0) as [Hrz| Hrz]. {
  rewrite Hrz; cbn.
  unfold mat_nrows in Hrz.
  now apply length_zero_iff_nil in Hrz; rewrite Hrz.
}
apply Nat.neq_0_lt_0 in Hrz.
rewrite (List_map_hd 0); [ | now rewrite seq_length ].
now rewrite List_map_seq_length.
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
apply in_map_iff in Hl.
destruct Hl as (i & Hil & Hi).
now rewrite <- Hil; rewrite List_map_seq_length.
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
apply in_map_iff in Hl.
destruct Hl as (i & Hil & Hi).
now rewrite <- Hil; rewrite List_map_seq_length.
Qed.

Theorem comatrix_transpose : in_charac_0_field →
  ∀ M,
  is_square_matrix M = true
  → com M⁺ = (com M)⁺%M.
Proof.
intros Hif * Hsm.
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
  apply length_zero_iff_nil in Hrz.
  now rewrite Hrz in Hcz.
}
apply Nat.neq_0_lt_0 in Hcz, Hrz.
unfold mat_transp, com, mat_ncols; cbn - [ det ].
f_equal.
rewrite (List_map_hd 0); [ | now rewrite seq_length ].
rewrite (List_map_hd 0); [ | now rewrite seq_length ].
do 4 rewrite map_length.
do 2 rewrite seq_length.
rewrite fold_mat_ncols.
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
assert (H : 1 ≤ i ≤ mat_ncols M) by flia Hi.
clear Hi; rename H into Hi.
apply map_ext_in.
intros j Hj; apply in_seq in Hj.
assert (H : 1 ≤ j ≤ mat_nrows M) by flia Hj.
clear Hj; rename H into Hj.
assert (Hi' : i - 1 < mat_ncols M) by flia Hi.
assert (Hj' : j - 1 < mat_nrows M) by flia Hj.
move j before i.
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
rewrite seq_nth; [ | easy ].
rewrite (Nat.add_comm 1 (j - 1)), Nat.sub_add; [ | easy ].
rewrite (Nat.add_comm 1 (i - 1)), Nat.sub_add; [ | easy ].
rewrite Nat.add_comm; f_equal; symmetry.
specialize (@fold_mat_transp T ro M) as H1.
rewrite H1.
now apply det_subm_transp.
Qed.

Theorem laplace_formula_on_cols : in_charac_0_field →
  ∀ (M : matrix T) j,
  is_square_matrix M = true
  → 1 ≤ j ≤ mat_ncols M
  → det M = ∑ (i = 1, mat_nrows M), mat_el M i j * mat_el (com M) i j.
Proof.
intros Hif * Hsm Hj.
rewrite <- determinant_transpose; [ | easy | easy ].
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite <- mat_transp_el; [ | | flia Hj | flia Hi ]. 2: {
    now apply squ_mat_is_corr.
  }
  easy.
}
cbn - [ det mat_el ].
specialize (@laplace_formula_on_rows Hif (M⁺)%M j) as H1.
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
rewrite comatrix_transpose; [ | easy | easy ].
symmetry.
apply mat_transp_el; [ | flia Hj | flia Hi ].
apply comatrix_is_correct.
now apply squ_mat_is_corr.
Qed.

(*
The following two theorems, "determinant_with_row" and determinant_with_bad_row
have some similitudes.
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

Theorem determinant_with_row : in_charac_0_field →
  ∀ i (M : matrix T),
  is_square_matrix M = true
  → 1 ≤ i ≤ mat_nrows M
  → det M =
    ∑ (j = 1, mat_nrows M),
    minus_one_pow (i + j) * mat_el M i j * det (subm i j M).
Proof.
intros Hif * Hsm Hir.
assert (Hop : rngl_has_opp = true) by now destruct Hif.
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
rewrite <- (determinant_alternating Hif M Hi1); [ | easy | flia Hir | easy ].
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
rewrite minus_one_pow_add_r; [ | easy ].
rewrite rngl_mul_opp_r; [ | easy ].
rewrite <- rngl_mul_opp_l; [ | easy ].
rewrite <- rngl_mul_opp_l; [ | easy ].
rewrite <- rngl_mul_opp_l; [ | easy ].
do 2 rewrite <- rngl_mul_assoc.
rewrite minus_one_pow_succ; [ | easy ].
f_equal.
rewrite rngl_mul_comm; [ | now destruct Hif ].
rewrite <- rngl_mul_assoc.
rewrite mat_el_mat_swap_rows; [ | flia Hj ].
f_equal.
rewrite rngl_mul_comm; [ | now destruct Hif ].
symmetry.
rewrite mat_swap_rows_comm.
rewrite <- determinant_subm_mat_swap_rows_0_i; try easy; [ | flia Hir Hi1 ].
unfold det.
rewrite mat_nrows_subm.
rewrite mat_swap_rows_nrows.
assert (H : 1 ≤ mat_nrows M) by flia Hir.
now apply Nat.leb_le in H; rewrite H.
Qed.

Theorem determinant_with_bad_row : in_charac_0_field →
  ∀ i k (M : matrix T),
  is_square_matrix M = true
  → 1 ≤ i ≤ mat_nrows M
  → 1 ≤ k ≤ mat_nrows M
  → i ≠ k
  → ∑ (j = 1, mat_nrows M),
    minus_one_pow (i + j) * mat_el M k j * det (subm i j M) = 0%L.
Proof.
intros Hif * Hsm Hir Hkr Hik.
specialize (squ_mat_ncols _ Hsm) as Hc.
remember
  (mk_mat
     (map
        (λ p,
         map (λ q, mat_el M (if p =? i then k else p) q)
           (seq 1 (mat_ncols M)))
        (seq 1 (mat_nrows M))))
  as A eqn:HA.
assert (Hasm : is_square_matrix A = true). {
  subst A.
  apply is_scm_mat_iff; cbn.
  unfold mat_ncols; cbn.
  rewrite List_map_seq_length.
  rewrite (List_map_hd 0); [ | rewrite seq_length; flia Hir ].
  rewrite List_map_seq_length.
  rewrite fold_mat_ncols.
  apply is_scm_mat_iff in Hsm.
  split; [ easy | ].
  intros l Hl.
  apply in_map_iff in Hl.
  destruct Hl as (j & Hjl & Hj).
  apply in_seq in Hj.
  now rewrite <- Hjl, List_map_seq_length.
}
assert (Hira : mat_nrows A = mat_nrows M). {
  now subst A; cbn; rewrite List_map_seq_length.
}
assert (H1 : det A = 0%L). {
  apply determinant_same_rows with (p := i) (q := k); try easy. {
    now rewrite Hira.
  } {
    now rewrite Hira.
  }
  intros j; subst A; cbn.
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hir ].
  symmetry.
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hkr ].
  f_equal.
  apply map_ext_in.
  intros u Hu; apply in_seq in Hu.
  rewrite seq_nth; [ | flia Hkr ].
  rewrite seq_nth; [ | flia Hir ].
  rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
  rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
  cbn; rewrite Nat.eqb_refl.
  apply Nat.neq_sym, Nat.eqb_neq in Hik.
  now rewrite Hik.
}
rewrite determinant_with_row with (i := i) in H1; [ | easy | easy | ]. 2: {
  now rewrite Hira.
}
rewrite <- H1 at 2.
rewrite Hira.
apply rngl_summation_eq_compat.
intros j Hj.
do 2 rewrite <- rngl_mul_assoc.
f_equal; f_equal. {
  rewrite HA; cbn.
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hir ].
  rewrite (List_map_nth' 0); [ | rewrite seq_length, Hc; flia Hj Hir ].
  rewrite seq_nth; [ | flia Hir ].
  rewrite seq_nth; [ | rewrite Hc; flia Hj Hir ].
  rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
  rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
  now rewrite Nat.eqb_refl.
}
(* oops... complicated from now! doing a lemma, perhaps? *)
unfold subm; cbn.
do 2 rewrite map_length.
do 2 rewrite butn_length.
do 2 rewrite fold_mat_nrows.
rewrite Hira.
f_equal; f_equal; f_equal.
rewrite HA; cbn.
destruct M as (ll); cbn in Hir, Hj |-*.
unfold mat_ncols; cbn.
remember (seq 1 (length (hd [] ll))) as x eqn:Hx.
rewrite List_seq_cut with (i := i); [ subst x | apply in_seq; flia Hir ].
rewrite Nat.sub_succ.
do 2 rewrite map_app; cbn.
rewrite Nat.eqb_refl.
erewrite map_ext_in. 2: {
  intros u Hu; apply in_seq in Hu.
  replace (u =? i) with false. 2: {
    symmetry; apply Nat.eqb_neq; flia Hu.
  }
  easy.
}
erewrite map_ext_in with (l := seq (S i) _). 2: {
  intros u Hu; apply in_seq in Hu.
  replace (u =? i) with false. 2: {
    symmetry; apply Nat.eqb_neq; flia Hu.
  }
  easy.
}
rewrite List_map_nth_seq with (la := ll) (d := []) at 1.
rewrite List_seq_cut with (i := i - 1); [ | apply in_seq; flia Hir ].
rewrite <- Nat.sub_succ_l; [ | easy ].
rewrite Nat_sub_succ_1, Nat.add_0_l, Nat.sub_0_r.
do 2 rewrite map_app.
do 3 rewrite butn_app.
do 2 rewrite List_map_seq_length.
rewrite Nat.ltb_irrefl.
rewrite Nat.sub_diag.
rewrite map_length.
replace (0 <? length [i - 1]) with true by easy.
rewrite <- map_butn.
rewrite app_nil_l.
remember (butn 0 _) as x; cbn in Heqx; subst x.
f_equal. {
  rewrite <- (seq_shift (i - 1)), map_map.
  apply map_ext_in.
  intros u Hu; apply in_seq in Hu.
  rewrite Nat_sub_succ_1.
  rewrite List_map_nth_seq with (d := 0%L) (la := nth u ll []).
  apply is_scm_mat_iff in Hsm.
  destruct Hsm as (Hcr, Hcl).
  cbn in Hcl.
  rewrite List_hd_nth_0.
  rewrite Hcl; [ | apply nth_In; flia Hu Hir ].
  rewrite Hcl; [ | apply nth_In; flia Hu Hir ].
  rewrite <- (seq_shift (length ll) 0), map_map.
  apply map_ext_in.
  intros v Hv; apply in_seq in Hv.
  rewrite Nat_sub_succ_1.
  rewrite List_map_nth_seq with (la := nth u ll []) (d := 0%L) at 1.
  f_equal; f_equal; f_equal.
  apply Hcl, nth_In; flia Hu Hir.
} {
  rewrite <- (seq_shift _ i), map_map.
  apply map_ext_in.
  intros u Hu; apply in_seq in Hu.
  rewrite Nat_sub_succ_1.
  rewrite List_map_nth_seq with (d := 0%L) (la := nth u ll []).
  apply is_scm_mat_iff in Hsm.
  destruct Hsm as (Hcr, Hcl).
  cbn in Hcl.
  rewrite List_hd_nth_0.
  rewrite Hcl; [ | apply nth_In; flia Hu ].
  rewrite Hcl; [ | apply nth_In; flia Hu ].
  rewrite <- (seq_shift _ 0), map_map.
  apply map_ext_in.
  intros v Hv; apply in_seq in Hv.
  rewrite Nat_sub_succ_1.
  rewrite List_map_nth_seq with (la := nth u ll []) (d := 0%L) at 1.
  f_equal; f_equal; f_equal.
  apply Hcl, nth_In; flia Hu.
}
Qed.

(* to be completed
Theorem glop_matrix_comatrix_transp_mul :
  ∀ (M : matrix T),
  is_square_matrix M = true
  → (M * (com M)⁺ = det M × mI (mat_nrows M))%M.
Proof.
intros * Hsm.
(*
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
assert (H : rngl_has_opp = true) by now destruct Hif.
specialize (Hos (or_introl H)); clear H.
move Hos before Hif.
*)
destruct M as (ll); cbn - [ det ].
unfold "*"%M, "×"%M, mat_nrows; cbn - [ det ]; f_equal.
rewrite map_map.
rewrite <- (seq_shift (length ll)).
rewrite map_map.
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
assert (Hll : 0 < length ll) by flia Hi.
Check laplace_formula_on_rows.
...
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
rewrite map_map.
rewrite <- seq_shift, map_map.
apply map_ext_in.
intros j Hj; apply in_seq in Hj.
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
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite seq_nth; [ | easy ].
  rewrite (Nat.add_comm 1 (k - 1)).
  rewrite Nat.sub_add; [ | easy ].
  rewrite rngl_mul_assoc.
  easy.
}
cbn - [ det ].
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  (* diagonal *)
  subst j; rewrite δ_diag, rngl_mul_1_r.
  unfold mat_mul_el.
  unfold mat_ncols.
  rewrite Hcl; [ | now apply List_hd_in ].
  apply rngl_summation_eq_compat.
  intros k Hk.
  unfold mat_el.
  rewrite Nat_sub_succ_1.
  rewrite <- rngl_mul_assoc; f_equal.
  cbn - [ det ].
  rewrite List_map_seq_length.
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length.
    unfold mat_ncols; cbn.
    rewrite (List_map_hd 0); [ | now rewrite seq_length ].
    rewrite List_map_seq_length.
    unfold mat_ncols.
    rewrite Hcl; [ flia Hk Hll | ].
    now apply List_hd_in.
  }
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth. 2: {
    rewrite comatrix_ncols.
    unfold mat_ncols; cbn.
    rewrite Hcl; [ flia Hk Hll | ].
    now apply List_hd_in.
  }
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length, seq_nth; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  rewrite Nat.add_comm, Nat.add_sub.
  rewrite (List_map_nth' 0). 2: {
    unfold mat_ncols.
    rewrite seq_length; cbn.
    rewrite Hcl; [ flia Hk Hll | ].
    now apply List_hd_in.
  }
  rewrite seq_nth. 2: {
    rewrite seq_nth; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  rewrite seq_nth; [ | easy ].
  rewrite seq_nth. 2: {
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
      rewrite seq_length, comatrix_ncols.
      unfold mat_ncols.
      rewrite Hcl; [ flia Hk Hi | ].
      now apply List_hd_in.
    }
    do 2 rewrite Nat.sub_0_r.
    rewrite (List_map_nth' 0). 2: {
      now rewrite comatrix_nrows, seq_length.
    }
    rewrite seq_nth; [ | now rewrite comatrix_nrows ].
    rewrite seq_nth. 2: {
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
    rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
    rewrite (List_map_nth' 0). 2: {
      rewrite seq_length; unfold mat_ncols.
      rewrite Hcl; [ flia Hk Hll | ].
      now apply List_hd_in.
    }
    rewrite seq_nth; [ | easy ].
    rewrite seq_nth. 2: {
      unfold mat_ncols.
      rewrite Hcl; [ flia Hk Hll | ].
      now apply List_hd_in.
    }
    cbn - [ det ].
    rewrite rngl_mul_comm; [ | now destruct Hif ].
    rewrite rngl_mul_mul_swap; [ | now destruct Hif ].
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
  specialize (determinant_with_bad_row Hif) as H1.
  specialize (H1 (S j) (S i) M).
  apply H1; [ | flia Hj | flia Hi | flia Hij ].
  apply is_scm_mat_iff; cbn.
  split; [ easy | ].
  intros l Hl; rewrite HM in Hl; cbn in Hl.
  now apply Hcl.
}
Qed.
*)

Theorem matrix_comatrix_transp_mul : in_charac_0_field →
  ∀ (M : matrix T),
  is_square_matrix M = true
  → (M * (com M)⁺ = det M × mI (mat_nrows M))%M.
Proof.
intros Hif * Hsm.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
assert (H : rngl_has_opp = true) by now destruct Hif.
specialize (Hos (or_introl H)); clear H.
move Hos before Hif.
destruct M as (ll); cbn - [ det ].
unfold "*"%M, "×"%M, mat_nrows; cbn - [ det ]; f_equal.
rewrite map_map.
rewrite <- (seq_shift (length ll)).
rewrite map_map.
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
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
rewrite map_map.
rewrite <- seq_shift, map_map.
apply map_ext_in.
intros j Hj; apply in_seq in Hj.
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
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite seq_nth; [ | easy ].
  rewrite (Nat.add_comm 1 (k - 1)).
  rewrite Nat.sub_add; [ | easy ].
  rewrite rngl_mul_assoc.
  easy.
}
cbn - [ det ].
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  (* diagonal *)
  subst j; rewrite δ_diag, rngl_mul_1_r.
  unfold mat_mul_el.
  unfold mat_ncols.
  rewrite Hcl; [ | now apply List_hd_in ].
  apply rngl_summation_eq_compat.
  intros k Hk.
  unfold mat_el.
  rewrite Nat_sub_succ_1.
  rewrite <- rngl_mul_assoc; f_equal.
  cbn - [ det ].
  rewrite List_map_seq_length.
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length.
    unfold mat_ncols; cbn.
    rewrite (List_map_hd 0); [ | now rewrite seq_length ].
    rewrite List_map_seq_length.
    unfold mat_ncols.
    rewrite Hcl; [ flia Hk Hll | ].
    now apply List_hd_in.
  }
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth. 2: {
    rewrite comatrix_ncols.
    unfold mat_ncols; cbn.
    rewrite Hcl; [ flia Hk Hll | ].
    now apply List_hd_in.
  }
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length, seq_nth; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  rewrite Nat.add_comm, Nat.add_sub.
  rewrite (List_map_nth' 0). 2: {
    unfold mat_ncols.
    rewrite seq_length; cbn.
    rewrite Hcl; [ flia Hk Hll | ].
    now apply List_hd_in.
  }
  rewrite seq_nth. 2: {
    rewrite seq_nth; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  rewrite seq_nth; [ | easy ].
  rewrite seq_nth. 2: {
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
      rewrite seq_length, comatrix_ncols.
      unfold mat_ncols.
      rewrite Hcl; [ flia Hk Hi | ].
      now apply List_hd_in.
    }
    do 2 rewrite Nat.sub_0_r.
    rewrite (List_map_nth' 0). 2: {
      now rewrite comatrix_nrows, seq_length.
    }
    rewrite seq_nth; [ | now rewrite comatrix_nrows ].
    rewrite seq_nth. 2: {
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
    rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
    rewrite (List_map_nth' 0). 2: {
      rewrite seq_length; unfold mat_ncols.
      rewrite Hcl; [ flia Hk Hll | ].
      now apply List_hd_in.
    }
    rewrite seq_nth; [ | easy ].
    rewrite seq_nth. 2: {
      unfold mat_ncols.
      rewrite Hcl; [ flia Hk Hll | ].
      now apply List_hd_in.
    }
    cbn - [ det ].
    rewrite rngl_mul_comm; [ | now destruct Hif ].
    rewrite rngl_mul_mul_swap; [ | now destruct Hif ].
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
  specialize (determinant_with_bad_row Hif) as H1.
  specialize (H1 (S j) (S i) M).
  apply H1; [ | flia Hj | flia Hi | flia Hij ].
  apply is_scm_mat_iff; cbn.
  split; [ easy | ].
  intros l Hl; rewrite HM in Hl; cbn in Hl.
  now apply Hcl.
}
Qed.

Theorem comatrix_transp_matrix_mul : in_charac_0_field →
  ∀ (M : matrix T),
  is_square_matrix M = true
  → ((com M)⁺ * M = det M × mI (mat_nrows M))%M.
Proof.
intros Hif * Hsm.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
assert (H : rngl_has_opp = true) by now destruct Hif.
specialize (Hos (or_introl H)); clear H.
move Hos before Hif.
destruct M as (ll); cbn - [ det ].
destruct (Nat.eq_dec (length ll) 0) as [Hlz| Hlz]. {
  apply length_zero_iff_nil in Hlz; subst ll; cbn.
  unfold "*"%M, mI; cbn; symmetry.
  apply mat_mul_scal_1_l.
}
apply Nat.neq_0_lt_0 in Hlz.
destruct (Nat.eq_dec (length ll) 1) as [Hl1| Hl1]. {
  destruct ll as [| l]; [ easy | ].
  destruct ll; [ clear Hl1 | easy ].
  apply is_scm_mat_iff in Hsm.
  unfold mat_ncols in Hsm; cbn - [ In ] in Hsm.
  destruct Hsm as (_, Hcl).
  unfold "*"%M, "×"%M, mat_transp, mat_mul_el, com; cbn.
  rewrite Hcl; [ cbn | now left ].
  do 2 rewrite rngl_summation_only_one; cbn.
  do 2 rewrite rngl_mul_1_l.
  now do 2 rewrite rngl_mul_1_r.
}
unfold "*"%M, "×"%M, mat_nrows; cbn - [ det ]; f_equal.
rewrite map_map.
rewrite List_map_seq_length.
rewrite comatrix_ncols.
generalize Hsm; intros Hsm_v.
apply is_scm_mat_iff in Hsm.
cbn in Hsm.
destruct Hsm as (Hcr, Hcl).
unfold mat_ncols at 2.
rewrite Hcl; [ | now apply List_hd_in ].
rewrite <- (seq_shift (length ll)), map_map.
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
unfold mat_ncols.
rewrite Hcl; [ | now apply List_hd_in ].
rewrite map_map.
rewrite <- seq_shift, map_map.
apply map_ext_in.
intros j Hj; apply in_seq in Hj.
move j before i.
rewrite laplace_formula_on_cols with (j := S j); [ | easy | easy | ]. 2: {
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
  subst j; rewrite δ_diag, rngl_mul_1_r.
  erewrite rngl_summation_eq_compat. 2: {
    intros k Hk.
    rewrite rngl_mul_comm; [ | now destruct Hif ].
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
      rewrite seq_length, comatrix_ncols.
      unfold mat_ncols.
      rewrite Hcl; [ flia Hk Hi | ].
      now apply List_hd_in.
    }
    rewrite (List_map_nth' 0). 2: {
      rewrite seq_length, comatrix_nrows; cbn.
      flia Hk Hlz.
    }
    rewrite seq_nth; [ | rewrite comatrix_nrows; cbn; flia Hk Hlz ].
    rewrite seq_nth. 2: {
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
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hk Hlz ].
    rewrite (List_map_nth' 0). 2: {
      rewrite seq_length; unfold mat_ncols.
      rewrite Hcl; [ easy | ].
      now apply List_hd_in.
    }
    rewrite seq_nth; [ | flia Hk Hlz ].
    rewrite (Nat.add_comm 1 (k - 1)), Nat.sub_add; [ | easy ].
    rewrite seq_nth. 2: {
      unfold mat_ncols.
      rewrite Hcl; [ easy | ].
      now apply List_hd_in.
    }
    cbn - [ det ].
    rewrite rngl_mul_mul_swap; [ | now destruct Hif ].
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
  specialize (determinant_with_bad_row Hif) as H1.
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
    rewrite <- determinant_transpose; [ | easy | ]. 2: {
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

Theorem mat_mul_inv_r : in_charac_0_field →
  ∀ (M : matrix T),
  is_square_matrix M = true
  → det M ≠ 0%L
  → (M * mat_inv M = mI (mat_nrows M))%M.
Proof.
intros Hif * Hsm Hdz.
destruct (Nat.eq_dec (mat_nrows M) 0) as [Hrz| Hrz]. {
  rewrite Hrz; cbn.
  unfold mat_nrows in Hrz.
  apply length_zero_iff_nil in Hrz.
  now destruct M as (ll); cbn in Hrz; subst ll.
}
unfold mat_inv.
rewrite mat_mul_mul_scal_l; cycle 1. {
  now destruct Hif.
} {
  now destruct Hif.
} {
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
rewrite matrix_comatrix_transp_mul; [ | easy | easy ].
rewrite mat_mul_scal_l_mul_assoc.
rewrite rngl_mul_inv_l; [ | now destruct Hif | now destruct Hif ].
now apply mat_mul_scal_1_l.
Qed.

Theorem mat_mul_inv_l : in_charac_0_field →
  ∀ (M : matrix T),
  is_square_matrix M = true
  → det M ≠ 0%L
  → (mat_inv M * M = mI (mat_nrows M))%M.
Proof.
intros Hif * Hsm Hdz.
unfold mat_inv.
rewrite mat_mul_scal_l_mul; [ | now destruct Hif | ]. 2: {
  apply squ_mat_is_corr.
  apply mat_transp_is_square.
  now apply comatrix_is_square.
}
rewrite comatrix_transp_matrix_mul; [ | easy | easy ].
rewrite mat_mul_scal_l_mul_assoc.
rewrite rngl_mul_inv_l; [ | now destruct Hif | easy ].
now apply mat_mul_scal_1_l.
Qed.

Notation "A ⁻¹" := (mat_inv A) (at level 1, format "A ⁻¹") : M_scope.

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

(* to be completed
Theorem glop_mat_inv_det_comm :
  ∀ M,
  is_square_matrix M = true
  → det M ≠ 0%L
  → (det M × M⁻¹ = (com M)⁺)%M.
Proof.
intros * Hsm Hmz.
Check matrix_comatrix_transp_mul.
...
specialize (matrix_comatrix_transp_mul Hif M Hsm) as H1.
specialize (mat_mul_inv_l Hif M Hsm Hmz) as H3.
apply (f_equal (mat_mul M⁻¹)) in H1.
destruct (Nat.eq_dec (mat_nrows M) 0) as [Hrz| Hrz]. {
  destruct M as (ll).
  cbn in Hrz.
  apply length_zero_iff_nil in Hrz; subst ll.
  cbn.
  unfold mat_transp, mat_inv, com; cbn.
  unfold mat_transp; cbn.
  rewrite rngl_inv_1; [ | now destruct Hif | ]. 2: {
    destruct Hif as (Hic, Hop, Hin, Hit, Hde, Hch).
    now rewrite Hch.
  }
  rewrite rngl_div_1_r; cycle 1. {
    destruct Hif as (Hic, Hop, Hin, Hit, Hde, Hch).
    now apply rngl_has_inv_or_quot_iff; left.
  } {
    destruct Hif as (Hic, Hop, Hin, Hit, Hde, Hch).
    now rewrite Hch.
  }
  easy.
}
assert (Hcz : mat_ncols M ≠ 0). {
  now rewrite (squ_mat_ncols _ Hsm).
}
rewrite mat_mul_assoc in H1; [ | now destruct Hif | easy | easy | ]. 2: {
  rewrite mat_inv_ncols.
  rewrite if_eqb_eq_dec.
  now destruct (Nat.eq_dec _ _).
}
rewrite H3 in H1.
rewrite mat_mul_1_l in H1; [ | now destruct Hif | | ]; cycle 1. {
  apply mat_transp_is_corr.
  apply comatrix_is_correct.
  now apply squ_mat_is_corr.
} {
  rewrite mat_transp_nrows.
  rewrite comatrix_ncols.
  symmetry; apply (squ_mat_ncols _ Hsm).
}
rewrite mat_mul_mul_scal_l in H1; cycle 1. {
  now destruct Hif.
} {
  now destruct Hif.
} {
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
rewrite mat_mul_1_r in H1; [ | now destruct Hif | | ]; cycle 1. {
  apply mat_inv_is_corr.
  now apply squ_mat_is_corr.
} {
  rewrite mat_inv_ncols.
  rewrite if_eqb_eq_dec.
  now destruct (Nat.eq_dec _ _).
}
rewrite H1.
rewrite mat_mul_scal_l_mul_assoc.
rewrite rngl_div_1_l; [ | now destruct Hif ].
rewrite rngl_mul_inv_l; [ | now destruct Hif | easy ].
symmetry; apply mat_mul_scal_1_l.
Qed.
*)

Theorem mat_inv_det_comm : in_charac_0_field →
  ∀ M,
  is_square_matrix M = true
  → det M ≠ 0%L
  → (M⁻¹ = (1%L / det M) × (com M)⁺)%M.
Proof.
intros Hif * Hsm Hmz.
specialize (matrix_comatrix_transp_mul Hif M Hsm) as H1.
specialize (mat_mul_inv_l Hif M Hsm Hmz) as H3.
apply (f_equal (mat_mul M⁻¹)) in H1.
destruct (Nat.eq_dec (mat_nrows M) 0) as [Hrz| Hrz]. {
  destruct M as (ll).
  cbn in Hrz.
  apply length_zero_iff_nil in Hrz; subst ll.
  cbn.
  unfold mat_transp, mat_inv, com; cbn.
  unfold mat_transp; cbn.
  rewrite rngl_inv_1; [ | now destruct Hif | ]. 2: {
    destruct Hif as (Hic, Hop, Hin, Hit, Hde, Hch).
    now rewrite Hch.
  }
  rewrite rngl_div_1_r; cycle 1. {
    destruct Hif as (Hic, Hop, Hin, Hit, Hde, Hch).
    now apply rngl_has_inv_or_quot_iff; left.
  } {
    destruct Hif as (Hic, Hop, Hin, Hit, Hde, Hch).
    now rewrite Hch.
  }
  easy.
}
assert (Hcz : mat_ncols M ≠ 0). {
  now rewrite (squ_mat_ncols _ Hsm).
}
rewrite mat_mul_assoc in H1; [ | now destruct Hif | easy | easy | ]. 2: {
  rewrite mat_inv_ncols.
  rewrite if_eqb_eq_dec.
  now destruct (Nat.eq_dec _ _).
}
rewrite H3 in H1.
rewrite mat_mul_1_l in H1; [ | now destruct Hif | | ]; cycle 1. {
  apply mat_transp_is_corr.
  apply comatrix_is_correct.
  now apply squ_mat_is_corr.
} {
  rewrite mat_transp_nrows.
  rewrite comatrix_ncols.
  symmetry; apply (squ_mat_ncols _ Hsm).
}
rewrite mat_mul_mul_scal_l in H1; cycle 1. {
  now destruct Hif.
} {
  now destruct Hif.
} {
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
rewrite mat_mul_1_r in H1; [ | now destruct Hif | | ]; cycle 1. {
  apply mat_inv_is_corr.
  now apply squ_mat_is_corr.
} {
  rewrite mat_inv_ncols.
  rewrite if_eqb_eq_dec.
  now destruct (Nat.eq_dec _ _).
}
rewrite H1.
rewrite mat_mul_scal_l_mul_assoc.
rewrite rngl_div_1_l; [ | now destruct Hif ].
rewrite rngl_mul_inv_l; [ | now destruct Hif | easy ].
symmetry; apply mat_mul_scal_1_l.
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
now rewrite map_length.
Qed.

(*
Theorem firstn_map2 : ∀ A B C (f : A → B → C) la lb i,
  firstn i (map2 f la lb) = map2 f (firstn i la) (firstn i lb).
Proof.
intros.
revert i lb.
induction la as [| a]; intros; cbn. {
  now do 2 rewrite firstn_nil.
}
destruct lb as [| b]. {
  do 2 rewrite firstn_nil.
  now rewrite map2_nil_r.
}
destruct i; [ easy | cbn; f_equal ].
apply IHla.
Qed.
*)

Theorem butn_map2 : ∀ A B C (f : A → B → C) la lb i,
  butn i (map2 f la lb) = map2 f (butn i la) (butn i lb).
Proof.
intros.
revert i lb.
induction la as [| a]; intros; cbn. {
  now do 2 rewrite butn_nil.
}
destruct lb as [| b]. {
  do 2 rewrite butn_nil.
  now rewrite map2_nil_r.
}
destruct i; [ easy | cbn; f_equal ].
apply IHla.
Qed.

Theorem det_mat_repl_vect : in_charac_0_field →
  ∀ M V,
  is_square_matrix M = true
  → vect_size V = mat_nrows M
  → ∀ k, 1 ≤ k ≤ mat_ncols M
  → det (mat_repl_vect k M V) = vect_el ((com M)⁺ • V) k.
Proof.
intros Hif * Hsm Hvm * Hk.
specialize (squ_mat_is_corr _ Hsm) as Hcm.
move Hcm before Hsm.
assert (Hk' : k - 1 < mat_ncols M) by flia Hk.
rewrite laplace_formula_on_cols with (j := k); [ | easy | | ]; cycle 1. {
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
rewrite (List_map_nth' []); [ | now rewrite List_map_seq_length ].
unfold vect_dot_mul.
cbn - [ mat_el com ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite map2_map_l.
rewrite map2_map2_seq_l with (d := 0).
rewrite map2_map2_seq_r with (d := 0%L).
rewrite seq_length.
rewrite fold_vect_size, Hvm.
rewrite comatrix_nrows.
rewrite map2_diag.
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
rewrite rngl_mul_comm; [ | now destruct Hif ].
f_equal.
unfold com.
cbn - [ det ].
rewrite seq_nth; [ | easy ].
rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
rewrite (seq_nth _ _ Hi').
rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite (seq_nth _ _ Hi').
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite (seq_nth _ _ Hk').
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length, map2_length.
  rewrite fold_mat_nrows, fold_vect_size, Hvm.
  now rewrite Nat.min_id.
}
rewrite seq_nth. 2: {
  rewrite map2_length.
  rewrite fold_mat_nrows, fold_vect_size, Hvm.
  now rewrite Nat.min_id.
}
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length, mat_repl_vect_ncols; [ easy | easy | ].
  now rewrite (squ_mat_ncols _ Hsm).
}
rewrite seq_nth. 2: {
  rewrite mat_repl_vect_ncols; [ easy | easy | ].
  now rewrite (squ_mat_ncols _ Hsm).
}
f_equal.
rewrite (Nat.add_comm _ (i - 1)), Nat.sub_add; [ | easy ].
rewrite (Nat.add_comm _ (k - 1)), Nat.sub_add; [ | easy ].
unfold mat_repl_vect.
unfold subm.
cbn - [ det ].
rewrite map_butn.
rewrite map_butn.
rewrite map_map2.
rewrite map2_map2_seq_l with (d := []).
rewrite map2_map2_seq_r with (d := 0%L).
rewrite fold_mat_nrows.
rewrite fold_vect_size.
rewrite Hvm.
rewrite map2_diag.
symmetry.
erewrite map_ext_in. 2: {
  intros j Hj.
  apply in_seq in Hj.
  unfold replace_at.
  rewrite butn_app.
  rewrite firstn_length.
  rewrite fold_corr_mat_ncols; [ | easy | easy ].
  rewrite min_l; [ | flia Hk ].
  rewrite Nat.ltb_irrefl.
  rewrite Nat.sub_diag.
  rewrite butn_0_cons.
  now rewrite fold_butn.
}
now rewrite <- List_map_map_seq.
Qed.

(* Cramer's rule *)

(* to be completed
Theorem glop_cramer's_rule :
  ∀ (M : matrix T) (U V : vector T),
  is_square_matrix M = true
  → vect_size U = mat_nrows M
 → det M ≠ 0%L
  → (M • U)%V = V
  → ∀ i,
  1 ≤ i ≤ mat_nrows M
  → (vect_el U i * det M)%L = det (mat_repl_vect i M V).
Proof.
intros * Hsm Hum Hmz Hmuv k Hk.
assert (Huv : vect_size V = vect_size U). {
  rewrite <- Hmuv; cbn.
  now rewrite map_length.
}
Check mat_inv_det_comm.
...
specialize (mat_inv_det_comm Hif M Hsm Hmz) as H1.
apply (f_equal (mat_mul_vect_r (M⁻¹)%M)) in Hmuv.
rewrite mat_vect_mul_assoc in  Hmuv; cycle 1. {
  now destruct Hif.
} {
  apply mat_inv_is_corr.
  now apply squ_mat_is_corr.
} {
  now apply squ_mat_is_corr.
} {
  rewrite mat_inv_ncols.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec _ _) as [Hcz| Hcz]; [ | easy ].
  now rewrite squ_mat_ncols in Hcz.
} {
  now rewrite squ_mat_ncols.
}
rewrite mat_mul_inv_l in Hmuv; [ | easy | easy | easy ].
rewrite mat_vect_mul_1_l in Hmuv; [ | now destruct Hif | easy ].
rewrite H1 in Hmuv.
rewrite <- mat_mul_scal_vect_assoc in Hmuv; cycle 1. {
  now destruct Hif.
} {
  apply mat_transp_is_corr.
  apply comatrix_is_correct.
  now apply squ_mat_is_corr.
} {
  rewrite mat_transp_ncols.
  rewrite comatrix_ncols, comatrix_nrows.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec _ _) as [Hcz| Hcz]. {
    rewrite (squ_mat_ncols _ Hsm) in Hcz.
    now rewrite Huv, Hum.
  } {
    now rewrite Huv.
  }
}
rewrite Hmuv.
rewrite vect_el_mul_scal_l. 2: {
  split; [ easy | ].
  rewrite vect_size_mat_mul_vect_r.
  rewrite mat_transp_nrows.
  rewrite comatrix_ncols.
  now rewrite (squ_mat_ncols _ Hsm).
}
rewrite rngl_mul_comm; [ | now destruct Hif ].
rewrite rngl_div_1_l; [ | now destruct Hif ].
unfold rngl_div.
rewrite (cf_has_inv Hif); f_equal.
symmetry.
rewrite <- (squ_mat_ncols _ Hsm) in Hk.
apply (det_mat_repl_vect Hif); [ easy | congruence | easy ].
Qed.
...
*)

Theorem cramer's_rule : in_charac_0_field →
  ∀ (M : matrix T) (U V : vector T),
  is_square_matrix M = true
  → vect_size U = mat_nrows M
 → det M ≠ 0%L
  → (M • U)%V = V
  → ∀ i,
  1 ≤ i ≤ mat_nrows M
  → vect_el U i = (det (mat_repl_vect i M V) / det M)%L.
Proof.
intros Hif * Hsm Hum Hmz Hmuv k Hk.
assert (Huv : vect_size V = vect_size U). {
  rewrite <- Hmuv; cbn.
  now rewrite map_length.
}
specialize (mat_inv_det_comm Hif M Hsm Hmz) as H1.
apply (f_equal (mat_mul_vect_r (M⁻¹)%M)) in Hmuv.
rewrite mat_vect_mul_assoc in  Hmuv; cycle 1. {
  now destruct Hif.
} {
  apply mat_inv_is_corr.
  now apply squ_mat_is_corr.
} {
  now apply squ_mat_is_corr.
} {
  rewrite mat_inv_ncols.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec _ _) as [Hcz| Hcz]; [ | easy ].
  now rewrite squ_mat_ncols in Hcz.
} {
  now rewrite squ_mat_ncols.
}
rewrite mat_mul_inv_l in Hmuv; [ | easy | easy | easy ].
rewrite mat_vect_mul_1_l in Hmuv; [ | now destruct Hif | easy ].
rewrite H1 in Hmuv.
rewrite <- mat_mul_scal_vect_assoc in Hmuv; cycle 1. {
  now destruct Hif.
} {
  apply mat_transp_is_corr.
  apply comatrix_is_correct.
  now apply squ_mat_is_corr.
} {
  rewrite mat_transp_ncols.
  rewrite comatrix_ncols, comatrix_nrows.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec _ _) as [Hcz| Hcz]. {
    rewrite (squ_mat_ncols _ Hsm) in Hcz.
    now rewrite Huv, Hum.
  } {
    now rewrite Huv.
  }
}
rewrite Hmuv.
rewrite vect_el_mul_scal_l. 2: {
  split; [ easy | ].
  rewrite vect_size_mat_mul_vect_r.
  rewrite mat_transp_nrows.
  rewrite comatrix_ncols.
  now rewrite (squ_mat_ncols _ Hsm).
}
rewrite rngl_mul_comm; [ | now destruct Hif ].
rewrite rngl_div_1_l; [ | now destruct Hif ].
unfold rngl_div.
rewrite (cf_has_inv Hif); f_equal.
symmetry.
rewrite <- (squ_mat_ncols _ Hsm) in Hk.
apply (det_mat_repl_vect Hif); [ easy | congruence | easy ].
Qed.

(* *)

Theorem minus_one_pow_mul_same :
  rngl_has_opp = true →
  ∀ i, (minus_one_pow i * minus_one_pow i = 1)%L.
Proof.
intros Hop *.
unfold minus_one_pow.
destruct (i mod 2); [ apply rngl_mul_1_l | ].
now apply rngl_squ_opp_1.
Qed.

End a.

Arguments com {T}%type {ro} M%M.
Arguments cramer's_rule {T ro rp} _ [M%M U%V V%V] _ _ _ _ [i]%nat _.
Arguments laplace_formula_on_cols {T}%type {ro rp} Hif M%M [j]%nat.
Arguments laplace_formula_on_rows {T}%type {ro rp} Hif M%M [i]%nat.
Arguments mat_inv {T}%type {ro} M%M.
Arguments mat_mul_inv_r {T}%type {ro rp} Hof M%L.

Notation "A ⁻¹" := (mat_inv A) (at level 1, format "A ⁻¹") : M_scope.

(* tests
Require Import RnglAlg.Qrl.
Require Import RnglAlg.Rational.
Import Q.Notations.
Open Scope Q_scope.
Compute 3.
Compute (let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1];[18;3;2;1]] in (det M, mat_inv M)).
Compute (let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1];[18;3;2;1]] in (M * mat_inv M)%M).
Compute (let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1];[18;3;2;1]] in (mat_inv M * M)%M).
Compute (let M := mk_mat [[3;0;0;1];[0;0;2;7];[1;0;1;1];[18;0;2;1]] in (det M, com M)).
Compute (let M := mk_mat [[3;0;0;1];[0;0;2;7];[1;0;1;1];[18;0;2;1]] in (det M, (M * com M)%M, (com M * M)%M)).
*)
