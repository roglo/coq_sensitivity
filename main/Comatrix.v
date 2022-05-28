(* comatrices *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Misc RingLike IterAdd IterMul Pigeonhole.
Require Import PermutationFun SortingFun Matrix PermutSeq Signature.
Require Import Determinant.
Import matrix_Notations.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

Definition com (M : matrix T) : matrix T :=
  mk_mat
    (map
      (λ i,
       map (λ j, (minus_one_pow (i + j) * det (subm i j M))%F)
         (seq 0 (mat_ncols M)))
      (seq 0 (mat_nrows M))).

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
unfold transposition.
do 2 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec j i) as [Hji| Hji]. {
  subst j.
  now apply nth_indep.
}
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
  p < q
  → q < r
  → subm r j (mat_swap_rows p q M) = mat_swap_rows p q (subm r j M).
Proof.
intros * Hpq Hq.
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
destruct (le_dec r i) as [Hir| Hir]. 2: {
  apply Nat.nle_gt in Hir.
  rewrite Nat.add_0_r.
  destruct (Nat.eq_dec i p) as [Hip| Hip]. {
    subst i; clear Hir.
    rewrite transposition_1.
    destruct (lt_dec q (length (butn r ll))) as [Hqrl| Hqrl]. {
      rewrite (List_map_nth' []); [ | easy ].
      now rewrite nth_butn_after.
    }
    apply Nat.nlt_ge in Hqrl.
    symmetry.
    rewrite nth_overflow; [ | now rewrite map_length ].
    rewrite butn_length in Hqrl.
    destruct (le_dec (length ll) q) as [Hlq| Hlq]. {
      rewrite nth_overflow with (n := q); [ | easy ].
      now rewrite butn_nil.
    }
    apply Nat.nle_gt in Hlq.
    unfold Nat.b2n in Hi, Hqrl.
    rewrite if_ltb_lt_dec in Hi, Hqrl.
    destruct (lt_dec r (length ll)) as [Hrl| Hrl]; [ | flia Hqrl Hlq ].
    flia Hq Hrl Hqrl Hlq.
  }
  destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
    subst i; clear Hir.
    rewrite transposition_2.
    destruct (lt_dec p (length (butn r ll))) as [Hprl| Hprl]. {
      rewrite (List_map_nth' []); [ | easy ].
      rewrite nth_butn_after; [ easy | flia Hpq Hq ].
    }
    apply Nat.nlt_ge in Hprl.
    rewrite butn_length in Hprl.
    flia Hpq Hi Hprl.
  }
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec i p) as [H| H]; [ easy | clear H ].
  destruct (Nat.eq_dec i q) as [H| H]; [ easy | clear H ].
  rewrite map_butn.
  rewrite nth_butn_after; [ | easy ].
  rewrite (List_map_nth' []); [ easy | flia Hi ].
}
unfold transposition.
do 4 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec i p) as [H| H]; [ flia Hpq Hq Hir H | clear H ].
destruct (Nat.eq_dec i q) as [H| H]; [ flia Hq Hir H | clear H ].
destruct (Nat.eq_dec (i + 1) p) as [H| H]; [ flia Hpq Hq Hir H | clear H ].
destruct (Nat.eq_dec (i + 1) q) as [H| H]; [ flia Hq Hir H | clear H ].
rewrite map_butn.
rewrite nth_butn_before; [ | easy ].
rewrite (List_map_nth' []); [ easy | ].
unfold Nat.b2n in Hi.
rewrite if_ltb_lt_dec in Hi.
destruct (lt_dec r (length ll)) as [Hrl| Hrl]; [ flia Hi Hir | ].
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
  q < mat_nrows M
  → mat_el' (mat_swap_rows p q M) (S q) j = mat_el' M (S p) j.
Proof.
intros * Hql; cbn.
destruct M as (ll); cbn in Hql |-*.
f_equal; clear j.
rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hql ].
rewrite seq_nth; [ | flia Hql ].
rewrite Nat.add_0_l.
do 2 rewrite Nat.sub_0_r.
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
  p < mat_nrows M
  → subm 0 q (mat_swap_rows 0 p M) =
    subm p q
      (fold_left (λ M' k, mat_swap_rows k (k + 1) M') (seq 0 (p - 1)) M).
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
destruct (lt_dec p (length ll)) as [H| H]; [ clear H | flia H Hp ].
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
destruct (le_dec p i) as [Hpi| Hpi]. 2: {
  apply Nat.nle_gt in Hpi.
  rewrite nth_butn_after; [ | easy ].
  rewrite nth_fold_left_map_transp; cbn.
  rewrite Nat.sub_0_r.
  destruct (le_dec (length ll) i) as [H| H]; [ flia Hi H | clear H ].
  destruct (Nat.eq_dec i (p - 1)) as [Hip1| Hip1]. {
    rewrite Hip1, Nat.sub_add; [ | flia Hpi ].
    now rewrite transposition_2.
  }
  destruct (le_dec (length ll) 0) as [H| H]; [ flia Hp H | clear H ].
  destruct (le_dec (length ll) (p - 1)) as [H| H]; [ flia Hp H | clear H ].
  unfold transposition.
  unfold Nat.b2n.
  do 2 rewrite if_eqb_eq_dec.
  rewrite if_leb_le_dec.
  rewrite Nat.add_1_r.
  destruct (Nat.eq_dec (S i) 0) as [H| H]; [ easy | clear H ].
  destruct (Nat.eq_dec (S i) p) as [H| H]; [ flia Hip1 H | clear H ].
  destruct (le_dec i (p - 1)) as [H| H]; [ | flia Hpi H ].
  now rewrite Nat.add_1_r.
}
rewrite transposition_out; [ | flia | flia Hpi ].
rewrite nth_butn_before; [ | easy ].
symmetry.
rewrite nth_fold_left_map_transp; cbn; rewrite Nat.sub_0_r.
destruct (le_dec (length ll) (i + 1)) as [H| H]; [ flia Hi H | clear H ].
destruct (Nat.eq_dec (i + 1) (p - 1)) as [H| H]; [ flia Hpi H | clear H ].
destruct (le_dec (length ll) 0) as [H| H]; [ flia Hp H | clear H ].
destruct (le_dec (length ll) (p - 1)) as [H| H]; [ flia Hp H | clear H ].
unfold Nat.b2n.
rewrite if_leb_le_dec.
destruct (le_dec (i + 1) (p - 1)) as [H| H]; [ flia Hpi H | clear H ].
now rewrite Nat.add_0_r.
Qed.

Theorem subm_fold_left_lt : ∀ (M : matrix T) i j m,
  m < i
  → subm i j
      (fold_left (λ M' k, mat_swap_rows k (k + 1) M')
         (seq 0 m) M) =
    fold_left
      (λ M' k, mat_swap_rows k (k + 1) M')
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
  → det (fold_left (λ M' k, mat_swap_rows k (k + 1) M') (seq 0 i) M) =
    (minus_one_pow i * det M)%F.
Proof.
intros (Hic & Hop & Hiv & H10 & Hit & Hde & Hch) * Hin Hsm.
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
  now rewrite mat_nrows_fold_left_swap, Hr, Nat.add_1_r.
} {
  specialize (square_matrix_ncols _ Hsm) as Hc1.
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
  → 0 < i < mat_nrows M
  → j < mat_nrows M
  → det (subm 0 j (mat_swap_rows 0 i M)) =
    (- minus_one_pow i * det (subm i j M))%F.
Proof.
intros (Hic & Hop & Hiv & H10 & Hit & Hde & Hch) * Hsm (Hiz, Hin) Hjn.
rewrite subm_mat_swap_rows_circ; [ | easy ].
destruct i; [ flia Hiz | ].
rewrite minus_one_pow_succ; [ | easy ].
rewrite rngl_opp_involutive; [ | easy ].
rewrite Nat_sub_succ_1.
rewrite subm_fold_left_lt; [ | flia ].
apply determinant_circular_shift_rows; [ easy | | ]. {
  rewrite mat_nrows_subm.
  apply Nat.ltb_lt in Hin; rewrite Hin; cbn.
  apply Nat.ltb_lt in Hin; flia Hin.
}
apply is_squ_mat_subm; [ flia Hin | flia Hjn | easy ].
Qed.

(* Laplace formulas *)

Theorem laplace_formula_on_rows : in_charac_0_field →
  ∀ (M : matrix T) i,
  is_square_matrix M = true
  → 1 ≤ i ≤ mat_nrows M
  → det M = ∑ (j = 1, mat_ncols M), mat_el' M i j * mat_el' (com M) i j.
Proof.
intros Hif * Hsm Hlin.
specialize (square_matrix_ncols M Hsm) as Hc.
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
  destruct Hif as (Hic & Hop & Hin & H10 & Hit & Hde & Hch).
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_mul_swap; [ | easy ].
  rewrite (List_map_nth' 0); [ | rewrite seq_length, Hc; flia Hj Hnz ].
  rewrite seq_nth; [ | rewrite Hc; flia Hj Hnz ].
  rewrite map_length.
  cbn - [ butn ].
  f_equal; f_equal. {
    destruct j; [ easy | ].
    rewrite Nat_sub_succ_1.
    rewrite minus_one_pow_succ; [ | easy ].
    rewrite minus_one_pow_succ; [ | easy ].
    now symmetry; apply rngl_opp_involutive.
  }
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
  destruct Hif as (Hic & Hop & Hin & H10 & Hit & Hde & Hch) in Hj.
  cbn.
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hlin ].
  rewrite (List_map_nth' 0); [ | rewrite seq_length, Hc; flia Hj Hnz ].
  rewrite seq_nth; [ | flia Hlin ].
  rewrite seq_nth; [ | flia Hj Hc Hnz ].
  do 2 rewrite Nat.add_0_l.
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_mul_swap; [ | easy ].
  easy.
}
cbn.
rename i into p.
remember (mat_swap_rows 0 (p - 1) M) as M'.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite map_length, butn_length, fold_mat_nrows.
  rewrite rngl_mul_mul_swap; [ | now destruct Hif ].
  rewrite Nat.add_comm.
  rewrite minus_one_pow_add_r; [ | now destruct Hif ].
  do 2 rewrite <- rngl_mul_assoc.
  rewrite rngl_mul_comm; [ | now destruct Hif ].
  rewrite rngl_mul_assoc.
  remember (minus_one_pow (p - 1) * _)%F as x eqn:Hx.
  rewrite <- rngl_opp_involutive in Hx; [ | now destruct Hif ].
  rewrite <- rngl_mul_opp_l in Hx; [ | now destruct Hif ].
  specialize determinant_subm_mat_swap_rows_0_i as H1.
  specialize (H1 Hif).
  specialize (H1 M (p - 1) (j - 1) Hsm).
  cbn - [ butn ] in H1.
  rewrite map_length, map_butn, butn_length in H1.
  rewrite list_swap_elem_length, fold_mat_nrows in H1.
  rewrite butn_length, map_length, fold_mat_nrows in H1.
  apply Nat.neq_0_lt_0, Nat.ltb_lt in Hnz.
  rewrite Hnz in H1; cbn - [ "<?" ] in H1.
  apply Nat.ltb_lt in Hnz.
  rewrite <- H1 in Hx; [ | flia Hi1 Hlin | flia Hj Hnz ].
  subst x; clear H1.
  rewrite rngl_mul_comm; [ | now destruct Hif ].
  rewrite rngl_mul_assoc, rngl_mul_mul_swap; [ | now destruct Hif ].
  replace (mat_el' M p j) with (mat_el' (mat_swap_rows 0 (p - 1) M) 0 j). 2: {
    unfold mat_swap_rows.
    cbn; unfold list_swap_elem.
    rewrite fold_mat_nrows.
    rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
    rewrite seq_nth; [ | easy ].
    rewrite Nat.add_0_r, transposition_1.
    easy.
  }
  rewrite <- HeqM'.
  rewrite rngl_mul_opp_r; [ | now destruct Hif ].
  easy.
}
cbn.
rewrite <- rngl_opp_summation; [ | now destruct Hif ].
(*
do 2 rewrite <- determinant_succ.
*)
subst M'.
rewrite <- rngl_opp_involutive; [ | now destruct Hif ].
f_equal.
(*
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1.
*)
rewrite fold_det.
assert (H1 : 0 ≠ p - 1) by flia Hlin Hi1.
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
apply rngl_summation_eq_compat.
intros i Hi.
f_equal; f_equal.
destruct i; [ easy | ].
rewrite Nat_sub_succ_1.
rewrite minus_one_pow_succ; [ | now destruct Hif ].
rewrite minus_one_pow_succ; [ | now destruct Hif ].
now symmetry; apply rngl_opp_involutive; destruct Hif.
Qed.

Theorem rngl_product_seq_permut :
  rngl_is_comm = true →
  ∀ n σ (f : nat → T),
  n ≠ 0
  → is_permut n σ
  → ∏ (i = 0, n - 1), f (ff_app σ i) = ∏ (i = 0, n - 1), f i.
Proof.
intros Hic * Hnz Hσ.
destruct n; [ easy | clear Hnz ].
rewrite Nat_sub_succ_1.
destruct Hσ as ((Hs, Hinj) & Hσl).
revert σ Hs Hinj Hσl.
induction n; intros; cbn. {
  do 2 rewrite rngl_product_only_one.
  destruct σ as [| a l]; [ easy | ].
  destruct l; [ | easy ].
  specialize (Hs a (or_introl eq_refl)).
  now apply Nat.lt_1_r in Hs; subst a.
}
set
  (g := λ i,
   if lt_dec i (ff_app (isort_rank Nat.leb σ) (S n)) then i else i + 1).
set (σ' := map (λ i, ff_app σ (g i)) (seq 0 (S n))).
assert (Hσ'l : length σ' = S n). {
  now unfold σ'; rewrite List_map_seq_length.
}
move g after Hσl; move σ' after Hσl.
specialize (IHn σ').
rewrite Hσ'l in IHn.
assert (Hs' : ∀ x, x ∈ σ' → x < S n). {
  intros x Hx.
  apply in_map_iff in Hx.
  destruct Hx as (i & Hxi & Hi); apply in_seq in Hi.
  rewrite <- Hxi.
  unfold g.
  destruct (lt_dec i _) as [His| His]. {
    specialize (Hs (ff_app σ i)) as H1.
    assert (H : ff_app σ i ∈ σ) by (apply nth_In; rewrite Hσl; flia Hi).
    specialize (H1 H); clear H.
    rewrite Hσl in H1.
    enough (H : ff_app σ i ≠ S n) by flia H1 H; intros Hσs.
    rewrite <- Hσs in His.
    rewrite permut_isort_permut in His; [ | easy | rewrite Hσl; flia Hi ].
    now apply lt_irrefl in His.
  } {
    rewrite Nat.add_1_r.
    specialize (Hs (ff_app σ (S i))) as H1.
    assert (H : ff_app σ (S i) ∈ σ). {
      apply nth_In; rewrite Hσl.
      now apply -> Nat.succ_lt_mono.
    }
    specialize (H1 H); clear H.
    rewrite Hσl in H1.
    enough (H : ff_app σ (S i) ≠ S n) by flia H1 H; intros Hσs.
    rewrite <- Hσs in His.
    rewrite permut_isort_permut in His; [ | easy | rewrite Hσl; flia Hi ].
    now apply His.
  }
}
move Hs' before Hs.
specialize (IHn Hs').
assert (H : NoDup σ'). {
  apply nat_NoDup.
  intros i j Hi Hj Hij; unfold σ', ff_app in Hij.
  rewrite Hσ'l in Hi, Hj.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  do 2 rewrite Nat.add_0_l in Hij.
  unfold g in Hij; cbn in Hij.
  specialize (NoDup_nat _ Hinj) as Hinj'.
  rewrite Hσl in Hinj'.
  destruct (lt_dec i _) as [His| His]. {
    destruct (lt_dec j _) as [Hjs| Hjs]. {
      apply Hinj' in Hij; [ easy | flia Hi | flia Hj ].
    }
    rewrite Nat.add_1_r in Hij.
    apply Nat.nlt_ge in Hjs.
    apply Hinj' in Hij; [ flia His Hjs Hij | flia Hi | ].
    now apply -> Nat.succ_lt_mono.
  }
  apply Nat.nlt_ge in His.
  rewrite Nat.add_1_r in Hij.
  destruct (lt_dec j _) as [Hjs| Hjs]. {
    apply Hinj' in Hij; [ flia His Hjs Hij | | flia Hj ].
    now apply -> Nat.succ_lt_mono.
  }
  rewrite Nat.add_1_r in Hij.
  apply Nat.succ_lt_mono in Hi, Hj.
  apply Hinj' in Hij; [ | easy | easy ].
  now apply Nat.succ_inj in Hij.
}
specialize (IHn H eq_refl); clear H.
remember (ff_app (isort_rank Nat.leb σ) (S n)) as k eqn:Hk.
destruct (Nat.eq_dec k (S n)) as [Hksn| Hksn]. {
  erewrite rngl_product_eq_compat in IHn. 2: {
    intros i Hi.
    unfold σ', g; cbn - [ seq ].
    unfold ff_app.
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hi ].
    rewrite seq_nth; [ | flia Hi ].
    rewrite Nat.add_0_l.
    destruct (lt_dec i k) as [H| H]; [ easy | flia Hksn Hi H ].
  }
  cbn in IHn.
  rewrite rngl_product_split_last; [ | flia ].
  rewrite rngl_product_succ_succ' with (g0 := λ i, f (ff_app σ i)).
  symmetry.
  rewrite rngl_product_split_last; [ | flia ].
  rewrite rngl_product_succ_succ'.
  symmetry; unfold ff_app at 1.
  rewrite IHn; f_equal; f_equal.
  rewrite Hk in Hksn.
  rewrite <- Hksn at 1.
  apply permut_permut_isort; [ easy | now rewrite Hσl ].
}
specialize (isort_rank_is_permut_list Nat.leb) as H1.
specialize (H1 σ).
rewrite rngl_product_split with (j := k) in IHn. 2: {
  split; [ flia | ].
  destruct H1 as (H1 & H2).
  apply -> Nat.succ_le_mono.
  rewrite isort_rank_length, Hσl in H1.
  specialize (H1 k).
  assert (H : k ∈ isort_rank Nat.leb σ). {
    rewrite Hk.
    apply nth_In.
    now rewrite isort_rank_length, Hσl.
  }
  specialize (H1 H); clear H.
  flia Hksn H1.
}
rewrite rngl_product_split_last in IHn; [ | flia ].
destruct (Nat.eq_dec k 0) as [Hkz| Hkz]. {
  move Hkz at top; subst k.
  rewrite rngl_product_empty in IHn; [ | flia ].
  rewrite rngl_mul_1_l, Nat.add_0_l in IHn.
  unfold σ' in IHn at 1.
  cbn - [ seq ] in IHn.
  unfold ff_app in IHn at 1.
  rewrite (List_map_nth' 0) in IHn; [ | rewrite seq_length; flia ].
  rewrite seq_nth in IHn; [ | flia ].
  rewrite Nat.add_0_l in IHn.
  erewrite rngl_product_eq_compat in IHn. 2: {
    intros i Hi.
    unfold ff_app, σ'.
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hi ].
    rewrite seq_nth; [ | flia Hi ].
    rewrite Nat.add_0_l.
    easy.
  }
  symmetry.
  rewrite rngl_product_split_last; [ | flia ].
  rewrite rngl_product_succ_succ'.
  rewrite <- IHn.
  symmetry.
  rewrite rngl_product_split_first; [ | flia ].
  rewrite rngl_product_succ_succ.
  rewrite rngl_product_split_first; [ | flia ].
  rewrite rngl_mul_comm; [ | easy ].
  do 2 rewrite <- rngl_mul_assoc.
  f_equal.
  f_equal. 2: {
    f_equal; rewrite Hk.
    apply permut_permut_isort; [ easy | now rewrite Hσl ].
  }
  apply rngl_product_eq_compat.
  intros i Hi.
  unfold g; rewrite Nat.add_1_r.
  destruct (lt_dec i 0) as [H| H]; [ flia Hi H | easy ].
}
erewrite rngl_product_eq_compat in IHn. 2: {
  intros i Hi.
  unfold σ'; cbn - [ seq ].
  assert (H : i - 1 < S n). {
    destruct H1 as (H1, H2).
    specialize (H1 k).
    assert (H : k ∈ isort_rank Nat.leb σ). {
      rewrite Hk; unfold ff_app.
      apply nth_In.
      now rewrite isort_rank_length, Hσl.
    }
    specialize (H1 H); clear H.
    rewrite isort_rank_length, Hσl in H1.
    flia H1 Hi.
  }
  unfold ff_app at 1.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite Nat.add_0_l.
  unfold g.
  clear H.
  destruct (lt_dec (i - 1) k) as [H| H]; [ | flia Hi H ].
  easy.
}
cbn - [ seq ] in IHn.
destruct k; [ easy | clear Hkz ].
rewrite rngl_product_succ_succ' with (g0 := λ i, f (ff_app σ i)) in IHn.
erewrite rngl_product_eq_compat with (b := S k + 1) in IHn. 2: {
  intros i Hi.
  unfold ff_app, σ'.
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hi ].
  rewrite seq_nth; [ | flia Hi ].
  rewrite Nat.add_0_l.
  unfold g.
  destruct (lt_dec i (S k)) as [H| H]; [ flia Hi H | easy ].
}
cbn in IHn.
rewrite rngl_mul_mul_swap in IHn; [ | easy ].
symmetry.
rewrite rngl_product_split_last; [ | flia ].
rewrite rngl_product_succ_succ'.
rewrite <- IHn.
symmetry.
rewrite rngl_product_split with (j := k). 2: {
  split; [ flia | ].
  rewrite Hk.
  destruct H1 as (H1, H2).
  rewrite isort_rank_length, Hσl in H1.
  apply Nat.lt_le_incl.
  apply H1, nth_In.
  now rewrite isort_rank_length, Hσl.
}
do 2 rewrite <- rngl_mul_assoc.
f_equal.
rewrite rngl_product_split_last. 2: {
  rewrite Nat.add_1_r, Hk.
  destruct H1 as (H1, H2).
  rewrite isort_rank_length, Hσl in H1.
  apply Nat.lt_succ_r.
  apply H1, nth_In.
  now rewrite isort_rank_length, Hσl.
}
rewrite rngl_product_succ_succ' with (g0 := λ i, f (ff_app σ i)).
rewrite rngl_product_split_first. 2: {
  rewrite Nat.add_1_r.
  destruct H1 as (H1, H2).
  rewrite isort_rank_length, Hσl in H1.
  specialize (H1 (S k)).
  assert (H : S k ∈ isort_rank Nat.leb σ). {
    rewrite Hk.
    apply nth_In.
    now rewrite isort_rank_length, Hσl.
  }
  specialize (H1 H); clear H.
  flia Hksn H1.
}
replace (ff_app σ (k + 1)) with (S n). 2: {
  rewrite Nat.add_1_r.
  rewrite Hk.
  symmetry.
  apply permut_permut_isort; [ easy | now rewrite Hσl ].
}
rewrite <- rngl_mul_assoc.
rewrite rngl_mul_comm; [ | easy ].
rewrite rngl_mul_assoc.
f_equal.
destruct
  (Nat.eq_dec (ff_app (isort_rank Nat.leb σ) (S n)) n) as [H7| H7]. {
  rewrite H7 in Hk.
  rewrite Nat.add_1_r.
  rewrite Hk.
  rewrite rngl_product_empty; [ | flia ].
  rewrite rngl_product_empty; [ | flia ].
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hk ].
  rewrite seq_nth; [ | flia Hk ].
  unfold g; cbn.
  destruct (lt_dec (S k) (S k)) as [H| H]; [ flia H | clear H ].
  now rewrite Nat.add_1_r, Hk.
}
assert (Hkn : S (k + 1) ≤ n). {
  rewrite Nat.add_1_r.
  destruct H1 as (H1, H2).
  apply Nat.le_succ_l.
  rewrite isort_rank_length, Hσl in H1.
  specialize (H1 (S k)).
  assert (H : S k ∈ isort_rank Nat.leb σ). {
    rewrite Hk.
    apply nth_In.
    now rewrite isort_rank_length, Hσl.
  }
  specialize (H1 H); clear H.
  rewrite <- Hk in H7.
  flia Hksn H1 H7.
}
rewrite rngl_product_split_first; [ | easy ].
rewrite <- rngl_mul_assoc.
rewrite rngl_mul_comm; [ | easy ].
unfold g.
rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hkn ].
rewrite seq_nth; [ | flia Hkn ].
rewrite Nat.add_1_r.
cbn.
destruct (lt_dec (S k) (S k)) as [H| H]; [ flia H | clear H ].
rewrite Nat.add_1_r.
f_equal.
symmetry.
rewrite rngl_product_split_last; [ | flia Hkn ].
rewrite Nat.add_1_r.
f_equal.
apply rngl_product_eq_compat.
intros i Hi.
rewrite Nat.sub_add; [ easy | flia Hi ].
Qed.

Theorem det_by_any_sym_gr : in_charac_0_field →
  ∀ n (M : matrix T) (sg : list (list nat)),
  n ≠ 0
  → mat_nrows M = n
  → is_square_matrix M = true
  → is_sym_gr_list n sg
  → det M =
    ∑ (k = 0, n! - 1),
    ε (nth k sg []) *
    ∏ (i = 1, n), mat_el' M i (ff_app (nth k sg []) (i - 1) + 1).
Proof.
intros Hif * Hnz Hr Hsm Hsg.
rewrite det_is_det'; try now destruct Hif.
unfold det'.
rewrite Hr.
set (g := λ i, canon_sym_gr_list_inv n (nth i sg [])).
set (h := λ i, sym_gr_inv sg (canon_sym_gr_list n i)).
rewrite rngl_summation_change_var with (g0 := g) (h0 := h). 2: {
  intros i (_, Hi).
  unfold g, h.
  rewrite (nth_sym_gr_inv_sym_gr Hsg). 2: {
    apply canon_sym_gr_list_is_permut.
    specialize (fact_neq_0 n) as H.
    flia Hi H.
  }
  apply canon_sym_gr_list_inv_canon_sym_gr_list.
  specialize (fact_neq_0 n) as H.
  flia Hi H.
}
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | apply Nat.neq_0_lt_0, fact_neq_0 ].
rewrite Nat_sub_succ_1.
erewrite rngl_summation_list_eq_compat. 2: {
  intros i Hi.
  apply in_map_iff in Hi.
  destruct Hi as (j & Hji & Hj).
  apply in_seq in Hj.
  unfold g.
  rewrite canon_sym_gr_list_canon_sym_gr_list_inv. 2: {
    split. {
      apply Hsg; rewrite <- Hji.
      now apply (sym_gr_inv_lt _ Hnz).
    } {
      destruct Hsg as (H1 & H2 & H3).
      apply H1; rewrite <- Hji.
      now apply (sym_gr_inv_lt _ Hnz).
    }
  }
  easy.
}
cbn.
apply (rngl_summation_list_permut _ _ Nat.eqb_eq).
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | apply Nat.neq_0_lt_0, fact_neq_0 ].
rewrite Nat_sub_succ_1.
remember (map _ _) as la eqn:Hla.
replace n! with (length la) by now rewrite Hla, List_map_seq_length.
apply permut_list_permutation_iff.
subst la.
(* lemma to do? *)
unfold h.
split. {
  intros i Hi.
  rewrite List_map_seq_length.
  apply in_map_iff in Hi.
  destruct Hi as (j & Hji & Hj).
  apply in_seq in Hj.
  rewrite <- Hji.
  rewrite <- sym_gr_size with (sg := sg); [ | easy ].
  now apply (sym_gr_inv_lt _ Hnz).
} {
  apply (NoDup_map_iff 0).
  rewrite seq_length.
  intros i j Hi Hj Hij.
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  do 2 rewrite Nat.add_0_l in Hij.
  apply (@sym_gr_inv_inj n) in Hij; [ | easy | | ]; cycle 1. {
    now apply canon_sym_gr_list_is_permut.
  } {
    now apply canon_sym_gr_list_is_permut.
  }
  now apply canon_sym_gr_list_inj in Hij.
}
Qed.

Theorem map_permut_seq_is_permut : ∀ n σ,
  is_permut n σ
  → is_permut n (map (ff_app σ) (seq 0 n)).
Proof.
intros * Hσ.
split; [ | now rewrite List_map_seq_length ].
split. {
  intros i Hi.
  apply in_map_iff in Hi.
  destruct Hi as (j & Hji & Hj).
  apply in_seq in Hj.
  rewrite List_map_seq_length.
  rewrite <- Hji.
  destruct Hσ as (H1, H2).
  rewrite <- H2 in Hj |-*.
  now apply permut_list_ub.
} {
  apply (NoDup_map_iff 0).
  rewrite seq_length.
  intros i j Hi Hj Hij.
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  do 2 rewrite Nat.add_0_l in Hij.
  destruct Hσ as ((Hσa, Hσn), Hσl).
  apply (NoDup_nat _ Hσn); [ congruence | congruence | easy ].
}
Qed.

Theorem rngl_product_map_permut :
  rngl_is_comm = true →
   ∀ n f σ,
  is_permut n σ
  → ∏ (i ∈ map (ff_app σ) (seq 0 n)), f i = ∏ (i = 1, n), f (i - 1)%nat.
Proof.
intros Hic * Hσ.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
rewrite (rngl_product_list_permut _ _ Nat.eqb_eq) with
    (l2 := seq 0 n); [ | easy | ]. 2: {
  destruct Hσ as (H1, H2).
  rewrite <- H2 at 1.
  rewrite <- List_map_ff_app_seq, <- H2.
  now apply permut_list_permutation_iff.
}
unfold iter_seq.
rewrite Nat_sub_succ_1.
rewrite <- seq_shift.
replace n with (S (n - 1) - 0) by flia Hnz.
rewrite <- rngl_product_change_var; [ easy | ].
intros i Hi.
now rewrite Nat.sub_succ, Nat.sub_0_r.
Qed.

Theorem map_ff_app_permut_permut_is_permut : ∀ n l1 l2,
  is_permut n l1
  → is_permut n l2
  → is_permut n (map (ff_app l1) l2).
Proof.
intros n l σ (Hl1, Hl2) (Hσ1, Hσ2).
split; [ | now rewrite map_length ].
split. {
  intros i Hi; apply in_map_iff in Hi.
  destruct Hi as (j & Hji & Hj).
  rewrite map_length.
  rewrite <- Hji.
  rewrite Hσ2, <- Hl2.
  apply permut_list_ub; [ easy | ].
  rewrite Hl2, <- Hσ2.
  now apply Hσ1.
} {
  apply (NoDup_map_iff 0).
  intros u v Hu Hv Huv.
  destruct Hl1 as (Ha1, Hn1).
  apply (NoDup_nat _ Hn1) in Huv; cycle 1. {
    rewrite Hl2, <- Hσ2.
    now apply Hσ1, nth_In.
  } {
    rewrite Hl2, <- Hσ2.
    now apply Hσ1, nth_In.
  }
  destruct Hσ1 as (Hσa1, Hσn1).
  now apply (NoDup_nat _ Hσn1) in Huv.
}
Qed.

Theorem isort_rank_inj2 : ∀ l1 l2,
  is_permut_list l1
  → is_permut_list l2
  → isort_rank Nat.leb l1 = isort_rank Nat.leb l2
  → l1 = l2.
Proof.
intros * Hpl1 Hpl2 Hill.
assert (Hll : length l1 = length l2). {
  apply List_eq_iff in Hill.
  now do 2 rewrite isort_rank_length in Hill.
}
apply (f_equal (comp_list l1)) in Hill.
(**)
rewrite comp_isort_rank_r in Hill.
rewrite permut_isort_leb in Hill; [ | easy ].
apply (f_equal (λ l, comp_list l l2)) in Hill.
rewrite comp_1_l in Hill; [ | now rewrite Hll; destruct Hpl2 ].
rewrite <- (@permut_comp_assoc (length l2)) in Hill; [ | | easy ]. 2: {
  apply isort_rank_length.
}
rewrite permut_comp_isort_rank_l in Hill; [ | easy ].
now rewrite comp_1_r in Hill.
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

Theorem det_any_permut_l : in_charac_0_field →
  ∀ n (M : matrix T) (σ : list nat),
  n ≠ 0
  → mat_nrows M = n
  → is_square_matrix M = true
  → is_permut n σ
  → det M =
    (∑ (μ ∈ canon_sym_gr_list_list n), ε μ * ε σ *
     ∏ (k = 0, n - 1), mat_el' M (ff_app σ k + 1) (ff_app μ k + 1))%F.
Proof.
intros Hif * Hnz Hr Hsm Hσ.
erewrite rngl_summation_list_eq_compat. 2: {
  intros μ Hμ.
  assert (Hpμ : is_permut n μ). {
    apply in_map_iff in Hμ.
    destruct Hμ as (i & Hiμ & Hi).
    apply in_seq in Hi.
    rewrite <- Hiμ.
    now apply canon_sym_gr_list_is_permut.
  }
  remember (μ ° isort_rank Nat.leb σ) as ν eqn:Hν.
  assert (Hσν : ν ° σ = μ). {
    rewrite Hν.
    assert (H : length (isort_rank Nat.leb σ) = n). {
      rewrite isort_rank_length; apply Hσ.
    }
    rewrite <- (permut_comp_assoc _ H Hσ); clear H.
    rewrite permut_comp_isort_rank_l; [ | now destruct Hσ ].
    apply comp_1_r.
    destruct Hσ, Hpμ; congruence.
  }
  subst ν.
  rewrite <- Hσν at 1.
  replace (ε ((μ ° isort_rank Nat.leb σ) ° σ)) with
      (ε (μ ° isort_rank Nat.leb σ) * ε σ)%F. 2: {
    destruct Hσ.
    rewrite <- sign_comp; [ easy | easy | ].
    now rewrite comp_length, isort_rank_length.
  }
  rewrite <- (rngl_mul_assoc _ (ε σ) (ε σ)).
  rewrite NoDup_ε_square; [ | now destruct Hif | ]. 2: {
    now destruct Hσ as ((_, H), _).
  }
  rewrite rngl_mul_1_r.
  easy.
}
cbn.
unfold canon_sym_gr_list_list.
rewrite <- rngl_summation_list_change_var.
rewrite rngl_summation_seq_summation; [ | apply fact_neq_0 ].
rewrite Nat.add_0_l.
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  rewrite rngl_product_change_var with
      (g := ff_app (isort_rank Nat.leb σ)) (h := ff_app σ). 2: {
    intros j Hj.
    apply permut_isort_permut; [ now destruct Hσ | ].
    destruct Hσ as (Hσp, Hσl); rewrite Hσl.
    flia Hj Hnz.
  }
  rewrite Nat.sub_0_r.
  rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
  rewrite Nat_sub_succ_1.
  erewrite rngl_product_list_eq_compat. 2: {
    intros j Hj.
    apply in_map_iff in Hj.
    destruct Hj as (k & Hkj & Hk).
    apply in_seq in Hk.
    rewrite permut_permut_isort; [ | now destruct Hσ | ]. 2: {
      rewrite <- Hkj.
      destruct Hσ as (H1, H2).
      rewrite <- H2 in Hk.
      now apply permut_list_ub.
    }
    easy.
  }
  cbn.
  rewrite rngl_product_map_permut; [ | now destruct Hif | easy ].
  easy.
}
cbn.
set
  (sg := map (λ k, canon_sym_gr_list n k ° isort_rank Nat.leb σ) (seq 0 n!)).
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  assert (Hkn : k < n!). {
    specialize (fact_neq_0 n) as H.
    flia Hk H.
  }
  replace (_ ° _) with (nth k sg []). 2: {
    unfold sg.
    rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
    now rewrite seq_nth.
  }
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite Nat.sub_add; [ | flia Hi ].
    replace (ff_app _ _) with (ff_app (nth k sg []) (i - 1)). 2: {
      unfold sg.
      rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
      rewrite seq_nth; [ | easy ].
      rewrite Nat.add_0_l.
      unfold "°".
      unfold ff_app.
      rewrite (List_map_nth' 0). 2: {
        rewrite isort_rank_length.
        destruct Hσ as (H1, H2); rewrite H2.
        flia Hi.
      }
      easy.
    }
    easy.
  }
  easy.
}
cbn.
apply det_by_any_sym_gr; try easy.
unfold sg.
split. {
  rewrite List_map_seq_length.
  intros i Hi.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite Nat.add_0_l.
  split. {
    unfold "°"; cbn.
    rewrite map_length.
    rewrite isort_rank_length.
    now destruct Hσ.
  } {
    apply (comp_is_permut_list n). {
      now apply canon_sym_gr_list_is_permut.
    } {
      now apply isort_rank_is_permut; destruct Hσ.
    }
  }
}
split. {
  rewrite List_map_seq_length.
  intros i j Hi Hj Hij.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  do 2 rewrite Nat.add_0_l in Hij.
  unfold "°" in Hij.
  specialize (ext_in_map Hij) as H1.
  apply (nth_canon_sym_gr_list_inj2 n); [ easy | easy | ].
  intros k Hk.
  apply H1.
  apply (permutation_in_iff Nat.eqb_eq) with (lb := seq 0 n). 2: {
    clear - Hk.
    induction n; intros; [ easy | ].
    rewrite seq_S; cbn.
    apply in_or_app.
    destruct (Nat.eq_dec k n) as [Hkn| Hkn]. {
      now subst k; right; left.
    }
    left; apply IHn; flia Hk Hkn.
  }
  replace n with (length (isort_rank Nat.leb σ)). 2: {
    rewrite isort_rank_length.
    now destruct Hσ.
  }
  apply permut_list_permutation_iff.
  apply isort_rank_is_permut_list.
} {
  intros l Hl.
  apply in_map_iff.
  destruct Hl as (Hl1, Hl2).
  destruct Hσ as (Hσ1, Hσ2).
  exists (canon_sym_gr_list_inv n (l ° σ)).
  rewrite canon_sym_gr_list_canon_sym_gr_list_inv. 2: {
    now apply map_ff_app_permut_permut_is_permut.
  }
  split. {
    rewrite <- (permut_comp_assoc n); [ | easy | ]. 2: {
      now apply isort_rank_is_permut.
    }
    rewrite permut_comp_isort_rank_r; [ | easy ].
    apply comp_1_r.
    congruence.
  }
  apply in_seq.
  split; [ easy | ].
  rewrite Nat.add_0_l.
  apply canon_sym_gr_list_inv_ub.
  now apply map_ff_app_permut_permut_is_permut.
}
Qed.

Theorem det_any_permut_r : in_charac_0_field →
  ∀ n (M : matrix T) (σ : list nat),
  n ≠ 0
  → mat_nrows M = n
  → is_square_matrix M = true
  → is_permut n σ
  → det M =
    (∑ (μ ∈ canon_sym_gr_list_list n), ε μ * ε σ *
     ∏ (k = 0, n - 1), mat_el' M (ff_app μ k + 1) (ff_app σ k + 1))%F.
Proof.
intros Hif * Hnz Hr Hsm Hσ.
erewrite rngl_summation_list_eq_compat. 2: {
  intros μ Hμ.
  assert (Hpμ : is_permut n μ). {
    apply in_map_iff in Hμ.
    destruct Hμ as (i & Hiμ & Hi).
    apply in_seq in Hi.
    rewrite <- Hiμ.
    now apply canon_sym_gr_list_is_permut.
  }
  remember (σ ° isort_rank Nat.leb μ) as ν eqn:Hν.
  assert (Hσν : ν ° μ = σ). {
    rewrite Hν.
    assert (H : length (isort_rank Nat.leb μ) = n). {
      rewrite isort_rank_length.
      apply Hpμ.
    }
    rewrite <- (permut_comp_assoc _ H); clear H; [ | apply Hpμ ].
    rewrite permut_comp_isort_rank_l; [ | now destruct Hpμ ].
    apply comp_1_r.
    destruct Hσ, Hpμ; congruence.
  }
  subst ν.
  rewrite <- Hσν at 1.
  replace (ε ((σ ° isort_rank Nat.leb μ) ° μ)) with
      (ε (σ ° isort_rank Nat.leb μ) * ε μ)%F. 2: {
    destruct Hif.
    rewrite <- sign_comp; [ easy | easy | ].
    rewrite comp_length, isort_rank_length.
    now destruct Hpμ.
  }
  destruct Hif as (Hic & Hop & Hiv & Hit & H10 & Hde & Hch) in Hsm.
  rewrite (rngl_mul_comm Hic _ (ε μ)).
  rewrite rngl_mul_assoc.
  rewrite NoDup_ε_square; [ | easy | now destruct Hpμ as ((_, H), _) ].
  rewrite rngl_mul_1_l.
  easy.
}
cbn.
unfold canon_sym_gr_list_list.
rewrite <- rngl_summation_list_change_var.
rewrite rngl_summation_seq_summation; [ | apply fact_neq_0 ].
rewrite Nat.add_0_l.
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  assert (Hc : is_permut n (canon_sym_gr_list n i)). {
    apply canon_sym_gr_list_is_permut.
    specialize (fact_neq_0 n) as H.
    flia Hi H.
  }
  rewrite rngl_product_change_var with
      (g := ff_app (isort_rank Nat.leb (canon_sym_gr_list n i)))
      (h := ff_app (canon_sym_gr_list n i)). 2: {
    intros j (_, Hj).
    apply permut_isort_permut. 2: {
      rewrite canon_sym_gr_list_length; flia Hj Hnz.
    }
    apply canon_sym_gr_list_is_permut.
    specialize (fact_neq_0 n) as H.
    flia Hi H.
  }
  rewrite Nat.sub_0_r.
  rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
  rewrite Nat_sub_succ_1.
  erewrite rngl_product_list_eq_compat. 2: {
    intros j Hj.
    apply in_map_iff in Hj.
    destruct Hj as (k & Hkj & Hk).
    apply in_seq in Hk.
    rewrite permut_permut_isort; [ easy | | ]. {
      apply canon_sym_gr_list_is_permut_list.
      specialize (fact_neq_0 n) as H.
      flia Hi H.
    }
    rewrite <- Hkj.
    apply permut_list_ub; [ apply Hc | ].
    now rewrite canon_sym_gr_list_length.
  }
  cbn.
  destruct Hif as (Hic & Hop & Hiv & Hit & H10 & Hde & Hch) in Hsm.
  rewrite rngl_product_map_permut; [ | easy | easy ].
  easy.
}
cbn.
set
  (sg :=
     map (λ k, σ ° isort_rank Nat.leb (canon_sym_gr_list n k)) (seq 0 n!)).
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  assert (Hkn : k < n!). {
    specialize (fact_neq_0 n) as H.
    flia Hk H.
  }
  replace (_ ° _) with (nth k sg []). 2: {
    unfold sg.
    rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
    now rewrite seq_nth.
  }
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite Nat.sub_add; [ | flia Hi ].
    replace (ff_app _ _) with (ff_app (nth k sg []) (i - 1)). 2: {
      unfold sg.
      rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
      rewrite seq_nth; [ | easy ].
      rewrite Nat.add_0_l.
      unfold "°".
      unfold ff_app.
      rewrite (List_map_nth' 0). 2: {
        rewrite isort_rank_length.
        rewrite canon_sym_gr_list_length.
        flia Hi.
      }
      easy.
    }
    easy.
  }
  easy.
}
cbn.
apply det_by_any_sym_gr; try easy.
unfold sg.
split. {
  rewrite List_map_seq_length.
  intros i Hi.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite Nat.add_0_l.
  split. {
    unfold "°"; cbn.
    rewrite map_length.
    rewrite isort_rank_length.
    apply canon_sym_gr_list_length.
  } {
    apply (comp_is_permut_list n); [ easy | ].
    apply isort_rank_is_permut.
    now apply canon_sym_gr_list_is_permut.
  }
}
split. {
  rewrite List_map_seq_length.
  intros i j Hi Hj Hij.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  do 2 rewrite Nat.add_0_l in Hij.
  unfold "°" in Hij.
  apply (f_equal (map (ff_app (isort_rank Nat.leb σ)))) in Hij.
  do 2 rewrite map_map in Hij.
  erewrite map_ext_in in Hij. 2: {
    intros k Hk.
    apply (In_nth _ _ 0) in Hk.
    destruct Hk as (u & Hu1 & Hu2).
    rewrite permut_isort_permut; [ | now destruct Hσ | ]. 2: {
      rewrite <- Hu2.
      eapply Nat.lt_le_trans. {
        apply permut_list_ub; [ | easy ].
        apply isort_rank_is_permut_list.
      }
      rewrite isort_rank_length.
      rewrite canon_sym_gr_list_length.
      now destruct Hσ as (_, Hσl); rewrite Hσl.
    }
    easy.
  }
  symmetry in Hij.
  erewrite map_ext_in in Hij. 2: {
    intros k Hk.
    apply (In_nth _ _ 0) in Hk.
    destruct Hk as (u & Hu1 & Hu2).
    rewrite permut_isort_permut; [ | now destruct Hσ | ]. 2: {
      rewrite <- Hu2.
      eapply Nat.lt_le_trans. {
        apply permut_list_ub; [ | easy ].
        apply isort_rank_is_permut_list.
      }
      rewrite isort_rank_length.
      rewrite canon_sym_gr_list_length.
      now destruct Hσ as (_, Hσl); rewrite Hσl.
    }
    easy.
  }
  symmetry in Hij.
  do 2 rewrite map_id in Hij.
  apply isort_rank_inj2 in Hij; cycle 1. {
    now apply canon_sym_gr_list_is_permut_list.
  } {
    now apply canon_sym_gr_list_is_permut_list.
  }
  now apply canon_sym_gr_list_inj in Hij.
} {
  intros l Hl.
  apply in_map_iff.
  exists (canon_sym_gr_list_inv n (isort_rank Nat.leb l ° σ)).
  rewrite canon_sym_gr_list_canon_sym_gr_list_inv. 2: {
    apply comp_is_permut; [ | easy ].
    apply isort_rank_is_permut.
    now destruct Hl.
  }
  rewrite (permut_isort_rank_comp n); [ | | | easy ]; cycle 1. {
    apply NoDup_isort_rank.
  } {
    rewrite isort_rank_length.
    now destruct Hl.
  }
  rewrite (permut_comp_assoc n); cycle 1. {
    rewrite isort_rank_length.
    now destruct Hσ.
  } {
    do 2 apply isort_rank_is_permut.
    now destruct Hl.
  }
  rewrite permut_comp_isort_rank_r; [ | now destruct Hσ ].
  rewrite comp_1_l. 2: {
    intros i Hi.
    apply in_isort_rank_lt in Hi.
    rewrite isort_rank_length in Hi.
    destruct Hσ, Hl; congruence.
  }
  rewrite permut_isort_rank_involutive; [ | now destruct Hl ].
  split; [ easy | ].
  apply in_seq.
  split; [ easy | ].
  apply canon_sym_gr_list_inv_ub.
  apply comp_is_permut; [ | easy ].
  apply isort_rank_is_permut.
  now destruct Hl.
}
Qed.

(* https://proofwiki.org/wiki/Permutation_of_Determinant_Indices *)

Theorem determinant_transpose : in_charac_0_field →
  ∀ (M : matrix T),
  is_square_matrix M = true
  → det M⁺ = det M.
Proof.
intros Hif * Hsm.
remember (mat_nrows M) as n eqn:Hr; symmetry in Hr.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  unfold det.
  rewrite mat_transp_nrows, Hr.
  rewrite square_matrix_ncols; [ | easy ].
  now rewrite Hr, Hnz.
}
specialize (mat_transp_is_square M Hsm) as Hts.
assert (Hs : is_permut n (seq 0 n)) by apply seq_is_permut.
assert (Hr' : mat_nrows M⁺ = n). {
  now rewrite mat_transp_nrows, square_matrix_ncols.
}
rewrite (det_any_permut_l Hif M Hnz Hr Hsm Hs).
rewrite (det_any_permut_r Hif (M⁺)%M Hnz Hr' Hts Hs).
apply rngl_summation_list_eq_compat.
intros p Hp.
f_equal.
apply rngl_product_eq_compat.
intros k Hk.
unfold mat_transp.
unfold ff_app; cbn.
do 2 rewrite Nat.add_sub.
rewrite seq_nth; [ | flia Hk Hnz ].
assert (Hpr : ff_app p k < mat_nrows M). {
  apply in_map_iff in Hp.
  destruct Hp as (i & Hi & His).
  apply in_seq in His.
  rewrite <- Hi.
  rewrite Hr.
  apply canon_sym_gr_list_ub; [ easy | ].
  flia Hnz Hk.
}
rewrite (List_map_nth' 0). 2: {
  now rewrite seq_length, square_matrix_ncols.
}
rewrite (List_map_nth' 0); [ | rewrite seq_length, Hr; flia Hk Hnz ].
rewrite seq_nth; [ | rewrite Hr; flia Hk Hnz ].
rewrite Nat.add_0_l.
rewrite seq_nth; [ | now rewrite square_matrix_ncols ].
now do 2 rewrite Nat.add_1_r.
Qed.

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
specialize (square_matrix_ncols _ Hsm) as Hc.
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
do 2 rewrite seq_length.
symmetry.
do 2 rewrite <- seq_shift.
rewrite map_map.
symmetry.
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
destruct Hi as (_, Hi); cbn in Hi.
do 2 rewrite map_map.
apply map_ext_in.
intros j Hj; apply in_seq in Hj.
destruct Hj as (_, Hj); cbn in Hj.
move j before i.
do 2 rewrite Nat_sub_succ_1.
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
rewrite seq_nth; [ | easy ].
do 2 rewrite Nat.add_0_l.
rewrite Nat.add_comm; f_equal; symmetry.
erewrite map_ext_in. 2: {
  intros k Hk.
  now rewrite seq_shift.
}
specialize (@fold_mat_transp T ro M) as H1.
rewrite <- seq_shift with (len := mat_ncols M) in H1.
rewrite map_map in H1.
rewrite H1.
rewrite <- determinant_transpose; [ | easy | ]. 2: {
  rewrite square_matrix_ncols in Hi; [ | easy ].
  now apply is_squ_mat_subm.
}
f_equal.
specialize (square_matrix_ncols _ Hsm) as Hcr.
destruct (Nat.eq_dec (mat_ncols M) 1) as [Hc1| Hc1]. {
  rewrite Hc1 in Hi.
  rewrite Hc1 in Hcr; symmetry in Hcr.
  rewrite Hcr in Hj.
  apply Nat.lt_1_r in Hi, Hj; subst i j.
  destruct M as (ll).
  unfold mat_ncols in Hc1.
  cbn in Hc1, Hcr.
  destruct ll as [| l]; [ easy | ].
  destruct ll; [ | easy ].
  cbn in Hc1.
  unfold subm, mat_transp; cbn.
  destruct l as [| a]; [ easy | ].
  now destruct l.
}
assert (Hcm : is_correct_matrix M = true) by now apply squ_mat_is_corr.
assert (Hcmt : is_correct_matrix M⁺ = true) by now apply mat_transp_is_corr.
apply matrix_eq; cycle 1. {
  now apply mat_transp_is_corr, subm_is_corr_mat.
} {
  apply subm_is_corr_mat; [ | easy ].
  rewrite mat_transp_ncols.
  rewrite if_eqb_eq_dec.
  rewrite Hcr in Hc1.
  now destruct (Nat.eq_dec (mat_ncols M) 0).
} {
  rewrite mat_transp_nrows.
  rewrite mat_nrows_subm.
  rewrite mat_ncols_subm; [ | easy ].
  replace (mat_nrows M) with (S (S (mat_nrows M - 2))) by flia Hcr Hc1 Hi.
  now rewrite mat_transp_nrows.
} {
  rewrite mat_transp_ncols.
  rewrite mat_ncols_subm; [ | easy ].
  replace (mat_nrows M) with (S (S (mat_nrows M - 2))) by flia Hcr Hc1 Hi.
  rewrite mat_ncols_subm; [ | easy ].
  rewrite mat_transp_nrows.
  replace (mat_ncols M) with (S (S (mat_ncols M - 2))) at 3 by flia Hc1 Hi.
  rewrite mat_transp_ncols.
  rewrite mat_nrows_subm.
  apply Nat.neq_0_lt_0 in Hcz.
  apply Nat.eqb_neq in Hcz; rewrite Hcz.
  apply Nat.ltb_lt in Hi; rewrite Hi.
  apply Nat.ltb_lt in Hj; rewrite Hj; cbn.
  rewrite if_eqb_eq_dec.
  rewrite Hcr.
  now destruct (Nat.eq_dec (mat_nrows M - 1) 0).
}
intros u v Hu Hv.
rewrite mat_transp_el; [ | now apply subm_is_corr_mat | flia Hu | flia Hv ].
unfold mat_transp; cbn.
rewrite (List_map_nth' []). 2: {
  rewrite butn_length.
  rewrite fold_mat_nrows.
  apply Nat.ltb_lt in Hj; rewrite Hj.
  apply Nat.ltb_lt in Hj; cbn.
  rewrite mat_ncols_subm in Hv; [ | easy ].
  rewrite mat_transp_nrows in Hv.
  replace (mat_ncols M) with (S (S (mat_ncols M - 2))) in Hv by flia Hi Hc1.
  rewrite mat_transp_ncols in Hv.
  apply Nat.neq_0_lt_0 in Hcz.
  apply Nat.eqb_neq in Hcz; rewrite Hcz in Hv.
  enough (H : v < mat_nrows M). {
    destruct v; [ easy | ].
    destruct (mat_nrows M); [ easy | ].
    do 2 rewrite Nat_sub_succ_1.
    now apply Nat.succ_lt_mono in H.
  }
  apply Nat.ltb_lt in Hj; rewrite Hj in Hv.
  cbn in Hv; flia Hv.
}
rewrite (List_map_nth' []). 2: {
  rewrite butn_length.
  rewrite List_map_seq_length.
  apply Nat.ltb_lt in Hi; rewrite Hi.
  apply Nat.ltb_lt in Hi; cbn.
  rewrite mat_transp_nrows in Hu.
  rewrite mat_ncols_subm in Hu; [ | easy ].
  replace (mat_nrows M) with (S (S (mat_nrows M - 2))) in Hu by
    flia Hj Hcr Hc1.
  enough (H : u < mat_ncols M). {
    destruct u; [ easy | ].
    destruct (mat_ncols M); [ easy | ].
    do 2 rewrite Nat_sub_succ_1.
    now apply Nat.succ_lt_mono in H.
  }
  apply Nat.ltb_lt in Hi; rewrite Hi in Hu.
  cbn in Hu; flia Hu.
}
do 4 rewrite nth_butn.
rewrite mat_transp_nrows in Hu.
rewrite mat_ncols_subm in Hu; [ | easy ].
rewrite mat_ncols_subm in Hv; [ | easy ].
rewrite mat_transp_nrows in Hv.
rewrite mat_transp_ncols in Hv.
replace (mat_nrows M) with (S (S (mat_nrows M - 2))) in Hu by flia Hj Hcr Hc1.
replace (mat_ncols M) with (S (S (mat_ncols M - 2))) in Hv by flia Hi Hc1.
cbn - [ "<?" ] in Hv.
apply Nat.ltb_lt in Hi; rewrite Hi in Hu.
apply Nat.ltb_lt in Hj; rewrite Hj in Hv.
cbn in Hu, Hv.
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  unfold Nat.b2n; rewrite if_leb_le_dec.
  destruct (le_dec i (u - 1)); flia Hu.
}
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  unfold Nat.b2n; rewrite if_leb_le_dec.
  destruct (le_dec j (v - 1)); flia Hv.
}
rewrite seq_nth. 2: {
  unfold Nat.b2n; rewrite if_leb_le_dec.
  destruct (le_dec j (v - 1)); flia Hv.
}
rewrite seq_nth. 2: {
  unfold Nat.b2n; rewrite if_leb_le_dec.
  destruct (le_dec i (u - 1)); flia Hu.
}
unfold mat_el'.
symmetry.
rewrite Nat.add_comm, Nat.add_sub.
rewrite (Nat.add_comm 1 (v - 1 + _)), Nat.add_sub.
easy.
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
rewrite (List_map_nth_seq (nth i (l :: ll) []) 0%F) at 1.
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

Theorem laplace_formula_on_cols : in_charac_0_field →
  ∀ (M : matrix T) j,
  is_square_matrix M = true
  → 1 ≤ j ≤ mat_ncols M
  → det M = ∑ (i = 1, mat_nrows M), mat_el' M i j * mat_el' (com M) i j.
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
cbn - [ det mat_el' ].
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
  → ∑ (j = 0, n), minus_one_pow (i + j) * M i j * det (subm M i j) = det M

determinant_with_bad_row
  ∀ (i k n : nat) (M : matrix (S n) (S n) T),
  i ≤ n → k ≤ n → i ≠ k
  → ∑ (j = 0, n), minus_one_pow (i + j) * M k j * det (subm M i j) = 0%F
*)

Theorem determinant_with_row : in_charac_0_field →
  ∀ i (M : matrix T),
  is_square_matrix M = true
  → 1 ≤ i ≤ mat_nrows M
  → det M =
    ∑ (j = 1, mat_nrows M),
    minus_one_pow (i + j) * mat_el' M i j * det (subm (i - 1) (j - 1) M).
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
assert (Hiz : i - 1 ≠ 0) by flia Hi1 Hir.
apply rngl_opp_inj; [ easy | ].
rewrite <- (determinant_alternating Hif M Hiz); [ | | | easy ]; cycle 1. {
  flia Hir.
} {
  flia Hir.
}
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
rewrite <- Nat.sub_succ_l; [ | easy ].
rewrite Nat_sub_succ_1.
f_equal.
rewrite rngl_mul_comm; [ | now destruct Hif ].
symmetry.
rewrite mat_swap_rows_comm.
replace (minus_one_pow i) with (- minus_one_pow (i - 1))%F. 2: {
  destruct i; [ easy | cbn ].
  rewrite Nat.sub_0_r.
  now rewrite minus_one_pow_succ.
}
rewrite <- determinant_subm_mat_swap_rows_0_i; try easy; cycle 1. {
  flia Hir Hiz.
} {
  flia Hj Hir.
}
unfold det.
rewrite mat_nrows_subm.
rewrite mat_swap_rows_nrows.
assert (H : 0 < mat_nrows M) by flia Hir.
now apply Nat.ltb_lt in H; rewrite H; clear H.
Qed.

Theorem determinant_with_bad_row : in_charac_0_field →
  ∀ i k (M : matrix T),
  is_square_matrix M = true
  → 1 ≤ i ≤ mat_nrows M
  → 1 ≤ k ≤ mat_nrows M
  → i ≠ k
  → ∑ (j = 1, mat_nrows M),
    minus_one_pow (i + j) * mat_el' M k j * det (subm (i - 1) (j - 1) M) = 0%F.
Proof.
intros Hif * Hsm Hir Hkr Hik.
specialize (square_matrix_ncols _ Hsm) as Hc.
remember
  (mk_mat
     (map
        (λ p,
         map (λ q, mat_el' M (if p =? i then k else p) q)
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
assert (H1 : det A = 0%F). {
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
(*
apply Nat.ltb_lt in Hir; rewrite Hir; cbn.
*)
f_equal; f_equal; f_equal.
rewrite HA; cbn.
destruct M as (ll); cbn in Hir, Hj |-*.
unfold mat_ncols; cbn.
(*
apply Nat.ltb_lt in Hir.
*)
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
  rewrite List_map_nth_seq with (d := 0%F) (la := nth u ll []).
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
  rewrite List_map_nth_seq with (la := nth u ll []) (d := 0%F) at 1.
  f_equal; f_equal; f_equal.
  apply Hcl, nth_In; flia Hu Hir.
} {
  rewrite <- (seq_shift _ i), map_map.
  apply map_ext_in.
  intros u Hu; apply in_seq in Hu.
  rewrite Nat_sub_succ_1.
  rewrite List_map_nth_seq with (d := 0%F) (la := nth u ll []).
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
  rewrite List_map_nth_seq with (la := nth u ll []) (d := 0%F) at 1.
  f_equal; f_equal; f_equal.
  apply Hcl, nth_In; flia Hu.
}
Qed.

Theorem mat_transp_subm : ∀ M i j,
  is_correct_matrix M = true
  → mat_nrows M ≠ 1
  → i < mat_ncols M
  → j < mat_nrows M
  → subm i j M⁺ = ((subm j i M)⁺)%M.
Proof.
intros * Hcm Hr1 Hic Hjr.
unfold mat_transp at 2.
unfold subm at 1.
f_equal.
rewrite mat_nrows_subm.
rewrite mat_ncols_subm; [ | easy ].
replace (mat_nrows M) with (S (S (mat_nrows M - 2))) at 1 by flia Hjr Hr1.
apply Nat.ltb_lt in Hic; rewrite Hic.
apply Nat.ltb_lt in Hjr; rewrite Hjr; cbn.
apply Nat.ltb_lt in Hic, Hjr.
rewrite map_butn, map_map, <- map_butn.
unfold butn at 2.
rewrite List_firstn_seq.
rewrite Nat.min_l; [ | flia Hic ].
destruct (Nat.eq_dec i (mat_ncols M - 1)) as [Hic1| Hic1]. {
  rewrite Hic1.
  rewrite skipn_all2; [ | rewrite seq_length; flia Hjr ].
  rewrite app_nil_r.
  apply map_ext_in.
  intros u Hu; apply in_seq in Hu.
  rewrite Nat.add_comm, Nat.sub_add in Hu; [ | flia Hic ].
  rewrite <- map_butn.
  unfold butn at 1.
  rewrite List_firstn_seq.
  rewrite Nat.min_l; [ | flia Hjr ].
  destruct (Nat.eq_dec j (mat_nrows M - 1)) as [Hjr1| Hjr1]. {
    rewrite Hjr1.
    rewrite skipn_all2; [ | rewrite seq_length; flia Hjr ].
    rewrite app_nil_r.
    apply map_ext_in.
    intros v Hv.
    rewrite map_butn.
    rewrite nth_butn.
    apply in_seq in Hv.
    rewrite Nat.add_comm, Nat.sub_add in Hv; [ | flia Hjr ].
    unfold Nat.b2n.
    rewrite if_leb_le_dec.
    destruct (le_dec (mat_nrows M - 1) (v - 1)) as [H| H]; [ flia Hv H | ].
    clear H.
    rewrite Nat.add_0_r.
    rewrite (List_map_nth' []); [ | rewrite fold_mat_nrows; flia Hv ].
    rewrite nth_butn.
    unfold Nat.b2n.
    rewrite if_leb_le_dec.
    destruct (le_dec (mat_ncols M - 1) (u - 1)) as [H| H]; [ flia Hu H | ].
    clear H.
    now rewrite Nat.add_0_r.
  }
  replace (mat_nrows M - 1) with (j + (mat_nrows M - 1 - j)) at 1. 2: {
    flia Hjr Hjr1.
  }
  rewrite seq_app.
  do 2 rewrite map_app.
  f_equal. {
    apply map_ext_in.
    intros v Hv; apply in_seq in Hv.
    rewrite (List_map_nth' []). 2: {
      rewrite butn_length, fold_mat_nrows.
      apply Nat.ltb_lt in Hjr; rewrite Hjr; cbn.
      apply Nat.ltb_lt in Hjr; flia Hv Hjr.
    }
    rewrite nth_butn.
    unfold Nat.b2n.
    rewrite if_leb_le_dec.
    destruct (le_dec (mat_ncols M - 1) (u - 1)) as [H| H]; [ flia Hu H | ].
    clear H.
    rewrite Nat.add_0_r.
    rewrite nth_butn.
    unfold Nat.b2n.
    rewrite if_leb_le_dec.
    destruct (le_dec j (v - 1)) as [H| H]; [ flia Hv H | ].
    clear H.
    now rewrite Nat.add_0_r.
  } {
    rewrite List_skipn_seq; [ | flia Hjr Hjr1 ].
    rewrite <- Nat.sub_add_distr.
    rewrite <- seq_shift, map_map.
    apply map_ext_in.
    intros v Hv; apply in_seq in Hv.
    destruct Hv as (Hjv, Hv).
    rewrite Nat.sub_add_distr in Hv.
    rewrite Nat.add_sub_assoc in Hv; [ | flia Hjr Hjr1 ].
    rewrite (List_map_nth' []). 2: {
      rewrite butn_length, fold_mat_nrows.
      unfold Nat.b2n.
      rewrite if_ltb_lt_dec.
      destruct (lt_dec j (mat_nrows M)) as [H| H]; [ flia H Hv Hjv | ].
      clear H.
      rewrite Nat.sub_0_r; flia Hv Hjv.
    }
    rewrite nth_butn.
    unfold Nat.b2n.
    rewrite if_leb_le_dec.
    destruct (le_dec (mat_ncols M - 1) (u - 1)) as [H| H]; [ flia Hu H | ].
    clear H.
    rewrite Nat.add_0_r.
    rewrite nth_butn.
    unfold Nat.b2n.
    rewrite if_leb_le_dec.
    destruct (le_dec j (v - 1)) as [H| H]; [ | flia Hv Hjv H ].
    rewrite Nat.sub_add; [ | flia Hjv ].
    unfold mat_el'.
    now rewrite Nat_sub_succ_1.
  }
}
replace (mat_ncols M - 1) with (i + (mat_ncols M - 1 - i)) at 1. 2: {
  flia Hic Hic1.
}
rewrite seq_app.
do 2 rewrite map_app.
f_equal. {
  apply map_ext_in.
  intros u Hu; apply in_seq in Hu.
  rewrite <- map_butn.
  unfold butn at 1.
  rewrite List_firstn_seq.
  rewrite Nat.min_l; [ | flia Hjr ].
  destruct (Nat.eq_dec j (mat_nrows M - 1)) as [Hjr1| Hjr1]. {
    rewrite Hjr1.
    rewrite skipn_all2; [ | rewrite seq_length; flia Hjr ].
    rewrite app_nil_r.
    apply map_ext_in.
    intros v Hv.
    rewrite map_butn.
    rewrite nth_butn.
    apply in_seq in Hv.
    rewrite Nat.add_comm, Nat.sub_add in Hv; [ | flia Hjr ].
    unfold Nat.b2n.
    rewrite if_leb_le_dec.
    destruct (le_dec (mat_nrows M - 1) (v - 1)) as [H| H]; [ flia Hv H | ].
    clear H.
    rewrite Nat.add_0_r.
    rewrite (List_map_nth' []); [ | rewrite fold_mat_nrows; flia Hv ].
    rewrite nth_butn.
    unfold Nat.b2n.
    rewrite if_leb_le_dec.
    destruct (le_dec i (u - 1)) as [H| H]; [ flia Hu H | ].
    clear H.
    now rewrite Nat.add_0_r.
  }
  replace (mat_nrows M - 1) with (j + (mat_nrows M - 1 - j)) at 1. 2: {
    flia Hjr Hjr1.
  }
  rewrite seq_app.
  do 2 rewrite map_app.
  f_equal. {
    apply map_ext_in.
    intros v Hv; apply in_seq in Hv.
    rewrite (List_map_nth' []). 2: {
      rewrite butn_length, fold_mat_nrows.
      apply Nat.ltb_lt in Hjr; rewrite Hjr; cbn.
      apply Nat.ltb_lt in Hjr; flia Hv Hjr.
    }
    rewrite nth_butn.
    unfold Nat.b2n.
    rewrite if_leb_le_dec.
    destruct (le_dec i (u - 1)) as [H| H]; [ flia Hu H | ].
    clear H.
    rewrite Nat.add_0_r.
    rewrite nth_butn.
    unfold Nat.b2n.
    rewrite if_leb_le_dec.
    destruct (le_dec j (v - 1)) as [H| H]; [ flia Hv H | ].
    now rewrite Nat.add_0_r.
  } {
    rewrite List_skipn_seq; [ | flia Hjr Hjr1 ].
    rewrite <- Nat.sub_add_distr.
    rewrite <- seq_shift, map_map.
    apply map_ext_in.
    intros v Hv; apply in_seq in Hv.
    destruct Hv as (Hjv, Hv).
    rewrite Nat.sub_add_distr in Hv.
    rewrite Nat.add_sub_assoc in Hv; [ | flia Hjr Hjr1 ].
    rewrite Nat.add_comm, Nat.add_assoc, Nat.add_sub in Hv.
    rewrite Nat.sub_add in Hv; [ | flia Hjr ].
    rewrite (List_map_nth' []). 2: {
      rewrite butn_length, fold_mat_nrows.
      apply Nat.ltb_lt in Hjr; rewrite Hjr.
      cbn; flia Hv Hr1.
    }
    rewrite nth_butn.
    unfold Nat.b2n.
    rewrite if_leb_le_dec.
    destruct (le_dec i (u - 1)) as [H| H]; [ flia Hu H | ].
    clear H.
    rewrite Nat.add_0_r.
    rewrite nth_butn.
    unfold Nat.b2n.
    rewrite if_leb_le_dec.
    destruct (le_dec j (v - 1)) as [H| H]; [ | flia H Hjv ].
    rewrite Nat.sub_add; [ | flia Hjv ].
    unfold mat_el'.
    now rewrite Nat_sub_succ_1.
  }
}
rewrite List_skipn_seq; [ | flia Hic Hic1 ].
rewrite <- Nat.sub_add_distr.
...
rewrite Nat.add_0_l, <- seq_shift, map_map.
apply map_ext_in.
intros u Hu; apply in_seq in Hu.
destruct Hu as (Hiu, Hu).
rewrite Nat.sub_add_distr in Hu.
rewrite Nat.add_sub_assoc in Hu; [ | flia Hic Hic1 ].
rewrite <- map_butn.
unfold butn at 1.
rewrite List_firstn_seq.
rewrite Nat.min_l; [ | flia Hjr ].
destruct (Nat.eq_dec j (mat_nrows M - 1)) as [Hjr1| Hjr1]. {
  rewrite Hjr1.
  rewrite skipn_all2; [ | rewrite seq_length; flia Hjr ].
  rewrite app_nil_r.
  apply map_ext_in.
  intros v Hv.
  rewrite map_butn.
  rewrite nth_butn.
  apply in_seq in Hv.
  destruct Hv as (_, Hv); cbn in Hv.
  apply Nat.leb_gt in Hv; rewrite Hv.
  apply Nat.leb_gt in Hv.
  rewrite Nat.add_0_r.
  rewrite (List_map_nth' []); [ | rewrite fold_mat_nrows; flia Hv ].
  rewrite nth_butn.
  apply Nat.leb_le in Hiu; rewrite Hiu.
  now rewrite Nat.add_1_r.
}
replace (mat_nrows M - 1) with (j + (mat_nrows M - 1 - j)) at 1. 2: {
  flia Hjr Hjr1.
}
rewrite seq_app, Nat.add_0_l.
do 2 rewrite map_app.
f_equal. {
  apply map_ext_in.
  intros v Hv; apply in_seq in Hv.
  destruct Hv as (_, Hv); cbn in Hv.
  rewrite (List_map_nth' []). 2: {
    rewrite butn_length, fold_mat_nrows.
    apply Nat.ltb_lt in Hjr; rewrite Hjr; cbn.
    apply Nat.ltb_lt in Hjr; flia Hv Hjr.
  }
  rewrite nth_butn.
  apply Nat.leb_le in Hiu; rewrite Hiu, Nat.add_1_r.
  rewrite nth_butn.
  apply Nat.leb_gt in Hv; rewrite Hv, Nat.add_0_r.
  easy.
} {
  rewrite List_skipn_seq; [ | flia Hjr Hjr1 ].
  rewrite <- Nat.sub_add_distr.
  rewrite Nat.add_0_l, <- seq_shift, map_map.
  apply map_ext_in.
  intros v Hv; apply in_seq in Hv.
  destruct Hv as (Hjv, Hv).
  rewrite Nat.sub_add_distr in Hv.
  rewrite Nat.add_sub_assoc in Hv; [ | flia Hjr Hjr1 ].
  rewrite Nat.add_comm, Nat.add_sub in Hv.
  rewrite (List_map_nth' []). 2: {
    rewrite butn_length, fold_mat_nrows.
    now apply Nat.ltb_lt in Hjr; rewrite Hjr.
  }
  rewrite nth_butn.
  apply Nat.leb_le in Hiu; rewrite Hiu, Nat.add_1_r.
  rewrite nth_butn.
  apply Nat.leb_le in Hjv; rewrite Hjv, Nat.add_1_r.
  easy.
}
Qed.

...

Theorem matrix_comatrix_transp_mul : in_charac_0_field →
  ∀ (M : matrix T),
  is_square_matrix M = true
  → (M * (com M)⁺ = det M × mI (mat_nrows M))%M.
Proof.
intros Hif * Hsm.
destruct M as (ll); cbn - [ det ].
unfold "*"%M, "×"%M, mat_nrows; cbn - [ det ]; f_equal.
rewrite map_map.
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
assert (Hll : 0 < length ll) by flia Hi.
rewrite laplace_formula_on_rows with (i := i); try easy.
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
apply map_ext_in.
intros j Hj; apply in_seq in Hj.
move j before i.
erewrite rngl_summation_eq_compat. 2: {
  intros k Hk.
  assert (Hkc : k < mat_ncols {| mat_list_list := ll |}). {
    unfold mat_ncols; cbn.
    rewrite Hcl; [ flia Hk Hll | ].
    now apply List_hd_in.
  }
  cbn - [ det ].
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite seq_nth; [ | easy ].
  do 2 rewrite Nat.add_0_l.
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
  rewrite (List_map_nth' 0); [ | now rewrite seq_length, seq_nth ].
  rewrite (List_map_nth' 0). 2: {
    unfold mat_ncols.
    rewrite seq_length; cbn.
    rewrite Hcl; [ flia Hk Hll | ].
    now apply List_hd_in.
  }
  rewrite seq_nth; [ | now rewrite seq_nth ].
  rewrite seq_nth; [ | easy ].
  rewrite seq_nth. 2: {
    unfold mat_ncols; rewrite Hcl; [ flia Hk Hll | ].
    now apply List_hd_in.
  }
  easy.
} {
  (* not on diagonal: zeroes *)
  rewrite δ_ndiag; [ | easy ].
  rewrite rngl_mul_0_r; [ | now destruct Hif; left ].
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
    rewrite (List_map_nth' 0); [ | now rewrite seq_length, comatrix_nrows ].
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
  apply determinant_with_bad_row; [ easy | | easy | easy | easy ].
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
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
unfold mat_ncols.
rewrite Hcl; [ | now apply List_hd_in ].
rewrite map_map.
apply map_ext_in.
intros j Hj; apply in_seq in Hj.
move j before i.
rewrite laplace_formula_on_cols with (j := j); [ | easy | easy | ]. 2: {
  now rewrite square_matrix_ncols.
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
  symmetry; f_equal; rewrite mat_transp_el; [ easy | ].
  apply squ_mat_is_corr.
  now apply comatrix_is_square.
} {
  (* not on diagonal: zeroes *)
  rewrite δ_ndiag; [ | easy ].
  rewrite rngl_mul_0_r; [ | now destruct Hif; left ].
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
    rewrite HM at 1.
    cbn - [ det ].
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hk Hlz ].
    rewrite (List_map_nth' 0). 2: {
      rewrite seq_length; unfold mat_ncols.
      rewrite Hcl; [ easy | ].
      now apply List_hd_in.
    }
    rewrite seq_nth; [ | flia Hk Hlz ].
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
  specialize (H1 i j (M⁺)%M).
  assert (Hsmt : is_square_matrix M⁺ = true). {
    now apply mat_transp_is_square.
  }
  specialize (H1 Hsmt).
  rewrite mat_transp_nrows in H1.
  rewrite square_matrix_ncols in H1; [ | easy ].
  specialize (H1 Hi Hj Hij).
  erewrite rngl_summation_eq_compat in H1. 2: {
    intros k Hk.
    destruct Hk as (_, Hk).
    rewrite <- determinant_transpose; [ | easy | ]. 2: {
      apply is_squ_mat_subm. {
        rewrite mat_transp_nrows, square_matrix_ncols; [ | easy ].
        flia Hk Hi.
      } {
        rewrite mat_transp_nrows, square_matrix_ncols; [ | easy ].
        flia Hk Hi.
      }
      now apply mat_transp_is_square.
    }
    rewrite mat_transp_subm; cycle 1. {
      now apply squ_mat_is_corr.
    } {
      subst M; unfold mat_nrows.
      destruct ll; [ easy | ].
      now destruct ll.
    } {
      subst M; unfold mat_ncols.
      destruct ll; [ easy | ].
      destruct ll; [ easy | ].
      cbn in Hi |-*.
      cbn - [ In ] in Hcl.
      rewrite Hcl; [ easy | now left ].
    } {
      flia Hk Hi.
    }
    rewrite mat_transp_involutive. 2: {
      apply subm_is_corr_mat; [ | now apply squ_mat_is_corr ].
      unfold mat_ncols; rewrite HM; cbn.
      rewrite Hcl; [ | now apply List_hd_in ].
      now rewrite HM.
    }
    rewrite mat_transp_el; [ | now apply squ_mat_is_corr ].
    rewrite Nat.add_comm.
    easy.
  }
  easy.
}
Qed.

Definition mat_inv (M : matrix T) := ((det M)⁻¹ × (com M)⁺)%M.

Theorem mat_mul_inv_r : in_charac_0_field →
  ∀ (M : matrix T),
  is_square_matrix M = true
  → det M ≠ 0%F
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
  → det M ≠ 0%F
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

Theorem minus_one_pow_mul_same :
  rngl_has_opp = true →
  ∀ i, (minus_one_pow i * minus_one_pow i = 1)%F.
Proof.
intros Hop *.
unfold minus_one_pow.
destruct (i mod 2); [ apply rngl_mul_1_l | ].
now apply rngl_squ_opp_1.
Qed.

(* to be completed
Theorem comatrix_mul :
  rngl_is_comm = true →
  rngl_has_opp = true →
  ∀ n A B,
  is_square_matrix A = true
  → is_square_matrix B = true
  → mat_nrows A = n
  → mat_nrows B = n
  → com (A * B) = (com A * com B)%M.
Proof.
intros Hic Hop * Hsma Hsmb Hra Hrb.
unfold mat_mul; cbn.
assert (Hca : mat_ncols A = n) by now rewrite square_matrix_ncols.
assert (Hcb : mat_ncols B = n) by now rewrite square_matrix_ncols.
rewrite Hra, Hca, Hcb.
unfold com at 1; cbn - [ det ].
do 2 rewrite List_map_seq_length.
rewrite comatrix_ncols, Hcb.
f_equal.
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
destruct Hi as (_, Hi); cbn in Hi.
unfold mat_ncols.
cbn - [ det ].
rewrite (List_map_hd 0); [ | rewrite seq_length; flia Hi ].
rewrite List_map_seq_length.
apply map_ext_in.
intros j Hj; apply in_seq in Hj.
destruct Hj as (_, Hj); cbn in Hj.
move j before i.
symmetry.
unfold mat_mul_el at 1.
rewrite comatrix_ncols, Hca.
unfold com at 1.
unfold com at 1.
cbn - [ det ].
rewrite Hra, Hrb, Hca, Hcb.
erewrite rngl_summation_eq_compat. 2: {
  intros u Hu.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hu Hi ].
  rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hu Hi ].
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite seq_nth; [ | flia Hu Hi ].
  rewrite seq_nth; [ | easy ].
  do 3 rewrite Nat.add_0_l.
  rewrite rngl_mul_mul_swap with (n0 := minus_one_pow (i + u)); [ | easy ].
  rewrite rngl_mul_assoc.
  rewrite minus_one_pow_add_r; [ | easy ].
  rewrite minus_one_pow_add_r; [ | easy ].
  rewrite rngl_mul_assoc.
  rewrite <- rngl_mul_assoc with (a := minus_one_pow i).
  rewrite minus_one_pow_mul_same; [ | easy ].
  rewrite rngl_mul_1_r.
  rewrite <- minus_one_pow_add_r; [ | easy ].
  rewrite rngl_mul_mul_swap; [ | easy ].
  rewrite <- rngl_mul_assoc.
  easy.
}
cbn - [ det ].
rewrite <- rngl_mul_summation_distr_l; [ | now left ].
f_equal.
remember (mat_mul A B) as C eqn:HC.
generalize HC; intros H.
unfold mat_mul in H.
rewrite Hcb, Hra in H.
rewrite <- H, HC; clear C HC H.
symmetry.
(* lemma, perhaps? *)
(*1
rewrite det_is_det'.
erewrite rngl_summation_eq_compat. 2: {
  intros u (_, Hu).
  rewrite det_is_det'.
  rewrite det_is_det'.
  do 2 rewrite mat_nrows_subm.
  rewrite Hra, Hrb.
  apply Nat.ltb_lt in Hi; rewrite Hi.
  assert (H : u < n) by flia Hu Hj.
  apply Nat.ltb_lt in H; rewrite H.
  now cbn.
  admit.
  admit.
  admit.
  admit.
}
cbn.
rewrite map_length.
rewrite <- map_butn.
rewrite map_butn_seq.
rewrite map_length.
rewrite seq_length.
rewrite Hra.
apply Nat.ltb_lt in Hi; rewrite Hi; cbn.
apply Nat.ltb_lt in Hi.
cbn.
Print det'.
...
  ============================
  det' (n - 1) (subm (A * B) i j) = ∑ (i0 = 0, n - 1), det' (n - 1) (subm A i i0) * det' (n - 1) (subm B i0 j)
1*)
cbn.
rewrite map_length.
rewrite <- map_butn.
rewrite map_butn_seq.
rewrite map_length.
rewrite seq_length.
rewrite Hra.
apply Nat.ltb_lt in Hi; rewrite Hi; cbn.
apply Nat.ltb_lt in Hi.
erewrite rngl_summation_eq_compat. 2: {
  intros u (_, Hu).
  do 2 rewrite map_length.
  do 2 rewrite butn_length.
  do 2 rewrite fold_mat_nrows.
  rewrite Hra, Hrb.
  apply Nat.ltb_lt in Hi; rewrite Hi.
  assert (H : u < n) by flia Hu Hj.
  apply Nat.ltb_lt in H; rewrite H.
  now cbn.
}
cbn.
(*
  ============================
  determinant_loop (n - 1) (subm (A * B) i j) =
  ∑ (i0 = 0, n - 1), determinant_loop (n - 1) (subm A i i0) * determinant_loop (n - 1) (subm B i0 j)
*)
...
j'abandonne parce que ce théorème essaie de prouver com(A*B)=com(A)*com(B) dans
le but lointain de prouver det(A*B)=det(A)*det(B), sauf que com fait déjà
intervenir det ; c'est donc peut-être une mauvaise piste
...
destruct n. {
  cbn.
  rewrite rngl_summation_only_one.
  symmetry.
  apply rngl_mul_1_l.
}
rewrite Nat_sub_succ_1.
induction n. {
  cbn.
  rewrite rngl_summation_only_one.
  symmetry.
  apply rngl_mul_1_l.
}
Search (determinant_loop (S _)).
rewrite determinant_succ.
...
rewrite subm_mat_swap_rows_circ; [ | easy ].
destruct i; [ flia Hiz | ].
rewrite minus_one_pow_succ; [ | easy ].
rewrite rngl_opp_involutive; [ | easy ].
rewrite Nat_sub_succ_1.
rewrite subm_fold_left_lt; [ | flia ].
apply determinant_circular_shift_rows; [ easy | | ]. {
  rewrite mat_nrows_subm.
  apply Nat.ltb_lt in Hin; rewrite Hin; cbn.
  apply Nat.ltb_lt in Hin; flia Hin.
}
apply is_squ_mat_subm; [ flia Hin | flia Hjn | easy ].
...
*)

End a.

Arguments com {T}%type {ro} M%M.
Arguments mat_mul_inv_r {T}%type {ro rp} Hof M%F.
Arguments mat_inv {T}%type {ro} M%M.
Arguments laplace_formula_on_rows {T}%type {ro rp} Hif M%M [i]%nat.
Arguments laplace_formula_on_cols {T}%type {ro rp} Hif M%M [j]%nat.

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
