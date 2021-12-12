(* comatrices *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Misc RingLike IterAdd IterMul Pigeonhole.
Require Import Matrix PermutSeq Signature.
Require Import Determinant.
Import matrix_Notations.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

Definition comatrix (M : matrix T) : matrix T :=
  mk_mat
    (map
      (λ i,
       map (λ j, (minus_one_pow (i + j) * determinant (subm M i j))%F)
         (seq 0 (mat_ncols M)))
      (seq 0 (mat_nrows M))).

Arguments comatrix M%M.

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
  → subm (mat_swap_rows p q M) r j = mat_swap_rows p q (subm M r j).
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
  → subm (mat_swap_rows p q M) r j = mat_swap_rows p q (subm M r j).
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
  → mat_el (mat_swap_rows p q M) q j = mat_el M p j.
Proof.
intros * Hql; cbn.
destruct M as (ll); cbn in Hql |-*.
f_equal; clear j.
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
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

Theorem nth_0_fold_left_cons_cons : ∀ A B (b : A) (la : list B) lb lc d f,
  nth 0 (fold_left (λ v i, nth 0 v d :: f v i) la (b :: lb)) lc = b.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
now rewrite IHla.
Qed.

Theorem nth_0_fold_left_nth_transp: ∀ A (b : A) lb d f n,
  nth 0
    (fold_left
       (λ v i, nth (transposition i (i + 1) 0) v d :: f v i) (seq 0 (S n))
       (b :: lb))
    d = nth 0 lb d.
Proof.
intros; cbn.
rewrite <- seq_shift.
rewrite List_fold_left_map; cbn.
now rewrite nth_0_fold_left_cons_cons.
Qed.

Theorem nth_succ_fold_left_app_cons : ∀ A B n (b : A) (la : list B) lb d f g,
  length lb = S n
  → (∀ v i, length (g v i) = n)
  → nth (S n)
       (fold_left (λ v i, f v i :: g v i ++ [nth (S n) v d]) la (b :: lb)) d =
    nth n lb d.
Proof.
intros * Hlb Hf.
revert b lb Hlb Hf.
induction la as [| a]; intros; [ easy | cbn ].
rewrite IHla; [ | | apply Hf ]. 2: {
  rewrite app_length; cbn.
  rewrite Nat.add_1_r; f_equal.
  apply Hf.
}
rewrite app_nth2; [ | now unfold "≥"; rewrite Hf ].
now rewrite Hf, Nat.sub_diag.
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
  rewrite IHlen; [ | now rewrite map_length, seq_length ].
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
  → subm (mat_swap_rows 0 p M) 0 q =
    subm (fold_left (λ M' k, mat_swap_rows k (k + 1) M') (seq 0 (p - 1)) M)
      p q.
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
  → subm
      (fold_left (λ M' k, mat_swap_rows k (k + 1) M')
         (seq 0 m) M) i j =
    fold_left
      (λ M' k, mat_swap_rows k (k + 1) M')
      (seq 0 m) (subm M i j).
Proof.
intros * Hmi.
revert i Hmi.
induction m; intros; [ easy | ].
rewrite seq_S; cbn.
do 2 rewrite fold_left_app; cbn.
rewrite <- IHm; [ | flia Hmi ].
apply subm_mat_swap_rows_lt; flia Hmi.
Qed.

Theorem determinant_circular_shift_rows : in_field →
  ∀ (M : matrix T) i,
  i < mat_nrows M
  → is_square_matrix M = true
  → determinant (fold_left (λ M' k, mat_swap_rows k (k + 1) M') (seq 0 i) M) =
    (minus_one_pow i * determinant M)%F.
Proof.
intros (Hic & Hop & Hiv & H10 & Hit & Hde & Hch) * Hin Hsm.
remember (mat_nrows M) as n eqn:Hr; symmetry in Hr.
revert M Hsm Hr.
induction i; intros; [ now cbn; rewrite rngl_mul_1_l | ].
assert (H : i < n) by flia Hin.
specialize (IHi H); clear H.
rewrite seq_S; cbn.
rewrite fold_left_app; cbn - [ determinant ].
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

Theorem determinant_subm_mat_swap_rows_0_i : in_field →
  ∀ (M : matrix T) i j,
  is_square_matrix M = true
  → 0 < i < mat_nrows M
  → j < mat_nrows M
  → determinant (subm (mat_swap_rows 0 i M) 0 j) =
    (- minus_one_pow i * determinant (subm M i j))%F.
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

Theorem laplace_formula_on_rows : in_field →
  ∀ (M : matrix T) i,
  is_square_matrix M = true
  → i < mat_nrows M
  → determinant M =
    ∑ (j = 0, mat_nrows M - 1), mat_el M i j * mat_el (comatrix M) i j.
Proof.
intros Hif * Hsm Hlin.
specialize (square_matrix_ncols M Hsm) as Hc.
specialize (proj1 (is_scm_mat_iff _ M) Hsm) as H1.
destruct H1 as (Hcr & Hc').
destruct (Nat.eq_dec (mat_nrows M) 0) as [Hnz| Hnz]. {
  now rewrite Hnz in Hlin.
}
destruct (Nat.eq_dec i 0) as [Hiz| Hiz]. {
  subst i; cbn.
  symmetry.
  unfold determinant.
  replace (mat_nrows M) with (S (mat_nrows M - 1)) by flia Hnz.
  cbn - [ butn ]; rewrite Nat.sub_0_r.
  apply rngl_summation_eq_compat.
  intros j Hj.
  destruct Hif as (Hic & Hop & Hin & H10 & Hit & Hde & Hch).
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_mul_swap; [ | easy ].
  rewrite (List_map_nth' 0); [ | rewrite seq_length, Hc; flia Hj Hnz ].
  rewrite seq_nth; [ | rewrite Hc; flia Hj Hnz ].
  rewrite map_length.
  f_equal; f_equal.
  rewrite butn_length, fold_mat_nrows.
  apply Nat.neq_0_lt_0, Nat.ltb_lt in Hnz.
  now rewrite Hnz.
}
unfold determinant.
replace (mat_nrows M) with (S (mat_nrows M - 1)) by flia Hnz.
cbn; rewrite Nat.sub_0_r.
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  destruct Hif as (Hic & Hop & Hin & H10 & Hit & Hde & Hch) in Hj.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
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
remember (mat_swap_rows 0 p M) as M'.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite map_length, butn_length, fold_mat_nrows.
  rewrite rngl_mul_mul_swap; [ | now destruct Hif ].
  rewrite Nat.add_comm.
  rewrite minus_one_pow_add_r; [ | now destruct Hif ].
  do 2 rewrite <- rngl_mul_assoc.
  rewrite rngl_mul_comm; [ | now destruct Hif ].
  rewrite rngl_mul_assoc.
  remember (minus_one_pow p * _)%F as x eqn:Hx.
  rewrite <- rngl_opp_involutive in Hx; [ | now destruct Hif ].
  rewrite <- rngl_mul_opp_l in Hx; [ | now destruct Hif ].
  specialize determinant_subm_mat_swap_rows_0_i as H1.
  specialize (H1 Hif).
  specialize (H1 M p j Hsm).
  cbn - [ butn ] in H1.
  rewrite map_length, map_butn, butn_length in H1.
  rewrite length_list_swap_elem, fold_mat_nrows in H1.
  rewrite butn_length, map_length, fold_mat_nrows in H1.
  apply Nat.neq_0_lt_0, Nat.ltb_lt in Hnz.
  rewrite Hnz in H1; cbn - [ "<?" ] in H1.
  apply Nat.ltb_lt in Hnz.
  rewrite <- H1 in Hx; [ | flia Hiz Hlin | flia Hj Hnz ].
  subst x; clear H1.
  rewrite rngl_mul_comm; [ | now destruct Hif ].
  rewrite rngl_mul_assoc, rngl_mul_mul_swap; [ | now destruct Hif ].
  replace (mat_el M p j) with (mat_el (mat_swap_rows 0 p M) 0 j). 2: {
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
do 2 rewrite <- determinant_succ.
subst M'.
rewrite <- rngl_opp_involutive; [ | now destruct Hif ].
f_equal.
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1.
rewrite fold_determinant.
apply Nat.neq_sym in Hiz.
apply Nat.neq_0_lt_0 in Hnz.
rewrite <- (determinant_alternating Hif M Hiz); [ | easy | easy | easy ].
unfold determinant.
now rewrite mat_swap_rows_nrows.
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
   if lt_dec i (ff_app (permut_list_inv σ) (S n)) then i else i + 1).
set (σ' := map (λ i, ff_app σ (g i)) (seq 0 (S n))).
assert (Hσ'l : length σ' = S n). {
  now unfold σ'; rewrite map_length, seq_length.
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
    rewrite (permut_inv_permut (S (S n))) in His; [ | easy | flia Hi ].
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
    rewrite (permut_inv_permut (S (S n))) in His; [ | easy | flia Hi ].
    now apply His.
  }
}
move Hs' before Hs.
specialize (IHn Hs').
assert (H : ∀ i j, i < S n → j < S n → ff_app σ' i = ff_app σ' j → i = j). {
  intros i j Hi Hj Hij; unfold σ', ff_app in Hij.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  do 2 rewrite Nat.add_0_l in Hij.
  unfold g in Hij; cbn in Hij.
  rewrite Hσl in Hinj.
  destruct (lt_dec i _) as [His| His]. {
    destruct (lt_dec j _) as [Hjs| Hjs]. {
      apply Hinj in Hij; [ easy | flia Hi | flia Hj ].
    }
    rewrite Nat.add_1_r in Hij.
    apply Nat.nlt_ge in Hjs.
    apply Hinj in Hij; [ flia His Hjs Hij | flia Hi | ].
    now apply -> Nat.succ_lt_mono.
  }
  apply Nat.nlt_ge in His.
  rewrite Nat.add_1_r in Hij.
  destruct (lt_dec j _) as [Hjs| Hjs]. {
    apply Hinj in Hij; [ flia His Hjs Hij | | flia Hj ].
    now apply -> Nat.succ_lt_mono.
  }
  rewrite Nat.add_1_r in Hij.
  apply Nat.succ_lt_mono in Hi, Hj.
  apply Hinj in Hij; [ | easy | easy ].
  now apply Nat.succ_inj in Hij.
}
specialize (IHn H eq_refl); clear H.
remember (ff_app (permut_list_inv σ) (S n)) as k eqn:Hk.
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
  now apply (permut_permut_inv (S (S n))).
}
specialize permut_list_inv_is_permut_list as H1.
specialize (H1 σ).
assert (H : is_permut_list σ) by easy.
specialize (H1 H); clear H.
rewrite rngl_product_split with (j := k) in IHn. 2: {
  split; [ flia | ].
  destruct H1 as (H1 & H2).
  apply -> Nat.succ_le_mono.
  rewrite length_permut_list_inv, Hσl in H1.
  specialize (H1 k).
  assert (H : k ∈ permut_list_inv σ). {
    rewrite Hk.
    apply nth_In.
    now rewrite length_permut_list_inv, Hσl.
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
    now apply (permut_permut_inv (S (S n))).
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
    assert (H : k ∈ permut_list_inv σ). {
      rewrite Hk; unfold ff_app.
      apply nth_In.
      now rewrite length_permut_list_inv, Hσl.
    }
    specialize (H1 H); clear H.
    rewrite length_permut_list_inv, Hσl in H1.
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
  rewrite length_permut_list_inv, Hσl in H1.
  apply Nat.lt_le_incl.
  apply H1, nth_In.
  now rewrite length_permut_list_inv, Hσl.
}
do 2 rewrite <- rngl_mul_assoc.
f_equal.
rewrite rngl_product_split_last. 2: {
  rewrite Nat.add_1_r, Hk.
  destruct H1 as (H1, H2).
  rewrite length_permut_list_inv, Hσl in H1.
  apply Nat.lt_succ_r.
  apply H1, nth_In.
  now rewrite length_permut_list_inv, Hσl.
}
rewrite rngl_product_succ_succ' with (g0 := λ i, f (ff_app σ i)).
rewrite rngl_product_split_first. 2: {
  rewrite Nat.add_1_r.
  destruct H1 as (H1, H2).
  rewrite length_permut_list_inv, Hσl in H1.
  specialize (H1 (S k)).
  assert (H : S k ∈ permut_list_inv σ). {
    rewrite Hk.
    apply nth_In.
    now rewrite length_permut_list_inv, Hσl.
  }
  specialize (H1 H); clear H.
  flia Hksn H1.
}
replace (ff_app σ (k + 1)) with (S n). 2: {
  rewrite Nat.add_1_r.
  rewrite Hk.
  symmetry.
  now apply (permut_permut_inv (S (S n))).
}
rewrite <- rngl_mul_assoc.
rewrite rngl_mul_comm; [ | easy ].
rewrite rngl_mul_assoc.
f_equal.
destruct
  (Nat.eq_dec (ff_app (permut_list_inv σ) (S n)) n) as [H7| H7]. {
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
  rewrite length_permut_list_inv, Hσl in H1.
  specialize (H1 (S k)).
  assert (H : S k ∈ permut_list_inv σ). {
    rewrite Hk.
    apply nth_In.
    now rewrite length_permut_list_inv, Hσl.
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

Theorem permut_comp_assoc : ∀ n f g h,
  length g = n
  → is_permut n h
  → (f ° (g ° h) = (f ° g) ° h)%F.
Proof.
intros * Hg (Hph, Hh).
unfold "°", comp_list; cbn.
rewrite map_map.
apply map_ext_in.
intros i Hi.
unfold ff_app.
rewrite (List_map_nth' 0); [ easy | ].
rewrite Hg, <- Hh.
now apply Hph.
Qed.

Theorem List_find_nth_not_None : ∀ n l i,
  is_permut n l
  → i < n
  → List_find_nth (Nat.eqb i) l ≠ None.
Proof.
intros n f i (Hs, Hf) Hi Hx.
specialize (List_find_nth_None 0 _ _ Hx) as H1; cbn.
specialize (pigeonhole_list n (i :: f)) as H2.
rewrite List_length_cons in H2.
assert (H : n < S (length f)) by now rewrite Hf.
specialize (H2 H); clear H.
assert (H : ∀ x, x ∈ i :: f → x < n). {
  intros x [Hxi| Hxf]; [ now subst x | ].
  now rewrite <- Hf; apply Hs.
}
specialize (H2 H); clear H.
remember (pigeonhole_comp_list (i :: f)) as xx eqn:Hxx.
symmetry in Hxx.
destruct xx as (x, x').
specialize (H2 x x' eq_refl).
destruct H2 as (Hxf & Hx'f & Hxx' & Hxx'if).
destruct x. {
  rewrite List_nth_0_cons in Hxx'if.
  destruct x'; [ easy | ].
  apply Nat.succ_lt_mono in Hx'f.
  cbn in Hxx'if.
  specialize (H1 x' Hx'f).
  now apply Nat.eqb_neq in H1.
}
rewrite List_nth_succ_cons in Hxx'if.
destruct x'. {
  apply Nat.succ_lt_mono in Hxf.
  cbn in Hxx'if; symmetry in Hxx'if.
  specialize (H1 x Hxf).
  now apply Nat.eqb_neq in H1.
}
cbn in Hxx'if.
apply Nat.succ_lt_mono in Hxf, Hx'f.
apply Hs in Hxx'if; [ | easy | easy ].
now rewrite Hxx'if in Hxx'.
Qed.

Theorem comp_permut_permut_inv : ∀ n f,
  is_permut n f
  → (f ° permut_list_inv f = seq 0 n).
Proof.
intros * Hf.
unfold "°"; cbn.
unfold permut_list_inv.
rewrite map_map.
rewrite (List_map_nth_seq (seq 0 n)) with (d := 0).
rewrite seq_length.
destruct Hf as (Hs, Hf).
rewrite Hf.
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
rewrite seq_nth; [ | easy ].
rewrite Nat.add_0_l.
remember (List_find_nth (Nat.eqb i) f) as x eqn:Hx.
symmetry in Hx.
destruct x as [x| ]. {
  apply (List_find_nth_Some 0) in Hx; cbn.
  destruct Hx as (Hx & Hbef & Hix).
  now apply Nat.eqb_eq in Hix.
} {
  exfalso.
  revert Hx.
  now apply (List_find_nth_not_None (conj Hs Hf)).
}
Qed.

Theorem comp_permut_inv_permut : ∀ n f,
  is_permut n f
  → (permut_list_inv f ° f = seq 0 n).
Proof.
intros * Hf.
unfold "°"; cbn.
rewrite (List_map_nth_seq f) with (d := 0) at 2.
rewrite (List_map_nth_seq (seq 0 n)) with (d := 0).
rewrite (proj2 Hf).
rewrite seq_length.
rewrite map_map.
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
destruct Hi as (_, Hi); cbn in Hi.
rewrite seq_nth; [ | easy ].
now apply (permut_inv_permut n).
Qed.

Theorem comp_id_l : ∀ n l, (∀ i, i ∈ l → i < n) → seq 0 n ° l = l.
Proof.
intros * Hn.
unfold "°".
unfold ff_app.
erewrite map_ext_in. 2: {
  intros i Hi.
  rewrite seq_nth; [ | now apply Hn ].
  now rewrite Nat.add_0_l.
}
apply map_id.
Qed.

Theorem comp_id_r : ∀ n l, length l = n → l ° seq 0 n = l.
Proof.
intros * Hn.
now symmetry; apply List_map_nth_seq'.
Qed.

Theorem det_by_any_sym_gr : in_field →
  ∀ n (M : matrix T) (sg : list (list nat)),
  n ≠ 0
  → mat_nrows M = n
  → is_square_matrix M = true
  → is_sym_gr_list n sg
  → determinant M =
    ∑ (k = 0, n! - 1),
    ε n (nth k sg []) *
    ∏ (i = 1, n), mat_el M (i - 1) (ff_app (nth k sg []) (i - 1)).
Proof.
intros Hif * Hnz Hr Hsm Hsg.
rewrite det_is_det_by_canon_permut; [ | easy | easy ].
unfold determinant'.
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
  apply canon_sym_gr_inv_of_canon_sym_gr.
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
  rewrite permut_in_canon_sym_gr_of_its_rank. 2: {
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
apply rngl_summation_list_permut.
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | apply Nat.neq_0_lt_0, fact_neq_0 ].
rewrite Nat_sub_succ_1.
apply permut_list_Permutation.
(* lemma to do? *)
unfold h.
split; [ | now rewrite map_length, seq_length ].
split. {
  intros i Hi.
  rewrite map_length, seq_length.
  apply in_map_iff in Hi.
  destruct Hi as (j & Hji & Hj).
  apply in_seq in Hj.
  rewrite <- Hji.
  rewrite <- sym_gr_size with (sg := sg); [ | easy ].
  now apply (sym_gr_inv_lt _ Hnz).
} {
  rewrite map_length, seq_length.
  intros i j Hi Hj Hij.
  unfold ff_app in Hij.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
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
split; [ | now rewrite map_length, seq_length ].
split. {
  intros i Hi.
  apply in_map_iff in Hi.
  destruct Hi as (j & Hji & Hj).
  apply in_seq in Hj.
  rewrite map_length, seq_length.
  rewrite <- Hji.
  destruct Hσ as (H1, H2).
  rewrite <- H2 in Hj |-*.
  now apply permut_list_ub.
} {
  rewrite map_length, seq_length.
  intros i j Hi Hj Hij.
  apply NoDup_nth in Hij; [ easy | | | ]; cycle 1. {
    now rewrite map_length, seq_length.
  } {
    now rewrite map_length, seq_length.
  }
  apply (NoDup_map_iff 0).
  rewrite seq_length.
  intros u v Hu Hv Huv.
  rewrite seq_nth in Huv; [ | easy ].
  rewrite seq_nth in Huv; [ | easy ].
  do 2 rewrite Nat.add_0_l in Huv.
  apply Hσ; [ destruct Hσ; congruence | destruct Hσ; congruence | easy ].
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
rewrite rngl_product_list_permut with (l2 := seq 0 n); [ | easy | ]. 2: {
  apply permut_list_Permutation.
  now apply map_permut_seq_is_permut.
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
  rewrite map_length.
  intros i j Hi Hj Hij.
  apply NoDup_nth in Hij; [ easy | | | ]; cycle 1. {
    now rewrite map_length.
  } {
    now rewrite map_length.
  }
  apply (NoDup_map_iff 0).
  intros u v Hu Hv Huv.
  apply Hl1 in Huv; cycle 1. {
    rewrite Hl2, <- Hσ2.
    now apply Hσ1, nth_In.
  } {
    rewrite Hl2, <- Hσ2.
    now apply Hσ1, nth_In.
  }
  now apply Hσ1 in Huv.
}
Qed.

Theorem permut_list_inv_inj2 : ∀ l1 l2,
  is_permut_list l1
  → is_permut_list l2
  → permut_list_inv l1 = permut_list_inv l2
  → l1 = l2.
Proof.
intros * Hpl1 Hpl2 Hill.
assert (Hll : length l1 = length l2). {
  apply List_eq_iff in Hill.
  now do 2 rewrite length_permut_list_inv in Hill.
}
apply (f_equal (comp_list l1)) in Hill.
rewrite (@comp_permut_permut_inv (length l1)) in Hill; [ | easy ].
apply (f_equal (λ l, comp_list l l2)) in Hill.
rewrite <- (@permut_comp_assoc (length l2)) in Hill; [ | | easy ]. 2: {
  apply length_permut_list_inv.
}
rewrite (@comp_permut_inv_permut (length l2)) in Hill; [ | easy ].
rewrite comp_id_r in Hill; [ | easy ].
rewrite comp_id_l in Hill; [ easy | ].
rewrite Hll.
apply Hpl2.
Qed.

Theorem permut_list_inv_comp : ∀ n l1 l2,
  is_permut n l1
  → is_permut n l2
  → permut_list_inv (l1 ° l2) = permut_list_inv l2 ° permut_list_inv l1.
Proof.
intros * Hnl1 Hnl2.
unfold "°".
unfold permut_list_inv; cbn.
rewrite map_length.
rewrite map_map.
destruct Hnl1 as (Hp1, Hl1).
destruct Hnl2 as (Hp2, Hl2).
rewrite Hl2, <- Hl1.
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
unfold ff_app.
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  unfold unsome.
  remember (List_find_nth _ _) as x eqn:Hx.
  symmetry in Hx.
  destruct x as [x| ]. {
    apply (List_find_nth_Some 0) in Hx.
    destruct Hx as (Hxσ & Hbefx & Hx).
    congruence.
  }
  flia Hi.
}
remember (List_find_nth _ _) as x eqn:Hx.
remember (List_find_nth _ l2) as y eqn:Hy.
symmetry in Hx, Hy.
destruct x as [x| ]. {
  apply (List_find_nth_Some 0) in Hx.
  rewrite map_length in Hx.
  destruct Hx as (Hxl & Hbefx & Hx).
  apply Nat.eqb_eq in Hx.
  rewrite (List_map_nth' 0) in Hx; [ | easy ].
  destruct y as [y| ]. {
    apply (List_find_nth_Some 0) in Hy.
    destruct Hy as (Hyl & Hbefy & Hy).
    apply Nat.eqb_eq in Hy.
    unfold unsome in Hy.
    remember (List_find_nth (Nat.eqb i) l1) as z eqn:Hz.
    symmetry in Hz.
    destruct z as [z| ]. {
      apply (List_find_nth_Some 0) in Hz.
      destruct Hz as (Hzl & Hbefz & Hz).
      apply Nat.eqb_eq in Hz.
      rewrite seq_nth in Hy; [ | congruence ].
      rewrite Nat.add_0_l in Hy.
      rewrite Hx in Hz.
      apply Hp1 in Hz; [ | | easy ]. 2: {
        rewrite Hl1, <- Hl2.
        now apply Hp2, nth_In.
      }
      rewrite Hy in Hz.
      apply Hp2 in Hz; [ | easy | easy ].
      easy.
    }
    rewrite seq_nth in Hy; [ | flia Hi ].
    specialize (List_find_nth_None 0 _ _ Hz) as H1.
    specialize (H1 (nth x l2 0)).
    assert (H : nth x l2 0 < length l1). {
      rewrite Hl1, <- Hl2.
      apply Hp2.
      now apply (nth_In _ 0).
    }
    specialize (H1 H); clear H.
    now apply Nat.eqb_neq in H1.
  }
  exfalso.
  revert Hy.
  apply (@List_find_nth_not_None n); [ easy | ].
  unfold unsome.
  remember (List_find_nth (Nat.eqb i) l1) as z eqn:Hz.
  symmetry in Hz.
  destruct z as [z| ]. {
    apply (List_find_nth_Some 0) in Hz.
    destruct Hz as (Hzl & Hbefz & Hz).
    rewrite seq_nth; [ | easy ].
    now rewrite Hl1 in Hzl.
  }
  rewrite seq_nth; [ flia Hl2 Hxl | flia Hi ].
}
exfalso.
revert Hx.
apply (@List_find_nth_not_None n); [ | now rewrite <- Hl1 ].
now apply map_ff_app_permut_permut_is_permut.
Qed.

Theorem permut_list_inv_involutive : ∀ l,
  is_permut_list l
  → permut_list_inv (permut_list_inv l) = l.
Proof.
intros * Hl.
unfold permut_list_inv.
rewrite map_length, seq_length.
rewrite List_map_nth_seq with (d := 0).
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
remember (List_find_nth _ _) as x eqn:Hx; symmetry in Hx.
destruct x as [x| ]. {
  apply (List_find_nth_Some 0) in Hx.
  rewrite map_length, seq_length in Hx.
  destruct Hx as (Hxl & Hbefx & Hx).
  rewrite (List_map_nth' 0) in Hx; [ | now rewrite seq_length ].
  rewrite seq_nth in Hx; [ | easy ].
  rewrite Nat.add_0_l in Hx.
  apply Nat.eqb_eq in Hx.
  unfold unsome in Hx.
  remember (List_find_nth (Nat.eqb x) l) as y eqn:Hy.
  symmetry in Hy.
  destruct y as [y| ]. {
    subst y.
    apply (List_find_nth_Some 0) in Hy.
    destruct Hy as (Hyl & Hbefy & Hy).
    now apply Nat.eqb_eq in Hy.
  }
  exfalso.
  revert Hy.
  apply (@List_find_nth_not_None (length l)); [ | easy ].
  easy.
}
exfalso.
revert Hx.
apply (@List_find_nth_not_None (length l)); [ | easy ].
now apply permut_list_inv_is_permut.
Qed.

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

Theorem mat_transp_is_square : ∀ M,
  is_square_matrix M = true
  → is_square_matrix M⁺ = true.
Proof.
intros * Hsm.
specialize (square_matrix_ncols _ Hsm) as Hc.
apply is_scm_mat_iff in Hsm.
apply is_scm_mat_iff.
destruct Hsm as (Hcr & Hcl).
cbn; rewrite map_length, seq_length.
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

Theorem det_any_permut_l : in_field →
  ∀ n (M : matrix T) (σ : list nat),
  n ≠ 0
  → mat_nrows M = n
  → is_square_matrix M = true
  → is_permut n σ
  → determinant M =
    (∑ (μ ∈ canon_sym_gr_list_list n), ε n μ * ε n σ *
     ∏ (k = 0, n - 1), mat_el M (ff_app σ k) (ff_app μ k))%F.
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
  remember (μ ° permut_list_inv σ) as ν eqn:Hν.
  assert (Hσν : ν ° σ = μ). {
    rewrite Hν.
    assert (H : length (permut_list_inv σ) = n). {
      rewrite length_permut_list_inv; apply Hσ.
    }
    rewrite <- (permut_comp_assoc _ _ H Hσ); clear H.
    rewrite (@comp_permut_inv_permut n); [ | easy ].
    apply comp_id_r, Hpμ.
  }
  subst ν.
  rewrite <- Hσν at 1.
  replace (ε n ((μ ° permut_list_inv σ) ° σ)) with
      (ε n (μ ° permut_list_inv σ) * ε n σ)%F. 2: {
    destruct Hσ.
    rewrite <- signature_comp; try easy.
    apply comp_is_permut; [ easy | ].
    now apply permut_list_inv_is_permut.
  }
  rewrite <- (rngl_mul_assoc _ (ε n σ) (ε n σ)).
  replace (ε n σ * ε n σ)%F with 1%F by now symmetry; apply ε_square.
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
      (g := ff_app (permut_list_inv σ)) (h := ff_app σ). 2: {
    intros j (_, Hj).
    apply (@permut_inv_permut n); [ easy | ].
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
    rewrite (@permut_permut_inv n); [ | easy | ]. 2: {
      rewrite <- Hkj.
      destruct Hσ as (H1, H2).
      rewrite <- H2 in Hk |-*.
      now apply permut_list_ub.
    }
    easy.
  }
  cbn.
  rewrite rngl_product_map_permut; [ | now destruct Hif | easy ].
  easy.
}
cbn.
set (sg := map (λ k, canon_sym_gr_list n k ° permut_list_inv σ) (seq 0 n!)).
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
    replace (ff_app _ _) with (ff_app (nth k sg []) (i - 1)). 2: {
      unfold sg.
      rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
      rewrite seq_nth; [ | easy ].
      rewrite Nat.add_0_l.
      unfold "°".
      unfold ff_app.
      rewrite (List_map_nth' 0). 2: {
        rewrite length_permut_list_inv.
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
  rewrite map_length, seq_length.
  intros i Hi.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite Nat.add_0_l.
  split. {
    unfold "°"; cbn.
    rewrite map_length.
    rewrite length_permut_list_inv.
    now destruct Hσ.
  } {
    apply (comp_is_permut_list n). {
      now apply canon_sym_gr_list_is_permut.
    } {
      now apply permut_list_inv_is_permut.
    }
  }
}
split. {
  rewrite map_length, seq_length.
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
(* lemme à faire ? *)
  unfold permut_list_inv.
  apply in_map_iff.
  exists (ff_app σ k).
  split. {
    unfold unsome.
    remember (List_find_nth _ _) as x eqn:Hx.
    symmetry in Hx.
    destruct x as [x| ]. {
      apply (List_find_nth_Some 0) in Hx.
      destruct Hx as (Hxl & Hbefx & Hx).
      apply Nat.eqb_eq in Hx.
      destruct Hσ as (Hσ1, Hσ2).
      rewrite <- Hσ2 in Hk.
      now apply Hσ1.
    } {
      specialize (List_find_nth_None 0 _ _ Hx) as H2.
      destruct Hσ as (Hσ1, Hσ2).
      rewrite <- Hσ2 in Hk.
      specialize (H2 k Hk).
      now rewrite Nat.eqb_refl in H2.
    }
  } {
    apply in_seq.
    split; [ easy | ].
    rewrite Nat.add_0_l.
    destruct Hσ as (Hσ1, Hσ2).
    rewrite <- Hσ2 in Hk.
    now apply permut_list_ub.
  }
} {
  intros l Hl.
  apply in_map_iff.
  destruct Hl as (Hl1, Hl2).
  destruct Hσ as (Hσ1, Hσ2).
  exists (canon_sym_gr_list_inv n (map (ff_app l) σ)).
  rewrite permut_in_canon_sym_gr_of_its_rank. 2: {
    now apply map_ff_app_permut_permut_is_permut.
  }
  split. {
    unfold "°".
    unfold ff_app.
    erewrite map_ext_in. 2: {
      intros i Hi.
      rewrite (List_map_nth' 0). 2: {
        now apply in_permut_list_inv_lt.
      }
      easy.
    }
    unfold permut_list_inv.
    rewrite map_map.
    rewrite (List_map_nth_seq l 0) at 1.
    rewrite Hl2, <- Hσ2.
    apply map_ext_in.
    intros i Hi; apply in_seq in Hi.
    unfold unsome.
    remember (List_find_nth _ _) as x eqn:Hx.
    symmetry in Hx.
    destruct x as [x| ]. {
      apply (List_find_nth_Some 0) in Hx.
      destruct Hx as (Hxσ & Hbefx & Hx).
      apply Nat.eqb_eq in Hx.
      now rewrite <- Hx.
    }
    exfalso; revert Hx.
    rewrite Hσ2 in Hi.
    now apply (List_find_nth_not_None (conj Hσ1 Hσ2)).
  }
  apply in_seq.
  split; [ easy | ].
  rewrite Nat.add_0_l.
  apply canon_sym_gr_list_inv_ub.
  now apply map_ff_app_permut_permut_is_permut.
}
Qed.

Theorem det_any_permut_r : in_field →
  ∀ n (M : matrix T) (σ : list nat),
  n ≠ 0
  → mat_nrows M = n
  → is_square_matrix M = true
  → is_permut n σ
  → determinant M =
    (∑ (μ ∈ canon_sym_gr_list_list n), ε n μ * ε n σ *
     ∏ (k = 0, n - 1), mat_el M (ff_app μ k) (ff_app σ k))%F.
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
  remember (σ ° permut_list_inv μ) as ν eqn:Hν.
  assert (Hσν : ν ° μ = σ). {
    rewrite Hν.
    assert (H : length (permut_list_inv μ) = n). {
      rewrite length_permut_list_inv.
      apply Hpμ.
    }
    rewrite <- (permut_comp_assoc _ _ H); clear H; [ | apply Hpμ ].
    rewrite (@comp_permut_inv_permut n); [ | easy ].
    apply comp_id_r, Hσ.
  }
  subst ν.
  rewrite <- Hσν at 1.
  replace (ε n ((σ ° permut_list_inv μ) ° μ)) with
      (ε n (σ ° permut_list_inv μ) * ε n μ)%F. 2: {
    destruct Hif.
    rewrite <- signature_comp; try easy.
    apply comp_is_permut; [ easy | ].
    now apply permut_list_inv_is_permut.
  }
  destruct Hif as (Hic & Hop & Hiv & Hit & H10 & Hde & Hch) in Hsm.
  rewrite (rngl_mul_comm Hic _ (ε n μ)).
  rewrite rngl_mul_assoc.
  replace (ε n μ * ε n μ)%F with 1%F by now symmetry; apply ε_square.
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
      (g := ff_app (permut_list_inv (canon_sym_gr_list n i)))
      (h := ff_app (canon_sym_gr_list n i)). 2: {
    intros j (_, Hj).
    apply (@permut_inv_permut n); [ | flia Hj Hnz ].
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
    rewrite (@permut_permut_inv n); [ easy | easy | ].
    rewrite <- Hkj.
    rewrite <- length_canon_sym_gr_list with (k := i).
    apply permut_list_ub; [ apply Hc | ].
    now rewrite length_canon_sym_gr_list.
  }
  cbn.
  destruct Hif as (Hic & Hop & Hiv & Hit & H10 & Hde & Hch) in Hsm.
  rewrite rngl_product_map_permut; [ | easy | easy ].
  easy.
}
cbn.
set (sg := map (λ k, σ ° permut_list_inv (canon_sym_gr_list n k)) (seq 0 n!)).
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
    replace (ff_app _ _) with (ff_app (nth k sg []) (i - 1)). 2: {
      unfold sg.
      rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
      rewrite seq_nth; [ | easy ].
      rewrite Nat.add_0_l.
      unfold "°".
      unfold ff_app.
      rewrite (List_map_nth' 0). 2: {
        rewrite length_permut_list_inv.
        rewrite length_canon_sym_gr_list.
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
  rewrite map_length, seq_length.
  intros i Hi.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite Nat.add_0_l.
  split. {
    unfold "°"; cbn.
    rewrite map_length.
    rewrite length_permut_list_inv.
    apply length_canon_sym_gr_list.
  } {
    apply (comp_is_permut_list n); [ easy | ].
    apply permut_list_inv_is_permut.
    now apply canon_sym_gr_list_is_permut.
  }
}
split. {
  rewrite map_length, seq_length.
  intros i j Hi Hj Hij.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  do 2 rewrite Nat.add_0_l in Hij.
  unfold "°" in Hij.
  apply (f_equal (map (ff_app (permut_list_inv σ)))) in Hij.
  do 2 rewrite map_map in Hij.
  erewrite map_ext_in in Hij. 2: {
    intros k Hk.
    apply (In_nth _ _ 0) in Hk.
    destruct Hk as (u & Hu1 & Hu2).
    rewrite permut_inv_permut with (n := n); [ | easy | ]. 2: {
      rewrite <- Hu2.
      eapply Nat.lt_le_trans. {
        apply permut_list_ub; [ | easy ].
        apply permut_list_inv_is_permut_list.
        now apply canon_sym_gr_list_is_permut.
      }
      rewrite length_permut_list_inv.
      now rewrite length_canon_sym_gr_list.
    }
    easy.
  }
  symmetry in Hij.
  erewrite map_ext_in in Hij. 2: {
    intros k Hk.
    apply (In_nth _ _ 0) in Hk.
    destruct Hk as (u & Hu1 & Hu2).
    rewrite permut_inv_permut with (n := n); [ | easy | ]. 2: {
      rewrite <- Hu2.
      eapply Nat.lt_le_trans. {
        apply permut_list_ub; [ | easy ].
        apply permut_list_inv_is_permut_list.
        now apply canon_sym_gr_list_is_permut.
      }
      rewrite length_permut_list_inv.
      now rewrite length_canon_sym_gr_list.
    }
    easy.
  }
  symmetry in Hij.
  do 2 rewrite map_id in Hij.
  apply permut_list_inv_inj2 in Hij; cycle 1. {
    now apply canon_sym_gr_list_is_permut_list.
  } {
    now apply canon_sym_gr_list_is_permut_list.
  }
  now apply canon_sym_gr_list_inj in Hij.
} {
  intros l Hl.
  apply in_map_iff.
  exists (canon_sym_gr_list_inv n (permut_list_inv l ° σ)).
  rewrite permut_in_canon_sym_gr_of_its_rank. 2: {
    apply comp_is_permut; [ | easy ].
    now apply permut_list_inv_is_permut.
  }
  rewrite (@permut_list_inv_comp n); [ | | easy ]. 2: {
    now apply permut_list_inv_is_permut.
  }
  rewrite (@permut_comp_assoc n); cycle 1. {
    rewrite length_permut_list_inv.
    now destruct Hσ.
  } {
    now do 2 apply permut_list_inv_is_permut.
  }
  rewrite (@comp_permut_permut_inv n); [ | easy ].
  rewrite comp_id_l. 2: {
    intros i Hi.
    apply in_permut_list_inv_lt in Hi.
    rewrite length_permut_list_inv in Hi.
    destruct Hl as (H1, H2).
    now rewrite H2 in Hi.
  }
  rewrite permut_list_inv_involutive; [ | now destruct Hl ].
  split; [ easy | ].
  apply in_seq.
  split; [ easy | ].
  apply canon_sym_gr_list_inv_ub.
  apply comp_is_permut; [ | easy ].
  now apply permut_list_inv_is_permut.
}
Qed.

(* https://proofwiki.org/wiki/Permutation_of_Determinant_Indices *)

Theorem determinant_transpose : in_field →
  ∀ (M : matrix T),
  is_square_matrix M = true
  → determinant M⁺ = determinant M.
Proof.
intros Hif * Hsm.
remember (mat_nrows M) as n eqn:Hr; symmetry in Hr.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  unfold determinant.
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
do 2 rewrite Nat.add_0_l.
rewrite seq_nth; [ | now rewrite square_matrix_ncols ].
easy.
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

Theorem comatrix_nrows : ∀ M, mat_nrows (comatrix M) = mat_nrows M.
Proof.
intros.
unfold comatrix; cbn.
now rewrite List_map_seq_length.
Qed.

Theorem comatrix_ncols : ∀ M, mat_ncols (comatrix M) = mat_ncols M.
Proof.
intros.
unfold comatrix.
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
  → is_square_matrix (comatrix M) = true.
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

Theorem laplace_formula_on_cols : in_field →
  ∀ (M : matrix T) j,
  is_square_matrix M = true
  → j < mat_nrows M
  → determinant M =
    ∑ (i = 0, mat_nrows M - 1), mat_el M i j * mat_el (comatrix M⁺)⁺ i j.
Proof.
intros Hif * Hsm Hljn.
rewrite <- determinant_transpose; [ | easy | easy ].
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite <- mat_transp_el; [ | now apply squ_mat_is_corr ].
  easy.
}
cbn - [ determinant mat_el ].
rewrite <- square_matrix_ncols; [ | easy ].
rewrite <- mat_transp_nrows.
specialize (@laplace_formula_on_rows Hif (M⁺)%M j) as H1.
assert (H : is_square_matrix M⁺ = true) by now apply mat_transp_is_square.
specialize (H1 H); clear H.
rewrite mat_transp_nrows in H1.
rewrite square_matrix_ncols in H1; [ | easy ].
specialize (H1 Hljn).
rewrite <- square_matrix_ncols in H1; [ | easy ].
rewrite mat_transp_nrows.
rewrite H1.
apply rngl_summation_eq_compat.
intros i Hi.
f_equal.
symmetry.
apply mat_transp_el.
apply squ_mat_is_corr.
apply comatrix_is_square.
now apply mat_transp_is_square.
Qed.

Theorem mat_swap_rows_involutive : ∀ (M : matrix T) i j,
  i < mat_nrows M
  → j < mat_nrows M
  → mat_swap_rows i j (mat_swap_rows i j M) = M.
Proof.
intros * Hi Hj.
destruct M as (ll); cbn in Hj |-*.
unfold mat_swap_rows.
f_equal; cbn.
rewrite List_map_seq_length.
rewrite List_map_nth_seq with (d := []).
apply map_ext_in.
intros k Hk; apply in_seq in Hk.
unfold transposition.
do 2 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec k i) as [Hki| Hki]. {
  subst k.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ cbn | easy ].
  rewrite Nat.eqb_refl.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec j i) as [Hji| Hji]; [ now subst i | easy ].
}
destruct (Nat.eq_dec k j) as [Hkj| Hkj]. {
  subst k.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ cbn | easy ].
  now rewrite Nat.eqb_refl.
}
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ cbn | easy ].
now apply Nat.eqb_neq in Hki, Hkj; rewrite Hki, Hkj.
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

Isn't it strange? (or beautiful?)
*)

Theorem determinant_with_row : in_field →
  ∀ i (M : matrix T),
  is_square_matrix M = true
  → i < mat_nrows M
  → determinant M =
    ∑ (j = 0, mat_nrows M - 1),
    minus_one_pow (i + j) * mat_el M i j * determinant (subm M i j).
Proof.
intros Hif * Hsm Hir.
destruct (Nat.eq_dec i 0) as [Hiz| Hiz]. {
  subst i; cbn - [ determinant ].
  unfold determinant.
  erewrite rngl_summation_eq_compat. 2: {
    intros i Hi.
    rewrite mat_nrows_subm.
    apply Nat.ltb_lt in Hir; rewrite Hir.
    easy.
  }
  cbn.
  replace (mat_nrows M) with (S (mat_nrows M - 1)) by flia Hir.
  now cbn; rewrite Nat.sub_0_r.
}
apply rngl_opp_inj; [ now destruct Hif | ].
apply Nat.neq_sym in Hiz.
rewrite <- (determinant_alternating Hif M Hiz); [ | flia Hir | easy | easy ].
unfold determinant at 1.
rewrite mat_swap_rows_nrows.
replace (mat_nrows M) with (S (mat_nrows M - 1)) at 1 by flia Hir.
rewrite determinant_succ at 1.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite mat_swap_rows_comm.
  rewrite mat_el_mat_swap_rows; [ | flia Hir ].
  easy.
}
rewrite rngl_opp_summation; [ | now destruct Hif ].
apply rngl_summation_eq_compat.
intros j Hj.
rewrite <- rngl_mul_assoc; symmetry.
rewrite <- rngl_mul_opp_r; [ | now destruct Hif ].
rewrite (Nat.add_comm i j).
rewrite minus_one_pow_add_r; [ | now destruct Hif ].
do 2 rewrite <- rngl_mul_assoc.
f_equal.
rewrite rngl_mul_comm; [ | now destruct Hif ].
rewrite <- rngl_mul_assoc.
f_equal.
rewrite rngl_mul_opp_l, <- rngl_mul_opp_r; cycle 1. {
  now destruct Hif.
} {
  now destruct Hif.
}
rewrite rngl_mul_comm; [ | now destruct Hif ].
symmetry.
rewrite mat_swap_rows_comm.
rewrite <- determinant_subm_mat_swap_rows_0_i; try easy; cycle 1. {
  flia Hir Hiz.
} {
  flia Hj Hir.
}
unfold determinant.
rewrite mat_nrows_subm.
rewrite mat_swap_rows_nrows.
assert (H : 0 < mat_nrows M) by flia Hir.
now apply Nat.ltb_lt in H; rewrite H; clear H.
Qed.

Theorem determinant_with_bad_row : in_field →
  ∀ i k (M : matrix T),
  is_square_matrix M = true
  → i < mat_nrows M
  → k < mat_nrows M
  → i ≠ k
  → ∑ (j = 0, mat_nrows M - 1),
    minus_one_pow (i + j) * mat_el M k j * determinant (subm M i j) = 0%F.
Proof.
intros Hif * Hsm Hir Hkr Hik.
specialize (square_matrix_ncols _ Hsm) as Hc.
remember
  (mk_mat
     (map
        (λ p,
         map (λ q, mat_el M (if p =? i then k else p) q)
           (seq 0 (mat_ncols M)))
        (seq 0 (mat_nrows M))))
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
assert (H1 : determinant A = 0%F). {
  apply determinant_same_rows with (p := i) (q := k); try easy. {
    now rewrite Hira.
  } {
    now rewrite Hira.
  }
  intros j; subst A; cbn.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  symmetry.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  f_equal.
  apply map_ext_in.
  intros u Hu; apply in_seq in Hu.
  rewrite seq_nth; [ | easy ].
  rewrite seq_nth; [ | easy ].
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
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0); [ | rewrite seq_length, Hc; flia Hj Hir ].
  rewrite seq_nth; [ | easy ].
  rewrite seq_nth; [ | rewrite Hc; flia Hj Hir ].
  now rewrite Nat.eqb_refl.
}
(* oops... complicated from now! doing a lemma, perhaps? *)
unfold subm; cbn.
do 2 rewrite map_length.
do 2 rewrite butn_length.
do 2 rewrite fold_mat_nrows.
rewrite Hira.
apply Nat.ltb_lt in Hir; rewrite Hir; cbn.
f_equal; f_equal; f_equal.
rewrite HA; cbn.
destruct M as (ll); cbn in Hir, Hj |-*.
unfold mat_ncols; cbn.
apply Nat.ltb_lt in Hir.
remember (seq 0 (length (hd [] ll))) as x eqn:Hx.
rewrite List_seq_cut with (i := i); [ subst x | now apply in_seq ].
rewrite Nat.sub_0_r, Nat.add_0_l.
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
rewrite List_seq_cut with (i := i); [ | now apply in_seq ].
rewrite Nat.sub_0_r, Nat.add_0_l.
do 2 rewrite map_app.
rewrite butn_app; [ cbn | symmetry; apply List_map_seq_length ].
rewrite butn_app; [ cbn | symmetry; apply List_map_seq_length ].
f_equal. {
  apply map_ext_in.
  intros u Hu; apply in_seq in Hu.
  rewrite List_map_nth_seq with (d := 0%F) (la := nth u ll []).
  apply is_scm_mat_iff in Hsm.
  destruct Hsm as (Hcr, Hcl).
  cbn in Hcl.
  rewrite List_hd_nth_0.
  rewrite Hcl; [ | apply nth_In; flia Hu Hir ].
  rewrite Hcl; [ | apply nth_In; flia Hu Hir ].
  apply map_ext_in.
  intros v Hv; apply in_seq in Hv.
  rewrite List_map_nth_seq with (la := nth u ll []) (d := 0%F) at 1.
  f_equal; f_equal; f_equal.
  apply Hcl, nth_In; flia Hu Hir.
} {
  apply map_ext_in.
  intros u Hu; apply in_seq in Hu.
  rewrite List_map_nth_seq with (d := 0%F) (la := nth u ll []).
  apply is_scm_mat_iff in Hsm.
  destruct Hsm as (Hcr, Hcl).
  cbn in Hcl.
  rewrite List_hd_nth_0.
  rewrite Hcl; [ | apply nth_In; flia Hu ].
  rewrite Hcl; [ | apply nth_In; flia Hu ].
  apply map_ext_in.
  intros v Hv; apply in_seq in Hv.
  rewrite List_map_nth_seq with (la := nth u ll []) (d := 0%F) at 1.
  f_equal; f_equal; f_equal.
  apply Hcl, nth_In; flia Hu.
}
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

Theorem comatrix_transpose : in_field →
  ∀ M,
  is_square_matrix M = true
  → comatrix M⁺ = (comatrix M)⁺%M.
Proof.
intros Hif * Hsm.
destruct (Nat.eq_dec (mat_ncols M) 0) as [Hcz| Hcz]. {
  unfold mat_transp, comatrix; cbn - [ determinant ].
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
unfold mat_transp, comatrix, mat_ncols; cbn - [ determinant ].
f_equal.
rewrite (List_map_hd 0); [ | now rewrite seq_length ].
rewrite (List_map_hd 0); [ | now rewrite seq_length ].
do 4 rewrite map_length.
do 2 rewrite seq_length.
rewrite fold_mat_ncols.
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
destruct Hi as (_, Hi); cbn in Hi.
apply map_ext_in.
intros j Hj; apply in_seq in Hj.
destruct Hj as (_, Hj); cbn in Hj.
move j before i.
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
rewrite seq_nth; [ | easy ].
do 2 rewrite Nat.add_0_l.
rewrite Nat.add_comm; f_equal; symmetry.
rewrite fold_mat_transp.
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
rewrite mat_transp_el; [ | now apply subm_is_corr_mat ].
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
  now apply Nat.ltb_lt in Hj; rewrite Hj in Hv.
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
  now apply Nat.ltb_lt in Hi; rewrite Hi in Hu.
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
  destruct (le_dec i u); flia Hu.
}
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  unfold Nat.b2n; rewrite if_leb_le_dec.
  destruct (le_dec j v); flia Hv.
}
rewrite seq_nth. 2: {
  unfold Nat.b2n; rewrite if_leb_le_dec.
  destruct (le_dec j v); flia Hv.
}
rewrite seq_nth. 2: {
  unfold Nat.b2n; rewrite if_leb_le_dec.
  destruct (le_dec i u); flia Hu.
}
easy.
Qed.

Theorem mat_transp_subm : ∀ M i j,
  is_correct_matrix M = true
  → mat_nrows M ≠ 1
  → i < mat_ncols M
  → j < mat_nrows M
  → subm M⁺ i j = ((subm M j i)⁺)%M.
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
  destruct Hu as (_, Hu); cbn in Hu.
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
    apply Nat.leb_gt in Hu; rewrite Hu.
    now rewrite Nat.add_0_r.
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
    apply Nat.leb_gt in Hu; rewrite Hu, Nat.add_0_r.
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
    apply Nat.leb_gt in Hu; rewrite Hu, Nat.add_0_r.
    rewrite nth_butn.
    apply Nat.leb_le in Hjv; rewrite Hjv, Nat.add_1_r.
    easy.
  }
}
replace (mat_ncols M - 1) with (i + (mat_ncols M - 1 - i)) at 1. 2: {
  flia Hic Hic1.
}
rewrite seq_app, Nat.add_0_l.
do 2 rewrite map_app.
f_equal. {
  apply map_ext_in.
  intros u Hu; apply in_seq in Hu.
  destruct Hu as (_, Hu); cbn in Hu.
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
    apply Nat.leb_gt in Hu; rewrite Hu.
    now rewrite Nat.add_0_r.
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
    apply Nat.leb_gt in Hu; rewrite Hu, Nat.add_0_r.
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
    apply Nat.leb_gt in Hu; rewrite Hu, Nat.add_0_r.
    rewrite nth_butn.
    apply Nat.leb_le in Hjv; rewrite Hjv, Nat.add_1_r.
    easy.
  }
}
rewrite List_skipn_seq; [ | flia Hic Hic1 ].
rewrite <- Nat.sub_add_distr.
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

Theorem mat_transp_inj : ∀ M,
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
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
destruct Hi as (_, Hi); cbn in Hi.
erewrite map_ext_in. 2: {
  intros j Hj; apply in_seq in Hj.
  destruct Hj as (_, Hj); cbn in Hj.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite seq_nth; [ | easy ].
  now cbn.
}
destruct ll as [| l]; [ easy | ].
unfold mat_ncols in Hcz; cbn in Hcz.
cbn - [ nth ].
rewrite (List_map_nth_seq (nth i (l :: ll) []) 0%F) at 1.
apply is_scm_mat_iff in Hcm.
unfold mat_ncols in Hcm; cbn - [ In ] in Hcm.
destruct Hcm as (_, Hcl).
symmetry.
rewrite Hcl; [ easy | ].
now apply nth_In.
Qed.

Theorem matrix_comatrix_transp_mul : in_field →
  ∀ (M : matrix T),
  is_square_matrix M = true
  → (M * (comatrix M)⁺ = determinant M × mI (mat_nrows M))%M.
Proof.
intros Hif * Hsm.
destruct M as (ll); cbn - [ determinant ].
unfold "*"%M, "×"%M, mat_nrows; cbn - [ determinant ]; f_equal.
rewrite map_map.
apply map_ext_in.
intros i Hi; apply in_seq in Hi.
assert (Hll : 0 < length ll) by flia Hi.
rewrite laplace_formula_on_rows with (i := i); try easy.
cbn - [ mat_el ].
rewrite mat_transp_ncols.
rewrite comatrix_nrows, comatrix_ncols.
unfold mat_ncols.
cbn - [ mat_el mat_nrows comatrix ].
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
  cbn - [ determinant ].
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite seq_nth; [ | easy ].
  do 2 rewrite Nat.add_0_l.
  rewrite rngl_mul_assoc.
  easy.
}
cbn - [ determinant ].
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  (* diagonal *)
  subst j; rewrite δ_diag, rngl_mul_1_r.
  unfold mat_mul_el.
  unfold mat_ncols.
  rewrite Hcl; [ | now apply List_hd_in ].
  apply rngl_summation_eq_compat.
  intros k Hk.
  rewrite <- rngl_mul_assoc; f_equal.
  cbn - [ determinant ].
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
  cbn - [ comatrix ].
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
    cbn - [ comatrix ].
    easy.
  }
  cbn - [ comatrix ].
  unfold mat_ncols.
  rewrite Hcl; [ | now apply List_hd_in ].
  remember (mk_mat ll) as M eqn:HM.
  erewrite rngl_summation_eq_compat. 2: {
    intros k Hk.
    rewrite HM at 1.
    cbn - [ determinant ].
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
    cbn - [ determinant ].
    rewrite rngl_mul_comm; [ | now destruct Hif ].
    rewrite rngl_mul_mul_swap; [ | now destruct Hif ].
    replace ll with (mat_list_list M) at 1 by now rewrite HM.
    rewrite fold_mat_el.
    rewrite <- HM.
    easy.
  }
  cbn - [ determinant ].
  replace (length ll) with (mat_nrows M) in Hi, Hj, Hcl |-* by now rewrite HM.
  apply Nat.neq_sym in Hij.
  apply determinant_with_bad_row; [ easy | | easy | easy | easy ].
  apply is_scm_mat_iff; cbn.
  split; [ easy | ].
  intros l Hl; rewrite HM in Hl; cbn in Hl.
  now apply Hcl.
}
Qed.

Theorem comatrix_transp_matrix_mul : in_field →
  ∀ (M : matrix T),
  is_square_matrix M = true
  → ((comatrix M)⁺ * M = determinant M × mI (mat_nrows M))%M.
Proof.
intros Hif * Hsm.
destruct M as (ll); cbn - [ determinant ].
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
  unfold "*"%M, "×"%M, mat_transp, mat_mul_el, comatrix; cbn.
  rewrite Hcl; [ cbn | now left ].
  do 2 rewrite rngl_summation_only_one; cbn.
  do 2 rewrite rngl_mul_1_l.
  now do 2 rewrite rngl_mul_1_r.
}
unfold "*"%M, "×"%M, mat_nrows; cbn - [ determinant ]; f_equal.
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
rewrite laplace_formula_on_cols with (j := j); [ | easy | easy | easy ].
unfold mat_mul_el.
rewrite mat_transp_ncols.
rewrite comatrix_ncols.
unfold mat_ncols.
rewrite Hcl; [ | now apply List_hd_in ].
rewrite comatrix_nrows.
cbn - [ mat_el comatrix ].
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
  cbn - [ mat_el comatrix ].
  apply rngl_summation_eq_compat.
  intros k Hk.
  symmetry; f_equal; rewrite mat_transp_el. 2: {
    apply squ_mat_is_corr.
    apply comatrix_is_square.
    now apply mat_transp_is_square.
  }
  f_equal.
  now apply comatrix_transpose.
} {
  (* not on diagonal: zeroes *)
  rewrite δ_ndiag; [ | easy ].
  rewrite rngl_mul_0_r; [ | now destruct Hif; left ].
  unfold mat_transp.
  cbn - [ comatrix ].
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
    cbn - [ comatrix ].
    easy.
  }
  cbn - [ comatrix ].
  remember (mk_mat ll) as M eqn:HM.
  erewrite rngl_summation_eq_compat. 2: {
    intros k Hk.
    rewrite HM at 1.
    cbn - [ determinant ].
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
    cbn - [ determinant ].
    rewrite rngl_mul_mul_swap; [ | now destruct Hif ].
    replace ll with (mat_list_list M) at 1 by now rewrite HM.
    rewrite fold_mat_el.
    rewrite <- HM.
    easy.
  }
  cbn - [ determinant ].
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
    rewrite mat_transp_inj. 2: {
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

Definition mat_inv (M : matrix T) := ((determinant M)⁻¹ × (comatrix M)⁺)%M.

Theorem mat_mul_inv_r : in_field →
  ∀ (M : matrix T),
  is_square_matrix M = true
  → determinant M ≠ 0%F
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

Theorem mat_mul_inv_l : in_field →
  ∀ (M : matrix T),
  is_square_matrix M = true
  → determinant M ≠ 0%F
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

End a.

Arguments comatrix {T}%type {ro} M%M.
Arguments mat_inv {T}%type {ro} M%M.

(* tests
Require Import Qrl.
Require Import Rational.
Import Q.Notations.
Open Scope Q_scope.
Compute 3.
Compute (let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1];[18;3;2;1]] in (determinant M, mat_inv M)).
Compute (let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1];[18;3;2;1]] in (M * mat_inv M)%M).
Compute (let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1];[18;3;2;1]] in (mat_inv M * M)%M).
Compute (let M := mk_mat [[3;0;0;1];[0;0;2;7];[1;0;1;1];[18;0;2;1]] in (determinant M, comatrix M)).
Compute (let M := mk_mat [[3;0;0;1];[0;0;2;7];[1;0;1;1];[18;0;2;1]] in (determinant M, (M * comatrix M)%M, (comatrix M * M)%M)).
*)
