(* trying to prove that det(AB)=det(A)det(B) *)

(* there are several proofs of that, none of them being simple *)
(* here, trying to prove it by the Cauchy-Binet Formula *)
(* https://proofwiki.org/wiki/Cauchy-Binet_Formula *)

(* det(AB)= ∑ 1≤j1<j2<⋯<jm≤n det(Aj1j2…jm)det(Bj1j2…jm)
   where A is a m×n matrix, B a n×m matrix
   Aj1j2…jm denotes the m×m matrix consisting of columns j1,j2,…,jm of A.
   Bj1j2…jm denotes the m×m matrix consisting of rows j1,j2,…,jm of B. *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Import List.ListNotations Init.Nat.

Require Import RingLike.RingLike.
Require Import Misc IterAdd IterMul.
Require Import PermutationFun SortingFun SortRank.
Require Import PermutSeq Signature Matrix Determinant.
Import matrix_Notations.

(* all lists [j1;j2;...jm] such that 0≤j1<j2<...<jm<n for some m and n *)

Fixpoint sls1n (i n k : nat) {struct n} : list (list nat) :=
  match k with
  | 0 => [[]]
  | S k' =>
      match n with
      | 0 => []
      | S n' =>
          List.map (λ l : list nat, i :: l)
            (sls1n (S i) n' k') ++ sls1n (S i) n' k
      end
  end.

Definition sub_lists_of_seq_1_n := sls1n 1.

Theorem sls1n_length : ∀ i n k,
  length (sls1n i n k) = binomial n k.
Proof.
intros.
revert i k.
induction n; intros; [ now destruct k | ].
destruct k; [ easy | cbn ].
rewrite List.length_app, List.length_map.
now rewrite IHn, IHn.
Qed.

Theorem sls1n_bounds : ∀ i n k t,
  t ∈ sls1n i n k
  → ∀ a, a ∈ t → i ≤ a ≤ i + n.
Proof.
intros * Ht * Hat.
revert i k t Ht Hat.
induction n; intros. {
  destruct k; [ cbn in Ht | easy ].
  destruct Ht; [ now subst t | easy ].
}
destruct k; cbn in Ht. {
  destruct Ht; [ now subst t | easy ].
}
apply List.in_app_iff in Ht.
destruct Ht as [Ht| Ht]. 2: {
  specialize (IHn (S i) (S k) t Ht Hat).
  flia IHn.
}
apply List.in_map_iff in Ht.
destruct Ht as (l & Hln & Hl); subst t.
destruct Hat as [Hat| Hat]; [ subst a; flia | ].
specialize (IHn (S i) k l Hl Hat).
flia IHn.
Qed.

Theorem in_sls1n_iff : ∀ i n k t,
  t ∈ sls1n i n k
  ↔ k = 0 ∧ t = [] ∨
    sorted Nat.ltb t ∧ length t = k ∧ (∀ j, j ∈ t → i ≤ j < i + n).
Proof.
intros.
split. {
  intros Ht.
  destruct k. {
    left.
    split; [ easy | ].
    now destruct n; destruct Ht.
  }
  right.
  revert i k t Ht.
  induction n; intros; [ easy | ].
  cbn in Ht.
  apply List.in_app_iff in Ht.
  destruct Ht as [Ht| Ht]. 2: {
    specialize (IHn _ k t Ht).
    split; [ easy | ].
    split; [ easy | ].
    intros j Hj.
    destruct IHn as (_ & _ & IHn).
    specialize (IHn _ Hj).
    flia IHn.
  }
  apply List.in_map_iff in Ht.
  destruct Ht as (t' & H & Ht); subst t.
  rename t' into t; cbn.
  destruct k. {
    destruct n. {
      destruct Ht; [ subst t | easy ].
      split; [ easy | ].
      split; [ easy | ].
      intros j Hj.
      destruct Hj; [ subst j; flia | easy ].
    }
    cbn in Ht.
    destruct Ht; [ subst t | easy ].
    split; [ easy | ].
    split; [ easy | ].
    intros j Hj.
    destruct Hj; [ subst j; flia | easy ].
  }
  specialize (IHn _ _ _ Ht).
  destruct IHn as (Hs & Htk & Htb).
  split. {
    apply (sorted_cons_iff Nat_ltb_trans).
    split; [ easy | ].
    intros a Ha.
    apply Nat.ltb_lt.
    apply sls1n_bounds with (a := a) in Ht; [ flia Ht | easy ].
  }
  split; [ now f_equal | ].
  intros j Hj.
  destruct Hj as [Hj| Hj]; [ subst j; flia | ].
  specialize (Htb _ Hj); flia Htb.
} {
  intros * Hs.
  destruct Hs as [Hs| Hs]. {
    destruct Hs; subst k t.
    now destruct n; left.
  }
  destruct Hs as (Hs & Htk & Hbnd).
  revert i k t Hs Htk Hbnd.
  induction n; intros; cbn. {
    destruct k. {
      apply List.length_zero_iff_nil in Htk; subst t.
      now left.
    }
    exfalso.
    destruct t as [| a]; [ easy | ].
    specialize (Hbnd _ (or_introl eq_refl)).
    flia Hbnd.
  }
  destruct k. {
    apply List.length_zero_iff_nil in Htk; subst t.
    now left.
  }
  destruct t as [| a]; [ easy | cbn in Htk ].
  apply Nat.succ_inj in Htk.
  apply List.in_app_iff.
  destruct (Nat.eq_dec a i) as [Hai| Hai]. {
    subst a; left.
    apply List.in_map_iff.
    exists t.
    split; [ easy | ].
    apply IHn; [ | easy | ]. 2: {
      intros j Hj.
      specialize (Hbnd _ (or_intror Hj)).
      rewrite <- Nat.add_succ_comm in Hbnd.
      split; [ | easy ].
      destruct (Nat.eq_dec i j) as [Hij| Hij]; [ | flia Hbnd Hij ].
      subst j; exfalso; clear Hbnd.
      apply (sorted_cons_iff Nat_ltb_trans) in Hs.
      destruct Hs as (Hs & Ht).
      destruct t as [| a]; [ easy | ].
      destruct Hj as [Hj| Hj]. {
        subst a.
        specialize (Ht _ (or_introl eq_refl)).
        now rewrite Nat.ltb_irrefl in Ht.
      }
      specialize (Ht _ (or_intror Hj)).
      now rewrite Nat.ltb_irrefl in Ht.
    }
    cbn in Hs.
    now apply (sorted_cons_iff Nat_ltb_trans) in Hs.
  }
  right.
  apply IHn; [ easy | now cbn; f_equal | ].
  intros j Hj.
  destruct Hj as [Hj| Hj]. {
    subst j.
    specialize (Hbnd a (or_introl eq_refl)).
    flia Hbnd Hai.
  }
  specialize (Hbnd a (or_introl eq_refl)) as H1.
  specialize (Hbnd _ (or_intror Hj)) as H2.
  cbn in Hs.
  apply (sorted_cons_iff Nat_ltb_trans) in Hs.
  destruct Hs as (Hs & Ht).
  specialize (Ht j Hj).
  apply Nat.ltb_lt in Ht.
  flia Ht H1 H2.
}
Qed.

Theorem in_sub_lists_of_seq_1_n_length : ∀ n k t,
  t ∈ sub_lists_of_seq_1_n n k → List.length t = k.
Proof.
intros * Ht.
unfold sub_lists_of_seq_1_n in Ht.
apply in_sls1n_iff in Ht.
destruct Ht as [(Hk, Ht)| Ht]; [ now subst k t | easy ].
Qed.

(* *)

Theorem sub_lists_of_seq_1_n_bounds : ∀ n k t,
  t ∈ sub_lists_of_seq_1_n n k
  → ∀ a, a ∈ t → 1 ≤ a ≤ n.
Proof.
intros * Ht a Hat.
unfold sub_lists_of_seq_1_n in Ht.
apply in_sls1n_iff in Ht.
destruct Ht as [(Hk, Ht)| Ht]; [ now subst t | ].
destruct Ht as (Hs & H & Ht); subst k.
specialize (Ht _ Hat).
split; [ easy | ].
now apply Nat.lt_succ_r.
Qed.

(* *)

Theorem sls1n_out : ∀ i n k,
  n < k
  → sls1n i n k = [].
Proof.
intros * Hnk.
revert i k Hnk.
induction n; intros; cbn; [ now destruct k | ].
destruct k; [ easy | ].
apply Nat.succ_lt_mono in Hnk.
rewrite IHn; [ | flia Hnk ].
apply IHn.
now apply Nat.lt_lt_succ_r.
Qed.

Theorem sls1n_inj : ∀ i n k u v,
  u < binomial n k
  → v < binomial n k
  → List.nth u (sls1n i n k) [] = List.nth v (sls1n i n k) []
  → u = v.
Proof.
intros * Hu Hv Huv.
revert i u v k Hu Hv Huv.
induction n; intros; cbn in Huv. {
  destruct k; [ apply Nat.lt_1_r in Hu, Hv; congruence | easy ].
}
destruct k; [ apply Nat.lt_1_r in Hu, Hv; congruence | ].
destruct (lt_dec u (binomial n k)) as [Hub| Hub]. {
  rewrite List.app_nth1 in Huv. 2: {
    now rewrite List.length_map, sls1n_length.
  }
  rewrite (List_map_nth' []) in Huv; [ | now rewrite sls1n_length ].
  destruct (lt_dec v (binomial n k)) as [Hvb| Hvb]. {
    rewrite List.app_nth1 in Huv. 2: {
      now rewrite List.length_map, sls1n_length.
    }
    rewrite (List_map_nth' []) in Huv; [ | now rewrite sls1n_length ].
    injection Huv; clear Huv; intros Huv.
    now apply IHn in Huv.
  }
  apply Nat.nlt_ge in Hvb.
  rewrite List.app_nth2 in Huv. 2: {
    now rewrite List.length_map, sls1n_length.
  }
  rewrite List.length_map, sls1n_length in Huv.
  specialize sls1n_bounds as H1.
  specialize (H1 (S i) n (S k)).
  remember (sls1n (S i) n (S k)) as la eqn:Hla.
  remember (v - binomial n k) as j eqn:Hj.
  specialize (H1 (List.nth j la [])).
  destruct (lt_dec j (length la)) as [Hjla| Hjla]. 2: {
    apply Nat.nlt_ge in Hjla.
    now rewrite List.nth_overflow with (n := j) in Huv.
  }
  assert (H : List.nth j la [] ∈ la) by now apply List.nth_In.
  specialize (H1 H); clear H.
  rewrite <- Huv in H1.
  specialize (H1 _ (or_introl eq_refl)).
  flia H1.
}
apply Nat.nlt_ge in Hub.
rewrite List.app_nth2 in Huv; [ | now rewrite List.length_map, sls1n_length ].
rewrite List.length_map, sls1n_length in Huv.
destruct (lt_dec v (binomial n k)) as [Hvb| Hvb]. {
  rewrite List.app_nth1 in Huv. 2: {
    now rewrite List.length_map, sls1n_length.
  }
  rewrite (List_map_nth' []) in Huv; [ | now rewrite sls1n_length ].
  specialize sls1n_bounds as H1.
  specialize (H1 (S i) n (S k)).
  remember (sls1n (S i) n (S k)) as la eqn:Hla.
  remember (u - binomial n k) as j eqn:Hj.
  specialize (H1 (List.nth j la [])).
  destruct (lt_dec j (length la)) as [Hjla| Hjla]. 2: {
    apply Nat.nlt_ge in Hjla.
    now rewrite List.nth_overflow with (n := j) in Huv.
  }
  assert (H : List.nth j la [] ∈ la) by now apply List.nth_In.
  specialize (H1 H); clear H.
  rewrite Huv in H1.
  specialize (H1 _ (or_introl eq_refl)).
  flia H1.
}
apply Nat.nlt_ge in Hvb.
rewrite List.app_nth2 in Huv; [ | now rewrite List.length_map, sls1n_length ].
rewrite List.length_map, sls1n_length in Huv.
apply IHn in Huv; [ | cbn in Hu; flia Hu Hub | cbn in Hv; flia Hv Hvb ].
flia Huv Hub Hvb.
Qed.

Theorem sls1n_0_r : ∀ i n, sls1n i n 0 = [[]].
Proof. now intros; destruct n. Qed.

Theorem sls1n_diag : ∀ i n, sls1n i n n = [List.seq i n].
Proof.
intros.
revert i.
induction n; intros; [ easy | ].
cbn; rewrite IHn; cbn.
f_equal.
now apply sls1n_out.
Qed.

Theorem sls1n_are_correct : ∀ i k n t,
  k ≠ 0
  → t ∈ sls1n i n k
  → t ≠ [].
Proof.
intros * Hkz Ht Htz; subst t.
destruct k; [ easy | clear Hkz ].
revert i Ht.
induction n; intros; [ easy | cbn in Ht ].
apply List.in_app_iff in Ht.
destruct Ht as [Ht| Ht]; [ | now apply IHn in Ht ].
apply List.in_map_iff in Ht.
now destruct Ht as (x & Hx & Hxn).
Qed.

Theorem sub_lists_of_seq_1_n_are_correct : ∀ k n t,
  k ≠ 0 → t ∈ sub_lists_of_seq_1_n n k → t ≠ [].
Proof.
intros * Hkz Ht.
now apply sls1n_are_correct in Ht.
Qed.

Theorem sls1n_are_sorted : ∀ i n k la,
  la ∈ sls1n i n k
  → sorted Nat.ltb la.
Proof.
intros * Hla.
apply in_sls1n_iff in Hla.
destruct Hla as [(H1,H2) | Ht]; [ now subst k la | easy ].
Qed.

Theorem sub_lists_of_seq_1_n_are_sorted : ∀ n k ll,
  ll = sub_lists_of_seq_1_n n k
  → ∀ l, l ∈ ll → sorted Nat.ltb l.
Proof.
intros * Hll * Hl.
subst ll.
now apply sls1n_are_sorted in Hl.
Qed.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

(* submatrix with list rows jl *)
Definition mat_select_rows (jl : list nat) (M : matrix T) :=
  mk_mat
    (List.map
       (λ i, List.map (λ j, mat_el M i j) (List.seq 1 (mat_ncols M))) jl).

(* submatrix with list cols jl *)
Definition mat_select_cols (jl : list nat) (M : matrix T) :=
  ((mat_select_rows jl M⁺)⁺)%M.

End a.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
(*
Context (Hon : rngl_has_1 = true).
*)

(* https://fr.wikipedia.org/wiki/Formule_de_Binet-Cauchy *)

Theorem mat_select_rows_nrows : ∀ (A : matrix T) kl,
  mat_nrows (mat_select_rows kl A) = length kl.
Proof.
intros; cbn.
apply List.length_map.
Qed.

Theorem mat_select_rows_ncols : ∀ (A : matrix T) kl,
  kl ≠ []
  → mat_ncols (mat_select_rows kl A) = mat_ncols A.
Proof.
intros * Hkl; cbn.
destruct kl as [| k]; [ easy | ].
now cbn; rewrite List_length_map_seq.
Qed.

Theorem mat_select_cols_nrows : ∀ (A : matrix T) kl,
  kl ≠ []
  → mat_ncols A ≠ 0
  → mat_nrows (mat_select_cols kl A) = mat_nrows A.
Proof.
intros * Hlk Hcz; cbn.
rewrite List_length_map_seq.
rewrite mat_select_rows_ncols; [ | easy ].
rewrite mat_transp_ncols.
now apply Nat.eqb_neq in Hcz; rewrite Hcz.
Qed.

Theorem mat_select_cols_el : ∀ M i j jl,
  1 ≤ i ≤ mat_nrows M
  → 1 ≤ j ≤ length jl
  → (∀ j, 1 ≤ j ≤ length jl → 1 ≤ jl.(j) ≤ mat_ncols M)
  → mat_el (mat_select_cols jl M) i j = mat_el M i jl.(j).
Proof.
intros * Hi Hj Hjl.
assert (Hjlz : jl ≠ []). {
  intros H; rewrite H in Hj; cbn in Hj; flia Hj.
}
cbn.
rewrite List.length_map.
rewrite (List_map_nth' 0). 2: {
  rewrite List.length_seq, mat_select_rows_ncols; [ | easy ].
  rewrite mat_transp_ncols.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (mat_ncols M) 0) as [Hcz| Hcz]; [ | flia Hi ].
  specialize (Hjl _ Hj); flia Hjl Hcz.
}
rewrite List.seq_nth. 2: {
  rewrite mat_select_rows_ncols; [ | easy ].
  rewrite mat_transp_ncols.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (mat_ncols M) 0) as [Hcz| Hcz]; [ | flia Hi ].
  specialize (Hjl _ Hj); flia Hjl Hcz.
}
rewrite Nat.add_comm, Nat.add_sub.
rewrite (List_map_nth' 0); [ | rewrite List.length_seq; flia Hj ].
rewrite List.seq_nth; [ | flia Hj ].
rewrite Nat.add_comm, Nat.add_sub.
rewrite (List_map_nth' 0); [ | flia Hj ].
rewrite (List_map_nth' 0). 2: {
  rewrite List.length_seq, mat_transp_ncols.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (mat_ncols M) 0) as [Hcz| Hcz]; [ | flia Hi ].
  specialize (Hjl _ Hj); flia Hjl Hcz.
}
rewrite List.seq_nth. 2: {
  rewrite mat_transp_ncols.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (mat_ncols M) 0) as [Hcz| Hcz]; [ | flia Hi ].
  specialize (Hjl _ Hj); flia Hjl Hcz.
}
rewrite (List_map_nth' 0). 2: {
  rewrite List.length_seq.
  specialize (Hjl _ Hj); flia Hjl.
}
rewrite Nat.add_comm, Nat.add_sub.
rewrite List.seq_nth; [ | specialize (Hjl _ Hj); flia Hjl ].
rewrite (List_map_nth' 0); [ | rewrite List.length_seq; flia Hi ].
rewrite Nat.add_comm, Nat.sub_add; [ | now specialize (Hjl _ Hj) ].
rewrite List.seq_nth; [ | flia Hi ].
now rewrite Nat.add_comm, Nat.sub_add.
Qed.

Theorem mat_select_rows_is_square : ∀ kl (A : matrix T),
  is_correct_matrix A = true
  → mat_ncols A = length kl
  → (∀ k, k ∈ kl → 1 ≤ k ≤ mat_nrows A)
  → is_square_matrix (mat_select_rows kl A) = true.
Proof.
intros * Ha Hca Hkc.
destruct (Nat.eq_dec (length kl) 0) as [Hnz| Hnz]. {
  apply List.length_zero_iff_nil in Hnz; subst kl.
  now cbn; rewrite iter_list_empty.
}
apply is_scm_mat_iff.
apply is_scm_mat_iff in Ha.
destruct Ha as (Hcra, Hcla).
split. {
  rewrite mat_select_rows_nrows.
  unfold mat_ncols; cbn.
  intros Hc.
  destruct kl as [| k]; [ easy | exfalso ].
  clear Hnz; cbn in Hc.
  rewrite List_length_map_seq in Hc.
  now rewrite Hca in Hc.
} {
  intros l Hl.
  rewrite mat_select_rows_nrows.
  cbn in Hl.
  apply List.in_map_iff in Hl.
  destruct Hl as (a & Hal & Ha).
  subst l.
  now rewrite List_length_map_seq.
}
Qed.

Theorem mat_select_cols_is_square : ∀ kl (A : matrix T),
  is_correct_matrix A = true
  → mat_nrows A = length kl
  → (∀ k, k ∈ kl → 1 ≤ k ≤ mat_ncols A)
  → is_square_matrix (mat_select_cols kl A) = true.
Proof.
intros * Ha Hca Hkc.
destruct (Nat.eq_dec (mat_ncols A) 0) as [Hcz| Hcz]. {
  apply is_scm_mat_iff in Ha.
  destruct Ha as (Hcr & Hc).
  rewrite Hcr in Hca; [ | easy ].
  symmetry in Hca; apply List.length_zero_iff_nil in Hca; subst kl.
  now cbn; rewrite iter_list_empty.
}
unfold mat_select_cols.
apply mat_transp_is_square.
apply mat_select_rows_is_square. {
  now apply mat_transp_is_corr.
} {
  rewrite mat_transp_ncols.
  now apply Nat.eqb_neq in Hcz; rewrite Hcz.
} {
  now rewrite mat_transp_nrows.
}
Qed.

Theorem nth_concat_same_length : ∀ A m n (lll : list (list (list A))) i,
  (∀ ll, ll ∈ lll → length ll = m)
  → (∀ ll, ll ∈ lll → ∀ l, l ∈ ll → length l = n)
  → i < length lll * m
  → length (List.nth i (List.concat lll) []) = n.
Proof.
intros * Hlll Hll Hi.
revert i Hi.
induction lll as [| ll1]; intros; [ easy | cbn ].
destruct (lt_dec i (length ll1)) as [Hill| Hill]. {
  rewrite List.app_nth1; [ | easy ].
  apply Hll with (ll := ll1); [ now left | ].
  now apply List.nth_In.
}
apply Nat.nlt_ge in Hill.
rewrite List.app_nth2; [ | easy ].
apply IHlll. {
  intros ll2 Hll2.
  now apply Hlll; right.
} {
  intros ll2 Hll2 l Hl.
  apply Hll with (ll := ll2); [ now right | easy ].
} {
  cbn in Hi.
  rewrite Hlll; [ | now left ].
  rewrite Hlll in Hill; [ | now left ].
  flia Hi Hill.
}
Qed.

Theorem nth_cart_prod_same_length : ∀ A n (ll : list (list A)) i,
  (∀ l, l ∈ ll → length l = n)
  → i < n ^ length ll
  → length (List.nth i (cart_prod ll) []) = length ll.
Proof.
intros * Hll Hi.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  destruct ll as [| l]. {
    now apply Nat.lt_1_r in Hi; subst i.
  }
  now rewrite Nat.pow_0_l in Hi.
}
revert n i Hnz Hi Hll.
induction ll as [| l]; intros. {
  destruct i; [ easy | now destruct i ].
}
destruct ll as [| l1]. {
  cbn.
  specialize (Hll _ (or_introl eq_refl)).
  subst n.
  rewrite Nat.pow_1_r in Hi.
  clear Hnz.
  revert i Hi.
  induction l as [| a]; intros; [ easy | cbn ].
  destruct i; [ easy | ].
  cbn in Hi; apply Nat.succ_lt_mono in Hi.
  now apply IHl.
}
remember (l1 :: ll) as ll'; cbn; subst ll'.
rewrite List.flat_map_concat_map.
apply nth_concat_same_length with (m := n ^ length (l1 :: ll)). {
  intros ll1 Hll1.
  apply List.in_map_iff in Hll1.
  destruct Hll1 as (a & Hll1 & Ha).
  subst ll1.
  rewrite List.length_map.
  rewrite cart_prod_length; [ | easy ].
  apply iter_list_mul_same_length.
  intros l2 Hl2.
  now apply Hll; right.
} {
  intros ll1 Hll1 l2 Hl2.
  apply List.in_map_iff in Hll1.
  destruct Hll1 as (a & Hll1 & Ha).
  subst ll1.
  apply List.in_map_iff in Hl2.
  destruct Hl2 as (l3 & Hl3 & Hl2).
  subst l2; cbn; f_equal.
  now apply in_cart_prod_length in Hl2.
} {
  rewrite List.length_map.
  rewrite Hll; [ | now left ].
  now rewrite <- Nat.pow_succ_r'.
}
Qed.

Theorem nth_cart_prod_rep_length_seq : ∀ n i,
  i < n ^ n
  → length (List.nth i (cart_prod_rep_seq n) []) = n.
Proof.
intros * Hi.
unfold cart_prod_rep_seq.
rewrite nth_cart_prod_same_length with (n := n). {
  apply List.repeat_length.
} {
  intros l Hl.
  apply List.repeat_spec in Hl; subst l.
  apply List.length_seq.
} {
  now rewrite List.repeat_length.
}
Qed.

Theorem det_isort_rows_with_dup :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_characteristic T = 0 →
  (rngl_is_integral_domain T || rngl_has_inv_or_quot T)%bool = true →
  ∀ A kl,
  is_correct_matrix A = true
  → mat_ncols A = length kl
  → (∀ k, k ∈ kl → 1 ≤ k ≤ mat_nrows A)
  → no_dup Nat.eqb kl = false
  → det (mat_select_rows kl A) =
      (ε kl * det (mat_select_rows (isort Nat.leb kl) A))%L.
Proof.
intros Hon Hop Hic Hch Hii * Hcm Hac Hkl Hadk.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
apply (no_dup_false_iff Nat.eqb_eq) in Hadk.
destruct Hadk as (l1 & l2 & l3 & a & Ha).
rewrite (ε_when_dup Hop). 2: {
  intros H.
  rewrite Ha in H.
  apply List.NoDup_remove_2 in H.
  apply H; clear H.
  apply List.in_or_app; right.
  now apply List.in_or_app; right; left.
}
rewrite rngl_mul_0_l; [ | easy ].
set (p1 := S (length l1)).
set (q1 := S (length (l1 ++ a :: l2))).
apply (determinant_same_rows) with (p := p1) (q := q1); try easy; cycle 1. {
  progress unfold p1, q1.
  rewrite List.length_app; cbn; flia.
} {
  rewrite Ha.
  unfold p1.
  split; [ flia | ].
  rewrite mat_select_rows_nrows.
  rewrite List.length_app; cbn; flia.
} {
  rewrite Ha.
  unfold q1.
  split; [ flia | ].
  rewrite mat_select_rows_nrows.
  rewrite List.length_app; cbn.
  rewrite List.length_app; cbn.
  rewrite List.length_app; cbn; flia.
} {
  intros i Hi.
  unfold p1, q1.
  unfold mat_el; cbn.
  f_equal.
  rewrite (List_map_nth' 0). 2: {
    rewrite Ha.
    rewrite List.length_app; cbn; flia.
  }
  rewrite (List_map_nth' 0). 2: {
    rewrite Ha.
    rewrite List.length_app; cbn.
    rewrite List.length_app; cbn.
    rewrite List.length_app; cbn; flia.
  }
  apply List.map_ext_in.
  intros j Hj.
  do 2 rewrite Nat.sub_0_r.
  rewrite Ha.
  rewrite List.app_nth2; [ | now unfold ge ].
  rewrite Nat.sub_diag; cbn.
  rewrite List.app_nth2; [ | rewrite List.length_app; flia ].
  rewrite List.length_app, Nat.add_comm, Nat.add_sub; cbn.
  rewrite List.app_nth2; [ | now unfold ge ].
  now rewrite Nat.sub_diag.
}
now apply mat_select_rows_is_square.
Qed.

Theorem det_isort_rows_no_dup :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_characteristic T ≠ 1 →
  ∀ A kl,
  is_correct_matrix A = true
  → mat_ncols A = length kl
  → (∀ k, k ∈ kl → 1 ≤ k ≤ mat_nrows A)
  → no_dup Nat.eqb kl = true
  → det (mat_select_rows kl A) =
      (ε kl * det (mat_select_rows (isort Nat.leb kl) A))%L.
Proof.
intros Hon Hop Hic Hch * Hcm Hac Hkl Hadk.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
destruct (Nat.eq_dec (length kl) 0) as [Hkz| Hkz]. {
  apply List.length_zero_iff_nil in Hkz; subst kl.
  cbn; symmetry.
  apply (rngl_mul_1_l Hon).
}
rewrite (det_is_det'' Hon); [ | easy | ]. 2: {
  now apply mat_select_rows_is_square.
}
rewrite (det_is_det'' Hon); [ | easy | ]. 2: {
  apply mat_select_rows_is_square; [ easy | | ]. {
    now rewrite isort_length.
  } {
    intros k Hk.
    apply Hkl.
    now apply in_isort in Hk.
  }
}
unfold det''.
do 2 rewrite mat_select_rows_nrows.
rewrite isort_length.
rewrite rngl_mul_summation_list_distr_l; [ | easy ].
symmetry; erewrite rngl_summation_list_eq_compat. 2: {
  intros jl Hjl.
  now rewrite rngl_mul_assoc.
}
symmetry.
remember (length kl) as n eqn:Hn.
assert (Heql : equality (list_eqv Nat.eqb)). {
  intros la lb.
  apply -> equality_list_eqv.
  unfold equality.
  apply Nat.eqb_eq.
}
set (g1 := λ l, l ° collapse kl).
set (h1 := λ l, l ° isort_rank Nat.leb kl).
assert (Hgh : ∀ l, l ∈ cart_prod_rep_seq n → g1 (h1 l) = l). {
  intros l Hl.
  unfold g1, h1.
  rewrite <- (permut_comp_assoc n); cycle 1. {
    now rewrite isort_rank_length.
  } {
    rewrite Hn.
    apply collapse_length.
  } {
    apply collapse_permut_seq_with_len.
  }
  rewrite permut_comp_isort_rank_r; [ | apply isort_rank_permut_seq ].
  rewrite isort_rank_length, <- Hn.
  apply comp_1_r.
  apply in_cart_prod_rep_seq_iff in Hl.
  now destruct Hl.
}
assert (Hhg : ∀ l, l ∈ cart_prod_rep_seq n → h1 (g1 l) = l). {
  intros l Hl.
  unfold g1, h1.
  rewrite <- (permut_comp_assoc n); cycle 1. {
    now rewrite collapse_length.
  } {
    rewrite Hn.
    apply isort_rank_length.
  } {
    apply isort_rank_permut_seq.
  }
  unfold collapse.
  rewrite permut_comp_isort_rank_l; [ | apply isort_rank_permut_seq ].
  rewrite isort_rank_length, <- Hn.
  apply comp_1_r.
  apply in_cart_prod_rep_seq_iff in Hl.
  now destruct Hl.
}
rewrite rngl_summation_list_change_var with (g := g1) (h := h1); [ | easy ].
rewrite (rngl_summation_list_permut Heql) with (lb := cart_prod_rep_seq n). {
  apply rngl_summation_list_eq_compat.
  intros la Hla.
  f_equal. {
    unfold g1.
    rewrite (sign_comp Hon Hop). 2: {
      apply in_cart_prod_rep_seq_iff in Hla.
      destruct Hla as [Hla| Hla]; [ easy | ].
      destruct Hla as (_ & Hnc & Hcn).
      rewrite Hnc, Hn.
      apply collapse_permut_seq_with_len.
    }
    rewrite (ε_mul_comm Hon Hop).
    f_equal.
    apply ε_collapse_ε.
    now apply (no_dup_NoDup Nat.eqb_eq).
  }
  set (g2 := λ i, S (List.nth (i - 1) (isort_rank Nat.leb kl) 0)).
  set (h2 := λ i, S (List.nth (i - 1) (collapse kl) 0)).
  assert (Hgh2 : ∀ i, 1 ≤ i ≤ n → g2 (h2 i) = i). {
    intros i Hi.
    unfold g2, h2.
    rewrite Nat_sub_succ_1.
    unfold collapse.
    rewrite permut_permut_isort; [ flia Hi | | ]. {
      apply isort_rank_permut_seq.
    }
    rewrite isort_rank_length, <- Hn; flia Hi.
  }
  assert (Hhg2 : ∀ i, 1 ≤ i ≤ n → h2 (g2 i) = i). {
    intros i Hi.
    unfold g2, h2.
    rewrite Nat_sub_succ_1.
    unfold collapse.
    rewrite permut_isort_permut; [ flia Hi | | ]. {
      apply isort_rank_permut_seq.
    }
    rewrite isort_rank_length, <- Hn; flia Hi.
  }
  rewrite rngl_product_change_var with (g := g2) (h := h2); [ | easy ].
  rewrite (rngl_product_list_permut Hon Nat.eqb_eq)
      with (lb := List.seq 1 n); [ | easy | ]. {
    rewrite rngl_product_seq_product; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub.
    apply rngl_product_eq_compat.
    intros i Hi.
    unfold g1.
    unfold "°".
    unfold g2.
    rewrite Nat_sub_succ_1.
    rewrite (List_map_nth' 0). 2: {
      rewrite collapse_length.
      apply isort_rank_ub.
      now intros H; rewrite H in Hn.
    }
    unfold collapse.
    rewrite permut_isort_permut; cycle 1. {
      apply isort_rank_permut_seq.
    } {
      rewrite isort_rank_length, <- Hn.
      flia Hi.
    }
    rewrite <- comp_isort_rank_r.
    unfold "°".
    unfold mat_el.
    f_equal.
    rewrite Nat_sub_succ_1.
    cbn.
    rewrite (List_map_nth' 0). 2: {
      apply isort_rank_ub.
      now intros H; rewrite H in Hn.
    }
    rewrite (List_map_nth' 0). 2: {
      rewrite List.length_map, isort_rank_length, <- Hn.
      flia Hi.
    }
    rewrite (List_map_nth' 0). 2: {
      rewrite isort_rank_length, <- Hn.
      flia Hi.
    }
    easy.
  }
  rewrite Nat_sub_succ_1.
  apply (NoDup_permutation Nat.eqb_eq). {
    apply (NoDup_map_iff 0).
    intros i j Hi Hj Hij.
    rewrite List.length_seq in Hi, Hj.
    rewrite List.seq_nth in Hij; [ | easy ].
    rewrite List.seq_nth in Hij; [ | easy ].
    unfold h2 in Hij.
    apply Nat.succ_inj in Hij.
    do 2 rewrite Nat.add_comm, Nat.add_sub in Hij.
    apply isort_rank_inj in Hij; [ easy | | | ]. {
      apply isort_rank_permut_seq.
    } {
      now rewrite isort_rank_length, <- Hn.
    } {
      now rewrite isort_rank_length, <- Hn.
    }
  } {
    apply List.seq_NoDup.
  }
  intros i.
  split; intros Hi. {
    apply List.in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj); subst i.
    apply List.in_seq in Hj.
    apply List.in_seq.
    unfold h2.
    split; [ flia | cbn ].
    apply -> Nat.succ_lt_mono.
    rewrite Hn.
    rewrite <- (isort_rank_length Nat.leb).
    apply isort_rank_ub.
    intros H.
    apply eq_isort_rank_nil in H.
    now subst kl.
  } {
    apply List.in_seq in Hi.
    apply List.in_map_iff.
    exists (g2 i).
    split; [ apply Hhg2; flia Hi | ].
    apply List.in_seq.
    unfold g2.
    split; [ flia | cbn ].
    apply -> Nat.succ_lt_mono.
    rewrite Hn.
    apply isort_rank_ub.
    intros H.
    now subst kl.
  }
}
apply NoDup_permutation. {
  apply -> equality_list_eqv.
  unfold equality.
  apply Nat.eqb_eq.
} {
  apply (NoDup_map_iff []).
  rewrite cart_prod_rep_length_seq; [ | easy ].
  intros i j Hi Hj Hij.
  unfold h1 in Hij.
  unfold "°" in Hij.
  specialize (List.ext_in_map Hij) as H1.
  assert
    (H : ∀ k, k < n →
     List.nth k (List.nth i (cart_prod_rep_seq n) []) 0 =
       List.nth k (List.nth j (cart_prod_rep_seq n) []) 0). {
    intros k Hk.
    apply H1.
    apply (permutation_in_iff Nat.eqb_eq) with (la := List.seq 0 n). 2: {
      now apply List.in_seq.
    }
    apply (permutation_sym Nat.eqb_eq).
    eapply (permutation_trans Nat.eqb_eq). {
      apply isort_rank_permut_seq.
    }
    rewrite isort_rank_length, <- Hn.
    apply (permutation_refl Nat.eqb_eq).
  }
  clear H1; rename H into H1.
  specialize (cart_prod_rep_seq_inj Hkz Hi Hj) as H2.
  apply H2.
  remember (List.nth i (cart_prod_rep_seq n) []) as la eqn:Hla.
  remember (List.nth j (cart_prod_rep_seq n) []) as lb eqn:Hlb.
  move lb before la.
  apply List_eq_iff.
  split. {
    rewrite Hla, Hlb.
    rewrite nth_cart_prod_rep_length_seq; [ | easy ].
    now rewrite nth_cart_prod_rep_length_seq.
  }
  intros d k.
  destruct (lt_dec k n) as [Hkn| Hkn]. 2: {
    apply Nat.nlt_ge in Hkn.
    rewrite List.nth_overflow. 2: {
      rewrite Hla.
      now rewrite nth_cart_prod_rep_length_seq.
    }
    rewrite List.nth_overflow. 2: {
      rewrite Hlb.
      now rewrite nth_cart_prod_rep_length_seq.
    }
    easy.
  }
  rewrite List.nth_indep with (d' := 0). 2: {
    rewrite Hla.
    now rewrite nth_cart_prod_rep_length_seq.
  }
  symmetry.
  rewrite List.nth_indep with (d' := 0). 2: {
    rewrite Hlb.
    now rewrite nth_cart_prod_rep_length_seq.
  }
  symmetry.
  now apply H1.
} {
  apply NoDup_cart_prod_rep_seq.
}
intros la.
split; intros Hla. {
  apply List.in_map_iff in Hla.
  destruct Hla as (lb & Hla & Hlb); subst la.
  apply in_cart_prod_rep_seq_iff in Hlb.
  destruct Hlb as [Hlb| Hlb]; [ easy | ].
  destruct Hlb as (_ & Hlb & Hlbn).
  unfold h1, "°"; cbn.
  apply in_cart_prod_rep_seq_iff; right.
  split; [ easy | ].
  rewrite List.length_map, isort_rank_length.
  split; [ easy | ].
  intros i Hi.
  apply List.in_map_iff in Hi.
  destruct Hi as (j & Hi & Hj); subst i.
  apply Hlbn, List.nth_In.
  apply in_isort_rank in Hj.
  congruence.
} {
  apply in_cart_prod_rep_seq_iff in Hla.
  destruct Hla as [Hla| Hla]; [ easy | ].
  destruct Hla as (_ & Hlan & Hla).
  apply List.in_map_iff.
  exists (g1 la).
  split. {
    now apply Hhg, in_cart_prod_rep_seq_iff; right.
  }
  apply in_cart_prod_rep_seq_iff; right.
  split; [ easy | ].
  split. {
    unfold g1.
    now rewrite comp_length, collapse_length.
  }
  intros i Hi.
  unfold g1, "°" in Hi.
  apply List.in_map_iff in Hi.
  destruct Hi as (j & Hi & Hj); subst i.
  apply Hla, List.nth_In.
  apply in_isort_rank in Hj.
  rewrite isort_rank_length in Hj.
  congruence.
}
Qed.

Theorem det_isort_rows :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_characteristic T = 0 →
  (rngl_is_integral_domain T || rngl_has_inv_or_quot T)%bool = true →
  ∀ A kl,
  is_correct_matrix A = true
  → mat_ncols A = length kl
  → (∀ k, k ∈ kl → 1 ≤ k ≤ mat_nrows A)
  → det (mat_select_rows kl A) =
      (ε kl * det (mat_select_rows (isort Nat.leb kl) A))%L.
Proof.
intros Hon Hop Hic Hch Hii * Hcm Hac Hkl.
remember (no_dup Nat.eqb kl) as adk eqn:Hadk; symmetry in Hadk.
destruct adk. {
  apply det_isort_rows_no_dup; try easy.
  now intros H; rewrite H in Hch.
} {
  now apply det_isort_rows_with_dup.
}
Qed.

Theorem permutation_filter_app_filter : ∀ A (eqb : A → _),
  equality eqb →
  ∀ f la,
  permutation eqb la (List.filter f la ++ List.filter (λ x, negb (f x)) la).
Proof.
intros * Heqb *.
induction la as [| a]; [ easy | cbn ].
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool (f a)) as [Hfa| Hfa]. {
  rewrite Hfa; cbn.
  apply permutation_skip; [ now intros b; apply Heqb | ].
  apply IHla.
} {
  rewrite Hfa; cbn.
  apply (permutation_cons_app Heqb), IHla.
}
Qed.

Theorem permutation_no_dup_cart_prod_repeat_flat_all_permut_sub_lists : ∀ n m,
  permutation (list_eqv eqb)
    (List.filter (no_dup Nat.eqb) (cart_prod (List.repeat (List.seq 1 n) m)))
    (List.flat_map all_permut (sub_lists_of_seq_1_n n m)).
Proof.
intros.
assert (Hel : equality (list_eqv eqb)). {
  apply -> equality_list_eqv.
  unfold equality.
  apply Nat.eqb_eq.
}
apply permut_if_isort with (rel := list_leb Nat.leb); [ easy | ].
specialize Nat_leb_trans as Htra.
rewrite isort_when_sorted. 2: {
  apply sorted_filter; [ now apply transitive_list_leb | ].
  apply sorted_list_ltb_leb_incl.
  apply cart_prod_repeat_seq_ltb_sorted.
}
symmetry.
unfold sub_lists_of_seq_1_n.
rewrite List.flat_map_concat_map.
rewrite <- List.flat_map_concat_map.
set (la := List.flat_map all_permut (sls1n 1 n m)).
set
  (lb :=
     List.filter (no_dup Nat.eqb) (cart_prod (List.repeat (List.seq 1 n) m))).
assert (Hab : la ⊂ lb). {
  subst la lb.
  intros la Hla.
  apply List.in_flat_map in Hla.
  destruct Hla as (lb & Hlb & Hla).
  apply in_sls1n_iff in Hlb.
  destruct Hlb as [Hlb| Hlb]. {
    destruct Hlb; subst m lb.
    destruct Hla as [Hla| ]; [ subst la | easy ].
    cbn; now left.
  }
  destruct Hlb as (Hsb & Hlb & Hb).
  apply List.filter_In.
  split. {
    apply in_cart_prod_repeat_iff.
    destruct m; [ left | right ]. {
      apply List.length_zero_iff_nil in Hlb; subst lb.
      now destruct Hla.
    }
    split; [ easy | ].
    apply in_all_permut_permutation in Hla.
    split; [ apply permutation_length in Hla; congruence | ].
    intros i Hi.
    specialize (permutation_in_iff Nat.eqb_eq Hla) as H1.
    apply H1 in Hi.
    specialize (Hb _ Hi) as H2.
    split; [ easy | now apply Nat.lt_succ_r ].
  }
  apply in_all_permut_permutation in Hla.
  apply (no_dup_NoDup Nat.eqb_eq).
  apply (sorted_NoDup Nat.ltb_irrefl Nat_ltb_trans) in Hsb.
  apply (permutation_sym Nat.eqb_eq) in Hla.
  now apply (permutation_NoDup Nat.eqb_eq) in Hla.
}
assert (Hba : lb ⊂ la). {
  subst la lb.
  intros la Hla.
  apply List.filter_In in Hla.
  destruct Hla as (Hla, Hnd).
  apply (no_dup_NoDup Nat.eqb_eq) in Hnd.
  apply List.in_flat_map.
  apply (in_cart_prod_iff 0) in Hla.
  rewrite List.repeat_length in Hla.
  destruct Hla as (Hm, Hla).
  rewrite Hm in Hla.
  assert (H : ∀ i, i < m → 1 ≤ List.nth i la 0 ≤ n). {
    intros i Hi.
    specialize (Hla _ Hi) as H1.
    rewrite List_nth_repeat in H1.
    destruct (lt_dec i m); [ | easy ].
    apply List.in_seq in H1.
    split; [ easy | now apply Nat.lt_succ_r ].
  }
  clear Hla; rename H into Hla.
  exists (isort Nat.leb la).
  split. 2: {
    apply permutation_in_all_permut.
    apply permuted_isort; unfold equality.
    apply Nat.eqb_eq.
  }
  apply in_sls1n_iff.
  rewrite isort_length.
  right.
  split. {
    apply NoDup_sorted_nat_leb_ltb. 2: {
      apply sorted_isort; apply Nat_leb_total_relation.
    }
    apply (permutation_NoDup Nat.eqb_eq) with (la := la); [ | easy ].
    apply permuted_isort.
    unfold equality.
    apply Nat.eqb_eq.
  }
  split; [ easy | ].
  intros j Hj.
  apply in_isort in Hj.
  apply (List.In_nth _ _ 0) in Hj.
  destruct Hj as (k & Hk & Hj).
  rewrite Hm in Hk.
  specialize (Hla k Hk) as H1.
  rewrite Hj in H1.
  split; [ easy | now apply Nat.lt_succ_r ].
}
rewrite <- isort_when_sorted with (rel := list_leb Nat.leb) (l := lb). 2: {
  unfold lb.
  apply sorted_filter; [ apply transitive_list_leb, Nat_leb_trans | ].
  apply sorted_list_ltb_leb_incl.
  apply cart_prod_repeat_seq_ltb_sorted.
}
apply (isort_when_permuted Hel). {
  apply antisymmetric_list_leb, Nat_leb_antisym.
} {
  apply transitive_list_leb, Nat_leb_trans.
} {
  apply total_relation_list_leb, Nat_leb_total_relation.
}
apply (incl_incl_permutation Hel); [ | | easy | easy ]. {
  unfold la.
  rewrite List.flat_map_concat_map.
  apply NoDup_concat_if. {
    intros lc Hlc.
    apply List.in_map_iff in Hlc.
    destruct Hlc as (ld & H & Hld); subst lc.
    apply NoDup_all_permut.
    apply in_sls1n_iff in Hld.
    destruct Hld as [Hld| Hld]. {
      destruct Hld; subst m ld; constructor.
    }
    destruct Hld as (Hs & Hdm & Hld).
    now apply (sorted_NoDup Nat.ltb_irrefl Nat_ltb_trans).
  }
  intros i j Hij lc Hlci Hlcj.
  apply Hij; clear Hij.
  destruct (Nat.eq_dec m 0) as [Hmz| Hmz]. {
    subst m.
    rewrite sls1n_0_r in Hlci, Hlcj.
    cbn in Hlci, Hlcj.
    destruct i; [ | now rewrite Tauto_match_nat_same in Hlci ].
    destruct j; [ | now rewrite Tauto_match_nat_same in Hlcj ].
    easy.
  }
  destruct (lt_dec i (binomial n m)) as [Hinm| Hinm]. 2: {
    apply Nat.nlt_ge in Hinm.
    rewrite List.nth_overflow in Hlci; [ easy | ].
    now rewrite List.length_map, sls1n_length.
  }
  destruct (lt_dec j (binomial n m)) as [Hjnm| Hjnm]. 2: {
    apply Nat.nlt_ge in Hjnm.
    rewrite List.nth_overflow in Hlcj; [ easy | ].
    now rewrite List.length_map, sls1n_length.
  }
  rewrite (List_map_nth' []) in Hlci; [ | now rewrite sls1n_length ].
  rewrite (List_map_nth' []) in Hlcj; [ | now rewrite sls1n_length ].
  apply in_all_permut_permutation in Hlci.
  apply in_all_permut_permutation in Hlcj.
  apply (permutation_sym Nat.eqb_eq) in Hlci.
  eapply (permutation_trans Nat.eqb_eq) in Hlcj; [ | apply Hlci ].
  specialize sorted_sorted_permuted as H1.
  apply (H1 _ _ Nat.ltb) in Hlcj; cycle 1. {
    unfold equality; apply Nat.eqb_eq.
  } {
    apply Nat_ltb_antisym.
  } {
    apply Nat_ltb_trans.
  } {
    apply (sls1n_are_sorted 1 n m), List.nth_In.
    now rewrite sls1n_length.
  } {
    apply (sls1n_are_sorted 1 n m), List.nth_In.
    now rewrite sls1n_length.
  }
  now apply sls1n_inj in Hlcj.
} {
  unfold lb.
  apply List.NoDup_filter.
  apply NoDup_cart_prod_repeat.
}
Qed.

Theorem rngl_summation_cart_prod_repeat_filter_no_dup :
  rngl_has_opp T = true →
  ∀ n m f,
  ∑ (kl ∈ cart_prod (List.repeat (List.seq 1 n) m)),
    ε kl * f kl =
  ∑ (kl ∈
       List.filter (no_dup Nat.eqb)
         (cart_prod (List.repeat (List.seq 1 n) m))),
    ε kl * f kl.
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
assert (Hel : equality (list_eqv eqb)). {
  apply -> equality_list_eqv.
  unfold equality.
  apply Nat.eqb_eq.
}
set (g := no_dup Nat.eqb).
erewrite (rngl_summation_list_permut Hel). 2: {
  assert (H : ∀ ll,
    permutation (list_eqv eqb) ll
      (List.filter g ll ++ List.filter (λ l, negb (g l)) ll)). {
    now apply permutation_filter_app_filter.
  }
  apply H.
}
rewrite rngl_summation_list_app.
rewrite rngl_add_comm.
rewrite all_0_rngl_summation_list_0. 2: {
  intros kl Hkl.
  apply List.filter_In in Hkl.
  destruct Hkl as (Hkl, Hsl).
  unfold g in Hsl.
  apply Bool.negb_true_iff in Hsl.
  rewrite ε_when_dup; [ | easy | ]. 2: {
    intros H.
    apply (no_dup_NoDup Nat.eqb_eq) in H.
    congruence.
  }
  now apply rngl_mul_0_l.
}
subst g.
rewrite rngl_add_0_l.
easy.
Qed.

Theorem rngl_summation_cart_prod_sub_lists_all_permut :
  rngl_has_opp T = true →
  ∀ n m f,
  ∑ (kl ∈ cart_prod (List.repeat (List.seq 1 n) m)), ε kl * f kl =
  ∑ (jl ∈ sub_lists_of_seq_1_n n m), ∑ (kl ∈ all_permut jl), ε kl * f kl.
Proof.
intros Hopp *.
assert (Hel : equality (list_eqv eqb)). {
  apply -> equality_list_eqv.
  unfold equality.
  apply Nat.eqb_eq.
}
rewrite rngl_summation_cart_prod_repeat_filter_no_dup; [ | easy ].
rewrite rngl_summation_summation_list_flat_map; cbn.
apply (rngl_summation_list_permut Hel).
apply permutation_no_dup_cart_prod_repeat_flat_all_permut_sub_lists.
Qed.

Definition det''' (M : matrix T) :=
  let n := mat_nrows M in
  ∑ (l ∈ all_permut (List.seq 1 n)), ε l * ∏ (i = 1, n), mat_el M i l.(i).

(* (I am not happy of this definition; it is close to det' since both
    use canon_sym_gr_list but with a different way, and I don't know
    how to fix it) *)

Theorem fold_det''' : ∀ n M,
  mat_nrows M = n
  → ∑ (l ∈ all_permut (List.seq 1 n)), ε l * ∏ (i = 1, n), mat_el M i l.(i) =
    det''' M.
Proof. now intros; subst n. Qed.

Theorem det_is_det''' :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ M, is_square_matrix M = true
  → det M = det''' M.
Proof.
intros Hon Hop * Hm.
rewrite (det_is_det'' Hon); [ | easy | easy ].
unfold det'', det'''.
unfold cart_prod_rep_seq.
rewrite rngl_summation_cart_prod_sub_lists_all_permut; [ | easy ].
unfold sub_lists_of_seq_1_n.
rewrite sls1n_diag.
now rewrite rngl_summation_list_only_one.
Qed.

Theorem map_collapse_all_permut_seq : ∀ i la n m,
  la ∈ sub_lists_of_seq_1_n n m
  → List.map (λ lb, List.map (add i) (collapse lb)) (all_permut la) =
    all_permut (List.seq i (length la)).
Proof.
intros * Hla.
destruct la as [| a]; intros; [ easy | ].
cbn - [ all_permut List.seq ].
unfold all_permut.
rewrite <- List.cons_seq at 1.
rewrite List.length_seq.
rewrite List.map_map.
apply List.map_ext_in.
intros lb Hlb.
apply List.in_map_iff in Hlb.
destruct Hlb as (k & Hlb & Hk).
apply List.in_seq in Hk; destruct Hk as (_, Hk); rewrite Nat.add_0_l in Hk.
subst lb.
erewrite List.map_ext_in with (f := λ j, List.nth _ (List.seq _ _) _). 2: {
  intros j Hj.
  apply in_canon_sym_gr_list in Hj; [ | easy ].
  now rewrite List.seq_nth.
}
f_equal.
clear i.
erewrite List.map_ext_in. 2: {
  intros j Hj.
  rewrite List.nth_indep with (d' := 0). 2: {
    now apply in_canon_sym_gr_list in Hj.
  }
  easy.
}
remember (a :: la) as lb eqn:Hlb.
replace (S (length la)) with (length lb) in Hk |-* by now subst lb.
clear a la Hlb; rename lb into la.
rewrite fold_comp_list.
apply in_sls1n_iff in Hla.
destruct Hla as [Hla| Hla]; [ now destruct Hla; subst m la | ].
destruct Hla as (Hs & Hlam & Hla).
rewrite collapse_comp; cycle 1. {
  now apply (sorted_NoDup Nat.ltb_irrefl Nat_ltb_trans).
} {
  now apply canon_sym_gr_list_permut_seq.
} {
  symmetry; apply canon_sym_gr_list_length.
}
rewrite eq_sorted_collapse_seq; [ | now apply sorted_nat_ltb_leb_incl ].
apply comp_1_l.
intros i Hi.
now apply in_canon_sym_gr_list in Hi.
Qed.

Theorem permutation_seq_collapse : ∀ la,
  permutation eqb la (List.seq 1 (length la))
  → collapse la = List.map pred la.
Proof.
intros * Hp.
assert (H1 : ∀ a, a ∈ la → 1 ≤ a ≤ length la). {
  intros a Ha.
  specialize (permutation_in_iff Nat.eqb_eq Hp a) as H1.
  specialize (proj1 H1 Ha) as H2.
  apply List.in_seq in H2.
  split; [ easy | flia H2 ].
}
apply (permutation_map Nat.eqb_eq Nat.eqb_eq pred) in Hp.
rewrite List_map_seq, List.map_id in Hp.
remember (List.map pred la) as lb eqn:Hlb.
assert (Hab : la = List.map S lb). {
  rewrite Hlb, List.map_map.
  erewrite List.map_ext_in. 2: {
    intros a Ha.
    rewrite Nat.succ_pred; [ | specialize (H1 _ Ha); flia H1 ].
    easy.
  }
  symmetry; apply List.map_id.
}
rewrite Hab, List.length_map in Hp.
rewrite Hab.
clear la Hlb H1 Hab.
rename lb into la.
unfold collapse.
specialize (isort_rank_map_add_compat 1 0 la) as H1.
replace (add 1) with S in H1 by easy; rewrite H1.
cbn; rewrite List.map_id; clear H1.
rewrite fold_collapse.
now apply permut_collapse.
Qed.

Theorem mat_select_all_rows : ∀ A,
  is_square_matrix A = true
  → mat_select_rows (List.seq 1 (mat_nrows A)) A = A.
Proof.
intros * Hsm.
specialize (squ_mat_ncols A Hsm) as Hc.
generalize Hsm; intros H.
apply is_scm_mat_iff in H.
destruct H as (_, Hcla).
unfold mat_select_rows.
destruct A as (lla); cbn; f_equal.
cbn in Hsm, Hc, Hcla.
apply List_eq_iff.
rewrite List_length_map_seq.
split; [ easy | ].
intros d i.
destruct (lt_dec i (length lla)) as [Hila| Hila]. 2: {
  apply Nat.nlt_ge in Hila.
  rewrite List.nth_overflow; [ | now rewrite List_length_map_seq ].
  now rewrite List.nth_overflow.
}
rewrite (List_map_nth' 0); [ | now rewrite List.length_seq ].
rewrite List.seq_nth; [ | easy ].
rewrite Nat.add_comm, Nat.add_sub.
rewrite Hc.
rewrite <- List.seq_shift, List.map_map; cbn.
erewrite List.map_ext_in; [ | now intros; rewrite Nat.sub_0_r ].
specialize (List_map_nth_seq 0%L (List.nth i lla [])) as H1.
rewrite Hcla in H1 by now apply List.nth_In.
rewrite <- H1.
now symmetry; apply List.nth_indep.
Qed.

Theorem mat_select_all_cols : ∀ A,
  is_square_matrix A = true
  → mat_select_cols (List.seq 1 (mat_ncols A)) A = A.
Proof.
intros * Hsm.
unfold mat_select_cols.
rewrite <- mat_transp_nrows.
rewrite mat_select_all_rows. {
  apply mat_transp_involutive.
  now apply squ_mat_is_corr.
} {
  now apply mat_transp_is_square.
}
Qed.

(* Cauchy-Binet formula in several steps *)
(* https://proofwiki.org/wiki/Cauchy-Binet_Formula *)

Lemma Cauchy_Binet_formula_step_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  ∀ [m n A B], m ≠ 0 →
  mat_nrows A = m
  → mat_ncols A = n
  → mat_ncols B = m
  → det (A * B) =
      ∑ (l ∈ cart_prod_rep_seq m),
        ε l * ∏ (i = 1, m), (∑ (k = 1, n), mat_el A i k * mat_el B k l.(i)).
Proof.
intros Hon Hop Hch * Hmz Har Hac Hbc.
assert (Hab : is_square_matrix (A * B) = true). {
  apply is_scm_mat_iff.
  split. {
    rewrite mat_mul_ncols; [ | now rewrite Har ].
    now intros H; rewrite H in Hbc; symmetry in Hbc.
  } {
    intros l Hl.
    rewrite mat_mul_nrows, Har.
    apply List.In_nth with (d := []) in Hl.
    destruct Hl as (p & Hp & Hl).
    rewrite <- Hl; cbn.
    progress unfold mat_list_list_mul.
    rewrite (List_map_nth' 0). 2: {
      rewrite List.length_seq.
      cbn in Hp.
      progress unfold mat_list_list_mul in Hp.
      now rewrite List_length_map_seq in Hp.
    }
    now rewrite List_length_map_seq.
  }
}
rewrite (det_is_det'' Hon); [ | easy | easy ].
unfold det''.
rewrite mat_mul_nrows, Har.
(*
  ∑ (l ∈ cart_prod_rep_seq m),
    ε l * ∏ (i = 1, m), mat_el (A * B) i l.(i) =
  ∑ (l ∈ cart_prod_...

*)
unfold "*"%M at 1.
progress unfold mat_list_list_mul.
cbn.
unfold mat_mul_el.
rewrite Har, Hac, Hbc.
cbn - [ det ].
apply rngl_summation_list_eq_compat.
intros l Hl.
erewrite rngl_product_eq_compat; [ easy | ].
intros i Hi.
specialize (fact_neq_0 m) as Hm.
rewrite (List_map_nth' 0); [ | rewrite List.length_seq; flia Hi ].
rewrite List.seq_nth; [ | flia Hi ].
rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
assert (Him : l.(i) - 1 < m). {
  apply in_cart_prod_rep_seq_iff in Hl.
  destruct Hl as [Hl| Hl]; [ easy | ].
  destruct Hl as (_ & Hlm & Hl).
  assert (H : l.(i) ∈ l). {
    apply List.nth_In.
    rewrite Hlm; flia Hi.
  }
  specialize (Hl _ H); clear H.
  flia Hl.
}
rewrite (List_map_nth' 0); [ | now rewrite List.length_seq ].
rewrite List.seq_nth; [ | easy ].
rewrite Nat.add_comm.
rewrite Nat.sub_add; [ easy | ].
apply in_cart_prod_rep_seq_iff in Hl.
destruct Hl as [Hl| Hl]; [ easy | ].
destruct Hl as (_ & Hlm & Hl).
assert (H : List.nth (i - 1) l 0 ∈ l). {
  apply List.nth_In.
  rewrite Hlm; flia Hi.
}
now specialize (Hl _ H).
Qed.

Lemma Cauchy_Binet_formula_step_2 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  ∀ [m n A B], m ≠ 0 →
  ∑ (l ∈ cart_prod_rep_seq m),
    ε l * ∏ (i = 1, m), (∑ (j = 1, n), mat_el A i j * mat_el B j l.(i)) =
  ∑ (kl ∈ cart_prod (List.repeat (List.seq 1 n) m)),
    (∏ (i = 1, m), mat_el A i kl.(i)) *
    (∑ (l ∈ cart_prod_rep_seq m), ε l * ∏ (i = 1, m), mat_el B kl.(i) l.(i)).
Proof.
intros Hon Hop Hic * Hmz.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
erewrite rngl_summation_list_eq_compat. 2: {
  intros l Hl.
  rewrite (rngl_product_summation_distr_cart_prod Hon); [ | easy | easy ].
  remember (∑ (kl ∈ _), _) as x; subst x.
  easy.
}
cbn - [ det].
remember (∑ (l ∈ _), _) as x; subst x.
(*
  ∑ (l ∈ cart_prod_rep_seq m),
    ε l *
    (∑ (kl ∈ cart_prod (repeat (List.seq 1 n) m)),
       ∏ (i = 1, m), (mat_el A i kl.(i) * mat_el B kl.(i) l.(i))) =
  ∑ (kl ∈ cart_prod ...
*)
erewrite rngl_summation_list_eq_compat. 2: {
  intros l Hl.
  erewrite rngl_summation_list_eq_compat. 2: {
    intros kl Hkl.
    rewrite (rngl_product_mul_distr Hon); [ | easy ].
    easy.
  }
  easy.
}
cbn.
remember (∑ (l ∈ _), _) as x; subst x.
(*
  ∑ (l ∈ cart_prod_rep_seq m),
    ε l *
    (∑ (i ∈ cart_prod (repeat (List.seq 1 n) m)),
       ∏ (i0 = 1, m), mat_el A i0 i.(i0) *
       ∏ (i0 = 1, m), mat_el B i.(i0) l.(i0)) =
  ∑ (kl ∈ cart_prod ...
*)
erewrite rngl_summation_list_eq_compat. 2: {
  intros l Hl.
  rewrite rngl_mul_summation_list_distr_l; [ | easy ].
  erewrite rngl_summation_list_eq_compat. 2: {
    intros kl Hkl.
    rewrite rngl_mul_assoc.
    easy.
  }
  remember (∑ (kl ∈ _), _) as x; subst x.
  easy.
}
cbn.
remember (∑ (l ∈ _), _) as x; subst x.
(*
  ∑ (l ∈ cart_prod_rep_seq m),
    (∑ (kl ∈ cart_prod (repeat (List.seq 1 n) m)),
       ε l * ∏ (i = 1, m), mat_el A i kl.(i) *
       ∏ (i = 1, m), mat_el B kl.(i) l.(i)) =
  ∑ (kl ∈ cart_prod ...
*)
rewrite rngl_summation_summation_list_swap.
erewrite rngl_summation_list_eq_compat. 2: {
  intros kl Hkl.
  remember (∑ (l ∈ _), _) as x; subst x.
  easy.
}
cbn.
remember (∑ (kl ∈ _), _) as x; subst x.
(*
  ∑ (kl ∈ cart_prod (repeat (List.seq 1 n) m)),
    (∑ (l ∈ cart_prod_rep_seq m),
       ε l * ∏ (i = 1, m), mat_el A i kl.(i) *
       ∏ (i = 1, m), mat_el B kl.(i) l.(i)) =
  ∑ (kl ∈ cart_prod ...
*)
apply rngl_summation_list_eq_compat.
intros kl Hkl.
erewrite rngl_summation_list_eq_compat. 2: {
  intros l Hl.
  rewrite rngl_mul_mul_swap; [ | easy ].
  easy.
}
cbn.
rewrite <- rngl_mul_summation_list_distr_r; [ | easy ].
rewrite rngl_mul_comm; [ | easy ].
easy.
Qed.

Lemma Cauchy_Binet_formula_step_3 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  ∀ [m n] f [B], m ≠ 0 →
  is_correct_matrix B = true
  → mat_nrows B = n
  → mat_ncols B = m
  → ∑ (kl ∈ cart_prod (List.repeat (List.seq 1 n) m)),
      f kl *
      (∑ (l ∈ cart_prod_rep_seq m),
         ε l * ∏ (i = 1, m), mat_el B kl.(i) l.(i)) =
    ∑ (kl ∈ cart_prod (List.repeat (List.seq 1 n) m)),
      f kl * det (mat_select_rows kl B).
Proof.
intros Hon Hop Hch * Hmz Hcb Hbr Hbc.
apply rngl_summation_list_eq_compat.
intros l Hl.
f_equal.
generalize Hl; intros H.
apply in_cart_prod_repeat_iff in H.
destruct H as [H| H]; [ easy | ].
destruct H as (_ & Hlm & Hln).
rewrite (det_is_det'' Hon); [ | easy | ]. 2: {
  apply mat_select_rows_is_square; [ easy | congruence | ].
  rewrite Hbr.
  intros j Hj.
  now apply Hln.
}
unfold det''.
rewrite mat_select_rows_nrows, Hlm.
apply rngl_summation_list_eq_compat.
intros l1 Hl1.
f_equal.
apply rngl_product_eq_compat.
intros i Hi.
unfold mat_select_rows, mat_el; cbn.
rewrite (List_map_nth' 0); [ | rewrite Hlm; flia Hi ].
assert (H1 : l1.(i) - 1 < m). {
  apply in_cart_prod_repeat_iff in Hl1.
  destruct Hl1 as [Hl1| Hl1]; [ easy | ].
  destruct Hl1 as (_ & Hl1m & Hl1).
  specialize (Hl1 (List.nth (i - 1) l1 0)).
  assert (H : List.nth (i - 1) l1 0 ∈ l1). {
    apply List.nth_In; rewrite Hl1m; flia Hi.
  }
  specialize (Hl1 H); clear H.
  flia Hl1.
}
rewrite (List_map_nth' 0); [ | now rewrite List.length_seq, Hbc ].
rewrite List.seq_nth; [ | now rewrite Hbc ].
now rewrite Nat.add_comm, Nat.add_sub.
Qed.

Lemma Cauchy_Binet_formula_step_4 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_characteristic T = 0 →
  (rngl_is_integral_domain T || rngl_has_inv_or_quot T)%bool = true →
  ∀ [m n] [B] f, m ≠ 0 →
  is_correct_matrix B = true
  → mat_nrows B = n
  → mat_ncols B = m
  → ∑ (kl ∈ cart_prod (List.repeat (List.seq 1 n) m)),
      f kl * det (mat_select_rows kl B) =
    ∑ (kl ∈ cart_prod (List.repeat (List.seq 1 n) m)),
      ε kl * f kl * det (mat_select_rows (isort Nat.leb kl) B).
Proof.
intros Hon Hop Hic Hch Hii * Hmz Hcb Hbr Hbc.
apply rngl_summation_list_eq_compat.
intros la Hla.
rewrite (det_isort_rows Hon Hop Hic Hch Hii _ _ Hcb); cycle 1. {
  apply in_cart_prod_length in Hla.
  rewrite List.repeat_length in Hla.
  congruence.
} {
  intros k Hk.
  apply in_cart_prod_repeat_iff in Hla.
  destruct Hla as [| Hla]; [ easy | ].
  destruct Hla as (_ & Hlam & Hla).
  rewrite Hbr.
  now apply Hla.
}
rewrite rngl_mul_assoc.
now rewrite (rngl_mul_comm Hic _ (ε la)).
Qed.

Lemma Cauchy_Binet_formula_step_5_1 :
  rngl_has_opp T = true →
  ∀ m n A B,
  ∑ (kl ∈ cart_prod (List.repeat (List.seq 1 n) m)),
    ε kl * ∏ (i = 1, m), mat_el A i kl.(i) *
    det (mat_select_rows (isort Nat.leb kl) B) =
  ∑ (jl ∈ sub_lists_of_seq_1_n n m),
    (∑ (kl ∈ all_permut jl), ε kl * ∏ (i = 1, m), mat_el A i kl.(i)) *
    det (mat_select_rows jl B).
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
erewrite rngl_summation_list_eq_compat. 2: {
  intros kl Hkl.
  now rewrite <- rngl_mul_assoc.
}
cbn - [ det ].
remember (∑ (kl ∈ _), _) as x; subst x.
rewrite rngl_summation_cart_prod_sub_lists_all_permut; [ | easy ].
(*
  ∑ (jl ∈ sub_lists_of_seq_1_n n m),
    (∑ (kl ∈ all_permut jl),
       ε kl * (∏ (i = 1, m), mat_el A i kl.(i) *
       det (mat_select_rows (isort Nat.leb kl) B))) =
  ∑ (jl ∈ sub_lists_...
*)
apply rngl_summation_list_eq_compat.
intros jl Hjl.
erewrite rngl_summation_list_eq_compat. 2: {
  intros kl Hkl.
  replace (isort Nat.leb kl) with jl. 2: {
    symmetry.
    apply in_all_permut_permutation in Hkl.
    rewrite (isort_when_permuted Nat.eqb_eq) with (lb := jl); cycle 1. {
      apply Nat_leb_antisym.
    } {
      apply Nat_leb_trans.
    } {
      apply Nat_leb_total_relation.
    } {
      easy.
    }
    apply isort_when_sorted.
    apply (sub_lists_of_seq_1_n_are_sorted n m) in Hjl; [ | easy ].
    now apply sorted_nat_ltb_leb_incl.
  }
  rewrite rngl_mul_assoc.
  easy.
}
cbn - [ det ].
symmetry.
apply (rngl_mul_summation_list_distr_r Hos).
Qed.

Lemma Cauchy_Binet_formula_step_5_2 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ [m n A] f, m ≠ 0 →
  ∑ (jl ∈ sub_lists_of_seq_1_n n m),
    (∑ (kl ∈ all_permut jl), ε kl * ∏ (i = 1, m), mat_el A i kl.(i)) *
    f jl =
  ∑ (jl ∈ sub_lists_of_seq_1_n n m),
    (∑ (kl ∈ all_permut (List.seq 1 m)),
       ε kl * ∏ (i = 1, m), mat_el A i jl.(kl.(i))) *
    f jl.
Proof.
intros Hon Hop * Hmz.
apply rngl_summation_list_eq_compat.
intros jl Hjl.
f_equal.
generalize Hjl; intros H.
apply in_sls1n_iff in H.
destruct H as [H| H]; [ easy | ].
destruct H as (Hsj & Hjm & Hjlb).
set (g1 := λ l, jl ° collapse l).
set (h1 := λ l, List.map S (collapse l)).
rewrite rngl_summation_list_change_var with (g := g1) (h := h1). 2: {
  intros kl Hkl.
  unfold g1, h1.
  replace (collapse (List.map S (collapse kl))) with (collapse kl). 2: {
    symmetry.
    unfold collapse at 1 3; f_equal.
    specialize (isort_rank_map_add_compat 1 0) as H1.
    rewrite H1; cbn.
    rewrite List.map_id.
    unfold collapse.
    apply permut_isort_rank_involutive.
    apply isort_rank_permut_seq.
  }
  apply in_all_permut_permutation in Hkl.
  apply sorted_permuted_comp_collapse. 2: {
    now apply (permutation_sym Nat.eqb_eq).
  }
  now apply sorted_nat_ltb_leb_incl.
}
replace (List.map h1 (all_permut jl)) with (all_permut (List.seq 1 m)). 2: {
  symmetry.
  unfold h1.
  specialize (map_collapse_all_permut_seq 1 _ _ _ Hjl) as H1.
  replace (add 1) with S in H1 by easy.
  now rewrite Hjm in H1.
}
remember (∑ (kl ∈ _), _) as x; subst x.
unfold g1.
apply rngl_summation_list_eq_compat.
intros kl Hkl.
f_equal. {
  unfold g1.
  assert (Hndj : List.NoDup jl). {
    apply sorted_NoDup in Hsj; [ easy | | ]. {
      unfold irreflexive; apply Nat.ltb_irrefl.
    } {
      apply Nat_ltb_trans.
    }
  }
  assert (Hkm : length kl = m). {
    apply in_all_permut_permutation in Hkl.
    apply permutation_length in Hkl.
    now rewrite List.length_seq in Hkl.
  }
  rewrite <- ε_collapse_ε. 2: {
    apply NoDup_comp_iff; [ | easy ].
    rewrite Hjm, <- Hkm.
    apply collapse_permut_seq_with_len.
  }
  rewrite collapse_comp; [ | easy | | ]; cycle 1. {
    apply isort_rank_permut_seq.
  } {
    rewrite collapse_length; congruence.
  }
  symmetry.
  rewrite <- ε_collapse_ε. 2: {
    apply in_all_permut_permutation in Hkl.
    apply (permutation_sym Nat.eqb_eq) in Hkl.
    apply (permutation_NoDup Nat.eqb_eq) in Hkl; [ easy | ].
    apply List.seq_NoDup.
  }
  symmetry.
  rewrite (sign_comp Hon Hop). 2: {
    rewrite collapse_length, Hjm, <- Hkm.
    apply collapse_permut_seq_with_len.
  }
  replace (collapse jl) with (List.seq 0 (length jl)). 2: {
    symmetry.
    apply sorted_nat_ltb_leb_incl in Hsj.
    apply (eq_sorted_isort_rank_seq Nat_leb_trans) in Hsj.
    unfold collapse; rewrite Hsj.
    apply isort_rank_leb_seq.
  }
  now rewrite ε_seq, (rngl_mul_1_l Hon).
}
apply rngl_product_eq_compat.
intros i Hi.
f_equal.
unfold comp_list.
assert (Hkm : length kl = m). {
  apply in_all_permut_permutation in Hkl.
  apply permutation_length in Hkl.
  now rewrite List.length_seq in Hkl.
}
rewrite (List_map_nth' 0); [ | rewrite collapse_length, Hkm; flia Hi ].
f_equal.
rewrite <- Hkm in Hkl, Hi.
apply in_all_permut_permutation in Hkl.
apply permutation_seq_collapse in Hkl.
rewrite Hkl.
rewrite (List_map_nth' 0); [ flia | flia Hi ].
Qed.

Lemma Cauchy_Binet_formula_step_5_3 :
  ∀ [m n A] f, m ≠ 0 →
  mat_nrows A = m
  → mat_ncols A = n
  → ∑ (jl ∈ sub_lists_of_seq_1_n n m),
       (∑ (kl ∈ all_permut (List.seq 1 m)),
          ε kl * ∏ (i = 1, m), mat_el A i jl.(kl.(i))) * f jl =
     ∑ (jl ∈ sub_lists_of_seq_1_n n m),
       (∑ (kl ∈ all_permut (List.seq 1 m)),
          ε kl * ∏ (i = 1, m), mat_el (mat_select_cols jl A) i kl.(i)) * f jl.
Proof.
intros * Hmz Har Hac.
apply rngl_summation_list_eq_compat.
intros jl Hjl.
f_equal; symmetry.
generalize Hjl; intros H.
apply in_sls1n_iff in H.
destruct H as [H| H]; [ easy | ].
destruct H as (Hsj & Hjm & Hjlb).
apply rngl_summation_list_eq_compat.
intros kl Hkl.
apply in_all_permut_iff in Hkl.
generalize Hkl; intros Hpk.
apply (permut_if_isort _ Nat.eqb_eq) in Hpk.
rewrite (@isort_when_sorted _ _ (List.seq 1 m)) in Hkl. 2: {
  apply sorted_nat_ltb_leb_incl.
  apply sorted_seq.
}
f_equal.
apply rngl_product_eq_compat.
intros i Hi.
rewrite mat_select_cols_el; [ easy | now rewrite Har | | ]. {
  rewrite Hjm.
  assert (Hklen : length kl = m). {
    apply (f_equal (λ l, length l)) in Hkl.
    now rewrite isort_length, List.length_seq in Hkl.
  }
  rewrite <- Hklen in Hpk.
  specialize (permutation_in_iff Nat.eqb_eq) as Hp.
  specialize (Hp _ _ Hpk).
  assert (H : kl.(i) ∈ kl). {
    apply List.nth_In; rewrite Hklen; flia Hi.
  }
  apply Hp in H.
  rewrite Hklen in H.
  apply List.in_seq in H.
  split; [ easy | flia H ].
} {
  rewrite Hac.
  intros j Hj.
  specialize (Hjlb jl.(j)).
  assert (H : jl.(j) ∈ jl) by (apply List.nth_In; flia Hj).
  specialize (Hjlb H); clear H.
  flia Hjlb.
}
Qed.

Lemma Cauchy_Binet_formula_step_5_4 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  ∀ [m n A] f, m ≠ 0 → n ≠ 0 →
  is_correct_matrix A = true
  → mat_nrows A = m
  → mat_ncols A = n
  → ∑ (jl ∈ sub_lists_of_seq_1_n n m),
      (∑ (kl ∈ all_permut (List.seq 1 m)),
         ε kl * ∏ (i = 1, m), mat_el (mat_select_cols jl A) i kl.(i)) *
      f jl =
    ∑ (jl ∈ sub_lists_of_seq_1_n n m),
      det (mat_select_cols jl A) * f jl.
Proof.
intros Hon Hop H10 * Hmz Hnz Hca Har Hac.
apply rngl_summation_list_eq_compat.
intros jl Hjl.
f_equal.
rewrite fold_det'''. 2: {
  rewrite mat_select_cols_nrows; [ easy | | congruence ].
  now apply sub_lists_of_seq_1_n_are_correct in Hjl.
}
rewrite <- (det_is_det''' Hon); [ easy | easy | ].
generalize Hjl; intros H.
apply in_sub_lists_of_seq_1_n_length in H.
apply mat_select_cols_is_square; [ easy | congruence | ].
rewrite Hac.
intros j Hj.
now apply sub_lists_of_seq_1_n_bounds with (a := j) in Hjl.
Qed.

Theorem Cauchy_Binet_formula :
  charac_0_field T →
  ∀ m n A B,
  is_correct_matrix A = true
  → is_correct_matrix B = true
  → mat_nrows A = m
  → mat_ncols A = n
  → mat_nrows B = n
  → mat_ncols B = m
  → det (A * B) =
     ∑ (jl ∈ sub_lists_of_seq_1_n n m),
     det (mat_select_cols jl A) * det (mat_select_rows jl B).
Proof.
intros Hif * Hca Hcb Har Hac Hbr Hbc.
assert (Hon : rngl_has_1 T = true) by now destruct Hif.
assert (Hop : rngl_has_opp T = true) by now destruct Hif.
assert (Hiv : rngl_has_inv T = true) by now destruct Hif.
assert (Hic : rngl_mul_is_comm T = true) by now destruct Hif.
assert (Hch : rngl_characteristic T = 0) by now destruct Hif.
assert (H10 : rngl_characteristic T ≠ 1) by now rewrite Hch.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hi1.
assert
  (Hii : (rngl_is_integral_domain T || rngl_has_inv_or_quot T)%bool = true). {
  destruct Hif.
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_or_quot_iff; left.
}
clear Hif.
destruct (Nat.eq_dec m 0) as [Hmz| Hmz]. {
  move Hmz at top; subst m.
  apply is_scm_mat_iff in Hcb.
  destruct Hcb as (Hcrb, Hclb).
  specialize (Hcrb Hbc) as H1.
  rewrite Hbr in H1.
  move H1 at top; subst n.
  destruct A as (lla).
  destruct B as (llb).
  cbn in Har, Hbr.
  apply List.length_zero_iff_nil in Har, Hbr.
  subst lla llb; cbn.
  rewrite rngl_summation_list_only_one; cbn.
  symmetry; apply (rngl_mul_1_l Hon).
}
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  apply is_scm_mat_iff in Hca.
  destruct Hca as (Hcra, Hcla).
  specialize (Hcra Hac) as H1.
  now rewrite Har in H1.
}
rewrite (Cauchy_Binet_formula_step_1 Hon Hop H10 Hmz Har Hac Hbc).
(*
  ∑ (l ∈ cart_prod_rep_seq m),
    ε l * ∏ (i = 1, m), (∑ (k = 1, n), mat_el A i k * mat_el B k l.(i)) =
  ∑ (jl ∈ sub_lists...
*)
rewrite (Cauchy_Binet_formula_step_2 Hon Hop Hic Hmz).
(*
  ∑ (kl ∈ cart_prod (repeat (List.seq 1 n) m)),
    (∏ (i = 1, m), mat_el A i kl.(i)) *
    (∑ (l ∈ cart_prod_rep_seq m), ε l * ∏ (i = 1, m), mat_el B kl.(i) l.(i)) =
  ∑ (jl ∈ sub_lists...
*)
rewrite (Cauchy_Binet_formula_step_3 Hon Hop H10 _ Hmz Hcb Hbr Hbc).
(*
  ∑ (kl ∈ cart_prod (repeat (List.seq 1 n) m)),
    (∏ (i = 1, m), mat_el A i kl.(i)) * det (mat_select_rows kl B) =
  ∑ (jl ∈ sub_lists...
*)
rewrite (Cauchy_Binet_formula_step_4 Hon Hop Hic Hch Hii _ Hmz Hcb Hbr Hbc).
(*
  ∑ (kl ∈ cart_prod (repeat (List.seq 1 n) m)),
    ε kl * ∏ (i = 1, m), mat_el A i kl.(i) *
    det (mat_select_rows (isort Nat.leb kl) B) =
  ∑ (jl ∈ sub_lists...
*)
rewrite (Cauchy_Binet_formula_step_5_1 Hop).
(*
  ∑ (jl ∈ sub_lists_of_seq_1_n n m),
    (∑ (kl ∈ all_permut jl), ε kl * ∏ (i = 1, m), mat_el A i kl.(i)) *
    det (mat_select_rows jl B) =
  ∑ (jl ∈ sub_lists_...
*)
rewrite (Cauchy_Binet_formula_step_5_2 Hon Hop _ Hmz).
(*
  ∑ (jl ∈ sub_lists_of_seq_1_n n m),
    (∑ (kl ∈ all_permut (List.seq 1 m)),
       ε kl * ∏ (i = 1, m), mat_el A i jl.(kl.(i))) *
    det (mat_select_rows jl B) =
  ∑ (jl ∈ sub_lists_...
*)
rewrite (Cauchy_Binet_formula_step_5_3 _ Hmz Har Hac).
(*
  ∑ (jl ∈ sub_lists_of_seq_1_n n m),
    (∑ (kl ∈ all_permut (List.seq 1 m)),
       ε kl * ∏ (i = 1, m), mat_el (mat_select_cols jl A) i kl.(i)) *
    det (mat_select_rows jl B) =
  ∑ (jl ∈ sub_lists_...
*)
rewrite (Cauchy_Binet_formula_step_5_4 Hon Hop H10 _ Hmz Hnz Hca Har Hac).
(*
  ∑ (jl ∈ sub_lists_of_seq_1_n n m),
    det (mat_select_cols jl A) * det (mat_select_rows jl B) =
  ∑ (jl ∈ sub_lists_...
*)
easy.
Qed.

End a.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
(*
Context (Hon : rngl_has_1 T = true).
*)

Corollary determinant_mul :
  charac_0_field T →
  ∀ [A B],
  is_square_matrix A = true
  → is_square_matrix B = true
  → mat_nrows A = mat_nrows B
  → det (A * B) = (det A * det B)%L.
Proof.
(* version shunting Cauchy_Binet_formula using only steps 1 to 5
intros Hif * Hsma Hsmb Hrab *.
remember (mat_nrows A) as n eqn:Har.
rename Hrab into Hbr.
symmetry in Har, Hbr.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  destruct A as (lla).
  destruct B as (llb).
  cbn in *.
  apply List.length_zero_iff_nil in Har, Hbr.
  subst lla llb; cbn.
  symmetry; apply (rngl_mul_1_l Hon).
}
specialize (squ_mat_ncols A Hsma) as Hac.
specialize (squ_mat_ncols B Hsmb) as Hbc.
rewrite Har in Hac; rewrite Hbr in Hbc.
specialize (squ_mat_is_corr A Hsma) as Hca.
specialize (squ_mat_is_corr B Hsmb) as Hcb.
rewrite (Cauchy_Binet_formula_step_1 Hif A B Hnz Har Hac Hbc).
rewrite (Cauchy_Binet_formula_step_2 Hif n A B Hnz).
rewrite (Cauchy_Binet_formula_step_3 Hif _ B Hnz Hcb Hbr Hbc).
rewrite (Cauchy_Binet_formula_step_4 Hif _ B Hnz Hcb Hbr Hbc).
rewrite (Cauchy_Binet_formula_step_5_1 Hif).
unfold sub_lists_of_seq_1_n.
rewrite sls1n_diag.
rewrite rngl_summation_list_only_one.
rewrite (fold_det''' _ A Har).
rewrite <- (det_is_det''' _); try (now destruct Hif).
rewrite <- Hbr.
rewrite mat_select_all_rows; [ | easy ].
easy.
...
*)
intros Hif * Hsma Hsmb Hrab *.
specialize Cauchy_Binet_formula as H1.
remember (mat_nrows A) as n eqn:Hn.
rename Hn into Hra; rename Hrab into Hrb.
symmetry in Hra, Hrb.
specialize (H1 Hif n n A B).
assert (H : is_correct_matrix A = true) by now apply squ_mat_is_corr.
specialize (H1 H); clear H.
assert (H : is_correct_matrix B = true) by now apply squ_mat_is_corr.
specialize (H1 H); clear H.
assert (Hca : mat_ncols A = n) by now rewrite squ_mat_ncols.
assert (Hcb : mat_ncols B = n) by now rewrite squ_mat_ncols.
specialize (H1 Hra Hca Hrb Hcb).
rewrite H1.
unfold sub_lists_of_seq_1_n.
rewrite sls1n_diag.
rewrite rngl_summation_list_only_one.
rewrite <- Hrb.
rewrite mat_select_all_rows; [ | easy ].
rewrite Hrb, <- Hca.
now rewrite mat_select_all_cols.
Qed.

End a.
