(* trying to prove that det(AB)=det(A)det(B) *)

(* there are several proofs of that, none of them being simple *)
(* here, trying to prove it by the Cauchy-Binet Formula *)
(* https://proofwiki.org/wiki/Cauchy-Binet_Formula *)

(* det(AB)= ∑ 1≤j1<j2<⋯<jm≤n det(Aj1j2…jm)det(Bj1j2…jm)
   where A is a m×n matrix, B a n×m matrix
   Aj1j2…jm denotes the m×m matrix consisting of columns j1,j2,…,jm of A.
   Bj1j2…jm denotes the m×m matrix consisting of rows j1,j2,…,jm of B. *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Permutation.
Import List List.ListNotations.

Require Import Misc RingLike IterAdd IterMul IterAnd Pigeonhole.
Require Import Matrix PermutSeq Signature.
Require Import Determinant.
Import matrix_Notations.

(* all lists [j1;j2;...jm] such that 0≤j1<j2<...<jm<n for some m and n *)

Fixpoint sub_lists_of_seq_0_n (n k : nat) : list (list nat) :=
  match k with
  | 0 => [[]]
  | S k' =>
      match n with
      | 0 => []
      | S n' =>
          sub_lists_of_seq_0_n n' k ++
          map (λ l, l ++ [n']) (sub_lists_of_seq_0_n n' k')
      end
  end.

Fixpoint rank_of_sub_list_of_seq_0_n n k (t : list nat) : nat :=
  match k with
  | 0 => 0
  | S k' =>
      match n with
      | 0 => 0
      | S n' =>
          if last t 0 =? n' then
            length (sub_lists_of_seq_0_n n' k) +
            rank_of_sub_list_of_seq_0_n n' k' (removelast t)
          else
            rank_of_sub_list_of_seq_0_n n' k t
      end
  end.

(*
Compute (let n := 5 in map (λ i, let l := sub_lists_of_seq_0_n n i in length l) (seq 0 (n + 3))).
Compute (let n := 5 in map (λ i, let l := sub_lists_of_seq_0_n n i in (length l, l)) (seq 0 (n + 3))).
Compute (let '(n,k) := (5,3) in let ll := sub_lists_of_seq_0_n n k in map (λ i, (i, rank_of_sub_list_of_seq_0_n n k (nth i ll []))) (seq 0 (length ll))).
*)

(* binomial *)
(* code borrowed from my work "coq_euler_prod_form" *)

Fixpoint binomial n k :=
  match k with
  | 0 => 1
  | S k' =>
      match n with
      | 0 => 0
      | S n' => binomial n' k' + binomial n' k
     end
  end.

Theorem binomial_out : ∀ n k, n < k → binomial n k = 0.
Proof.
intros * Hnk.
revert k Hnk.
induction n; intros; [ now destruct k | cbn ].
destruct k; [ flia Hnk | ].
apply Nat.succ_lt_mono in Hnk.
rewrite IHn; [ | easy ].
rewrite Nat.add_0_l.
apply IHn; flia Hnk.
Qed.

Theorem binomial_diag : ∀ n, binomial n n = 1.
Proof.
intros.
induction n; [ easy | cbn ].
rewrite IHn.
now rewrite binomial_out.
Qed.

(* end borrowed code *)

Theorem sub_lists_of_seq_0_n_length : ∀ k n,
  length (sub_lists_of_seq_0_n n k) = binomial n k.
Proof.
intros.
revert k.
induction n; intros; [ now destruct k | ].
destruct k; [ easy | cbn ].
rewrite app_length, map_length.
rewrite IHn, IHn.
apply Nat.add_comm.
Qed.

Theorem sub_list_firstn_nat_length : ∀ n k t,
  t ∈ sub_lists_of_seq_0_n n k → length t = k.
Proof.
intros * Ht.
revert t k Ht.
induction n; intros. {
  cbn in Ht.
  destruct k; [ | easy ].
  destruct Ht; [ now subst t | easy ].
}
destruct k. {
  destruct Ht; [ now subst t | easy ].
}
cbn in Ht.
apply in_app_iff in Ht.
destruct Ht as [Ht| Ht]; [ now apply IHn | ].
apply in_map_iff in Ht.
destruct Ht as (l & Hln & Hl).
rewrite <- Hln.
rewrite app_length, Nat.add_1_r; f_equal.
now apply IHn.
Qed.

(* *)

Theorem sub_lists_of_seq_0_n_lt : ∀ n k t,
  t ∈ sub_lists_of_seq_0_n n k
  → ∀ a, a ∈ t → a < n.
Proof.
intros * Ht a Hat.
revert k t Ht Hat.
induction n; intros. {
  destruct k; [ cbn in Ht | easy ].
  destruct Ht; [ now subst t | easy ].
}
destruct k; cbn in Ht. {
  destruct Ht; [ now subst t | easy ].
}
apply in_app_iff in Ht.
destruct Ht as [Ht| Ht]. {
  specialize (IHn _ _ Ht Hat).
  now apply Nat.lt_lt_succ_r.
}
apply in_map_iff in Ht.
destruct Ht as (l & Hln & Hl); subst t.
apply in_app_iff in Hat.
cbn in Hat.
destruct Hat as [Hal| [Hal| Hal]]; [ | now subst a | easy ].
apply Nat.lt_lt_succ_r.
now apply (IHn k l).
Qed.

(* *)

Theorem sub_lists_of_seq_0_n_0_r : ∀ n, sub_lists_of_seq_0_n n 0 = [[]].
Proof. now intros; destruct n. Qed.

Theorem sub_lists_of_seq_0_n_out : ∀ n k,
  n < k
  → sub_lists_of_seq_0_n n k = [].
Proof.
intros * Hnk.
revert k Hnk.
induction n; intros; cbn; [ now destruct k | ].
destruct k; [ easy | ].
apply Nat.succ_lt_mono in Hnk.
rewrite IHn; [ | flia Hnk ].
now rewrite IHn.
Qed.

Theorem rank_of_sub_list_of_seq_0_n_out : ∀ n k t,
  n < k
  → rank_of_sub_list_of_seq_0_n n k t = 0.
Proof.
intros * Hnk.
revert t k Hnk.
induction n; intros; cbn; [ now destruct k | ].
destruct k; [ easy | ].
apply Nat.succ_lt_mono in Hnk.
rewrite sub_lists_of_seq_0_n_length.
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec (last t 0) n) as [Htn| Htn]. {
  rewrite IHn; [ | easy ].
  rewrite Nat.add_0_r.
  rewrite binomial_out; [ easy | flia Hnk ].
}
apply IHn; flia Hnk.
Qed.

Theorem rank_of_sub_list_of_seq_0_n_ub : ∀ n k t,
  k ≤ n
  → rank_of_sub_list_of_seq_0_n n k t < binomial n k.
Proof.
intros * Hkn.
revert k t Hkn.
induction n; intros. {
  now apply Nat.le_0_r in Hkn; subst k; cbn.
}
destruct k; cbn; [ easy | ].
apply Nat.succ_le_mono in Hkn.
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec (last t 0) n) as [Hln| Hln]. {
  rewrite sub_lists_of_seq_0_n_length, Nat.add_comm.
  apply Nat.add_lt_mono_r.
  now apply IHn.
} {
  destruct (Nat.eq_dec k n) as [Hk| Hk]. {
    subst k.
    rewrite rank_of_sub_list_of_seq_0_n_out; [ | easy ].
    now rewrite binomial_diag.
  }
  transitivity (binomial n (S k)); [ apply IHn; flia Hkn Hk | ].
  apply Nat.lt_add_pos_l.
  specialize (IHn k [] Hkn).
  flia IHn.
}
Qed.

Theorem rank_of_sub_list_of_seq_0_n_of_nth : ∀ n k i,
  i < binomial n k
  → rank_of_sub_list_of_seq_0_n n k (nth i (sub_lists_of_seq_0_n n k) []) = i.
Proof.
intros * Hi.
revert k i Hi.
induction n; intros. {
  destruct k; [ now apply Nat.lt_1_r in Hi | easy ].
}
cbn.
rewrite sub_lists_of_seq_0_n_length.
destruct k; [ now apply Nat.lt_1_r in Hi | ].
cbn in Hi.
destruct (lt_dec i (binomial n (S k))) as [Hik| Hik]. {
  rewrite app_nth1; [ | now rewrite sub_lists_of_seq_0_n_length ].
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec _ n) as [Hlz| Hlz]; [ | now apply IHn ].
  exfalso.
  specialize (sub_lists_of_seq_0_n_lt n (S k)) as H1.
  remember (sub_lists_of_seq_0_n n (S k)) as ll eqn:Hll.
  specialize (H1 (nth i ll [])).
  assert (H : nth i ll [] ∈ ll). {
    now apply nth_In; rewrite Hll, sub_lists_of_seq_0_n_length.
  }
  specialize (H1 H); clear H.
  specialize (H1 n).
  assert (H : n ∈ nth i ll []). {
    rewrite <- Hlz.
    rewrite List_last_nth.
    apply nth_In.
    apply Nat.sub_lt; [ | easy ].
    rewrite Hll.
    rewrite (sub_list_firstn_nat_length n (S k)); [ flia | ].
    apply nth_In.
    now rewrite sub_lists_of_seq_0_n_length.
  }
  specialize (H1 H).
  now apply Nat.lt_irrefl in H1.
}
apply Nat.nlt_ge in Hik.
rewrite app_nth2; [ | now rewrite sub_lists_of_seq_0_n_length ].
rewrite sub_lists_of_seq_0_n_length.
remember (i - binomial n (S k)) as j eqn:Hj.
rewrite (List_map_nth' []); [ | rewrite sub_lists_of_seq_0_n_length; flia Hi Hik Hj ].
rewrite last_last, Nat.eqb_refl.
rewrite removelast_last.
rewrite IHn; [ flia Hj Hik | flia Hi Hik Hj ].
Qed.

Theorem sorted_hd_no_dup : ∀ a i l,
  sorted Nat.ltb (a :: l) = true
  → i < length l
  → a = nth i l 0
  → False.
Proof.
intros * Hsort Hil Ha.
destruct l as [| b]; [ cbn in Hil; flia Hil | ].
apply sorted_cons_cons_true_iff in Hsort.
destruct Hsort as (Hab & Hs).
apply Nat.ltb_lt in Hab.
specialize (@sorted_extends _ Nat.ltb b l) as H1.
destruct i; [ cbn in Ha; flia Hab Ha | cbn in Ha ].
specialize (H1 Nat_ltb_trans).
specialize (H1 Hs a).
cbn in Hil.
apply Nat.succ_lt_mono in Hil.
assert (H : a ∈ l) by now subst a; apply nth_In.
specialize (H1 H).
apply Nat.ltb_lt in H1.
flia Hab H1.
Qed.

Theorem nth_of_rank_of_sub_list_of_seq_0_n : ∀ n k t,
  sorted Nat.ltb t = true
  → length t = k
  → (∀ i, i ∈ t → i < n)
  → nth (rank_of_sub_list_of_seq_0_n n k t) (sub_lists_of_seq_0_n n k) [] = t.
Proof.
intros * Hs Htk Hlt.
destruct (le_dec k n) as [Hkn| Hkn]. 2: {
  apply Nat.nle_gt in Hkn.
  rewrite rank_of_sub_list_of_seq_0_n_out; [ | easy ].
  rewrite sub_lists_of_seq_0_n_out; [ | easy ].
  cbn; symmetry.
  specialize (pigeonhole_list) as H1.
  specialize (H1 n t).
  rewrite <- Htk in Hkn.
  specialize (H1 Hkn Hlt).
  remember (pigeonhole_comp_list t) as xx eqn:Hxx.
  symmetry in Hxx.
  destruct xx as (x, x').
  specialize (H1 x x' eq_refl).
  destruct H1 as (Hx & Hx' & Hxx' & Hxxt).
  exfalso; apply Hxx'; clear Hxx'.
  clear - Hs Hx Hx' Hxxt.
  revert x x' Hx Hx' Hxxt.
  induction t as [| a]; intros; [ easy | ].
  destruct x. {
    destruct x'; [ easy | exfalso ].
    cbn in Hx'.
    apply Nat.succ_lt_mono in Hx'.
    now apply (@sorted_hd_no_dup a x' t).
  }
  cbn in Hx.
  apply Nat.succ_lt_mono in Hx.
  destruct x'. {
    exfalso.
    cbn in Hxxt; symmetry in Hxxt.
    now apply (@sorted_hd_no_dup a x t).
  }
  cbn in Hx', Hxxt.
  apply Nat.succ_lt_mono in Hx'.
  f_equal.
  apply IHt; [ | easy | easy | easy ].
  destruct t as [| b]; [ easy | ].
  now apply sorted_cons_cons_true_iff in Hs.
}
revert k t Hs Htk Hlt Hkn.
induction n; intros. {
  apply Nat.le_0_r in Hkn; subst k.
  now apply length_zero_iff_nil in Hkn; subst t.
}
destruct k. {
  now apply length_zero_iff_nil in Htk; subst t.
}
apply Nat.succ_le_mono in Hkn.
cbn.
rewrite sub_lists_of_seq_0_n_length.
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec (last t 0) n) as [Hln| Hln]. {
  rewrite app_nth2; [ | rewrite sub_lists_of_seq_0_n_length; flia ].
  rewrite sub_lists_of_seq_0_n_length.
  rewrite Nat.add_comm, Nat.add_sub.
  rewrite (List_map_nth' []). 2: {
    rewrite sub_lists_of_seq_0_n_length.
    now apply rank_of_sub_list_of_seq_0_n_ub.
  }
  destruct t as [| a] using rev_ind; [ easy | ].
  rewrite last_last in Hln; subst a.
  rewrite removelast_last.
  rewrite app_length, Nat.add_1_r in Htk; cbn in Htk.
  apply Nat.succ_inj in Htk.
  f_equal.
  apply IHn; [ | easy | | easy ]. {
    now apply sorted_app in Hs.
  }
  intros i Hi.
  apply sorted_app in Hs.
  destruct Hs as (Ht & _ & Hs).
  specialize (Hs Nat_ltb_trans i n Hi (or_introl eq_refl)).
  now apply Nat.ltb_lt in Hs.
}
destruct (lt_dec (rank_of_sub_list_of_seq_0_n n (S k) t) (binomial n (S k)))
    as [Hrb| Hrb]. {
  rewrite app_nth1; [ | now rewrite sub_lists_of_seq_0_n_length ].
  destruct (Nat.eq_dec n k) as [Hnk| Hnk]. {
    subst k.
    rewrite rank_of_sub_list_of_seq_0_n_out in Hrb; [ cbn in Hrb | easy ].
    now rewrite binomial_out in Hrb.
  }
  apply IHn; [ easy | easy | | flia Hkn Hnk ].
  intros i Hi.
  clear - Hs Hlt Hln Hi.
  specialize (Hlt i Hi) as H1.
  destruct (Nat.eq_dec i n) as [Hin| Hin]; [ | flia H1 Hin ].
  subst i; exfalso; clear H1.
  apply (In_nth _ _ 0) in Hi.
  destruct Hi as (m & Hmt & Hmn).
  assert (Hmtl : nth m t 0 < last t 0). {
    rewrite List_last_nth.
    specialize (@sorted_any _ Nat.ltb m (length t - 1) 0 t) as H1.
    specialize (H1 Nat_ltb_trans Hs).
    assert (H : m < length t - 1). {
      destruct (Nat.eq_dec m (length t - 1)) as [Hmt1| Hmt1]. {
        exfalso; clear Hmt H1; subst m.
        now rewrite List_last_nth in Hln.
      }
      flia Hmt Hmt1.
    }
    specialize (H1 H); clear H.
    assert (H : length t - 1 < length t) by flia Hmt.
    specialize (H1 H); clear H.
    now apply Nat.ltb_lt in H1.
  }
  rewrite Hmn in Hmtl.
  apply Nat.nle_gt in Hmtl; apply Hmtl; clear Hmtl.
  apply Nat.lt_succ_r.
  apply Hlt.
  rewrite List_last_nth.
  apply nth_In.
  flia Hmt.
}
apply Nat.nlt_ge in Hrb.
rewrite app_nth2; [ | now rewrite sub_lists_of_seq_0_n_length ].
rewrite sub_lists_of_seq_0_n_length.
rewrite (List_map_nth' []). 2: {
  rewrite sub_lists_of_seq_0_n_length.
  destruct (Nat.eq_dec k n) as [Hkn'| Hkn']. {
    subst k.
    rewrite rank_of_sub_list_of_seq_0_n_out; [ | easy ].
    now rewrite binomial_diag.
  }
  assert (H : S k ≤ n) by flia Hkn Hkn'.
  specialize (rank_of_sub_list_of_seq_0_n_ub t H) as H1; clear H.
  flia Hrb H1.
}
exfalso. (* since last t ≠ m *)
destruct (Nat.eq_dec k n) as [Hkn'| Hkn']. {
  subst k; clear Hrb Hkn.
  specialize (pigeonhole_list) as H1.
  specialize (H1 n t).
  assert (H : n < length t) by flia Htk.
  specialize (H1 H); clear H.
  assert (H : ∀ x, x ∈ t → x < n). {
    intros x Hx.
    specialize (Hlt x Hx) as H2.
    destruct (Nat.eq_dec x n) as [Hxn| Hxn]; [ | flia H2 Hxn ].
    subst x.
    clear H2.
    exfalso; clear IHn H1.
    apply (In_nth _ _ 0) in Hx.
    destruct Hx as (i & Hi & Hin).
    specialize (sorted_any) as H1.
    specialize (H1 nat Nat.ltb i (length t - 1) 0 t Nat_ltb_trans Hs).
    assert (H : i < length t - 1). {
      destruct (Nat.eq_dec i (length t - 1)) as [Hit| Hit]. {
        rewrite Hit in Hin.
        now rewrite <- List_last_nth in Hin.
      }
      flia Hi Hit.
    }
    specialize (H1 H); clear H.
    assert (H : length t - 1 < length t) by flia Hi.
    specialize (H1 H); clear H.
    rewrite Hin in H1.
    rewrite <- List_last_nth in H1.
    apply Nat.ltb_lt in H1.
    specialize (Hlt (last t 0)).
    assert (H : last t 0 ∈ t). {
      rewrite List_last_nth.
      apply nth_In; flia Hi.
    }
    specialize (Hlt H); clear H.
    flia Hlt H1.
  }
  specialize (H1 H); clear H.
  remember (pigeonhole_comp_list t) as xx eqn:Hxx.
  symmetry in Hxx.
  destruct xx as (x, x').
  specialize (H1 x x' eq_refl).
  destruct H1 as (Hx & Hx' & Hxx' & Hxxt).
  exfalso; apply Hxx'; clear Hxx'.
  clear - Hs Hx Hx' Hxxt.
  revert x x' Hx Hx' Hxxt.
  induction t as [| a]; intros; [ easy | ].
  destruct x. {
    destruct x'; [ easy | exfalso ].
    cbn in Hx'.
    apply Nat.succ_lt_mono in Hx'.
    cbn in Hxxt.
    now apply (@sorted_hd_no_dup a x' t).
  }
  cbn in Hx.
  apply Nat.succ_lt_mono in Hx.
  destruct x'. {
    exfalso.
    cbn in Hxxt; symmetry in Hxxt.
    now apply (@sorted_hd_no_dup a x t).
  }
  cbn in Hx', Hxxt.
  apply Nat.succ_lt_mono in Hx'.
  f_equal.
  apply IHt; [ | easy | easy | easy ].
  now apply sorted_cons in Hs.
}
apply Nat.nlt_ge in Hrb; apply Hrb.
apply rank_of_sub_list_of_seq_0_n_ub.
flia Hkn Hkn'.
Qed.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

(* submatrix with list rows jl *)
(**)
Definition list_list_select_rows jl ll :=
  map (λ i, map (λ j, nth j (nth i ll []) 0%F) (seq 0 (length ll))) jl.
Definition mat_select_rows jl M :=
  mk_mat (list_list_select_rows jl (mat_list_list M)).

Definition mat_select_rows' (jl : list nat) (M : matrix T) :=
  mk_mat (map (λ i, map (λ j, mat_el M i j) (seq 0 (mat_ncols M))) jl).
(*
Definition mat_select_rows (jl : list nat) (M : matrix T) :=
  mk_mat (map (λ j, nth j (mat_list_list M) []) jl).
*)

(*
End a.
Require Import RnglAlg.Nrl.
Print mat_select_rows.
Compute (let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1];[18;3;2;1]] in mat_select_rows _ [0;2;3] M).
Compute (let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1];[18;3;2;1]] in mat_select_rows' _ [0;2;3] M).
Compute (let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1]] in mat_select_rows _ [0;2;3] M).
Compute (let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1]] in mat_select_rows' _ [0;2;3] M).
Compute (let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1];[18;3;2;1]] in mat_select_rows _ [2;1] M).
Compute (let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1];[18;3;2;1]] in mat_select_rows' _ [2;1] M).
*)

(* submatrix with list cols jl *)
Definition mat_select_cols (jl : list nat) (M : matrix T) :=
  mk_mat (map (λ i, map (λ j, mat_el M i j) jl) (seq 0 (mat_nrows M))).

Definition mat_select_cols' (jl : list nat) (M : matrix T) :=
  ((mat_select_rows jl M⁺)⁺)%M.

End a.

Arguments list_list_select_rows {T ro} jl%list ll%list.
Arguments mat_select_rows {T ro} jl%list M%M.
Arguments mat_select_cols {T ro} jl%list M%M.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

(*
Require Import RnglAlg.Nrl.
Print mat_select_cols.
About mat_select_cols.
Arguments mat_select_cols {T}%type {ro} jl%list M%M.
Arguments mat_select_cols' {T}%type {ro} jl%list M%M.
Compute (let jl := [0;2;3] in let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1];[18;3;2;1];[8;7;6;5]] in mat_select_cols jl M = mat_select_cols' jl M).
Compute (let jl := [] in let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1];[18;3;2;1];[8;7;6;5]] in mat_select_cols jl M = mat_select_cols' jl M).
(* conclusion: la première version se comporte mal si jl=[] ; faut-il donc
   préférer absolument la version avec la transposée ? sachant que bon,
   faudra se la taper dans les preuves, en double exemplaire, ici, en
   plus ? *)
...
*)

(*
Theorem map_with_cols_cols' : ∀ M jl,
  mat_select_cols jl M = mat_select_cols' jl M.
Proof.
intros.
destruct (Nat.eq_dec (length jl) 0) as [Hjz| Hjz]. {
  apply length_zero_iff_nil in Hjz; subst jl.
  unfold mat_select_cols, mat_select_cols', mat_select_rows; cbn.
...
unfold mat_select_cols, mat_select_cols', mat_select_rows, mat_transp, mat_ncols.
cbn; f_equal.
rewrite map_length.
rewrite fold_mat_ncols.
rewrite List_map_hd with (a := 0).
...
rewrite List_map_nth' with (a := 0). 2: {
  rewrite seq_length.
...
}
rewrite List_map_seq_length.
...
*)

Theorem sub_lists_of_seq_0_n_1_r : ∀ n,
  sub_lists_of_seq_0_n n 1 = map (λ i, [i]) (seq 0 n).
Proof.
intros.
induction n; [ easy | ].
rewrite seq_S; cbn.
rewrite map_app; cbn.
rewrite <- IHn; f_equal.
now rewrite sub_lists_of_seq_0_n_0_r.
Qed.

Theorem sub_lists_of_seq_0_n_are_correct : ∀ k n t,
  k ≠ 0 → t ∈ sub_lists_of_seq_0_n n k → t ≠ [].
Proof.
intros * Hkz Ht Htz; subst t.
destruct k; [ easy | clear Hkz ].
induction n; [ easy | cbn in Ht ].
apply in_app_iff in Ht.
destruct Ht as [Ht| Ht]; [ easy | ].
apply in_map_iff in Ht.
destruct Ht as (x & Hx & Hxn).
now apply app_eq_nil in Hx.
Qed.

Theorem sub_lists_of_seq_0_n_are_sorted : ∀ n k ll,
  ll = sub_lists_of_seq_0_n n k
  → ∀ l, l ∈ ll → sorted Nat.ltb l = true.
Proof.
intros * Hll * Hl.
subst ll.
revert k l Hl.
induction n; intros. {
  destruct k; [ cbn in Hl | easy ].
  destruct Hl; [ now subst l | easy ].
}
destruct k; cbn in Hl. {
  destruct Hl; [ now subst l | easy ].
}
apply in_app_iff in Hl.
destruct Hl as [Hl| Hl]; [ now apply IHn in Hl | ].
apply in_map_iff in Hl.
destruct Hl as (l' & Hl'n & Hl); subst l.
rename l' into l.
specialize (sub_lists_of_seq_0_n_lt _ _ _ Hl) as H1.
specialize (IHn _ _ Hl).
clear k Hl.
revert n H1 IHn.
induction l as [| a]; intros; [ easy | ].
destruct l as [| b]. {
  cbn - [ "<?" ].
  rewrite Bool.andb_true_r.
  now apply Nat.ltb_lt, H1; left.
}
cbn - [ sorted ] in IHl |-*.
apply sorted_cons_cons_true_iff in IHn.
apply sorted_cons_cons_true_iff.
destruct IHn as (Hab, Hbl).
split; [ easy | ].
apply IHl; [ | easy ].
intros c Hc.
apply H1.
now right.
Qed.

Theorem sub_list_of_seq_0_n_has_no_dup :
  ∀ m n l, l ∈ sub_lists_of_seq_0_n m n → NoDup l.
Proof.
intros * Hs.
specialize (sub_lists_of_seq_0_n_are_sorted m n) as H1.
specialize (H1 _ eq_refl _ Hs).
clear - H1.
induction l as [| a]; [ constructor | ].
constructor. {
  intros Hal.
  specialize sorted_extends as H2.
  specialize (H2 _ Nat.ltb a l Nat_ltb_trans H1).
  specialize (H2 a Hal).
  now rewrite Nat.ltb_irrefl in H2.
}
apply IHl.
now apply sorted_cons in H1.
Qed.

Theorem sub_lists_of_seq_0_n_is_inj : ∀ n k ll,
  ll = sub_lists_of_seq_0_n n k
  → ∀ i j, i < length ll → j < length ll →
   nth i ll [] = nth j ll [] → i = j.
Proof.
intros * Hll * Hi Hj Hij.
rewrite Hll in Hi, Hj.
rewrite sub_lists_of_seq_0_n_length in Hi, Hj.
specialize rank_of_sub_list_of_seq_0_n_of_nth as H1.
specialize (H1 n k i Hi).
specialize rank_of_sub_list_of_seq_0_n_of_nth as H2.
specialize (H2 n k j Hj).
congruence.
Qed.

Theorem sub_lists_of_seq_0_n_is_surj : ∀ n k ll,
  ll = sub_lists_of_seq_0_n n k
  → (∀ l, l ∈ ll → ∃ i, nth i ll [] = l).
Proof.
intros * Hll * Hl.
specialize (sub_lists_of_seq_0_n_are_sorted n k Hll l Hl) as Hsort.
specialize nth_of_rank_of_sub_list_of_seq_0_n as H1.
specialize (H1 n k l Hsort).
assert (H : length l = k). {
  apply (sub_list_firstn_nat_length n).
  now rewrite <- Hll.
}
specialize (H1 H); clear H.
rewrite <- Hll in H1.
exists (rank_of_sub_list_of_seq_0_n n k l).
apply H1.
intros i Hi.
apply (sub_lists_of_seq_0_n_lt _ k l); [ | easy ].
now rewrite <- Hll.
Qed.

Theorem sub_lists_of_seq_0_n_prop : ∀ n k ll,
  ll = sub_lists_of_seq_0_n n k
  → (∀ l, l ∈ ll → sorted Nat.ltb l = true) ∧
    (∀ i j, i < length ll → j < length ll →
     nth i ll [] = nth j ll [] → i = j) ∧
    (∀ l, l ∈ ll → ∃ i, nth i ll [] = l).
Proof.
intros * Hll.
split. {
  intros l Hl.
  now apply (sub_lists_of_seq_0_n_are_sorted n k Hll).
}
split. {
  now apply (sub_lists_of_seq_0_n_is_inj n k).
} {
  now apply (sub_lists_of_seq_0_n_is_surj n k).
}
Qed.

Theorem sub_lists_of_seq_0_n_diag : ∀ n, sub_lists_of_seq_0_n n n = [seq 0 n].
Proof.
intros.
induction n; [ easy | ].
rewrite seq_S; cbn.
rewrite sub_lists_of_seq_0_n_out; [ | easy ].
now rewrite IHn.
Qed.

(* https://fr.wikipedia.org/wiki/Formule_de_Binet-Cauchy *)
(* https://proofwiki.org/wiki/Cauchy-Binet_Formula *)

Theorem mat_select_rows_nrows : ∀ (A : matrix T) kl,
  mat_nrows (mat_select_rows kl A) = length kl.
Proof.
intros.
(*
now cbn; rewrite map_length.
*)
cbn; unfold list_list_select_rows.
now rewrite map_length.
(**)
Qed.

Theorem mat_select_rows_is_square : ∀ kl (A : matrix T),
  is_correct_matrix A = true
(*
  → mat_ncols A = length kl
*)
  → mat_nrows A = length kl
(**)
  → (∀ k, k ∈ kl → k < mat_nrows A)
  → is_square_matrix (mat_select_rows kl A) = true.
Proof.
intros * Ha Hra Hkc.
destruct (Nat.eq_dec (length kl) 0) as [Hnz| Hnz]. {
  apply length_zero_iff_nil in Hnz; subst kl.
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
(*
  rewrite Hcla in Hc. 2: {
    apply nth_In.
    rewrite fold_mat_nrows.
    now apply Hkc; left.
  }
  congruence.
*)
(*
  clear Hnz; cbn in Hc.
  rewrite List_map_seq_length in Hc.
  rewrite Hcra in Hkc; [ | easy ].
  now specialize (Hkc k (or_introl eq_refl)).
*)
  clear Hnz; cbn in Hc.
  rewrite List_map_seq_length in Hc.
  specialize (Hkc k (or_introl eq_refl)).
  rewrite Hcra in Hkc; [ easy | ].
  rewrite fold_mat_nrows in Hc.
  now rewrite Hc in Hkc.
(**)
} {
  intros l Hl.
  rewrite mat_select_rows_nrows.
  cbn in Hl.
  apply in_map_iff in Hl.
  destruct Hl as (a & Hal & Ha).
  subst l.
(*
  rewrite Hcla; [ easy | ].
  apply nth_In; rewrite fold_mat_nrows.
  now apply Hkc.
*)
(*
  now rewrite List_map_seq_length.
*)
  now rewrite List_map_seq_length, fold_mat_nrows.
(**)
}
Qed.

(**)

Theorem sorted_bsort_insert : ∀ A (ord : A → _),
  antisymmetric ord
  → transitive ord
  → total_order ord
  → ∀ a ls l,
  sorted ord (ls ++ a :: l) = true
  → sorted ord (bsort_insert ord a ls) = true.
Proof.
intros * Hant Htra Htot * Hs.
revert a l Hs.
induction ls as [| b]; intros; [ easy | cbn ].
remember (ord a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  specialize (sorted_middle) as Hba.
  specialize (Hba A ord b a [] ls l Htra Hs).
  specialize (Hant a b Hab Hba) as H; subst b.
  remember (a :: ls) as ls'; cbn; subst ls'.
  rewrite Hba.
  apply sorted_app_iff in Hs; [ | easy ].
  destruct Hs as (Hs, _).
  now rewrite Hs.
} {
  cbn.
  remember (bsort_insert ord a ls) as ls' eqn:Hls'.
  symmetry in Hls'.
  destruct ls' as [| a']; [ easy | ].
  apply Bool.andb_true_iff.
  split. 2: {
    rewrite <- Hls'.
    apply IHls with (l := l).
    cbn - [ sorted ] in Hs.
    now apply sorted_cons in Hs.
  } {
    replace (b :: ls) with ([b] ++ ls) in Hs by easy.
    apply sorted_app_iff in Hs; [ | easy ].
    destruct Hs as (Hls & Hal & Hs).
    specialize in_bsort_insert as H1.
    specialize (H1 A ord a' a ls).
    rewrite Hls' in H1.
    specialize (H1 (or_introl eq_refl)).
    destruct H1 as [H1| H1]. {
      subst a'.
      specialize (Htot a b) as H1.
      now rewrite Hab in H1.
    } {
      now apply (sorted_extends _ ls).
    }
  }
}
Qed.

Theorem sorted_bsort_loop : ∀ A (ord : A → _),
  antisymmetric ord
  → transitive ord
  → total_order ord
  → ∀ ls l,
  sorted ord (ls ++ l) = true
  → bsort_loop ord ls l = ls ++ l.
Proof.
intros * Hant Htra Htot * Hs.
revert ls Hs.
induction l as [| a]; intros; [ now rewrite app_nil_r | cbn ].
rewrite IHl. 2: {
  apply sorted_app_iff; [ easy | ].
  split. {
    now apply sorted_bsort_insert with (l := l).
  }
  split. {
    apply sorted_app in Hs.
    destruct Hs as (_ & Hs & _).
    now apply sorted_cons in Hs.
  } {
    intros b c Hb Hc.
    apply in_bsort_insert in Hb.
    apply sorted_app_iff in Hs; [ | easy ].
    destruct Hs as (Hss & Hsa & Hs).
    destruct Hb as [Hb| Hb]. {
      subst b.
      now apply sorted_extends with (l := l).
    } {
      apply Hs; [ easy | now right ].
    }
  }
}
replace (a :: l) with ([a] ++ l) by easy.
rewrite app_assoc; f_equal.
clear IHl.
replace (a :: l) with ([a] ++ l) in Hs by easy.
rewrite app_assoc in Hs.
apply sorted_app_iff in Hs; [ | easy ].
destruct Hs as (Hsa, _).
clear l.
revert a Hsa.
induction ls as [| b]; intros; [ easy | cbn ].
remember (ord a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  apply sorted_app_iff in Hsa; [ | easy ].
  destruct Hsa as (Hsb & _ & Hs').
  specialize (Hs' b a (or_introl eq_refl) (or_introl eq_refl)) as H1.
  specialize (Hant _ _ Hab H1) as H2; subst b; clear H1.
  assert (H : ∀ b, b ∈ ls → ord b a = true). {
    intros c Hc.
    apply Hs'; [ now right | now left ].
  }
  clear Hs'; rename H into Hs.
  specialize sorted_extends as H1.
  specialize (H1 A ord a ls Htra Hsb).
  f_equal.
  assert (H2 : ∀ b, b ∈ ls → b = a). {
    intros b Hb.
    specialize (Hs _ Hb) as H2.
    specialize (H1 _ Hb) as H3.
    apply (Hant _ _ H2 H3).
  }
  clear IHls Hab Hsb Hs H1.
  induction ls as [| b]; [ easy | cbn ].
  rewrite H2 with (b0 := b); [ | now left ].
  f_equal.
  apply IHls.
  intros c Hc.
  now apply H2; right.
} {
  f_equal.
  apply IHls.
  cbn - [ sorted ] in Hsa.
  now apply sorted_cons in Hsa.
}
Qed.

Theorem sorted_bsort : ∀ A (ord : A → _),
  antisymmetric ord
  → transitive ord
  → total_order ord
  → ∀ l,
  sorted ord l = true
  → bsort ord l = l.
Proof.
intros * Hant Htra Htot * Hs.
unfold bsort.
now apply sorted_bsort_loop.
Qed.

Theorem det_mat_swap_rows_with_rows : in_charac_0_field →
  ∀ p q A jl,
  is_correct_matrix A = true
  → (∀ k, k ∈ jl → k < mat_nrows A)
(*
  → mat_ncols A = length jl
*)
  → mat_nrows A = length jl
(**)
  → p < length jl
  → q < length jl
  → p ≠ q
  → det (mat_swap_rows p q (mat_select_rows jl A)) =
    (- det (mat_select_rows jl A))%F.
Proof.
intros Hif * Hcm Hro Hco Hp Hq Hpq.
apply determinant_alternating; [ easy | easy | | | ]. {
  now rewrite mat_select_rows_nrows.
} {
  now rewrite mat_select_rows_nrows.
}
now apply mat_select_rows_is_square.
Qed.

Definition swap n p q := list_swap_elem 0 (seq 0 n) p q.

Theorem swap_length : ∀ n p q, length (swap n p q) = n.
Proof.
intros.
unfold swap, list_swap_elem.
rewrite List_map_seq_length.
apply seq_length.
Qed.

Fixpoint first_non_fix_transp i p :=
  match p with
  | [] => i
  | j :: l =>
      if i =? j then first_non_fix_transp (S i) l
      else i
  end.

(*
Fixpoint transp_loop it i (p : list nat) :=
  match it with
  | 0 => []
  | S it' =>
      match List_rank (Nat.eqb i) p with
      | None => []
      | Some j =>
          if j =? 0 then transp_loop it' (S i) (tl p)
          else
            (i, i + j) :: transp_loop it' (S i) (tl (replace_at j p (hd 0 p)))
      end
  end.

Definition transp_list p := transp_loop (length p) 0 p.
*)

(*
Theorem transp_loop_app_seq : ∀ it s i la,
  transp_loop it (s + i) la = transp_loop (it + i) s (seq s i ++ la).
Proof.
intros.
(*
Compute (
  let la := [3;6;5;8;4] in
  let s := 1 in
  let i := 2 in
  let it := 8 in
  transp_loop it (s + i) la = transp_loop (it + i) s (seq s i ++ la)
).
*)
revert i s la.
induction it; intros. {
  cbn.
  revert s la.
  induction i; intros; [ easy | cbn ].
  do 2 rewrite Nat.eqb_refl.
  apply IHi.
}
cbn - [ seq "=?" ].
remember (List_rank (Nat.eqb (s + i)) la) as j1 eqn:Hj1.
remember (List_rank (Nat.eqb s) (seq s i ++ la)) as j2 eqn:Hj2.
symmetry in Hj1, Hj2.
destruct j1 as [j1| ]. {
  rewrite if_eqb_eq_dec.
  apply List_rank_Some with (d := 0) in Hj1.
  destruct Hj1 as (H1l & Hbef1 & Hij1).
  apply Nat.eqb_eq in Hij1.
  destruct j2 as [j2| ]. {
    rewrite if_eqb_eq_dec.
    apply List_rank_Some with (d := 0) in Hj2.
    destruct Hj2 as (H2l & Hbef2 & Hij2).
    apply Nat.eqb_eq in Hij2.
    destruct (Nat.eq_dec j1 0) as [H1z| H1z]. {
      subst j1.
      clear Hbef1.
      destruct (Nat.eq_dec j2 0) as [H2z| H2z]. {
        subst j2.
        clear Hbef2 H2l.
        rewrite <- Nat.add_succ_l.
        destruct i. {
          clear Hij1; cbn in Hij2 |-*.
          now do 2 rewrite Nat.add_0_r.
        }
        cbn.
        destruct la as [| a]. {
          cbn in Hij1; flia Hij1.
        }
        cbn in Hij1 |-*.
        clear Hij2 H1l; subst a.
        rewrite <- Nat.add_succ_l.
        rewrite IHit.
        replace (s + S i :: la) with ([s + S i] ++ la) by easy.
        rewrite app_assoc.
        f_equal; f_equal.
        now rewrite seq_S, Nat.add_succ_r.
      }
      destruct la as [| a]; [ easy | ].
      cbn in Hij1 |-*; clear H1l; subst a.
      rewrite app_length, seq_length in H2l; cbn in H2l.
(* ouais bon *)
... bof
destruct la as [| a]. {
  rewrite app_nil_r.
  destruct i; [ easy | cbn ].
  rewrite Nat.eqb_refl.
  symmetry; apply transp_loop_seq.
}
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec (s + i) a) as [Hia| Hia]. {
  subst a.
  replace (seq s i ++ s + i :: la) with (seq s (S i) ++ la). 2: {
    now rewrite seq_S, <- app_assoc.
  }
  cbn.
  rewrite Nat.eqb_refl.
  rewrite <- Nat.add_succ_r.
  rewrite IHit.
  rewrite Nat.add_succ_r; cbn.
  now rewrite Nat.eqb_refl.
}
remember (seq s i ++ a :: la) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]; [ now destruct i | ].
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec s b) as [Hsb| Hsb]. 2: {
  destruct i. {
    do 2 rewrite Nat.add_0_r.
    cbn in Hlb.
    now injection Hlb; clear Hlb; intros; subst b lb.
  }
  cbn in Hlb.
  now injection Hlb; clear Hlb; intros.
}
subst b.
destruct i. {
  rewrite Nat.add_0_r in Hia.
  cbn in Hlb.
  now injection Hlb; clear Hlb; intros; subst a lb.
}
cbn in Hlb.
injection Hlb; clear Hlb; intros Hlb.
(*1*)
subst lb.
specialize (IHit i (S s) (a :: la)) as H1.
rewrite (Nat.add_succ_r it).
...
*)

(*
Compute (transp_list [3;2;0;1]).
Compute (map (λ l, (l, transp_list l)) (canon_sym_gr_list_list 4)).
Compute (map (λ l, last (transp_list l) (0, 0)) (canon_sym_gr_list_list 5)).
Compute (transp_list [20;12;7;9]).
Compute (transp_list (collapse [20;12;7;9])).
Compute (transp_list [3;2;0;1]).
Compute (
map (λ p, ((*p,*)
  list_eqb Nat.eqb p
    (iter_list (transp_list p) (λ l t, swap (length p) (fst t) (snd t) ° l)
      (seq 0 (length p))))) (canon_sym_gr_list_list 4)).
Compute (let p := [1;2;3;0;5;4] in
  let i := first_non_fix_transp 0 p in
  let l := skipn i p in
  let it := length l in
  fold_right
    (λ (t : nat * nat) (l0 : list nat), swap (length l0) (fst t) (snd t) ° l0)
    (seq 0 i ++ l) (transp_loop it i l) = seq 0 (i + length l)
).
Compute (map (λ p,
  let i := first_non_fix_transp 0 p in
  let l := skipn i p in
  let it := length l in
  fold_right
    (λ (t : nat * nat) (l0 : list nat), swap (length l0) (fst t) (snd t) ° l0)
    (seq 0 i ++ l) (transp_loop it i l) = seq 0 (i + length l)
) (canon_sym_gr_list_list 4)
).
*)

(*
Theorem permut_eq_iter_list_transp_loop : ∀ l it i,
  is_permut_list (seq 0 i ++ l)
  → length l ≤ it
  → seq 0 i ++ l =
    fold_left (λ l t, swap (length l) (fst t) (snd t) ° l)
      (transp_loop it i l) (seq 0 (i + length l)).
Proof.
intros * Hp Hit.
revert l i Hp Hit.
induction it; intros; cbn. {
  apply Nat.le_0_r, length_zero_iff_nil in Hit; subst l.
  now rewrite app_nil_r, Nat.add_0_r.
}
(*
destruct l as [| j]. {
  now cbn; rewrite app_nil_r, Nat.add_0_r.
}
cbn in Hit.
apply Nat.succ_le_mono in Hit.
*)
remember (List_rank (Nat.eqb i) l) as j eqn:Hj.
symmetry in Hj.
destruct j as [j| ]. 2: {
  specialize (List_rank_None 0 _ _ Hj) as H1; cbn.
  destruct l as [| j]. {
    now cbn; rewrite app_nil_r, Nat.add_0_r.
  }
  exfalso.
  clear - Hp H1.
  destruct Hp as (Hpp, Hpl).
  rewrite app_length, seq_length in Hpp; cbn in Hpp.
  (* d'après H1, i ne fait pas partie de la liste j :: l *)
  (* du coup, avec le principe des tiroirs, Hpp et Hpl ne
     devraient pas être possibles *)
  ...
}
apply List_rank_Some with (d := 0) in Hj.
destruct Hj as (Hjl & Hbef & Hij).
apply Nat.eqb_eq in Hij.
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec j 0) as [Hjz| Hjz]. {
  subst j.
  destruct l as [| j]; [ easy | ].
  cbn in Hit, Hij; subst j.
  apply Nat.succ_le_mono in Hit.
  specialize (IHit (tl (i :: l)) (S i)) as H1.
  cbn - [ seq ] in H1.
  rewrite seq_S in H1.
  rewrite <- app_assoc in H1.
  specialize (H1 Hp Hit).
  cbn - [ seq ] in H1.
  rewrite List_length_cons, Nat.add_succ_r.
  apply H1.
} {
  cbn.
  destruct l as [| k]; [ easy | ].
  replace j with (S (j - 1)) in Hij by flia Hjz.
  cbn in Hit, Hij.
  apply Nat.succ_le_mono in Hit.
  rewrite seq_length.
  specialize (IHit (tl (replace_at j (k :: l) (hd 0 (k :: l))))) as H1.
  specialize (H1 (S i)).
  cbn - [ seq ] in H1.
  assert (H : is_permut_list (seq 0 (S i) ++ tl (replace_at j (k :: l) k))). {
    replace j with (S (j - 1)) by flia Hjz.
    rewrite replace_at_succ_cons; cbn - [ seq ].
    ... (* devrait le faire, j'espère *)
  }
  specialize (H1 H); clear H.
  assert (Hr : length (tl (replace_at j (k :: l) k)) = length l). {
    destruct j; [ easy | ].
    cbn in Hjl; apply Nat.succ_lt_mono in Hjl.
    rewrite replace_at_succ_cons; cbn.
    now apply length_replace_at.
  }
  assert (H : length (tl (replace_at j (k :: l) k)) ≤ it) by now rewrite Hr.
  specialize (H1 H); clear H.
  rewrite Hr in H1.
  cbn.
  destruct j; [ easy | ].
  rewrite replace_at_succ_cons in H1.
  rewrite replace_at_succ_cons.
  cbn - [ seq  ] in H1.
  cbn.
  do 2 rewrite Nat.add_succ_r.
  rewrite comp_1_r by now rewrite swap_length.
(* marche pas *)
...
*)

(*
Theorem fold_right_transp_loop : ∀ l it i,
  is_permut_list (seq 0 i ++ l)
  → length l ≤ it
  → fold_right (λ t l, swap (length l) (fst t) (snd t) ° l)
      (seq 0 i ++ l) (transp_loop it i l) =
    seq 0 (i + length l).
Proof.
intros * Hp Hit.
(*
Compute
  (map (λ p,
  let i := first_non_fix_transp 0 p in
  let l := skipn i p in
  let it := length l - 1 in
(
  fold_right (λ (t : nat * nat) (l0 : list nat), swap (length l0) (fst t) (snd t) ° l0) 
    (seq 0 i ++ l) (transp_loop it i l) = seq 0 (i + length l)))
 (canon_sym_gr_list_list 4)).
...
*)
revert l i Hp Hit.
induction it; intros; cbn. {
  apply Nat.le_0_r, length_zero_iff_nil in Hit; subst l.
  now rewrite app_nil_r, Nat.add_0_r.
}
remember (List_rank (Nat.eqb i) l) as j eqn:Hj.
symmetry in Hj.
destruct j as [j| ]. 2: {
  specialize (List_rank_None 0 _ _ Hj) as H1; cbn.
  exfalso.
  clear - Hp H1.
  ... (* devrait le faire *)
}
apply List_rank_Some with (d := 0) in Hj.
destruct Hj as (Hjl & Hbef & Hij).
apply Nat.eqb_eq in Hij.
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec j 0) as [Hjz| Hjz]. {
  subst j.
  destruct l as [| j]; [ easy | ].
  cbn in Hit, Hij; subst j.
  apply Nat.succ_le_mono in Hit.
  specialize (IHit (tl (i :: l)) (S i)) as H1.
  cbn - [ seq ] in H1.
  rewrite seq_S in H1.
  rewrite <- app_assoc in H1.
  specialize (H1 Hp Hit).
  cbn - [ seq ] in H1.
  rewrite List_length_cons, Nat.add_succ_r.
  apply H1.
} {
  cbn.
  rewrite List_length_fold_right; [ | now intros; rewrite comp_length ].
  rewrite app_length, seq_length.
  destruct l as [| k]; [ easy | ].
  replace j with (S (j - 1)) in Hij by flia Hjz.
  cbn in Hit, Hij.
  apply Nat.succ_le_mono in Hit.
  specialize (IHit (tl (replace_at j (k :: l) (hd 0 (k :: l))))) as H1.
  specialize (H1 (S i)).
  cbn - [ seq ] in H1.
  assert (H : is_permut_list (seq 0 (S i) ++ tl (replace_at j (k :: l) k))). {
    replace j with (S (j - 1)) by flia Hjz.
    rewrite replace_at_succ_cons; cbn - [ seq ].
    ... (* devrait le faire, j'espère *)
  }
  specialize (H1 H); clear H.
  assert (Hr : length (tl (replace_at j (k :: l) k)) = length l). {
    destruct j; [ easy | ].
    cbn in Hjl; apply Nat.succ_lt_mono in Hjl.
    rewrite replace_at_succ_cons; cbn.
    now apply length_replace_at.
  }
  assert (H : length (tl (replace_at j (k :: l) k)) ≤ it) by now rewrite Hr.
  specialize (H1 H); clear H.
  rewrite Hr in H1.
  cbn.
  destruct j; [ easy | clear Hjz ].
  rewrite replace_at_succ_cons in H1.
  rewrite replace_at_succ_cons.
  cbn - [ seq  ] in H1.
  cbn.
  do 2 rewrite Nat.add_succ_r.
  rewrite <- H1; clear H1.
  unfold "°"; cbn - [ seq ].
  rewrite Nat_sub_succ_1 in Hij.
  remember (ff_app (swap (S (i + length l)) i (S (i + j)))) as f eqn:Hf.
  remember (λ t l, map (ff_app (swap (length l) (fst t) (snd t))) l) as g
    eqn:Hg.
  remember (transp_loop it (S i) (replace_at j l k)) as lb eqn:Hlb.
  rewrite seq_S, <- app_assoc; cbn.
  move g before f; move lb before g.
  move Hij at bottom.
...
*)

Fixpoint nb_nfit i l :=
  match l with
  | [] => 0
  | j :: l' => (if i =? j then 0 else 1) + nb_nfit (S i) l'
  end.

Fixpoint transp_loop it i (p : list nat) :=
  match it with
  | 0 => []
  | S it' =>
      match p with
      | [] => []
      | j :: l =>
          if i =? j then transp_loop it' (S i) l
          else (i, j) :: transp_loop it' i (list_swap_elem 0 p 0 (j - i))
      end
  end.

Definition transp_list p := transp_loop (length p + nb_nfit 0 p) 0 p.

(*
Compute
map (λ p, (p, last (transp_loop (length p + nb_nfit 0 p - 1) 0 p) (0,0))) (canon_sym_gr_list_list 4).
Compute
map (λ p, (p, last (transp_loop (length p + nb_nfit 0 p) 0 p) (0,0))) (canon_sym_gr_list_list 4).
Compute
map (λ p, (p, last (transp_list p) (17,17))) (canon_sym_gr_list_list 4).
*)

(*
Theorem glop : ∀ p i j l,
  p = j :: l
  → i < j
  → nb_fit i p < nb_fit i (list_swap_elem 0 p 0 (j - i)).
Proof.
intros * Hp Hij.
subst p.
revert i j Hij.
induction l as [| k]; intros. {
  cbn - [ nth ].
  rewrite nth_overflow; [ | cbn; flia Hij ].
  do 2 rewrite Nat.add_0_r.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec i j) as [H| H]; [ flia Hij H | clear H ].
  destruct (Nat.eq_dec i 0) as [Hiz| Hiz]; [ easy | ].
...
intros * Hp Hij.
subst p.
unfold list_swap_elem.
cbn - [ nth seq ].
apply Nat.eqb_neq in Hij; rewrite Hij.
apply Nat.eqb_neq in Hij.
rewrite Nat.add_0_l.
unfold transposition.
cbn - [ nth ].
...
*)

(*
Compute (transp_list [3;2;0;1]).
Compute (map (λ l, (l, transp_list l)) (canon_sym_gr_list_list 4)).
Compute (transp_list [20;12;7;9]).
Compute (transp_list (collapse [20;12;7;9])).
Compute (transp_list [3;2;0;1]).
*)

Notation "'Comp' n ( i ∈ l ) , g" :=
  (iter_list l (λ c i, g ° c) (seq 0 n))
  (at level 35, i at level 0, l at level 60, n at level 0).

Theorem swap_id : ∀ n k, swap n k k = seq 0 n.
Proof.
intros.
unfold swap, list_swap_elem.
erewrite map_ext_in. 2: {
  rewrite seq_length.
  intros i Hi.
  apply in_seq in Hi.
  rewrite transposition_id.
  now rewrite seq_nth.
}
rewrite seq_length.
induction n; [ easy | ].
rewrite seq_S; cbn.
rewrite map_app; cbn; f_equal.
apply IHn.
Qed.

Theorem ε_seq : ∀ sta len, ε (seq sta len) = 1%F.
Proof.
intros.
destruct (Nat.eq_dec len 0) as [Hnz| Hnz]. {
  subst len; cbn.
  unfold ε; cbn.
  unfold iter_seq, iter_list; cbn.
  now do 2 rewrite rngl_mul_1_l.
}
unfold ε.
rewrite seq_length.
unfold sign_diff, ff_app.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite seq_nth; [ | flia Hj Hnz ].
    rewrite seq_nth; [ | flia Hi Hnz ].
    replace (if _ <? _ then _ else _) with 1%F. 2: {
      symmetry.
      rewrite if_ltb_lt_dec.
      destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
      apply Nat.add_lt_mono_l with (p := sta) in Hij.
      now apply Nat.compare_gt_iff in Hij; rewrite Hij.
    }
    easy.
  }
  easy.
}
apply all_1_rngl_product_1.
intros i Hi.
now apply all_1_rngl_product_1.
Qed.

Theorem ε_swap_id : ∀ n k, ε (swap n k k) = 1%F.
Proof.
intros.
rewrite swap_id.
apply ε_seq.
Qed.

Theorem is_square_matrix_map : ∀ A B (f : list A → list B) ll n,
  mat_nrows (mk_mat ll) = n
  → (∀ la, la ∈ ll → length (f la) = n)
  → is_square_matrix (mk_mat (map f ll)) = true.
Proof.
intros * Hr Hf.
apply is_scm_mat_iff; cbn in Hr |-*.
rewrite map_length.
split. {
  intros Hc.
  unfold mat_ncols in Hc; cbn in Hc.
  apply length_zero_iff_nil in Hc.
  destruct ll as [| l]; [ easy | exfalso ].
  cbn in Hc.
  specialize (Hf l (or_introl eq_refl)).
  now rewrite Hc, <- Hr in Hf.
} {
  intros l Hl.
  apply in_map_iff in Hl.
  destruct Hl as (a & Hfa & Ha).
  subst l.
  now rewrite Hr, Hf.
}
Qed.

Theorem mat_select_rows_butn_subm : ∀ (M : matrix T) p i k n,
  is_square_matrix M = true
  → NoDup p
  → nth i p 0 = n
  → length p = S n
  → mat_nrows M = S n
  → k ≤ n
  → mat_select_rows (butn i p) (subm n k M) = subm i k (mat_select_rows p M).
Proof.
intros * Hsm Hnd Hi Hp Hr Hk.
unfold mat_select_rows, subm; cbn.
f_equal.
destruct M as (ll); cbn in Hr |-*.
unfold list_list_select_rows.
rewrite <- map_butn, map_map.
apply map_ext_in.
intros j Hj.
destruct (lt_dec j (S n)) as [Hjn| Hjn]. 2: {
  apply Nat.nlt_ge in Hjn.
  rewrite nth_overflow. 2: {
    rewrite map_length, butn_length, Hr; cbn.
    rewrite Nat.leb_refl; cbn.
    rewrite Nat.sub_0_r; flia Hjn.
  }
  rewrite nth_overflow by now rewrite Hr.
  rewrite map_length, butn_length, Hr.
  cbn - [ nth seq ]; rewrite Nat.leb_refl.
  cbn - [ nth seq ]; rewrite Nat.sub_0_r.
  rewrite <- map_butn.
  rewrite (@List_map_const_is_repeat _ _ 0%F). 2: {
    intros; apply List_nth_nil.
  }
  symmetry.
  rewrite (@List_map_const_is_repeat _ _ 0%F). 2: {
    intros; apply List_nth_nil.
  }
  rewrite butn_length.
  do 2 rewrite seq_length.
  f_equal.
  apply Nat.lt_succ_r, Nat.ltb_lt in Hk.
  now rewrite Hk, Nat_sub_succ_1.
}
destruct (Nat.eq_dec j n) as [Hjn'| Hjn']. {
  subst j.
  specialize (NoDup_nat _ Hnd) as H1.
  apply (In_nth _ _ 0) in Hj.
  destruct Hj as (j & Hnj & Hin).
  rewrite butn_length in Hnj.
  rewrite Hp in H1, Hnj.
  rewrite nth_butn in Hin.
  unfold Nat.b2n in Hin.
  rewrite if_leb_le_dec in Hin.
  unfold Nat.b2n in Hin.
  destruct (le_dec i j) as [Hij| Hij]. {
    rewrite fold_ff_app in Hi, Hin.
    specialize (H1 i (j + 1)).
    assert (H : i < S n). {
      unfold Nat.b2n in Hnj.
      rewrite if_ltb_lt_dec in Hnj.
      destruct (lt_dec i (S n)) as [H| Hisn]; [ easy | ].
      flia Hisn Hnj Hij.
    }
    specialize (H1 H).
    apply Nat.ltb_lt in H.
    rewrite H in Hnj; clear H.
    rewrite Nat_sub_succ_1 in Hnj.
    assert (H : j + 1 < S n) by flia Hnj.
    specialize (H1 H); clear H.
    rewrite Hi, Hin in H1.
    specialize (H1 eq_refl).
    flia Hnj Hij H1.
  } {
    apply Nat.nle_gt in Hij.
    destruct (lt_dec i (S n)) as [Hisn| Hisn]. 2: {
      apply Nat.nlt_ge in Hisn.
      rewrite nth_overflow in Hi; [ | now rewrite Hp ].
      subst n.
      unfold Nat.b2n in Hnj.
      rewrite if_ltb_lt_dec in Hnj.
      destruct (lt_dec i 1) as [H| H]; [ flia H Hisn | clear H ].
      rewrite Nat.sub_0_r in Hnj.
      apply Nat.lt_1_r in Hnj; subst j.
      destruct ll as [| la]; [ easy | ].
      destruct ll; [ | easy ].
      cbn.
      destruct la as [| a]; [ easy | ].
      apply is_scm_mat_iff in Hsm.
      destruct Hsm as (Hcrb, Hclb).
      cbn - [ In ] in Hclb.
      specialize (Hclb (a :: la) (or_introl eq_refl)) as H2.
      cbn in H2.
      destruct la; [ | easy ].
      now apply Nat.le_0_r in Hk; subst k.
    }
    specialize (H1 i j Hisn).
    apply Nat.ltb_lt in Hisn; rewrite Hisn in Hnj.
    cbn in Hnj.
    assert (H : j < S n) by flia Hnj.
    rewrite fold_ff_app in Hi, Hin.
    rewrite Nat.add_0_r in Hin.
    rewrite Hi, Hin in H1.
    specialize (H1 H eq_refl).
    flia Hij H1.
  }
}
rewrite (List_map_nth' []). 2: {
  rewrite butn_length, Hr; cbn.
  rewrite Nat.leb_refl; cbn.
  flia Hjn Hjn'.
}
rewrite nth_butn.
unfold Nat.b2n.
rewrite if_leb_le_dec.
destruct (le_dec n j) as [H| H]; [ flia Hjn Hjn' H | clear H ].
rewrite map_length, butn_length, Hr.
cbn - [ nth seq ]; rewrite Nat.leb_refl.
cbn - [ nth seq ]; rewrite Nat.sub_0_r.
rewrite <- map_butn.
rewrite map_butn_seq.
apply Nat.lt_succ_r, Nat.ltb_lt in Hk.
rewrite Hk, Nat_sub_succ_1.
apply map_ext_in.
intros u v.
rewrite Nat.add_0_l, Nat.add_0_r.
now rewrite nth_butn.
(**)
Qed.

Theorem fold_left_mk_mat : ∀ A (M : matrix T) (f : _ → A → _) l,
  fold_left (λ M a, mk_mat (f (mat_list_list M) a)) l M =
  mk_mat (fold_left f l (mat_list_list M)).
Proof.
intros.
destruct M as (ll); cbn.
revert ll.
induction l as [| a]; intros; [ easy | cbn ].
apply IHl.
Qed.

(*
Compute (
map (λ p, ((*p,*)
  list_eqb Nat.eqb p
    (iter_list (transp_list p) (λ l t, swap (length p) (fst t) (snd t) ° l)
      (seq 0 (length p))))) (canon_sym_gr_list_list 4)).
Print transp_list.
Compute
map (λ p, transp_list p) (canon_sym_gr_list_list 4).
Compute
map (λ p, transp_loop (length p + length p - nb_fit 0 p) 0 p) (canon_sym_gr_list_list 4).
Compute
map (λ p, transp_loop (length p + length p - nb_fit 0 p - 1) 0 p) (canon_sym_gr_list_list 4).
Compute
map (λ p, last (transp_loop (length p + length p - nb_fit 0 p) 0 p) (0,0)) (canon_sym_gr_list_list 4).
Compute
map (λ p, last (transp_loop (length p + length p - nb_fit 0 p - 1) 0 p) (0,0)) (canon_sym_gr_list_list 4).
Compute
map (λ p, last (transp_loop (length p + length p - nb_fit 0 p - 1) 0 p) (0,0)) (canon_sym_gr_list_list 5).
Compute
map (λ p, last (transp_loop (length p + length p - nb_fit 0 p - 2) 0 p) (0,0)) (canon_sym_gr_list_list 6).
Compute
map (λ p, last (transp_loop (length p + length p - nb_fit 0 p - 1) 0 p) (0,0)) (canon_sym_gr_list_list 6).
Compute
map (λ p, last (transp_loop (length p + length p - nb_fit 0 p) 0 p) (0,0)) (canon_sym_gr_list_list 6).
...
Compute
map (λ p, (p, last (transp_loop (length p + length p - nb_fit 0 p - 1) 0 p) (0,0))) (canon_sym_gr_list_list 4).
Compute (let p := [2; 3; 0; 1] in transp_list p).
Compute (let p := [2; 3; 0; 1] in
(length p + length p - nb_fit 0 p - 1,
transp_loop (length p + length p - nb_fit 0 p - 1) 0 p)).
...
Compute (let p := [2; 3; 0; 1] in
(length p + length p - nb_fit 0 p - 2,
transp_loop (length p + length p - nb_fit 0 p - 2) 0 p)).
...
Compute (
map (λ p, (p,
  list_eqb Nat.eqb p
    (iter_list (transp_loop (length p + 1) 0 p) (λ l t, swap (length p) (fst t) (snd t) ° l)
      (seq 0 (length p))))) (canon_sym_gr_list_list 6)).
Compute (let p := [1;2;3;0;5;4] in
transp_loop (length p + 2) 0 p).
Compute (let p := [1;2;3;0;5;4] in
transp_loop (length p + 3) 0 p).
Compute (let p := [1;2;3;0;5;4] in
transp_loop (length p + 4) 0 p).
Compute (let p := [1;2;3;0;5;4] in
transp_loop (length p + 5) 0 p).
Compute (let p := [1;2;3;0;5;4] in
length p - nb_fit 0 p).
...
[1; 2; 3; 0; 5; 4]
213054 1
312054 2
012354 3
012354 0
012354 1
012354 2
012354 3
012345 5
012345 4
012345 5
...
[1; 2; 0; 4; 3]
[2; 0; 1; 4; 3]
...
Compute (map (λ l, (l, length l - nb_fit 0 l, transp_list l)) (canon_sym_gr_list_list 4)).
...
*)

Theorem transp_loop_nil : ∀ it i, transp_loop it i [] = [].
Proof. intros; now destruct it. Qed.

Theorem nth_list_swap_elem : ∀ A (d : A) i j l,
  i < length l
  → j < length l
  → nth j (list_swap_elem d l i j) d = nth i l d.
Proof.
intros * Hil Hjl.
unfold list_swap_elem.
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
now rewrite transposition_2.
Qed.

(*
Theorem transp_loop_enough_iter : ∀ it1 it2 i l,
  2 * length l ≤ it1
  → 2 * length l ≤ it2
  → transp_loop it1 i l = transp_loop it2 i l.
Proof.
intros * Hli1 Hli2.
revert i l it2 Hli1 Hli2.
induction it1; intros; cbn. {
  apply Nat.le_0_r, Nat.eq_mul_0 in Hli1.
  destruct Hli1 as [Hli1| Hli1]; [ easy | ].
  apply length_zero_iff_nil in Hli1; subst l; cbn.
  symmetry; apply transp_loop_nil.
}
destruct l as [| j]. {
  symmetry; apply transp_loop_nil.
}
destruct it2. {
  apply Nat.le_0_r, Nat.eq_mul_0 in Hli2.
  now destruct Hli2.
}
cbn - [ list_swap_elem ].
do 2 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  apply IHit1. {
    cbn in Hli1 |-*; flia Hli1.
  } {
    cbn in Hli2 |-*; flia Hli2.
  }
} {
  f_equal.
  cbn in Hli1, Hli2.
  rewrite Nat.add_0_r, Nat.add_succ_r in Hli1, Hli2.
  apply Nat.succ_le_mono in Hli1, Hli2.
...
Theorem glop : ∀ it1 it2 i j l,
  S (length l + length l) ≤ it1
  →  S (length l + length l) ≤ it2
  → transp_loop it1 i (list_swap_elem 0 (j :: l) 0 (j - i)) =
    transp_loop it2 i (list_swap_elem 0 (j :: l) 0 (j - i)).
Proof.
intros * Hit1 Hit2.
revert i j l it2 Hit1 Hit2.
induction it1; intros; [ easy | ].
destruct it2; [ easy | ].
apply Nat.succ_le_mono in Hit1, Hit2.
cbn - [ list_swap_elem ].
remember (list_swap_elem 0 (j :: l) 0 (j - i)) as l1 eqn:Hl1.
symmetry in Hl1.
destruct l1 as [| j1]; [ easy | ].
do 2 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec i j1) as [Hij1| Hij1]. {
  subst j1.
  destruct it1. {
    apply Nat.le_0_r, Nat.eq_add_0 in Hit1.
    destruct Hit1 as (H, _).
    apply length_zero_iff_nil in H; subst l.
    cbn - [ nth ] in Hl1.
    injection Hl1; clear Hl1; intros Hi H; subst l1.
    now do 2 rewrite transp_loop_nil.
  }
  destruct it2. {
    apply Nat.le_0_r, Nat.eq_add_0 in Hit2.
    destruct Hit2 as (H, _).
    apply length_zero_iff_nil in H; subst l.
    cbn - [ nth ] in Hl1.
    injection Hl1; clear Hl1; intros Hi H; subst l1.
    now do 2 rewrite transp_loop_nil.
  }
  cbn - [ list_swap_elem "=?" ].
  destruct l1 as [| j1]; [ easy | ].
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (S i) j1) as [Hsij1| Hsij1]. {
    subst j1.
...
  remember (list_swap_elem 0 (j :: l) 0 (j - i)) as l1 eqn:Hl1.
  symmetry in Hl1.
...
  cbn in Hli1, Hli2.
  rewrite Nat.add_0_r, Nat.add_succ_r in Hli1, Hli2.
  apply Nat.succ_le_mono in Hli1, Hli2.
  destruct it1; [ easy | ].
  destruct it2; [ easy | ].
  apply Nat.succ_le_mono in Hli1, Hli2.
  cbn - [ list_swap_elem ].
  destruct l1 as [| j1]; [ easy | ].
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec i j1) as [Hij1| Hij1]. {
    subst j1.
    destruct it1. {
      apply Nat.le_0_r, Nat.eq_add_0 in Hli1.
      destruct Hli1 as (H, _).
      apply length_zero_iff_nil in H; subst l.
      cbn - [ nth ] in Hl1.
      injection Hl1; clear Hl1; intros Hi H; subst l1.
      now do 2 rewrite transp_loop_nil.
    }
    destruct it2. {
      apply Nat.le_0_r, Nat.eq_add_0 in Hli2.
      destruct Hli2 as (H, _).
      apply length_zero_iff_nil in H; subst l.
      cbn - [ nth ] in Hl1.
      injection Hl1; clear Hl1; intros Hi H; subst l1.
      now do 2 rewrite transp_loop_nil.
    }
    cbn - [ list_swap_elem "=?" ].
    destruct l1 as [| j1]; [ easy | ].
    do 2 rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec (S i) j1) as [Hsij1| Hsij1]. {
      subst j1.
      destruct it1. {
        apply Nat.le_1_r in Hli1.
        destruct Hli1 as [H| H]. {
          apply Nat.eq_add_0 in H.
          destruct H as (H, _).
          now apply length_zero_iff_nil in H; subst l.
        }
        apply Nat.eq_add_1 in H.
        destruct H as [H| H]. {
          now destruct H as (H1, H2); rewrite H1 in H2.
        } {
          now destruct H as (H1, H2); rewrite H1 in H2.
        }
      }
      destruct it2. {
        apply Nat.le_1_r in Hli2.
        destruct Hli2 as [H| H]. {
          apply Nat.eq_add_0 in H.
          destruct H as (H, _).
          now apply length_zero_iff_nil in H; subst l.
        }
        apply Nat.eq_add_1 in H.
        destruct H as [H| H]. {
          now destruct H as (H1, H2); rewrite H1 in H2.
        } {
          now destruct H as (H1, H2); rewrite H1 in H2.
        }
      }
      cbn - [ list_swap_elem "=?" ].
      destruct l1 as [| j1]; [ easy | ].
      do 2 rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec (S (S i)) j1) as [Hsij1| Hsij1]. {
        subst j1.
...
  → list_swap_elem 0 (j :: l) 0 (j - i) = i :: S i :: S (S i) :: l1
  → transp_loop it1 (S (S (S i))) l1 = transp_loop it2 (S (S (S i))).
...
        destruct it1. {
          destruct l as [| j1]; [ easy | ].
          cbn in Hli1.
          rewrite Nat.add_succ_r in Hli1.
          do 2 apply Nat.succ_le_mono in Hli1.
          apply Nat.le_0_r, Nat.eq_add_0 in Hli1.
          destruct Hli1 as (H, _).
          now apply length_zero_iff_nil in H; subst l.
        }
        destruct it2. {
          destruct l as [| j1]; [ easy | ].
          cbn in Hli2.
          rewrite Nat.add_succ_r in Hli2.
          do 2 apply Nat.succ_le_mono in Hli2.
          apply Nat.le_0_r, Nat.eq_add_0 in Hli2.
          destruct Hli2 as (H, _).
          now apply length_zero_iff_nil in H; subst l.
        }
        cbn - [ list_swap_elem "=?" ].
        destruct l1 as [| j1]; [ easy | ].
        do 2 rewrite if_eqb_eq_dec.
        destruct (Nat.eq_dec (S (S (S i))) j1) as [Hsij1| Hsij1]. {
          subst j1.
...
...
Theorem glop : ∀ l i j,
  i ≠ j
  → nb_fit i (list_swap_elem 0 (j :: l) 0 (j - i)) < nb_fit i l.
Proof.
intros * Hij.
cbn.
remember (j - i) as k eqn:Hk; symmetry in Hk.
destruct k. {
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec i j) as [H| H]; [ easy | clear H ].
  rewrite Nat.add_0_r.
  erewrite map_ext_in. 2: {
    intros n Hn.
    apply in_seq in Hn.
    rewrite transposition_id.
    replace n with (S (n - 1)) at 1 by flia Hn.
    easy.
  }
...
  apply IHit1; rewrite list_swap_elem_length.
(* ouais bin chais pas *)
...
(* à chaque itération, le nombre de trucs pas à sa place diminue au moins de 1 *)
Print transp_loop.
Theorem glop : ∀ l i j,
  nb_fit 0 (list_swap_elem 0 l 0 (j - i)) < nb_fit 0 l.
(* ouais, non *)
...
*)

(*
Theorem nb_fit_ub : ∀ i l, nb_fit i l ≤ length l.
Proof.
intros.
revert i.
induction l as [| j]; intros; cbn; [ easy | cbn ].
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  subst j.
  apply -> Nat.succ_le_mono.
  apply IHl.
} {
  transitivity (length l); [ | apply Nat.le_succ_diag_r ].
  apply IHl.
}
Qed.
*)

(*
Theorem eq_nb_fit_length : ∀ i l,
  nb_fit i l = length l
  → l = seq i (length l).
Proof.
intros * Hfl.
revert i Hfl.
induction l as [| j]; intros; [ easy | cbn ].
cbn in Hfl.
rewrite if_eqb_eq_dec in Hfl.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  subst j; f_equal.
  apply Nat.succ_inj in Hfl.
  now apply IHl.
} {
  cbn in Hfl.
  specialize (nb_fit_ub (S i) l) as H1.
  rewrite Hfl in H1.
  apply Nat.nle_gt in H1.
  now exfalso; apply H1.
}
Qed.
*)

(* il manque une restriction sur la première hypothèse
   (∀ a b, f (f a b) b = a)
Theorem fold_left_invol_rev : ∀ A B (f : A → B → A) a b l,
  (∀ a b, f (f a b) b = a)
  → fold_left f l a = b
  → fold_left f (rev l) b = a.
Proof.
intros * Huv Hab.
rewrite <- fold_left_rev_right.
rewrite rev_involutive.
revert a b Hab.
induction l as [| c]; intros; [ easy | ].
cbn in Hab |-*.
rewrite (IHl _ _ Hab).
apply Huv.
Qed.
*)

Theorem transp_loop_seq : ∀ it sta len,
  transp_loop it sta (seq sta len) = [].
Proof.
intros.
revert sta len.
induction it; intros; cbn; [ easy | ].
destruct len; [ easy | cbn ].
rewrite Nat.eqb_refl.
apply IHit.
Qed.

Theorem transp_loop_app_seq_gen : ∀ it s i la,
  transp_loop it (s + i) la = transp_loop (it + i) s (seq s i ++ la).
Proof.
intros.
revert i s la.
induction it; intros. {
  cbn.
  revert s la.
  induction i; intros; [ easy | cbn ].
  rewrite Nat.eqb_refl.
  apply IHi.
}
cbn - [ seq "=?" ].
destruct la as [| a]. {
  rewrite app_nil_r.
  destruct i; [ easy | cbn ].
  rewrite Nat.eqb_refl.
  symmetry; apply transp_loop_seq.
}
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec (s + i) a) as [Hia| Hia]. {
  subst a.
  replace (seq s i ++ s + i :: la) with (seq s (S i) ++ la). 2: {
    now rewrite seq_S, <- app_assoc.
  }
  cbn.
  rewrite Nat.eqb_refl.
  rewrite <- Nat.add_succ_r.
  rewrite IHit.
  rewrite Nat.add_succ_r; cbn.
  now rewrite Nat.eqb_refl.
}
remember (seq s i ++ a :: la) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]; [ now destruct i | ].
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec s b) as [Hsb| Hsb]. 2: {
  destruct i. {
    do 2 rewrite Nat.add_0_r.
    cbn in Hlb.
    now injection Hlb; clear Hlb; intros; subst b lb.
  }
  cbn in Hlb.
  now injection Hlb; clear Hlb; intros.
}
subst b.
clear IHit.
revert it s a la lb Hia Hlb.
induction i; intros. {
  rewrite Nat.add_0_r in Hia.
  cbn in Hlb.
  now injection Hlb; clear Hlb; intros; subst a lb.
}
cbn in Hlb.
injection Hlb; clear Hlb; intros Hlb.
subst lb.
rewrite (Nat.add_succ_r it).
cbn - [ list_swap_elem seq "=?" ].
remember (seq (S s) i ++ a :: la) as lb eqn:Hb.
symmetry in Hb.
destruct lb as [| b]; [ now destruct i | ].
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec (S s) b) as [Hsb| Hsb]. {
  subst b.
  rewrite <- Nat.add_succ_comm in Hia |-*.
  now apply IHi.
}
rewrite <- Nat.add_succ_comm, Nat.add_comm.
f_equal. {
  destruct i. {
    cbn in Hb.
    now injection Hb; clear Hb; intros; subst b lb.
  }
  cbn in Hb.
  now injection Hb; clear Hb; intros.
}
destruct i. {
  cbn in Hb.
  rewrite Nat.add_0_l, Nat.add_0_r.
  now injection Hb; clear Hb; intros; subst b lb.
}
cbn in Hb.
now injection Hb; clear Hb; intros; subst b lb.
Qed.

Theorem transp_loop_app_seq : ∀ it i la,
  transp_loop it i la = transp_loop (it + i) 0 (seq 0 i ++ la).
Proof.
intros.
now rewrite <- transp_loop_app_seq_gen.
Qed.

Theorem list_swap_elem_id : ∀ A (d : A) l i, list_swap_elem d l i i = l.
Proof.
intros.
unfold list_swap_elem.
rewrite List_map_nth_seq with (d := d).
apply map_ext_in.
intros j Hj.
now rewrite transposition_id.
Qed.

Theorem in_transp_loop_bounds : ∀ it k ij l,
  ij ∈ transp_loop it k l
  → k ≤ fst ij ≤ k + length l.
Proof.
intros * Hij.
revert ij k l Hij.
induction it; intros; [ easy | cbn in Hij ].
destruct l as [| j]; [ easy | ].
rewrite if_eqb_eq_dec in Hij.
destruct (Nat.eq_dec k j) as [Hkj| Hkj]. {
  subst j.
  specialize (IHit _ _ _ Hij) as H1.
  destruct H1 as (H1, H2).
  rewrite Nat.add_succ_comm in H2.
  split; [ | easy ].
  destruct (Nat.eq_dec (S k) (fst ij)) as [Hkij| Hkij]; [ | flia H1 Hkij ].
  rewrite <- Hkij.
  apply Nat.le_succ_diag_r.
}
destruct Hij as [Hij| Hij]. {
  subst ij; cbn.
  split; [ easy | ].
  apply Nat.le_add_r.
}
specialize (IHit _ _ _ Hij) as H1.
now rewrite list_swap_elem_length in H1.
Qed.

Theorem permut_eq_iter_list_transp_loop : ∀ l it i,
  is_permut_list (seq 0 i ++ l)
  → it = length l + nb_nfit i l
  → seq 0 i ++ l =
    fold_left (λ l t, swap (length l) (fst t) (snd t) ° l)
      (transp_loop it i l) (seq 0 (i + length l)).
Proof.
intros * Hp Hit.
revert l i Hp Hit.
induction it; intros; cbn. {
  cbn in Hit.
  symmetry in Hit.
  apply Nat.eq_add_0 in Hit.
  destruct Hit as (Hl & Hnf).
  apply length_zero_iff_nil in Hl; subst l.
  now rewrite app_nil_r, Nat.add_0_r.
}
destruct l as [| j]; [ easy | ].
cbn in Hit.
apply Nat.succ_inj in Hit.
rewrite if_eqb_eq_dec in Hit |-*.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  subst j.
  replace (seq 0 i ++ i :: l) with (seq 0 (S i) ++ l). 2: {
    now rewrite seq_S, <- app_assoc.
  }
  rewrite List_length_cons, <- Nat.add_succ_comm.
  apply IHit; [ now rewrite seq_S, <- app_assoc | easy ].
} {
  cbn - [ list_swap_elem "=?" ].
  rewrite seq_length.
  rewrite comp_1_r by now rewrite swap_length.
Abort.

Theorem app_seq_swap_is_permut_list : ∀ i j l,
  is_permut_list (seq 0 i ++ j :: l)
  → i < j
  → is_permut_list (seq 0 i ++ list_swap_elem 0 (j :: l) 0 (j - i)).
Proof.
intros * Hp Hilj.
split. {
  intros k Hk.
  rewrite app_length, seq_length, list_swap_elem_length; cbn.
  apply in_app_or in Hk.
  destruct Hk as [Hk| Hk]; [ apply in_seq in Hk; flia Hk | ].
  unfold list_swap_elem in Hk.
  rewrite in_map_iff in Hk.
  destruct Hk as (u & Huk & Hu).
  subst k.
  apply in_seq in Hu; cbn in Hu.
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec u 0) as [Huz| Huz]. {
    subst u.
    destruct Hp as (Hpp, Hpl).
    rewrite app_length, seq_length in Hpp; cbn in Hpp.
    specialize (Hpp (nth (j - i) (j :: l) 0)) as H2.
    apply H2; clear H2.
    apply in_or_app.
    right; right.
    replace (j - i) with (S (j - S i)) by flia Hilj; cbn.
    apply nth_In.
    specialize (Hpp j) as H2.
    assert (H : j ∈ seq 0 i ++ j :: l). {
      apply in_or_app.
      now right; left.
    }
    specialize (H2 H); clear H.
    cbn in H2.
    flia H2 Hilj.
  }
  destruct (Nat.eq_dec u (j - i)) as [Huj| Huj]. {
    subst u; cbn; flia Hu.
  }
  destruct u; [ easy | ].
  cbn.
  destruct Hp as (Hpp, Hpl).
  rewrite app_length, seq_length in Hpp; cbn in Hpp.
  apply Hpp, in_or_app.
  destruct (lt_dec (nth u l 0) i) as [Hui| Hui]. {
    now left; apply in_seq.
  }
  right.
  apply Nat.nlt_ge in Hui.
  destruct (Nat.eq_dec (nth u l 0) j) as [Hnuj| Hnuj]. {
    now rewrite Hnuj; left.
  }
  right.
  apply nth_In.
  destruct Hu as (_, Hu).
  now apply Nat.succ_lt_mono.
} {
  apply nat_NoDup.
  rewrite app_length, seq_length, list_swap_elem_length.
  cbn - [ list_swap_elem ].
  intros u v Hu Hv Huv.
  unfold ff_app in Huv.
  destruct (lt_dec u i) as [Hui| Hui]. {
    rewrite app_nth1 in Huv; [ | now rewrite seq_length ].
    rewrite seq_nth in Huv; [ | easy ].
    rewrite Nat.add_0_l in Huv.
    destruct (lt_dec v i) as [Hvi| Hvi]. {
      rewrite app_nth1 in Huv; [ | now rewrite seq_length ].
      rewrite seq_nth in Huv; [ | easy ].
      easy.
    }
    apply Nat.nlt_ge in Hvi; exfalso.
    rewrite app_nth2 in Huv; [ | now rewrite seq_length ].
    rewrite seq_length in Huv.
    rewrite Huv in Hui.
    apply Nat.nle_gt in Hui.
    apply Hui; clear Hui.
    unfold list_swap_elem.
    rewrite (List_map_nth' 0). 2: {
      rewrite seq_length; cbn; flia Hv.
    }
    rewrite seq_nth; [ | cbn; flia Hv ].
    rewrite Nat.add_0_l.
    unfold transposition.
    do 2 rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec (v - i) 0) as [Hviz| Hviz]. {
      replace (j - i) with (S (j - S i)) by flia Hilj.
      rewrite List_nth_succ_cons.
      apply Nat.sub_0_le in Hviz.
      apply Nat.le_antisymm in Hvi; [ subst v | easy ].
      clear Hviz Hv.
      rewrite Nat.sub_diag in Huv.
      unfold list_swap_elem in Huv.
      rewrite (List_map_nth' 0) in Huv; [ | now rewrite seq_length; cbn ].
      rewrite seq_nth in Huv; [ | now cbn ].
      unfold transposition in Huv.
      rewrite Nat.eqb_refl in Huv.
      replace (j - i) with (S (j - S i)) in Huv by flia Hilj.
      rewrite List_nth_succ_cons in Huv.
      rewrite <- Huv.
      destruct Hp as (Hpp, Hpl).
      rewrite app_length, seq_length in Hpp; cbn in Hpp.
      assert (Hj : j ∈ seq (S i) (length l)). {
        apply in_seq.
        split; [ easy | cbn ].
        rewrite <- Nat.add_succ_r.
        apply (Hpp j).
        now apply in_or_app; right; left.
      }
      assert (Hul : u ∈ l). {
        rewrite Huv.
        apply nth_In.
        apply in_seq in Hj.
        flia Hj.
      }
      assert (Hus : u ∉ seq 0 i). {
        intros H.
        apply NoDup_app_iff in Hpl.
        destruct Hpl as (Hil & Hjl & Hnjl).
        apply Hnjl in H.
        now apply H; right.
      }
      apply Nat.nlt_ge; intros H; apply Hus; clear Hus.
      now apply in_seq.
    }
    destruct (Nat.eq_dec (v - i) (j - i)) as [Hvji| Hvji]. {
      now apply Nat.lt_le_incl.
    }
    replace (v - i) with (S (v - S i)) by flia Hvi Hviz.
    rewrite List_nth_succ_cons.
    destruct Hp as (Hpp, Hpl).
    rewrite app_length, seq_length in Hpp; cbn in Hpp.
    unfold list_swap_elem in Huv.
    rewrite (List_map_nth' 0) in Huv. 2: {
      rewrite seq_length; cbn; flia Hv.
    }
    rewrite seq_nth in Huv; [ | cbn; flia Hv ].
    unfold transposition in Huv.
    rewrite Nat.add_0_l in Huv.
    replace (v - i) with (S (v - S i)) in Huv at 1 by flia Hviz.
    replace (S (v - S i) =? 0) with false in Huv by easy.
    apply Nat.eqb_neq in Hvji; rewrite Hvji in Huv.
    apply Nat.eqb_neq in Hvji.
    replace (v - i) with (S (v - S i)) in Huv at 1 by flia Hviz.
    rewrite List_nth_succ_cons in Huv.
    rewrite <- Huv.
    assert (Hul : u ∈ l). {
      rewrite Huv.
      apply nth_In.
      flia Hv Hviz.
    }
    assert (Hus : u ∉ seq 0 i). {
      intros H.
      apply NoDup_app_iff in Hpl.
      destruct Hpl as (Hil & Hjl & Hnjl).
      apply Hnjl in H.
      now apply H; right.
    }
    apply Nat.nlt_ge; intros H; apply Hus; clear Hus.
    now apply in_seq.
  }
  apply Nat.nlt_ge in Hui.
  rewrite app_nth2 in Huv; [ | now rewrite seq_length ].
  rewrite seq_length in Huv.
  destruct (lt_dec v i) as [Hvi| Hvi]. 2: {
    apply Nat.nlt_ge in Hvi.
    rewrite app_nth2 in Huv; [ | now rewrite seq_length ].
    rewrite seq_length in Huv.
    unfold list_swap_elem in Huv.
    rewrite (List_map_nth' 0) in Huv; [ | rewrite seq_length; cbn; flia Hu ].
    rewrite (List_map_nth' 0) in Huv; [ | rewrite seq_length; cbn; flia Hv ].
    rewrite seq_nth in Huv; [ | cbn; flia Hu ].
    rewrite seq_nth in Huv; [ | cbn; flia Hv ].
    do 2 rewrite Nat.add_0_l in Huv.
    unfold transposition in Huv.
    do 4 rewrite if_eqb_eq_dec in Huv.
    destruct (Nat.eq_dec (u - i) 0) as [Huiz| Huiz]. {
      apply Nat.sub_0_le in Huiz.
      apply Nat.le_antisymm in Huiz; [ | easy ].
      subst u; clear Hu Hui.
      destruct (Nat.eq_dec (v - i) 0) as [Hviz| Hviz]. {
        apply Nat.sub_0_le in Hviz.
        now apply Nat.le_antisymm.
      }
      destruct (Nat.eq_dec (v - i) (j - i)) as [Hvij| Hvij]. {
        rewrite <- Hvij in Huv.
        replace (v - i) with (S (v - S i)) in Huv by flia Hviz Hvi.
        rewrite List_nth_succ_cons in Huv.
        rewrite List_nth_0_cons in Huv.
        assert (H : v = j) by flia Hvij Hviz.
        subst v; clear Hvij Hviz.
        destruct Hp as (Hpp, Hpl).
        rewrite app_length, seq_length in Hpp; cbn in Hpp.
        assert (Hul : j ∈ l). {
          rewrite <- Huv.
          apply nth_In.
          flia Hv Hilj.
        }
        apply NoDup_app_iff in Hpl.
        destruct Hpl as (Hil & Hjl & Hnjl).
        apply NoDup_cons_iff in Hjl.
        easy.
      }
      destruct Hp as (Hpp, Hpl).
      rewrite app_length, seq_length in Hpp; cbn in Hpp.
      apply NoDup_app_iff in Hpl.
      destruct Hpl as (Hil & Hjl & Hnjl).
      apply Nat.neq_sym in Hvij.
      apply (NoDup_nat _ Hjl) in Huv; [ easy | cbn | cbn; flia Hv ].
      specialize (Hpp j) as H1.
      assert (H : j ∈ seq 0 i ++ j :: l). {
        now apply in_or_app; right; left.
      }
      specialize (H1 H); clear H.
      flia H1.
    }
    destruct (Nat.eq_dec (u - i) (j - i)) as [Huji| Huji]. {
      rewrite List_nth_0_cons in Huv.
      assert (H : u = j) by flia Huji Huiz.
      subst u.
      clear Hui Huji Huiz Hui.
      destruct (Nat.eq_dec (v - i) 0) as [Hviz| Hviz]. {
        assert (H : v = i) by flia Hviz Hvi; subst v.
        clear Hvi Hviz Hv.
        replace (j - i) with (S (j - S i)) in Huv by flia Hilj.
        rewrite List_nth_succ_cons in Huv.
        assert (Hul : j ∈ l). {
          rewrite Huv.
          apply nth_In.
          flia Hu Hilj.
        }
        destruct Hp as (Hpp, Hpl).
        rewrite app_length, seq_length in Hpp; cbn in Hpp.
        apply NoDup_app_iff in Hpl.
        destruct Hpl as (Hil & Hjl & Hnjl).
        apply NoDup_cons_iff in Hjl.
        easy.
      }
      destruct (Nat.eq_dec (v - i) (j - i)) as [Hvji| Hvji]. {
        flia Hvji Hviz.
      }
      replace (v - i) with (S (v - S i)) in Huv by flia Hviz.
      rewrite List_nth_succ_cons in Huv.
      assert (Hul : j ∈ l). {
        rewrite Huv.
        apply nth_In.
        flia Hv Hviz.
      }
      destruct Hp as (Hpp, Hpl).
      rewrite app_length, seq_length in Hpp; cbn in Hpp.
      apply NoDup_app_iff in Hpl.
      destruct Hpl as (Hil & Hjl & Hnjl).
      apply NoDup_cons_iff in Hjl.
      easy.
    } {
      replace (u - i) with (S (u - S i)) in Huv by flia Hui Huiz.
      rewrite List_nth_succ_cons in Huv.
      destruct (Nat.eq_dec (v - i) 0) as [Hviz| Hviz]. {
        assert (H : v = i) by flia Hviz Hvi; subst v.
        clear Hvi Hviz Hv.
        replace (j - i) with (S (j - S i)) in Huv by flia Hilj.
        rewrite List_nth_succ_cons in Huv.
        destruct Hp as (Hpp, Hpl).
        rewrite app_length, seq_length in Hpp; cbn in Hpp.
        apply NoDup_app_iff in Hpl.
        destruct Hpl as (Hil & Hjl & Hnjl).
        apply NoDup_cons_iff in Hjl.
        destruct Hjl as (Hjl & Hl).
        apply (NoDup_nat _ Hl) in Huv; cycle 1. {
          flia Hu Huiz.
        } {
          specialize (Hpp j) as H1.
          assert (H : j ∈ seq 0 i ++ j :: l). {
            now apply in_or_app; right; left.
          }
          specialize (H1 H); clear H.
          flia H1 Hilj.
        }
        flia Huiz Huv Hilj Huji.
      }
      destruct (Nat.eq_dec (v - i) (j - i)) as [Hvji| Hvji]. {
        cbn in Huv.
        assert (H : v = j) by flia Hviz Hvji; subst v.
        clear Hvji Hviz.
        assert (Hul : j ∈ l). {
          rewrite <- Huv.
          apply nth_In.
          flia Hu Huiz.
        }
        destruct Hp as (Hpp, Hpl).
        rewrite app_length, seq_length in Hpp; cbn in Hpp.
        apply NoDup_app_iff in Hpl.
        destruct Hpl as (Hil & Hjl & Hnjl).
        apply NoDup_cons_iff in Hjl.
        easy.
      } {
        replace (v - i) with (S (v - S i)) in Huv by flia Hviz.
        rewrite List_nth_succ_cons in Huv.
        destruct Hp as (Hpp, Hpl).
        rewrite app_length, seq_length in Hpp; cbn in Hpp.
        apply NoDup_app_iff in Hpl.
        destruct Hpl as (Hil & Hjl & Hnjl).
        apply NoDup_cons_iff in Hjl.
        destruct Hjl as (Hjl & Hl).
        apply (NoDup_nat _ Hl) in Huv; cycle 1. {
          flia Hu Huiz.
        } {
          flia Hv Hviz.
        }
        flia Huv Hui Hvi Huiz Hviz.
      }
    }
  } {
    exfalso.
    clear Hv.
    rewrite app_nth1 in Huv; [ | now rewrite seq_length ].
    rewrite seq_nth in Huv; [ | easy ].
    rewrite Nat.add_0_l in Huv.
    rewrite <- Huv in Hvi; clear Huv.
    unfold list_swap_elem in Hvi.
    rewrite (List_map_nth' 0) in Hvi. 2: {
      rewrite seq_length; cbn; flia Hu.
    }
    rewrite seq_nth in Hvi; [ | cbn; flia Hu ].
    rewrite Nat.add_0_l in Hvi.
    destruct Hp as (Hpp, Hpl).
    rewrite app_length, seq_length in Hpp; cbn in Hpp.
    apply NoDup_app_iff in Hpl.
    destruct Hpl as (Hil & Hjl & Hnjl).
    remember (nth _ _ _) as k eqn:Hk.
    assert (H1 : k ∈ seq 0 i) by now apply in_seq.
    apply Hnjl in H1; apply H1; clear H1.
    rewrite Hk.
    apply nth_In; cbn.
    unfold transposition.
    do 2 rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec (u - i) 0) as [Huiz| Huiz]. {
      specialize (Hpp j) as H1.
      assert (H : j ∈ seq 0 i ++ j :: l). {
        now apply in_or_app; right; left.
      }
      specialize (H1 H); clear H.
      flia H1.
    }
    destruct (Nat.eq_dec (u - i) (j - i)) as [Huji| Huji]; [ easy | ].
    flia Hu.
  }
}
Qed.

Theorem nb_nfit_app : ∀ i la lb,
  nb_nfit i (la ++ lb) = nb_nfit i la + nb_nfit (i + length la) lb.
Proof.
intros.
revert i lb.
induction la as [| j]; intros; [ now rewrite Nat.add_0_r | cbn ].
now rewrite IHla, Nat.add_assoc, Nat.add_succ_comm.
Qed.

Theorem fold_right_transp_loop : ∀ l it i,
  is_permut_list (seq 0 i ++ l)
  → length l + nb_nfit i l ≤ it
  → fold_right (λ t l, swap (length l) (fst t) (snd t) ° l)
      (seq 0 i ++ l) (transp_loop it i l) =
    seq 0 (i + length l).
Proof.
intros * Hp Hit.
(*
Compute (let p := [1;2;3;0;5;4] in
  let i := first_non_fix_transp 0 p in
  let l := skipn i p in
  let it := length l + length l - nb_fit i l in
  fold_right
    (λ (t : nat * nat) (l0 : list nat), swap (length l0) (fst t) (snd t) ° l0)
    (seq 0 i ++ l) (transp_loop it i l) = seq 0 (i + length l)
).
Compute (map (λ p,
  let i := first_non_fix_transp 0 p in
  let l := skipn i p in
  let it := length l + length l - nb_fit i l in
  fold_right
    (λ (t : nat * nat) (l0 : list nat), swap (length l0) (fst t) (snd t) ° l0)
    (seq 0 i ++ l) (transp_loop it i l) = seq 0 (i + length l)
) (canon_sym_gr_list_list 4)
).
*)
revert l i Hp Hit.
induction it; intros; cbn. {
  apply Nat.le_0_r in Hit.
  apply Nat.eq_add_0 in Hit.
  destruct Hit as (Hl & Hnf).
  apply length_zero_iff_nil in Hl; subst l.
  now rewrite app_nil_r, Nat.add_0_r.
}
destruct l as [| j]. {
  now cbn; rewrite app_nil_r, Nat.add_0_r.
}
cbn in Hit.
apply Nat.succ_le_mono in Hit.
rewrite if_eqb_eq_dec in Hit |-*.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  subst j.
  replace (seq 0 i ++ i :: l) with (seq 0 (S i) ++ l). 2: {
    now rewrite seq_S, <- app_assoc.
  }
  rewrite List_length_cons, <- Nat.add_succ_comm.
  apply IHit; [ now rewrite seq_S, <- app_assoc | easy ].
} {
  cbn - [ list_swap_elem ].
  rewrite List_length_fold_right by now intros; rewrite comp_length.
  rewrite app_length, seq_length, List_length_cons.
  unfold "°"; cbn - [ seq ].
  remember (ff_app (swap (i + S (length l)) i j)) as f eqn:Hf.
  remember (λ t l, map (ff_app (swap (length l) (fst t) (snd t))) l) as g
    eqn:Hg.
  remember (list_swap_elem 0 (j :: l) 0 (j - i)) as la eqn:Hla.
  move g before f; move la before g.
  assert (Hilj : i < j). {
    apply Nat.nle_gt.
    intros Hc.
    destruct Hp as (Hpp, Hpl).
    specialize (NoDup_nat _ Hpl i j) as H2.
    rewrite app_length, seq_length in H2.
    cbn in H2.
    assert (H : i < i + S (length l)) by flia.
    specialize (H2 H); clear H.
    assert (H : j < i + S (length l)) by flia Hc.
    specialize (H2 H); clear H.
    unfold ff_app in H2.
    rewrite app_nth2 in H2; [ | now rewrite seq_length; unfold ge ].
    rewrite seq_length, Nat.sub_diag in H2; cbn in H2.
    rewrite app_nth1 in H2; [ | rewrite seq_length; flia Hij Hc ].
    rewrite seq_nth in H2; [ | flia Hij Hc ].
    now specialize (H2 eq_refl).
  }
  move Hilj before Hij.
(*
(* option 1 *)
  specialize (IHit (j :: l) i Hp) as H1.
  rewrite List_length_cons in H1.
  unfold "°" in H1.
  rewrite <- Hg in H1.
  assert (H : S (length l) + nb_nfit i (j :: l) ≤ it). {
    rewrite Nat.add_succ_comm.
    cbn; rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec i j) as [H| H]; [ easy | clear H ].
(* ne fontionne pas *)
...
(* option 2 *)
*)
  assert (Hpa : is_permut_list (seq 0 i ++ la)). {
    rewrite Hla.
    now apply app_seq_swap_is_permut_list.
  }
  specialize (IHit la i) as H1.
  unfold "°" in H1.
  rewrite <- Hg in H1.
  specialize (H1 Hpa).
  assert (H : length la + nb_nfit i la ≤ it). {
    rewrite Hla, list_swap_elem_length, List_length_cons.
    rewrite Nat.add_succ_comm.
    etransitivity; [ | apply Hit ].
    apply Nat.add_le_mono_l.
    apply -> Nat.succ_le_mono.
    cbn - [ nth ].
    rewrite <- seq_shift, map_map.
    erewrite map_ext_in. 2: {
      intros u Hu.
      replace (j - i) with (S (j - S i)) by flia Hilj.
      unfold transposition.
      cbn - [ nth ].
      replace (nth _ _ _) with (if u =? j - S i then j else nth u l 0). 2: {
        do 2 rewrite if_eqb_eq_dec.
        now destruct (Nat.eq_dec u (j - S i)).
      }
      easy.
    }
    enough (H :
      nb_nfit (S i)
        (map (λ u, if u =? j - S i then j else nth u l 0)
           (seq 0 (length l))) <
      nb_nfit (S i) l). {
      rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec i (nth _ _ _)) as [H2| H2]; [ flia H | easy ].
    }
    assert (Hji : j - S i < length l). {
      destruct Hp as (Hpp, Hpl).
      specialize (Hpp j) as H2.
      rewrite app_length, seq_length in H2.
      assert (H : j ∈ seq 0 i ++ j :: l). {
        now apply in_or_app; right; left.
      }
      specialize (H2 H); clear H; cbn in H2.
      flia H2 Hilj.
    }
    remember (λ u, if _ =? _ then _ else _) as f1 eqn:Hf1.
    remember (length l) as len eqn:Hlen.
    rewrite List_map_nth_seq with (la := l) (d := 0).
    subst len f1.
    rewrite List_seq_cut with (i := j - S i); [ | now apply in_seq ].
    rewrite Nat.sub_0_r; cbn.
    do 2 rewrite map_app.
    cbn; rewrite Nat.eqb_refl.
    erewrite map_ext_in. 2: {
      intros k Hk.
      apply in_seq in Hk.
      rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec k (j - S i)) as [H| H]; [ flia Hk H | ].
      easy.
    }
    do 2 rewrite nb_nfit_app.
    apply Nat.add_lt_mono_l.
    rewrite List_map_seq_length.
    rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
    cbn; rewrite Nat.eqb_refl, Nat.add_0_l.
    erewrite map_ext_in. 2: {
      intros k Hk.
      apply in_seq in Hk.
      rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec k (j - S i)) as [H| H]; [ flia Hk H | ].
      easy.
    }
    rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec j (nth (j - S i) l 0)) as [Hjji| Hjji]; [ | flia ].
    exfalso.
    destruct Hp as (Hpp, Hpl).
    apply NoDup_app_iff in Hpl.
    destruct Hpl as (Hil & Hjl & Hnjl).
    apply NoDup_cons_iff in Hjl.
    destruct Hjl as (H2, H3); apply H2.
    rewrite Hjji.
    apply nth_In; flia Hji.
  }
  specialize (H1 H); clear H.
  clear IHit.
  subst f.
  rewrite fold_comp_list.
  replace (length la) with (S (length l)) in H1. 2: {
    rewrite Hla.
    now rewrite list_swap_elem_length.
  }
...
  rewrite transp_loop_app_seq in H1 |-*.
...
assert (pour_rigoler : transp_loop it (S i) la = (i, i + j) :: transp_loop it (S i) (j :: l)). {
  induction it. {
    cbn in H1 |-*.
    specialize (nb_fit_ub (S i) l) as H2.
    flia Hit H2.
  }
  cbn - [ list_swap_elem "=?" ].
  destruct la as [| k]; [ easy | ].
  cbn - [ nth "=?" ] in Hla.
  unfold transposition in Hla at 1.
  rewrite Nat.eqb_refl in Hla.
  remember (nth (j - i) (j :: l) 0) as x.
  injection Hla; clear Hla; intros Hk Hla.
  subst x k.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (S i) (nth (j - i) (j :: l) 0)) as [Hsij| Hsij]. {
    destruct
...
  rewrite <- H1; clear H1.
  unfold "°"; cbn - [ seq ].
  rewrite Nat.add_succ_r.
  remember (ff_app (swap (S (i + length l)) i j)) as f eqn:Hf.
  remember (λ t l, map (ff_app (swap (length l) (fst t) (snd t))) l) as g
    eqn:Hg.
  remember (list_swap_elem 0 (j :: l) 0 (j - i)) as la eqn:Hla.
  move g before f; move la before g.
  move Hij at bottom.
  rewrite transp_loop_app_seq.
  destruct i. {
    cbn.
    rewrite Nat.add_0_l in Hf.
    rewrite Nat.sub_0_r in Hla.
    rewrite Nat.add_0_r.
    destruct j; [ easy | clear Hij ].
    cbn in Hp.
    assert (Hlaz : nth 0 la 0 = nth j l 0) by now rewrite Hla.
    assert (Hlaj : nth (S j) la 0 = S j). {
      rewrite Hla.
      cbn - [ nth ].
      rewrite List_nth_succ_cons.
      assert (H1 : j < length l). {
        destruct Hp as (Hpp, Hpl).
        specialize (Hpp (S j) (or_introl eq_refl)).
        cbn in Hpp.
        now apply Nat.succ_lt_mono in Hpp.
      }
      rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
      rewrite seq_nth; [ | easy ].
      now cbn; rewrite Nat.eqb_refl.
    }
    (* "S j" is at its place in "la"; therefore not appearing in the
       result of transp_loop *)
...
Theorem glop : ∀ it la i j k,
  it = length la + length la - nb_fit i la
  → nth j la 0 = i + j
  → (i + j, k) ∉ transp_loop it i la.
Proof.
intros * Hit Hi Him.
revert i j k la Hit Hi Him.
induction it; intros; [ easy | cbn in Him ].
destruct la as [| n]; [ easy | ].
rewrite if_eqb_eq_dec in Him.
destruct (Nat.eq_dec i n) as [Hin| Hin]. {
  subst n.
  cbn in Hit.
  rewrite Nat.eqb_refl in Hit.
  cbn in Hit.
  rewrite Nat.add_succ_r in Hit.
  rewrite Nat.sub_succ_l in Hit. 2: {
    specialize (nb_fit_ub (S i) la) as H1.
    flia H1.
  }
  apply Nat.succ_inj in Hit.
  destruct j. {
    clear Hi.
    rewrite Nat.add_0_r in Him.
...
  apply (IHit _ _ k _ Hit).
  clear IHit.
  revert i j k la Hi Him.
  induction it; intros; [ easy | ].
  cbn; rewrite Nat.eqb_refl.
  cbn - [ list_swap_elem "=?" ] in Him.
  destruct la as [| i1]; [ easy | ].
  rewrite if_eqb_eq_dec in Him.
  destruct (Nat.eq_dec (S i) i1) as [Hi1| Hi1]. {
    subst i1.
    destruct j. {
      clear Hi.
      rewrite Nat.add_0_r in Him |-*.
      destruct it; [ easy | ].
      cbn in Him |-*.
      rewrite Nat.eqb_refl.
      destruct la as [| j]; [ easy | ].
      destruct j. {
        cbn - [ list_swap_elem "=?" ] in Him.
        destruct Him as [Him| Him]. {
          injection Him; clear Him; intros H1 H2.
          flia H2.
        }
        now rewrite list_swap_elem_id in Him.
      }
      destruct j. {
        destruct Him as [Him| Him]. {
          injection Him; clear Him; intros H1 H2.
          flia H2.
        }
        now rewrite list_swap_elem_id in Him.
      }
      rewrite if_eqb_eq_dec in Him.
      destruct (Nat.eq_dec i j) as [Hij| Hij]. {
        subst j.
...
(* contre-exemple *)
Compute (
  let la := [3;2;7;5] in
  let j := 1 in
  let i := 1 in
  let k := 7 in
  let it := 4 in
  nth j la 0 = i + j
  → (i, k) ∉ transp_loop it i la
).
Compute (transp_loop 10 0 [0;3;2;7;5]).
...
03275
0723500
0023507
...
revert i j k la Hi Him.
induction it; intros; [ easy | cbn in Him ].
destruct la as [| n]; [ easy | ].
rewrite if_eqb_eq_dec in Him.
destruct (Nat.eq_dec i n) as [Hin| Hin]. {
  subst n.
...
(**)
  apply (IHit _ _ k _ Hi).
  clear IHit.
  revert i j k la Hi Him.
  induction it; intros; [ easy | ].
  cbn; rewrite Nat.eqb_refl.
  cbn - [ list_swap_elem "=?" ] in Him.
  destruct la as [| i1]; [ easy | ].
  rewrite if_eqb_eq_dec in Him.
  destruct (Nat.eq_dec (S i) i1) as [Hi1| Hi1]. {
    subst i1.
    apply IHit. {
      destruct it; [ easy | ].
      cbn - [ list_swap_elem "=?" ] in Him.
      destruct la as [| i1]; [ easy | ].
      rewrite if_eqb_eq_dec in Him.
      destruct (Nat.eq_dec (S (S i)) i1) as [Hi1| Hi1]. {
        subst i1.
...
      destruct it; [ easy | ].
      cbn - [ list_swap_elem "=?" ] in Him.
      destruct la as [| i1]; [ easy | ].
      rewrite if_eqb_eq_dec in Him.
      destruct (Nat.eq_dec (S (S (S i))) i1) as [Hi1| Hi1]. {
        subst i1.
...
  specialize in_transp_loop_bounds as H1.
  specialize (H1 it (S i) (j, k) la Him).
  cbn in H1.
  destruct j; [ easy | ].
  rewrite List_nth_succ_cons in Hi.
  specialize (IHit i (S j) k (i :: la)) as H2.
  rewrite List_nth_succ_cons in H2.
  specialize (H2 Hi).
  destruct it; [ easy | ].
  cbn in H2; rewrite Nat.eqb_refl in H2.
  destruct it. {
    cbn - [ list_swap_elem "=?" ] in Him, H2.
    clear H2.
    destruct la as [| i1]; [ easy | ].
    rewrite if_eqb_eq_dec in Him.
    destruct (Nat.eq_dec (S i) i1) as [Hi1| Hi1]; [ easy | ].
    destruct Him as [Him| Him]; [ | easy ].
    injection Him; clear Him; intros Hk Hij; subst i1 j.
    apply Nat.neq_sym in Hi1; clear H1.
    destruct i; [ easy | ].
    cbn in Hi.
...
(*
Search transp_loop.
Theorem glop :
  (i, j) ∈ transp_loop it k la
  → nth i la 0 ≠ k + i.
...
  specialize (IHit _ _ k _ Hi) as H2.
...
*)
  apply (IHit _ _ k _ Hi).
  apply (IHit i j k (i :: la) Hi).
...
rewrite transp_loop_app_seq in Him.
rewrite transp_loop_app_seq.
rewrite Nat.add_succ_r in Him.
cbn - [ list_swap_elem "=?" ] in Him.
rewrite Nat.eqb_refl in Him.
rewrite transp_loop_app_seq in Him.
...
  destruct it; [ easy | cbn ].
  rewrite Nat.eqb_refl.
  cbn - [ list_swap_elem "=?" ] in Him.
  destruct la as [| n]; [ easy | ].
  rewrite if_eqb_eq_dec in Him.
  destruct (Nat.eq_dec (S i) n) as [Hsin| Hsin]. {
    subst n.
Search transp_loop.
...
Theorem glop : ∀ it i j l,
  j ∈ map fst (transp_loop it i l)
  → i ≤ j ≤ i + length l.
Proof.
intros * Hj.
revert i j l Hj.
induction it; intros; [ easy | cbn in Hj ].
destruct l as [| k]; [ easy | ].
rewrite if_eqb_eq_dec in Hj.
destruct (Nat.eq_dec i k) as [Hik| Hik]. {
  subst k.
...
  apply IHit.
  destruct it; [ easy | ].
  cbn in Hj |-*.
  rewrite Nat.eqb_refl.
  destruct l as [| k]; [ easy | ].
  destruct k. {
    cbn - [ list_swap_elem transp_loop ] in Hj.
    destruct Hj as [Hj| Hj]. {
      subst j.
      destruct it. {
        cbn.
...
Theorem glop : ∀ it i l,
  transp_loop it (S i) l = transp_loop (S it) i (i :: l).
Proof.
intros.
now cbn; rewrite Nat.eqb_refl.
Qed.
rewrite glop in Hj.
cbn - [ list_swap_elem ] in Hj.
rewrite Nat.eqb_refl in Hj.
apply IHit in Hj.
Inspect 2.
...
now rewrite glop in Hj.
...
  destruct it; [ easy | ].
  cbn in Hj |-*.
  rewrite Nat.eqb_refl.
  destruct l as [| k]; [ easy | cbn ].
  destruct k. {
    cbn in Hj.
...
specialize (glop it (S i) j la Him) as H1.
destruct H1 as (H1, H2).
destruct j; [ easy | ].
cbn in H2.
apply Nat.succ_le_mono in H1.
apply Nat.succ_le_mono in H2.
cbn in Hi.
destruct la as [| k]. {
  cbn in Hi.
  now rewrite match_id, Nat.add_succ_r in Hi.
}
cbn in H2.

Search transp_loop.
Search transp_list.
...
  destruct j. {
    clear Hi.
...
    destruct it; [ easy | cbn in Him ].
    destruct la as [| i1]; [ easy | ].
    destruct i1. {
      cbn in Him.
      destruct Him as [Him| Him]; [ easy | ].
...
  specialize (IHit i j (i :: la) Hi) as H1.
...
    assert (Hsj : ∀ ij, ij ∈ transp_loop it 0 la → S j ∉ [fst ij; snd ij]). {
      intros * Hij Hn.
      destruct Hn as [Hn| Hn]. {
        rewrite Hla in Hij.
        clear - Hij Hn.
        revert j l ij Hij Hn.
        induction it; intros; [ easy | ].
        cbn - [ list_swap_elem "=?" ] in Hij.
        remember (list_swap_elem 0 (S j :: l) 0 (S j)) as la eqn:Hla.
        symmetry in Hla.
        destruct la as [| i]; [ easy | ].
        rewrite if_eqb_eq_dec in Hij.
        destruct (Nat.eq_dec 0 i) as [Hiz| Hiz]. {
          subst i.
          cbn in Hla.
          injection Hla; clear Hla; intros Hla H1.
...
(*
                                   j
     l           |   |   |   |   | * |   |   |   |   |
     la      | * |   |   |   |   |S j|   |   |   |   |
  S j :: l   |S j|   |   |   |   | * |   |   |   |   |

Quand on applique g à partir de "la", ça ne modifie pas ce qu'il y a en "S j"
car "la(S j)=S j" mais ce qu'il y a en 0 ("*") peut se retrouver ailleurs,
mettons en "k".
  Quand on applique g à partir de "S j :: l", ça ne modifie pas non plus donc
ce qu'il y a en "S j" (en l'occurrence "*") mais ce qu'il y a en 0 ("S j")
peut se retrouver ailleurs, en l'occurrence en "k".
                                       S j          k
 fold     la      |lk |   |   |   |   |S j|   |   | * |   |
 fold  S j :: l   |lk |   |   |   |   | * |   |   |S j|   |
Donc je pense que ça ne devrait pas marcher.
*)
(* ah, pourtant, si, ça a l'air de marcher ci-dessous; mais bon, c'est sur un exemple
   j'échoue à trouver un contre-exemple *)
...
subst f g.
Compute (
  let l := [2;3;4;0;5] in
  let j := 0 in
  let la := list_swap_elem 0 (S j :: l) 0 (S j) in
  let it := 42 in
  map (ff_app (swap (S (length l)) 0 (S j)))
    (fold_right (λ (t : nat * nat) (l0 : list nat), map (ff_app (swap (length l0) (fst t) (snd t))) l0)
       (S j :: l) (transp_loop it 0 (list_swap_elem 0 (S j :: l) 0 (S j)))) =
  fold_right (λ (t : nat * nat) (l0 : list nat), map (ff_app (swap (length l0) (fst t) (snd t))) l0)
    (list_swap_elem 0 (S j :: l) 0 (S j)) (transp_loop it 0 (list_swap_elem 0 (S j :: l) 0 (S j)))
).
...
    assert (H : la = nth j l 0 :: replace_at j l (S j)). {
      rewrite Hla.
      unfold list_swap_elem.
      cbn - [ nth ].
      f_equal.
      destruct j. {
        cbn - [ nth ].
        destruct l as [| a]. {
          destruct Hp as (Hpp, Hpl).
          specialize (Hpp 1 (or_introl eq_refl)).
          cbn in Hpp; flia Hpp.
        }
        cbn - [ nth ]; f_equal.
        erewrite map_ext_in. 2: {
          intros k Hk.
          apply in_seq in Hk.
          unfold transposition; cbn.
          do 2 rewrite if_eqb_eq_dec.
          destruct (Nat.eq_dec k 0) as [H| H]; [ flia Hk H | clear H ].
          destruct (Nat.eq_dec k 1) as [H| H]; [ flia Hk H | clear H ].
          replace k with (S (S (k - 2))) at 1 by flia Hk.
          easy.
        }
        clear.
        remember 2 as sta; clear Heqsta.
        revert sta.
        induction l as [| a]; intros; [ easy | ].
        cbn - [ nth ].
        rewrite Nat.sub_diag; f_equal.
        symmetry.
        rewrite <- IHl with (sta := S sta) at 1.
        apply map_ext_in.
        intros i Hi.
        apply in_seq in Hi.
        now replace (i - sta) with (S (i - S sta)) by flia Hi.
      }
...
  destruct it. {
    cbn in Hit.
    specialize (nb_fit_ub (S i) l) as H1.
    rewrite <- Hit in H1.
    flia H1.
  }
  destruct it. {
    cbn in Hit.
    specialize (nb_fit_ub (S i) l) as H1.
    rewrite Nat.add_succ_r in Hit.
    apply Nat.succ_inj in Hit.
    rewrite <- Hit in H1.
    destruct l; [ | cbn in H1; flia H1 ].
    destruct Hp as (Hpp, Hpl).
    rewrite app_length, seq_length in Hpp.
    cbn in Hpp.
    specialize (Hpp j) as H2.
    assert (H : j ∈ seq 0 i ++ [j]). {
      apply in_app_iff.
      now right; left.
    }
    specialize (H2 H); clear H.
    specialize (NoDup_nat _ Hpl i j) as H3.
    rewrite app_length, seq_length in H3.
    cbn in H3.
    assert (H : i < i + 1) by flia.
    specialize (H3 H H2); clear H.
    unfold ff_app in H3.
    rewrite app_nth2 in H3; [ | now rewrite seq_length; unfold ge ].
    rewrite seq_length, Nat.sub_diag in H3; cbn in H3.
    rewrite app_nth1 in H3; [ | rewrite seq_length; flia Hij H2 ].
    rewrite seq_nth in H3; [ | flia Hij H2 ].
    now specialize (H3 eq_refl).
  }
...

Theorem permut_eq_iter_list_transp_loop : ∀ l it i,
  is_permut_list (seq 0 i ++ l)
  → length l + length l = it + nb_fit i l
  → seq 0 i ++ l =
    fold_left (λ l t, swap (length l) (fst t) (snd t) ° l)
      (transp_loop it i l) (seq 0 (i + length l)).
Proof.
(*
intros * Hp Hit.
rewrite seq_app; cbn.
symmetry.
rewrite <- (rev_involutive (transp_loop _ _ _)).
...
apply fold_left_invol_rev. {
  intros la t.
  rewrite comp_length.
  apply List_eq_iff.
  split; [ now do 2 rewrite comp_length | ].
  intros d j.
  unfold "°"; cbn.
  destruct (lt_dec j (length la)) as [Hjl| Hjl]. 2: {
    apply Nat.nlt_ge in Hjl.
    rewrite nth_overflow; [ | now do 2 rewrite map_length ].
    now rewrite nth_overflow.
  }
  rewrite map_map.
  rewrite (List_map_nth' 0); [ | easy ].
  unfold ff_app.
  symmetry.
  rewrite nth_indep with (d' := 0); [ | easy ].
  unfold swap, list_swap_elem.
  rewrite seq_length.
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length.
    rewrite (List_map_nth' 0). 2: {
      rewrite seq_length.
...
unfold swap.
unfold list_swap_elem.
rewrite seq_length.
rewrite <- list_comp_assoc.
  specialize swap_length as H1.
  specialize (H1 (length l) (fst t) (snd t)).
...
*)
intros * Hp Hit.
revert l i Hp Hit.
induction it; intros; cbn. {
  cbn in Hit.
  rewrite seq_app; f_equal; cbn.
  specialize (nb_fit_ub i l) as H1.
  rewrite <- Hit in H1.
  destruct l as [| j]. {
    cbn.
    rewrite app_nil_r, seq_length.
    rewrite swap_id.
    symmetry; apply comp_1_r, seq_length.
  }
  cbn in H1; flia H1.
}
destruct l as [| j]. {
  now cbn; rewrite app_nil_r, Nat.add_0_r.
}
cbn in Hit.
apply Nat.succ_inj in Hit.
rewrite if_eqb_eq_dec in Hit |-*.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  subst j.
  replace (seq 0 i ++ i :: l) with (seq 0 (S i) ++ l). 2: {
    now rewrite seq_S, <- app_assoc.
  }
  rewrite List_length_cons, <- Nat.add_succ_comm.
  apply IHit; [ now rewrite seq_S, <- app_assoc | ].
  cbn in Hit.
  do 2 rewrite Nat.add_succ_r in Hit.
  now apply Nat.succ_inj in Hit.
} {
(*
  specialize (IHit (map (λ k, k - i) (j :: l)) 0) as H1.
  rewrite map_length in H1.
  cbn in H1.
  remember (j - i) as k eqn:Hk; symmetry in Hk.
  destruct k. {
    (* should work since it contradicts Hij Hk and Hp *)
*)
  cbn - [ list_swap_elem ].
  rewrite seq_length.
  rewrite comp_1_r; [ | now rewrite swap_length ].
(**)
  specialize (IHit ((list_swap_elem 0 (j :: l) 0 (j - i))) i) as H1.
  rewrite list_swap_elem_length in H1.
  rewrite List_length_cons in H1.
  assert
    (H : is_permut_list (seq 0 i ++ list_swap_elem 0 (j :: l) 0 (j - i))). {
    admit.
  }
  specialize (H1 H); clear H.
  assert
    (H :
       S (length l) + S (length l) =
       it + nb_fit i (list_swap_elem 0 (j :: l) 0 (j - i))). {
    admit.
  }
  specialize (H1 H); clear H.
...
  rewrite IHit; [ | easy | ]. 2: {
    cbn.
    rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec i j) as [H| H]; [ easy | clear H ].
(* et c'est mort *)
...
  cbn - [ list_swap_elem ].
  rewrite seq_length.
  rewrite comp_1_r; [ | now rewrite swap_length ].
...
  unfold swap at 2.
  specialize (IHit (j :: l) i Hp) as H1.
  rewrite List_length_cons in H1.
  cbn in H1.
...
  destruct (Nat.eq_dec (it + nb_fit (S i) l) (length l)) as [Hil| Hil]. {
    apply IHit; [ now rewrite seq_S, <- app_assoc | ].
...
  apply IHit; [ now rewrite seq_S, <- app_assoc | ].
...
  destruct (Nat.eq_dec (it + nb_fit (S i) l) (length l)) as [Hil| Hil]. {
    apply IHit; [ now rewrite seq_S, <- app_assoc | easy ].
  }
...
  destruct (Nat.eq_dec (2 * (S i + length l)) (S it)) as [Hilt| Hilt]. 2: {
    apply IHit; [ now rewrite seq_S, <- app_assoc | ].
    flia Hit Hilt.
  }
...

Theorem permut_eq_iter_list_transp_loop : ∀ l it i,
  is_permut_list (seq 0 i ++ l)
  → 2 * (i + length l) ≤ it
  → seq 0 i ++ l =
    fold_left (λ l t, swap (length l) (fst t) (snd t) ° l)
      (transp_loop it i l) (seq 0 (i + length l)).
Proof.
intros * Hp Hit.
revert l i Hp Hit.
induction it; intros; cbn. {
  apply Nat.le_0_r in Hit.
  apply Nat.eq_mul_0 in Hit.
  destruct Hit as [Hit| Hit]; [ easy | ].
  apply Nat.eq_add_0 in Hit.
  destruct Hit as (Hi, Hl).
  now apply length_zero_iff_nil in Hl; subst i l.
}
destruct l as [| j]. {
  now rewrite app_nil_r, Nat.add_0_r.
}
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  subst j.
  replace (seq 0 i ++ i :: l) with (seq 0 (S i) ++ l). 2: {
    now rewrite seq_S, <- app_assoc.
  }
  rewrite List_length_cons, <- Nat.add_succ_comm in Hit |-*.
  destruct (Nat.eq_dec (2 * (S i + length l)) (S it)) as [Hilt| Hilt]. 2: {
    apply IHit; [ now rewrite seq_S, <- app_assoc | ].
    flia Hit Hilt.
  }
Print transp_loop.
...
  cbn in Hilt.
  apply Nat.succ_inj in Hilt.
  rewrite Nat.add_0_r, Nat.add_succ_r in Hilt.
  rewrite <- Hilt.
  cbn - [ list_swap_elem nth seq "=?" ].
  destruct l as [| j]. {
    cbn - [ seq ].
    now rewrite app_nil_r, Nat.add_0_r.
  }
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (S i) j) as [Hsij| Hsij]. {
    subst j.
    rewrite List_length_cons.
...
Compute (let p := [0;1;3;2] in
let i := 2 in
let l := skipn i p in
let it' := 2 * (i + length l) in
let it := 3 in
seq 0 i ++ l =
fold_left (λ l t, swap (length l) (fst t) (snd t) ° l)
  (transp_loop it i l) (seq 0 (i + length l))).
Compute (
map (λ p, (p,
  first_non_fix_transp 0 p)) (canon_sym_gr_list_list 4)).
Compute (
map (λ p,
  let i := first_non_fix_transp 0 p in
  let l := skipn i p in
  let it := 2 * (i + length l) in
list_eqb Nat.eqb
  (seq 0 i ++ l)
    (fold_left (λ l t, swap (length l) (fst t) (snd t) ° l)
      (transp_loop it i l) (seq 0 (i + length l))))
    (canon_sym_gr_list_list 5)).
...
*)

Theorem permut_eq_iter_list_transp : ∀ l,
  is_permut_list l
  → l =
    iter_list (transp_list l)
      (λ l t, swap (length l) (fst t) (snd t) ° l) (seq 0 (length l)).
Proof.
intros * Hp.
destruct (Nat.eq_dec (length l) 0) as [Hlz| Hlz]. {
  now apply length_zero_iff_nil in Hlz; subst l.
}
unfold iter_list.
unfold transp_list, iter_seq, iter_list.
...
specialize permut_eq_iter_list_transp_loop as H1.
specialize (H1 l (2 * length l) 0 Hp (Nat.le_refl _)).
easy.
...
rewrite <- Nat.double_twice; unfold Nat.double.
remember (length l) as n eqn:Hn; symmetry in Hn.
revert l Hp Hn.
induction n; intros. {
  now apply length_zero_iff_nil in Hn.
}
cbn - [ transp_loop ].
...

Theorem collapse_iter_list_transp : ∀ l,
  collapse l =
  iter_list (transp_list (collapse l))
    (λ l t, swap (length l) (fst t) (snd t) ° l) (seq 0 (length l)).
Proof.
intros.
rewrite <- collapse_length.
...
apply permut_eq_iter_list_transp.
apply collapse_is_permut.
...
rewrite collapse_length.
Compute (let p := collapse [2;8;1;7] in
  p =
  iter_list (transp_list p) (λ l t, swap (length p) (fst t) (snd t) ° l)
    (seq 0 (length p))).
Compute (
map (λ p, ((*p,*)
  list_eqb Nat.eqb p
    (iter_list (transp_list p) (λ l t, swap (length p) (fst t) (snd t) ° l)
      (seq 0 (length p))))) (canon_sym_gr_list_list 6)).
Compute (let p := [1;2;3;0;5;4] in
  p =
  iter_list (transp_list p) (λ l t, swap (length p) (fst t) (snd t) ° l)
    (seq 0 (length p))).
Compute (let p := [1;2;3;0;5;4] in transp_list p).
...
[2;1;3;0;5;4]
[3;1;2;0;5;4]
[0;1;2;3;5;4]
...
[1; 2; 3; 0; 5; 4], false);
[2; 0; 3; 1; 5; 4], false);
[2; 3; 1; 0; 5; 4], false);
...
Compute (let p := [1;2;0;4;3] in
  p =
  iter_list (transp_list p) (λ l t, swap (length p) (fst t) (snd t) ° l)
    (seq 0 (length p))).
Compute (let p := [1;2;0;4;3] in transp_list p).
...
[2;1;0;4;3]
[0;1;2;4;3]
[0;1;2;3;4]
...
Compute (
map (λ p,
  collapse p =
  iter_list (transp_list p) (λ l t, swap (length p) (fst t) (snd t) ° l)
    (seq 0 (length p))) (canon_sym_gr_list_list 4)).
*)
...

Theorem map_iter_list_transp_list : ∀ A (d : A) l p,
  is_permut (length l) p
  → map (λ i, nth i l d) p =
    iter_list (transp_list p) (λ l t, list_swap_elem d l (fst t) (snd t)) l.
Proof.
intros * Hp.
Compute (let p := [2;8;1;7] in let d := 0 in
  let A := nat in
(collapse p =
  iter_list (transp_list p) (λ (l0 : list A) (t : nat * nat), list_swap_elem d l0 (fst t) (snd t)) (seq 0 (length p)))).
Compute (let p := [2;8;1;7] in let d := 0 in
  let A := nat in
(collapse p =
  iter_list (transp_list p) (λ (l0 : list A) (t : nat * nat), list_swap_elem d (seq 0 (length p)) (fst t) (snd t) ° l0) (seq 0 (length p)))).
...
Compute (let l := [3;7;8] in let p := [2;0;1] in let d := 0 in
  let A := nat in
((l ° p),
  map (λ i : nat, nth i l d) p =
  l ° iter_list (transp_list p) (λ (l0 : list A) (t : nat * nat), list_swap_elem d (seq 0 (length l)) (fst t) (snd t) ° l0) (seq 0 (length l)))).
Compute (let l := [3;7;8] in let p := [2;0;1] in let d := 0 in
  let A := nat in
((l ° p),
  map (λ i : nat, nth i l d) p =
  l ° iter_list (transp_list p) (λ (l0 : list A) (t : nat * nat), l0 ° list_swap_elem d (seq 0 (length l)) (fst t) (snd t)) (seq 0 (length l)))).
...
Compute (let l := [3;7;8] in let p := [2;0;1] in let d := 0 in
  let A := nat in
((l ° p),
  map (λ i : nat, nth i l d) p =
  iter_list (transp_list p) (λ (l0 : list A) (t : nat * nat), list_swap_elem d l0 (fst t) (snd t)) l)).
(* ah putain, merde, c'est pas bon *)
Compute (let l := [3;7;8] in
  (l ° [2;0;1], list_swap_elem 0 (list_swap_elem 0 l 0 1) 1 2)).
...
Compute (let l := [3;7;8] in let p := [2;0;1] in let d := 0 in
  let A := nat in
  (p, transp_list p)).
...
     = ([2; 0; 1], [(0, 1); (1, 2)])
...

Theorem list_list_select_rows_with_permut_transp : ∀ n ll p,
  (length (hd [] ll) = 0 → n = 0)
  → (∀ l, l ∈ ll → length l = n)
  → length ll = n
  → is_permut n p
  → list_list_select_rows p ll =
    iter_list (transp_list p) (λ ll t, list_swap_elem [] ll (fst t) (snd t))
      ll.
Proof.
intros * Hcr Hc Hr Hp.
...
specialize map_iter_list_transp_list as H1.
specialize (H1 (list T) []).
specialize (H1 ll p).
rewrite <- H1.
assert (list_list_select_rows p ll = map (λ i, nth i ll []) p). {
  unfold list_list_select_rows.
  apply map_ext_in.
  intros i Hi.
  remember (nth i ll []) as la eqn:Hla.
  rewrite Hr.
  replace n with (length la). {
    now rewrite <- List_map_nth_seq.
  }
  rewrite Hla.
  apply Hc.
  apply nth_In.
  rewrite Hr.
  destruct Hp as (Hpp, Hpl).
  rewrite <- Hpl.
  now apply Hpp.
}
easy.
*)
...
revert ll p Hcr Hc Hr Hp.
induction n; intros. {
  destruct Hp as (Hpp, Hpl).
  apply length_zero_iff_nil in Hpl; subst p.
  now apply length_zero_iff_nil in Hr; subst ll.
}
specialize (permut_without_highest Hp) as H1.
destruct H1 as (i & Hip & Hin & Hpi).
assert (Hi : i < S n). {
  destruct Hpi as (Hpp, Hpl).
  rewrite butn_length in Hpl.
  apply Nat.ltb_lt in Hip; rewrite Hip in Hpl.
  apply Nat.ltb_lt in Hip; cbn in Hpl.
  rewrite <- Hpl.
  rewrite <- Nat.sub_succ_l; [ | flia Hip ].
  now rewrite Nat_sub_succ_1.
}
assert (Hpn : length p = S n). {
  destruct Hpi as (Hpp, Hpl).
  rewrite butn_length in Hpl.
  apply Nat.ltb_lt in Hip; rewrite Hip in Hpl.
  apply Nat.ltb_lt in Hip; cbn in Hpl.
  rewrite <- Hpl.
  rewrite <- Nat.sub_succ_l; [ | flia Hip ].
  now rewrite Nat_sub_succ_1.
}
assert (Hkj :
  ∀ k,
  k ≤ n
  → let j := ff_app (bsort_rank Nat.leb p) k in
    let q := collapse (butn j p) in
    list_list_select_rows q (map (butn k) (butn k ll)) =
      iter_list (transp_list q)
         (λ ll t, list_swap_elem [] ll (fst t) (snd t))
         (map (butn k) (butn k ll))). {
  intros * Hk *.
  specialize (IHn (map (butn k) (butn k ll)) q) as H2.
  rewrite map_length, butn_length, Hr in H2.
  assert (H : length (hd [] (map (butn k) (butn k ll))) = 0 → n = 0). {
    intros H.
    apply length_zero_iff_nil in H.
    destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ easy | ].
    rewrite List_map_hd with (a := []) in H. 2: {
      rewrite butn_length, Hr.
      apply Nat.lt_succ_r, Nat.ltb_lt in Hk.
      rewrite Hk; cbn.
      apply Nat.ltb_lt in Hk.
      rewrite Nat.sub_0_r.
      now apply Nat.neq_0_lt_0.
    }
    destruct ll as [| la]; [ easy | ].
    cbn in Hcr.
    destruct la as [| a]; [ now specialize (Hcr eq_refl) | ].
    cbn in Hr.
    specialize (Hc (a :: la) (or_introl eq_refl)) as H1.
    cbn in H1.
    apply Nat.succ_inj in Hr, H1.
    move H1 before Hr.
    destruct ll as [| lb]; [ easy | ].
    cbn in Hr.
    destruct lb as [| b]. {
      now specialize (Hc _ (or_intror (or_introl eq_refl))).
    }
    destruct k; [ | easy ].
    cbn in H; subst lb.
    specialize (Hc _ (or_intror (or_introl eq_refl))) as H3.
    cbn in H3.
    now destruct n.
  }
  specialize (H2 H); clear H.
  assert (H : ∀ l, l ∈ map (butn k) (butn k ll) → length l = n). {
    intros l Hl.
    apply in_map_iff in Hl.
    destruct Hl as (la & Hlal & Hla).
    rewrite <- Hlal.
    rewrite butn_length.
    apply in_butn in Hla.
    specialize (Hc _ Hla) as H1; rewrite H1.
    apply Nat.lt_succ_r, Nat.ltb_lt in Hk.
    rewrite Hk; cbn.
    now rewrite Nat.sub_0_r.
  }
  specialize (H2 H); clear H.
  apply Nat.lt_succ_r, Nat.ltb_lt in Hk.
  rewrite Hk, Nat_sub_succ_1 in H2.
  specialize (H2 eq_refl).
  assert (H : is_permut n q). {
    unfold q.
    specialize collapse_is_permut as H3.
    specialize (H3 (butn j p)).
    rewrite butn_length, Hpn in H3.
    assert (H : j < S n). {
      unfold j, ff_app.
      rewrite <- Hpn.
      apply bsort_rank_ub.
      now intros H; rewrite H in Hip.
    }
    apply Nat.ltb_lt in H.
    now rewrite H, Nat_sub_succ_1 in H3.
  }
  now specialize (H2 H).
}
...
specialize (Hkj n (le_refl _)) as H1.
cbn in H1.
rewrite permut_collapse in H1. 2: {
  apply butn_is_permut_list; [ now destruct Hp | ].
  now rewrite Hpn, Nat_sub_succ_1.
}
rewrite <- Hin in H1.
rewrite fold_ff_app in H1.
rewrite permut_bsort_permut in H1; [ | now destruct Hp | now rewrite Hpn ].
unfold ff_app in H1.
rewrite Hin in H1.
...
rewrite mat_select_rows_butn_subm in H1;
  [ | easy | | easy | easy | easy | easy ]. 2: {
  now destruct Hp as ((Hpa, Hpd), Hpl).
}
specialize (Hkj 0 (Nat.le_0_l _)) as H2.
cbn in H2.
set (j := ff_app (bsort_rank Nat.leb p) 0) in H2.
set (q := collapse (butn j p)) in H2.
...
...
intros * Hcr Hc Hr Hp.
subst n.
unfold iter_list, list_list_select_rows.
revert p Hp.
induction ll as [| la]; intros. {
  destruct Hp as (Hpp, Hpl).
  apply length_zero_iff_nil in Hpl; subst p; cbn.
  unfold transp_list; cbn.
  now unfold iter_seq, iter_list.
}
rewrite List_length_cons, seq_S.
cbn - [ nth ].
rewrite map_app.
...

Theorem mat_select_rows_with_permut_transp : ∀ n (M : matrix T) p,
  is_square_matrix M = true
  → mat_nrows M = n
  → is_permut n p
  → mat_select_rows p M =
      iter_list (transp_list p) (λ M t, mat_swap_rows (fst t) (snd t) M) M.
Proof.
intros * Hsm Hr Hp.
unfold mat_select_rows.
...
rewrite (@list_list_select_rows_with_permut_transp n); try easy; cycle 1. {
  intros Hc.
  apply is_scm_mat_iff in Hsm.
  rewrite Hr in Hsm.
  now apply Hsm.
} {
  apply is_scm_mat_iff in Hsm.
  rewrite Hr in Hsm.
  now apply Hsm.
}
unfold mat_swap_rows.
unfold iter_list.
specialize fold_left_mk_mat as H1.
specialize (H1 (nat * nat)%type M).
specialize (H1 (λ ll t, list_swap_elem [] ll (fst t) (snd t))).
symmetry.
apply H1.
...
intros * Hsm Hr Hp.
(*
Require Import RnglAlg.Zrl.
Require Import ZArith.
Open Scope Z_scope.
Compute (let M := mk_mat [[3;2;7];[2;1;8];[6;6;5]] in
map (λ p,
  mat_select_rows p M =
    iter_list (transp_list p) (λ M t, mat_swap_rows (fst t) (snd t) M) M
) (canon_sym_gr_list_list 3)).
ça a l'air juste
*)
revert M p Hsm Hr Hp.
induction n; intros; cbn. {
  destruct Hp as (Hpp, Hpl).
  apply length_zero_iff_nil in Hpl; subst p; cbn.
  unfold mat_select_rows, transp_list; cbn.
  unfold iter_seq, iter_list; cbn.
  destruct M as (ll); cbn in Hr.
  now apply length_zero_iff_nil in Hr; subst ll.
}
specialize (permut_without_highest Hp) as H1.
destruct H1 as (i & Hip & Hin & Hpi).
assert (Hi : i < S n). {
  destruct Hpi as (Hpp, Hpl).
  rewrite butn_length in Hpl.
  apply Nat.ltb_lt in Hip; rewrite Hip in Hpl.
  apply Nat.ltb_lt in Hip; cbn in Hpl.
  rewrite <- Hpl.
  rewrite <- Nat.sub_succ_l; [ | flia Hip ].
  now rewrite Nat_sub_succ_1.
}
assert (Hpn : length p = S n). {
  destruct Hpi as (Hpp, Hpl).
  rewrite butn_length in Hpl.
  apply Nat.ltb_lt in Hip; rewrite Hip in Hpl.
  apply Nat.ltb_lt in Hip; cbn in Hpl.
  rewrite <- Hpl.
  rewrite <- Nat.sub_succ_l; [ | flia Hip ].
  now rewrite Nat_sub_succ_1.
}
(**)
assert (Hkj :
  ∀ k,
  k ≤ n
  → let j := ff_app (bsort_rank Nat.leb p) k in
    let q := collapse (butn j p) in
    mat_select_rows q (subm k k M) =
      iter_list (transp_list q) (λ M t, mat_swap_rows (fst t) (snd t) M)
         (subm k k M)). {
  intros * Hk *.
  specialize (IHn (subm k k M) q) as H2.
  assert (H : is_square_matrix (subm k k M) = true). {
    apply is_squ_mat_subm; [ flia Hr Hk | flia Hr Hk | easy ].
  }
  specialize (H2 H); clear H.
  assert (H : mat_nrows (subm k k M) = n). {
    rewrite mat_nrows_subm, Hr; cbn.
    apply Nat.leb_le in Hk; rewrite Hk; cbn.
    apply Nat.sub_0_r.
  }
  specialize (H2 H); clear H.
  assert (H : is_permut n q). {
    unfold q.
    specialize collapse_is_permut as H3.
    specialize (H3 (butn j p)).
    rewrite butn_length, Hpn in H3.
    assert (H : j < S n). {
      unfold j, ff_app.
      rewrite <- Hpn.
      apply bsort_rank_ub.
      now intros H; rewrite H in Hip.
    }
    apply Nat.ltb_lt in H.
    now rewrite H, Nat_sub_succ_1 in H3.
  }
  now specialize (H2 H).
}
specialize (Hkj n (le_refl _)) as H1.
cbn in H1.
rewrite permut_collapse in H1. 2: {
  apply butn_is_permut_list; [ now destruct Hp | ].
  now rewrite Hpn, Nat_sub_succ_1.
}
rewrite <- Hin in H1.
rewrite fold_ff_app in H1.
rewrite permut_bsort_permut in H1; [ | now destruct Hp | now rewrite Hpn ].
unfold ff_app in H1.
rewrite Hin in H1.
rewrite mat_select_rows_butn_subm in H1;
  [ | easy | | easy | easy | easy | easy ]. 2: {
  now destruct Hp as ((Hpa, Hpd), Hpl).
}
specialize (Hkj 0 (Nat.le_0_l _)) as H2.
cbn in H2.
set (j := ff_app (bsort_rank Nat.leb p) 0) in H2.
set (q := collapse (butn j p)) in H2.
...
destruct M as (ll).
unfold mat_select_rows.
cbn.
...
Search (collapse (butn _ _)).
Search (collapse (_ ++ _)).
unfold collapse in H2.
Check mat_select_rows_butn_subm.
Print mat_select_rows.
Print mat_select_cols.
About mat_select_rows.
apply matrix_eq.
intros u v Hu Hv.
rewrite mat_select_rows_nrows, Hpn in Hu.
Search (mat_ncols (iter_list _ _ _)).
Search (mat_ncols (fold_left _ _ _)).
...
Theorem sort_rank_butn : ∀ A (ord : A → _) l i,
  bsort_rank ord (butn i l) = butn i (bsort_rank ord l).
Proof.
intros.
destruct l as [| d]; intros; [ now do 2 rewrite butn_nil | ].
unfold bsort_rank at 2.
remember (d :: l) as l' eqn:Hl'.
clear l Hl'; rename l' into l.
Theorem butn_bsort_rank_loop : ∀ ord f lr l i,
  butn i (bsort_rank_loop ord f lr l) = bsort_rank_loop ...
...
Theorem collapse_butn : ∀ l i,
  collapse (butn i l) = butn i (collapse l).
Proof.
unfold collapse.
...
unfold collapse in H2.
Search (mat_select_rows (bsort_rank _ _)).
Check mat_select_rows_butn_subm.
Search (bsort_rank _ (butn _ _)).
Search (bsort_rank _ (_ ++ _)).
...
rewrite mat_select_rows_butn_subm in H2;
  [ | easy | | | | | easy ]; cycle 1. {
  now destruct Hp as ((Hpa, Hpd), Hpl).
} {
...
(*
Abort.
End a.

Section a.
Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).
*)
Definition surm u v row col (M : matrix T) :=
  match row with
  | [] => M
  | d :: _ =>
      mk_mat
        (map
           (λ i,
            map
              (λ j,
               match Nat.compare i u with
               | Lt =>
                   match Nat.compare j v with
                   | Lt => mat_el M i j
                   | Eq => nth i col d
                   | Gt => mat_el M i (j - 1)
                   end
               | Eq => nth j row d
               | Gt =>
                   match Nat.compare j v with
                   | Lt => mat_el M (i - 1) j
                   | Eq => nth i col d
                   | Gt => mat_el M (i - 1) (j - 1)
                   end
               end)
              (seq 0 (length row)))
           (seq 0 (length col)))
  end.
(*
End a.
Require Import RnglAlg.Nrl.
Compute (let M := mk_mat [[1;2;3;4];[5;6;7;8];[9;10;11;12]] in
surm _ 1 2 [13;14;15;16;17] [18;19;20;21] M).
surm _ 0 0 [13;14;15;16;17] [18;19;20;21] M).
...
Print matrix.
*)
Definition mat_row i (M : matrix T) :=
  nth i (mat_list_list M) [].
Definition mat_col j (M : matrix T) :=
  map (λ i, mat_el M i j) (seq 0 (mat_nrows M)).
(*
End a.
Require Import RnglAlg.Nrl.
Compute (let M := mk_mat [[1;2;3;4];[5;6;7;8];[9;10;11;12]] in
mat_col _ 4 M).
*)
Theorem surm_of_subm : ∀ (M : matrix T) i j,
  M = surm i j (mat_row i M) (mat_col j M) (subm i j M).
Proof.
intros.
destruct M as (ll); cbn.
unfold surm.
(* ouais, fait chier *)
...
rewrite (surm_of_subm (mat_select_rows p M) i n).
rewrite H1.
unfold surm.
...

Theorem glop : in_charac_0_field →
  ∀ n A p,
  is_square_matrix A = true
  → mat_nrows A = n
  → is_permut n p
  → det A = (ε p * det (mat_select_rows p A))%F.
Proof.
intros Hif * Hsm Hra Hp.
Print n_transp.
Check determinant_alternating.
...
rewrite mat_select_rows_with_transp.
...
Require Import RnglAlg.Zrl.
Require Import ZArith.
Compute (map (λ p, ε p = if n_transp p mod 2 =? 0 then 1%F else (-1)%F) (canon_sym_gr_list_list 4)).
Compute (map (λ p, Z.eqb (ε p) (if n_transp p mod 2 =? 0 then 1%F else (-1)%F)) (canon_sym_gr_list_list 4)).
Compute (let p := [3;2;0;1] in let n := length p in p = Comp n (t ∈ transp_list p), swap n (fst t) (snd t)).
Compute (map (λ p, let n := length p in p = Comp n (t ∈ transp_list p), swap n (fst t) (snd t)) (canon_sym_gr_list_list 4)).
Compute (map (λ p, let n := length p in list_eqb Nat.eqb p (Comp n (t ∈ transp_list p), swap n (fst t) (snd t))) (canon_sym_gr_list_list 4)).
...
enough (Hpt : p = Comp n (t ∈ transp_list p), swap n (fst t) (snd t)).
rewrite Hpt.
enough
  (Hpε :
   ε (Comp n (t ∈ transp_list p), swap n (fst t) (snd t)) =
   minus_one_pow (length (transp_list p))).
rewrite Hpε.
remember (length (transp_list p)) as m eqn:Hm.
symmetry in Hm.
destruct m. {
  cbn - [ det ]; rewrite rngl_mul_1_l.
  apply length_zero_iff_nil in Hm.
  rewrite Hm.
  unfold iter_list; cbn.
  unfold det; cbn.
  rewrite List_map_seq_length.
  rewrite Hra.
  f_equal.
  unfold mat_select_rows.
  destruct A as (ll); cbn; f_equal.
  cbn in Hra.
  rewrite <- Hra.
  apply List_map_nth_seq.
}
destruct m. {
  unfold iter_list; cbn.
  rewrite map_length.
  remember (transp_list p) as lt eqn:Hlt.
  symmetry in Hlt.
  destruct lt as [| (i, j)]; [ easy | ].
  destruct lt; [| easy ]; cbn.
  clear Hm.
  rewrite comp_length, seq_length.
  unfold iter_list in Hpε; cbn in Hpε.
  rewrite sign_comp in Hpε; [ | easy | ]. 2: {
    rewrite swap_length.
    apply seq_is_permut.
  }
  rewrite comp_1_r; [ | apply swap_length ].
  destruct (lt_dec i n) as [Hin| Hin]. 2: {
    apply Nat.nlt_ge in Hin.
    unfold transp_list in Hlt.
...
    destruct p as [| a]; [ easy | ].

unfold transp_list in Hlt.
Search swap.
unfold swap.
...
  specialize determinant_alternating as H1.
  specialize (H1 Hif A i j).
  assert (H : i ≠ j). {
    intros H; subst j.
    rewrite ε_swap_id, rngl_mul_1_l in Hpε.
    rewrite ε_seq in Hpε.
    apply rngl_sub_move_0_r in Hpε; [ | now destruct Hif ].
    rewrite <- fold_rngl_sub in Hpε; [ | now destruct Hif ].
    rewrite rngl_opp_involutive in Hpε; [ | now destruct Hif ].
    replace (1 + 1)%F with (rngl_of_nat 2) in Hpε. 2: {
      now cbn; rewrite rngl_add_0_r.
    }
    apply eq_rngl_of_nat_0 in Hpε; [ easy | now destruct Hif ].
  }
  specialize (H1 H); clear H.
  rewrite Hra in H1.
...
Search (_ - _ = _)%F.
Require Import ZArith.
Search (_ - _ = 0)%Z.
About rngl_sub_move_0_r.
...
Check fold_det.
...

(* kl is not necessarily in order *)
Theorem det_with_rows : in_charac_0_field →
  ∀ m n A kl,
  mat_nrows A = n
  → mat_ncols A = m
  → is_correct_matrix A = true
  → NoDup kl
  → length kl = m
  → (∀ k, k ∈ kl → k < n)
  → det (mat_select_rows kl A) =
       (ε kl * det (mat_select_rows (bsort Nat.leb kl) A))%F.
Proof.
intros Hif * Hra Hca Ha Hnkl Hklm Hkn.
Check determinant_alternating.
...
intros Hif * Hra Hca Ha Hnkl Hklm Hkn.
(*
Abort.
Require Import RnglAlg.Zrl.
Require Import ZArith.
Open Scope Z_scope.
Compute (let A := mk_mat [[1;2;0];[4;5;6];[7;8;9];[2;5;1]] in
  let kl := [3;1;2]%nat in
  det (mat_select_rows kl A) =
     (ε kl * det (mat_select_rows (bsort Nat.leb kl) A))%Z).
...
*)
rewrite det_is_det_by_canon_permut; try now destruct Hif. 2: {
  apply mat_select_rows_is_square; [ easy | now rewrite Hklm | ].
  intros k Hk; rewrite Hra.
  now apply Hkn.
}
rewrite det_is_det_by_canon_permut; try now destruct Hif. 2: {
  apply mat_select_rows_is_square; [ easy | | ]. {
    rewrite length_bsort.
    congruence.
  }
  intros k Hk; rewrite Hra.
  apply Hkn.
  now apply in_bsort in Hk.
}
unfold det'.
rewrite mat_select_rows_nrows, Hklm.
rewrite mat_select_rows_nrows.
rewrite length_bsort, Hklm.
rewrite rngl_mul_summation_distr_l; [ | now destruct Hif; left ].
erewrite rngl_summation_eq_compat; [ | easy ].
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros k (_, Hk).
  rewrite rngl_mul_assoc.
  rewrite <- ε_collapse_ε; [ | easy ].
  rewrite <- sign_comp; [ | easy | ]. 2: {
    rewrite length_collapse.
    rewrite Hklm.
    apply canon_sym_gr_list_is_permut.
    specialize (fact_neq_0 m) as H.
    flia Hk H.
  }
  easy.
}
cbn - [ mat_el ].
set (p := collapse kl).
(* la formule g, h ci-dessous, je pense qu'elle n'est pas bonne
*)
set (g := λ i,
  canon_sym_gr_list_inv m (bsort_rank Nat.leb p ° canon_sym_gr_list m i)).
(*
set (h := λ i,
  canon_sym_gr_list_inv m
    (bsort_rank Nat.leb
        (bsort_rank Nat.leb (canon_sym_gr_list m i) ° bsort_rank Nat.leb p))).
*)
(* il faut que
  ff_app (canon_sym_gr_list m (g i)) (ff_app (collapse kl) j) =
  ff_app (canon_sym_gr_list m i) j
*)
erewrite rngl_summation_change_var with (g0 := g).
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | ].
rewrite Nat_sub_succ_1.
rewrite rngl_summation_list_permut with (l2 := seq 0 m!).
rewrite rngl_summation_seq_summation.
rewrite Nat.add_0_l.
apply rngl_summation_eq_compat.
intros i (_, Hi).
f_equal.
f_equal.
2: {
rewrite (rngl_product_shift 1).
rewrite Nat.sub_diag.
erewrite rngl_product_eq_compat. 2: {
  intros j (_, Hj).
  now rewrite Nat.add_comm, Nat.add_sub.
}
symmetry.
rewrite (rngl_product_shift 1); [ | ].
rewrite Nat.sub_diag.
erewrite rngl_product_eq_compat. 2: {
  intros j (_, Hj).
  now rewrite Nat.add_comm, Nat.add_sub.
}
symmetry. {
erewrite rngl_product_change_var with (g0 := ff_app (collapse kl)).
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | ].
rewrite Nat_sub_succ_1.
rewrite rngl_product_list_permut with (l2 := seq 0 m).
rewrite rngl_product_seq_product.
rewrite Nat.add_0_l.
apply rngl_product_eq_compat.
intros j (_, Hj).
unfold mat_el.
(*1*)
f_equal. {
  fold p.
(*
unfold g.
unfold "°".
rewrite permut_in_canon_sym_gr_of_its_rank.
unfold ff_app.
rewrite (List_map_nth' 0).
do 4 rewrite fold_ff_app.
...
rewrite permut_bsort_permut.
...
*)
rewrite <- (@canon_sym_gr_sym_gr_inv m (g i)).
symmetry.
rewrite <- (@canon_sym_gr_sym_gr_inv m (g i)).
rewrite canon_sym_gr_inv_sym_gr.
f_equal.
...
Search (length (nth _ _ _)).
Search canon_sym_gr_list_list.
Print canon_sym_gr_list_list.
Print sym_gr_inv.
...
permut_bsort_permut:
  ∀ (i : nat) (l : list nat), is_permut_list l → i < length l → ff_app (bsort_rank Nat.leb l) (ff_app l i) = i
canon_sym_gr_sym_gr_inv:
  ∀ n k i : nat, k < n! → i < n → ff_app (canon_sym_gr_list n k) (ff_app (canon_sym_gr_inv_list n k) i) = i
...
Search canon_sym_gr_inv_list.
...
Search (ff_app (canon_sym_gr_list _ _)).
unfold canon_sym_gr_inv_list.
...
Theorem pouet : ∀ n i,
  nth i (canon_sym_gr_list_list n) [] =
  bsort_rank Nat.leb (canon_sym_gr_inv_list n i).
...
...
  replace (g i) with (ff_app (canon_sym_gr_list m i) j).
Search (ff_app (canon_sym_gr_inv_list _ _)).
Search canon_sym_gr_inv_list.
...
  replace (g i) with (canon_sym_gr_list_inv m (bsort_rank Nat.leb p)).
  rewrite permut_in_canon_sym_gr_of_its_rank.
  rewrite permut_bsort_permut.
...
  unfold ff_app.
Search canon_sym_gr_list.
  replace (g i) with (canon_sym_gr_list_inv m i).
  replace (g i) with (ff_app (bsort Nat.leb p) i).
  unfold ff_app.
...
  rewrite permut_in_canon_sym_gr_of_its_rank.
...
  unfold g, "°".
  rewrite permut_in_canon_sym_gr_of_its_rank.
  unfold ff_app.
  rewrite (List_map_nth' 0).
...1
f_equal. 2: {
unfold mat_select_rows.
cbn.
rewrite (List_map_nth' 0).
symmetry.
rewrite (List_map_nth' 0).
symmetry.
f_equal.
rewrite (bsort_bsort_rank _ 0).
rewrite (List_map_nth' 0).
f_equal.
rewrite fold_ff_app.
unfold collapse.
rewrite permut_permut_bsort.
easy.
apply bsort_rank_is_permut_list.
rewrite length_bsort_rank.
rewrite Hklm.
admit.
rewrite length_bsort_rank.
admit.
admit.
admit.
}
fold p.
(* la formule g, h ci-dessous, je pense qu'elle n'est pas bonne
set (g := λ i,
  canon_sym_gr_list_inv m (bsort_rank Nat.leb p ° canon_sym_gr_list m i)).
Search (canon_sym_gr_list _ _).
*)
...
set (g' := canon_sym_gr_list_inv m (bsort_rank Nat.leb kl)).
...
permut_in_canon_sym_gr_of_its_rank:
  ∀ (n : nat) (l : list nat),
    is_permut n l → canon_sym_gr_list n (canon_sym_gr_list_inv n l) = l
...
unfold g.
Search (canon_sym_gr_list _ (canon_sym_gr_list_inv _ _)).
rewrite permut_in_canon_sym_gr_of_its_rank.
unfold "°".
unfold ff_app.
rewrite (List_map_nth' 0).
do 4 rewrite fold_ff_app.
...
apply rngl_product_eq_compat.
intros j (_, Hj).
(* bin non, c'est pas possible, ça !
   on prend la ligne j dans les deux cas ! *)
...
Print mat_select_rows.
Compute (mat_select_rows [1;0;2] (mk_mat [[1;2;3];[4;5;6];[7;8;9]])).
Compute (let A := mk_mat [[1;2;3];[4;5;6];[7;8;9]] in
  let kl := [1;0;2] in
  (mat_el (mat_select_rows (bsort Nat.leb kl) A) 0 =
   mat_el (mat_select_rows kl A) 0)).
...
set (g := λ i,
  canon_sym_gr_list_inv m (bsort_rank Nat.leb p ° canon_sym_gr_list m i)).
set (h := λ i,
  canon_sym_gr_list_inv m
    (bsort_rank Nat.leb
        (bsort_rank Nat.leb (canon_sym_gr_list m i) ° bsort_rank Nat.leb p))).
assert (Hgh : ∀ i, i < m! → g (h i) = i). {
  intros i Hi.
  unfold g, h.
  rewrite permut_in_canon_sym_gr_of_its_rank. 2: {
    apply bsort_rank_is_permut; unfold p.
    now rewrite comp_length, length_bsort_rank, length_collapse.
  }
  rewrite (permut_bsort_rank_comp m); cycle 1. {
    apply NoDup_bsort_rank.
  } {
    now rewrite length_bsort_rank, length_canon_sym_gr_list.
  } {
    apply bsort_rank_is_permut; unfold p.
    now rewrite length_collapse.
  }
  rewrite (permut_comp_assoc m); cycle 1. {
    do 2 rewrite length_bsort_rank.
    now unfold p; rewrite length_collapse.
  } {
    apply bsort_rank_is_permut.
    now rewrite length_bsort_rank, length_canon_sym_gr_list.
  }
  rewrite permut_comp_bsort_rank_r; [ | apply bsort_rank_is_permut_list ].
  unfold p.
  rewrite length_bsort_rank, length_collapse, Hklm.
  rewrite comp_1_l. 2: {
    intros j Hj.
    rewrite permut_bsort_rank_involutive in Hj. 2: {
      now apply canon_sym_gr_list_is_permut_list.
    }
    apply (In_nth _ _ 0) in Hj.
    rewrite length_canon_sym_gr_list in Hj.
    destruct Hj as (k & Hkm & Hkj).
    rewrite <- Hkj.
    now apply canon_sym_gr_list_ub.
  }
  rewrite permut_bsort_rank_involutive. 2: {
    now apply canon_sym_gr_list_is_permut_list.
  }
  now apply canon_sym_gr_inv_of_canon_sym_gr.
}
specialize (fact_neq_0 m) as Hfmz.
rewrite rngl_summation_change_var with (g0 := g) (h0 := h). 2: {
  intros i Hi.
  apply Hgh.
  flia Hi Hfmz.
}
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hfmz ].
rewrite Nat_sub_succ_1.
erewrite rngl_summation_list_eq_compat. 2: {
  intros i Hi.
  assert (Him : i < m!). {
    apply in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj).
    apply in_seq in Hj.
    destruct Hj as (_, Hj); cbn in Hj.
    rewrite <- Hji; unfold h.
    rewrite (permut_bsort_rank_comp m); cycle 1. {
      apply NoDup_bsort_rank.
    } {
      now rewrite length_bsort_rank, length_canon_sym_gr_list.
    } {
      apply bsort_rank_is_permut; unfold p.
      now rewrite length_collapse.
    }
    rewrite permut_bsort_rank_involutive. 2: {
      apply collapse_is_permut.
    }
    rewrite permut_bsort_rank_involutive. 2: {
      now apply canon_sym_gr_list_is_permut_list.
    }
    apply canon_sym_gr_list_inv_ub.
    apply comp_is_permut. {
      split; [ apply collapse_is_permut | ].
      now unfold p; rewrite length_collapse.
    }
    now apply canon_sym_gr_list_is_permut.
  }
  unfold g at 1.
  rewrite permut_in_canon_sym_gr_of_its_rank. 2: {
    apply comp_is_permut. {
      apply bsort_rank_is_permut; unfold p.
      now rewrite length_collapse.
    } {
      now apply canon_sym_gr_list_is_permut.
    }
  }
  rewrite (permut_comp_assoc m); cycle 1. {
    now unfold p; rewrite length_bsort_rank, length_collapse.
  } {
    now apply canon_sym_gr_list_is_permut.
  }
  rewrite comp_bsort_rank_r.
  rewrite permut_bsort_leb; [ | apply collapse_is_permut ].
  rewrite comp_1_l. 2: {
    intros j Hj.
    unfold p; rewrite length_collapse, Hklm.
    apply (In_nth _ _ 0) in Hj.
    rewrite length_canon_sym_gr_list in Hj.
    destruct Hj as (k & Hkm & Hkj).
    rewrite <- Hkj.
    now apply canon_sym_gr_list_ub.
  }
  easy.
}
cbn - [ mat_el ].
rewrite rngl_summation_list_permut with (l2 := seq 0 m!). 2: {
  apply permut_list_Permutation.
  split; [ | apply List_map_seq_length ].
  split. {
    rewrite List_map_seq_length.
    intros i Hi.
    apply in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj).
    apply in_seq in Hj.
    destruct Hj as (_, Hj); cbn in Hj.
    rewrite <- Hji; unfold h.
    apply canon_sym_gr_list_inv_ub.
    apply bsort_rank_is_permut; unfold p.
    now rewrite comp_length, length_bsort_rank, length_collapse.
  } {
    apply (NoDup_map_iff 0).
    rewrite seq_length.
    intros i j Hi Hj Hij.
    rewrite seq_nth in Hij; [ | easy ].
    rewrite seq_nth in Hij; [ | easy ].
    rewrite <- Hgh; [ symmetry | easy ].
    rewrite <- Hgh; [ symmetry | easy ].
    now f_equal.
  }
}
rewrite rngl_summation_seq_summation; [ | easy ].
rewrite Nat.add_0_l.
apply rngl_summation_eq_compat.
intros i (_, Hi).
f_equal.
(**)
destruct (Nat.eq_dec m 0) as [Hmz| Hmz]. {
  move Hmz at top; subst m.
  rewrite rngl_product_empty; [ | easy ].
  rewrite rngl_product_empty; [ | easy ].
  easy.
}
rewrite (rngl_product_shift 1); [ | flia Hmz ].
rewrite Nat.sub_diag.
erewrite rngl_product_eq_compat. 2: {
  intros j (_, Hj).
  now rewrite Nat.add_comm, Nat.add_sub.
}
symmetry.
rewrite (rngl_product_shift 1); [ | flia Hmz ].
rewrite Nat.sub_diag.
erewrite rngl_product_eq_compat. 2: {
  intros j (_, Hj).
  now rewrite Nat.add_comm, Nat.add_sub.
}
symmetry.
assert (Hpz : p ≠ []). {
  intros H; unfold p in H.
  apply length_zero_iff_nil in H.
  rewrite length_collapse in H.
  now rewrite Hklm in H.
}
assert (H : i < m!) by flia Hi Hfmz.
clear Hi Hfmz; rename H into Hi.
unfold g, p.
Check mk_mat.
Abort.
End a.
Require Import RnglAlg.Zrl.
Require Import ZArith.
Open Scope Z_scope.
Compute
  (let kl := [2;3;1]%nat in let m := length kl in
   let A := mk_mat [[3;4;1];[0;6;7];[1;3;1];[7;6;5]] in
map (λ i,
  ∏ (i0 = 0, m - 1),
  mat_el (mat_select_rows (bsort Nat.leb kl) A) i0
    (ff_app
       (canon_sym_gr_list m (canon_sym_gr_list_inv m (bsort_rank Nat.leb (collapse kl) ° canon_sym_gr_list m i)))
       i0) = ∏ (i0 = 0, m - 1), mat_el (mat_select_rows kl A) i0 (ff_app (canon_sym_gr_list m i) i0)) (seq 0 m!)).
(*
     = [42 = 42; 147 = 30; 0 = 147; 0 = 0; 42 = 42; 30 = 0]
*)
(* ils sont pas égaux, bordel de cul *)
Compute
  (let kl := [2;3;1]%nat in let m := length kl in
   let A := mk_mat [[3;4;1];[0;6;7];[1;3;1];[7;6;5]] in
  det (mat_select_rows kl A) =
       (ε kl * det (mat_select_rows (bsort Nat.leb kl) A))%F).
(* mais là, c'est bon, là *)
...
set (f l := ff_app (canon_sym_gr_inv_list m i ° l ° canon_sym_gr_list m i)).
set (g' := f p).
set (h' := f (bsort_rank Nat.leb p)).
erewrite rngl_product_change_var with (g0 := g') (h0 := h'). 2: {
  intros j (_, Hj).
  assert (H : j < m) by flia Hj Hmz.
  clear Hj Hmz; rename H into Hj.
  unfold g', h', f, "°".
  unfold ff_app.
  rewrite (List_map_nth' 0). 2: {
    rewrite (List_map_nth' 0). 2: {
      now rewrite length_canon_sym_gr_list.
    }
    rewrite (List_map_nth' 0). 2: {
      unfold p; rewrite length_bsort_rank, length_collapse, Hklm.
      now apply canon_sym_gr_list_ub.
    }
    do 3 rewrite fold_ff_app.
    rewrite length_canon_sym_gr_list.
    apply canon_sym_gr_inv_list_ub; [ easy | ].
    unfold ff_app.
    replace m with (length p); [ | now unfold p; rewrite <- Hklm, length_collapse ].
    now apply bsort_rank_ub.
  }
  rewrite (List_map_nth' 0). 2: {
    rewrite (List_map_nth' 0). 2: {
      now rewrite length_canon_sym_gr_list.
    }
    rewrite (List_map_nth' 0). 2: {
      unfold p; rewrite length_bsort_rank, length_collapse, Hklm.
      now apply canon_sym_gr_list_ub.
    }
    unfold p; rewrite length_collapse, Hklm.
    apply canon_sym_gr_list_ub; [ easy | ].
    apply canon_sym_gr_inv_list_ub; [ easy | ].
    do 2 rewrite fold_ff_app.
    replace m with (length p). 2: {
      now unfold p; rewrite <- Hklm, length_collapse.
    }
    now apply bsort_rank_ub.
  }
  rewrite (List_map_nth' 0). 2: {
    now rewrite length_canon_sym_gr_list.
  }
  rewrite (List_map_nth' 0). 2: {
    unfold p; rewrite length_bsort_rank, length_collapse, Hklm.
    now apply canon_sym_gr_list_ub.
  }
  do 6 rewrite fold_ff_app.
  rewrite canon_sym_gr_sym_gr_inv; [ | easy | ]. 2: {
    replace m with (length p). 2: {
      now unfold p; rewrite <- Hklm, length_collapse.
    }
    now apply bsort_rank_ub.
  }
  rewrite permut_permut_bsort; cycle 1. {
    apply collapse_is_permut.
  } {
    unfold p; rewrite length_collapse, Hklm.
    now apply canon_sym_gr_list_ub.
  }
  now apply canon_sym_gr_inv_sym_gr.
}
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hmz ].
rewrite Nat_sub_succ_1.
rewrite rngl_product_list_permut with (l2 := seq 0 m); cycle 1. {
  now destruct Hif.
} {
  apply permut_list_Permutation.
  unfold h', f.
  split; [ | now rewrite List_map_seq_length ].
  apply (map_ff_app_is_permut_list m); [ | apply seq_is_permut ].
  apply comp_is_permut; [ | now apply canon_sym_gr_list_is_permut ].
  apply comp_is_permut. 2: {
    unfold p; apply bsort_rank_is_permut.
    now rewrite length_collapse.
  }
  split. {
    now apply canon_sym_gr_inv_list_is_permut_list.
  }
  apply length_canon_sym_gr_inv_list.
}
rewrite rngl_product_seq_product; [ | easy ].
rewrite Nat.add_0_l.
apply rngl_product_eq_compat.
intros j (_, Hj).
assert (H : j < m) by flia Hj Hmz.
clear Hj Hmz; rename H into Hj.
unfold mat_select_rows, mat_el.
cbn.
unfold ff_app.
assert (H1 :
  nth (g' j) (canon_sym_gr_list m (g i)) 0 =
  nth j (canon_sym_gr_list m i) 0). {
  do 2 rewrite fold_ff_app.
  unfold g', g, f.
  assert (Hpc : ff_app p (ff_app (canon_sym_gr_list m i) j) < m). {
    unfold p, collapse.
    eapply lt_le_trans. {
      apply bsort_rank_ub.
      intros H.
      apply eq_bsort_rank_nil in H.
      now subst kl.
    }
    now rewrite length_bsort_rank, Hklm.
  }
  rewrite permut_in_canon_sym_gr_of_its_rank. 2: {
    apply comp_is_permut. {
      apply bsort_rank_is_permut; unfold p.
      now rewrite length_collapse.
    } {
      now apply canon_sym_gr_list_is_permut.
    }
  }
  unfold "°", ff_app.
  rewrite (List_map_nth' 0). 2: {
    rewrite (List_map_nth' 0). 2: {
      now rewrite length_canon_sym_gr_list.
    }
    rewrite (List_map_nth' 0). 2: {
      unfold p; rewrite length_collapse, Hklm.
      now apply canon_sym_gr_list_ub.
    }
    do 3 rewrite fold_ff_app.
    rewrite length_canon_sym_gr_list.
    now apply canon_sym_gr_inv_list_ub.
  }
  rewrite (List_map_nth' 0). 2: {
    now rewrite length_canon_sym_gr_list.
  }
  rewrite (List_map_nth' 0). 2: {
    unfold p; rewrite length_collapse, Hklm.
    now apply canon_sym_gr_list_ub.
  }
  do 5 rewrite fold_ff_app.
  rewrite canon_sym_gr_sym_gr_inv; [ | easy | easy ].
  rewrite permut_bsort_permut; cycle 1. {
    apply collapse_is_permut.
  } {
    unfold p; rewrite length_collapse, Hklm.
    now apply canon_sym_gr_list_ub.
  }
  easy.
}
rewrite H1.
f_equal.
rewrite (List_map_nth' 0). 2: {
  rewrite length_bsort.
  unfold g', f, "°", ff_app.
  rewrite (List_map_nth' 0); [ | now rewrite length_canon_sym_gr_list ].
  rewrite (List_map_nth' 0). 2: {
    unfold p; rewrite length_collapse, Hklm.
    now apply canon_sym_gr_list_ub.
  }
  do 3 rewrite fold_ff_app.
  rewrite Hklm.
  apply canon_sym_gr_inv_list_ub; [ easy | ].
  unfold p, collapse.
  unfold ff_app at 1.
  eapply lt_le_trans. {
    apply bsort_rank_ub.
    intros H.
    apply eq_bsort_rank_nil in H.
    now subst kl.
  }
  now rewrite length_bsort_rank, Hklm.
}
rewrite (List_map_nth' 0); [ | now rewrite Hklm ].
unfold g', f, "°", ff_app.
rewrite (List_map_nth' 0); [ | now rewrite length_canon_sym_gr_list ].
rewrite (List_map_nth' 0). 2: {
  unfold p; rewrite length_collapse, Hklm.
  now apply canon_sym_gr_list_ub.
}
(*
unfold p, collapse.
*)
do 5 rewrite fold_ff_app.
f_equal.
rewrite fold_comp_lt.
rewrite fold_comp_lt.
rewrite fold_comp_lt.
replace
  (bsort Nat.leb kl ° canon_sym_gr_inv_list m i ° p ° canon_sym_gr_list m i)
with
  (bsort Nat.leb kl ° (canon_sym_gr_inv_list m i ° p ° canon_sym_gr_list m i)).
unfold "°" at 1.
unfold ff_app at 1.
rewrite (List_map_nth' 0).
rewrite fold_ff_app.
fold (f p).
fold g'.
rewrite (bsort_bsort_rank _ 0).
unfold ff_app at 1.
rewrite (List_map_nth' 0).
do 2 rewrite fold_ff_app.
rewrite permut_permut_bsort.
unfold g', f.
...
rewrite <- (permut_comp_assoc n).
rewrite <- (permut_comp_assoc n).
rewrite <- list_comp_assoc.
fold f.
...
Compute (let kl := [7;2;28] in let m := 3 in let i := 6 in let j := 2 in
  ff_app
    (bsort Nat.leb kl ° canon_sym_gr_inv_list m i ° bsort_rank Nat.leb (bsort_rank Nat.leb kl)
     ° canon_sym_gr_list m i) j = ff_app kl j
).
unfold g, g', f in H1.
do 2 rewrite fold_ff_app in H1.
rewrite fold_comp_lt in H1.
...
Search (ff_app (bsort _ _)).
...
Print canon_sym_gr_inv_list.
Print canon_sym_gr_list_inv.
...
canon_sym_gr_inv_list = λ n k : nat, map (canon_sym_gr_inv_elem n k) (seq 0 n)
     : nat → nat → list nat
canon_sym_gr_list_inv = 
fix canon_sym_gr_list_inv (n : nat) (l : list nat) {struct n} : nat :=
  match n with
  | 0 => 0
  | S n' => hd 0 l * n'! + canon_sym_gr_list_inv n' (sub_canon_permut_list l)
  end
     : nat → list nat → nat
...
  nth (g' j) (canon_sym_gr_list m (g i)) 0 = nth j (canon_sym_gr_list m i) 0
...
the row
   (mat_select_rows (bsort Nat.leb kl) A)
      (?g i0)
must be the same row as
   (mat_select_rows kl A)
      i0
...
rewrite rngl_product_change_var with
  (g0 := ff_app (bsort_rank Nat.leb p)) (h0 := ff_app (bsort_rank Nat.leb p)). 2: {
...
}
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hmz ].
rewrite Nat_sub_succ_1.
(* pour voir... *)
erewrite rngl_product_list_eq_compat. 2: {
  intros j Hj.
  unfold mat_select_rows, mat_el.
  cbn.
  rewrite (List_map_nth' 0). 2: {
    rewrite length_bsort.
    unfold ff_app.
    rewrite Hp.
    unfold collapse.
    rewrite permut_bsort_rank_involutive. 2: {
      apply bsort_rank_is_permut_list.
    }
    apply bsort_rank_ub.
    intros H; subst kl.
    now symmetry in Hklm.
  }
  rewrite (bsort_bsort_rank _ 0).
  erewrite map_ext_in. 2: {
    intros k Hk.
    rewrite fold_ff_app.
    easy.
  }
  rewrite fold_comp_list.
  rewrite comp_bsort_rank_r.
  rewrite (bsort_bsort_rank _ 0).
  unfold ff_app.
  rewrite (List_map_nth' 0). 2: {
    rewrite length_bsort_rank.
    rewrite Hp.
    unfold collapse.
    rewrite permut_bsort_rank_involutive. 2: {
      apply bsort_rank_is_permut_list.
    }
    apply bsort_rank_ub.
    intros H; subst kl.
    now symmetry in Hklm.
  }
  do 4 rewrite fold_ff_app.
  rewrite fold_mat_el.
unfold ff_app at 1.
Search (ff_app (bsort_rank _ _)).
...
...
unfold g.
rewrite permut_in_canon_sym_gr_of_its_rank. 2: {
  apply comp_is_permut. {
    apply bsort_rank_is_permut.
    now rewrite Hp, length_collapse.
  } {
    apply canon_sym_gr_list_is_permut.
    flia Hi Hmz.
  }
}
(**)
unfold mat_el.
unfold "°".
unfold ff_app.
rewrite (List_map_nth' 0). 2: {
  rewrite length_canon_sym_gr_list; flia Hj.
}
remember (nth (j - 1) (canon_sym_gr_list m i) 0) as k eqn:Hk.
rewrite Hp.
unfold collapse.
rewrite permut_bsort_rank_involutive. 2: {
  apply bsort_rank_is_permut_list.
}
rewrite bsort_bsort_rank with (d := 0).
remember (bsort_rank Nat.leb kl) as q eqn:Hq.
unfold mat_select_rows.
cbn.
rewrite map_map.
rewrite (List_map_nth' 0). 2: {
  rewrite Hq, length_bsort_rank, Hklm; flia Hj.
}
rewrite (List_map_nth' 0); [ | rewrite Hklm; flia Hj ].
do 2 rewrite fold_mat_el.
...
f_equal. 2: {
  rewrite Hp; unfold collapse.
  rewrite permut_bsort_rank_involutive. 2: {
    apply bsort_rank_is_permut_list.
  }
(* mmm.... si kl n'est pas trié (il n'est pas censé l'être, je ne vois
   pas en quoi ce serait vrai, ça ; j'ai merdé quelque part *)
...
  rewrite bsort_rank_of_nodup_sorted; [ | | | easy | easy ]; cycle 1. {
    apply Nat_leb_antisym.
  } {
    apply Nat_leb_trans.
  }
  rewrite comp_1_l; [ easy | ].
  intros k Hk.
  apply (In_nth _ _ 0) in Hk.
  rewrite length_canon_sym_gr_list in Hk.
  destruct Hk as (u & Hum & Hnu).
  rewrite <- Hnu, Hklm.
  apply canon_sym_gr_list_ub; [ flia Hi Hmz | easy ].
}
f_equal.
apply sorted_bsort; [ | | | easy ]. {
  apply Nat_leb_antisym.
} {
  apply Nat_leb_trans.
} {
  apply Nat_leb_has_total_order.
}
Qed.

...

Arguments det_with_rows Hif (m n)%nat _ [kl]%list.

Theorem cauchy_binet_formula : in_charac_0_field →
  ∀ m n A B,
  is_correct_matrix A = true
  → is_correct_matrix B = true
  → mat_nrows A = m
  → mat_ncols A = n
  → mat_nrows B = n
  → mat_ncols B = m
  → det (A * B) =
     ∑ (jl ∈ sub_lists_of_seq_0_n n m),
     det (mat_select_cols jl A) * det (mat_select_rows jl B).
Proof.
intros Hif * Hca Hcb Har Hac Hbr Hbc.
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
  apply length_zero_iff_nil in Har, Hbr.
  subst lla llb; cbn.
  rewrite rngl_summation_list_only_one; cbn.
  symmetry; apply rngl_mul_1_l.
}
assert (Hab : is_square_matrix (A * B) = true). {
  apply is_scm_mat_iff.
  split. {
    rewrite mat_mul_ncols; [ | now rewrite Har ].
    now intros H; rewrite H in Hbc; symmetry in Hbc.
  } {
    intros l Hl.
    rewrite mat_mul_nrows, Har.
    apply In_nth with (d := []) in Hl.
    destruct Hl as (p & Hp & Hl).
    rewrite <- Hl; cbn.
    rewrite (List_map_nth' 0). 2: {
      rewrite seq_length.
      cbn in Hp.
      now rewrite List_map_seq_length in Hp.
    }
    now rewrite List_map_seq_length.
  }
}
(*1*)
rewrite det_is_det_by_canon_permut; try now destruct Hif.
erewrite rngl_summation_list_eq_compat. 2: {
  intros s Hs.
  rewrite (det_with_rows Hif m n B Hbr Hbc Hcb); cycle 1. {
    now apply (sub_list_of_seq_0_n_has_no_dup n m).
  } {
    now apply sub_list_firstn_nat_length in Hs.
  } {
    specialize (sub_lists_of_seq_0_n_are_sorted n m) as H1.
    specialize (H1 _ eq_refl _ Hs).
    now apply sorted_ltb_leb_incl.
  } {
    intros k Hk.
    now apply sub_lists_of_seq_0_n_lt with (k := m) (t := s).
  }
  easy.
}
cbn - [ det det' mat_nrows ].
Search (det (mat_select_rows _ _)).
(* https://proofwiki.org/wiki/Cauchy-Binet_Formula *)
Print det'.
Check det_with_rows.
Search (det (mat_select_rows _ _)).
...
rewrite det_is_det_by_canon_permut; [ | easy | easy ].
rewrite mat_mul_nrows, Har.
unfold mat_mul, mat_mul_el.
rewrite Har, Hac, Hbc.
(*2*)
unfold det'.
cbn - [ det ].
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_shift; [ | flia Hmz ].
  erewrite rngl_product_eq_compat. 2: {
    intros k Hk.
    rewrite Nat.add_comm, Nat.add_sub.
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hk Hmz ].
    rewrite (List_map_nth' 0). 2: {
      rewrite seq_length.
      apply canon_sym_gr_list_ub; [ | flia Hk Hmz ].
      specialize (fact_neq_0 m) as H.
      flia Hi H.
    }
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite seq_nth; [ | flia Hk Hmz ].
      rewrite seq_nth. 2: {
        apply canon_sym_gr_list_ub; [ | flia Hk Hmz ].
        specialize (fact_neq_0 m) as H.
        flia Hi H.
      }
      do 2 rewrite Nat.add_0_l.
      easy.
    }
    easy.
  }
  easy.
}
cbn - [ det ].
(* https://proofwiki.org/wiki/Cauchy-Binet_Formula *)
remember (canon_sym_gr_list m) as σ eqn:Hσ.
(*
  ∑ (k = 0, m! - 1),
  ε m (σ k) *
  ∏ (i = 0, m - 1),
    (∑ (j = 0, n - 1), mat_el A i j * mat_el B j (ff_app (σ k) i)) =

  ∑ (k = 0, m! - 1),
  ε m (σ k) *
  (a 0 0 * b 0 (σ k 0) + a 0 1 * b 1 (σ k 0) + ... + a 0 (n-1) * b (n-1) (σ k 0)) *
  (a 1 0 * b 0 (σ k 1) + a 1 1 * b 1 (σ k 1) + ... + a 1 (n-1) * b (n-1) (σ k 1)) *
  ...
  (a (m-1) 0 * b 0 (σ k (m-1)) + a (m-1) 1 * b 1 (σ k (m-1)) + ... + a (m-1) (n-1) * b (n-1) (σ k (m-1)))

In the initial theorem,
  lhs has m!(n^m) terms
  rhs has n!/(m!(n-m)!).(m!/(2!(n-2)!)) terms
how is it possible to make both sides equal?
*)
...
Restart.
intros Hif * Hca Hcb Har Hac Hbr Hbc.
Show.
...
*)
...
erewrite rngl_summation_change_var.
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | apply Nat.neq_0_lt_0, fact_neq_0 ].
rewrite Nat_sub_succ_1.
...2
erewrite map_ext_in. 2: {
  intros i Hi.
  erewrite map_ext_in. 2: {
    intros k Hk.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite rngl_mul_comm; [ | now destruct Hif ].
      easy.
    }
    easy.
  }
  easy.
}
(* k-th col of AB is
     ∑ (j = 0, n - 1), mat_el B j k * mat_el A i j
 *)
(* i.e.
     let As j := mat_el A i j in
     ∑ (j = 0, n - 1), mat_el B j k * As j
 *)
unfold det'.
cbn - [ det ].
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_shift; [ | flia Hmz ].
  erewrite rngl_product_eq_compat. 2: {
    intros k Hk.
    rewrite Nat.add_comm, Nat.add_sub.
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hk Hmz ].
    rewrite (List_map_nth' 0). 2: {
      rewrite seq_length.
      apply canon_sym_gr_list_ub; [ | flia Hk Hmz ].
      specialize (fact_neq_0 m) as H.
      flia Hi H.
    }
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite seq_nth. 2: {
        apply canon_sym_gr_list_ub; [ | flia Hk Hmz ].
        specialize (fact_neq_0 m) as H.
        flia Hi H.
      }
      rewrite Nat.add_0_l.
      rewrite seq_nth; [ | flia Hk Hmz ].
      rewrite Nat.add_0_l.
      easy.
    }
    easy.
  }
  easy.
}
cbn - [ det ].
...
Require Import MyVector.
Check @determinant_multilinear.
Print mat_repl_vect.
map2 (replace_at k) (mat_list_list M) (vect_list V) =
map
  (λ i : nat,
   map (λ k : nat, ∑ (j = 0, n - 1), mat_el B j k * mat_el A i j)
     (seq 0 m))
  (seq 0 m)

Print replace_at.
...1
rewrite det_is_det_by_canon_permut; [ | easy | easy ].
rewrite mat_mul_nrows, Har.
unfold det'.
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj; cbn.
    rewrite (List_map_nth' 0); [ | rewrite seq_length, Har; flia Hj ].
    rewrite Har, Hbc.
    unfold mat_mul_el.
    rewrite Hac.
    rewrite seq_nth; [ | flia Hj ].
    rewrite Nat.add_0_l.
    easy.
  }
  easy.
}
symmetry; symmetry.
...
(* interesting property, even if, perhaps, not useful here *)
assert (sub_lists_of_seq_0_n m m = [seq 0 m]).
...

(*
Abort.
End a.
Require Import RnglAlg.Zrl.
Require Import ZArith.
Open Scope Z_scope.
Arguments mat_select_cols {T}%type {ro} jl%list.
Compute (let A := mk_mat [[3;4;1];[0;6;7];[1;3;1]] in let jl := [0;2]%nat in mat_select_rows jl A).
Compute (let A := mk_mat [[3;4;1];[0;6;7];[1;3;1]] in let B := mk_mat [[0;6;7];[1;3;1];[3;2;1]] in let m := mat_nrows A in let n := mat_ncols A in (det (A * B), ∑ (jl ∈ sub_lists_of_seq_0_n n m), det (mat_select_cols jl A) * det (mat_select_rows jl B), det A * det B)).
Compute (let B := mk_mat [[3;4];[2;6];[1;3]] in let A := mk_mat [[1;6;7];[1;3;1]] in let m := mat_nrows A in let n := mat_ncols A in (det (A * B), ∑ (jl ∈ sub_lists_of_seq_0_n n m), det (mat_select_cols jl A) * det (mat_select_rows jl B), det A * det B, m, n, sub_lists_of_seq_0_n n m)).
Compute (sub_lists_of_seq_0_n 3 3).
...
*)


(* other attempts to prove det(AB)=det(A)det(B) *)

(*
Theorem determinant_mul : ∀ A B, det (A * B) = (det A * det B)%F.
Proof.
intros.
(* essai avec les formes multilinéaires alternées...

trouvé sur le web
(https://les-mathematiques.net/vanilla/index.php?p=discussion/1339028#Comment_1339028)

 Il vaut mieux éviter à tout prix la formule explicite. On peut
 utiliser la méthode de Gauss, ou bien utiliser le fait que
 l'application B↦det(AB) est multilinéaire alternée, et donc est un
 multiple de B↦detB

 Il faut d'abord avoir établi que l'espace des formes multilinéaires
 alternées est de dimension 1 et que le déterminant est l'unique telle
 forme qui vaut 1 en l'identité. Une fois ceci acquis, on en déduit
 que det(AB)=αdetB où α est un scalaire qui ne dépend que de A. On le
 trouve en prenant B=I, ce qui donne detA=αdetI=α.
*)
Check determinant_multilinear.
Check determinant_alternating.
...
*)

(* very interesting, too, contains several proofs of det(AB)=det(A)det(B)
https://proofwiki.org/wiki/Determinant_of_Matrix_Product
*)

(* stuff to play with "ring_simplify" below *)
Context {Hic : @rngl_is_comm T ro rp = true}.
Context {Hop : @rngl_has_opp T ro = true}.
Require Import Ring.
Add Ring rngl_ring : (@rngl_ring_theory T ro rp Hic Hop).
(* end stuff *)

Theorem determinant_mul : in_charac_0_field →
  ∀ A B,
  is_square_matrix A = true
  → is_square_matrix B = true
  → mat_nrows A = mat_nrows B
  → det (A * B) = (det A * det B)%F.
Proof.
intros Hif * Hasm Hbsm Hrab.
(* essai avec le déterminant défini par permutations *)
assert (Habsm : is_square_matrix (A * B) = true). {
  now apply squ_mat_mul_is_squ.
}
remember (mat_nrows A) as n eqn:Hra.
rename Hrab into Hrb.
symmetry in Hra, Hrb.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  unfold det; cbn.
  move Hnz at top; subst n; cbn.
  rewrite Hra, Hrb; cbn.
  symmetry; apply rngl_mul_1_l.
}
rewrite det_is_det_by_canon_permut; [ | easy | easy ].
rewrite det_is_det_by_canon_permut; [ | easy | easy ].
rewrite det_is_det_by_canon_permut; [ | easy | easy ].
rewrite mat_mul_nrows.
unfold det'.
rewrite Hra, Hrb.
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite mat_el_mul; cycle 1. {
      rewrite mat_mul_nrows, Hra.
      flia Hj.
    } {
      rewrite mat_mul_ncols; [ | rewrite Hra; flia Hj ].
      rewrite square_matrix_ncols; [ | easy ].
      rewrite Hrb.
      apply canon_sym_gr_list_ub; [ | flia Hj ].
      specialize (fact_neq_0 n) as Hfnz.
      flia Hi Hfnz.
    }
    rewrite square_matrix_ncols; [ | easy ].
    rewrite Hra.
    easy.
  }
  cbn.
  easy.
}
cbn.
(*1*)
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  rewrite rngl_product_shift; [ | flia Hnz ].
  erewrite rngl_product_eq_compat. 2: {
    intros j (_, Hj).
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  easy.
}
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  rewrite rngl_product_shift; [ | flia Hnz ].
  erewrite rngl_product_eq_compat. 2: {
    intros j (_, Hj).
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  easy.
}
rewrite rngl_mul_comm; [ | now destruct Hif ].
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  rewrite rngl_product_shift; [ | flia Hnz ].
  erewrite rngl_product_eq_compat. 2: {
    intros j (_, Hj).
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  easy.
}
rewrite rngl_mul_comm; [ | now destruct Hif ].
symmetry.
(*
Noting
   ε(i) = signature of the i-th permutation in the canonic symmetric group
   σ(i,j) = j-th element of the i-th permutation in the canonic sym gr
We have to prove that
  ∑ (i = 0, n!-1), ε(i) ∏ (j = 0, n-1), ∑ (k = 0, n-1), a(j,k) * b(k,σ(i,j)) =
  ∑ (i = 0, n! - 1), ε(i) ∏ (j = 0, n-1), a(j,σ(i,j)) *
  ∑ (i = 0, n! - 1), ε(i) ∏ (j = 0, n-1), b(j,σ(i,j))
The problem is that the lhs contains
  n!*n^n terms
But the rhs contains
  n!*n! terms
Some terms of the lhs must cancel each other. But which ones?
*)
destruct n; [ easy | ].
destruct n. {
  cbn - [ "/" ff_app ].
...
  unfold ε'.
  do 3 rewrite rngl_summation_only_one.
  do 7 rewrite rngl_product_only_one.
  rewrite rngl_summation_only_one; cbn.
  rewrite rngl_div_1_r; [ | now destruct Hif; left | now destruct Hif ].
  now do 3 rewrite rngl_mul_1_l.
}
destruct n. {
  unfold iter_seq, iter_list; cbn.
  do 7 rewrite rngl_add_0_l.
  do 6 rewrite rngl_mul_1_l.
  unfold ε', iter_seq, iter_list; cbn.
  do 8 rewrite rngl_mul_1_l.
  rewrite rngl_add_0_r.
  rewrite rngl_sub_0_r; [ | now destruct Hif; left ].
  rewrite rngl_add_sub; [ | now destruct Hif; left ].
  rewrite rngl_mul_1_l.
  rewrite rngl_div_1_r; [ | now destruct Hif; left | now destruct Hif ].
  rewrite rngl_div_1_r; [ | now destruct Hif; left | now destruct Hif ].
  remember (mat_el A) as a eqn:Ha.
  remember (mat_el B) as b eqn:Hb.
  move b before a.
(**)
  ring_simplify.
(*
  rewrite rngl_mul_1_l.
  do 2 rewrite rngl_mul_1_l.
  unfold rngl_sub.
  replace rngl_has_opp with true by now destruct Hif.
  rewrite rngl_mul_1_r.
  rewrite rngl_add_0_l.
  rewrite rngl_mul_opp_l; [ | now destruct Hif ].
  rewrite rngl_mul_opp_l; [ | now destruct Hif ].
  rewrite rngl_mul_opp_l; [ | now destruct Hif ].
  do 3 rewrite rngl_mul_1_l.
  rewrite fold_rngl_sub; [ | now destruct Hif ].
  rewrite fold_rngl_sub; [ | now destruct Hif ].
  rewrite fold_rngl_sub; [ | now destruct Hif ].
*)
...
(*
  (a 0 0 * b 0 0 + a 0 1 * b 1 0) * (a 1 0 * b 0 1 + a 1 1 * b 1 1) -
  (a 0 0 * b 0 1 + a 0 1 * b 1 1) * (a 1 0 * b 0 0 + a 1 1 * b 1 0) =

  (a 0 0 * a 1 1 - a 0 1 * a 1 0) * (b 0 0 * b 1 1 - b 0 1 * b 1 0)
*)
...1
rewrite rngl_summation_mul_summation; [ | now destruct Hif; left ].
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros i (_, Hi).
  rewrite <- rngl_mul_summation_distr_l; [ | now destruct Hif; left ].
  easy.
}
symmetry.
apply rngl_summation_eq_compat.
intros i (_, Hi).
rewrite <- rngl_mul_assoc.
f_equal.
symmetry.
rewrite rngl_mul_summation_distr_l; [ | now destruct Hif; left ].
symmetry.
rewrite rngl_product_shift; [ | flia Hnz ].
rewrite rngl_product_summation_distr; [ | destruct Hif; now left ].
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  erewrite rngl_product_eq_compat. 2: {
    intros k Hk.
    now rewrite (Nat.add_comm 1 k), Nat.add_sub.
  }
  easy.
}
cbn.
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite rngl_mul_assoc.
  rewrite rngl_mul_mul_swap; [ | now destruct Hif ].
  rewrite <- rngl_product_mul_distr; [ | now destruct Hif ].
  rewrite rngl_mul_comm; [ | now destruct Hif ].
  rewrite rngl_product_shift; [ | flia Hnz ].
  erewrite rngl_product_eq_compat. 2: {
    intros k Hk.
    rewrite Nat.add_comm, Nat.add_sub.
    easy.
  }
  easy.
}
symmetry.
(* bizarre: n^n termes vs n! termes *)
destruct (Nat.eq_dec n 2) as [Hn2| Hn2]. {
  move Hn2 at top; subst n.
  cbn - [ "/" "mod" Nat.pow "-" canon_sym_gr_list ].
  replace (2 - 1) with 1 by easy.
  replace (2 ^ 2 - 1) with 3 by easy.
  cbn in Hi.
  cbn - [ "/" "mod" ].
  unfold iter_seq, iter_list.
  cbn - [ "/" "mod" ].
  do 2 rewrite rngl_add_0_l.
  do 6 rewrite rngl_mul_1_l.
  rewrite Nat.div_0_l; [ | easy ].
  rewrite Nat.div_0_l; [ | easy ].
  rewrite Nat.div_0_l; [ | easy ].
  rewrite Nat.div_0_l; [ | easy ].
  rewrite Nat.div_0_l; [ | easy ].
  rewrite Nat.mod_0_l; [ | easy ].
  rewrite Nat.mod_0_l; [ | easy ].
  do 4 rewrite Nat.div_1_r.
  rewrite Nat.div_same; [ | easy ].
  rewrite Nat.mod_same; [ | easy ].
  rewrite Nat.mod_small; [ | flia ].
  cbn.
  unfold ε'; cbn.
  unfold iter_seq, iter_list; cbn.
  do 8 rewrite rngl_mul_1_l.
  repeat rewrite rngl_add_0_r.
  rewrite rngl_sub_0_r; [ | now destruct Hif; left ].
  rewrite rngl_mul_1_l.
  rewrite rngl_mul_1_r.
  rewrite rngl_add_sub; [ | now destruct Hif; left ].
  rewrite rngl_div_1_r; [ | now destruct Hif; left | now destruct Hif ].
  rewrite rngl_div_1_r; [ | now destruct Hif; left | now destruct Hif ].
  rewrite rngl_mul_1_l.
  rewrite rngl_mul_1_r.
  destruct (Nat.eq_dec i 1) as [Hi1| Hi1]. {
    subst i.
    cbn.
...
intros.
(* essai avec le déterminant défini par récurrence *)
cbn.
rewrite List_map_seq_length.
unfold det.
remember (mat_nrows A) as n eqn:Hra.
symmetry in Hra.
enough (Hrb : mat_nrows B = n).
...
intros.
rewrite laplace_formula_on_rows with (i := 0).
rewrite laplace_formula_on_rows with (i := 0).
rewrite laplace_formula_on_rows with (i := 0).
rewrite mat_mul_ncols.
(* déjà, ce serait pas mal si on  prouvait que com(A*B)=com(A)*com(B) *)
(* mais je viens de laisser tomber cette idée parce que, de toutes façons,
   la définition de com fait déjà intervenir det : ça boucle ! *)
...
Check comatrix_mul.
...
intros.
Check @laplace_formula_on_rows.
(* https://www.youtube.com/watch?v=-CySi7uauCg *)
...
rewrite det_is_det_by_canon_permut.
rewrite det_is_det_by_canon_permut.
rewrite det_is_det_by_canon_permut.
cbn; rewrite List_map_seq_length.
unfold determinant'.
...
Check laplace_formula_on_rows.
Check laplace_formula_on_cols.
Search comatrix.
...
Require Import IterMul.
Search determinant.
...
intros.
unfold determinant; cbn.
rewrite List_map_seq_length.
Print determinant_loop.
...
