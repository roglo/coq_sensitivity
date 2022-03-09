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

Fixpoint first_non_fix_transp i p :=
  match p with
  | [] => None
  | j :: l =>
      if i =? j then first_non_fix_transp (S i) l
      else Some (i, j)
  end.

Fixpoint transp_loop' it (p : list nat) :=
  match it with
  | 0 => []
  | S it' =>
      match first_non_fix_transp 0 p with
      | None => []
      | Some (k, pk) => (k, pk) :: transp_loop' it' (list_swap_elem 0 p k pk)
      end
  end.

Definition transp_list' p := transp_loop' (length p) p.

Fixpoint transp_loop'' it i (p : list nat) :=
  match it with
  | 0 => []
  | S it' =>
      match first_non_fix_transp i p with
      | None => []
      | Some (k, pk) =>
          (k, pk) ::
          transp_loop'' it' k
            (skipn (k - i) (list_swap_elem 0 p (k - i) (pk - i)))
      end
  end.

(*
Definition list_swap_elem' A (d : A) l i j :=
  replace_at j (replace_at i l (nth j l d)) (nth i l d).
*)

Definition transp_list'' p := transp_loop'' (length p) 0 p.

(*
Compute (transp_list' [3;2;0;1]).
Compute (transp_list'' [3;2;0;1]).
Compute (map (λ l, (l, transp_list' l)) (canon_sym_gr_list_list 4)).
Compute (map (λ l, (l, transp_list'' l)) (canon_sym_gr_list_list 4)).
Compute (map (λ l, (transp_list' l, transp_list'' l)) (canon_sym_gr_list_list 4)).
Compute (map (λ l, list_eqb (pair_eqb Nat.eqb) (transp_list' l) (transp_list'' l)) (canon_sym_gr_list_list 4)).
*)

Fixpoint bsort_gen_insert {A B} (ord : A → A → bool) (f : B → A) ia lrank :=
  match lrank with
  | [] => ([ia], 0)
  | ib :: l =>
      if ord (f ia) (f ib) then (ia :: lrank, 0)
      else
        let (l', n) := bsort_gen_insert ord f ia l in
        (ib :: l', S n)
  end.

Fixpoint bsort_gen_loop {A} (ord : A → A → bool) f lrank (l : list A) :=
  match l with
  | [] => (lrank, [])
  | _ :: l' =>
      let (lrank', n) := bsort_gen_insert ord f (length lrank) lrank in
      let (l'', nl) := bsort_gen_loop ord f lrank' l' in
      (l'', length lrank - n :: nl)
  end.

(* return a pair
   - the permutation to apply to the initial list to get the sorted list
   - a list of the number of transpositions to insert the elements
*)
Definition bsort_gen {A} (ord : A → A → bool) l :=
  match l with
  | [] => ([], [])
  | d :: _ => bsort_gen_loop ord (λ i, nth i l d) [] l
  end.

(*
Compute (bsort_gen Nat.leb [20;12;7;9]).
Compute (bsort_gen Nat.leb [7;8;5;4]).
Compute (bsort_gen Nat.leb [3;2;0;1]).
Compute (map (λ l, (l, snd (bsort_gen Nat.leb l))) (canon_sym_gr_list_list 4)).
*)

(*
Definition transp_of_pos m n :=
  iter_list (seq n (m - n)) (λ t i, (i, i + 1) :: t) [].

Definition transp_list p :=
  fold_right
    (λ i l,
     let j := nth i (snd (bsort_gen Nat.leb p)) 0 in
     if i =? j then l else transp_of_pos i j ++ l)
    []
    (seq 0 (length p)).
*)

Fixpoint transp_of_pos n i :=
  match i with
  | 0 => []
  | S i' => (n - 1, n) :: transp_of_pos (n -  1) i'
  end.

Definition transp_list p :=
  iter_seq 0 (length p - 1)
    (λ t n, t ++ transp_of_pos n (ff_app (snd (bsort_gen Nat.leb p)) n)) [].

(*
Compute (transp_list [20;12;7;9]).
Compute (transp_list [3;2;0;1]).
Compute (map (λ l, (l, transp_list l)) (canon_sym_gr_list_list 4)).
*)

Theorem first_non_fix_transp_Some_neq_le : ∀ i p k kp,
  first_non_fix_transp i p = Some (k, kp)
  → i ≤ k ∧ k ≠ kp ∧ k < i + length p.
Proof.
intros * Hk.
split. {
  revert i k kp Hk.
  induction p as [| a]; intros; [ easy | ].
  cbn in Hk.
  rewrite if_eqb_eq_dec in Hk.
  destruct (Nat.eq_dec i a) as [Hia| Hia]. {
    specialize (IHp _ _ _ Hk) as H1.
    flia H1.
  }
  now injection Hk; clear Hk; intros; subst i a.
}
split. {
  revert i k kp Hk.
  induction p as [| a]; intros; [ easy | ].
  cbn in Hk.
  rewrite if_eqb_eq_dec in Hk.
  destruct (Nat.eq_dec i a) as [Hia| Hia]. {
    now apply IHp with (i := S i).
  }
  now injection Hk; clear Hk; intros; subst k kp.
} {
  revert i k kp Hk.
  induction p as [| a]; intros; [ easy | ].
  cbn in Hk.
  rewrite if_eqb_eq_dec in Hk.
  destruct (Nat.eq_dec i a) as [Hia| Hia]. {
    apply IHp in Hk.
    cbn; flia Hk.
  }
  cbn.
  injection Hk; clear Hk; intros; subst i kp.
  flia.
}
Qed.

Theorem first_non_fix_transp_Some_iff : ∀ i p k kp,
  first_non_fix_transp i p = Some (k, kp)
  ↔ (∀ j, i ≤ j < k → nth (j - i) p 0 = j) ∧
    nth (k - i) p 0 = kp ∧
    k ≠ kp ∧
    i ≤ k < i + length p.
Proof.
intros.
split. {
  intros Hk.
  split. {
    intros j Hijk.
    revert i k kp Hk Hijk.
    induction p as [| a]; intros; [ easy | ].
    cbn in Hk.
    rewrite if_eqb_eq_dec in Hk.
    destruct (Nat.eq_dec i a) as [Hia| Hia]. {
      specialize (IHp _ _ _ Hk) as H1.
      subst a.
      destruct (Nat.eq_dec i j) as [Hij| Hij]. {
        subst j.
        now rewrite Nat.sub_diag.
      }
      assert (H : S i ≤ j < k) by flia Hijk Hij.
      specialize (H1 H); clear H.
      now replace (j - i) with (S (j - S i)) by flia Hijk Hij.
    }
    injection Hk; clear Hk; intros; subst i a.
    flia Hijk.
  }
  split. {
    revert i k kp Hk.
    induction p as [| a]; intros; [ easy | ].
    cbn in Hk.
    rewrite if_eqb_eq_dec in Hk.
    destruct (Nat.eq_dec i a) as [Hia| Hia]. {
      specialize (IHp _ _ _ Hk) as H1.
      subst a.
      destruct (le_dec k i) as [Hki| Hki]. {
        specialize (first_non_fix_transp_Some_neq_le _ _ Hk) as H2.
        flia Hki H2.
      }
      apply Nat.nle_gt in Hki.
      now replace (k - i) with (S (k - S i)) by flia Hki.
    }
    injection Hk; clear Hk; intros; subst i a.
    now rewrite Nat.sub_diag.
  }
  split. {
    apply (first_non_fix_transp_Some_neq_le i p Hk).
  } {
    specialize (first_non_fix_transp_Some_neq_le i p Hk) as H1.
    easy.
  }
} {
  intros (Hbef & Hkp & Hkkp & Hkl).
  revert i k kp Hbef Hkp Hkkp Hkl.
  induction p as [| a]; intros. {
    rewrite Nat.add_0_r in Hkl; flia Hkl.
  }
  cbn.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec i a) as [Hia| Hia]. {
    subst a.
    destruct p as [| b]. {
      exfalso.
      cbn in Hkl.
      replace k with i in Hkp, Hbef, Hkkp by flia Hkl.
      now rewrite Nat.sub_diag in Hkp.
    }
    destruct (Nat.eq_dec k i) as [Hki| Hki]. {
      subst k.
      now rewrite Nat.sub_diag in Hkp; cbn in Hkp.
    }
    apply IHp; [ | | easy | ]. {
      intros j Hj.
      destruct j; [ easy | ].
      rewrite Nat.sub_succ.
      specialize (Hbef (S j)) as H1.
      assert (H : i ≤ S j < k) by flia Hj.
      specialize (H1 H); clear H.
      rewrite Nat.sub_succ_l in H1; [ easy | flia Hj ].
    } {
      now replace (k - i) with (S (k - S i)) in Hkp by flia Hki Hkl.
    } {
      cbn in Hkl |-*.
      flia Hkl Hki.
    }
  }
  destruct (Nat.eq_dec k i) as [Hki| Hki]. {
    subst k; f_equal; f_equal.
    now rewrite Nat.sub_diag in Hkp.
  }
  exfalso.
  replace (k - i) with (S (k - S i)) in Hkp by flia Hki Hkl.
  cbn in Hkp.
  cbn in Hkl.
  destruct p as [| b]. {
    cbn in Hkl.
    flia Hkl Hki.
  }
  cbn in Hkl.
  specialize (Hbef i) as H1.
  assert (H : i ≤ i < k) by flia Hkl Hki.
  specialize (H1 H); clear H.
  rewrite Nat.sub_diag in H1; cbn in H1.
  now symmetry in H1.
}
Qed.

Definition swap n p q := list_swap_elem 0 (seq 0 n) p q.

Theorem swap_length : ∀ n p q, length (swap n p q) = n.
Proof.
intros.
unfold swap, list_swap_elem.
rewrite List_map_seq_length.
apply seq_length.
Qed.

Notation "'Comp' n ( i ∈ l ) , g" :=
  (iter_list l (λ c i, g ° c) (seq 0 n))
  (at level 35, i at level 0, l at level 60, n at level 0).

Theorem bsort_rank_gen_insert : ∀ A B (ord : A → _) (f : B → _) ia lr,
  bsort_rank_insert ord f ia lr =
  fst (bsort_gen_insert ord f ia lr).
Proof.
intros.
revert ia.
induction lr as [| ib]; intros; [ easy | cbn ].
destruct (ord (f ia) (f ib)); [ easy | ].
rewrite IHlr.
now destruct (bsort_gen_insert _ _ _ _).
Qed.

Theorem bsort_rank_gen_loop : ∀ A (ord : A → _) f lr l,
  bsort_rank_loop ord f lr l = fst (bsort_gen_loop ord f lr l).
Proof.
intros.
revert lr.
induction l as [| a]; intros; [ easy | cbn ].
rewrite IHl.
rewrite bsort_rank_gen_insert.
remember (bsort_gen_insert _ _ _ _) as x eqn:Hx; symmetry in Hx.
destruct x as (lr', n).
remember (bsort_gen_loop ord f lr' l) as y eqn:Hy; symmetry in Hy.
destruct y as (l'', nl); cbn.
now rewrite Hy.
Qed.

Theorem bsort_rank_gen : ∀ A (ord : A → _) l,
  bsort_rank ord l = fst (bsort_gen ord l).
Proof.
intros.
unfold bsort_rank, bsort_gen.
destruct l as [| d]; [ easy | ].
apply bsort_rank_gen_loop.
Qed.

Theorem snd_bsort_gen_insert_ub : ∀ A B (ord : A → _) (f : B → _) ia lr,
  snd (bsort_gen_insert ord f ia lr) ≤ length lr.
Proof.
intros.
revert ia.
induction lr as [| ib]; intros; [ easy | cbn ].
destruct (ord (f ia) (f ib)); [ easy | ].
remember (bsort_gen_insert ord f ia lr) as x eqn:Hx.
symmetry in Hx.
destruct x as (lr', n); cbn.
apply -> Nat.succ_le_mono.
specialize (IHlr ia) as H1.
now rewrite Hx in H1.
Qed.

Theorem length_snd_bsort_gen_loop : ∀ A (ord : A → _) f lr l,
  length (snd (bsort_gen_loop ord f lr l)) = length l.
Proof.
intros.
revert lr.
induction l as [| a]; intros; [ easy | cbn ].
remember (bsort_gen_insert ord f (length lr) lr) as x eqn:Hx.
symmetry in Hx.
destruct x as (lr', n).
remember (bsort_gen_loop ord f lr' l) as y eqn:Hy.
symmetry in Hy.
destruct y as (l'', nl).
cbn; f_equal.
specialize (IHl lr') as H1.
now rewrite Hy in H1.
Qed.

Theorem length_fst_bsort_gen_insert : ∀ A B (ord : A → _) (f : B → _) ia lr,
  length (fst (bsort_gen_insert ord f ia lr)) = S (length lr).
Proof.
intros.
revert ia.
induction lr as [| ib]; intros; [ easy | cbn ].
destruct (ord (f ia) (f ib)); [ easy | ].
remember (bsort_gen_insert ord f ia lr) as x eqn:Hx; symmetry in Hx.
destruct x as (lr', n); cbn.
f_equal.
specialize (IHlr ia) as H1.
now rewrite Hx in H1.
Qed.

Theorem in_bsort_gen_insert : ∀ A B (ord : A → _) (f : B → _) ia lr i,
  i ∈ fst (bsort_gen_insert ord f ia lr) → i ∈ ia :: lr.
Proof.
intros * Hi.
induction lr as [| ib]. {
  cbn in Hi.
  destruct Hi as [Hi| Hi]; [ | easy ].
  now rewrite Hi; left.
}
cbn in Hi.
destruct (ord (f ia) (f ib)); [ easy | ].
remember (bsort_gen_insert ord f ia lr) as x eqn:Hx.
symmetry in Hx.
destruct x as (lr', n).
cbn - [ In ] in Hi, IHlr.
destruct Hi as [Hi| Hi]; [ now subst i; right; left | ].
specialize (IHlr Hi).
destruct IHlr as [H| H]; [ now left | now right; right ].
Qed.

Theorem snd_bsort_gen_loop_ub : ∀ A (ord : A → _) f lrank l i,
  (∀ i, i ∈ lrank → i < length lrank)
  → nth i (snd (bsort_gen_loop ord f lrank l)) 0 ≤ i + length lrank.
Proof.
intros * Hi.
revert lrank i Hi.
induction l as [| a]; intros; [ now cbn; rewrite match_id | cbn ].
remember (bsort_gen_insert ord _ (length lrank) lrank) as x eqn:Hx.
symmetry in Hx.
destruct x as (lr', n).
remember (bsort_gen_loop ord _ lr' l) as y eqn:Hy.
symmetry in Hy.
destruct y as (lr'', nl).
cbn - [ nth ].
destruct i; cbn; [ flia | ].
specialize (IHl lr' i) as H1.
rewrite Hy in H1; cbn in H1.
specialize length_fst_bsort_gen_insert as H2.
specialize (H2 A nat ord f (length lrank) lrank).
rewrite Hx in H2; cbn in H2.
rewrite <- Nat.add_succ_r, <- H2.
apply H1.
intros j Hj.
rewrite H2.
specialize in_bsort_gen_insert as H3.
specialize (H3 A nat ord f (length lrank) lrank j).
rewrite Hx in H3; cbn - [ In ] in H3.
specialize (H3 Hj).
destruct H3 as [H3| H3]; [ now subst j | ].
specialize (Hi j H3).
flia Hi.
Qed.

Theorem snd_bsort_gen_ub : ∀ A (ord : A → _) l i,
  nth i (snd (bsort_gen ord l)) 0 ≤ i.
Proof.
intros.
destruct l as [| d]; [ now cbn; rewrite match_id | ].
unfold bsort_gen.
remember (d :: l) as l' eqn:Hl'.
clear l Hl'.
rename l' into l.
specialize snd_bsort_gen_loop_ub as H1.
specialize (H1 A ord (λ j, nth j l d) [] l i).
rewrite Nat.add_0_r in H1.
now apply H1.
Qed.

(* # of transpositions of some permutation p *)
Definition n_transp p :=
  nat_∑ (i = 0, length p), ff_app (snd (bsort_gen Nat.leb p)) i.
(*
Definition n_transp p :=
  iter_seq 0 (length p - 1)
    (λ c i, c + ff_app (snd (bsort_gen Nat.leb p)) i) 0.
Definition n_transp p :=
  iter_list (seq 0 (length p))
    (λ c i, c + ff_app (snd (bsort_gen Nat.leb p)) i) 0.
*)

(*
Theorem ε_sum_n_transp : ∀ p,
  ε p = if n_transp p mod 2 =? 0 then 1%F else (-1)%F.
Proof.
(* je veux démontrer ça pour le sport, mais je sens que ça va être
   du sport ! *)
intros.
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec _ _) as [Hnz| Hnz]. {
  apply Nat.mod_divides in Hnz; [ | easy ].
  destruct Hnz as (k, Hn).
  unfold n_transp in Hn.
  unfold ε.
...
Require Import RnglAlg.Zrl.
Require Import ZArith.
Compute (let p := [12;20;7;9] in
  ε p = if n_transp p mod 2 =? 0 then 1%F else (-1)%F).
Compute (map (λ p,
  Z.eqb (ε p) (if n_transp p mod 2 =? 0 then 1%F else (-1)%F)
) (canon_sym_gr_list_list 5)).
Check Z.eqb.
...
*)

(*
Theorem permut_transp_list : ∀ p,
  is_permut_list p
  → p = Comp (length p) (t ∈ transp_list p), swap (length p) (fst t) (snd t).
Proof.
intros * Hp.
unfold transp_list.
unfold iter_list.
unfold iter_seq, iter_list.
rewrite Nat.sub_0_r.
...
Print bsort_gen_insert.
Compute (bsort_gen Nat.leb [20;9;12;7]).
Compute (bsort_gen Nat.leb [20;12;7;9]).
Print ε.
Require Import RnglAlg.Zrl.
Require Import ZArith.
Compute (let p := [12;20;7;9] in (bsort_gen Nat.leb p, ε p)).
Compute (let p := [20;12;7;9] in (bsort_gen Nat.leb p, ε p)).
Compute (let p := [20;9;12;7] in (bsort_gen Nat.leb p, ε p)).
Compute (let p := [20;9;12;7;5;22;3;0;18] in (bsort_gen Nat.leb p, ε p)).
Compute (let p := [20;0;12;7;5;22;3;9;18] in (bsort_gen Nat.leb p, ε p)).
...
Compute (bsort_gen Nat.leb [12;20;7;9]).
     = ([2; 3; 0; 1], [0; 1; 0; 1])
(0-0)+(1-1)+(2-0)+(3-1)=4 transpositions
12;7;20;9  7;12;20;9  7;12;9;20  7;9;12;20
map2 (λ a t,
...
bsort ord p = f (snd (bsort_gen ord p)) ?
bsort_rank ord p = f (snd (bsort_gen ord p)) ?
...
Compute (bsort_gen Nat.leb [3;2;0;1]).
Compute (bsort_gen Nat.leb [1;2;0;3]).
Compute (map (λ l, (l, snd (bsort_gen Nat.leb l))) (canon_sym_gr_list_list 4)).
Compute (map (λ l, (l, bsort_gen Nat.leb l)) (canon_sym_gr_list_list 3)).
Compute (map (λ l, (l, bsort_gen Nat.leb l)) (canon_sym_gr_list_list 5)).
...
intros * Hp.
unfold iter_list.
remember (length p) as n eqn:Hn; symmetry in Hn.
revert p Hp Hn.
induction n; intros. {
  now apply length_zero_iff_nil in Hn; subst p.
}
rewrite seq_S.
cbn - [ swap ].
unfold transp_list.
(* oh putain... *)
...
Compute (let p := [3;2;0;1] in
  p = Comp (length p) (t ∈ transp_list p), swap (length p) (fst t) (snd t)).
Compute (map (λ p,
  list_eqb Nat.eqb p (Comp (length p) (t ∈ transp_list p), swap (length p) (fst t) (snd t))
) (canon_sym_gr_list_list 5)).
...
Compute (transp_list [20;12;7;9]).
Compute (transp_list [3;2;0;1]).
Compute (map (λ l, (l, transp_list l)) (canon_sym_gr_list_list 4)).
...
intros * Hp.
unfold iter_list.
remember (length p) as n eqn:Hn; symmetry in Hn.
revert p Hp Hn.
induction n; intros. {
  now apply length_zero_iff_nil in Hn; subst p.
}
rewrite seq_S.
cbn - [ swap ].
...
now apply permut_transp_loop.
...
Compute
  (map (λ p, list_eqb Nat.eqb p (iter_list (transp_list p) (λ c t, swap (length p) t ° c) (seq 0 (length p))))) (canon_sym_gr_list_list 4).
Check
  (map (λ p, list_eqb Nat.eqb p (iter_list (transp_list p) (λ c t, swap (length p) t ° c) (seq 0 (length p))))) (canon_sym_gr_list_list 4).
...
...
enough (Hpt : p = Comp n (t ∈ transp_list p), swap n (fst t) (snd t)).
*)

Theorem ε_swap_id : ∀ n k, ε (swap n k k) = 1%F.
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  unfold swap, ε; cbn.
  unfold iter_seq, iter_list; cbn.
  now do 2 rewrite rngl_mul_1_l.
}
unfold swap, list_swap_elem.
rewrite seq_length.
unfold ε; cbn - [ "<?" ].
rewrite List_map_seq_length.
unfold sign_diff.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    unfold transposition, ff_app.
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hj Hnz ].
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hi Hnz ].
    rewrite (@seq_nth _ _ j); [ | flia Hj Hnz ].
    rewrite (@seq_nth _ _ i); [ | flia Hi Hnz ].
    do 2 rewrite Nat.add_0_l.
    do 2 rewrite fold_transposition.
    do 2 rewrite transposition_refl.
    rewrite seq_nth; [ | flia Hj Hnz ].
    rewrite seq_nth; [ | flia Hi Hnz ].
    do 2 rewrite Nat.add_0_l.
    replace (if _ <? _ then _ else _) with 1%F. 2: {
      symmetry.
      rewrite if_ltb_lt_dec.
      destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
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
(*
  now rewrite butn_nil.
*)
(*
  rewrite <- map_butn.
  rewrite (@List_map_const_is_repeat _ _ 0%F). 2: {
    intros; apply List_nth_nil.
  }
  symmetry.
  rewrite (@List_map_const_is_repeat _ _ 0%F). 2: {
    intros; apply List_nth_nil.
  }
  f_equal.
  rewrite butn_length.
  do 2 rewrite seq_length.
  rewrite square_matrix_ncols; [ | easy ].
  cbn - [ "<?" ].
  rewrite Hr.
  apply Nat.lt_succ_r, Nat.ltb_lt in Hk.
  rewrite Hk, Nat_sub_succ_1.
  rewrite square_matrix_ncols. 2: {
    apply is_square_matrix_map with (n := n). {
      cbn; rewrite butn_length, Hr; cbn.
      rewrite Nat.leb_refl; cbn.
      now rewrite Nat.sub_0_r.
    }
    intros la Hla; rewrite butn_length.
    apply in_butn in Hla.
    apply is_scm_mat_iff in Hsm.
    cbn in Hsm.
    destruct Hsm as (Hcr, Hc).
    rewrite Hc; [ | easy ].
    now rewrite Hr, Hk, Nat_sub_succ_1.
  }
  cbn; rewrite map_length, butn_length, Hr; cbn.
  rewrite Nat.leb_refl; cbn.
  now rewrite Nat.sub_0_r.
*)
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
(**)
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
(*
now rewrite Nat.add_0_r.
*)
(*
symmetry.
rewrite <- map_butn.
rewrite square_matrix_ncols; [ cbn | easy ].
rewrite square_matrix_ncols. 2: {
  apply Nat.lt_succ_r, Nat.ltb_lt in Hk.
  apply is_square_matrix_map with (n := n). {
    cbn; rewrite butn_length, Hr; cbn.
    rewrite Nat.leb_refl; cbn.
    now rewrite Nat.sub_0_r.
  }
  intros la Hla; rewrite butn_length.
  apply in_butn in Hla.
  apply is_scm_mat_iff in Hsm.
  cbn in Hsm.
  destruct Hsm as (Hcr, Hc).
  rewrite Hc; [ | easy ].
  now rewrite Hr, Hk, Nat_sub_succ_1.
}
cbn; rewrite map_length, butn_length, Hr; cbn.
rewrite Nat.leb_refl; cbn.
rewrite Nat.sub_0_r.
rewrite cons_seq.
rewrite map_butn_seq.
apply Nat.lt_succ_r, Nat.ltb_lt in Hk.
rewrite Hk, Nat_sub_succ_1.
apply map_ext_in.
intros u v.
rewrite Nat.add_0_l, Nat.add_0_r.
now rewrite nth_butn.
*)
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

Theorem collapse_iter_list_transp : ∀ l,
  collapse l =
  iter_list (transp_list l) (λ l t, swap (length l) (fst t) (snd t) ° l)
    (seq 0 (length l)).
Proof.
intros.
destruct (Nat.eq_dec (length l) 0) as [Hlz| Hlz]. {
  now apply length_zero_iff_nil in Hlz; subst l.
}
unfold iter_list.
unfold transp_list, iter_seq, iter_list.
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | now apply Nat.neq_0_lt_0 ].
rewrite Nat_sub_succ_1.
(*
Theorem glop : ∀ A B C (f : A → B → A) (g : list B → C → list B) a lb lc,
  fold_left f (fold_left g lc lb) a = a.
Proof.
intros.
...
(* en fait, je ne sais pas ce que devient lb ; ici, il démarre à [] et
   se remplit petit à petit *)
(* pas sûr qu'on puisse fusionner les deux fold_left *)
*)

(* sort by selection *)

Fixpoint min_in_list {A} (ord : A → A → bool) a la :=
  match la with
  | [] => (a, [])
  | b :: lb =>
      let (c, lc) := min_in_list ord (if ord a b then a else b) lb in
      (c, (if ord a b then b else a) :: lc)
  end.

Fixpoint ssort_loop {A} (ord : A → A → bool) it l :=
  match it with
  | 0 => l
  | S it' =>
      match l with
      | [] => []
      | a :: la =>
          let (a', la') := min_in_list ord a la in
          a' :: ssort_loop ord it' la'
      end
  end.

Definition ssort {A} (ord : A → _) l := ssort_loop ord (length l) l.

(*
Compute (ssort Nat.leb [3;2;1;7]).
Compute (map (λ l, (bsort Nat.leb l, ssort Nat.leb l)) (canon_sym_gr_list_list 4)).
*)

(* bubble sort *)

Fixpoint bbsort_swap {A} (ord : A → A → bool) it l :=
  match it with
  | 0 => (l, false)
  | S it' =>
      match l with
      | [] | [_] => (l, false)
      | a :: b :: l' =>
          let (l'', modif) :=
            bbsort_swap ord it' ((if ord a b then b else a) :: l')
          in
          if ord a b then (a :: l'', modif)
          else (b :: l'', true)
      end
  end.

Fixpoint bbsort_loop {A} (ord : A → A → bool) it l :=
  match it with
  | 0 => l
  | S it' =>
      let (l', modif) := bbsort_swap ord (length l) l in
      if modif then bbsort_loop ord it' l' else l'
  end.

Definition bbsort {A} (ord : A → _) l := bbsort_loop ord (length l) l.

Compute (bbsort Nat.leb [3;2;1;7]).
Compute (map (λ l, (bsort Nat.leb l, bbsort Nat.leb l)) (canon_sym_gr_list_list 04)).

...
rewrite glop.
specialize glop as H1.
specialize (H1 nat).
specialize (H1 (nat * nat)%type).
specialize (H1 (λ (l0 : list nat) (t : nat * nat), swap (length l0) (fst t) (snd t) ° l0)).
specialize (H1 (λ (t : list (nat * nat)) (n : nat), t ++ transp_of_pos n (ff_app (snd (bsort_gen Nat.leb l)) n))).
...
Print transp_list.
Print transp_of_pos.
Search bsort_gen.
Compute (bsort_gen Nat.leb [3;2;0;1]).
Compute (bsort_gen Nat.leb [1;2;0;3]).
Compute (map (λ l, (l, snd (bsort_gen Nat.leb l))) (canon_sym_gr_list_list 4)).
Compute (map (λ l, (l, bsort_gen Nat.leb l)) (canon_sym_gr_list_list 3)).
Compute (map (λ l, (l, bsort_gen Nat.leb l)) (canon_sym_gr_list_list 5)).
...
remember (length l) as n eqn:Hn; symmetry in Hn.
revert l Hn.
induction n; intros. {
  now apply length_zero_iff_nil in Hn; subst l.
}
rewrite seq_S; cbn.
Search (fold_left _ _ (_ ++ _)).
Search (fold_left _ _ _ + _)%F.
...
(* ça a l'air bon
Compute (let p := [2;8;1;7] in
  collapse p =
  iter_list (transp_list p) (λ l t, swap (length p) (fst t) (snd t) ° l)
    (seq 0 (length p))).
Compute (
map (λ p,
  list_eqb Nat.eqb p
    (iter_list (transp_list p) (λ l t, swap (length p) (fst t) (snd t) ° l)
      (seq 0 (length p)))) (canon_sym_gr_list_list 5)).
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
