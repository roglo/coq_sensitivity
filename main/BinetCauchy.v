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
Definition mat_with_rows (jl : list nat) (M : matrix T) :=
  mk_mat (map (λ j, nth j (mat_list_list M) []) jl).

(*
End a.
Require Import RnglAlg.Nrl.
Print mat_with_rows.
Compute (let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1];[18;3;2;1]] in mat_with_rows [0;2;3] M).
...
*)

(* submatrix with list cols jl *)
Definition mat_with_cols (jl : list nat) (M : matrix T) :=
  mk_mat (map (λ i, map (λ j, mat_el M i j) jl) (seq 0 (mat_nrows M))).

Definition mat_with_cols' (jl : list nat) (M : matrix T) :=
  ((mat_with_rows jl M⁺)⁺)%M.

(*
End a.
Require Import RnglAlg.Nrl.
Print mat_with_cols.
About mat_with_cols.
Arguments mat_with_cols {T}%type {ro} jl%list M%M.
Arguments mat_with_cols' {T}%type {ro} jl%list M%M.
Compute (let jl := [0;2;3] in let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1];[18;3;2;1];[8;7;6;5]] in mat_with_cols jl M = mat_with_cols' jl M).
Compute (let jl := [] in let M := mk_mat [[3;7;4;1];[0;6;2;7];[1;3;1;1];[18;3;2;1];[8;7;6;5]] in mat_with_cols jl M = mat_with_cols' jl M).
(* conclusion: la première version se comporte mal si jl=[] ; faut-il donc
   préférer absolument la version avec la transposée ? sachant que bon,
   faudra se la taper dans les preuves, en double exemplaire, ici, en
   plus ? *)
...
*)

(*
Theorem map_with_cols_cols' : ∀ M jl,
  mat_with_cols jl M = mat_with_cols' jl M.
Proof.
intros.
destruct (Nat.eq_dec (length jl) 0) as [Hjz| Hjz]. {
  apply length_zero_iff_nil in Hjz; subst jl.
  unfold mat_with_cols, mat_with_cols', mat_with_rows; cbn.
...
unfold mat_with_cols, mat_with_cols', mat_with_rows, mat_transp, mat_ncols.
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

Theorem mat_with_rows_nrows : ∀ A kl,
  mat_nrows (mat_with_rows kl A) = length kl.
Proof.
intros.
now cbn; rewrite map_length.
Qed.

Theorem mat_with_rows_is_square : ∀ kl A,
  is_correct_matrix A = true
  → mat_ncols A = length kl
  → (∀ k, k ∈ kl → k < mat_nrows A)
  → is_square_matrix (mat_with_rows kl A) = true.
Proof.
intros * Ha Hra Hkc.
destruct (Nat.eq_dec (length kl) 0) as [Hnz| Hnz]. {
  apply length_zero_iff_nil in Hnz; subst kl; cbn in Hra.
  now cbn; rewrite iter_list_empty.
}
apply is_scm_mat_iff.
apply is_scm_mat_iff in Ha.
destruct Ha as (Hcra, Hcla).
split. {
  rewrite mat_with_rows_nrows.
  unfold mat_ncols; cbn.
  intros Hc.
  destruct kl as [| k]; [ easy | exfalso ].
  clear Hnz; cbn in Hra, Hc.
  rewrite Hcla in Hc. 2: {
    apply nth_In.
    rewrite fold_mat_nrows.
    now apply Hkc; left.
  }
  congruence.
} {
  intros l Hl.
  rewrite mat_with_rows_nrows.
  cbn in Hl.
  apply in_map_iff in Hl.
  destruct Hl as (a & Hal & Ha).
  subst l.
  rewrite Hcla; [ easy | ].
  apply nth_In; rewrite fold_mat_nrows.
  now apply Hkc.
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

(* kl is not necessarily in order *)
Theorem det_with_rows : in_charac_0_field →
  ∀ m n A kl,
  mat_nrows A = n
  → mat_ncols A = m
  → is_correct_matrix A = true
  → NoDup kl
  → length kl = m
  → (∀ k, k ∈ kl → k < n)
  → det (mat_with_rows kl A) =
       (ε kl * det (mat_with_rows (bsort Nat.leb kl) A))%F.
Proof.
intros Hif * Hra Hca Ha Hnkl Hklm Hkn.
rewrite det_is_det_by_canon_permut; try now destruct Hif. 2: {
  apply mat_with_rows_is_square; [ easy | now rewrite Hklm | ].
  intros k Hk; rewrite Hra.
  now apply Hkn.
}
rewrite det_is_det_by_canon_permut; try now destruct Hif. 2: {
  apply mat_with_rows_is_square; [ easy | | ]. {
    rewrite length_bsort.
    congruence.
  }
  intros k Hk; rewrite Hra.
  apply Hkn.
  now apply in_bsort in Hk.
}
unfold det'.
rewrite mat_with_rows_nrows, Hklm.
rewrite mat_with_rows_nrows.
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
remember (collapse kl) as p eqn:Hp.
(**)
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
    apply bsort_rank_is_permut.
    now rewrite comp_length, length_bsort_rank, Hp, length_collapse.
  }
  rewrite (permut_bsort_rank_comp m); cycle 1. {
    apply NoDup_bsort_rank.
  } {
    now rewrite length_bsort_rank, length_canon_sym_gr_list.
  } {
    apply bsort_rank_is_permut.
    now rewrite Hp, length_collapse.
  }
  rewrite (permut_comp_assoc m); cycle 1. {
    do 2 rewrite length_bsort_rank.
    now rewrite Hp, length_collapse.
  } {
    apply bsort_rank_is_permut.
    now rewrite length_bsort_rank, length_canon_sym_gr_list.
  }
  rewrite permut_comp_bsort_rank_r; [ | apply bsort_rank_is_permut_list ].
  rewrite length_bsort_rank, Hp, length_collapse, Hklm.
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
      apply bsort_rank_is_permut.
      now rewrite Hp, length_collapse.
    }
    rewrite permut_bsort_rank_involutive. 2: {
      rewrite Hp.
      apply collapse_is_permut.
    }
    rewrite permut_bsort_rank_involutive. 2: {
      now apply canon_sym_gr_list_is_permut_list.
    }
    apply canon_sym_gr_list_inv_ub.
    apply comp_is_permut. {
      rewrite Hp.
      split; [ apply collapse_is_permut | ].
      now rewrite length_collapse.
    }
    now apply canon_sym_gr_list_is_permut.
  }
  unfold g at 1.
  rewrite permut_in_canon_sym_gr_of_its_rank. 2: {
    apply comp_is_permut. {
      apply bsort_rank_is_permut.
      now rewrite Hp, length_collapse.
    } {
      now apply canon_sym_gr_list_is_permut.
    }
  }
  rewrite (permut_comp_assoc m); cycle 1. {
    now rewrite length_bsort_rank, Hp, length_collapse.
  } {
    now apply canon_sym_gr_list_is_permut.
  }
  rewrite comp_bsort_rank_r.
  rewrite permut_bsort_leb. 2: {
    rewrite Hp.
    apply collapse_is_permut.
  }
  rewrite comp_1_l. 2: {
    intros j Hj.
    rewrite Hp, length_collapse, Hklm.
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
    apply bsort_rank_is_permut.
    now rewrite comp_length, length_bsort_rank, Hp, length_collapse.
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
set
  (g' := λ j,
   ff_app (canon_sym_gr_inv_list m i ° p ° canon_sym_gr_list m i) j).
remember (λ i, i + 27) as h'.
erewrite rngl_product_change_var with (g0 := g') (h0 := h').
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hmz ].
rewrite Nat_sub_succ_1.
rewrite rngl_product_list_permut with (l2 := seq 0 m).
rewrite rngl_product_seq_product; [ | easy ].
rewrite Nat.add_0_l.
apply rngl_product_eq_compat.
intros j (_, Hj).
unfold mat_with_rows, mat_el.
cbn.
unfold ff_app.
f_equal.
do 2 rewrite fold_ff_app.
unfold g.
rewrite permut_in_canon_sym_gr_of_its_rank.
unfold "°".
unfold ff_app.
rewrite (List_map_nth' 0).
do 3 rewrite fold_ff_app.
unfold g'.
unfold "°".
unfold ff_app.
rewrite (List_map_nth' 0).
rewrite (List_map_nth' 0).
repeat rewrite fold_ff_app.
rewrite canon_sym_gr_sym_gr_inv.
rewrite permut_bsort_permut.
...
Search (ff_app (bsort_rank _ _)).
rewrite permut_bsort_permut.

rewrite <- fold_comp_list.
rewrite permut_bsort_rank_involutive.
Search (ff_app (canon_sym_gr_list _ _)).
...
Search (ff_app (canon_sym_gr_list _ _)).
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
   (mat_with_rows (bsort Nat.leb kl) A)
      (?g i0)
must be the same row as
   (mat_with_rows kl A)
      i0
...
rewrite rngl_product_change_var with
  (g0 := ff_app (bsort_rank Nat.leb p)) (h0 := ff_app (bsort_rank Nat.leb p)). 2: {
  admit.
}
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hmz ].
rewrite Nat_sub_succ_1.
(* pour voir... *)
erewrite rngl_product_list_eq_compat. 2: {
  intros j Hj.
  unfold mat_with_rows, mat_el.
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
unfold mat_with_rows.
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
     det (mat_with_cols jl A) * det (mat_with_rows jl B).
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
Search (det (mat_with_rows _ _)).
(* https://proofwiki.org/wiki/Cauchy-Binet_Formula *)
Print det'.
Check det_with_rows.
Search (det (mat_with_rows _ _)).
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
Arguments mat_with_cols {T}%type {ro} jl%list.
Compute (let A := mk_mat [[3;4;1];[0;6;7];[1;3;1]] in let jl := [0;2]%nat in mat_with_rows jl A).
Compute (let A := mk_mat [[3;4;1];[0;6;7];[1;3;1]] in let B := mk_mat [[0;6;7];[1;3;1];[3;2;1]] in let m := mat_nrows A in let n := mat_ncols A in (det (A * B), ∑ (jl ∈ sub_lists_of_seq_0_n n m), det (mat_with_cols jl A) * det (mat_with_rows jl B), det A * det B)).
Compute (let B := mk_mat [[3;4];[2;6];[1;3]] in let A := mk_mat [[1;6;7];[1;3;1]] in let m := mat_nrows A in let n := mat_ncols A in (det (A * B), ∑ (jl ∈ sub_lists_of_seq_0_n n m), det (mat_with_cols jl A) * det (mat_with_rows jl B), det A * det B, m, n, sub_lists_of_seq_0_n n m)).
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
