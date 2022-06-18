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

Require Import Utf8 Arith.
Import List List.ListNotations Init.Nat.

Require Import Misc PermutationFun SortingFun RingLike.
Require Import IterAdd IterMul IterAnd Pigeonhole.
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

Theorem binomial_0_r : ∀ n, binomial n 0 = 1.
Proof. now intros; induction n. Qed.

Theorem binomial_1_r : ∀ n, binomial n 1 = n.
Proof.
intros.
induction n; [ easy | cbn ].
now rewrite IHn, binomial_0_r.
Qed.

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
  sorted Nat.ltb (a :: l)
  → i < length l
  → a = nth i l 0
  → False.
Proof.
intros * Hsort Hil Ha.
destruct l as [| b]; [ cbn in Hil; flia Hil | ].
apply sorted_cons_cons_true_iff in Hsort.
destruct Hsort as (Hab & Hs).
apply Nat.ltb_lt in Hab.
destruct i; [ cbn in Ha; flia Hab Ha | cbn in Ha ].
specialize (sorted_extends Nat_ltb_trans Hs a) as H1.
cbn in Hil.
apply Nat.succ_lt_mono in Hil.
assert (H : a ∈ l) by now subst a; apply nth_In.
specialize (H1 H).
apply Nat.ltb_lt in H1.
flia Hab H1.
Qed.

Theorem nth_of_rank_of_sub_list_of_seq_0_n : ∀ n k t,
  sorted Nat.ltb t
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
Definition mat_select_rows (jl : list nat) (M : matrix T) :=
  mk_mat (map (λ i, map (λ j, mat_el M i j) (seq 1 (mat_ncols M))) jl).

(* submatrix with list cols jl *)
Definition mat_select_cols (jl : list nat) (M : matrix T) :=
  ((mat_select_rows jl M⁺)⁺)%M.

End a.

Arguments mat_select_rows {T ro} jl%list M%M.
Arguments mat_select_cols {T ro} jl%list M%M.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

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
  → ∀ l, l ∈ ll → sorted Nat.ltb l.
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
  unfold sorted; cbn.
  rewrite Bool.andb_true_r.
  now apply Nat.ltb_lt, H1; left.
}
cbn in IHl |-*.
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
  specialize (sorted_extends Nat_ltb_trans H1 a Hal) as H2.
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
  → (∀ l, l ∈ ll → sorted Nat.ltb l) ∧
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
intros; cbn.
apply map_length.
Qed.

Theorem mat_select_rows_ncols : ∀ (A : matrix T) kl,
  kl ≠ []
  → mat_ncols (mat_select_rows kl A) = mat_ncols A.
Proof.
intros * Hkl; cbn.
destruct kl as [| k]; [ easy | ].
now cbn; rewrite List_map_seq_length.
Qed.

Theorem mat_select_cols_nrows : ∀ (A : matrix T) kl,
  kl ≠ []
  → mat_ncols A ≠ 0
  → mat_nrows (mat_select_cols kl A) = mat_nrows A.
Proof.
intros * Hlk Hcz; cbn.
rewrite List_map_seq_length.
rewrite mat_select_rows_ncols; [ | easy ].
rewrite mat_transp_ncols.
now apply Nat.eqb_neq in Hcz; rewrite Hcz.
Qed.

Theorem mat_select_rows_is_square : ∀ kl (A : matrix T),
  is_correct_matrix A = true
  → mat_ncols A = length kl
  → (∀ k, k ∈ kl → 1 ≤ k ≤ mat_nrows A)
  → is_square_matrix (mat_select_rows kl A) = true.
Proof.
intros * Ha Hca Hkc.
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
  clear Hnz; cbn in Hc.
  rewrite List_map_seq_length in Hc.
  now rewrite Hca in Hc.
} {
  intros l Hl.
  rewrite mat_select_rows_nrows.
  cbn in Hl.
  apply in_map_iff in Hl.
  destruct Hl as (a & Hal & Ha).
  subst l.
  now rewrite List_map_seq_length.
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
  symmetry in Hca; apply length_zero_iff_nil in Hca; subst kl.
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

Theorem det_mat_swap_rows_with_rows : in_charac_0_field →
  ∀ p q A jl,
  is_correct_matrix A = true
  → (∀ k, k ∈ jl → 1 ≤ k ≤ mat_nrows A)
  → mat_ncols A = length jl
  → 1 ≤ p ≤ length jl
  → 1 ≤ q ≤ length jl
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

(* *)

(* which transpositions to do for transforming {0..n-1} into p *)
Definition nat_transp_list p := transp_list Nat.eqb (seq 0 (length p)) p.

(* à voir
Inductive Member A : A → list A → Prop :=
  | ext_hd : ∀ a l, Member a (a :: l)
  | ext_tl : ∀ a b l, a ≠ b → Member a l → Member a (b :: l).

Inductive Transposition A : list A → list A → A → A → Prop :=
  | transp_1 :
      ∀ a b c la lb, Transposition la lb b c → Transposition (a :: la) (a :: lb) b c
  | transp_2 :
      ∀ a b la lb,
      a ≠ b
      → Member b (a :: la)
      → Member a (b :: lb)
      → Transposition (a :: la) (b :: lb) a b.

Example transposition_1 : Transposition [1;2;3] [1;3;2] 2 3.
Proof.
constructor.
constructor; [ easy | | ]. {
  constructor; [ easy | constructor ].
} {
  constructor; [ easy | constructor ].
}
Qed.

Example transposition_2 : Transposition [1;2;3] [2;1;3] 1 2.
Proof.
constructor; [ easy | | ]. {
  constructor; [ easy | constructor ].
} {
  constructor; [ easy | constructor ].
}
Qed.

Example transposition_3 : Transposition [1;2;3] [2;3;1] 1 2.
Proof.
constructor; [ easy | | ]. {
  constructor; [ easy | constructor ].
} {
  constructor; [ easy | constructor ].

}
Qed.
*)

(*
Compute (transp_list Nat.eqb [3;2;1] [1;2;3]).
Print transp_loop.
Compute (transp_list Nat.eqb [1;2;0] [0;1;2]).
Compute (map (λ la, (la, seq 0 (length la), transp_list Nat.eqb la (seq 0 (length la)))) (canon_sym_gr_list_list 3)).
Compute (map (λ lb, (seq 0 (length lb), lb, transp_list Nat.eqb (seq 0 (length lb)) lb)) (canon_sym_gr_list_list 3)).
Compute (map (λ lb, (seq 0 (length lb), lb, transp_list Nat.eqb (seq 0 (length lb)) lb)) (canon_sym_gr_list_list 4)).
Compute (map (λ lb, length (transp_list Nat.eqb (seq 0 (length lb)) lb)) (canon_sym_gr_list_list 5)).

Fixpoint nb_nfit i l :=
  match l with
  | [] => 0
  | j :: l' => (if i =? j then 0 else 1) + nb_nfit (S i) l'
  end.

Fixpoint transp_loop' it i (p : list nat) :=
  match it with
  | 0 => []
  | S it' =>
      match p with
      | [] => []
      | j :: l =>
          if i =? j then transp_loop' it' (S i) l
          else (i, j) :: transp_loop' it' i (list_swap_elem 0 p 0 (j - i))
      end
  end.

(* works only if p is a permutation of {0..n-1} *)
Definition transp_list' p := transp_loop' (length p + nb_nfit 0 p) 0 p.

Compute (map (λ p, (p, nat_transp_list p, transp_list' p)) (canon_sym_gr_list_list 3)).
(* ([1; 2; 0], [(0, 1); (1, 2)], [(0, 1); (0, 2)]) *)
Compute (map (λ p, (p, rev (nat_transp_list p), transp_list' p)) (canon_sym_gr_list_list 3)).
(* ([1; 2; 0], [(1, 2); (0, 1)], [(0, 1); (0, 2)]) *)
Compute (map (λ p, (p, transp_list Nat.eqb p (seq 0 (length p)), transp_list' p)) (canon_sym_gr_list_list 3)).
(* ([1; 2; 0], [(0, 2); (1, 2)], [(0, 1); (0, 2)]) *)
Compute (map (λ p, (p, rev (transp_list Nat.eqb p (seq 0 (length p))), transp_list' p)) (canon_sym_gr_list_list 3)).
(* ([1; 2; 0], [(1, 2); (0, 2)], [(0, 1); (0, 2)]) *)
...
*)

Notation "'Comp' n ( i ∈ l ) , g" :=
  (iter_list l (λ c i, c ° g) (seq 0 n))
  (at level 35, i at level 0, l at level 60, n at level 0).

(* seems to work; property to prove:
Compute (map (λ p, (p, Comp (length p) (ij ∈ nat_transp_list p), swap (length p) (fst ij) (snd ij))) (canon_sym_gr_list_list 4)).
Compute (map (λ p, list_eqb Nat.eqb p (Comp (length p) (ij ∈ nat_transp_list p), swap (length p) (fst ij) (snd ij))) (canon_sym_gr_list_list 5)).
*)

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
Theorem transp_loop_nil : ∀ it i, transp_loop it i [] = [].
Proof. intros; now destruct it. Qed.
*)

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
  rewrite List_app_cons, app_assoc, <- seq_S; cbn.
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
*)

Theorem list_swap_elem_id : ∀ A (d : A) l i, list_swap_elem d l i i = l.
Proof.
intros.
unfold list_swap_elem.
rewrite List_map_nth_seq with (d := d).
apply map_ext_in.
intros j Hj.
now rewrite transposition_id.
Qed.

Theorem List_fold_left_max : ∀ a b la lb,
  a ≤ b
  → Max (i ∈ la), i ≤ Max (i ∈ lb), i
  → fold_left max la a ≤ fold_left max lb b.
Proof.
intros * Hab Hm.
unfold iter_list in Hm.
rewrite List_fold_left_ext_in with (g := max) in Hm by easy.
rewrite List_fold_left_ext_in with (g := max) (l := lb) in Hm by easy.
rewrite fold_left_max_from_0.
rewrite fold_left_max_from_0 with (l := lb).
now apply Nat.max_le_compat.
Qed.

Theorem le_fold_left_max : ∀ a b la,
  a ≤ b ∨ (∃ c, c ∈ la ∧ a ≤ c)
  ↔ a ≤ fold_left max la b.
Proof.
intros.
split. {
  intros Hab.
  revert a b Hab.
  induction la as [| c]; intros. {
    destruct Hab as [Hab| Hab]; [ easy | ].
    now destruct Hab.
  }
  cbn.
  apply IHla.
  destruct Hab as [Hab| Hab]. {
    left.
    transitivity b; [ easy | ].
    apply Nat.le_max_l.
  }
  destruct Hab as (d & Hd & Had).
  destruct Hd as [Hd| Hd]. {
    subst d; left.
    transitivity c; [ easy | ].
    apply Nat.le_max_r.
  }
  right.
  now exists d.
} {
  intros Hab.
  revert a b Hab.
  induction la as [| c]; intros; [ now left | ].
  cbn in Hab.
  apply IHla in Hab.
  destruct Hab as [Hab| Hab]. {
    destruct (le_dec b c) as [Hbc| Hbc]. {
      rewrite Nat.max_r in Hab; [ | easy ].
      right.
      exists c.
      split; [ now left | easy ].
    }
    apply Nat.nle_gt, Nat.lt_le_incl in Hbc.
    rewrite Nat.max_l in Hab; [ | easy ].
    now left.
  }
  destruct Hab as (d & Hd & Had).
  right.
  exists d.
  split; [ now right | easy ].
}
Qed.

Theorem fold_left_max_le : ∀ a b la,
  (∀ c, c ∈ a :: la → c ≤ b)
  → fold_left max la a ≤ b.
Proof.
intros * Hc.
revert a Hc.
induction la as [| d]; intros; [ now apply Hc; left | cbn ].
apply IHla.
intros c Hcad.
destruct Hcad as [Hcad| Hcla]. {
  subst c.
  apply Hc.
  destruct (le_dec a d) as [H1| H1]. {
    rewrite Nat.max_r; [ | easy ].
    now right; left.
  }
  apply Nat.nle_gt, Nat.lt_le_incl in H1.
  rewrite Nat.max_l; [ | easy ].
  now left.
}
apply Hc.
now right; right.
Qed.

(*
Theorem in_transp_loop_bounds : ∀ it k l i j,
  (i, j) ∈ transp_loop it k l
  → k ≤ i < k + length l ∧ j ≤ Max (u ∈ l), u.
Proof.
intros * Hij.
revert i j k l Hij.
induction it; intros; [ easy | cbn in Hij ].
destruct l as [| v]; [ easy | ].
rewrite if_eqb_eq_dec in Hij.
destruct (Nat.eq_dec k v) as [Hkv| Hkv]. {
  subst v.
  specialize (IHit _ _ _ _ Hij) as H1.
  destruct H1 as ((H1, H2), H3).
  rewrite Nat.add_succ_comm in H2.
  split. {
    split; [ | easy ].
    destruct (Nat.eq_dec (S k) i) as [Hkij| Hkij]; [ | flia H1 Hkij ].
    rewrite <- Hkij.
    apply Nat.le_succ_diag_r.
  }
  rewrite iter_list_cons'.
  etransitivity; [ apply H3 | ].
  unfold iter_list at 2.
  rewrite fold_left_max_from_0.
  rewrite fold_iter_list.
  apply Nat.le_max_r.
}
destruct Hij as [Hij| Hij]. {
  injection Hij; clear Hij; intros; subst k v; cbn.
  split. {
    split; [ easy | flia ].
  }
  rewrite iter_list_cons'.
  unfold iter_list.
  rewrite fold_left_max_from_0.
  rewrite fold_iter_list.
  apply Nat.le_max_l.
}
specialize (IHit _ _ _ _ Hij) as H1.
destruct H1 as (H1, H2).
split. {
  now rewrite list_swap_elem_length in H1.
}
etransitivity; [ apply H2 | ].
unfold iter_list.
rewrite List_fold_left_ext_in with (g := max) by easy.
remember (fold_left max (list_swap_elem _ _ _ _) _) as x.
rewrite List_fold_left_ext_in with (g := max) by easy; subst x.
remember (v :: l) as l'.
remember (v - k) as x.
clear; rename l' into l.
rename x into i.
assert (H : ∀ i a l,
  fold_left max (list_swap_elem 0 l 0 i) a ≤ fold_left max l a). {
  clear l i.
  intros.
  apply fold_left_max_le.
  intros * Hc.
  destruct Hc as [Hc| Hc]. {
    subst c.
    now apply le_fold_left_max; left.
  }
  unfold list_swap_elem in Hc.
  apply in_map_iff in Hc.
  destruct Hc as (b & Hbc & Hb).
  apply in_seq in Hb; destruct Hb as (_, Hb); cbn in Hb.
  subst c.
  destruct (lt_dec i (length l)) as [Hil| Hil]. 2: {
    apply Nat.nlt_ge in Hil.
    unfold transposition.
    do 2 rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec b 0) as [Hbz| Hbz]. {
      now rewrite nth_overflow.
    }
    destruct (Nat.eq_dec b i) as [H| H]; [ flia H Hb Hil | ].
    apply le_fold_left_max.
    right.
    exists (nth b l 0).
    split; [ | easy ].
    now apply nth_In.
  }
  apply le_fold_left_max.
  right.
  exists (nth (transposition 0 i b) l 0).
  split; [ | easy ].
  apply nth_In.
  apply transposition_lt; [ flia Hb | easy | easy ].
}
apply H.
Qed.

Theorem in_transp_list_bounds : ∀ i j l,
  (i, j) ∈ transp_list l
  → i < length l ∧ j ≤ Max (u ∈ l), u.
Proof.
intros * Hij.
unfold transp_list in Hij.
specialize (in_transp_loop_bounds) as H1.
specialize (H1 _ _ _ _ _ Hij).
now destruct H1 as ((_, H1), H2).
Qed.
*)

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
    rewrite Nat_succ_sub_succ_r; [ cbn | easy ].
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
      rewrite Nat_succ_sub_succ_r; [ | easy ].
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
      rewrite Nat_succ_sub_succ_r in Huv; [ | easy ].
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
    rewrite Nat_succ_sub_succ_r; [ | flia Hvi Hviz ].
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
    rewrite Nat_succ_sub_succ_r in Huv at 1; [ | flia Hviz ].
    replace (S (v - S i) =? 0) with false in Huv by easy.
    apply Nat.eqb_neq in Hvji; rewrite Hvji in Huv.
    rewrite Nat_succ_sub_succ_r in Huv at 1; [ | flia Hviz ].
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
        rewrite Nat_succ_sub_succ_r in Huv; [ | flia Hviz Hvi ].
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
        rewrite Nat_succ_sub_succ_r in Huv; [ | easy ].
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
      rewrite Nat_succ_sub_succ_r in Huv; [ | flia Hviz ].
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
      rewrite Nat_succ_sub_succ_r in Huv; [ | flia Hui Huiz ].
      rewrite List_nth_succ_cons in Huv.
      destruct (Nat.eq_dec (v - i) 0) as [Hviz| Hviz]. {
        assert (H : v = i) by flia Hviz Hvi; subst v.
        clear Hvi Hviz Hv.
        rewrite (@Nat_succ_sub_succ_r j i) in Huv; [ | easy ].
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
        rewrite (@Nat_succ_sub_succ_r v i) in Huv; [ | flia Hviz ].
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

(*
Theorem nb_nfit_app : ∀ i la lb,
  nb_nfit i (la ++ lb) = nb_nfit i la + nb_nfit (i + length la) lb.
Proof.
intros.
revert i lb.
induction la as [| j]; intros; [ now rewrite Nat.add_0_r | cbn ].
now rewrite IHla, Nat.add_assoc, Nat.add_succ_comm.
Qed.

Theorem permut_eq_iter_list_transp_loop : ∀ l it i,
  is_permut_list (seq 0 i ++ l)
  → length l + nb_nfit i l ≤ it
  → fold_left (λ l t, l ° swap (length l) (fst t) (snd t))
      (transp_loop it i l) (seq 0 i ++ l) = seq 0 (i + length l).
Proof.
intros * Hp Hit.
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
  rewrite List_app_cons, app_assoc, <- seq_S.
  rewrite List_cons_length, <- Nat.add_succ_comm.
  apply IHit; [ now rewrite seq_S, <- app_assoc | easy ].
} {
  remember (list_swap_elem 0 (j :: l) 0 (j - i)) as la eqn:Hla.
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
  move Hji before Hilj.
  assert (Hpa : is_permut_list (seq 0 i ++ la)). {
    rewrite Hla.
    now apply app_seq_swap_is_permut_list.
  }
  specialize (IHit la i Hpa) as H1.
  assert (H : length la + nb_nfit i la ≤ it). {
    rewrite Hla, list_swap_elem_length, List_cons_length.
    rewrite Nat.add_succ_comm.
    etransitivity; [ | apply Hit ].
    apply Nat.add_le_mono_l.
    apply -> Nat.succ_le_mono.
    cbn - [ nth ].
    rewrite <- seq_shift, map_map.
    erewrite map_ext_in. 2: {
      intros u Hu.
      rewrite Nat_succ_sub_succ_r; [ | easy ].
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
  set (g := λ l t, l ° swap (length l) (fst t) (snd t)) in H1 |-*.
  rewrite List_cons_length.
  replace (length la) with (S (length l)) in H1. 2: {
    rewrite Hla.
    now rewrite list_swap_elem_length.
  }
  cbn.
  unfold g at 2.
  rewrite app_length, seq_length.
  cbn.
  unfold "°".
  unfold ff_app.
  enough
    (H : seq 0 i ++ la =
     map (λ i0 : nat, nth i0 (seq 0 i ++ j :: l) 0) (swap (i + S (length l)) i j)). {
    now rewrite <- H.
  }
  symmetry.
  rewrite Hla.
  unfold swap.
  unfold list_swap_elem.
  rewrite map_map.
  rewrite seq_length.
  rewrite List_cons_length.
  rewrite List_seq_cut with (i := i). 2: {
    apply in_seq.
    split; [ easy | ].
    flia.
  }
  rewrite Nat.sub_0_r.
  cbn - [ nth seq ].
  rewrite map_app.
  cbn - [ nth seq ].
  f_equal. {
    rewrite List_map_nth_seq with (d := 0).
    rewrite seq_length.
    apply map_ext_in.
    intros k Hk; apply in_seq in Hk.
    rewrite seq_nth; [ | easy ].
    replace (i + S (length l) - S i) with (length l) by flia Hji.
    rewrite Nat.add_0_l.
    unfold transposition.
    do 2 rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec k i) as [H| H]; [ flia Hk H | clear H ].
    destruct (Nat.eq_dec k j) as [H| H]; [ flia Hk Hilj H | clear H ].
    remember (seq 0 i ++ j :: l) as x.
    rewrite app_nth1; subst x; [ | now rewrite seq_length ].
    rewrite seq_nth; [ | easy ].
    rewrite app_nth1; [ | now rewrite seq_length ].
    now apply seq_nth.
  }
  cbn - [ nth ].
  f_equal. {
    rewrite transposition_1.
    remember (seq 0 i ++ j :: l) as x.
    rewrite app_nth2; subst x. 2: {
      rewrite seq_length.
      now apply Nat.lt_le_incl.
    }
    rewrite seq_length.
    replace (i + S (length l) - S i) with (length l) by flia Hji.
    replace (i :: seq (S i) (length l)) with (seq i (S (length l))) by easy.
    rewrite app_nth2. 2: {
      rewrite seq_length; unfold ge.
      rewrite seq_nth; [ | flia Hji ].
      flia Hilj.
    }
    rewrite seq_length.
    f_equal.
    rewrite seq_nth; [ now rewrite Nat.add_comm, Nat.add_sub | ].
    flia Hji.
  }
  replace (i + S (length l) - S i) with (length l) by flia Hji.
  symmetry.
  rewrite <- seq_shift, map_map.
  symmetry.
  rewrite List_map_seq.
  apply map_ext_in.
  intros k Hk; apply in_seq in Hk; destruct Hk as (_, Hk); cbn in Hk.
  rewrite List_app_cons, app_assoc, <- seq_S, <- seq_app.
  rewrite (Nat.add_succ_comm _ (length l)).
  unfold transposition.
  replace (S k =? 0) with false by easy.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (S i + k) i) as [H| H]; [ flia H | clear H ].
  destruct (Nat.eq_dec (S i + k) j) as [Hsikj| Hsikj]. {
    rewrite seq_nth; [ | flia ].
    rewrite app_nth2; [ | now rewrite seq_length; unfold ge ].
    rewrite seq_length, Nat.sub_diag.
    rewrite List_nth_0_cons.
    rewrite <- Hsikj.
    replace (S i + k - i) with (S k) by flia.
    now rewrite Nat.eqb_refl; cbn.
  }
  rewrite seq_nth. 2: {
    rewrite Nat.add_succ_comm.
    apply Nat.add_lt_mono_l.
    now apply -> Nat.succ_lt_mono.
  }
  rewrite Nat.add_0_l.
  rewrite app_nth2; [ | rewrite seq_length; flia ].
  rewrite seq_length.
  replace (S i + k - i) with (S k) by flia.
  rewrite List_nth_succ_cons.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (S k) (j - i)) as [Hskji| Hskji]. {
    replace k with (j - S i) in Hsikj by flia Hskji.
    now rewrite Nat.add_comm, Nat.sub_add in Hsikj.
  }
  now rewrite List_nth_succ_cons.
}
Qed.

Theorem permut_eq_iter_list_transp : ∀ l,
  is_permut_list l
  → iter_list (transp_list l) (λ l t, l ° swap (length l) (fst t) (snd t)) l =
    seq 0 (length l).
Proof.
intros * Hp.
unfold iter_list.
unfold transp_list.
specialize permut_eq_iter_list_transp_loop as H1.
specialize (H1 l (length l + nb_nfit 0 l) 0).
apply (H1 Hp (le_refl _)).
Qed.
*)

Theorem permut_list_max : ∀ l,
  is_permut_list l
  → Max (i ∈ l), i = length l - 1.
Proof.
intros * Hp.
remember (length l) as n eqn:Hn.
symmetry in Hn.
revert l Hp Hn.
induction n; intros. {
  now apply length_zero_iff_nil in Hn; subst l.
}
rewrite Nat_sub_succ_1.
specialize permut_without_highest as H1.
specialize (H1 n l).
assert (H : is_permut (S n) l) by easy.
specialize (H1 H); clear H.
destruct H1 as (j & Hj & Hjn & Hpj & Hpjl).
specialize (nth_split _ 0 Hj) as H1.
destruct H1 as (l1 & l2 & Hll & Hlj).
rewrite Hjn in Hll.
rewrite Hll.
rewrite max_list_app, max_list_cons.
rewrite (Nat.max_comm n).
rewrite Nat.max_assoc.
rewrite <- max_list_app.
assert (Hb : butn j l = l1 ++ l2). {
  unfold butn.
  rewrite Hll.
  rewrite firstn_app.
  rewrite Hlj, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite <- Hlj, firstn_all.
  rewrite List_app_cons, app_assoc, skipn_app.
  rewrite app_length, Nat.add_1_r, Nat.sub_diag.
  rewrite skipn_O.
  replace (S (length l1)) with (length (l1 ++ [n])). 2: {
    now rewrite app_length, Nat.add_1_r.
  }
  now rewrite skipn_all, app_assoc, app_nil_r.
}
rewrite Hb in Hpj, Hpjl.
rewrite IHn; [ | easy | easy ].
apply Nat.max_r; flia.
Qed.

Theorem list_swap_elem_firstn_skipn : ∀ A (d : A) i j l,
  i < j < length l
  → list_swap_elem d l i j =
     firstn i l ++ [nth j l d] ++
     firstn (j - S i) (skipn (S i) l) ++ [nth i l d] ++ skipn (S j) l.
Proof.
intros * Hij.
unfold list_swap_elem.
replace (length l) with (i + (length l - i)) by flia Hij.
rewrite seq_app, map_app.
f_equal. {
  erewrite map_ext_in. 2: {
    intros k Hk; apply in_seq in Hk; cbn in Hk; destruct Hk as (_, Hk).
    unfold transposition.
    do 2 rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec k i) as [H| H]; [ flia Hk H | clear H ].
    destruct (Nat.eq_dec k j) as [H| H]; [ flia Hij Hk H | clear H ].
    easy.
  }
  assert (Hi : i < length l) by flia Hij.
  clear j Hij.
  symmetry.
  now apply List_firstn_map_nth_seq.
}
rewrite Nat_succ_sub_succ_r; [ | flia Hij ].
cbn - [ skipn ].
f_equal. {
  unfold transposition.
  now rewrite Nat.eqb_refl.
}
replace (length l - S i) with ((j - S i) + (length l - j)) by flia Hij.
rewrite seq_app, map_app.
rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
f_equal. {
  symmetry.
  rewrite List_firstn_map_nth_seq with (d := d). 2: {
    rewrite skipn_length; flia Hij.
  }
  symmetry.
  rewrite <- List_seq_shift', map_map.
  apply map_ext_in.
  intros k Hk; apply in_seq in Hk; cbn in Hk; destruct Hk as (_, Hk).
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (S i + k) i) as [H| H]; [ flia H | clear H ].
  destruct (Nat.eq_dec (S i + k) j) as [H| H]; [ flia H Hk | clear H ].
  now rewrite List_nth_skipn, Nat.add_comm.
}
rewrite <- List_seq_shift', map_map.
rewrite Nat_succ_sub_succ_r; [ | easy ].
cbn - [ skipn ].
rewrite Nat.add_0_r, transposition_2; f_equal.
rewrite <- seq_shift, map_map.
symmetry.
erewrite map_ext_in. 2: {
  intros k Hk; apply in_seq in Hk; cbn in Hk; destruct Hk as (_, Hk).
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (j + S k) i) as [H| H]; [ flia H | clear H ].
  destruct (Nat.eq_dec (j + S k) j) as [H| H]; [ flia H | clear H ].
  rewrite Nat.add_comm, Nat.add_succ_comm.
  easy.
}
apply List_skipn_map_nth_seq.
Qed.

Theorem skipn_cons_skipn_succ : ∀ A (d : A) l i,
  i < length l
  → skipn i l = nth i l d :: skipn (S i) l.
Proof.
intros * Hi.
revert i Hi.
induction l as [| j]; intros; [ easy | cbn ].
destruct i; [ easy | ].
cbn in Hi.
apply Nat.succ_lt_mono in Hi.
now apply IHl.
Qed.

(*
Theorem transp_loop_enough_iter : ∀ it1 it2 i p,
  is_permut_list (seq 0 i ++ p)
  → length p + nb_nfit i p ≤ it1
  → length p + nb_nfit i p ≤ it2
  → transp_loop it1 i p = transp_loop it2 i p.
Proof.
intros * Hp Hit1 Hit2.
revert i p Hp it2 Hit1 Hit2.
induction it1; intros; cbn. {
  apply Nat.le_0_r, Nat.eq_add_0 in Hit1.
  destruct Hit1 as (H1, H2).
  apply length_zero_iff_nil in H1; subst p.
  symmetry; apply transp_loop_nil.
}
destruct p as [| j l]. {
  symmetry; apply transp_loop_nil.
}
cbn in Hit1, Hit2.
rewrite if_eqb_eq_dec in Hit1, Hit2 |-*.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  subst j; cbn.
  destruct it2; [ cbn in Hit2; flia Hit2 | ].
  cbn in Hit1, Hit2 |-*.
  apply Nat.succ_le_mono in Hit1, Hit2.
  rewrite Nat.eqb_refl.
  apply IHit1; [ | easy | easy ].
  now rewrite seq_S, <- app_assoc.
}
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
assert (Hjil : j < i + S (length l)). {
  destruct Hp as (Hpa, Hpn).
  rewrite app_length, seq_length in Hpa.
  specialize (Hpa j) as H1.
  now apply H1, in_or_app; right; left.
}
move Hjil before Hilj.
cbn in Hit1, Hit2.
destruct it2; [ flia Hit2 | ].
cbn - [ list_swap_elem ].
apply Nat.succ_le_mono in Hit1, Hit2.
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec i j) as [H| H]; [ flia Hij H | clear H ].
f_equal.
rewrite Nat.add_succ_r in Hit1, Hit2.
assert
  (H : nb_nfit i (list_swap_elem 0 (j :: l) 0 (j - i)) ≤ nb_nfit (S i) l). {
  clear Hij it1 it2 IHit1 Hit1 Hit2.
  cbn - [ nth ].
  rewrite Nat_succ_sub_succ_r; [ | easy ].
  rewrite List_nth_succ_cons.
  rewrite <- seq_shift, map_map.
  erewrite map_ext_in. 2: {
    intros k Hk.
    unfold transposition.
    replace (nth _ _ _) with (if k =? j - S i then j else nth k l 0). 2: {
      cbn.
      do 2 rewrite if_eqb_eq_dec.
      now destruct (Nat.eq_dec k (j - S i)).
    }
    easy.
  }
  rewrite if_eqb_eq_dec.
  remember (if Nat.eq_dec _ _ then _ else _) as x eqn:Hx.
  rewrite List_seq_cut with (i := j - S i). 2: {
    apply in_seq.
    split; [ easy | ].
    flia Hilj Hjil.
  }
  rewrite Nat.sub_0_r, Nat.add_0_l.
  rewrite map_app; cbn.
  rewrite Nat.eqb_refl.
  rewrite nb_nfit_app.
  rewrite List_map_seq_length.
  rewrite (Nat.add_comm (S i)), Nat.sub_add; [ | easy ].
  cbn; rewrite Nat.eqb_refl, Nat.add_0_l.
  specialize nth_split as H1.
  specialize (H1 _ (j - S i) l 0).
  assert (H : j - S i < length l) by flia Hjil Hilj.
  specialize (H1 H); clear H.
  destruct H1 as (l1 & l2 & Hll & Hl1l).
  rewrite Hll at 2.
  rewrite nb_nfit_app.
  subst x.
  destruct (Nat.eq_dec i (nth (j - S i) l 0)) as [Hjsi| Hjsi]. {
    rewrite Nat.add_0_l.
    apply Nat.add_le_mono. {
      erewrite map_ext_in. 2: {
        intros k Hk; apply in_seq in Hk.
        destruct Hk as (_, Hk); cbn in Hk.
        erewrite if_eqb_eq_dec.
        destruct (Nat.eq_dec k (j - S i)) as [H| H]; [ flia Hk H | ].
        rewrite Hll at 1.
        rewrite app_nth1; [ | now rewrite Hl1l ].
        easy.
      }
      rewrite <- Hl1l.
      now rewrite <- List_map_nth_seq.
    }
    rewrite Hl1l, (Nat.add_comm (S i)).
    rewrite Nat.sub_add; [ | easy ].
    rewrite <- List_seq_shift', map_map.
    erewrite map_ext_in. 2: {
      intros k Hk; apply in_seq in Hk.
      destruct Hk as (_, Hk); cbn in Hk.
      rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec (S (j - S i) + k) _) as [H| H]; [ flia H | clear H ].
      rewrite Hll at 1.
      rewrite app_nth2 at 1; [ | rewrite Hl1l; flia Hk ].
      rewrite Hl1l.
      replace (_ - _) with (S k) by flia.
      rewrite List_nth_succ_cons.
      easy.
    }
    replace (length l - S (j - S i)) with (length l2). 2: {
      rewrite Hll.
      rewrite app_length, Hl1l.
      cbn; flia.
    }
    rewrite <- List_map_nth_seq.
    rewrite Hll.
    rewrite app_nth2; [ | now rewrite Hl1l; unfold ge ].
    rewrite Hl1l, Nat.sub_diag.
    rewrite List_nth_0_cons.
    rewrite <- Hjsi; cbn; flia.
  }
  rewrite Nat.add_comm, <- Nat.add_assoc.
  apply Nat.add_le_mono. {
    erewrite map_ext_in. 2: {
      intros k Hk; apply in_seq in Hk.
      destruct Hk as (_, Hk); cbn in Hk.
      erewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec k (j - S i)) as [H| H]; [ flia Hk H | ].
      rewrite Hll at 1.
      rewrite app_nth1; [ | now rewrite Hl1l ].
      easy.
    }
    rewrite <- Hl1l.
    now rewrite <- List_map_nth_seq.
  }
  rewrite Hl1l, (Nat.add_comm (S i)).
  rewrite Nat.sub_add; [ | easy ].
  rewrite <- List_seq_shift', map_map.
  erewrite map_ext_in. 2: {
    intros k Hk; apply in_seq in Hk.
    destruct Hk as (_, Hk); cbn in Hk.
    rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec (S (j - S i) + k) _) as [H| H]; [ flia H | clear H ].
    rewrite Hll at 1.
    rewrite app_nth2 at 1; [ | rewrite Hl1l; flia Hk ].
    rewrite Hl1l.
    replace (_ - _) with (S k) by flia.
    rewrite List_nth_succ_cons.
    easy.
  }
  replace (length l - S (j - S i)) with (length l2). 2: {
    rewrite Hll.
    rewrite app_length, Hl1l.
    cbn; flia.
  }
  rewrite <- List_map_nth_seq.
  rewrite Hll.
  rewrite app_nth2; [ | now rewrite Hl1l; unfold ge ].
  rewrite Hl1l, Nat.sub_diag.
  rewrite List_nth_0_cons; cbn.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec j (nth (j - S i) l 0)) as [Hjjsi| Hjjsi]. 2: {
    now rewrite Nat.add_comm.
  }
  exfalso.
  rewrite <- Hjjsi in Hll.
  destruct Hp as (Hpa, Hpn).
  apply NoDup_app_iff in Hpn.
  destruct Hpn as (Hni & Hnjl & Hsjl).
  apply NoDup_cons_iff in Hnjl.
  destruct Hnjl as (H2, H3); apply H2.
  rewrite Hjjsi.
  apply nth_In; flia Hjil Hilj.
}
apply IHit1; cycle 1. {
  rewrite list_swap_elem_length.
  cbn - [ list_swap_elem ].
  etransitivity; [ | apply Hit1 ].
  apply -> Nat.succ_le_mono.
  now apply Nat.add_le_mono_l.
} {
  rewrite list_swap_elem_length.
  cbn - [ list_swap_elem ].
  etransitivity; [ | apply Hit2 ].
  apply -> Nat.succ_le_mono.
  now apply Nat.add_le_mono_l.
}
now apply app_seq_swap_is_permut_list.
Qed.

Theorem nb_nfit_succ_le : ∀ i j l, nb_nfit (S i) l ≤ nb_nfit i (j :: l).
Proof. cbn; flia. Qed.

Theorem eq_transp_loop_cons : ∀ it i j k p l,
  transp_loop it k p = (i, j) :: l
  → (∀ u, k + u < i → nth u p 0 = k + u) ∧
    nth (i - k) p 0 = j ∧
    k ≤ i ≤ it + k.
Proof.
intros * Hp *.
revert p k l Hp.
induction it; intros; [ easy | ].
cbn in Hp.
destruct p as [| a la]; [ easy | ].
rewrite if_eqb_eq_dec in Hp.
destruct (Nat.eq_dec k a) as [Hka| Hka]. {
  subst a.
  specialize (IHit la (S k) l Hp) as H1.
  destruct H1 as (H1 & H2 & H3).
  split. {
    intros u Hu.
    destruct u; [ now rewrite Nat.add_0_r | cbn ].
    rewrite <- Nat.add_succ_comm in Hu |-*.
    now apply H1.
  }
  specialize in_transp_loop_bounds as H4.
  specialize (H4 it (S k) la i j).
  rewrite Hp in H4.
  specialize (H4 (or_introl eq_refl)).
  split; [ now rewrite Nat_succ_sub_succ_r | ].
  rewrite <- Nat.add_succ_comm in H3.
  split; [ flia H3 | easy ].
}
injection Hp; clear Hp; intros Hp H1 H2; subst a k.
split; [ flia | ].
split; [ now rewrite Nat.sub_diag; cbn | flia ].
Qed.

Theorem eq_transp_list_cons : ∀ la lb i j,
  transp_list la = (i, j) :: lb
  → (∀ k, k < i → ff_app la k = k) ∧ nth i la 0 = j.
Proof.
intros * Hla.
unfold ff_app.
unfold transp_list in Hla.
specialize eq_transp_loop_cons as H1.
specialize (H1 (length la + nb_nfit 0 la) i j 0 la lb Hla).
rewrite Nat.sub_0_r in H1.
now destruct H1 as (H1 & H2 & H3).
Qed.
*)

Theorem list_swap_elem_comp_swap : ∀ l i j,
  i < length l
  → j < length l
  → list_swap_elem 0 l i j = l ° swap (length l) i j.
Proof.
intros * Hi Hj.
apply List_eq_iff.
unfold "°" at 1.
rewrite list_swap_elem_length, map_length, swap_length.
split; [ easy | ].
intros d k.
unfold swap.
revert i j k Hi Hj.
induction l as [| n]; intros; [ easy | ].
cbn in Hi, Hj |-*.
destruct k. {
  remember (transposition i j 0) as m eqn:Hm.
  symmetry in Hm.
  destruct m; [ easy | ].
  rewrite <- seq_shift.
  destruct (lt_dec m (length l)) as [Hml| Hml]. 2: {
    apply Nat.nlt_ge in Hml.
    unfold transposition in Hm.
    do 2 rewrite if_eqb_eq_dec in Hm.
    destruct (Nat.eq_dec 0 i) as [Hiz| Hiz]; [ flia  Hj Hm Hml | ].
    destruct (Nat.eq_dec 0 j) as [Hjz| Hjz]; [ flia  Hi Hm Hml | ].
    easy.
  }
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  now rewrite seq_nth.
}
rewrite seq_length.
rewrite map_map.
rewrite <- seq_shift.
do 2 rewrite map_map.
destruct (lt_dec k (length l)) as [Hkl| Hkl]. 2: {
  apply Nat.nlt_ge in Hkl.
  rewrite nth_overflow; [ | now rewrite List_map_seq_length ].
  rewrite nth_overflow; [ | now rewrite List_map_seq_length ].
  easy.
}
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ cbn | easy ].
remember (transposition i j (S k)) as m eqn:Hm.
symmetry in Hm.
destruct m; [ easy | ].
destruct (lt_dec m (length l)) as [Hml| Hml]. 2: {
  apply Nat.nlt_ge in Hml.
  unfold transposition in Hm.
  do 2 rewrite if_eqb_eq_dec in Hm.
  destruct (Nat.eq_dec (S k) i) as [Hiz| Hiz]; [ flia  Hj Hm Hml | ].
  destruct (Nat.eq_dec (S k) j) as [Hjz| Hjz]; [ flia  Hi Hm Hml | ].
  apply Nat.succ_inj in Hm; subst m.
  now apply Nat.nlt_ge in Hml.
}
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
now rewrite seq_nth.
Qed.

Theorem all_comb_inv_loop_cons : ∀ n a l,
  all_comb_inv_loop n (a :: l) = pred a + n * all_comb_inv_loop n l.
Proof. easy. Qed.

Theorem all_comb_inv_loop_ub : ∀ n l,
  n ≠ 0
  → (∀ i, i < length l → nth i l 0 ≤ n)
  → all_comb_inv_loop n l < n ^ length l.
Proof.
intros * Hnz Hnl.
revert n Hnz Hnl.
induction l as [| a]; intros; cbn; [ easy | ].
apply Nat_lt_lt_add_mul. 2: {
  specialize (Hnl 0 (Nat.lt_0_succ _)); cbn in Hnl.
  flia Hnl Hnz.
}
apply IHl; [ easy | ].
intros i Hi.
specialize (Hnl (S i)).
assert (H : S i < length (a :: l)) by now cbn; flia Hi.
now specialize (Hnl H).
Qed.

Theorem all_comb_inv_ub : ∀ n l,
  n ≠ 0
  → (∀ i, i < length l → nth i l 0 ≤ n)
  → all_comb_inv n l < n ^ length l.
Proof.
intros * Hnz Hnl.
unfold all_comb_inv.
rewrite <- rev_length.
apply all_comb_inv_loop_ub; [ easy | ].
intros i Hi.
rewrite rev_length in Hi.
rewrite rev_nth; [ | easy ].
apply Hnl.
flia Hi.
Qed.

Theorem nth_concat_same_length : ∀ A m n (lll : list (list (list A))) i,
  (∀ ll, ll ∈ lll → length ll = m)
  → (∀ ll, ll ∈ lll → ∀ l, l ∈ ll → length l = n)
  → i < length lll * m
  → length (nth i (concat lll) []) = n.
Proof.
intros * Hlll Hll Hi.
revert i Hi.
induction lll as [| ll1]; intros; [ easy | cbn ].
destruct (lt_dec i (length ll1)) as [Hill| Hill]. {
  rewrite app_nth1; [ | easy ].
  apply Hll with (ll := ll1); [ now left | ].
  now apply nth_In.
}
apply Nat.nlt_ge in Hill.
rewrite app_nth2; [ | easy ].
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

Theorem in_list_prodn_length : ∀ A (ll : list (list A)) l,
  (∀ l, l ∈ ll → l ≠ [])
  → l ∈ list_prodn ll
  → length l = length ll.
Proof.
intros * Hlz Hl.
revert l Hl.
induction ll as [| l1]; intros. {
  cbn in Hl.
  destruct Hl as [Hl| Hl]; [ now subst l | easy ].
}
cbn in Hl.
apply in_App_list in Hl.
destruct Hl as (a & Hl1 & Ha).
apply in_map_iff in Ha.
destruct Ha as (l3 & Hl & Hl3).
subst l; cbn; f_equal.
apply IHll; [ | easy ].
intros l4 Hl4.
now apply Hlz; right.
Qed.

Theorem nth_list_prodn_same_length : ∀ A n (ll : list (list A)) i,
  (∀ l, l ∈ ll → length l = n)
  → i < n ^ length ll
  → length (nth i (list_prodn ll) []) = length ll.
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
  destruct i; [ now rewrite App_list_cons | ].
  cbn in Hi; apply Nat.succ_lt_mono in Hi.
  rewrite App_list_cons; cbn.
  now apply IHl.
}
remember (l1 :: ll) as ll'; cbn; subst ll'.
rewrite App_list_concat_map.
apply nth_concat_same_length with (m := n ^ length (l1 :: ll)). {
  intros ll1 Hll1.
  apply in_map_iff in Hll1.
  destruct Hll1 as (a & Hll1 & Ha).
  subst ll1.
  rewrite map_length.
  rewrite list_prodn_length; [ | easy ].
  apply rngl_product_same_length.
  intros l2 Hl2.
  now apply Hll; right.
} {
  intros ll1 Hll1 l2 Hl2.
  apply in_map_iff in Hll1.
  destruct Hll1 as (a & Hll1 & Ha).
  subst ll1.
  apply in_map_iff in Hl2.
  destruct Hl2 as (l3 & Hl3 & Hl2).
  subst l2; cbn; f_equal.
  apply in_list_prodn_length in Hl2; [ easy | ].
  intros l4 Hl4.
  specialize (Hll _ (or_intror Hl4)).
  destruct l4; [ | easy ].
  now symmetry in Hll.
} {
  rewrite map_length.
  rewrite Hll; [ | now left ].
  now rewrite <- Nat.pow_succ_r'.
}
Qed.

Theorem nth_all_comb_length : ∀ n i,
  i < n ^ n
  → length (nth i (all_comb n) []) = n.
Proof.
intros * Hi.
unfold all_comb.
rewrite nth_list_prodn_same_length with (n := n). {
  apply repeat_length.
} {
  intros l Hl.
  apply repeat_spec in Hl; subst l.
  apply seq_length.
} {
  now rewrite repeat_length.
}
Qed.

Theorem all_comb_elem_ub : ∀ i j n,
  nth i (nth j (all_comb n) []) 0 ≤ n.
Proof.
intros.
unfold all_comb.
remember (list_prodn (repeat (seq 1 n) n)) as ll eqn:Hll.
destruct (lt_dec j (length ll)) as [Hjll| Hjll]. 2: {
  apply Nat.nlt_ge in Hjll.
  rewrite (nth_overflow ll); [ | easy ].
  now rewrite List_nth_nil.
}
assert (H1 : nth j ll [] ∈ ll) by now apply nth_In.
rewrite Hll in H1.
apply in_list_prodn_repeat_iff in H1.
rewrite <- Hll in H1.
destruct H1 as [(H1, H2)| H1]. {
  rewrite H1, H2.
  now rewrite List_nth_nil.
}
destruct H1 as (Hnz & Hn & Hln).
specialize (Hln (nth i (nth j ll []) 0)).
destruct (lt_dec i n) as [Hin| Hin]. 2: {
  apply Nat.nlt_ge in Hin.
  rewrite nth_overflow; [ easy | ].
  now rewrite Hn.
}
assert (H : nth i (nth j ll []) 0 ∈ nth j ll []). {
  apply nth_In.
  now rewrite Hn.
}
now specialize (Hln H).
Qed.

Theorem all_comb_elem_lb : ∀ i j n,
  i < n
  → j < n ^ n
  → 1 ≤ nth i (nth j (all_comb n) []) 0.
Proof.
intros * Hin Hjn.
unfold all_comb.
remember (list_prodn (repeat (seq 1 n) n)) as ll eqn:Hll.
assert (Hj : nth j ll [] ∈ ll). {
  apply nth_In.
  rewrite Hll.
  rewrite list_prodn_length; [ | now destruct n ].
  rewrite rngl_product_same_length with (n := n). 2: {
    intros l Hl.
    apply repeat_spec in Hl; subst l.
    apply seq_length.
  }
  now rewrite repeat_length.
}
rewrite Hll in Hj.
apply in_list_prodn_repeat_iff in Hj.
rewrite <- Hll in Hj.
destruct Hj as [(H1, H2)| Hj]; [ now subst n | ].
destruct Hj as (H1 & H2 & H3).
apply H3.
apply nth_In.
now rewrite H2.
Qed.

Theorem nth_in_list_prodn : ∀ A (d : A) ll l i,
  i < length ll
  → l ∈ list_prodn ll
  → nth i l d ∈ nth i ll [].
Proof.
intros * Hi Hll.
revert l i Hi Hll.
induction ll as [| l1]; intros; [ easy | ].
cbn in Hll |-*.
destruct i. {
  destruct ll as [| l2]. {
    apply in_App_list in Hll.
    destruct Hll as (a & Ha & Hla).
    apply in_map_iff in Hla.
    now destruct Hla as (l2 & H & Hl2); subst l.
  }
  apply in_App_list in Hll.
  destruct Hll as (a & Hl1 & Hl).
  apply in_map_iff in Hl.
  now destruct Hl as (l3 & H & Hl3); subst l.
}
cbn in Hi; apply Nat.succ_lt_mono in Hi.
destruct ll as [| l2]; [ easy | ].
apply in_App_list in Hll.
destruct Hll as (a & Ha & Hl).
apply in_map_iff in Hl.
destruct Hl as (l3 & H & Hl3); subst l.
rewrite List_nth_succ_cons.
now apply IHll.
Qed.

Theorem nat_summation_list_all_same : ∀ A (l : list A) a,
  ∑ (_ ∈ l), a = a * length l.
Proof.
intros.
induction l as [| b]; [ easy | ].
rewrite rngl_summation_list_cons.
cbn - [ rngl_add rngl_zero ].
rewrite IHl.
now rewrite Nat.mul_succ_r, Nat.add_comm.
Qed.

Theorem nat_product_list_all_same : ∀ A (l : list A) a,
  ∏ (_ ∈ l), a = a ^ length l.
Proof.
intros.
induction l as [| b]; [ easy | ].
rewrite rngl_product_list_cons.
cbn - [ rngl_mul rngl_one ].
now rewrite IHl.
Qed.

(* to be completed
Theorem det_isort_rows : in_charac_0_field →
  ∀ A kl,
  is_correct_matrix A = true
  → mat_ncols A = length kl
  → (∀ k, k ∈ kl → 1 ≤ k ≤ mat_nrows A)
  → det (mat_select_rows kl A) =
      (ε kl * det (mat_select_rows (isort Nat.leb kl) A))%F.
Proof.
intros Hif * Hcm Hac Hkl.
(*
Require Import RnglAlg.Zrl.
Require Import ZArith.
Compute (
  let A := mk_mat [[1;2;3];[4;5;6];[-7;8;9];[10;-11;12]]%Z in
  let kl := [1;4;3] in
  det (mat_select_rows kl A) =
    (ε kl * det (mat_select_rows (isort Nat.leb kl) A))%F
).
*)
destruct (Nat.eq_dec (length kl) 0) as [Hkz| Hkz]. {
  apply length_zero_iff_nil in Hkz; subst kl.
  cbn; rewrite ε_nil; symmetry.
  apply rngl_mul_1_l.
}
rewrite det_is_det'; try now destruct Hif. 2: {
  now apply mat_select_rows_is_square.
}
rewrite det'_is_det''; try now destruct Hif. 2: {
  now rewrite mat_select_rows_nrows.
}
rewrite det_is_det'; try now destruct Hif. 2: {
  apply mat_select_rows_is_square; [ easy | | ]. {
    now rewrite isort_length.
  } {
    intros k Hk.
    apply Hkl.
    now apply in_isort in Hk.
  }
}
rewrite det'_is_det''; try now destruct Hif. 2: {
  rewrite mat_select_rows_nrows.
  now rewrite isort_length.
}
unfold det''.
do 2 rewrite mat_select_rows_nrows.
rewrite isort_length.
rewrite rngl_mul_summation_list_distr_l; [ | now destruct Hif; left ].
symmetry; erewrite rngl_summation_list_eq_compat. 2: {
  intros jl Hjl.
  now rewrite rngl_mul_assoc.
}
symmetry.
remember (length kl) as n eqn:Hn.
set (f1 := λ kl l, map (λ j, nth j l 0) (isort_rank Nat.leb kl)).
set (g1 := f1 (isort_rank Nat.leb kl)).
set (h1 := f1 kl).
assert (Hgh : ∀ l, l ∈ all_comb n → g1 (h1 l) = l). {
  intros l Hl.
  unfold g1, h1, f1.
  erewrite map_ext_in. 2: {
    intros i Hi.
    rewrite (List_map_nth' 0). 2: {
      now apply in_isort_rank_lt in Hi.
    }
    easy.
  }
  unfold collapse.
  remember (isort_rank Nat.leb kl) as jl eqn:Hjl.
  rewrite List_map_nth_seq with (d := 0); symmetry.
  rewrite List_map_nth_seq with (d := 0); symmetry.
  rewrite map_length, isort_rank_length.
  replace (length jl) with n. 2: {
    now rewrite Hjl, isort_rank_length.
  }
  replace (length l) with n. 2: {
    apply in_all_comb_iff in Hl.
    now destruct Hl.
  }
  apply map_ext_in.
  intros i Hi.
  apply in_seq in Hi.
  rewrite (List_map_nth' 0). 2: {
    rewrite isort_rank_length, Hjl.
    now rewrite isort_rank_length, <- Hn.
  }
  do 3 rewrite fold_ff_app.
  rewrite permut_permut_isort; [ easy | | ]. 2: {
    now rewrite Hjl, isort_rank_length, <- Hn.
  }
  rewrite Hjl.
  apply isort_rank_is_permut_list.
}
assert (Hhg : ∀ l, l ∈ all_comb n → h1 (g1 l) = l). {
  intros l Hl.
  unfold g1, h1, f1.
  erewrite map_ext_in. 2: {
    intros i Hi.
    rewrite (List_map_nth' 0). 2: {
      apply in_isort_rank_lt in Hi.
      now do 2 rewrite isort_rank_length.
    }
    easy.
  }
  remember (isort_rank Nat.leb kl) as jl eqn:Hjl.
  rewrite List_map_nth_seq with (d := 0); symmetry.
  rewrite List_map_nth_seq with (d := 0); symmetry.
  rewrite map_length.
  replace (length jl) with n. 2: {
    now rewrite Hjl, isort_rank_length.
  }
  replace (length l) with n. 2: {
    apply in_all_comb_iff in Hl.
    now destruct Hl.
  }
  apply map_ext_in.
  intros i Hi.
  apply in_seq in Hi.
  rewrite (List_map_nth' 0). 2: {
    now rewrite Hjl, isort_rank_length, <- Hn.
  }
  do 3 rewrite fold_ff_app.
  rewrite permut_isort_permut; [ easy | | ]. 2: {
    now rewrite Hjl, isort_rank_length, <- Hn.
  }
  rewrite Hjl.
  apply isort_rank_is_permut_list.
}
erewrite rngl_summation_list_change_var with (g := g1) (h := h1); [ | easy ].
assert (Heql : equality (list_eqb Nat.eqb)). {
  intros la lb.
  apply -> equality_list_eqb.
  unfold equality.
  apply Nat.eqb_eq.
}
(**)
rewrite (rngl_summation_list_permut _ (list_eqb Nat.eqb))
    with (l2 := all_comb n); [ | easy | ]. 2: {
  apply permutation_nth with (d := []); [ easy | ].
  rewrite map_length, all_comb_length; [ | easy ].
  split; [ easy | ].
(*
Compute (
  let n := 3 in
  let kl := [1;4;3] in
  let g1 := λ l, map (λ j : nat, nth j l 0) (collapse kl) in
  let h1 := λ l, map (λ j : nat, nth j l 0) (isort_rank Nat.leb kl) in
  let f := λ i, all_comb_inv n (g1 (nth i (all_comb n) [])) in
  map (λ x,
  nth x (all_comb n) [] = nth (f x) (map h1 (all_comb n)) [])
  (seq 0 (n ^ n))
).
...
*)
  exists (λ i, all_comb_inv n (g1 (nth i (all_comb n) []))).
  split; [ | split ]. {
    unfold FinFun.bFun.
    intros i Hi.
    eapply lt_le_trans. {
      apply all_comb_inv_ub; [ easy | ].
      intros j Hj.
      unfold g1, f1 in Hj |-*.
      rewrite fold_collapse in Hj |-*.
      rewrite map_length, collapse_length, <- Hn in Hj.
      rewrite (List_map_nth' 0); [ | now rewrite collapse_length, <- Hn ].
      apply all_comb_elem_ub.
    }
    apply Nat.pow_le_mono_r; [ easy | ].
    unfold g1, f1.
    rewrite fold_collapse.
    now rewrite map_length, collapse_length, <- Hn.
  } 2: {
    intros i Hi.
    unfold g1, f1.
    rewrite fold_collapse.
    rewrite (List_map_nth' []). 2: {
      rewrite all_comb_length; [ | easy ].
      eapply lt_le_trans. {
        apply all_comb_inv_ub; [ easy | ].
        rewrite map_length, collapse_length, <- Hn.
        intros j Hj.
        rewrite (List_map_nth' 0); [ | now rewrite collapse_length, <- Hn ].
        apply all_comb_elem_ub.
      }
      now rewrite map_length, collapse_length, <- Hn.
    }
    unfold collapse.
    fold (f1 (isort_rank Nat.leb kl) (nth i (all_comb n) [])).
    fold g1.
    remember (nth i (all_comb n) []) as l eqn:Hl.
    symmetry.
    remember (all_comb_inv n (g1 l)) as x.
    rewrite <- Hhg. 2: {
      rewrite Hl.
      apply nth_In.
      now rewrite all_comb_length.
    }
    subst x.
    f_equal.
    unfold g1, f1.
    rewrite fold_collapse.
    remember (collapse kl) as jl eqn:Hjl.
    specialize (collapse_is_permut kl) as H1.
    rewrite <- Hjl, <- Hn in H1.
    remember (map (λ j, nth j l 0) jl) as l1 eqn:Hl1.
    assert (Hln : length l1 = n). {
      now rewrite Hl1, map_length, Hjl, collapse_length.
    }
Theorem nth_all_comb_inv_all_comb : ∀ n l,
  n = length l
  → (∀ a, a ∈ l → 1 ≤ a ≤ n)
  → nth (all_comb_inv n l) (all_comb n) [] = l.
Proof.
intros * Hnl Hln.
unfold all_comb_inv.
remember (rev l) as l' eqn:Hl'.
rewrite <- (rev_involutive l') in Hl'.
apply List_rev_inj in Hl'; subst l; rename l' into l.
rewrite rev_length in Hnl.
assert (H : ∀ a, a ∈ l → 1 ≤ a ≤ n). {
  intros * Ha.
  apply Hln.
  now apply -> in_rev.
}
move H before Hln; clear Hln; rename H into Hln.
revert n Hln Hnl.
induction l as [| a]; intros; [ now subst n | ].
destruct n; [ easy | ].
rewrite all_comb_inv_loop_cons.
rewrite Nat.add_comm.
rewrite <- List_nth_skipn.
cbn - [ seq "*" ].
rewrite iter_list_seq; [ | easy ].
rewrite Nat.add_comm, Nat.add_sub.
...
rewrite rngl_App_seq_App.
rewrite App_list_seq
...
Compute (all_comb 2).
Compute (all_comb 3).
Compute (
  let n := 2 in
all_comb (S n) = App (i = 1, n), map (cons i) (all_comb n)
).
Print list_prodn.
...
cbn - [ all_comb_inv_loop seq ].
Print all_comb_inv_loop.
...
Theorem all_comb_S : ∀ n, all_comb (S n) = seq 1 n :: all_comb n.
Proof.
intros.
cbn - [ seq ].
cbn - [ all_comb all_comb_inv_loop seq ].
...
rewrite IHl.
...
Compute (
  let l := [1;1;2;1;2] in
  let n := 2 in
  all_comb_inv n l
(*
  nth (all_comb_inv n l) (all_comb n) [] = l
*)
).
...
subst n.
induction l as [| a]; [ easy | ].
cbn - [ seq ].
Print all_comb_inv_loop.
...
intros * Hnl Hln.
revert l Hnl Hln.
induction n; intros; cbn - [ seq ]. {
  now apply length_zero_iff_nil in Hnl; subst l.
}
Print all_comb_inv_loop.
intros * Hnl Hln.
symmetry in Hnl.
unfold all_comb_inv.
revert l Hnl Hln.
induction n; intros; cbn - [ seq ]. {
  now apply length_zero_iff_nil in Hnl; subst l.
}
Print all_comb_inv_loop.
...
Compute (
  let l := [1;1;2;4;2] in
  let n := length l in
  nth (all_comb_inv n l) (all_comb n) [] = l
).
...
    apply nth_all_comb_inv_all_comb; [ easy | ].
    intros a Ha.
    rewrite Hl1 in Ha.
    apply in_map_iff in Ha.
    destruct Ha as (j & Hja & Hj); subst a.
    rewrite Hl.
    split; [ | apply all_comb_elem_ub ].
    apply all_comb_elem_lb; [ | easy ].
...
    unfold h1, g1.
    unfold f1 at 2.
    rewrite fold_collapse.
...
Theorem glop : ∀ i n,
  i < n ^ n
  → all_comb_inv n (nth i (all_comb n) []) = i.
Proof.
intros * Hin.
unfold all_comb, all_comb_inv.
revert i Hin.
induction n; intros. {
  rewrite Nat.pow_0_r in Hin; cbn.
  now apply Nat.lt_1_r in Hin; subst i.
}
cbn - [ seq ].
rewrite fold_iter_seq'.
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec (1 + S n) 0) as [H| H]; [ easy | clear H ].
rewrite Nat.add_comm, Nat.add_sub.
remember (repeat (seq 1 (S n)) n) as ll eqn:Hll; symmetry in Hll.
destruct ll as [| l1]. {
  apply List_eq_repeat_nil in Hll; subst n; cbn.
  now apply Nat.lt_1_r in Hin; subst i.
}
cbn.
(**)
destruct ll as [| l2]. {
  destruct n; [ easy | ].
  remember (seq 1 (S (S n))) as s.
  cbn in Hll.
  injection Hll; clear Hll; intros Hll Hl1; subst s.
  destruct n; [ | easy ].
  subst l1; cbn.
  destruct i; [ easy | ].
  destruct i; [ easy | ].
  destruct i; [ easy | ].
  destruct i; [ easy | ].
  cbn in Hin; flia Hin.
}
...
rewrite List_rev_nth.
rewrite (List_map_nth' []). 2: {
  rewrite List_flat_map_length.
  erewrite rngl_summation_list_eq_compat. 2: {
    intros j Hj.
    now rewrite map_length.
  }
  cbn - [ seq rngl_add rngl_zero ].
  rewrite nat_summation_list_all_same.
  rewrite seq_length.
  destruct ll as [| l2]. {
    rewrite map_length.
    destruct n; [ easy | ].
    remember (seq 1 (S (S n))) as s eqn:Hs.
    cbn in Hll.
    injection Hll; clear Hll; intros Hr H.
    subst l1 s.
    apply List_eq_repeat_nil in Hr; subst n.
    now rewrite seq_length.
  }
  rewrite List_flat_map_length.
  erewrite rngl_summation_list_eq_compat. 2: {
    intros j Hj.
    now rewrite map_length, list_prodn_length.
  }
  remember (S n) as sn.
  cbn - [ rngl_add rngl_zero rngl_mul rngl_one ].
  rewrite nat_summation_list_all_same.
  subst sn.
  generalize Hll; intros Hn.
  apply (f_equal length) in Hn.
  cbn in Hn; rewrite repeat_length in Hn.
  erewrite rngl_product_list_eq_compat. 2: {
    intros l Hl.
    replace (length l) with (S (S (S (length ll)))). 2: {
      destruct n; [ easy | ].
      cbn - [ seq ] in Hll.
      destruct n; [ easy | ].
      cbn - [ seq ] in Hll.
      injection Hll; clear Hll; intros Hll H2 H1.
      destruct Hl as [Hl| Hl]. {
        subst l l2.
        now cbn; rewrite seq_length, Hn.
      }
      rewrite <- Hll in Hl.
      apply repeat_spec in Hl.
      rewrite Hl, <- Hn.
      now cbn; rewrite seq_length.
    }
    easy.
  }
  cbn - [ "*" rngl_mul rngl_one ].
  replace (length l1) with (S n). 2: {
    destruct n; [ easy | ].
    cbn - [ seq ] in Hll.
    injection Hll; clear Hll; intros Hll Hl1.
    rewrite <- Hl1.
    now cbn; rewrite seq_length.
  }
  rewrite nat_product_list_all_same.
  rewrite <- Hn.
  replace (length (l2 :: ll)) with (n - 1). 2: {
    destruct n; [ easy | ].
    cbn - [ seq ] in Hll.
    injection Hll; clear Hll; intros Hll Hl1.
    rewrite <- Hll.
    rewrite repeat_length.
    now rewrite Nat_sub_succ_1.
  }
  destruct n; [ easy | ].
  rewrite Nat_sub_succ_1.
  rewrite Nat.mul_comm, Nat.mul_assoc.
  rewrite <- Nat.pow_succ_r'.
  rewrite Nat.mul_comm.
  now rewrite <- Nat.pow_succ_r'.
}
rewrite List_rev_nth.
...
Search (rev (flat_map _ _)).
Search (rev (concat _)).
...
Compute (
  let n := 4 in
  map (λ i, all_comb_inv n (nth i (all_comb n) [])) (seq 0 (n ^ n + 2))
).
...
rewrite glop.
...
Compute (
  let kl := [4;1;3] in
  let n := length kl in
  let f1 := λ kl l, map (λ j : nat, nth j l 0) (isort_rank Nat.leb kl) in
  let g1 := f1 (isort_rank Nat.leb kl) in
  let h1 := f1 kl in
  map (λ i,
    let l := nth i (all_comb n) [] in
    all_comb_inv n (g1 l)) (seq 0 (n ^ n))
).
Compute (
  let n := 3 in
  let kl := [1;4;3] in
  let f1 := λ kl l, map (λ j : nat, nth j l 0) (isort_rank Nat.leb kl) in
  let g1 := f1 (isort_rank Nat.leb kl) in
  let h1 := f1 kl in
  map (λ i,
    let l := nth i (all_comb n) [] in
    h1 (nth (all_comb_inv n (g1 l)) (all_comb n) []) = l) (seq 0 (n ^ n))
).
......
    erewrite map_ext_in. 2: {
      intros j Hj.
unfold all_comb_inv.
Print all_comb_inv_loop.
Print all_comb.
Search all_comb_inv.
Search (map _ (isort_rank _ _)).
...
(*
Theorem list_prodn_elem_in : ∀ ll i j,
  i < length (nth j (list_prodn ll) [])
  → j < length (list_prodn ll)
  → nth i (nth j (list_prodn ll) []) 0 ∈ concat ll.
Proof.
intros * Hi Hj.
remember (length ll) as len eqn:Hlen; symmetry in Hlen.
revert i j ll Hi Hj Hlen.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct len. {
  now apply length_zero_iff_nil in Hlen; subst ll; cbn.
}
destruct ll as [| l1]; [ easy | ].
cbn in Hlen.
apply Nat.succ_inj in Hlen; cbn - [ concat ].
destruct ll as [| l2]. {
  cbn; rewrite app_nil_r.
  cbn in Hi, Hj.
  rewrite map_length in Hj.
  rewrite (List_map_nth' 0) in Hi; [ | easy ].
  destruct l1 as [| a1]; [ easy | ].
  cbn - [ In ].
  destruct j. {
    destruct i; [ now left | ].
    cbn in Hi.
    now apply Nat.succ_lt_mono in Hi.
  }
  cbn in Hi, Hj.
  apply Nat.succ_lt_mono in Hj.
  apply Nat.lt_1_r in Hi; subst i.
  rewrite (List_map_nth' 0); [ | easy ].
  cbn - [ In ].
  now right; apply nth_In.
}
destruct i. {
...
*)
...
apply (nth_in_list_prodn 0) with (i := i) in H1. 2: {
  now rewrite repeat_length.
}
...
Theorem list_prodn_elem_ub : ∀ ll n i j,
  (∀ l, l ∈ ll → ∀ a, a ∈ l → a ≤ n)
  → nth i (nth j (list_prodn ll) []) 0 ≤ n.
Proof.
intros * Hll.
remember (length ll) as len eqn:Hlen; symmetry in Hlen.
revert n i j ll Hll Hlen.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct len. {
  apply length_zero_iff_nil in Hlen; subst ll; cbn.
  now rewrite Tauto_match_nat_same, List_nth_nil.
}
destruct ll as [| l1]; [ easy | ].
cbn in Hlen.
apply Nat.succ_inj in Hlen; cbn.
destruct ll as [| l2]. {
  destruct l1 as [| a1]. {
    now cbn; rewrite Tauto_match_nat_same, List_nth_nil.
  }
  cbn.
  destruct j. {
    destruct i. {
      cbn; apply Hll with (l := a1 :: l1); [ now left | ].
      now left.
    }
    now cbn; rewrite Tauto_match_nat_same.
  }
  destruct (lt_dec j (length l1)) as [Hjl| Hjl]. 2: {
    apply Nat.nlt_ge in Hjl.
    rewrite (nth_overflow (map _ _)); [ | now rewrite map_length ].
    now rewrite List_nth_nil.
  }
  rewrite (List_map_nth' 0); [ | easy ].
  destruct i. {
    cbn.
    apply Hll with (l := a1 :: l1); [ now left | ].
    now right; apply nth_In.
  }
  now cbn; rewrite Tauto_match_nat_same.
}
(**)
clear Hlen.
revert l1 l2 ll n i j Hll.
induction ll as [| l3]; intros. {
  cbn.
Search flat_map.
...
destruct i. {
  rewrite flat_map_concat_map.
  induction j. {
    clear Hll Hlen.
    destruct l1 as [| a1]; [ easy | ].
    destruct l2 as [| a2]. {
      cbn.
      destruct ll as [| l3]; cbn. {
        induction l1 as [| a2]; [ easy | cbn ].
        apply IHl1.
      }
      induction l1 as [| a2]; [ easy | cbn ].
      apply IHl1.
    }
    cbn - [ list_prodn ].
...
    destruct ll as [| l3]. {
      destruct l2; [ | easy ].
      now specialize (Hlz _ (or_intror (or_introl eq_refl))).
    }
    apply Hm.
    intros l Hl.
    now apply Hlz; right.
  }
...
intros * Hll.
destruct (lt_dec j (length (list_prodn ll))) as [Hjll| Hjll]. 2: {
  apply Nat.nlt_ge in Hjll.
  rewrite (nth_overflow (list_prodn ll)); [ | easy ].
  now rewrite List_nth_nil.
}
destruct (lt_dec i (length ll)) as [Hill| Hill]. 2: {
  apply Nat.nlt_ge in Hill.
  rewrite nth_overflow; [ easy | ].
  etransitivity; [ | apply Hill ].
...
Theorem nth_prodn_length : ∀ A (ll : list (list A)) i,
  i < length (list_prodn ll)
  → (∀ l, l ∈ ll → l ≠ [])
  → length (nth i (list_prodn ll) []) = length ll.
Proof.
intros * Hll Hlz.
revert i Hll.
induction ll as [| l1]; intros; cbn. {
  now rewrite Tauto_match_nat_same.
}
destruct ll as [| l2]. {
  cbn in Hll; rewrite map_length in Hll.
  destruct l1 as [| d]; [ easy | ].
  now rewrite (List_map_nth' d).
}
assert
  (Hm : ∀ A (a1 : A) l2 l3 ll,
     (∀ l, l ∈ l2 :: l3 :: ll → l ≠ [])
     → map (cons a1)
         (flat_map (λ a, map (cons a) (list_prodn (l3 :: ll))) l2) ≠ []). {
  clear.
  intros * Hlz H1.
  apply map_eq_nil in H1.
  rewrite flat_map_concat_map in H1.
  apply concat_nil_Forall in H1.
  specialize (proj1 (Forall_forall _ _) H1) as H2.
  cbn - [ list_prodn ] in H2.
  clear H1.
  destruct l2 as [| a2]. {
    now specialize (Hlz _ (or_introl eq_refl)).
  }
  remember (list_prodn (l3 :: ll)) as ll' eqn:Hll'.
  symmetry in Hll'.
  destruct ll' as [| l4]. {
    apply eq_list_prodn_nil_iff in Hll'.
    destruct Hll' as [H1| H1]; [ easy | ].
    destruct H1 as [H1| H1]. {
      subst l3.
      now specialize (Hlz _ (or_intror (or_introl eq_refl))).
    }
    now specialize (Hlz _ (or_intror (or_intror H1))).
  }
  cbn in H2.
  now specialize (H2 _ (or_introl eq_refl)).
}
destruct i. {
  rewrite flat_map_concat_map.
  rewrite <- List_hd_nth_0.
  rewrite List_hd_concat. 2: {
    cbn.
    destruct l1 as [| a1]; cbn. {
      now specialize (Hlz _ (or_introl eq_refl)).
    }
    destruct ll as [| l3]. {
      destruct l2; [ | easy ].
      now specialize (Hlz _ (or_intror (or_introl eq_refl))).
    }
    apply Hm.
    intros l Hl.
    now apply Hlz; right.
  }
  destruct l1 as [| a1]. {
    now specialize (Hlz _ (or_introl eq_refl)).
  }
  rewrite List_map_hd with (a := a1); [ | now cbn ].
  assert (H2 : 0 < length (list_prodn (l2 :: ll))). {
    rewrite list_prodn_length; [ | easy ].
    clear IHll Hll.
    remember (l2 :: ll) as x eqn:Hx.
    clear - Hlz; rename x into ll.
    induction ll as [| l2]. {
      now rewrite rngl_product_list_empty; cbn.
    }
    rewrite rngl_product_list_cons.
    apply Nat.lt_0_mul'.
    split. {
      destruct l2; [ | now cbn ].
      now specialize (Hlz _ (or_intror (or_introl eq_refl))).
    }
    apply IHll.
    intros l Hl.
    apply Hlz.
    destruct Hl as [Hl| H]; [ now left | now right; right ].
  }
  rewrite List_map_hd with (a := []); [ | easy ].
  cbn - [ list_prodn ]; f_equal.
  rewrite List_hd_nth_0.
  rewrite IHll; [ easy | | easy ].
  intros l Hl.
  now apply Hlz; right.
}
rewrite flat_map_concat_map.
rewrite List_nth_succ_concat. 2: {
  intros ll' Hll'.
  apply in_map_iff in Hll'.
  destruct Hll' as (a & Hll' & Ha); subst ll'; cbn.
  destruct ll as [| l3]. {
    destruct l2 as [| a2]; [ | easy ].
    now specialize (Hlz _ (or_intror (or_introl eq_refl))).
  }
  apply Hm.
  intros l Hl.
  now apply Hlz; right.
}
destruct l1 as [| a1]. {
  now specialize (Hlz _ (or_introl eq_refl)).
}
rewrite (List_map_hd a1); [ | now cbn ].
cbn - [ list_prodn ] in Hll |-*.
rewrite app_nth1. 2: {
rewrite list_prodn_length in Hll; [ | easy ].
...
Search (tl (map _ _ )).
rewrite (List_map_hd _ _ []).
Search (flat_map _ _ = flat_map _ _).
...
  destruct l2 as [| a2]. {
    now specialize (Hlz _ (or_intror (or_introl eq_refl))).
  }
  intros H1.
  apply map_eq_nil in H1.
  rewrite flat_map_concat_map in H1.
  apply concat_nil_Forall in H1.
  specialize (proj1 (Forall_forall _ _) H1) as H2.
  cbn - [ list_prodn ] in H2.
  clear H1.
...
  destruct l2 as [| a2]. {
      now specialize (Hlz _ (or_intror (or_introl eq_refl))).
    }
    remember (list_prodn (l3 :: ll)) as ll' eqn:Hll'.
    symmetry in Hll'.
    destruct ll' as [| l4]. {
      apply eq_list_prodn_nil_iff in Hll'.
      destruct Hll' as [H1| H1]; [ easy | ].
      destruct H1 as [H1| H1]. {
        subst l3.
        now specialize (Hlz _ (or_intror (or_intror (or_introl eq_refl)))).
      }
      now specialize (Hlz _ (or_intror (or_intror (or_intror H1)))).
    }
    cbn in H2.
    now specialize (H2 _ (or_introl eq_refl)).
Search (concat _ = []).
...
rewrite <- List_hd_nth_0.
  rewrite List_hd_concat. 2: {
    cbn.
    destruct l1 as [| a1]; cbn. {
...
  cbn.
  cbn.
  destruct ll as [| l3]. {
    destruct l2 as [| a2]; [ | easy ].
    now specialize (Hlz _ (or_intror (or_introl eq_refl))).
  }
  rewrite List_map_hd with (a := []). 2: {
...
  specialize (H1 (a1 :: l3)).
...
  destruct l2 as [| a2]; [ now right; left | ].
  cbn - [ In list_prodn ] in H1.
...
    assert (H3 : ∀ x, map (cons a2) (list_prodn (l3 :: ll)) = x → x = []). {
      intros.
...
      apply in_map_iff in H.
      now specialize (H2 _ H).
    }
...
    assert
      (H3 : ∀ x,
       (∃ y, map (cons y) (list_prodn (l3 :: ll)) = x ∧ y ∈ a2 :: l2) → x = []). {
      intros.
      apply in_map_iff in H.
      now specialize (H2 _ H).
    }
...
    specialize (H2 [a2 :: hd [] (list_prodn (l3 :: ll))]).
    assert (H : [a2 :: hd [] (list_prodn (l3 :: ll))] ∈ map (λ a : A, map (cons a) (list_prodn (l3 :: ll))) (a2 :: l2)). {
      apply in_map_iff.
      cbn.
...
    destruct l3 as [| a3]. {
      now specialize (Hlz _ (or_intror (or_intror (or_introl eq_refl)))).
    }
...
    destruct ll as [| l4]. {
      cbn in H2.
...
      erewrite map_ext_in in H2. 2: {
        intros i Hi.
        now rewrite map_map.
      }
      specialize (H2
...
    erewrite map_ext_in in H2. 2: {
      intros i Hi.
      cbn.
      detruct
...
    specialize (H1 (a3
...
  destruct l1 as [| a1]. {
    now specialize (Hlz _ (or_introl eq_refl)).
  }
  cbn - [ list_prodn ].
  rewrite app_nth1. 2: {
    clear - Hlz.
    rewrite map_length.
    rewrite list_prodn_length; [ | easy ].
    remember (l2 :: ll) as ll'.
    clear ll l2 Heqll'; rename ll' into ll.
    induction ll as [| l2]. {
      now rewrite rngl_product_list_empty; cbn.
    }
    rewrite rngl_product_list_cons.
    replace 0 with (0 * 0) by easy.
    apply Nat.mul_lt_mono. {
      specialize (Hlz _ (or_intror (or_introl eq_refl))).
      now destruct l2; cbn.
    }
    apply IHll.
    intros l Hl.
    destruct Hl as [Hl| Hl]; [ now subst l | ].
    now apply Hlz; right; right.
  }
  remember (list_prodn (l2 :: ll)) as ll' eqn:Hll'.
  symmetry in Hll'.
  destruct ll' as [| l3]. {
    exfalso.
    cbn in Hll'.
    destruct ll. {
      destruct l2; [ | easy ].
      now specialize (Hlz _ (or_intror (or_introl eq_refl))).
    }
    cbn in Hll'.
    destruct ll as [| l3]. {
      destruct l2. {
        now specialize (Hlz _ (or_intror (or_introl eq_refl))).
      }
      cbn in Hll'.
      apply app_eq_nil in Hll'.
      destruct Hll' as (H1, H2).
      destruct l; [ | easy ].
      now specialize (Hlz _ (or_intror (or_intror (or_introl eq_refl)))).
    }
    rewrite flat_map_concat_map in Hll'.
    apply concat_nil_Forall in Hll'.
    specialize (proj1 (Forall_forall _ _) Hll') as H1.
    cbn - [ list_prodn ] in H1.
...
  clear - Hlz.
  induction ll as [| l3]. {
    cbn.
    destruct l2 as [| a2]; [ | easy ].
    now specialize (Hlz _ (or_intror (or_introl eq_refl))).
  }
...
  remember (l3 :: ll) as ll'; cbn; subst ll'.
  induction ll as [| l4]. {
    cbn.
    destruct l2 as [| a2]; cbn. {
      now specialize (Hlz _ (or_intror (or_introl eq_refl))).
    }
    rewrite map_app.
    rewrite app_nth1. 2: {
      rewrite map_length, map_length, map_length.
      destruct l3 as [| a3]; [ | now cbn ].
      now specialize (Hlz _ (or_intror (or_intror (or_introl eq_refl)))).
    }
...
    induction ll as [| l3]; intros; rewrite map_length. {
      rewrite map_length.
      destruct l2 as [| a2]; [ | now cbn ].
      now specialize (Hlz _ (or_intror (or_introl eq_refl))).
    }
    cbn.
    destruct ll as [| l4]. {
      destruct l2 as [| a2]; cbn. {
        now specialize (Hlz _ (or_intror (or_introl eq_refl))).
      }
      rewrite app_length.
...
    rewrite flat_map_concat_map.
Compute (list_prodn [[]; []]).
...
  Search (nth _ (concat _)).
  Search (hd _ (concat _)).
  Search (hd (concat _)).
...
  now rewrite nth_prodn_length.
...
Theorem nth_nth_prodn : ∀ A (d : A) ll i j,
  ll ≠ []
  → (∀ l, l ∈ ll → l ≠ [])
  → nth i (nth j (list_prodn ll) []) d ∈ nth i ll [].
Proof.
intros * Hll Hl.
revert i j.
induction ll as [| l1]; intros; [ easy | cbn ].
destruct ll as [| l2]. {
  destruct i. {
    destruct (lt_dec j (length l1)) as [Hjll| Hjll]. 2: {
      apply Nat.nlt_ge in Hjll.
      rewrite (nth_overflow (map _ _)); [ | now rewrite map_length ].
...
    rewrite (List_map_nth' d).
...
specialize (nth_nth_prodn 0 ll i j) as H1.
destruct (lt_dec j (length (list_prodn ll))) as [Hjll| Hjll]. 2: {
  apply Nat.nlt_ge in Hjll.
  rewrite (nth_overflow (list_prodn ll)); [ | easy ].
  now rewrite List_nth_nil.
}
destruct (lt_dec i (length ll)) as [Hill| Hill]. 2: {
  apply Nat.nlt_ge in Hill.
  rewrite nth_overflow; [ easy | ].
Search (length (nth _ (list_prodn _) _)).
...
apply Hll with (l := nth i ll []); [ | easy ].
apply nth_In.
...
  destruct (lt_dec j (length (list_prodn (l1 :: ll)))) as [Hjll| Hjll]. 2: {
    apply Nat.nlt_ge in Hjll.
    now rewrite nth_overflow.
  }
...
intros * Hll.
revert n i j Hll.
induction ll as [| l1]; intros; [ now destruct j, i | ].
destruct (lt_dec i (S (length ll))) as [Hill| Hill]. 2: {
  apply Nat.nlt_ge in Hill.
  rewrite nth_overflow; [ easy | ].
  destruct (lt_dec j (length (list_prodn (l1 :: ll)))) as [Hjll| Hjll]. 2: {
    apply Nat.nlt_ge in Hjll.
    now rewrite nth_overflow.
  }
Search (length (nth _ _ _)).
...
  rewrite list_prodn_length in Hjll; [ | easy ].
...
  rewrite nth_list_prodn_same_length with (n := length l1). {
    easy.
  } {
    intros l Hl.
    destruct Hl as [Hl| Hl]; [ now subst l | ].
...
apply list_all_nth_prop. 2: {
...
  rewrite nth_list_prodn_same_length with (n := length l1). {
    cbn.
...
intros a Ha.
destruct j. {
  apply Hll with (l := l1); [ now left | ].
  cbn in Ha.
  destruct ll as [| l2]. {
    rewrite (List_map_nth' 0) in Ha.
    destruct Ha as [Ha| Ha]; [ subst a | easy ].
    apply nth_In.
...
apply (In_nth _ _ 0) in Ha.
destruct Ha as (k & Hkl & H).
subst a.

Search (_ ∈ _ → ∃ _, _).

Search (_ → _ (nth _ _ _)).
cbn.
destruct ll as [| l2]. {
  destruct (lt_dec j (length l1)) as [Hjl1| Hjl1]. 2: {
    apply Nat.nlt_ge in Hjl1.
    rewrite (nth_overflow (map _ _)); [ | now rewrite map_length ].
    now rewrite List_nth_nil.
  }
  rewrite (List_map_nth' 0); [ | easy ].
  destruct i. {
    cbn.
    apply Hll with (l := l1); [ now left | ].
    now apply nth_In.
  }
  now cbn; rewrite Tauto_match_nat_same.
}
destruct i. {
  destruct l1 as [| a1]. {
    now cbn; rewrite Tauto_match_nat_same.
  }
  apply Hll with (l := a1 :: l1); [ now left | ].
  rewrite flat_map_concat_map.
  cbn - [ In list_prodn ].
  destruct (lt_dec j (length (list_prodn (l2 :: ll)))) as [Hjll| Hjll]. {
    rewrite app_nth1; [ | now rewrite map_length ].
    rewrite (List_map_nth' []); [ now left | easy ].
  }
  apply Nat.nlt_ge in Hjll.
  rewrite app_nth2; [ | now rewrite map_length ].
  rewrite map_length.
...
intros * Hll.
destruct (lt_dec j (length (list_prodn ll))) as [Hjll| Hjll]. 2: {
  apply Nat.nlt_ge in Hjll.
  rewrite (nth_overflow (list_prodn ll)); [ | easy ].
  now rewrite List_nth_nil.
}
remember (nth j (list_prodn ll) []) as l eqn:Hl.
assert (H1 : l ∈ list_prodn ll). {
  rewrite Hl.
  now apply nth_In.
}
subst l.
apply in_list_prodn_length in H1. 2: {
  intros l1 Hl1 H; subst l1.
  now rewrite list_prodn_with_nil in H1.
}
...
apply list_prodn_elem_ub.
...
intros.
revert i j.
induction n; intros; [ now destruct j, i | ].
cbn - [ seq ].
...
    rewrite Tauto_match_nat_same.
induction n; intros; [ easy | clear Hnz ].
cbn - [ seq ].
remember (repeat (seq 1 (S n)) n) as ll eqn:Hll; symmetry in Hll.
destruct ll as [| l1]. {
  apply List_eq_repeat_nil in Hll; subst n; cbn.
  destruct j. {
    destruct i; [ easy | now destruct i ].
  }
  rewrite Tauto_match_nat_same.
  now rewrite List_nth_nil.
}
rewrite flat_map_concat_map.
Search (nth _ (concat _)).
...
        assert (H : nth i (all_comb n) [] ∈ all_comb n). {
          apply nth_In.
          now rewrite all_comb_length.
        }
        apply in_all_comb_iff in H.
        destruct H as (_ & Hnc & Hcn).
        remember (nth i (all_comb n) []) as l eqn:Hl.
        specialize (Hcn (nth j (collapse kl) 0)) as H1.
...
        remember (nth j (collapse kl) 0) as k eqn:Hk.
        rewrite <- Hnc.
Check In_nth.
...
        specialize (Hcn (nth j (collapse kl) 0)) as H1.
        assert (H : k ∈ l).
...
        specialize (Hgh _ H).
        unfold g1, h1 in Hgh.
        rewrite <- Hgh.
        rewrite (List_map_nth' 0).
        rewrite (List_map_nth' 0).
...
rewrite nth_list_prodn_same_length with (n := n). {
  now rewrite repeat_length.
} {
  intros l Hl.
  apply repeat_spec in Hl.
  rewrite Hl; apply seq_length.
} {
  now rewrite repeat_length.
}
...
Theorem nth_list_prodn_length : ∀ A (ll : list (list A)) i,
  i < ∏ (l ∈ ll), length l
  → length (nth i (list_prodn ll) []) = length ll.
Proof.
intros * Hi.
revert i Hi.
induction ll as [| l]; intros. {
  rewrite iter_list_empty in Hi; [ | easy ].
  now apply Nat.lt_1_r in Hi; subst i.
}
cbn.
destruct ll as [| l1]. {
  cbn.
  rewrite rngl_product_list_only_one in Hi.
  clear IHll.
  revert i Hi.
  induction l as [| a]; intros; [ easy | cbn ].
  destruct i; [ easy | ].
  cbn in Hi; apply Nat.succ_lt_mono in Hi.
  now apply IHl.
}
rewrite flat_map_concat_map.
Theorem length_nth_concat_same_length : ∀ A n i (lll : list (list (list A))),
  (∀ ll, ll ∈ lll → ∀ l, l ∈ ll → length l = n)
  → i < n ^ n
  → length (nth i (concat lll) []) = n.
...
rewrite (@length_nth_concat_same_length _ (length (l :: l1 :: ll))).
easy.
2: {
Search (∏ (_ ∈ _), _ = _ ^ _).
rewrite nat_product_same_length with (n := length (l :: l1 :: ll)) in Hi; [ easy | ].
...
Fixpoint nth_concat {A} i (ll : list (list A)) d :=
  match ll with
  | [] => d
  | l :: ll' =>
      if i <? length l then nth i l d
      else nth_concat (i - length l) ll' d
  end.
Check @nth_concat.
Theorem nth_concat_nth_concat : ∀ A (d : A) i ll,
  nth i (concat ll) d = nth_concat i ll d.
...
rewrite nth_concat_nth_concat.
...
Search (nth _ (concat _)).
...
rewrite flat_map_concat_map.
Search (nth _ (concat _)).
cbn - [ list_prodn ].
Search (nth _ (flat_map _ _)).
...
rewrite nth_list_prodn_length. 2: {
  erewrite rngl_product_list_eq_compat. 2: {
    intros l Hl.
    apply repeat_spec in Hl.
    rewrite Hl at 1.
    rewrite seq_length.
    easy.
  }
  cbn.
...
  eapply lt_le_trans; [ apply Hi | ].
  clear Hi.
  induction n; [ easy | ].
  unfold iter_list.
cbn.
  cbn - [ iter_list ].
    apply in_repeat in Hl.
apply repeat_length.
...
Search all_comb.
Check In_nth.
Check nth_In.
...
    erewrite map_ext_in. 2: {
      intros j Hj.
...
Compute (
  let n := 3 in
  let kl := [1;4;3] in
  let g1 := λ l, map (λ j : nat, nth j l 0) (collapse kl) in
  let h1 := λ l, map (λ j : nat, nth j l 0) (isort_rank Nat.leb kl) in
  let f := λ i, all_comb_inv n (g1 (nth i (all_comb n) [])) in
  map (λ x,
  nth x (all_comb n) [] = nth (f x) (map h1 (all_comb n)) [])
  (seq 0 (n ^ n))
).
...
  exists (λ i, all_comb_inv i (g1 (nth i (all_comb n) []))).
  split; [ | split ]. 3: {
    intros i Hi.
    unfold g1, h1.
    rewrite (List_map_nth' []).
    erewrite map_ext_in. 2: {
      intros j Hj.
      replace (...
(* ouais, en fait, j'en sais rien, je fais ça au pif *)
...
Compute (all_comb_inv 3 [1;1;3]).
Check map_map.
Check all_comb_inv.
Check (λ i, g1 (nth i (all_comb n) [])).
...
apply rngl_summation_list_eq_compat.
intros l Hl.
f_equal.
unfold g1.
Search (ε (map _ _)).
Require Import RnglAlg.Zrl.
Require Import ZArith.
Open Scope Z_scope.
Compute (
  let kl := [5;1;2]%nat in
  let l := [1;3;2]%nat in
map (λ l,
  ε (map (λ j : nat, nth j l 0%nat) (collapse kl)) = (ε kl * ε l)%F)
  (all_comb 3)
).
...
rewrite (rngl_summation_list_permut _ (list_eqb Nat.eqb))
    with (l2 := all_comb n); [ | easy | ]. 2: {
  apply permutation_nth with (d := []); [ easy | ].
  rewrite map_length, all_comb_length; [ | easy ].
  split; [ easy | ].
Compute (
  let kl := [5;1;2] in
  let h1 := λ l : list nat, map (λ j : nat, nth j l 0) (isort_rank Nat.leb kl) in
  let n := length kl in
  map h1 (all_comb n)
).
...
  exists (λ i, nth i (map g1 (all_comb n)) []).
...
nth (f x) (map h1 (all_comb n)) []) = h1 (nth (f x) (all_comb n) [])
...
nth x (all_comb n) [] =
map (λ j, nth j (nth (f x) (all_comb n) []) 0) (isort_rank Nat.leb kl)
...
Check List_map_nth'.
...
Compute (
  let kl := [5;1;2] in
  let h1 := λ l : list nat, map (λ j : nat, nth j l 0) (isort_rank Nat.leb kl) in
  let n := length kl in
  map h1 (all_comb n)
).
...
  clear - Hn.
  symmetry in Hn.
  subst h1.
...
  revert kl Hn.
  induction n; intros; [ easy | ].
  cbn - [ seq ].
  remember (repeat (seq 1 (S n)) n) as ll eqn:Hll; symmetry in Hll.
  destruct ll as [| l]. {
    destruct kl as [| k]; [ easy | ].
    cbn in Hn; apply Nat.succ_inj in Hn.
    apply List_eq_repeat_nil in Hll.
    move Hll at top; subst n.
    now apply length_zero_iff_nil in Hn; subst kl.
  }
...
Search (permutation _ (flat_map _ _)).
Search (permutation _ (concat _)).
rewrite flat_map_concat_map.
Search (map (concat _)).
...
Check permutation_swap.
  ∀ (A : Type) (eqb rel : A → A → bool), equality eqb → ∀ l : list A, permutation eqb l (isort rel l)
...
Compute (
  let kl := [5;1;2] in
  let h1 := λ l : list nat, map (λ j : nat, nth j l 0) (isort_rank Nat.leb kl) in
  let n := length kl in
  map h1 (all_comb n)
).
Require Import RnglAlg.Zrl.
Require Import ZArith.
Open Scope Z_scope.
Compute (
  let A := mk_mat [[11;12;13];[21;22;23];[31;32;33];[41;42;43]]%Z in
  let kl := [1;4;3]%nat in
  let n := length kl in
  let f := filter (λ x, negb (Z.eqb (fst x) 0)) in
  let g1 := λ l, map (λ j, nth j l 0%nat) (collapse kl) in
(
  (f (map (λ l, (ε (g1 l), map (λ i, mat_el (mat_select_rows kl A) i (ff_app (g1 l) (i - 1))) (seq 1 n))) (all_comb n))) =
  f (map (λ i,
  (ε kl * ε i, map (λ i0, mat_el (mat_select_rows (isort Nat.leb kl) A) i0 (ff_app i (i0 - 1))) (seq 1 n))) (all_comb n))
)%F
).
...
(
  (f (map (λ l, (ε l, map (λ i, mat_el (mat_select_rows kl A) i (ff_app (map (λ j, nth j l 0) (isort_rank Nat.leb kl)) (i - 1))) (seq 1 n))) (all_comb n))) =
  f (map (λ i,
  (ε i, map (λ i0, mat_el (mat_select_rows (isort Nat.leb kl) A) i0 (ff_app i (i0 - 1))) (seq 1 n))) (all_comb n))
)%F
).
...
Compute (
  let A := mk_mat [[11;12;13];[21;22;23];[31;32;33];[41;42;43]]%Z in
  let kl := [1;4;3]%nat in
  let n := length kl in
  let f := filter (λ x, negb (Z.eqb (fst x) 0)) in
(
  (f (map (λ l, (ε l, map (λ i, mat_el (mat_select_rows kl A) i (ff_app l (i - 1))) (seq 1 n))) (all_comb n))) =
  f (map (λ i,
  (ε i, map (λ i0, mat_el (mat_select_rows (isort Nat.leb kl) A) i0 (ff_app i (i0 - 1))) (seq 1 n))) (all_comb n))
)%F
).
...
Compute (
  let A := mk_mat [[11;12;13];[21;22;23];[31;32;33];[41;42;43]]%Z in
  let kl := [1;4;3]%nat in
  let n := length kl in
(
  map (λ l, (ε l, map (λ i, mat_el (mat_select_rows kl A) i (ff_app l (i - 1))) (seq 1 n))) (all_comb n) =
  map (λ i,
  (ε i, map (λ i0, mat_el (mat_select_rows (isort Nat.leb kl) A) i0 (ff_app i (i0 - 1))) (seq 1 n))) (all_comb n)
)%F
).
...
Compute (
  let A := mk_mat [[1;2];[3;-4];[-5;6]]%Z in
  let kl := [3;1] in
  let n := length kl in
  ∑ (l ∈ all_comb n), ε l * ∏ (i = 1, n), mat_el (mat_select_rows kl A) i (ff_app l (i - 1)) =
  ∑ (i ∈ all_comb n),
  ε kl * ε i * ∏ (i0 = 1, n), mat_el (mat_select_rows (isort Nat.leb kl) A) i0 (ff_app i (i0 - 1))
).
...
rewrite isort_isort_rank with (d := 0).
erewrite rngl_summation_list_change_var with (h := isort_rank Nat.leb).
(* truc comme ça... *)
...
rewrite rngl_summation_list_map.
...
isort_isort_rank:
  ∀ (A : Type) (rel : A → A → bool) (d : A) (l : list A),
    isort rel l = map (λ i : nat, nth i l d) (isort_rank rel l)
(*
Require Import RnglAlg.Zrl.
Require Import ZArith.
Compute (
  let A := mk_mat [[1;2;3];[4;5;6];[-7;8;9];[10;-11;12]]%Z in
  let kl := [1;4;3] in
  let n := length kl in
  ∑ (l ∈ all_comb n), ε l * ∏ (i = 1, n), mat_el (mat_select_rows kl A) i (ff_app l (i - 1)) =
  ∑ (i ∈ all_comb n),
  ε kl * ε i * ∏ (i0 = 1, n), mat_el (mat_select_rows (isort Nat.leb kl) A) i0 (ff_app i (i0 - 1))
).
*)
...

Theorem cauchy_binet_formula : in_charac_0_field →
  ∀ m n A B,
  is_correct_matrix A = true
  → is_correct_matrix B = true
  → mat_nrows A = m
  → mat_ncols A = n
  → mat_nrows B = n
  → mat_ncols B = m
  → det (A * B) =
     ∑ (jl ∈ map (map S) (sub_lists_of_seq_0_n n m)),
     det (mat_select_cols jl A) * det (mat_select_rows jl B).
Proof.
intros Hif * Hca Hcb Har Hac Hbr Hbc.
(*
Require Import RnglAlg.Zrl.
Require Import ZArith.
Compute (
  let m := 2 in
  let n := 3 in
map (map S) (sub_lists_of_seq_0_n n m)).
  let A := mk_mat [[1;2;3];[4;5;6]]%Z in
  let B := mk_mat [[7;8];[9;10];[11;12]]%Z in
     det (A * B) =
     ∑ (jl ∈ map (map S) (sub_lists_of_seq_0_n n m)),
     det (mat_select_cols jl A) * det (mat_select_rows jl B)
).
...
*)
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
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  apply is_scm_mat_iff in Hca.
  destruct Hca as (Hcra, Hcla).
  specialize (Hcra Hac) as H1.
  now rewrite Har in H1.
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
(**)
rewrite det_is_det'; try now destruct Hif.
rewrite det'_is_det''; try now destruct Hif. 2: {
  now rewrite mat_mul_nrows, Har.
}
unfold det''.
rewrite mat_mul_nrows, Har.
unfold "*"%M at 1.
unfold mat_mul_el.
rewrite Har, Hac, Hbc.
cbn - [ det ].
erewrite rngl_summation_list_eq_compat. 2: {
  intros l Hl.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    specialize (fact_neq_0 m) as Hm.
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hi ].
    rewrite seq_nth; [ | flia Hi ].
    rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
    assert (Him : ff_app l (i - 1) - 1 < m). {
      apply in_all_comb_iff in Hl.
      destruct Hl as (_ & Hlm & Hl).
      unfold ff_app.
      assert (H : nth (i - 1) l 0 ∈ l). {
        apply nth_In.
        rewrite Hlm; flia Hi.
      }
      specialize (Hl _ H); clear H.
      flia Hl.
    }
    rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
    rewrite seq_nth; [ | easy ].
    rewrite Nat.add_comm, Nat.sub_add. 2: {
      apply in_all_comb_iff in Hl.
      destruct Hl as (_ & Hlm & Hl).
      unfold ff_app.
      assert (H : nth (i - 1) l 0 ∈ l). {
        apply nth_In.
        rewrite Hlm; flia Hi.
      }
      now specialize (Hl _ H); clear H.
    }
    easy.
  }
  easy.
}
cbn - [ det ].
(*
  ∑ (l ∈ all_comb m),
  ε l *
  ∏ (i = 1, m), (∑ (j = 1, n), mat_el A i j * mat_el B j (ff_app l (i - 1)))
*)
erewrite rngl_summation_list_eq_compat. 2: {
  intros l Hl.
  rewrite rngl_product_summation_distr_prodn; [ | | easy ]. 2: {
    now destruct Hif; left.
  }
  erewrite rngl_summation_list_eq_compat. 2: {
    intros l1 Hl1.
    erewrite rngl_product_eq_compat. 2: {
      intros i Hi.
      now rewrite fold_ff_app.
    }
    cbn.
    rewrite rngl_product_mul_distr; [ | now destruct Hif ].
    easy.
  }
  cbn.
  rewrite rngl_mul_summation_list_distr_l; [ | now destruct Hif; left ].
  easy.
}
cbn - [ det ].
rewrite rngl_summation_summation_list_swap.
erewrite rngl_summation_list_eq_compat. 2: {
  intros l Hl.
  erewrite rngl_summation_list_eq_compat. 2: {
    intros l1 Hl1.
    rewrite rngl_mul_comm; [ | now destruct Hif ].
    rewrite rngl_mul_mul_swap; [ | now destruct Hif ].
    rewrite <- rngl_mul_assoc.
    easy.
  }
  cbn.
  rewrite <- rngl_mul_summation_list_distr_l; [ | now destruct Hif; left ].
  easy.
}
cbn - [ det ].
(*
  ∑ (k ∈ list_prodn (repeat (seq 1 n) m)),
  ∏ (i = 1, m), mat_el A i (ff_app k (i - 1)) *
  (∑ (l ∈ all_comb m),
   ε l * ∏ (i = 1, m), mat_el B (ff_app k (i - 1)) (ff_app l (i - 1)))
*)
erewrite rngl_summation_list_eq_compat. 2: {
  intros l Hl.
  replace (∑ (i ∈ all_comb m), ε i * ∏ (j = _, _), _) with
    (det (mat_select_rows l B)). 2: {
    generalize Hl; intros H.
    apply in_list_prodn_repeat_iff in H.
    destruct H as (_ & Hlm & Hln).
    rewrite det_is_det'; try now destruct Hif. 2: {
      apply mat_select_rows_is_square; [ easy | congruence | ].
      rewrite Hbr.
      intros j Hj.
      now apply Hln.
    }
    rewrite det'_is_det''; try now destruct Hif. 2: {
      rewrite mat_select_rows_nrows; congruence.
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
    assert (H1 : ff_app l1 (i - 1) - 1 < m). {
      unfold ff_app.
      apply in_list_prodn_repeat_iff in Hl1.
      destruct Hl1 as (_ & Hl1m & Hl1).
      specialize (Hl1 (nth (i - 1) l1 0)).
      assert (H : nth (i - 1) l1 0 ∈ l1). {
        apply nth_In; rewrite Hl1m; flia Hi.
      }
      specialize (Hl1 H); clear H.
      flia Hl1.
    }
    rewrite (List_map_nth' 0); [ | now rewrite seq_length, Hbc ].
    rewrite seq_nth; [ | now rewrite Hbc ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  easy.
}
cbn - [ det ].
(*
  ∑ (kl ∈ list_prodn (repeat (seq 1 n) m)),
  ∏ (j = 1, m), mat_el A j (ff_app kl (j - 1)) * det (mat_select_rows kl B)
*)
(*
Compute (
let m := 3 in
let n := 4 in
sub_lists_of_seq_0_n n m
).
Compute (
let m := 3 in
let n := 4 in
list_prodn (repeat (seq 1 n) m)
).
*)
(* I must prove that
     det (mat_select_rows kl B) = ε(kl) det (mat_select_rows jl B)
   where jl is ordered kl
*)
Require Import RnglAlg.Zrl.
Require Import ZArith.
Compute (
  let m := 2 in
  let n := 3 in
  let A := mk_mat [[-1;2;-3];[4;5;-6]]%Z in
  let B := mk_mat [[7;8];[9;10];[11;12]]%Z in
  ∑ (i ∈ list_prodn (repeat (seq 1 n) m)),
(*
  ∏ (i0 = 1, m), mat_el A i0 (ff_app i (i0 - 1)) *
  ε i * det (mat_select_rows (isort Nat.leb i) B) =
*)
(*
  (if is_sorted Nat.leb i then
  det (mat_select_cols i A) else 0%Z) *
  det (mat_select_rows i B) =
*)
(*
  det (mat_select_cols i A) *
  (if is_sorted Nat.leb i then
   det (mat_select_rows i B) else 0%Z) =
*)
(*
  (if is_sorted Nat.leb i then
  det (mat_select_cols i A) else 0%Z) *
  (if is_sorted Nat.leb i then
   det (mat_select_rows i B) else 0%Z) =
*)
(*
  (if is_sorted Nat.leb i then
     det (mat_select_cols i A) * det (mat_select_rows i B)
   else 0) =
*)
(* non
  det (mat_select_cols (isort Nat.leb i) A) *
   det (mat_select_rows (isort Nat.leb i) B) =
*)
  ∑ (jl ∈ map (map S) (sub_lists_of_seq_0_n n m)),
  det (mat_select_cols jl A) * det (mat_select_rows jl B)
).
(*
 map (map S) (sub_lists_of_seq_0_n n m)).
list_prodn (repeat (seq 1 n) m)).
let i := [3;3] in
 det (mat_select_rows i B)).
  ∑ (i ∈ list_prodn (repeat (seq 1 n) m)),
  ∏ (i0 = 1, m), mat_el A i0 (ff_app i (i0 - 1)) * det (mat_select_rows i B) =
  ∑ (jl ∈ map (map S) (sub_lists_of_seq_0_n n m)),
  det (mat_select_cols jl A) * det (mat_select_rows jl B)
).
*)
...
erewrite rngl_summation_list_eq_compat. 2: {
  intros kl Hkl.
(**)
  replace (det (mat_select_rows kl B)) with
    (ε kl * det (mat_select_rows (isort Nat.leb kl) B))%F. 2: {
...
    symmetry; apply det_isort_rows.
...
  }
  rewrite rngl_mul_comm; [ | now destruct Hif ].
  rewrite rngl_mul_mul_swap; [ | now destruct Hif ].
  replace (ε kl * ∏ (i = 1, m), mat_el A i (ff_app kl (i - 1)))%F with
    (det (mat_select_cols (isort Nat.eqb kl) A)). 2: {
...
  }
  easy.
}
cbn - [ det ].
...
  replace (∏ (i = 1, m), mat_el A i (ff_app k (i - 1))) with
    (det (mat_select_cols k A)). 2: {
    rewrite det_is_det'; try now destruct Hif. 2: {
      apply in_list_prodn_repeat_iff in Hk.
      destruct Hk as (_ & Hkm & Hk).
      apply mat_select_cols_is_square; [ easy | congruence | ].
      now rewrite Hac.
    }
    rewrite det'_is_det''; try now destruct Hif. 2: {
      unfold mat_select_cols.
      rewrite mat_transp_nrows.
      rewrite mat_select_rows_ncols. 2: {
        apply in_list_prodn_repeat_iff in Hk.
        destruct Hk as (_ & Hkm & Hk).
        now intros H; subst k; symmetry in Hkm.
      }
      rewrite mat_transp_ncols.
      rewrite Hac, Har.
      now apply Nat.eqb_neq in Hnz; rewrite Hnz.
    }
    unfold det''.
    rewrite mat_select_cols_nrows; [ | | now rewrite Hac ]. 2: {
      apply in_list_prodn_repeat_iff in Hk.
      destruct Hk as (_ & Hkm & Hk).
      now intros H; subst k; symmetry in Hkm.
    }
    rewrite Har.
...
*)

(*
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
...
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
*)

End a.
