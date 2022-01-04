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
Import List List.ListNotations.

Require Import Misc (*RingLike IterAdd IterMul*) Pigeonhole.
(*
Require Import Matrix PermutSeq Signature.
Require Import Determinant.
Import matrix_Notations.
*)

Section a.

Context {T : Type}.
(*
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).
*)

(* all lists [j1;j2;...jm] such that 0≤j1<j2<...<jm<n *)

Fixpoint ordered_tuples (n k : nat) : list (list nat) :=
  match k with
  | 0 => [[]]
  | S k' =>
      match n with
      | 0 => []
      | S n' =>
          ordered_tuples n' k ++
          map (λ l, l ++ [n']) (ordered_tuples n' k')
      end
  end.

Fixpoint ordered_tuple_rank n k (t : list nat) : nat :=
  match k with
  | 0 => 0
  | S k' =>
      match n with
      | 0 => 0
      | S n' =>
          if last t 0 =? n' then
            length (ordered_tuples n' k) +
            ordered_tuple_rank n' k' (removelast t)
          else
            ordered_tuple_rank n' k t
      end
  end.

(*
Compute (let n := 5 in map (λ i, let l := ordered_tuples n i in length l) (seq 0 (n + 3))).
Compute (let n := 5 in map (λ i, let l := ordered_tuples n i in (length l, l)) (seq 0 (n + 3))).
Compute (let '(n,k) := (5,3) in let ll := ordered_tuples n k in map (λ i, (i, ordered_tuple_rank n k (nth i ll []))) (seq 0 (length ll))).
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

Theorem ordered_tuples_length : ∀ k n,
  length (ordered_tuples n k) = binomial n k.
Proof.
intros.
revert k.
induction n; intros; [ now destruct k | ].
destruct k; [ easy | cbn ].
rewrite app_length, map_length.
rewrite IHn, IHn.
apply Nat.add_comm.
Qed.

Theorem ordered_tuple_length : ∀ n k t,
  t ∈ ordered_tuples n k → length t = k.
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

Theorem ordered_tuples_lt : ∀ k n t,
  t ∈ ordered_tuples n k
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

Fixpoint sorted {A} (ord : A → A → bool) l :=
  match l with
  | [] => true
  | [a] => true
  | a :: (b :: _) as la => (ord a b && sorted ord la)%bool
  end.

Definition transitive A (ord : A → A → bool) :=
  ∀ a b c, ord a b = true → ord b c = true → ord a c = true.

Theorem sorted_cons_cons_true_iff : ∀ A (ord : A → A -> bool) a b l,
  sorted ord (a :: b :: l) = true
  ↔ ord a b = true ∧ sorted ord (b :: l) = true.
Proof.
intros.
apply Bool.andb_true_iff.
Qed.

Theorem sorted_cons : ∀ A ord (a : A) l,
  sorted ord (a :: l) = true
  → sorted ord l = true.
Proof.
intros * Hsort.
destruct l as [| b]; [ easy | ].
now apply sorted_cons_cons_true_iff in Hsort.
Qed.

Theorem sorted_extends : ∀ A ord (a : A) l,
  transitive ord
  → sorted ord (a :: l) = true
  → ∀ b, b ∈ l → ord a b = true.
Proof.
intros * Htrans Hsort b Hb.
induction l as [| c]; [ easy | ].
apply sorted_cons_cons_true_iff in Hsort.
destruct Hsort as (Hac, Hsort).
destruct Hb as [Hb| Hb]; [ now subst c | ].
apply IHl; [ | easy ].
destruct l as [| d]; [ easy | ].
apply sorted_cons_cons_true_iff in Hsort.
apply sorted_cons_cons_true_iff.
destruct Hsort as (Hcd, Hsort).
split; [ now apply Htrans with (b := c) | easy ].
Qed.

Theorem sorted_app : ∀ A ord (la lb : list A),
  sorted ord (la ++ lb) = true
  → sorted ord la = true ∧ sorted ord lb = true ∧
    (transitive ord → ∀ a b, a ∈ la → b ∈ lb → ord a b = true).
Proof.
intros * Hab.
split. {
  revert lb Hab.
  induction la as [| a1]; intros; [ easy | ].
  destruct la as [| a2]; [ easy | ].
  cbn - [ sorted ] in Hab |-*.
  apply sorted_cons_cons_true_iff in Hab.
  apply sorted_cons_cons_true_iff.
  destruct Hab as (Haa & Hab).
  split; [ easy | ].
  now apply (IHla lb).
}
split. {
  revert lb Hab.
  induction la as [| a1]; intros; [ easy | ].
  destruct la as [| a2]. {
    cbn in Hab.
    destruct lb as [| b1]; [ easy | ].
    now apply Bool.andb_true_iff in Hab.
  }
  cbn - [ sorted ] in Hab.
  apply sorted_cons_cons_true_iff in Hab.
  destruct Hab as (Haa & Hab).
  now apply IHla.
} {
  intros Htrans * Ha Hb.
  revert a lb Ha Hab Hb.
  induction la as [| a1]; intros; [ easy | ].
  destruct Ha as [Ha| Ha]. 2: {
    apply (IHla a lb); [ easy | | easy ].
    cbn - [ sorted ] in Hab.
    now apply sorted_cons in Hab.
  }
  subst a1.
  cbn - [ sorted ] in Hab.
  apply sorted_extends with (l := la ++ lb); [ easy | easy | ].
  now apply in_or_app; right.
}
Qed.

Theorem sorted_any : ∀ A i j d (ord : A → A → bool) l,
  transitive ord
  → sorted ord l = true
  → i < j
  → j < length l
  → ord (nth i l d) (nth j l d) = true.
Proof.
intros * Htrans Hsort Hij Hj.
assert (Hi : i < length l) by now transitivity j.
specialize nth_split as H1.
specialize (H1 A i l d Hi).
destruct H1 as (la & lb & Hl & Hla).
...

(* *)

Theorem ordered_tuples_0_r : ∀ n, ordered_tuples n 0 = [[]].
Proof. now intros; destruct n. Qed.

Theorem ordered_tuples_out : ∀ n k,
  n < k
  → ordered_tuples n k = [].
Proof.
intros * Hnk.
revert k Hnk.
induction n; intros; cbn; [ now destruct k | ].
destruct k; [ easy | ].
apply Nat.succ_lt_mono in Hnk.
rewrite IHn; [ | flia Hnk ].
now rewrite IHn.
Qed.

Theorem ordered_tuple_rank_out : ∀ n k t,
  n < k
  → ordered_tuple_rank n k t = 0.
Proof.
intros * Hnk.
revert t k Hnk.
induction n; intros; cbn; [ now destruct k | ].
destruct k; [ easy | ].
apply Nat.succ_lt_mono in Hnk.
rewrite ordered_tuples_length.
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec (last t 0) n) as [Htn| Htn]. {
  rewrite IHn; [ | easy ].
  rewrite Nat.add_0_r.
  rewrite binomial_out; [ easy | flia Hnk ].
}
apply IHn; flia Hnk.
Qed.

Theorem ordered_tuple_rank_ub : ∀ n k t,
  k ≤ n
  → ordered_tuple_rank n k t < binomial n k.
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
  rewrite ordered_tuples_length, Nat.add_comm.
  apply Nat.add_lt_mono_r.
  now apply IHn.
} {
  destruct (Nat.eq_dec k n) as [Hk| Hk]. {
    subst k.
    rewrite ordered_tuple_rank_out; [ | easy ].
    now rewrite binomial_diag.
  }
  transitivity (binomial n (S k)); [ apply IHn; flia Hkn Hk | ].
  apply Nat.lt_add_pos_l.
  specialize (IHn k [] Hkn).
  flia IHn.
}
Qed.

Theorem ordered_tuple_rank_of_nth : ∀ n k i,
  i < binomial n k
  → ordered_tuple_rank n k (nth i (ordered_tuples n k) []) = i.
Proof.
intros * Hi.
revert k i Hi.
induction n; intros. {
  destruct k; [ now apply Nat.lt_1_r in Hi | easy ].
}
cbn.
rewrite ordered_tuples_length.
destruct k; [ now apply Nat.lt_1_r in Hi | ].
cbn in Hi.
destruct (lt_dec i (binomial n (S k))) as [Hik| Hik]. {
  rewrite app_nth1; [ | now rewrite ordered_tuples_length ].
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec _ n) as [Hlz| Hlz]; [ | now apply IHn ].
  exfalso.
  specialize (ordered_tuples_lt (S k) n) as H1.
  remember (ordered_tuples n (S k)) as ll eqn:Hll.
  specialize (H1 (nth i ll [])).
  assert (H : nth i ll [] ∈ ll). {
    now apply nth_In; rewrite Hll, ordered_tuples_length.
  }
  specialize (H1 H); clear H.
  specialize (H1 n).
  assert (H : n ∈ nth i ll []). {
    rewrite <- Hlz.
    rewrite List_last_nth.
    apply nth_In.
    apply Nat.sub_lt; [ | easy ].
    rewrite Hll.
    rewrite (ordered_tuple_length n (S k)); [ flia | ].
    apply nth_In.
    now rewrite ordered_tuples_length.
  }
  specialize (H1 H).
  now apply Nat.lt_irrefl in H1.
}
apply Nat.nlt_ge in Hik.
rewrite app_nth2; [ | now rewrite ordered_tuples_length ].
rewrite ordered_tuples_length.
remember (i - binomial n (S k)) as j eqn:Hj.
rewrite (List_map_nth' []); [ | rewrite ordered_tuples_length; flia Hi Hik Hj ].
rewrite last_last, Nat.eqb_refl.
rewrite removelast_last.
rewrite IHn; [ flia Hj Hik | flia Hi Hik Hj ].
Qed.

Theorem transitive_nat_lt : transitive Nat.ltb.
Proof.
intros a b c Hab Hbc.
apply Nat.ltb_lt in Hab, Hbc.
apply Nat.ltb_lt.
now transitivity b.
Qed.

Theorem nth_of_ordered_tuple_rank : ∀ n k t,
  sorted Nat.ltb t = true
  → length t = k
  → (∀ i, i ∈ t → i < n)
  → nth (ordered_tuple_rank n k t) (ordered_tuples n k) [] = t.
Proof.
intros * Hs Htk Hlt.
destruct (le_dec k n) as [Hkn| Hkn]. 2: {
  assert
    (Hsa : ∀ a i l,
        sorted Nat.ltb (a :: l) = true
        → i < length l
        → a = nth i l 0
        → False). {
    clear.
    intros * Hsort Hil Ha.
    destruct l as [| b]; [ cbn in Hil; flia Hil | ].
    apply sorted_cons_cons_true_iff in Hsort.
    destruct Hsort as (Hab & Hs).
    apply Nat.ltb_lt in Hab.
    specialize (@sorted_extends _ Nat.ltb b l) as H1.
    destruct i; [ cbn in Ha; flia Hab Ha | cbn in Ha ].
    specialize (H1 transitive_nat_lt).
    specialize (H1 Hs a).
    cbn in Hil.
    apply Nat.succ_lt_mono in Hil.
    assert (H : a ∈ l) by now subst a; apply nth_In.
    specialize (H1 H).
    apply Nat.ltb_lt in H1.
    flia Hab H1.
  }
  apply Nat.nle_gt in Hkn.
  rewrite ordered_tuple_rank_out; [ | easy ].
  rewrite ordered_tuples_out; [ | easy ].
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
  clear - Hs Hx Hx' Hxxt Hsa.
  revert x x' Hx Hx' Hxxt.
  induction t as [| a]; intros; [ easy | ].
  destruct x. {
    destruct x'; [ easy | exfalso ].
    cbn in Hx'.
    apply Nat.succ_lt_mono in Hx'.
    now apply (Hsa a x' t).
  }
  cbn in Hx.
  apply Nat.succ_lt_mono in Hx.
  destruct x'. {
    exfalso.
    cbn in Hxxt; symmetry in Hxxt.
    now apply (Hsa a x t).
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
rewrite ordered_tuples_length.
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec (last t 0) n) as [Hln| Hln]. {
  rewrite app_nth2; [ | rewrite ordered_tuples_length; flia ].
  rewrite ordered_tuples_length.
  rewrite Nat.add_comm, Nat.add_sub.
  rewrite (List_map_nth' []). 2: {
    rewrite ordered_tuples_length.
    now apply ordered_tuple_rank_ub.
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
  specialize (Hs transitive_nat_lt i n Hi (or_introl eq_refl)).
  now apply Nat.ltb_lt in Hs.
}
destruct (lt_dec (ordered_tuple_rank n (S k) t) (binomial n (S k)))
    as [Hrb| Hrb]. {
  rewrite app_nth1; [ | now rewrite ordered_tuples_length ].
  destruct (Nat.eq_dec n k) as [Hnk| Hnk]. {
    subst k.
    rewrite ordered_tuple_rank_out in Hrb; [ cbn in Hrb | easy ].
    now rewrite binomial_out in Hrb.
  }
  apply IHn; [ easy | easy | | flia Hkn Hnk ].
  intros i Hi.
  clear - T Hs Hlt Hln Hi.
  specialize (Hlt i Hi) as H1.
  destruct (Nat.eq_dec i n) as [Hin| Hin]; [ | flia H1 Hin ].
  subst i; exfalso; clear H1.
  apply (In_nth _ _ 0) in Hi.
  destruct Hi as (m & Hmt & Hmn).
  assert (H : nth m t 0 < last t 0). {
...
    rewrite List_last_nth.
    specialize (@sorted_any nat m (length t - 1) 0 Nat.ltb t) as H1.
    specialize (H1 transitive_nat_lt Hs Hmt).
...

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

Theorem ordered_tuples_1_r : ∀ n,
  ordered_tuples n 1 = map (λ i, [i]) (seq 0 n).
Proof.
intros.
induction n; [ easy | ].
rewrite seq_S; cbn.
rewrite map_app; cbn.
rewrite <- IHn; f_equal.
now rewrite ordered_tuples_0_r.
Qed.

Theorem ordered_tuples_are_correct : ∀ k n t,
  k ≠ 0 → t ∈ ordered_tuples n k → t ≠ [].
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

Theorem ordered_tuples_sorted : ∀ k n ll,
  ll = ordered_tuples n k
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
specialize (ordered_tuples_lt _ _ _ Hl) as H1.
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

...

(* should be useless if there is an inverse *)
Theorem ordered_tuples_inj : ∀ k n ll,
  ll = ordered_tuples n k
  → ∀ i j, i < length ll → j < length ll →
   nth i ll [] = nth j ll [] → i = j.
Proof.
intros * Hll * Hi Hj Hij.
subst ll.
rewrite ordered_tuples_length in Hi, Hj.
revert k i j Hi Hj Hij.
induction n; intros. {
  destruct k; cbn in Hi, Hj; [ | easy ].
  apply Nat.lt_1_r in Hi, Hj; congruence.
}
destruct k. {
  cbn in Hi, Hj.
  apply Nat.lt_1_r in Hi, Hj; congruence.
}
cbn in Hi, Hj, Hij.
assert (H1 : ∀ i j,
  nth i (ordered_tuples n (S k)) [] =
  nth (j - binomial n (S k)) (ordered_tuples n k) [] ++ [n]
  → i < binomial n (S k)
  → binomial n (S k) ≤ j
  → False). {
  clear i j Hi Hj Hij.
  intros * Hij Hik Hjk.
  specialize ordered_tuples_lt as H1.
  specialize (H1 (S k) n).
  specialize (H1 (nth i (ordered_tuples n (S k)) [])).
  remember (ordered_tuples n (S k)) as ll eqn:Hll.
  assert (H : nth i ll [] ∈ ll). {
    apply nth_In; subst ll.
    now rewrite ordered_tuples_length.
  }
  specialize (H1 H); clear H.
  rewrite Hij in H1.
  specialize (H1 n).
  remember (ordered_tuples n k) as ll1 eqn:Hll1.
  assert (H : n ∈ nth (j - binomial n (S k)) ll1 [] ++ [n]). {
    now apply in_or_app; right; left.
  }
  specialize (H1 H); clear H.
  now apply Nat.lt_irrefl in H1.
}
destruct (lt_dec i (binomial n (S k))) as [Hik| Hik]. {
  rewrite app_nth1 in Hij; [ | now rewrite ordered_tuples_length ].
  destruct (lt_dec j (binomial n (S k))) as [Hjk| Hjk]. {
    rewrite app_nth1 in Hij; [ | now rewrite ordered_tuples_length ].
    now apply IHn in Hij.
  }
  apply Nat.nlt_ge in Hjk.
  rewrite app_nth2 in Hij; [ | now rewrite ordered_tuples_length ].
  rewrite ordered_tuples_length in Hij.
  rewrite (List_map_nth' []) in Hij. 2: {
    rewrite ordered_tuples_length; flia Hj Hjk.
  }
  exfalso; clear IHn Hi Hj.
  now apply (H1 i j).
}
apply Nat.nlt_ge in Hik.
rewrite app_nth2 in Hij; [ | now rewrite ordered_tuples_length ].
rewrite ordered_tuples_length in Hij.
rewrite (List_map_nth' []) in Hij. 2: {
  rewrite ordered_tuples_length; flia Hi Hik.
}
destruct (lt_dec j (binomial n (S k))) as [Hjk| Hjk]. {
  rewrite app_nth1 in Hij; [ | now rewrite ordered_tuples_length ].
  exfalso; clear IHn Hi Hj.
  now apply (H1 j i).
}
clear H1.
apply Nat.nlt_ge in Hjk.
rewrite app_nth2 in Hij; [ | now rewrite ordered_tuples_length ].
rewrite ordered_tuples_length in Hij.
rewrite (List_map_nth' []) in Hij. 2: {
  rewrite ordered_tuples_length; flia Hj Hjk.
}
apply app_inv_tail_iff in Hij.
specialize (IHn k (i - binomial n (S k)) (j - binomial n (S k))).
assert (H : i - binomial n (S k) < binomial n k) by flia Hi Hik.
specialize (IHn H); clear H.
assert (H : j - binomial n (S k) < binomial n k) by flia Hj Hjk.
specialize (IHn H); clear H.
specialize (IHn Hij).
flia IHn Hik Hjk.
Qed.

Theorem ordered_tuples_surj : ∀ m n ll,
  ll = ordered_tuples n m
  → (∀ l, l ∈ ll → ∃ i, nth i ll [] = l).
Proof.
intros * Hll * Hl.
Print Module Sorted.
...

Theorem ordered_tuples_prop : ∀ m n ll,
  ll = ordered_tuples n m
  → (∀ l, l ∈ ll → Sorted lt l) ∧
    (∀ i j, i < length ll → j < length ll →
     nth i ll [] = nth j ll [] → i = j) ∧
    (∀ l, l ∈ ll → ∃ i, nth i ll [] = l).
Proof.
intros * Hll.
split. {
  intros l Hl.
...

(* TODO: see https://fr.wikipedia.org/wiki/Formule_de_Binet-Cauchy *)

...

Theorem ordered_tuples_id : ∀ n, ordered_tuples n n = [seq 0 n].
Proof.
intros.
induction n; [ easy | ].
cbn - [ seq "<?" ].
rewrite seq_S; cbn - [ "<?" ].
rewrite flat_map_app, filter_app.
cbn - [ "<?" ].
rewrite app_nil_r.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
rewrite flat_map_concat_map.
rewrite <- concat_filter_map.
rewrite map_map.
rewrite <- flat_map_concat_map.
replace (filter (forallb _) _) with ([] : list (list nat)). 2: {
  symmetry.
  clear IHn.
  remember (ordered_tuples _ _) as ll eqn:Hll.
  assert (H1 : ∀ t, t ∈ ll → t ≠ []). {
    specialize ordered_tuples_are_correct as H1.
    specialize (H1 n (S n)).
    rewrite <- Hll in H1.
    intros t Ht.
    now apply H1.
  }
  clear Hll.
  induction ll as [| l]; [ easy | ].
  cbn - [ "<?" ].
  rewrite IHll; [ | now intros; apply H1; right ].
  cbn; rewrite Nat.leb_refl, Bool.andb_true_l.
  remember (forallb _ _) as b eqn:Hb.
  symmetry in Hb.
  destruct b; [ exfalso | easy ].
  specialize (proj1 (forallb_forall _ _) Hb) as H2.
  cbn in H2.
  specialize (H1 l (or_introl eq_refl)).
  destruct l as [| a]; [ easy | ].
  cbn in H2.
  specialize (H2 _ (or_introl eq_refl)).
  apply Nat.leb_le, Nat.nlt_ge in H2.
  apply H2; flia.
}
rewrite app_nil_r.
rewrite flat_map_concat_map.
rewrite <- map_map.
rewrite concat_filter_map.
Compute (let n := 5 in (ordered_tuples n 0, ordered_tuples n n)).
Compute (let n := 5 in map (λ i, ordered_tuples (S i) i) (seq 0 n)).
(* bof, chais pas *)
(* bon, je vais essayer de faire un théorème qui prouve les
   propriétés de ordered_tuples (triés, injectif, surjectif)
   pour voir si ça peut m'aider pour ce théorème-ci ; ça sera
   de toutes façons utile, même si ça ne marche pas ici *)
...
rewrite <- flat_map_concat_map.
...
rewrite <- concat_filter_map.
rewrite map_map.
rewrite <- flat_map_concat_map.
...
Search (filter _ (map _ _)).
...
rewrite concat_filter_map.
Print ordered_tuples.
...
concat_filter_map:
  ∀ (A : Type) (f : A → bool) (l : list (list A)),
    concat (map (filter f) l) = filter f (concat l)
...
Search (forallb _ _ = true).
apply forallb_forall in Hb.
...
  erewrite filter_ext. 2: {
    intros l.
    replace (forallb _ _) with false. 2: {
      symmetry.
      apply Bool.negb_true_iff.
      apply Bool.eq_true_not_negb.
      intros H1.
      specialize (proj1 (forallb_forall _ l) H1) as H2.
      cbn - [ "<?" ] in H2.
      destruct l as [| a]. {
        cbn in H1.
...
apply -> forallb_forall in H.
Print forallb.
...
  induction n; [ easy | clear Hnz ].
  destruct n; [ easy | ].
  specialize (IHn (Nat.neq_succ_0 _)).

cbn.
  induction n; cbn.
...
Search (forallb _ _ = false).
Search (filter _ _ = []).
Search (map _ (filter _ _)).
...
concat_filter_map:
  ∀ (A : Type) (f : A → bool) (l : list (list A)),
    concat (map (filter f) l) = filter f (concat l)
...
rewrite map_app; cbn.
rewrite concat_app; cbn.
...

(* https://proofwiki.org/wiki/Cauchy-Binet_Formula *)
Theorem cauchy_binet_formula : in_charac_0_field →
  ∀ m n A B,
  is_correct_matrix A = true
  → is_correct_matrix B = true
  → mat_nrows A = m
  → mat_ncols A = n
  → mat_nrows B = n
  → mat_ncols B = m
  → det (A * B) =
     ∑ (jl ∈ ordered_tuples n m,
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
assert (ordered_tuples m m = [seq 0 m]).
...

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
  unfold ε.
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
  unfold ε, iter_seq, iter_list; cbn.
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
  unfold ε; cbn.
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
