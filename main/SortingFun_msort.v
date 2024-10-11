(* merge sort *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Import List.ListNotations.

Require Import Misc PermutationFun.
Require Import SortingFun_common.

Fixpoint merge_loop {A} (rel : A → A → bool) it la lb :=
  match it with
  | 0 => []
  | S it' =>
      match la, lb with
      | [], _ => lb
      | _, [] => la
      | a :: la', b :: lb' =>
          if rel a b then a :: merge_loop rel it' la' lb
          else b :: merge_loop rel it' la lb'
      end
  end.

Definition merge {A} (rel : A → A → bool) la lb :=
  merge_loop rel (length la + length lb) la lb.

Fixpoint split_list {A} (la : list A) :=
  match la with
  | [] | [_] => (la, [])
  | a :: b :: lb =>
      let (l1, l2) := split_list lb in
      (a :: l1, b :: l2)
  end.

Fixpoint msort_loop {A} (rel : A → A → bool) it la :=
  match it with
  | 0 => la
  | S it' =>
      let (l1, l2) := split_list la in
      let l3 := msort_loop rel it' l1 in
      let l4 := msort_loop rel it' l2 in
      merge rel l3 l4
  end.

Definition msort {A} (rel : A → _) la :=
  msort_loop rel (length la) la.

Theorem fold_merge : ∀ A (rel : A → _) la lb,
  merge_loop rel (length la + length lb) la lb = merge rel la lb.
Proof. easy. Qed.

Theorem merge_loop_length : ∀ A (rel : A → _) la lb it,
  length (la ++ lb) ≤ it
  → length (merge_loop rel it la lb) = length (la ++ lb).
Proof.
intros * Hit.
revert la lb Hit.
induction it; intros; cbn. {
  apply Nat.le_0_r, List.length_zero_iff_nil in Hit.
  now rewrite Hit.
}
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ now cbn; rewrite List.app_nil_r | ].
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; cbn; f_equal. {
  apply IHit; cbn in Hit.
  now apply Nat.succ_le_mono in Hit.
}
rewrite IHit; cbn. {
  do 2 rewrite List.length_app; cbn.
  symmetry; apply Nat.add_succ_r.
} {
  rewrite List.length_app in Hit; cbn in Hit.
  apply Nat.succ_le_mono in Hit.
  now rewrite Nat.add_succ_r, <- List.length_app in Hit.
}
Qed.

Theorem merge_length : ∀ A (rel : A → _) la lb,
  length (merge rel la lb) = length (la ++ lb).
Proof.
intros.
unfold merge.
apply merge_loop_length.
now rewrite List.length_app.
Qed.

Theorem split_list_length : ∀ A la (lb lc : list A),
  split_list la = (lb, lc)
  → length la = length lb + length lc.
Proof.
intros * Hs.
remember (length la) as len eqn:Hlen; symmetry in Hlen |-*.
revert la lb lc Hs Hlen.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct la as [| a]. {
  now injection Hs; clear Hs; intros; subst lb lc.
}
destruct la as [| b]. {
  now injection Hs; clear Hs; intros; subst lb lc.
}
cbn in Hs, Hlen.
remember (split_list la) as ll eqn:Hll; symmetry in Hll.
destruct ll as (ld, le).
injection Hs; clear Hs; intros; subst lb lc.
destruct len; [ easy | ].
destruct len; [ easy | cbn ].
rewrite Nat.add_succ_r; f_equal; f_equal.
do 2 apply Nat.succ_inj in Hlen.
apply (IHlen len) in Hll; [ easy | | easy ].
now transitivity (S len).
Qed.

Theorem msort_loop_length : ∀ A (rel : A → _) it la,
  length (msort_loop rel it la) = length la.
Proof.
intros.
revert la.
induction it; intros; [ easy | cbn ].
remember (split_list la) as ll eqn:Hll; symmetry in Hll.
destruct ll as (lb, lc).
rewrite merge_length.
rewrite List.length_app.
do 2 rewrite IHit.
now symmetry; apply split_list_length.
Qed.

Theorem msort_loop_nil : ∀ A (rel : A → _) it,
  msort_loop rel it [] = [].
Proof.
intros.
induction it; [ easy | cbn ].
now rewrite IHit; cbn.
Qed.

Theorem msort_loop_unit : ∀ A (rel : A → _) it a,
  msort_loop rel it [a] = [a].
Proof.
intros.
induction it; [ easy | cbn ].
now rewrite IHit, msort_loop_nil.
Qed.

Theorem msort_loop_pair : ∀ A (rel : A → _) it a b,
  rel a b = true
  → msort_loop rel it [a; b] = [a; b].
Proof.
intros * Hab.
induction it; [ easy | cbn ].
do 2 rewrite msort_loop_unit; cbn.
now rewrite Hab.
Qed.

Theorem split_list_lengths : ∀ A (l la lb : list A),
  split_list l = (la, lb)
  → length la = length lb ∨ length la = S (length lb).
Proof.
intros * Hll.
remember (length l) as len eqn:Hlen.
revert l la lb Hlen Hll.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct l as [| a]; intros; cbn. {
  now injection Hll; intros; subst la lb; left.
}
destruct l as [| b]; intros; cbn. {
  now injection Hll; intros; subst la lb; right.
}
cbn in Hll.
remember (split_list l) as ll eqn:H; symmetry in H.
destruct ll as (lc, ld).
injection Hll; clear Hll; intros; subst la lb.
rename lc into la; rename ld into lb; rename H into Hll.
destruct len; [ easy | ].
destruct len; [ easy | ].
cbn in Hlen |-*.
do 2 apply Nat.succ_inj in Hlen.
specialize (IHlen len) as H1.
assert (H : len < S (S len)) by now transitivity (S len).
specialize (H1 H); clear H.
specialize (H1 l la lb Hlen Hll).
now destruct H1 as [H1| H1]; rewrite H1; [ left | right ].
Qed.
