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

(* *)

Theorem sorted_merge_loop_cons_cons_r_aux : ∀ {A} {rel : A → _},
  antisymmetric rel →
  transitive rel →
  ∀ n it l la lb a b,
  length (List.repeat a (n + n) ++ a :: b :: l) ≤ n + it
  → rel a a = true
  → sorted rel (a :: b :: l)
  → split_list l = (la, lb)
  → merge_loop rel it la (List.repeat a n ++ a :: b :: lb) =
    merge_loop rel it (a :: la) (List.repeat a n ++ b :: lb).
Proof.
intros * Hant Htra * Hit Haa Hs Hla.
rewrite List.length_app, List.repeat_length in Hit; cbn in Hit.
rewrite <- Nat.add_assoc in Hit.
apply Nat.add_le_mono_l in Hit.
do 2 rewrite Nat.add_succ_r in Hit.
revert n l la lb a b Hit Haa Hs Hla.
induction it; intros; [ easy | ].
destruct l as [| c]. {
  injection Hla; clear Hla; intros; subst la lb.
  unfold sorted in Hs.
  cbn in Hs; rewrite Bool.andb_true_r in Hs.
  rename Hs into Hab.
  destruct n; cbn. {
    rewrite Hab.
    destruct it; [ flia Hit | easy ].
  }
  rewrite Haa; f_equal.
  destruct it; [ flia Hit | ].
  clear Hit; cbn.
  induction n; [ easy | cbn ].
  now f_equal.
}
destruct l as [| d]. {
  injection Hla; clear Hla; intros; subst la lb.
  unfold sorted in Hs.
  cbn in Hs |-*.
  remember (rel a b) as ab eqn:Hab; symmetry in Hab.
  remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
  destruct ab; [ | easy ].
  destruct bc; [ clear Hs | easy ].
  destruct n. {
    cbn; rewrite Hab.
    remember (rel c a) as ca eqn:Hca; symmetry in Hca.
    destruct ca; [ | easy ].
    specialize (Htra a b c Hab Hbc) as Hac.
    specialize (Hant a c Hac Hca) as H; subst c.
    specialize (Hant a b Hab Hbc) as H; subst b.
    clear Hac Hca Hbc Hab.
    f_equal.
    destruct it; [ easy | cbn ].
    rewrite Haa.
    destruct it; [ | easy ].
    cbn in Hit; flia Hit.
  }
  cbn.
  rewrite Haa.
  remember (rel c a) as ca eqn:Hca; symmetry in Hca.
  destruct ca. {
    specialize (Htra a b c Hab Hbc) as Hac.
    specialize (Hant a c Hac Hca) as H; subst c.
    specialize (Hant a b Hab Hbc) as H; subst b.
    clear Hab Hac Hca Hbc.
    f_equal.
    destruct it; [ flia Hit | cbn ].
    rewrite Haa; f_equal.
    destruct it; [ flia Hit | cbn; clear Hit ].
    induction n; [ easy | cbn ].
    now f_equal.
  }
  f_equal.
  clear Hit IHit.
  revert it.
  induction n; intros; [ easy | cbn ].
  destruct it; [ easy | cbn ].
  rewrite Hca.
  f_equal; apply IHn.
}
cbn in Hla.
remember (split_list l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hla; clear Hla; intros; subst la lb.
rename lc into la; rename ld into lb; rename Hlc into Hla; cbn.
remember (d :: l) as l'; cbn in Hs; subst l'.
unfold sorted in Hs; cbn in Hs.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
remember (rel c d) as cd eqn:Hcd; symmetry in Hcd.
destruct ab; [ | easy ].
destruct bc; [ | easy ].
destruct cd; [ | easy ].
remember (d :: l) as l'; cbn in Hs; subst l'.
destruct n. {
  cbn; rewrite Hab.
  remember (rel c a) as ca eqn:Hca; symmetry in Hca.
  destruct ca; [ | easy ].
  specialize (Htra a b c Hab Hbc) as Hac.
  specialize (Hant a c Hac Hca) as H; subst c.
  specialize (Hant a b Hab Hbc) as H; subst b.
  clear Hab Hbc Hac Hca.
  rename d into b; rename Hcd into Hab.
  f_equal.
  specialize (IHit 1 l la lb a b) as H1.
  cbn in Hit, H1.
  assert (H : S (S (S (length l))) ≤ it) by flia Hit.
  specialize (H1 H Haa); clear H.
  assert (H : sorted rel (a :: b :: l)). {
    unfold sorted; cbn.
    remember (b :: l) as l'; cbn; subst l'.
    now rewrite Hab, Hs.
  }
  apply (H1 H Hla).
}
cbn.
remember (rel c a) as ca eqn:Hca; symmetry in Hca.
rewrite Haa.
destruct ca. {
  specialize (Htra a b c Hab Hbc) as Hac.
  specialize (Hant a c Hac Hca) as H; subst c.
  specialize (Hant a b Hab Hbc) as H; subst b.
  f_equal.
  rewrite List_app_cons, List.app_assoc.
  rewrite <- List.repeat_cons; symmetry.
  rewrite List_app_cons, List.app_assoc.
  rewrite <- List.repeat_cons; symmetry.
  do 2 rewrite List.app_comm_cons.
  replace (a :: a :: List.repeat a n) with (List.repeat a (S (S n))) by easy.
  cbn in Hit.
  apply IHit with (l := l); [ flia Hit | easy | | easy ].
  remember (d :: l) as l'; cbn; subst l'.
  unfold sorted; cbn.
  now rewrite Hcd, Hs.
} {
  f_equal.
  rewrite IHit with (l := c :: d :: l); [ | flia Hit | easy | | ]; cycle 1. {
    unfold sorted.
    remember (d :: l) as l'; cbn; subst l'.
    now rewrite Hab, Hbc, Hcd.
  } {
    now cbn; rewrite Hla.
  }
  destruct it; [ easy | cbn ].
  rewrite Hca.
  destruct n; cbn; [ now rewrite Hab | ].
  now rewrite Haa.
}
Qed.

Theorem sorted_merge_loop_cons_cons_r : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
   ∀ it l la lb a b,
   S (S (length l)) ≤ it
   → rel a a = true
   → sorted rel (a :: b :: l)
   → split_list l = (la, lb)
   → merge_loop rel it la (a :: b :: lb) =
     merge_loop rel it (a :: la) (b :: lb).
Proof.
intros * Hant Htra * Hit Haa Hs Hll.
specialize (sorted_merge_loop_cons_cons_r_aux Hant Htra 0) as H1.
now apply (H1 it l).
Qed.

Theorem sorted_merge_loop : ∀ A (rel : A → _),
  total_relation rel →
  ∀ it la lb,
  length la + length lb ≤ it
  → sorted rel la
  → sorted rel lb
  → sorted rel (merge_loop rel it la lb).
Proof.
intros * Htot * Hit Hla Hlb.
revert la lb Hit Hla Hlb.
induction it; intros; [ easy | cbn ].
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | ].
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  cbn.
  remember (merge_loop rel it la (b :: lb)) as lc eqn:Hlc.
  symmetry in Hlc.
  destruct lc as [| c]; [ easy | ].
  rewrite List_cons_length, Nat.add_succ_l in Hit.
  apply Nat.succ_le_mono in Hit.
  specialize (IHit la (b :: lb) Hit) as H1.
  assert (H : sorted rel la) by now apply sorted_cons in Hla.
  specialize (H1 H Hlb); clear H.
  rewrite Hlc in H1.
  unfold sorted in H1 |-*.
  cbn in H1 |-*.
  rewrite H1, Bool.andb_true_r.
  destruct it; [ easy | ].
  cbn in Hlc.
  destruct la as [| d]. {
    now injection Hlc; clear Hlc; intros; subst c lc.
  }
  remember (rel d b) as db eqn:Hdb; symmetry in Hdb.
  destruct db. {
    injection Hlc; clear Hlc; intros H2 H3; subst d.
    rename Hdb into Hcb.
    cbn in Hla.
    unfold sorted in Hla; cbn in Hla.
    now destruct (rel a c).
  }
  now injection Hlc; clear Hlc; intros H2 H3; subst c.
}
cbn.
remember (merge_loop rel it (a :: la) lb) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [| c]; [ easy | ].
rewrite Nat.add_comm in Hit.
rewrite List_cons_length in Hit.
rewrite Nat.add_comm in Hit.
rewrite Nat.add_succ_r in Hit.
apply Nat.succ_le_mono in Hit.
specialize (IHit (a :: la) lb Hit) as H1.
assert (H : sorted rel lb) by now apply sorted_cons in Hlb.
specialize (H1 Hla H); clear H.
rewrite Hlc in H1.
unfold sorted in H1 |-*; cbn in H1 |-*.
rewrite H1, Bool.andb_true_r.
destruct it; [ easy | ].
cbn in Hlc.
destruct lb as [| d]. {
  injection Hlc; clear Hlc; intros; subst c lc.
  remember (rel b a) as ba eqn:Hba; symmetry in Hba.
  destruct ba; [ easy | ].
  specialize (Htot a b) as H.
  now rewrite Hab, Hba in H.
}
remember (rel a d) as ad eqn:Had; symmetry in Had.
destruct ad. {
  injection Hlc; clear Hlc; intros Hlc H; subst c.
  specialize (Htot a b) as H2.
  now rewrite Hab in H2; cbn in H2.
}
injection Hlc; clear Hlc; intros Hlc H; subst d.
cbn in Hlb.
unfold sorted in Hlb; cbn in Hlb.
now destruct (rel b c).
Qed.

Theorem sorted_merge : ∀ A (rel : A → _),
  total_relation rel →
  ∀ la lb,
  sorted rel la
  → sorted rel lb
  → sorted rel (merge rel la lb).
Proof.
intros * Htot * Hla Hlb.
unfold merge.
now apply sorted_merge_loop.
Qed.

Theorem sorted_msort_loop : ∀ A (rel : A → _),
  total_relation rel →
  ∀ l it,
  length l ≤ it
  → sorted rel (msort_loop rel it l).
Proof.
intros * Htot * Hit.
revert l Hit.
induction it; intros; cbn. {
  now apply Nat.le_0_r, List.length_zero_iff_nil in Hit; subst l.
}
remember (split_list l) as la eqn:Hla; symmetry in Hla.
destruct la as (la, lb).
destruct l as [| a]. {
  injection Hla; clear Hla; intros; subst la lb; cbn.
  now rewrite msort_loop_nil.
}
destruct l as [| b]. {
  injection Hla; clear Hla; intros; subst la lb; cbn.
  now rewrite msort_loop_unit, msort_loop_nil.
}
cbn in Hla.
remember (split_list l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hla; clear Hla; intros; subst la lb.
cbn in Hit.
apply Nat.succ_le_mono in Hit.
apply split_list_length in Hlc.
apply sorted_merge; [ easy | | ]. {
  apply IHit; cbn; flia Hit Hlc.
} {
  apply IHit; cbn; flia Hit Hlc.
}
Qed.

Theorem sorted_merge_loop_cons_cons : ∀ {A} {rel : A → _},
  antisymmetric rel →
  transitive rel →
  ∀ {it l la lb a b},
  length l ≤ it
  → sorted rel (a :: b :: l)
  → split_list l = (la, lb)
  → merge_loop rel (S (S it)) (a :: la) (b :: lb) =
    a :: b :: merge_loop rel it la lb.
Proof.
intros * Hant Htra * Hit Hs Hla.
remember (S it) as sit; cbn; subst sit.
unfold sorted in Hs.
remember (b :: l) as l'; cbn in Hs; subst l'.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ f_equal | easy ].
rewrite Bool.andb_true_l in Hs.
clear a Hab; rename b into a.
destruct l as [| b]. {
  injection Hla; clear Hla; intros; subst la lb.
  now destruct it.
}
move b after a.
destruct l as [| c]. {
  injection Hla; clear Hla; intros; subst la lb.
  cbn in Hs |-*.
  remember (rel a b) as ab eqn:Hab; symmetry in Hab.
  remember (rel b a) as ba eqn:Hba; symmetry in Hba.
  destruct ab; [ | easy ].
  destruct ba; [ | easy ].
  clear Hs.
  specialize (Hant a b Hab Hba) as H; subst b.
  now destruct it.
}
cbn in Hla.
remember (split_list l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hla; clear Hla; intros; subst la lb.
move c after b; cbn.
remember (c :: l) as l'; cbn in Hs; subst l'.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
remember (rel b a) as ba eqn:Hba; symmetry in Hba.
destruct ab; [ | easy ].
destruct ba; [ | easy ].
specialize (Hant a b Hab Hba) as H; subst b.
clear Hba; rename Hab into Haa.
f_equal.
now apply sorted_merge_loop_cons_cons_r with (l := l).
Qed.

Theorem merge_loop_when_sorted : ∀ {A} {rel : A → _},
  antisymmetric rel →
  transitive rel →
  ∀ it l la lb,
  length l ≤ it
  → sorted rel l
  → split_list l = (la, lb)
  → merge_loop rel it la lb = l.
Proof.
intros * Hant Htra * Hit Hs Hll.
remember (length l) as len eqn:Hlen.
symmetry in Hlen.
rewrite <- Hlen in Hit.
revert it l la lb Hlen Hit Hs Hll.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct l as [| a]. {
  injection Hll; intros; subst la lb; cbn.
  now destruct it.
}
destruct l as [| b]. {
  injection Hll; intros; subst la lb; cbn.
  now destruct it.
}
cbn in Hll.
remember (split_list l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hll; clear Hll; intros; subst la lb.
rename lc into la; rename ld into lb; rename Hlc into Hll.
destruct it; [ cbn in Hit; flia Hit | ].
cbn.
unfold sorted in Hs.
remember (b :: l) as l'; cbn in Hs; subst l'.
apply Bool.andb_true_iff in Hs.
destruct Hs as (Hab, Hs).
rewrite Hab; f_equal.
cbn in Hit.
apply Nat.succ_le_mono in Hit.
cbn in Hlen.
clear a Hab.
rename b into a.
destruct l as [| b]. {
  injection Hll; clear Hll; intros; subst la lb.
  destruct it; [ flia Hit | easy ].
}
destruct l as [| c]. {
  injection Hll; clear Hll; intros; subst la lb.
  destruct it; [ flia Hit | cbn ].
  cbn in Hs.
  rewrite Bool.andb_true_r in Hs.
  rename Hs into Hab.
  remember (rel b a) as ba eqn:Hba; symmetry in Hba.
  destruct ba. {
    specialize (Hant a b Hab Hba) as H; subst b.
    rename Hba into Haa; clear Hab.
    f_equal.
    destruct it; [ cbn in Hit; flia Hit | easy ].
  }
  f_equal.
  destruct it; [ cbn in Hit; flia Hit | easy ].
}
cbn in Hll.
remember (split_list l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hll; clear Hll; intros; subst la lb.
rename lc into la; rename ld into lb; rename Hlc into Hll.
destruct it; [ flia Hit | ].
apply Nat.succ_le_mono in Hit; cbn in Hit.
cbn.
remember (c :: l) as l'; cbn in Hs; subst l'.
rewrite Bool.andb_true_iff in Hs; destruct Hs as (Hab, Hs).
rewrite Bool.andb_true_iff in Hs; destruct Hs as (Hbc, Hs).
remember (rel b a) as ba eqn:Hba; symmetry in Hba.
destruct ba. {
  specialize (Hant a b Hab Hba) as H; subst b.
  rename Hab into Haa; clear Hba.
  f_equal.
  rename c into b; rename Hbc into Hab.
  rewrite sorted_merge_loop_cons_cons_r with (l := l); try easy. 2: {
    remember (b :: l) as l'; cbn; subst l'.
    unfold sorted; cbn in Hs |-*.
    now rewrite Hab, Hs.
  }
  replace it with (S (S (it - 2))) by flia Hit.
  rewrite sorted_merge_loop_cons_cons with (l := l); try easy; cycle 1. {
    flia Hit.
  } {
    remember (b :: l) as l'; cbn; subst l'.
    unfold sorted; cbn in Hs |-*.
    now rewrite Hab, Hs.
  }
  f_equal; f_equal.
  remember (it - 2) as it' eqn:H.
  assert (Hit' : length l ≤ it') by flia Hit H.
  move Hit' before Hit.
  clear it Hit H; rename it' into it; rename Hit' into Hit.
  cbn in Hlen.
  clear a Hab Haa.
  apply sorted_cons in Hs.
  clear b.
  apply IHlen with (m := len - 4); try easy; flia Hlen.
}
f_equal.
cbn in Hlen.
apply IHlen with (m := len - 2); try easy; try flia Hlen. {
  cbn; flia Hlen.
} {
  remember (c :: l) as l'; cbn; subst l'.
  unfold sorted; cbn in Hs |-*.
  now rewrite Hbc, Hs.
}
cbn.
now rewrite Hll.
Qed.

Theorem merge_when_sorted : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  ∀ l la lb,
  sorted rel l
  → split_list l = (la, lb)
  → merge rel la lb = l.
Proof.
intros * Hant Htra * Hs Hll.
unfold merge.
apply (merge_loop_when_sorted Hant Htra); [ | easy | easy ].
apply split_list_length in Hll.
now rewrite Hll.
Qed.

Theorem sorted_cons_cons_split_list' : ∀ A (rel : A → _),
  transitive rel →
  ∀ a b la lb l,
  sorted rel (a :: b :: l)
  → split_list l = (la, lb)
  → sorted rel (a :: la) ∧ sorted rel (b :: lb).
Proof.
intros * Htra * Hs Hla.
remember (length l) as len eqn:Hlen; symmetry in Hlen.
revert a b l la lb Hs Hla Hlen.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct len. {
  apply List.length_zero_iff_nil in Hlen; subst l.
  now injection Hla; clear Hla; intros; subst la lb.
}
destruct l as [| c]; [ easy | ].
cbn in Hlen; apply Nat.succ_inj in Hlen.
destruct len. {
  apply List.length_zero_iff_nil in Hlen; subst l.
  injection Hla; clear Hla; intros; subst la lb.
  unfold sorted in Hs |-*.
  cbn in Hs |-*.
  rewrite (Htra a b c); [ easy | | ]. {
    now destruct (rel a b).
  } {
    destruct (rel b c); [ easy | ].
    now rewrite Bool.andb_false_r in Hs.
  }
}
destruct l as [| d]; [ easy | ].
cbn in Hlen; apply Nat.succ_inj in Hlen.
cbn in Hla.
remember (split_list l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hla; clear Hla; intros; subst la lb.
rename lc into la; rename ld into lb; rename Hlc into Hla.
specialize (IHlen len) as H1.
assert (H : len < S (S len)) by now transitivity (S len).
specialize (H1 H); clear H.
specialize (H1 a b l la lb) as H2.
remember (c :: d :: l) as l'; cbn in Hs; subst l'.
remember (c :: la) as l'.
remember (d :: lb) as l''; cbn; subst l' l''.
unfold sorted in Hs |-*; cbn in Hs |-*.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
destruct ab; [ rewrite Bool.andb_true_l in Hs | easy ].
destruct bc; [ rewrite Bool.andb_true_l in Hs | easy ].
rewrite (Htra a b c Hab Hbc), Bool.andb_true_l.
assert (H : sorted rel (a :: b :: l)). {
  remember (b :: l) as l'; cbn; subst l'.
  unfold sorted; cbn.
  rewrite Hab, Bool.andb_true_l; cbn.
  destruct l as [| e]; [ easy | ].
  remember (e :: l) as l'; cbn in Hs; subst l'.
  remember (rel c d) as cd eqn:Hcd; symmetry in Hcd.
  remember (rel d e) as de eqn:Hde; symmetry in Hde.
  destruct cd; [ rewrite Bool.andb_true_l in Hs | easy ].
  destruct de; [ rewrite Bool.andb_true_l in Hs | easy ].
  rewrite Hs, Bool.andb_true_r.
  specialize (Htra b c d Hbc Hcd) as Hbd.
  apply (Htra b d e Hbd Hde).
}
specialize (H2 H Hla Hlen); clear H.
specialize (H1 c d l la lb Hs Hla Hlen) as H3.
split; [ easy | ].
destruct H3 as (H3, H4); rewrite H4, Bool.andb_true_r.
remember (d :: l) as l'; cbn in Hs; subst l'.
remember (rel c d) as cd eqn:Hcd; symmetry in Hcd.
destruct cd; [ | easy ].
apply (Htra b c d Hbc Hcd).
Qed.

Theorem sorted_merge_cons_cons : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  ∀ l la lb a b,
  sorted rel (a :: b :: l)
  → split_list l = (la, lb)
  → merge rel (a :: la) (b :: lb) = a :: b :: merge rel la lb.
Proof.
intros * Hant Htra * Hs Hla.
unfold merge.
do 2 rewrite List_cons_length.
rewrite Nat.add_succ_r, Nat.add_succ_l.
assert (H : length l ≤ length la + length lb). {
  apply split_list_length in Hla.
  now rewrite Hla.
}
now apply (sorted_merge_loop_cons_cons Hant Htra H).
Qed.

Theorem msort_loop_when_sorted : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ l it,
  length l ≤ it
  → sorted rel l
  → msort_loop rel it l = l.
Proof.
intros * Hant Htra Htot * Hit Hs.
revert l Hit Hs.
induction it; intros; [ easy | cbn ].
remember (split_list l) as la eqn:Hla; symmetry in Hla.
destruct la as (la, lb).
destruct l as [| a]. {
  injection Hla; intros; subst la lb.
  now rewrite msort_loop_nil.
}
destruct l as [| b]. {
  injection Hla; clear Hla; intros; subst la lb.
  now rewrite msort_loop_unit, msort_loop_nil.
}
cbn in Hla.
remember (split_list l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hla; clear Hla; intros; subst la lb.
rename lc into la; rename ld into lb; rename Hlc into Hla.
cbn in Hit.
apply Nat.succ_le_mono in Hit.
rewrite IHit; cycle 1. {
  apply split_list_length in Hla.
  cbn; flia Hit Hla.
} {
  now apply sorted_cons_cons_split_list' with (la := la) (lb := lb) in Hs.
}
rewrite IHit; cycle 1. {
  apply split_list_length in Hla.
  cbn; flia Hit Hla.
} {
  now apply sorted_cons_cons_split_list' with (la := la) (lb := lb) in Hs.
}
rewrite sorted_merge_cons_cons with (l := l); [ | easy | easy | easy | easy ].
f_equal; f_equal.
do 2 apply sorted_cons in Hs.
now apply merge_when_sorted.
Qed.
