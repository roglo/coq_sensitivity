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

(* *)

Theorem permutation_merge_loop_aux :
  ∀ {A} {eqb : A → _} rel (Heqb : equality eqb),
  ∀ {it} la lb lc,
  length la + length lc ≤ it
  → permutation eqb (la ++ lb ++ lc) (lb ++ merge_loop rel it la lc).
Proof.
intros * Heqb * Hit.
revert la lb lc Hit.
induction it as (it, IHit) using lt_wf_rec; intros.
destruct it. {
  apply Nat.le_0_r, Nat.eq_add_0 in Hit.
  destruct Hit as (H1, H2).
  apply List.length_zero_iff_nil in H1, H2; subst la lc.
  cbn; rewrite List.app_nil_r; cbn.
  now apply permutation_refl.
}
destruct la as [| a]; [ now apply permutation_refl | ].
cbn in Hit; apply Nat.succ_le_mono in Hit; cbn.
destruct lc as [| b]. {
  rewrite List.app_nil_r.
  rewrite List.app_comm_cons.
  apply (permutation_app_comm Heqb).
}
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  eapply (permutation_trans Heqb). 2: {
    apply (permutation_app_comm Heqb).
  }
  cbn.
  apply permutation_skip; [ now unfold reflexive; apply equality_refl | ].
  eapply (permutation_trans Heqb). {
    apply IHit; [ | apply Hit ]; easy.
  }
  apply (permutation_app_comm Heqb).
}
eapply (permutation_trans Heqb). 2: {
  apply (permutation_app_comm Heqb).
}
cbn.
rewrite List_cons_is_app.
do 2 rewrite List.app_assoc.
eapply (permutation_trans Heqb). {
  apply (permutation_app_comm Heqb).
}
cbn.
apply permutation_skip; [ now unfold reflexive; apply equality_refl | ].
eapply (permutation_trans Heqb). 2: {
  apply (permutation_app_comm Heqb).
}
rewrite List_app_cons.
eapply (permutation_trans Heqb). {
  apply (permutation_app_comm Heqb).
}
cbn.
do 2 rewrite List.app_comm_cons.
rewrite <- List.app_assoc.
cbn in Hit.
rewrite Nat.add_succ_r in Hit.
now apply IHit.
Qed.

Theorem permutation_merge_loop :
  ∀ A (eqb rel : A → _) (Heqb : equality eqb),
  ∀ it la lb,
  length la + length lb ≤ it
  → permutation eqb (la ++ lb) (merge_loop rel it la lb).
Proof.
intros * Heqb * Hit.
apply (permutation_merge_loop_aux rel Heqb la [] lb Hit).
Qed.

Theorem split_list_permutation : ∀ A (eqb : A → _) (Heqb : equality eqb),
  ∀ l la lb,
  split_list l = (la, lb)
  → permutation eqb l (la ++ lb).
Proof.
intros * Heqb * Hll.
remember (length l) as len eqn:Hlen; symmetry in Hlen.
revert l la lb Hlen Hll.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct l as [| a]. {
  injection Hll; clear Hll; intros; subst la lb.
  apply permutation_nil_nil.
}
destruct l as [| b]. {
  injection Hll; clear Hll; intros; subst la lb.
  rewrite List.app_nil_r.
  now apply permutation_refl.
}
destruct len; [ easy | ].
destruct len; [ easy | ].
cbn in Hlen, Hll.
do 2 apply Nat.succ_inj in Hlen.
remember (split_list l) as ll eqn:Hll'; symmetry in Hll'.
destruct ll as (lc, ld).
injection Hll; clear Hll; intros; subst la lb; cbn.
apply permutation_skip; [ now unfold reflexive; apply equality_refl | ].
eapply (permutation_trans Heqb). 2: {
  apply (permutation_app_comm Heqb).
}
cbn.
apply permutation_skip; [ now unfold reflexive; apply equality_refl | ].
eapply (permutation_trans Heqb). 2: {
  apply (permutation_app_comm Heqb).
}
apply (IHlen len); [ | easy | easy ].
now transitivity (S len).
Qed.

Theorem permutation_split_list_merge_loop :
  ∀ A (eqb rel : A → _) (Heqb : equality eqb),
  ∀ it l la lb,
  length la + length lb ≤ it
  → split_list l = (la, lb)
  → permutation eqb l (merge_loop rel it la lb).
Proof.
intros * Heqb * Hit Hll.
eapply (permutation_trans Heqb); [ | now apply permutation_merge_loop ].
now apply split_list_permutation.
Qed.

Theorem permutation_merge : ∀ {A} {eqb : A → _} rel (Heqb : equality eqb),
  ∀ l la lb,
  split_list l = (la, lb)
  → permutation eqb l (merge rel la lb).
Proof.
intros * Heqb * Hll.
now apply permutation_split_list_merge_loop.
Qed.

Fixpoint split_list_inv {A} (la lb : list A) :=
  match la, lb with
  | _, [] => la
  | [], _ => lb
  | a :: la', b :: lb' => a :: b :: split_list_inv la' lb'
  end.

Theorem split_list_split_list_inv : ∀ A (la lb : list A),
  (length la = length lb ∨ length la = S (length lb))
  → split_list (split_list_inv la lb) = (la, lb).
Proof.
intros * Hlen.
revert lb Hlen.
induction la as [| a]; intros. {
  destruct Hlen as [Hlen| Hlen]; [ | easy ].
  now destruct lb.
}
cbn.
destruct lb as [| b]. {
  destruct Hlen as [Hlen| Hlen]; [ easy | ].
  cbn in Hlen; apply Nat.succ_inj in Hlen.
  now apply List.length_zero_iff_nil in Hlen; subst la; cbn.
}
cbn.
rewrite (IHla lb); [ easy | ].
cbn in Hlen.
now destruct Hlen as [H| H]; [ left | right ]; now apply Nat.succ_inj in H.
Qed.

Theorem permutation_app_split_list_inv :
  ∀ A (eqb : A → _) (Heqb : equality eqb) la lb,
  permutation eqb (la ++ lb) (split_list_inv la lb).
Proof.
intros * Heqb *.
revert lb.
induction la as [| a]; intros; cbn. {
  destruct lb as [| b]; [ apply permutation_nil_nil | ].
  apply (permutation_refl Heqb).
}
destruct lb as [| b]. {
  rewrite List.app_nil_r.
  apply (permutation_refl Heqb).
}
apply permutation_skip; [ now unfold reflexive; apply equality_refl | ].
apply (permutation_trans Heqb) with (lb := (b :: (la ++ lb))). {
  rewrite List_app_cons, List.app_assoc, List.app_comm_cons.
  apply (permutation_app_tail Heqb).
  apply (permutation_sym Heqb).
  apply (permutation_cons_append Heqb).
}
apply permutation_skip; [ now unfold reflexive; apply equality_refl | ].
apply IHla.
Qed.

Theorem split_list_inv_nil_r : ∀ A (la : list A), split_list_inv la [] = la.
Proof. now intros; destruct la. Qed.

Theorem permutation_split_list_inv_split_list_inv :
  ∀ {A} {eqb : A → _} (Heqb : equality eqb),
  ∀ la lb lc ld,
  permutation eqb la lc
  → permutation eqb lb ld
  → permutation eqb (split_list_inv la lb) (split_list_inv lc ld).
Proof.
intros * Heqb * Hac Hbd.
revert lb lc ld Hac Hbd.
induction la as [| a]; intros; cbn. {
  apply permutation_nil_l in Hac; subst lc; cbn.
  destruct lb as [| b]; [ | now destruct ld ].
  apply permutation_nil_l in Hbd; subst ld.
  apply permutation_nil_nil.
}
destruct lb as [| b]. {
  apply permutation_nil_l in Hbd; subst ld.
  now rewrite split_list_inv_nil_r.
}
move b before a.
move lb before la; move lc before lb; move ld before lc.
specialize (permutation_in_iff Heqb) as H1.
specialize (proj1 (H1 _ _ Hac _) (or_introl eq_refl)) as Hc.
specialize (proj1 (H1 _ _ Hbd _) (or_introl eq_refl)) as Hd.
clear H1.
apply List.in_split in Hc, Hd.
destruct Hc as (lc1 & lc2 & Hc).
destruct Hd as (ld1 & ld2 & Hd).
subst lc ld.
eapply (permutation_trans Heqb). 2: {
  now apply permutation_app_split_list_inv.
}
specialize (permutation_app_inv Heqb [] la lc1 lc2 a Hac) as H1.
specialize (permutation_app_inv Heqb [] lb ld1 ld2 b Hbd) as H2.
cbn in H1, H2; clear Hac Hbd.
apply (permutation_sym Heqb).
rewrite (List_cons_is_app a).
rewrite (List_cons_is_app b).
rewrite <- List.app_assoc.
eapply (permutation_trans Heqb); [ now apply permutation_app_comm | cbn ].
apply permutation_skip; [ now unfold reflexive; apply equality_refl | ].
rewrite (List_cons_is_app b).
do 3 rewrite <- List.app_assoc.
rewrite List.app_assoc.
eapply (permutation_trans Heqb); [ now apply permutation_app_comm | cbn ].
apply permutation_skip; [ now unfold reflexive; apply equality_refl | ].
rewrite <- List.app_assoc.
eapply (permutation_trans Heqb); [ now apply permutation_app_comm | ].
do 2 rewrite <- List.app_assoc.
rewrite List.app_assoc.
eapply (permutation_trans Heqb). {
  now apply permutation_app_split_list_inv.
}
apply (permutation_sym Heqb).
now apply IHla.
Qed.

Theorem permuted_msort_loop : ∀ A (eqb rel : A → _) (Heqb : equality eqb),
  ∀ it l, permutation eqb l (msort_loop rel it l).
Proof.
intros * Heqb *.
revert l.
induction it; intros; [ now apply permutation_refl | cbn ].
remember (split_list l) as la eqn:Hla; symmetry in Hla.
destruct la as (la, lb).
remember (msort_loop rel it la) as lc eqn:Hlc.
remember (msort_loop rel it lb) as ld eqn:Hld.
remember (split_list_inv lc ld) as l' eqn:Hl'.
apply (permutation_trans Heqb) with (lb := l'). 2: {
  apply (permutation_merge rel Heqb).
  subst l'.
  rewrite split_list_split_list_inv; [ easy | ].
  apply split_list_lengths in Hla.
  apply (f_equal (λ l, length l)) in Hlc, Hld.
  rewrite msort_loop_length in Hlc, Hld.
  now rewrite Hlc, Hld.
}
subst l' lc ld.
apply (permutation_trans Heqb) with (lb := la ++ lb). {
  now apply split_list_permutation.
}
apply (permutation_trans Heqb) with (lb := split_list_inv la lb). {
  now apply permutation_app_split_list_inv.
}
apply (permutation_split_list_inv_split_list_inv Heqb); apply IHit.
Qed.

(* *)

Theorem merge_nil_l : ∀ A (rel : A → _) la, merge rel [] la = la.
Proof. now intros; destruct la. Qed.

Theorem merge_nil_r : ∀ A (rel : A → _) la, merge rel la [] = la.
Proof. now intros; destruct la. Qed.

Theorem merge_cons_cons : ∀ A (rel : A → _) a b la lb,
  merge rel (a :: la) (b :: lb) =
    if rel a b then a :: merge rel la (b :: lb)
    else b :: merge rel (a :: la) lb.
Proof.
intros; cbn.
replace (S (length lb)) with (length (b :: lb)) at 1 by easy.
rewrite <- Nat.add_succ_comm.
replace (S (length la)) with (length (a :: la)) at 1 by easy.
now destruct (rel a b).
Qed.

Theorem merge_in_iff : ∀ A (rel : A → _) a la lb,
  a ∈ merge rel la lb ↔ a ∈ la ∨ a ∈ lb.
Proof.
intros.
split; intros Ha. {
  revert lb Ha.
  induction la as [| a']; intros. {
    now rewrite merge_nil_l in Ha; right.
  }
  destruct lb as [| b]; [ now left | ].
  rewrite merge_cons_cons in Ha.
  destruct (rel a' b). {
    destruct Ha as [Ha| Ha]; [ now left; left | ].
    apply IHla in Ha.
    destruct Ha as [Ha| Ha]; [ now left; right | now right ].
  } {
    destruct Ha as [Ha| Ha]; [ now right; left | ].
    revert lb Ha.
    induction lb as [| b']; intros; [ now left | ].
    rewrite merge_cons_cons in Ha.
    destruct (rel a' b'). {
      destruct Ha as [Ha| Ha]; [ now left; left | ].
      apply IHla in Ha.
      destruct Ha as [Ha| Ha]; [ now left; right | now right; right ].
    } {
      destruct Ha as [Ha| Ha]; [ now right; right; left | ].
      specialize (IHlb Ha).
      destruct IHlb as [Hb| Hb]; [ now left | right ].
      destruct Hb as [Hb| Hb]; [ now left | now right; right ].
    }
  }
}
destruct Ha as [Ha| Ha]. {
  revert lb.
  induction la as [| a']; intros; [ easy | ].
  destruct Ha as [Ha| Ha]. {
    subst a'; clear IHla.
    induction lb as [| b]; [ now left | ].
    rewrite merge_cons_cons.
    destruct (rel a b); [ now left | right; apply IHlb ].
  } {
    specialize (IHla Ha).
    induction lb as [| b]; [ now right | ].
    rewrite merge_cons_cons.
    destruct (rel a' b); [ | right; apply IHlb ].
    right; apply IHla.
  }
} {
  revert la.
  induction lb as [| b]; intros; [ easy | ].
  destruct Ha as [Ha| Ha]. {
    subst b.
    induction la as [| a']; [ now left | ].
    rewrite merge_cons_cons.
    destruct (rel a' a); [ right; apply IHla | now left ].
  } {
    specialize (IHlb Ha).
    induction la as [| a']; [ now right | ].
    rewrite merge_cons_cons.
    destruct (rel a' b); [ right; apply IHla | ].
    right; apply IHlb.
  }
}
Qed.

Theorem merge_cons_l : ∀ A (rel : A → _) a la lb,
  merge rel (a :: la) lb =
    match lb with
    | [] => a :: la
    | b :: lb' =>
        if rel a b then a :: merge rel la lb else b :: merge rel (a :: la) lb'
    end.
Proof.
intros.
unfold merge at 1.
cbn - [ merge ].
destruct lb as [| b]; [ easy | ].
destruct (rel a b); [ easy | ].
cbn - [ merge_loop ].
rewrite <- Nat.add_succ_comm.
now replace (S (length la)) with (length (a :: la)).
Qed.

Theorem permutation_app_merge : ∀ {A} {eqb : A → _} rel,
  equality eqb →
  ∀ la lb,
  permutation eqb (la ++ lb) (merge rel la lb).
Proof.
intros * Heqb *.
revert la.
induction lb as [| b]; intros. {
  rewrite List.app_nil_r, merge_nil_r.
  apply (permutation_refl Heqb).
}
induction la as [| a]. {
  apply (permutation_refl Heqb).
}
cbn - [ merge ].
rewrite merge_cons_cons.
destruct (rel a b). {
  apply permutation_skip; [ now intros x; apply Heqb | easy ].
}
rewrite (List_cons_is_app a (la ++ b :: lb)).
rewrite List.app_assoc.
apply (permutation_sym Heqb).
apply (permutation_cons_app Heqb).
apply (permutation_sym Heqb).
apply IHlb.
Qed.

Theorem permutation_merge_comm : ∀ A (eqb rel : A → _),
  equality eqb →
  ∀ la lb,
  permutation eqb (merge rel la lb) (merge rel lb la).
Proof.
intros * Heqb *.
eapply (permutation_trans Heqb). 2: {
  apply (permutation_app_merge _ Heqb).
}
eapply (permutation_trans Heqb). 2: {
  apply (permutation_app_comm Heqb).
}
apply (permutation_sym Heqb).
apply (permutation_app_merge _ Heqb).
Qed.

Theorem split_list_nil_l : ∀ A (la lb : list A),
  split_list la = ([], lb) → la = [] ∧ lb = [].
Proof.
intros * Hab.
destruct la as [| a]; cbn in Hab |-*. {
  now injection Hab; clear Hab; intros; subst lb.
}
exfalso.
destruct la as [| b]; [ easy | ].
now destruct (split_list la).
Qed.

Theorem split_list_nil_r : ∀ A (la lb : list A),
  split_list la = (lb, []) → la = lb ∧ length la ≤ 1.
Proof.
intros * Hab.
destruct la as [| a]; cbn in Hab |-*. {
  now injection Hab; clear Hab; intros; subst lb.
}
destruct la as [| b]. {
  now injection Hab; clear Hab; intros; subst lb.
}
now destruct (split_list la).
Qed.

Theorem split_list_cons_cons : ∀ A (l la lb : list A) a b,
  split_list l = (a :: la, b :: lb)
  → ∃ l', split_list l' = (la, lb) ∧ l = a :: b :: l'.
Proof.
intros * Hs.
destruct l as [| c]; [ easy | ].
destruct l as [| d]; [ easy | ].
cbn in Hs.
remember (split_list l) as l' eqn:Hl'; symmetry in Hl'.
destruct l' as (lc, ld).
injection Hs; clear Hs; intros; subst lc ld c d.
now exists l.
Qed.

Theorem sorted_split_list : ∀ A (rel : A → _),
  transitive rel →
  ∀ la lb l,
  sorted rel l
  → split_list l = (la, lb)
  → sorted rel la ∧ sorted rel lb.
Proof.
intros * Htra * Hs Hla.
destruct l as [| a]; [ now injection Hla; intros; subst la lb | ].
destruct l as [| b]; [ now injection Hla; intros; subst la lb | ].
cbn in Hla.
remember (split_list l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hla; clear Hla; intros; subst la lb.
now apply sorted_cons_cons_split_list' with (l := l).
Qed.

Theorem msort_loop_enough_iter : ∀ A (rel : A → _) la ita itb,
  length la ≤ ita
  → length la ≤ itb
  → msort_loop rel ita la = msort_loop rel itb la.
Proof.
intros * Ha Hb.
revert la itb Ha Hb.
induction ita; intros; cbn. {
  apply Nat.le_0_r, List.length_zero_iff_nil in Ha; subst la.
  symmetry; apply msort_loop_nil.
}
destruct itb; cbn. {
  apply Nat.le_0_r, List.length_zero_iff_nil in Hb; subst la; cbn.
  now rewrite msort_loop_nil.
}
remember (split_list la) as ll eqn:Hll; symmetry in Hll.
destruct ll as (lc, ld).
destruct la as [| a]. {
  injection Hll; clear Hll; intros; subst lc ld.
  now do 2 rewrite msort_loop_nil.
}
cbn in Ha, Hb.
apply Nat.succ_le_mono in Ha, Hb.
destruct la as [| b]. {
  injection Hll; clear Hll; intros; subst lc ld.
  now do 2 rewrite msort_loop_unit, msort_loop_nil.
}
cbn in Ha, Hb.
cbn in Hll.
remember (split_list la) as ll eqn:H; symmetry in H.
destruct ll as (le, lf).
injection Hll; clear Hll; intros; subst lc ld.
rename le into lc; rename lf into ld; rename H into Hll.
apply split_list_length in Hll.
rewrite IHita with (itb := itb); cbn; [ | flia Ha Hll | flia Hb Hll ].
rewrite IHita with (itb := itb); cbn; [ | flia Ha Hll | flia Hb Hll ].
easy.
Qed.

(* main *)

Theorem msort_when_sorted : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ l,
  sorted rel l
  → msort rel l = l.
Proof.
intros * Hant Htra Htot * Hs.
unfold msort.
now apply msort_loop_when_sorted.
Qed.

(* *)

Theorem sorted_msort : ∀ [A] {rel : A → _},
  total_relation rel →
  ∀ l, sorted rel (msort rel l).
Proof.
intros * Htot *.
now apply sorted_msort_loop.
Qed.

(* *)

Theorem sorted_msort_iff : ∀ A (rel : A → A → bool),
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ l, sorted rel l ↔ msort rel l = l.
Proof.
intros * Hant Htra Htot *.
split; [ now apply msort_when_sorted | ].
intros Hs.
specialize sorted_msort as H1.
specialize (H1 _ rel Htot l).
now rewrite Hs in H1.
Qed.

(* *)

Theorem permuted_msort : ∀ {A} {eqb : A → _} rel (Heqb : equality eqb),
  ∀ l, permutation eqb l (msort rel l).
Proof.
intros.
now apply permuted_msort_loop.
Qed.

(* *)

Theorem msort_when_permuted : ∀ A (eqb rel : A → _),
  equality eqb →
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ la lb,
  permutation eqb la lb
  → msort rel la = msort rel lb.
Proof.
intros * Heqb Hant Htra Htot * Hpab.
specialize (sorted_msort Htot la) as Hsa.
specialize (sorted_msort Htot lb) as Hsb.
specialize (permuted_msort rel Heqb la) as Hpa.
specialize (permuted_msort rel Heqb lb) as Hpb.
assert (Hsab : permutation eqb (msort rel la) (msort rel lb)). {
  eapply (permutation_trans Heqb); [ | apply Hpb ].
  eapply (permutation_trans Heqb); [ | apply Hpab ].
  now apply (permutation_sym Heqb).
}
now apply (sorted_sorted_permuted Heqb Hant Htra).
Qed.

(* *)
