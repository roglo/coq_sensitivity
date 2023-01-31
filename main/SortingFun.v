(* Sorting algorithms : bubble, selection, insertion, merge *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.
Import Init.Nat.

Require Import Misc PermutationFun.

(* relation properties *)

Definition irreflexive A (rel : A → A → bool) :=
  ∀ a, rel a a = false.

Definition antisymmetric A (rel : A → A → bool) :=
  ∀ a b, rel a b = true → rel b a = true → a = b.

(* https://ncatlab.org/nlab/show/connected+relation *)
Definition connected_relation A (rel : A → A → bool) :=
  ∀ a b, rel a b = false → rel b a = false → a = b.

Definition transitive A (rel : A → A → bool) :=
  ∀ a b c, rel a b = true → rel b c = true → rel a c = true.

Definition total_relation {A} (rel : A → _) := ∀ a b,
  (rel a b || rel b a)%bool = true.

Theorem total_relation_is_reflexive : ∀ A (rel : A → _),
  total_relation rel → reflexive rel.
Proof.
intros * Htot a.
specialize (Htot a a) as H1.
apply Bool.orb_true_iff in H1.
now destruct H1.
Qed.

(* compute if a list is sorted *)

Fixpoint is_sorted {A} (rel : A → A → bool) l :=
  match l with
  | [] => true
  | [a] => true
  | a :: (b :: _) as la => (rel a b && is_sorted rel la)%bool
  end.

Fixpoint all_sorted A (rel : A → A → bool) a l :=
  match l with
  | [] => true
  | b :: l' => (rel a b && all_sorted rel a l')%bool
  end.

Fixpoint is_strongly_sorted A (rel : A → A → bool) l :=
  match l with
  | [] => true
  | a :: l' => (all_sorted rel a l' && is_strongly_sorted rel l')%bool
  end.

Definition sorted A (rel : A → _) l :=
  is_sorted rel l = true.
Definition strongly_sorted A (rel : A → _) l :=
  is_strongly_sorted rel l = true.

Theorem fold_sorted : ∀ A f (l : list A), (is_sorted f l = true) = sorted f l.
Proof. easy. Qed.

Theorem sorted_cons : ∀ A (rel : A → _) a la,
  sorted rel (a :: la) → sorted rel la.
Proof.
intros * Hs.
cbn in Hs.
destruct la as [| a']; [ easy | ].
now apply Bool.andb_true_iff in Hs.
Qed.

Theorem sorted_strongly_sorted : ∀ A (rel : A → A → bool),
  transitive rel →
  ∀ l, sorted rel l → strongly_sorted rel l.
Proof.
intros * Htra * Hs.
unfold sorted in Hs.
unfold strongly_sorted.
induction l as [| a]; [ easy | cbn ].
rewrite IHl. 2: {
  destruct l as [| a']; [ easy | ].
  now apply Bool.andb_true_iff in Hs.
}
rewrite Bool.andb_true_r.
clear IHl.
induction l as [| b]; [ easy | cbn ].
remember (b :: l) as lb; cbn in Hs; subst lb.
apply Bool.andb_true_iff in Hs.
destruct Hs as (Hab, Hs).
rewrite Hab; cbn.
apply IHl; cbn in Hs |-*.
destruct l as [| c]; [ easy | ].
apply Bool.andb_true_iff in Hs.
destruct Hs as (Hbc, Hs).
now rewrite (Htra a b c Hab Hbc).
Qed.

Theorem strongly_sorted_sorted : ∀ A (rel : A → A → bool),
  ∀ l, strongly_sorted rel l → sorted rel l.
Proof.
intros * Hs.
unfold strongly_sorted in Hs; unfold sorted.
induction l as [| a]; [ easy | ].
cbn in Hs.
apply Bool.andb_true_iff in Hs.
destruct Hs as (Ha, Hs).
specialize (IHl Hs); cbn.
destruct l as [| b]; [ easy | ].
cbn in Ha.
apply Bool.andb_true_iff in Ha.
destruct Ha as (Hab, Ha).
now rewrite Hab, IHl.
Qed.

Theorem all_sorted_forall : ∀ A (rel : A → _) a l,
  all_sorted rel a l = true
  → ∀ b, b ∈ l → rel a b = true.
Proof.
intros * Hsal * Hb.
induction l as [| c]; [ easy | ].
destruct Hb as [Hb| Hb]. {
  subst c.
  cbn in Hsal.
  now apply Bool.andb_true_iff in Hsal.
}
apply IHl; [ | easy ].
cbn in Hsal.
now apply Bool.andb_true_iff in Hsal.
Qed.

Theorem sorted_cons_iff : ∀ (A : Type) (rel : A → A → bool),
  transitive rel
  → ∀ a la,
      sorted rel (a :: la) ↔
      sorted rel la ∧ (∀ b, b ∈ la → rel a b = true).
Proof.
intros * Htra *.
split; intros Hla. {
  split; [ now apply sorted_cons in Hla | ].
  intros b Hb.
  apply all_sorted_forall with (l := la); [ | easy ].
  apply (sorted_strongly_sorted Htra) in Hla.
  unfold strongly_sorted in Hla; cbn in Hla.
  now apply Bool.andb_true_iff in Hla.
} {
  destruct Hla as (Hs & Hla).
  unfold sorted; cbn.
  destruct la as [| b]; [ easy | ].
  apply Bool.andb_true_iff.
  split; [ | easy ].
  now apply Hla; left.
}
Qed.

Theorem sorted_rel : ∀ A (d : A) rel l,
  sorted rel l
  → ∀ i, S i < length l
  → rel (nth i l d) (nth (S i) l d) = true.
Proof.
intros * Hs i Hi.
revert i Hi.
induction l as [| a]; intros; [ easy | ].
cbn in Hi.
apply Nat.succ_lt_mono in Hi.
destruct l as [| b]; [ easy | ].
remember (b :: l) as l'; cbn in Hs |-*; subst l'.
apply Bool.andb_true_iff in Hs.
destruct i; [ easy | ].
now apply IHl.
Qed.

Theorem strongly_sorted_if : ∀ A rel,
  transitive rel
  → ∀ l,
  strongly_sorted rel l
  → ∀ (d : A) i j,
    i < length l
    → j < length l
    → i < j
    → rel (nth i l d) (nth j l d) = true.
Proof.
intros * Htr * Hso * Hi Hj Hij.
remember (j - i) as n eqn:Hn.
replace j with (i + n) in * by flia Hn Hij.
assert (Hnz : n ≠ 0) by flia Hij.
clear Hi Hij Hn.
revert i Hj.
induction n; intros; [ easy | clear Hnz; cbn ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  rewrite Nat.add_1_r in Hj |-*.
  apply sorted_rel; [ | easy ].
  now apply strongly_sorted_sorted.
}
apply Htr with (b := nth (S i) l d). 2: {
  rewrite <- Nat.add_succ_comm in Hj.
  rewrite <- Nat.add_succ_comm.
  now apply IHn.
}
apply sorted_rel; [ | flia Hj ].
now apply strongly_sorted_sorted.
Qed.

Theorem sorted_cons_cons_true_iff : ∀ A (rel : A → A -> bool) a b l,
  sorted rel (a :: b :: l)
  ↔ rel a b = true ∧ sorted rel (b :: l).
Proof.
intros.
apply Bool.andb_true_iff.
Qed.

Theorem sorted_extends : ∀ A (rel : A → _),
  transitive rel →
  ∀ a l,
  sorted rel (a :: l)
  → ∀ b, b ∈ l → rel a b = true.
Proof.
intros * Htra * Hsort b Hb.
induction l as [| c]; [ easy | ].
apply sorted_cons_cons_true_iff in Hsort.
destruct Hsort as (Hac, Hsort).
destruct Hb as [Hb| Hb]; [ now subst c | ].
apply IHl; [ | easy ].
destruct l as [| d]; [ easy | ].
apply sorted_cons_cons_true_iff in Hsort.
apply sorted_cons_cons_true_iff.
destruct Hsort as (Hcd, Hsort).
split; [ now apply Htra with (b := c) | easy ].
Qed.

Theorem sorted_NoDup : ∀ A (rel : A → A → bool),
  irreflexive rel →
  transitive rel →
  ∀ l, sorted rel l → NoDup l.
Proof.
intros * Hirr Htra * Hsort.
induction l as [| a]; [ constructor | ].
constructor. 2: {
  apply IHl.
  now apply sorted_cons in Hsort.
}
intros Ha.
specialize (sorted_extends Htra Hsort _ Ha) as H1.
now rewrite Hirr in H1.
Qed.

Theorem sorted_app_iff : ∀ A (rel : A → _),
  transitive rel →
  ∀ la lb,
  sorted rel (la ++ lb) ↔
  sorted rel la ∧ sorted rel lb ∧ (∀ a b, a ∈ la → b ∈ lb → rel a b = true).
Proof.
intros * Htra *.
split. {
  intros Hab.
  split. {
    revert lb Hab.
    induction la as [| a1]; intros; [ easy | ].
    destruct la as [| a2]; [ easy | ].
    cbn in Hab.
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
    cbn in Hab.
    apply sorted_cons_cons_true_iff in Hab.
    destruct Hab as (Haa & Hab).
    now apply IHla.
  } {
    intros * Ha Hb.
    revert a lb Ha Hab Hb.
    induction la as [| a1]; intros; [ easy | ].
    destruct Ha as [Ha| Ha]. 2: {
      apply (IHla a lb); [ easy | | easy ].
      cbn in Hab.
      now apply sorted_cons in Hab.
    }
    subst a1.
    cbn in Hab.
    apply sorted_extends with (l := la ++ lb); [ easy | easy | ].
    now apply in_or_app; right.
  }
} {
  intros (Hla & Hlb & Hab).
  revert lb Hlb Hab.
  induction la as [| a1]; intros; [ easy | ].
  assert (H : sorted rel la) by now apply sorted_cons in Hla.
  specialize (IHla H); clear H.
  destruct la as [| a2]; intros; cbn. {
    unfold sorted; cbn.
    destruct lb as [| b]; [ easy | ].
    apply Bool.andb_true_iff.
    split; [ | easy ].
    now apply Hab; left.
  }
  apply sorted_cons_cons_true_iff in Hla.
  apply sorted_cons_cons_true_iff.
  split; [ easy | ].
  apply IHla; [ easy | ].
  intros * Ha Hb.
  apply Hab; [ now right | easy ].
}
Qed.

Theorem sorted_trans : ∀ A (rel : A → _),
  transitive rel →
  ∀ a b la,
  sorted rel (a :: la ++ [b]) →
  rel a b = true.
Proof.
intros * Htra * Hs.
revert a b Hs.
induction la as [| c]; intros. {
  cbn in Hs.
  now apply Bool.andb_true_iff in Hs.
}
remember (c :: la) as lb; cbn in Hs; subst lb.
rewrite <- app_comm_cons in Hs.
apply Bool.andb_true_iff in Hs.
destruct Hs as (Hac, Hs).
specialize (IHla _ _ Hs) as H1.
now apply Htra with (b := c).
Qed.

Theorem sorted_repeat : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  ∀ a la,
  sorted rel (a :: la ++ [a])
  → la = repeat a (length la).
Proof.
intros * Hant Htra * Hs.
revert a Hs.
induction la as [| b]; intros; [ easy | cbn ].
remember (b :: la) as lb; cbn in Hs; subst lb.
rewrite <- app_comm_cons in Hs.
apply Bool.andb_true_iff in Hs.
destruct Hs as (Hab, Hs).
specialize (sorted_trans Htra _ _ Hs) as Hba.
specialize (Hant a b Hab Hba) as H1; subst b.
f_equal.
now apply IHla.
Qed.

(* isort: sort by insertion *)

Fixpoint isort_insert {A} (rel : A → A → bool) a lsorted :=
  match lsorted with
  | [] => [a]
  | b :: l => if rel a b then a :: lsorted else b :: isort_insert rel a l
  end.

Fixpoint isort {A} (rel : A → A → bool) l :=
  match l with
  | [] => []
  | a :: l' => isort_insert rel a (isort rel l')
  end.

(* ssort: sort by selection *)

Fixpoint select_first {A} (rel : A → A → bool) a la :=
  match la with
  | [] => (a, [])
  | b :: lb =>
      let (c, lc) := select_first rel (if rel a b then a else b) lb in
      (c, (if rel a b then b else a) :: lc)
  end.

Fixpoint ssort_loop {A} (rel : A → A → bool) it l :=
  match it with
  | 0 => l
  | S it' =>
      match l with
      | [] => []
      | a :: la =>
          let (a', la') := select_first rel a la in
          a' :: ssort_loop rel it' la'
      end
  end.

Definition ssort {A} (rel : A → _) l := ssort_loop rel (length l) l.

(* bsort: bubble sort *)

Fixpoint bsort_swap {A} (rel : A → A → bool) l :=
  match l with
  | [] | [_] => None
  | a :: (b :: l'') as l' =>
      if rel a b then
        match bsort_swap rel l' with
        | Some l''' => Some (a :: l''')
        | None => None
        end
      else
        Some (b :: a :: l'')
  end.

Fixpoint bsort_loop {A} (rel : A → A → bool) it l :=
  match it with
  | 0 => l
  | S it' =>
      match bsort_swap rel l with
      | Some l' => bsort_loop rel it' l'
      | None => l
      end
  end.

Definition bsort {A} (rel : A → _) l := bsort_loop rel (length l * length l) l.

(* merge sort *)

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

(* *)

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
  now apply length_zero_iff_nil in Hlen; subst la; cbn.
}
cbn.
rewrite (IHla lb); [ easy | ].
cbn in Hlen.
now destruct Hlen as [H| H]; [ left | right ]; now apply Nat.succ_inj in H.
Qed.

Theorem merge_loop_length : ∀ A (rel : A → _) la lb it,
  length (la ++ lb) ≤ it
  → length (merge_loop rel it la lb) = length (la ++ lb).
Proof.
intros * Hit.
revert la lb Hit.
induction it; intros; cbn. {
  apply Nat.le_0_r, length_zero_iff_nil in Hit.
  now rewrite Hit.
}
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ now cbn; rewrite app_nil_r | ].
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; cbn; f_equal. {
  apply IHit; cbn in Hit.
  now apply Nat.succ_le_mono in Hit.
}
rewrite IHit; cbn. {
  do 2 rewrite app_length; cbn.
  symmetry; apply Nat.add_succ_r.
} {
  rewrite app_length in Hit; cbn in Hit.
  apply Nat.succ_le_mono in Hit.
  now rewrite Nat.add_succ_r, <- app_length in Hit.
}
Qed.

Theorem merge_length : ∀ A (rel : A → _) la lb,
  length (merge rel la lb) = length (la ++ lb).
Proof.
intros.
unfold merge.
apply merge_loop_length.
now rewrite app_length.
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

Theorem msort_loop_length : ∀ A (rel : A → _) it la,
  length (msort_loop rel it la) = length la.
Proof.
intros.
revert la.
induction it; intros; [ easy | cbn ].
remember (split_list la) as ll eqn:Hll; symmetry in Hll.
destruct ll as (lb, lc).
rewrite merge_length.
rewrite app_length.
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
  apply length_zero_iff_nil in Hlen; subst l.
  now injection Hla; clear Hla; intros; subst la lb.
}
destruct l as [| c]; [ easy | ].
cbn in Hlen; apply Nat.succ_inj in Hlen.
destruct len. {
  apply length_zero_iff_nil in Hlen; subst l.
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

Theorem sorted_merge_loop_cons_cons_r_aux : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  ∀ n it l la lb a b,
  length (repeat a (n + n) ++ a :: b :: l) ≤ n + it
  → rel a a = true
  → sorted rel (a :: b :: l)
  → split_list l = (la, lb)
  → merge_loop rel it la (repeat a n ++ a :: b :: lb) =
    merge_loop rel it (a :: la) (repeat a n ++ b :: lb).
Proof.
intros * Hant Htra * Hit Haa Hs Hla.
rewrite app_length, repeat_length in Hit; cbn in Hit.
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
  rewrite List_app_cons, app_assoc.
  rewrite <- repeat_cons; symmetry.
  rewrite List_app_cons, app_assoc.
  rewrite <- repeat_cons; symmetry.
  do 2 rewrite app_comm_cons.
  replace (a :: a :: repeat a n) with (repeat a (S (S n))) by easy.
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

Theorem sorted_merge_loop_cons_cons : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  ∀ it l la lb a b,
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
  now apply Nat.le_0_r, length_zero_iff_nil in Hit; subst l.
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

Theorem merge_loop_when_sorted : ∀ A (rel : A → _),
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

Theorem fold_isort : ∀ A (rel : A → _) a l,
  isort_insert rel a (isort rel l) = isort rel (a :: l).
Proof. easy. Qed.

(* isort length *)

Theorem isort_insert_length : ∀ A rel (a : A) lsorted,
  length (isort_insert rel a lsorted) = S (length lsorted).
Proof.
intros.
induction lsorted as [| b]; intros; [ easy | cbn ].
destruct (rel a b); [ easy | ].
now cbn; f_equal.
Qed.

Theorem isort_length : ∀ A rel (l : list A), length (isort rel l) = length l.
Proof.
intros.
induction l as [| a]; [ easy | cbn ].
rewrite <- IHl.
apply isort_insert_length.
Qed.

(* ssort length *)

Theorem select_first_length : ∀ A rel (a : A) la b lb,
  select_first rel a la = (b, lb)
  → length lb = length la.
Proof.
intros * Hab.
revert a b lb Hab.
induction la as [| a']; intros; cbn in Hab |-*. {
  now injection Hab; clear Hab; intros; subst b lb.
}
remember (rel a a') as x eqn:Hx; symmetry in Hx.
remember (select_first rel (if x then a else a') la) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as (c, lc).
injection Hab; clear Hab; intros; subst c lb.
cbn; f_equal.
now destruct x; apply IHla in Hlc.
Qed.

(* *)

Theorem in_isort_insert_id : ∀ A (rel : A → _) a l,
  a ∈ isort_insert rel a l.
Proof.
intros.
induction l as [| b]; [ now left | cbn ].
now destruct (rel a b); [ left | right ].
Qed.

Theorem permutation_cons_isort_insert_id : ∀ A (eqb rel : A → _),
  equality eqb →
  ∀ a la,
  permutation eqb (a :: la) (isort_insert rel a la).
Proof.
intros * Heqb *.
revert a.
induction la as [| b]; intros; [ now apply permutation_refl | cbn ].
destruct (rel a b); [ now apply permutation_refl | ].
eapply (permutation_trans Heqb); [ now apply permutation_swap | ].
apply permutation_skip; [ | easy ].
now unfold reflexive; apply equality_refl.
Qed.

Theorem permutation_cons_isort_insert : ∀ A (eqb rel : A → _),
  equality eqb →
  ∀ a la lb,
  permutation eqb la lb → permutation eqb (a :: la) (isort_insert rel a lb).
Proof.
intros * Heqb * Hpab; cbn.
apply permutation_cons_l_iff.
remember (extract (eqb a) (isort_insert rel a lb)) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl a) as H1.
  specialize (in_isort_insert_id rel a lb) as H.
  specialize (H1 H); clear H.
  now rewrite (equality_refl Heqb) in H1.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hli).
apply Heqb in H; subst x.
apply (permutation_trans Heqb) with (lb := lb); [ easy | ].
clear la Hpab.
rename lb into la.
revert bef aft Hbef Hli.
induction la as [| b]; intros. {
  cbn in Hli |-*.
  destruct bef as [| b]. {
    now injection Hli; clear Hli; intros; subst aft.
  }
  cbn in Hli.
  injection Hli; clear Hli; intros Hli H; subst b.
  now destruct bef.
}
cbn in Hli.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. 2: {
  destruct bef as [| c]. {
    cbn in Hli.
    injection Hli; clear Hli; intros; subst aft; cbn; subst b.
    clear IHla Hbef Hab.
    now apply permutation_cons_isort_insert_id.
  }
  cbn in Hli.
  injection Hli; clear Hli; intros Hli H; subst c; cbn.
  apply permutation_skip; [ now unfold reflexive; apply equality_refl | ].
  apply IHla; [ | easy ].
  now intros c Hc; apply Hbef; right.
}
destruct bef as [| c]. {
  cbn in Hli.
  injection Hli; clear Hli; intros; subst aft.
  now apply permutation_refl.
}
cbn in Hli.
injection Hli; clear Hli; intros Hli H; subst c; cbn.
rewrite Hli.
apply permutation_sym; [ easy | ].
now apply permutation_middle.
Qed.

Theorem permuted_isort_insert_sorted : ∀ A (eqb rel : A → _),
  equality eqb →
  ∀ la lb c,
  permutation eqb la lb
  → permutation eqb (isort_insert rel c la) (isort_insert rel c lb).
Proof.
intros * Heqb * Hp.
eapply (permutation_trans Heqb). 2: {
  apply (permutation_cons_isort_insert rel Heqb), Hp.
}
apply (permutation_sym Heqb).
apply (permutation_cons_isort_insert rel Heqb).
now apply permutation_refl.
Qed.

(* in isort *)

Theorem in_isort_insert : ∀ A (rel : A → A → bool) a b lsorted,
  a ∈ isort_insert rel b lsorted
  → a ∈ b :: lsorted.
Proof.
intros * Ha.
revert a b Ha.
induction lsorted as [| c]; intros. {
  cbn in Ha.
  destruct Ha as [Ha| Ha]; [ now left | easy ].
}
cbn in Ha.
destruct (rel b c); [ easy | ].
destruct Ha as [Ha| Ha]; [ now right; left | ].
apply IHlsorted in Ha.
destruct Ha as [Ha| Ha]; [ now left | now right; right ].
Qed.

Theorem in_isort : ∀ A (rel : A → A → bool) a l, a ∈ isort rel l → a ∈ l.
Proof.
intros * Ha.
revert a Ha.
induction l as [| b]; intros; [ easy | ].
cbn in Ha.
apply in_isort_insert in Ha.
destruct Ha as [Ha| Ha]; [ now left | now right; apply IHl ].
Qed.

(* *)

Theorem select_first_permutation :
  ∀ A (eqb rel : A → _) (Heqb : equality eqb),
  ∀ a b la lb,
  select_first rel a la = (b, lb)
  → permutation eqb (a :: la) (b :: lb).
Proof.
intros * Heqb * Hab.
revert a b lb Hab.
induction la as [| c]; intros. {
  cbn in Hab.
  injection Hab; clear Hab; intros; subst b lb.
  now apply permutation_refl.
}
cbn in Hab.
remember (rel a c) as ac eqn:Hac; symmetry in Hac.
destruct ac. {
  remember (select_first rel a la) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as (d, ld).
  injection Hab; clear Hab; intros; subst d lb.
  move c after b; move ld before la.
  apply permutation_cons_l_iff; cbn.
  remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
  destruct ab. {
    apply Heqb in Hab; subst b; cbn.
    specialize (IHla _ _ _ Hlc) as H1.
    apply permutation_cons_l_iff in H1; cbn in H1.
    rewrite (equality_refl Heqb) in H1; cbn in H1.
    apply permutation_skip; [ | easy ].
    now unfold reflexive; apply equality_refl.
  }
  remember (eqb a c) as eac eqn:Heac; symmetry in Heac.
  destruct eac. {
    apply Heqb in Heac; subst c; cbn.
    apply (IHla _ _ _ Hlc).
  }
  specialize (IHla _ _ _ Hlc) as H1.
  apply permutation_cons_l_iff in H1.
  cbn in H1; rewrite Hab in H1.
  remember (extract (eqb a) ld) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef, x), aft)| ]; [ | easy ].
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (H2 & H & H3).
  apply Heqb in H; subst x.
  cbn in H1 |-*.
  apply permutation_cons_l_iff; cbn.
  rewrite (equality_refl Heqb).
  remember (eqb c b) as cb eqn:Hcb; symmetry in Hcb.
  destruct cb; [ now apply Heqb in Hcb; subst c | easy ].
}
remember (select_first rel c la) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (d, ld).
injection Hab; clear Hab; intros; subst d lb; cbn.
apply permutation_cons_l_iff; cbn.
remember (eqb a b) as ab eqn:Heab; symmetry in Heab.
destruct ab. {
  apply Heqb in Heab; subst b; cbn.
  now apply IHla.
}
rewrite (equality_refl Heqb); cbn.
now apply IHla.
Qed.

Theorem permuted_ssort_loop : ∀ A (eqb rel : A → _) (Heqb : equality eqb),
  ∀ la len,
  length la ≤ len
  → permutation eqb la (ssort_loop rel len la).
Proof.
intros * Heqb * Hlen.
revert la Hlen.
induction len; intros. {
  now apply Nat.le_0_r, length_zero_iff_nil in Hlen; subst la.
}
destruct la as [| a]; [ easy | ].
cbn in Hlen; apply Nat.succ_le_mono in Hlen; cbn.
remember (select_first rel a la) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as (c, lc).
specialize (IHlen lc) as H1.
assert (H : length lc ≤ len). {
  apply select_first_length in Hlc.
  congruence.
}
specialize (H1 H); clear H.
apply (select_first_permutation rel Heqb) in Hlc.
apply (permutation_trans Heqb) with (lb := c :: lc); [ easy | ].
apply permutation_skip; [ | easy ].
now unfold reflexive; apply equality_refl.
Qed.

Theorem select_first_if : ∀ A (rel : A → _),
  transitive rel →
  total_relation rel →
  ∀ a b la lb,
  select_first rel a la = (b, lb)
  → (∀ c, c ∈ a :: la → rel b c = true) ∧
    (∀ c, c ∈ lb → rel b c = true).
Proof.
intros * Htr Htot * Hab.
revert a b lb Hab.
induction la as [| c]; intros. {
  cbn in Hab.
  injection Hab; clear Hab; intros; subst b lb.
  split; [ | easy ].
  intros c Hc.
  destruct Hc as [Hc| Hc]; [ | easy ].
  subst c.
  apply total_relation_is_reflexive in Htot.
  apply Htot.
}
cbn in Hab.
remember (if rel a c then a else c) as x eqn:Hx; symmetry in Hx.
remember (select_first rel x la) as ld eqn:Hld; symmetry in Hld.
destruct ld as (d, ld).
injection Hab; clear Hab; intros; subst d lb.
move c after b; move x before c.
move ld before la.
remember (rel a c) as ac eqn:Hac; symmetry in Hac.
specialize (IHla x b ld Hld) as H1.
destruct H1 as (H1 & H2).
split. {
  intros d Hd.
  destruct Hd as [Hd| [Hd| Hd]]. {
    subst d.
    destruct ac; subst x. {
      now specialize (H1 a (or_introl eq_refl)).
    }
    specialize (H1 c (or_introl eq_refl)) as H4.
    apply Htr with (b := c); [ easy | ].
    specialize (Htot a c) as H5.
    now rewrite Hac in H5; cbn in H5.
  } {
    subst d.
    destruct ac; subst x; [ | now apply H1; left ].
    apply Htr with (b := a); [ | easy ].
    now apply H1; left.
  } {
    now apply H1; right.
  }
}
intros d Hd.
destruct ac; subst x. {
  destruct Hd as [Hd| Hd]; [ | now apply H2 ].
  subst d.
  apply Htr with (b := a); [ | easy ].
  now apply H1; left.
} {
  destruct Hd as [Hd| Hd]; [ | now apply H2 ].
  subst d.
  apply Htr with (b := c); [ now apply H1; left | ].
  specialize (Htot a c) as H5.
  now rewrite Hac in H5.
}
Qed.

Theorem select_first_in : ∀ A (rel : A → _),
  ∀ a b la lb,
  select_first rel a la = (b, lb)
  → b ∈ a :: la.
Proof.
intros * Hs.
revert a b lb Hs.
induction la as [| c]; intros; cbn in Hs. {
  now injection Hs; intros; subst b lb; left.
}
remember (rel a c) as ac eqn:Hac; symmetry in Hac.
destruct ac. {
  remember (select_first rel a la) as lc eqn:Hlc.
  symmetry in Hlc.
  destruct lc as (d, ld).
  injection Hs; clear Hs; intros; subst d lb.
  specialize (IHla _ _ _ Hlc).
  now destruct IHla as [H1| H1]; [ left | right; right ].
}
remember (select_first rel c la) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as (d, ld).
injection Hs; clear Hs; intros; subst d lb.
right.
apply (IHla _ _ _ Hlc).
Qed.

Theorem ssort_loop_in : ∀ A (rel : A → _) it b la lb,
  ssort_loop rel it la = b :: lb
  → b ∈ la.
Proof.
intros * Hs.
revert b la lb Hs.
induction it; intros; cbn in Hs; [ now subst la; left | ].
destruct la as [| a]; [ easy | ].
remember (select_first rel a la) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as (c, lc).
injection Hs; clear Hs; intros Hs H; subst c.
now apply select_first_in in Hlc.
Qed.

Theorem sorted_ssort_loop : ∀ A (rel : A → _),
  transitive rel →
  total_relation rel →
  ∀ l len,
  length l ≤ len
  → sorted rel (ssort_loop rel len l).
Proof.
intros * Htr Htot * Hlen.
unfold sorted.
revert l Hlen.
induction len; intros; cbn. {
  now apply Nat.le_0_r, length_zero_iff_nil in Hlen; subst l.
}
destruct l as [| a la]; [ easy | cbn ].
cbn in Hlen; apply Nat.succ_le_mono in Hlen.
remember (select_first rel a la) as lb eqn:Hlb.
symmetry in Hlb.
destruct lb as (b, lb); cbn.
remember (ssort_loop rel len lb) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [| c]; [ easy | ].
apply Bool.andb_true_iff.
split. 2: {
  rewrite <- Hlc.
  apply IHlen.
  apply select_first_length in Hlb.
  congruence.
}
apply Bool.not_false_iff_true.
intros Hbc.
specialize (Htot b c) as Hcb.
rewrite Hbc in Hcb; cbn in Hcb.
apply (select_first_if Htr Htot) in Hlb.
destruct Hlb as (H1 & H2).
specialize (H2 c).
assert (H : c ∈ lb) by now apply ssort_loop_in in Hlc.
specialize (H2 H); clear H.
now rewrite H2 in Hbc.
Qed.

(* isort is sorted *)

Theorem sorted_isort_insert : ∀ A (rel : A → _),
  total_relation rel →
  ∀ a lsorted,
  sorted rel lsorted
  → sorted rel (isort_insert rel a lsorted).
Proof.
intros * Htot * Hs.
unfold sorted in Hs |-*.
revert a Hs.
induction lsorted as [| b]; intros; [ easy | cbn ].
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  remember (b :: lsorted) as l; cbn; subst l.
  now rewrite Hs, Hab.
} {
  cbn in Hs |-*.
  destruct lsorted as [| c]. {
    cbn; rewrite Bool.andb_true_r.
    specialize (Htot a b) as Hba.
    now rewrite Hab in Hba.
  }
  apply Bool.andb_true_iff in Hs.
  destruct Hs as (Hbc, Hs); cbn.
  specialize (IHlsorted a Hs) as H1.
  cbn in H1.
  remember (rel a c) as ac eqn:Hac; symmetry in Hac.
  rewrite H1.
  destruct ac; [ | now rewrite Hbc ].
  rewrite Bool.andb_true_r.
  specialize (Htot a b) as Hba.
  now rewrite Hab in Hba.
}
Qed.

Theorem select_first_sorted : ∀ A rel,
  transitive rel → ∀ (a b : A) la lb,
  sorted rel (a :: la)
  → select_first rel a la = (b, lb)
  → a = b ∧ la = lb.
Proof.
intros * Htr * Hs Hss.
revert a b lb Hs Hss.
induction la as [| c]; intros. {
  cbn in Hss.
  now injection Hss; intros.
}
remember (c :: la) as l; cbn in Hs; subst l.
apply Bool.andb_true_iff in Hs.
destruct Hs as (H1, H2).
cbn in Hss.
rewrite H1 in Hss.
remember (select_first rel a la) as ld eqn:Hld.
symmetry in Hld.
destruct ld as (d, ld).
injection Hss; clear Hss; intros; subst d lb.
rename ld into lb.
enough (H : a = b ∧ la = lb). {
  split; [ easy | now f_equal ].
}
apply IHla; [ | easy ].
cbn in H2 |-*.
destruct la as [| d]; [ easy | ].
apply Bool.andb_true_iff in H2.
apply Bool.andb_true_iff.
destruct H2 as (H2, H3).
split; [ | easy ].
now apply Htr with (b := c).
Qed.

Theorem ssort_loop_when_sorted : ∀ A (rel : A → _),
  transitive rel →
  ∀ it l,
  length l ≤ it
  → sorted rel l
  → ssort_loop rel it l = l.
Proof.
intros * Htr * Hit Hs.
revert l Hit Hs.
induction it; intros; [ easy | cbn ].
destruct l as [| a la]; [ easy | ].
cbn in Hit; apply Nat.succ_le_mono in Hit.
remember (select_first rel a la) as lb eqn:Hlb.
symmetry in Hlb.
destruct lb as (b, lb).
specialize (select_first_sorted Htr Hs Hlb) as H1.
destruct H1; subst b lb.
f_equal.
apply IHit; [ easy | ].
cbn in Hs.
destruct la as [| b]; [ easy | ].
now apply Bool.andb_true_iff in Hs.
Qed.

Theorem bsort_swap_when_sorted : ∀ A (rel : A → _),
  ∀ la,
  sorted rel la
  → bsort_swap rel la = None.
Proof.
intros * Hs.
induction la as [| a]; [ easy | ].
cbn in Hs |-*.
destruct la as [| b]; [ easy | ].
apply Bool.andb_true_iff in Hs.
destruct Hs as (Hab, Hs).
rewrite Hab.
now rewrite IHla.
Qed.

Theorem bsort_loop_when_sorted : ∀ A (rel : A → _),
  ∀ it l,
  sorted rel l
  → bsort_loop rel it l = l.
Proof.
intros * Hs.
rename l into la.
revert la Hs.
induction it; intros; [ easy | cbn ].
remember (bsort_swap rel la) as lb eqn:Hlb.
symmetry in Hlb.
destruct lb as [lb| ]; [ | easy ].
now rewrite bsort_swap_when_sorted in Hlb.
Qed.

Theorem bsort_swap_None : ∀ A (rel : A → _) la,
  bsort_swap rel la = None
  → sorted rel la.
Proof.
intros * Hs.
induction la as [| a]; [ easy | cbn ].
cbn in Hs.
destruct la as [| b]; [ easy | ].
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ | easy ].
remember (bsort_swap rel (b :: la)) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [lc| ]; [ easy | clear Hs ].
unfold sorted in IHla |-*; cbn in IHla |-*.
now rewrite (IHla eq_refl), Hab.
Qed.

Theorem bsort_swap_Some : ∀ A (rel : A → _) la lb,
  bsort_swap rel la = Some lb
  → is_sorted rel la = false ∧
    ∃ a b lc ld, rel a b = false ∧
    sorted rel (lc ++ [a]) ∧
    la = lc ++ a :: b :: ld ∧
    lb = lc ++ b :: a :: ld.
Proof.
intros * Hs.
revert lb Hs.
induction la as [| a]; intros; [ easy | ].
cbn in Hs.
destruct la as [| b]; [ easy | ].
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
remember (bsort_swap rel (b :: la)) as ld eqn:Hld.
symmetry in Hld.
destruct ld as [ld| ]. 2: {
  destruct ab; [ easy | ].
  injection Hs; clear Hs; intros; subst lb.
  split; [ now cbn; rewrite Hab | ].
  now exists a, b, [], la.
}
destruct ab. 2: {
  injection Hs; clear Hs; intros; subst lb.
  split; [ now cbn; rewrite Hab | ].
  now exists a, b, [], la.
}
injection Hs; clear Hs; intros; subst lb.
specialize (IHla ld eq_refl) as H1.
destruct H1 as (Hns & H1).
destruct H1 as (c & d & lc & le & H1).
destruct H1 as (Hsc & Hbla & Hlc & Hle).
split. {
  remember (b :: la) as lb eqn:Hlb; cbn; subst lb.
  rewrite Hns.
  apply Bool.andb_false_r.
}
exists c, d, (a :: lc), le.
split; [ easy | ].
split. {
  cbn.
  destruct lc as [| e]. {
    cbn in Hlc |-*.
    injection Hlc; clear Hlc; intros Hlc H; subst c la.
    unfold sorted; cbn.
    now rewrite Hab.
  }
  cbn in Hlc.
  injection Hlc; clear Hlc; intros Hlc H; subst e.
  unfold sorted in Hbla |-*.
  cbn in Hbla |-*.
  now rewrite Hab, Hbla.
}
rewrite Hlc, Hle.
easy.
Qed.

Fixpoint nb_nrel A (rel : A → A → bool) a l :=
  match l with
  | [] => 0
  | b :: l' => (if rel a b then 0 else 1) + nb_nrel rel a l'
  end.

Fixpoint nb_disorder A (rel : A → _) l :=
  match l with
  | [] => 0
  | a :: l' => nb_nrel rel a l' + nb_disorder rel l'
  end.

Theorem nb_disorder_le_square : ∀ A (rel : A → _) l,
  nb_disorder rel l ≤ length l * length l.
Proof.
intros.
induction l as [| a]; [ easy | cbn ].
rewrite Nat.mul_comm; cbn.
rewrite -> Nat.add_assoc.
rewrite <- Nat.add_succ_l.
apply Nat.add_le_mono; [ | easy ].
clear.
induction l as [| b]; [ easy | cbn ].
destruct (rel a b); cbn; flia IHl.
Qed.

Theorem bsort_swap_nb_disorder : ∀ A (rel : A → _),
  total_relation rel →
  ∀ la lb it,
  bsort_swap rel la = Some lb
  → nb_disorder rel la ≤ S it
  → nb_disorder rel lb ≤ it.
Proof.
intros * Htot * Hbs Hnd.
revert lb it Hbs Hnd.
induction la as [| a]; intros; [ easy | ].
cbn in Hbs, Hnd.
destruct la as [| b]; [ easy | ].
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  remember (bsort_swap rel (b :: la)) as lc eqn:Hlc.
  symmetry in Hlc.
  destruct lc as [lc| ]; [ | easy ].
  injection Hbs; clear Hbs; intros; subst lb.
  remember (it - nb_nrel rel a (b :: la)) as it' eqn:Hit'.
  specialize (IHla lc it' eq_refl) as H1.
  assert (H : nb_disorder rel (b :: la) ≤ S it'). {
    rewrite Hit'; flia Hnd.
  }
  specialize (H1 H); clear H.
  cbn in Hit'.
  cbn in Hit'; rewrite Hab, Nat.add_0_l in Hit'.
  subst it'; cbn.
  assert (H : nb_nrel rel a la = nb_nrel rel a lc). {
    specialize (bsort_swap_Some _ _ Hlc) as H2.
    destruct H2 as (Hsf & a' & b' & ld & le & H2).
    destruct H2 as (Hab' & Hst & Hbla & Hlc').
    subst lc.
    destruct ld as [| c]. {
      cbn in Hbla |-*.
      injection Hbla; clear Hbla; intros; subst a' la.
      now cbn; rewrite Hab.
    }
    cbn in Hbla.
    injection Hbla; intros; subst c la.
    cbn; rewrite Hab; cbn.
    clear.
    induction ld as [| b]; cbn. {
      do 2 rewrite Nat.add_assoc.
      f_equal.
      apply Nat.add_comm.
    }
    f_equal; apply IHld.
  }
  rewrite H in H1.
  assert (H' : nb_nrel rel a lc ≤ it). {
    rewrite <- H.
    cbn - [ nb_disorder ] in Hnd.
    rewrite Hab, Nat.add_0_l in Hnd.
    assert (H' : nb_disorder rel (b :: la) ≠ 0). {
      specialize (bsort_swap_Some _ _ Hlc) as H2.
      destruct H2 as (Hsf & a' & b' & lab & ld & H2).
      destruct H2 as (Hab' & Hst & Hla & Hld).
      rewrite Hla.
      clear - Hab'.
      induction lab as [| a]; cbn; [ now rewrite Hab' | ].
      flia IHlab.
    }
    flia Hnd H'.
  }
  flia H1 H'.
}
injection Hbs; clear Hbs; intros; subst lb.
cbn in Hnd |-*.
rewrite Hab in Hnd; cbn in Hnd.
apply Nat.succ_le_mono in Hnd.
specialize (Htot a b) as Hba.
rewrite Hab in Hba; cbn in Hba.
rewrite Hba, Nat.add_0_l.
rewrite Nat.add_assoc.
rewrite (Nat.add_comm (nb_nrel rel b la)).
now rewrite <- Nat.add_assoc.
Qed.

Theorem sorted_bsort_loop_nb_disorder : ∀ A (rel : A → _),
  total_relation rel →
  ∀ it la,
  nb_disorder rel la ≤ it
  → sorted rel (bsort_loop rel it la).
Proof.
intros * Htot * Hit.
revert la Hit.
induction it; intros. {
  apply Nat.le_0_r in Hit.
  induction la as [| a]; [ easy | ].
  cbn in Hit |-*.
  apply Nat.eq_add_0 in Hit.
  destruct Hit as (Hra, Hd).
  specialize (IHla Hd).
  cbn in IHla.
  unfold sorted in IHla |-*; cbn in IHla |-*.
  rewrite IHla.
  destruct la as [| b]; [ easy | ].
  rewrite Bool.andb_true_r.
  cbn in Hra.
  remember (rel a b) as ab eqn:Hab.
  symmetry in Hab.
  now destruct ab.
}
cbn.
remember (bsort_swap rel la) as lb eqn:Hlb.
symmetry in Hlb.
destruct lb as [lb| ]; [ | now apply bsort_swap_None ].
apply IHit.
now apply (bsort_swap_nb_disorder Htot la).
Qed.

Theorem sorted_bsort_loop : ∀ A (rel : A → _),
  total_relation rel →
  ∀ it l,
  length l * length l ≤ it
  → sorted rel (bsort_loop rel it l).
Proof.
intros * Htot * Hit.
rename l into la.
eapply le_trans in Hit. 2: {
  apply (nb_disorder_le_square rel).
}
now apply sorted_bsort_loop_nb_disorder.
Qed.

Theorem permuted_bsort_loop : ∀ A (eqb rel : A → _) (Heqb : equality eqb),
  ∀ la it, permutation eqb la (bsort_loop rel it la).
Proof.
intros.
revert la.
induction it; intros; [ now apply permutation_refl | cbn ].
remember (bsort_swap rel la) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [lb| ]; [ | now apply permutation_refl ].
apply bsort_swap_Some in Hlb.
destruct Hlb as (Hs & c & d & lc & ld & Hlb).
destruct Hlb as (Hcd & Hrc & Hbla & Hlbc).
apply (permutation_trans Heqb) with (lb := lb); [ | apply IHit ].
subst la lb.
apply (permutation_app_head Heqb).
apply (permutation_swap Heqb).
Qed.

(* *)

Theorem permutation_merge_loop_aux :
  ∀ A (eqb rel : A → _) (Heqb : equality eqb),
  ∀ it la lb lc,
  length la + length lc ≤ it
  → permutation eqb (la ++ lb ++ lc) (lb ++ merge_loop rel it la lc).
Proof.
intros * Heqb * Hit.
revert la lb lc Hit.
induction it as (it, IHit) using lt_wf_rec; intros.
destruct it. {
  apply Nat.le_0_r, Nat.eq_add_0 in Hit.
  destruct Hit as (H1, H2).
  apply length_zero_iff_nil in H1, H2; subst la lc.
  cbn; rewrite app_nil_r; cbn.
  now apply permutation_refl.
}
destruct la as [| a]; [ now apply permutation_refl | ].
cbn in Hit; apply Nat.succ_le_mono in Hit; cbn.
destruct lc as [| b]. {
  rewrite app_nil_r.
  rewrite app_comm_cons.
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
do 2 rewrite app_assoc.
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
do 2 rewrite app_comm_cons.
rewrite <- app_assoc.
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
  rewrite app_nil_r.
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

Theorem permutation_merge : ∀ A (eqb rel : A → _) (Heqb : equality eqb),
  ∀ l la lb,
  split_list l = (la, lb)
  → permutation eqb l (merge rel la lb).
Proof.
intros * Heqb * Hll.
now apply permutation_split_list_merge_loop.
Qed.

Theorem permutation_app_split_list_inv : ∀ A (eqb : A → _) (Heqb : equality eqb),
  ∀ la lb, permutation eqb (la ++ lb) (split_list_inv la lb).
Proof.
intros * Heqb *.
revert lb.
induction la as [| a]; intros; cbn. {
  destruct lb as [| b]; [ apply permutation_nil_nil | ].
  apply (permutation_refl Heqb).
}
destruct lb as [| b]. {
  rewrite app_nil_r.
  apply (permutation_refl Heqb).
}
apply permutation_skip; [ now unfold reflexive; apply equality_refl | ].
apply (permutation_trans Heqb) with (lb := (b :: (la ++ lb))). {
  rewrite List_app_cons, app_assoc, app_comm_cons.
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
  ∀ A (eqb : A → _) (Heqb : equality eqb),
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
apply in_split in Hc, Hd.
destruct Hc as (lc1 & lc2 & Hc).
destruct Hd as (ld1 & ld2 & Hd).
subst lc ld.
eapply (permutation_trans Heqb); [ | now apply permutation_app_split_list_inv ].
specialize (permutation_app_inv Heqb [] la lc1 lc2 a Hac) as H1.
specialize (permutation_app_inv Heqb [] lb ld1 ld2 b Hbd) as H2.
cbn in H1, H2; clear Hac Hbd.
apply (permutation_sym Heqb).
rewrite (List_cons_is_app a).
rewrite (List_cons_is_app b).
rewrite <- app_assoc.
eapply (permutation_trans Heqb); [ now apply permutation_app_comm | cbn ].
apply permutation_skip; [ now unfold reflexive; apply equality_refl | ].
rewrite (List_cons_is_app b).
do 3 rewrite <- app_assoc.
rewrite app_assoc.
eapply (permutation_trans Heqb); [ now apply permutation_app_comm | cbn ].
apply permutation_skip; [ now unfold reflexive; apply equality_refl | ].
rewrite <- app_assoc.
eapply (permutation_trans Heqb); [ now apply permutation_app_comm | ].
do 2 rewrite <- app_assoc.
rewrite app_assoc.
eapply (permutation_trans Heqb); [ now apply permutation_app_split_list_inv | ].
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
  apply (f_equal length) in Hlc, Hld.
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

Theorem sorted_middle : ∀ A (rel : A → _),
  transitive rel →
  ∀ a b la lb lc,
  sorted rel (la ++ a :: lb ++ b :: lc)
  → rel a b = true.
Proof.
intros * Htra * Hsort.
rewrite (List_cons_is_app a) in Hsort.
rewrite (List_cons_is_app b) in Hsort.
rewrite app_assoc in Hsort.
apply (sorted_app_iff Htra) in Hsort.
destruct Hsort as (Hla & Hsort & H1).
apply H1; [ now apply in_or_app; right; left | ].
apply in_or_app; right.
now apply in_or_app; left; left.
Qed.

Theorem sorted_any : ∀ A (rel : A → A → bool),
  transitive rel →
  ∀ l, sorted rel l →
  ∀ i j d,
  i < j
  → j < length l
  → rel (nth i l d) (nth j l d) = true.
Proof.
intros * Htrans * Hsort * Hij Hj.
assert (Hi : i < length l) by now transitivity j.
specialize nth_split as H1.
specialize (H1 A i l d Hi).
destruct H1 as (la & lb & Hl & Hla).
remember (nth i l d) as a eqn:Ha; clear Ha.
subst l i.
rewrite List_app_cons, app_assoc.
rewrite app_nth2; rewrite app_length, Nat.add_comm; cbn; [ | easy ].
remember (j - S (length la)) as k eqn:Hkj.
assert (Hk : k < length lb). {
  subst k.
  rewrite app_length in Hj; cbn in Hj.
  flia Hj Hij.
}
specialize nth_split as H1.
specialize (H1 A k lb d Hk).
destruct H1 as (lc & ld & Hl & Hlc).
remember (nth k lb d) as b eqn:Hb.
subst lb.
clear j k Hb Hij Hj Hkj Hk Hlc Hi.
rename lc into lb; rename ld into lc.
now apply sorted_middle in Hsort.
Qed.

Theorem sorted_nat_ltb_leb_incl : ∀ l,
  sorted Nat.ltb l → sorted Nat.leb l.
Proof.
intros * Hs.
induction l as [| a]; [ easy | ].
cbn - [ Nat.ltb ] in Hs |-*.
destruct l as [| b]; [ easy | ].
apply Bool.andb_true_iff in Hs.
apply Bool.andb_true_iff.
destruct Hs as (Hab, Hs).
split; [ | now apply IHl ].
apply Nat.ltb_lt in Hab.
now apply Nat.leb_le, Nat.lt_le_incl.
Qed.

Theorem sorted_sorted_permuted_not_antisym_1 : ∀ A (eqb leb : A → A → bool),
  equality eqb →
  reflexive leb →
  transitive leb →
  ∀ (d : A) (la lb : list A),
  sorted leb la
  → sorted leb lb
  → permutation eqb la lb
  → ∀ i, leb (nth i la d) (nth i lb d) = true.
Proof.
intros * Heqb Href Htra * Hsa Hsb Hpab i.
revert lb Hpab Hsb i.
induction la as [| a]; intros. {
  apply permutation_nil_l in Hpab; subst lb.
  apply Href.
}
assert (H : sorted leb la) by now apply sorted_cons in Hsa.
specialize (IHla H); clear H.
remember (length (a :: la)) as len eqn:Hlena.
symmetry in Hlena.
assert (Hlenb : length lb = len). {
  apply permutation_length in Hpab; congruence.
}
destruct (lt_dec i len) as [Hilen| Hilen]. 2: {
  apply Nat.nlt_ge in Hilen.
  rewrite nth_overflow; [ | now rewrite Hlena ].
  rewrite nth_overflow; [ | now rewrite Hlenb ].
  apply Href.
}
remember (List_rank (λ b, negb (eqb a b)) la) as n eqn:Hn.
symmetry in Hn.
destruct (Nat.eq_dec n (length la)) as [Hnla| Hnla]. {
  apply (List_rank_if d) in Hn.
  destruct Hn as (Hbefn, Hn).
  destruct Hn as [Hn| Hn]; [ flia Hn Hnla | clear Hnla ].
  rewrite Hn in Hbefn; clear Hn; rename Hbefn into Hn.
  destruct i; cbn. {
    destruct lb as [| b]; cbn. {
      now apply permutation_nil_r in Hpab.
    }
    apply permutation_cons_l_iff in Hpab.
    remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
    destruct lxl as [((bef, x), aft)| ]; [ | easy ].
    apply extract_Some_iff in Hlxl.
    destruct Hlxl as (Hbef & H & Haft).
    apply Heqb in H; subst x.
    destruct bef as [| c]. {
      now injection Haft; intros; subst b.
    }
    destruct la as [| e]. {
      now apply permutation_nil_l in Hpab.
    }
    cbn in Haft.
    injection Haft; clear Haft; intros Hb H; subst c lb.
    cbn - [ nth ] in Hn.
    apply (permutation_in_iff Heqb) with (a := b) in Hpab.
    cbn - [ In ] in Hpab.
    specialize (proj2 Hpab (or_introl eq_refl)) as H1.
    apply (In_nth _ _ d) in H1; cbn - [ nth ] in H1.
    destruct H1 as (j & Hjl & Hj).
    specialize (Hn _ Hjl).
    rewrite Hj in Hn.
    apply Bool.negb_false_iff, Heqb in Hn; subst b.
    apply Href.
  }
  apply permutation_cons_l_iff in Hpab.
  remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef, x), aft)| ]; [ | easy ].
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef & H & Haft).
  apply Heqb in H; subst x lb.
  destruct bef as [| c]. {
    cbn; apply IHla; [ easy | now apply sorted_cons in Hsb ].
  }
  cbn in Hsb |-*.
  cbn in Hlena; rewrite <- Hlena in Hilen.
  apply Nat.succ_lt_mono in Hilen.
  specialize (Hn _ Hilen) as H1.
  apply Bool.negb_false_iff, Heqb in H1.
  rewrite <- H1.
  destruct (Nat.eq_dec i (length bef)) as [Hib| Hib]. {
    rewrite app_nth2; [ | now unfold ge; rewrite Hib ].
    rewrite Hib, Nat.sub_diag; cbn.
    apply Href.
  }
  assert (H : nth i (bef ++ a :: aft) d ∈ la). {
    cbn in Hpab.
    specialize (permutation_in_iff Heqb) as H2.
    apply H2 with (la := c :: bef ++ aft). {
      now apply (permutation_sym Heqb).
    }
    destruct (lt_dec i (length bef)) as [Hib1| Hib1]. {
      rewrite app_nth1; [ | easy ].
      right; apply in_or_app; left.
      now apply nth_In.
    }
    apply Nat.nlt_ge in Hib1.
    rewrite app_nth2; [ | easy ].
    replace (i - length bef) with (S (i - S (length bef))) by flia Hib1 Hib.
    cbn - [ In ].
    right; apply in_or_app; right.
    apply nth_In.
    cbn in Hlenb.
    rewrite app_length in Hlenb; cbn in Hlenb.
    flia Hlena Hlenb Hilen Hib Hib1.
  }
  apply (In_nth _ _ d) in H.
  destruct H as (j & Hjl & Hj).
  specialize (Hn _ Hjl) as H2.
  rewrite Hj in H2.
  apply Bool.negb_false_iff, Heqb in H2.
  rewrite <- H2.
  apply Href.
}
apply (List_rank_if d) in Hn.
destruct Hn as (Hbef, Hn).
destruct Hn as [Hn| Hn]; [ | easy ].
destruct Hn as (Hnl & Hwhi).
clear Hnla.
apply Bool.negb_true_iff in Hwhi.
destruct i. {
  cbn.
  destruct lb as [| b]; [ easy | cbn ].
  destruct n. {
    clear Hbef.
    destruct la as [| a']; [ easy | ].
    cbn in Hwhi.
    apply (sorted_cons_iff Htra) in Hsa.
    destruct Hsa as (Hsa, Haa).
    specialize (Haa a' (or_introl eq_refl)) as H1.
    apply permutation_cons_l_iff in Hpab.
    remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
    destruct lxl as [((bef, x), aft)| ]; [ | easy ].
    apply extract_Some_iff in Hlxl.
    destruct Hlxl as (Hbef & H & Haft).
    apply Heqb in H; subst x.
    apply (permutation_in_iff Heqb) with (a := b) in Hpab.
    remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
    destruct ab; [ apply Heqb in Hab; subst b; apply Href | ].
    apply Haa, Hpab.
    move Haft at bottom.
    destruct bef as [| c]. {
      cbn in Haft.
      injection Haft; clear Haft; intros; subst b aft.
      now rewrite (equality_refl Heqb) in Hab.
    }
    cbn in Haft; injection Haft; clear Haft; intros; subst c lb.
    now cbn; left.
  }
  remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
  destruct ab. {
    apply Heqb in Hab; subst b.
    apply Href.
  }
  apply (sorted_cons_iff Htra) in Hsa.
  destruct Hsa as (Hsa & Hbla).
  apply Hbla.
  apply (permutation_sym Heqb) in Hpab.
  apply permutation_cons_l_iff in Hpab.
  remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef, x), aft)| ]; [ | easy ].
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef' & H & Haft).
  apply Heqb in H; subst x.
  enough (H : b ∈ a :: la). {
    destruct H as [H| H]; [ subst b | easy ].
    now rewrite (equality_refl Heqb) in Hab.
  }
  rewrite Haft.
  now apply in_or_app; right; left.
}
destruct lb as [| b]; [ cbn in Hlena, Hlenb; congruence | cbn ].
remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  apply Heqb in Hab; subst b.
  apply IHla; [ | now apply sorted_cons in Hsb ].
  now apply (permutation_cons_inv Heqb) in Hpab.
}
apply permutation_cons_l_iff in Hpab.
remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef' & H & Haft).
apply Heqb in H; subst x.
destruct bef as [| c]. {
  cbn in Haft; injection Haft; intros; subst b aft.
  now rewrite (equality_refl Heqb) in Hab.
}
cbn in Haft; injection Haft; clear Haft; intros; subst c lb.
cbn in Hpab.
specialize (permutation_in_iff Heqb Hpab) as H1.
specialize (proj2 (H1 b) (or_introl eq_refl)) as H2.
apply (In_nth _ _ d) in H2.
destruct H2 as (j & Hj & Hb).
assert (Hjn : n ≤ j). {
  apply Nat.nlt_ge; intros H.
  specialize (Hbef _ H) as H2.
  rewrite Hb in H2.
  now rewrite Hab in H2.
}
apply (sorted_cons_iff Htra) in Hsb.
destruct Hsb as (Hsb & Hbaa).
specialize (Hbaa a) as H2.
assert (H : a ∈ bef ++ a :: aft) by now apply in_or_app; right; left.
specialize (H2 H); clear H.
move Hsa at bottom.
move Hsb at bottom.
destruct (Nat.eq_dec i j) as [Hij| Hij]. {
  subst j.
  rewrite Hb.
  apply Hbaa, nth_In.
  cbn in Hlenb.
  rewrite <- Hlenb in Hilen.
  now apply Nat.succ_lt_mono in Hilen.
}
assert (Hbba : sorted leb (bef ++ b :: aft)). {
  apply (sorted_app_iff Htra) in Hsb.
  apply (sorted_app_iff Htra).
  destruct Hsb as (Hsb & Hsaa & Hba).
  split; [ easy | ].
  apply (sorted_cons_iff Htra) in Hsaa.
  split. {
    apply (sorted_cons_iff Htra) in Hsa.
    apply (sorted_cons_iff Htra).
    split; [ easy | ].
    intros c Hc.
    now apply Hbaa, in_or_app; right; right.
  }
  intros x y Hx Hy.
  destruct Hy as [Hy| Hy]. 2: {
    apply Hba; [ easy | now right ].
  }
  subst y.
  destruct Hsaa as (Hsa' & Hsaa).
  apply (Htra x a b). {
    apply Hba; [ easy | now left ].
  }
  apply (sorted_cons_iff Htra) in Hsa.
  destruct Hsa as (Hsa, Hlab).
  apply Hlab.
  now apply H1; left.
}
destruct (lt_dec i (length bef)) as [Hib| Hib]. {
  rewrite app_nth1; [ | easy ].
  rewrite <- app_nth1 with (l := bef) (l' := b :: aft); [ | easy ].
  apply IHla; [ | easy ].
  eapply (permutation_trans Heqb); [ apply Hpab | ].
  apply (permutation_middle Heqb).
}
apply Nat.nlt_ge in Hib.
rewrite app_nth2; [ | easy ].
destruct (Nat.eq_dec i (length bef)) as [Hib'| Hib']. {
  rewrite <- Hib', Nat.sub_diag; cbn.
  apply (Htra _ b _); [ | easy ].
  replace b with (nth i (bef ++ b :: aft) d). 2: {
    rewrite app_nth2; [ | easy ].
    now rewrite Hib', Nat.sub_diag; cbn.
  }
  apply IHla; [ | easy ].
  eapply (permutation_trans Heqb); [ apply Hpab | ].
  apply (permutation_middle Heqb).
}
replace (i - length bef) with (S (i - S (length bef))) by flia Hib Hib'.
cbn.
replace (nth (i - S (length bef)) aft d) with (nth i (bef ++ b :: aft) d). 2: {
  rewrite app_nth2; [ | easy ].
  now replace (i - length bef) with (S (i - S (length bef))) by flia Hib Hib'.
}
apply IHla; [ | easy ].
eapply (permutation_trans Heqb); [ apply Hpab | ].
apply (permutation_middle Heqb).
Qed.

Theorem sorted_sorted_permuted_not_antisym : ∀ A (eqb leb : A → A → bool),
  equality eqb →
  reflexive leb →
  transitive leb →
  ∀ (d : A) (la lb : list A),
  sorted leb la
  → sorted leb lb
  → permutation eqb la lb
  → ∀ i,
    leb (nth i la d) (nth i lb d) = true ∧
    leb (nth i lb d) (nth i la d) = true.
Proof.
intros * Heqb Href Htra * Hsa Hsb Hpab i.
split. {
  now apply (sorted_sorted_permuted_not_antisym_1 Heqb).
} {
  apply (permutation_sym Heqb) in Hpab.
  now apply (sorted_sorted_permuted_not_antisym_1 Heqb).
}
Qed.

Theorem sorted_sorted_permuted : ∀ A (eqb rel : A → _),
  equality eqb →
  antisymmetric rel →
  transitive rel →
  ∀ la lb,
  sorted rel la
  → sorted rel lb
  → permutation eqb la lb
  → la = lb.
Proof.
intros * Heqb Hant Htra * Hsa Hsb Hpab.
revert lb Hsb Hpab.
induction la as [| a]; intros; [ now apply permutation_nil_l in Hpab | ].
specialize sorted_cons as H.
specialize (H _ rel a la Hsa).
specialize (IHla H); clear H.
destruct lb as [| b]; [ now apply permutation_nil_r in Hpab | ].
apply permutation_cons_l_iff in Hpab.
cbn in Hpab.
remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  apply Heqb in Hab; subst b; f_equal.
  apply IHla; [ | easy ].
  now apply sorted_cons in Hsb.
}
remember (extract (eqb a) lb) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((befa, x), afta)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbefa & H & Hlb).
apply Heqb in H; subst x.
subst lb.
apply (permutation_sym Heqb) in Hpab.
cbn in Hpab.
apply permutation_cons_l_iff in Hpab.
remember (extract (eqb b) la) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((befb, x), aftb)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbefb & H & Hlb).
apply Heqb in H; subst x.
subst la.
move Hab at bottom.
move Hsa at bottom.
move Hsb at bottom.
specialize sorted_middle as H1.
specialize (H1 _ rel Htra _ _ [] _ _ Hsa) as H2.
specialize (H1 _ rel Htra _ _ [] _ _ Hsb) as H3.
specialize (Hant _ _ H2 H3) as H4.
subst b.
now rewrite (equality_refl Heqb) in Hab.
Qed.

Theorem msort_loop_enough_iter : ∀ A (rel : A → _) la ita itb,
  length la ≤ ita
  → length la ≤ itb
  → msort_loop rel ita la = msort_loop rel itb la.
Proof.
intros * Ha Hb.
revert la itb Ha Hb.
induction ita; intros; cbn. {
  apply Nat.le_0_r, length_zero_iff_nil in Ha; subst la.
  symmetry; apply msort_loop_nil.
}
destruct itb; cbn. {
  apply Nat.le_0_r, length_zero_iff_nil in Hb; subst la; cbn.
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

(* unicity of sorting algorithm *)

Theorem sorted_unique : ∀ A (eqb rel : A → A → bool),
  equality eqb →
  reflexive rel →
  antisymmetric rel →
  transitive rel →
  ∀ (sort_algo1 sort_algo2 : list A → _),
  (∀ l, permutation eqb (sort_algo1 l) l ∧ sorted rel (sort_algo1 l))
  → (∀ l, permutation eqb (sort_algo2 l) l ∧ sorted rel (sort_algo2 l))
  → ∀ l, sort_algo1 l = sort_algo2 l.
Proof.
intros * Heqb Href Hant Htra * Hps1 Hps2 l.
specialize (sorted_sorted_permuted Heqb Hant Htra) as H1.
apply H1; [ apply Hps1 | apply Hps2 | clear H1 ].
specialize (Hps1 l) as H1.
specialize (Hps2 l) as H2.
eapply (permutation_trans Heqb); [ apply H1 | ].
now apply (permutation_sym Heqb).
Qed.

(* main *)

Theorem isort_when_sorted : ∀ A (rel : A → _),
  ∀ l, sorted rel l → isort rel l = l.
Proof.
intros * Hs.
induction l as [| a]; [ easy | cbn ].
assert (H : sorted rel l) by now apply sorted_cons in Hs.
specialize (IHl H); clear H.
rewrite IHl; clear IHl.
unfold sorted in Hs; cbn in Hs.
destruct l as [| b]; [ easy | ].
apply Bool.andb_true_iff in Hs.
destruct Hs as (Hab, Hs).
now cbn; rewrite Hab.
Qed.

Theorem ssort_when_sorted : ∀ A (rel : A → _),
  transitive rel →
  ∀ l,
  sorted rel l
  → ssort rel l = l.
Proof.
intros * Htr * Hs.
unfold ssort.
now apply ssort_loop_when_sorted.
Qed.

Theorem bsort_when_sorted : ∀ A (rel : A → _),
  ∀ l,
  sorted rel l
  → bsort rel l = l.
Proof.
intros * Hs.
now apply bsort_loop_when_sorted.
Qed.

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

Theorem sorted_isort : ∀ A (rel : A → _),
  total_relation rel
  → ∀ l, sorted rel (isort rel l).
Proof.
intros * Hto *.
induction l as [| a]; [ easy | cbn ].
now apply sorted_isort_insert.
Qed.

Theorem sorted_ssort : ∀ A (rel : A → _),
  transitive rel →
  total_relation rel →
  ∀ l, sorted rel (ssort rel l).
Proof.
intros * Htr Htot *.
now apply sorted_ssort_loop.
Qed.

Theorem sorted_bsort : ∀ A (rel : A → _),
  total_relation rel →
  ∀ l, sorted rel (bsort rel l).
Proof.
intros * Htot *.
now apply sorted_bsort_loop.
Qed.

Theorem sorted_msort : ∀ A (rel : A → _),
  total_relation rel →
  ∀ l, sorted rel (msort rel l).
Proof.
intros * Htot *.
now apply sorted_msort_loop.
Qed.

(* *)

Theorem sorted_isort_iff : ∀ A (rel : A → A → bool),
  transitive rel →
  total_relation rel →
  ∀ l, sorted rel l ↔ isort rel l = l.
Proof.
intros * Htra Htot *.
split; [ now apply isort_when_sorted | ].
intros Hs.
specialize sorted_isort as H1.
specialize (H1 _ rel Htot l).
now rewrite Hs in H1.
Qed.

Theorem sorted_ssort_iff : ∀ A (rel : A → A → bool),
  transitive rel →
  total_relation rel →
  ∀ l, sorted rel l ↔ ssort rel l = l.
Proof.
intros * Htra Htot *.
split; [ now apply ssort_when_sorted | ].
intros Hs.
specialize sorted_ssort as H1.
specialize (H1 _ rel Htra Htot l).
now rewrite Hs in H1.
Qed.

Theorem sorted_bsort_iff : ∀ A (rel : A → A → bool),
  total_relation rel →
  ∀ l, sorted rel l ↔ bsort rel l = l.
Proof.
intros * Htot *.
split; [ now apply bsort_when_sorted | ].
intros Hs.
specialize sorted_bsort as H1.
specialize (H1 _ rel Htot l).
now rewrite Hs in H1.
Qed.

Theorem sorted_msort_iff : ∀ A (rel : A → A → bool),
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ l, sorted rel l ↔ msort rel l = l.
Proof.
intros * Hant Htra Htot *.
split; [ now apply msort_when_sorted | ].
intros Hs.
specialize (sorted_msort) as H1.
specialize (H1 _ rel Htot l).
now rewrite Hs in H1.
Qed.

(* *)

Theorem permuted_isort : ∀ A (eqb rel : A → _) (Heqb : equality eqb),
  ∀ l, permutation eqb l (isort rel l).
Proof.
intros.
induction l as [| a]; [ apply (permutation_refl Heqb) | cbn ].
now apply permutation_cons_isort_insert.
Qed.

Theorem permuted_ssort : ∀ A (eqb rel : A → _) (Heqb : equality eqb),
  ∀ l, permutation eqb l (ssort rel l).
Proof.
intros.
now apply permuted_ssort_loop.
Qed.

Theorem permuted_bsort : ∀ A (eqb rel : A → _) (Heqb : equality eqb),
  ∀ l, permutation eqb l (bsort rel l).
Proof.
intros.
now apply permuted_bsort_loop.
Qed.

Theorem permuted_msort : ∀ A (eqb rel : A → _) (Heqb : equality eqb),
  ∀ l, permutation eqb l (msort rel l).
Proof.
intros.
now apply permuted_msort_loop.
Qed.

(* *)

Theorem isort_when_permuted : ∀ A (eqb rel : A → _),
  equality eqb →
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ la lb,
  permutation eqb la lb
  → isort rel la = isort rel lb.
Proof.
intros * Heqb Hant Htra Htot * Hpab.
specialize (sorted_isort Htot la) as Hsa.
specialize (sorted_isort Htot lb) as Hsb.
specialize (permuted_isort rel Heqb la) as Hpa.
specialize (permuted_isort rel Heqb lb) as Hpb.
assert (Hsab : permutation eqb (isort rel la) (isort rel lb)). {
  eapply (permutation_trans Heqb); [ | apply Hpb ].
  eapply (permutation_trans Heqb); [ | apply Hpab ].
  now apply (permutation_sym Heqb).
}
now apply (sorted_sorted_permuted Heqb Hant Htra).
Qed.

Theorem ssort_when_permuted : ∀ A (eqb rel : A → _),
  equality eqb →
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ la lb,
  permutation eqb la lb
  → ssort rel la = ssort rel lb.
Proof.
intros * Heqb Hant Htra Htot * Hpab.
specialize (sorted_ssort Htra Htot la) as Hsa.
specialize (sorted_ssort Htra Htot lb) as Hsb.
specialize (permuted_ssort rel Heqb la) as Hpa.
specialize (permuted_ssort rel Heqb lb) as Hpb.
assert (Hsab : permutation eqb (ssort rel la) (ssort rel lb)). {
  eapply (permutation_trans Heqb); [ | apply Hpb ].
  eapply (permutation_trans Heqb); [ | apply Hpab ].
  now apply (permutation_sym Heqb).
}
now apply (sorted_sorted_permuted Heqb Hant Htra).
Qed.

Theorem bsort_when_permuted : ∀ A (eqb rel : A → _),
  equality eqb →
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ la lb,
  permutation eqb la lb
  → bsort rel la = bsort rel lb.
Proof.
intros * Heqb Hant Htra Htot * Hpab.
specialize (sorted_bsort Htot la) as Hsa.
specialize (sorted_bsort Htot lb) as Hsb.
specialize (permuted_bsort rel Heqb la) as Hpa.
specialize (permuted_bsort rel Heqb lb) as Hpb.
assert (Hsab : permutation eqb (bsort rel la) (bsort rel lb)). {
  eapply (permutation_trans Heqb); [ | apply Hpb ].
  eapply (permutation_trans Heqb); [ | apply Hpab ].
  now apply (permutation_sym Heqb).
}
now apply (sorted_sorted_permuted Heqb Hant Htra).
Qed.

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

Theorem permut_if_isort : ∀ A (eqb rel : A → _),
  equality eqb →
  ∀ la lb,
  isort rel la = isort rel lb
  → permutation eqb la lb.
Proof.
intros * Heqb * Hab.
specialize (permuted_isort rel Heqb la) as H1.
specialize (permuted_isort rel Heqb lb) as H2.
apply (permutation_trans Heqb) with (lb := isort rel la); [ easy | ].
rewrite Hab.
now apply permutation_sym.
Qed.

(* *)

Theorem Nat_leb_total_relation : total_relation Nat.leb.
Proof.
intros i j.
apply Bool.orb_true_iff.
destruct (le_dec i j) as [Hij| Hij]. {
  now apply Nat.leb_le in Hij; rewrite Hij; left.
} {
  apply Nat.nle_gt, Nat.lt_le_incl in Hij.
  now apply Nat.leb_le in Hij; rewrite Hij; right.
}
Qed.

Theorem Nat_leb_antisym : antisymmetric Nat.leb.
Proof.
intros a b Hab Hba.
apply Nat.leb_le in Hab, Hba.
now apply le_antisym.
Qed.

Theorem Nat_leb_trans : transitive Nat.leb.
Proof.
intros a b c Hab Hbc.
apply Nat.leb_le in Hab, Hbc.
apply Nat.leb_le.
now transitivity b.
Qed.

Theorem Nat_ltb_antisym : antisymmetric Nat.ltb.
Proof.
intros a b Hab Hba.
apply Nat.ltb_lt in Hab, Hba.
apply (Nat.lt_trans b) in Hab; [ | easy ].
now apply Nat.lt_irrefl in Hab.
Qed.

Theorem Nat_ltb_trans : transitive Nat.ltb.
Proof.
intros a b c Hab Hbc.
apply Nat.ltb_lt in Hab, Hbc.
apply Nat.ltb_lt.
now transitivity b.
Qed.

Theorem Nat_ltb_connected : connected_relation Nat.ltb.
Proof.
intros a b Hab Hba.
apply Nat.ltb_ge in Hab, Hba.
now apply Nat.le_antisymm.
Qed.

(* isort and ssort return same *)

Theorem isort_ssort : ∀ (A : Type) (eqb : A → _) (rel : A → A → bool),
  equality eqb →
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ l, isort rel l = ssort rel l.
Proof.
intros * Heqb Hant Htra Htot *.
specialize (total_relation_is_reflexive Htot) as Href.
apply (sorted_unique Heqb Href Hant Htra). {
  clear l; intros l.
  split; [ | now apply sorted_isort ].
  apply (permutation_sym Heqb).
  now apply permuted_isort.
} {
  clear l; intros l.
  split; [ | now apply sorted_ssort ].
  apply (permutation_sym Heqb).
  now apply permuted_ssort.
}
Qed.

(* ssort and bsort return same *)

Theorem ssort_bsort : ∀ A (eqb : A → _) (rel : A → A → bool),
  equality eqb →
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ l, ssort rel l = bsort rel l.
Proof.
intros * Heqb Hant Htra Htot *.
specialize (total_relation_is_reflexive Htot) as Href.
apply (sorted_unique Heqb Href Hant Htra). {
  clear l; intros l.
  split; [ | now apply sorted_ssort ].
  now apply permutation_sym, permuted_ssort.
} {
  clear l; intros l.
  split; [ | now apply sorted_bsort ].
  now apply permutation_sym, permuted_bsort.
}

(* bsort and isort return same *)

Theorem bsort_isort : ∀ A (eqb : A → _) (rel : A → A → bool),
  equality eqb →
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ l, bsort rel l = isort rel l.
Proof.
intros * Heqb Hant Htra Htot *.
specialize (total_relation_is_reflexive Htot) as Href.
apply (sorted_unique Heqb Href Hant Htra). {
  clear l; intros l.
  split; [ | now apply sorted_bsort ].
  now apply permutation_sym, permuted_bsort.
} {
  clear l; intros l.
  split; [ | now apply sorted_isort ].
  now apply permutation_sym, permuted_isort.
}
Qed.

(* *)

Theorem sorted_seq : ∀ sta len, sorted Nat.ltb (seq sta len).
Proof.
intros.
revert sta.
induction len; intros; [ easy | cbn ].
apply sorted_cons_iff; [ apply Nat_ltb_trans | ].
split; [ apply IHlen | ].
intros a Ha.
apply in_seq in Ha.
now apply Nat.ltb_lt.
Qed.

Theorem antisymmetric_list_leb : ∀ A (leb : A → _),
  antisymmetric leb → antisymmetric (list_leb leb).
Proof.
intros * Hant.
intros la lb Hlab Hlba.
revert lb Hlab Hlba.
induction la as [| a]; intros; [ now destruct lb | ].
destruct lb as [| b]; [ easy | ].
cbn in Hlab, Hlba.
remember (leb a b) as ab eqn:Hab; symmetry in Hab.
remember (leb b a) as ba eqn:Hba; symmetry in Hba.
destruct ab; [ | easy ].
destruct ba; [ | easy ].
rewrite (Hant _ _ Hab Hba); f_equal.
now apply IHla.
Qed.

Theorem transitive_list_leb : ∀ A (leb : A → _),
  transitive leb → transitive (list_leb leb).
Proof.
intros * Htra.
intros la lb lc Hlab Hlbc.
revert lb lc Hlab Hlbc.
induction la as [| a]; intros; [ now destruct lb | ].
destruct lb as [| b]; [ easy | ].
destruct lc as [| c]; [ easy | ].
cbn in Hlab, Hlbc |-*.
remember (leb a b) as ab eqn:Hab; symmetry in Hab.
remember (leb b a) as ba eqn:Hba; symmetry in Hba.
remember (leb b c) as bc eqn:Hbc; symmetry in Hbc.
remember (leb c b) as cb eqn:Hcb; symmetry in Hcb.
destruct ab; [ | easy ].
destruct bc; [ | easy ].
rewrite (Htra _ _ _ Hab Hbc).
destruct ba. {
  destruct cb. {
    rewrite (Htra _ _ _ Hcb Hba).
    now apply (IHla lb).
  }
  remember (leb c a) as ca eqn:Hca; symmetry in Hca.
  destruct ca; [ | easy ].
  now rewrite (Htra c a b Hca Hab) in Hcb.
} {
  remember (leb c a) as ca eqn:Hca; symmetry in Hca.
  destruct ca; [ | easy ].
  destruct cb; [ now rewrite (Htra b c a Hbc Hca) in Hba | ].
  now rewrite (Htra _ _ _ Hca Hab) in Hcb.
}
Qed.

Theorem total_relation_list_leb : ∀ A (leb : A → _),
  total_relation leb → total_relation (list_leb leb).
Proof.
intros * Htot.
intros la lb.
revert lb.
induction la as [| a]; intros; [ easy | ].
destruct lb as [| b]; [ easy | cbn ].
specialize (Htot a b).
remember (leb a b) as ab eqn:Hab; symmetry in Hab.
remember (leb b a) as ba eqn:Hba; symmetry in Hba.
destruct ab; [ | now destruct ba ].
destruct ba; [ | easy ].
apply IHla.
Qed.

Theorem transitive_list_ltb : ∀ A (ltb : A → _),
  antisymmetric ltb
  → connected_relation ltb
  → transitive ltb
  → transitive (list_ltb ltb).
Proof.
intros * Hant Hcon Htra.
intros la lb lc Hlab Hlbc.
revert la lb Hlab Hlbc.
induction lc as [| c]; intros; [ now destruct lb | ].
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | ].
cbn in Hlab, Hlbc |-*.
remember (ltb a c) as ac eqn:Hac; symmetry in Hac.
remember (ltb c a) as ca eqn:Hca; symmetry in Hca.
destruct ac; [ easy | ].
remember (ltb a b) as ab eqn:Hab; symmetry in Hab.
remember (ltb b a) as ba eqn:Hba; symmetry in Hba.
remember (ltb b c) as bc eqn:Hbc; symmetry in Hbc.
remember (ltb c b) as cb eqn:Hcb; symmetry in Hcb.
move ba before ab; move bc before ba; move cb before bc.
move ca before cb.
destruct ab. 2: {
  destruct ba; [ easy | ].
  specialize (Hcon _ _ Hab Hba) as H; subst a.
  destruct bc; [ congruence | ].
  destruct cb; [ easy | ].
  destruct ca; [ | now apply (IHlc _ lb) ].
  specialize (Hcon _ _ Hbc Hcb) as H; subst c.
  congruence.
}
destruct ca. 2: {
  specialize (Hcon _ _ Hac Hca) as H; subst c.
  destruct bc. {
    clear Hlab Hlbc.
    specialize (Hant a b Hab Hbc) as H1; subst a.
    congruence.
  }
  destruct cb; [ easy | congruence ].
}
destruct bc. {
  specialize (Htra a b c Hab Hbc) as H1.
  congruence.
}
destruct cb; [ easy | ].
specialize (Hcon b c Hbc Hcb) as H1; subst c.
congruence.
Qed.

Theorem sorted_sorted_map_cons : ∀ A (ltb : A → _),
  antisymmetric ltb →
  transitive ltb →
  connected_relation ltb →
  ∀ ll a,
  sorted (list_ltb ltb) ll → sorted (list_ltb ltb) (map (cons a) ll).
Proof.
intros * Hant Htra Hcon * Hs.
induction ll as [| la]; [ easy | cbn ].
apply sorted_cons_iff in Hs; [ | now apply transitive_list_ltb ].
destruct Hs as (Hs, Hlab).
apply sorted_cons_iff; [ now apply transitive_list_ltb | ].
split; [ now apply IHll | ].
intros lb Hlb; cbn.
destruct lb as [| b]. {
  clear IHll Hs Hlab.
  induction ll as [| lb]; [ easy | ].
  cbn in Hlb.
  destruct Hlb as [Hlb| Hlb]; [ easy | ].
  now apply IHll.
}
remember (ltb a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ easy | ].
remember (ltb b a) as ba eqn:Hba; symmetry in Hba.
apply in_map_iff in Hlb.
destruct Hlb as (lc & Hll & Hlb).
injection Hll; clear Hll; intros; subst b lc.
destruct ba; [ congruence | ].
now apply Hlab.
Qed.

(* *)

Theorem sorted_concat_iff : ∀ A (rel : A → _),
  transitive rel →
  ∀ ll,
  sorted rel (concat ll) ↔
    (∀ l, l ∈ ll → sorted rel l) ∧
    (∀ i j, i < j < length ll →
     ∀ a b, a ∈ nth i ll [] → b ∈ nth j ll [] → rel a b = true).
Proof.
intros * Htra *.
split. {
  intros Hs.
  split. {
    intros la Hla.
    induction ll as [| lb]; [ easy | ].
    cbn in Hs.
    apply sorted_app_iff in Hs; [ | easy ].
    destruct Hla as [Hla| Hla]; [ now subst lb | ].
    now apply IHll.
  }
  intros i j Hij a b Ha Hb.
  revert i j a b Hij Ha Hb.
  induction ll as [| la]; intros; [ easy | ].
  assert (H : sorted rel (concat ll)). {
    now cbn in Hs; apply sorted_app_iff in Hs; [ | easy ].
  }
  specialize (IHll H); clear H.
  cbn in Ha, Hb.
  destruct j; [ easy | ].
  destruct i. {
    cbn in Hs.
    apply sorted_app_iff in Hs; [ | easy ].
    destruct Hs as (Hla & Hs & Hab).
    apply Hab; [ easy | ].
    apply in_concat.
    exists (nth j ll []).
    split; [ | easy ].
    apply nth_In.
    destruct Hij as (_, Hj); cbn in Hj.
    now apply Nat.succ_lt_mono in Hj.
  }
  apply (IHll i j); [ | easy | easy ].
  destruct Hij as (Hi, Hj); cbn in Hj.
  now apply Nat.succ_lt_mono in Hi, Hj.
}
intros (Hs & Hleb).
induction ll as [| la]; [ easy | cbn ].
apply sorted_app_iff; [ easy | ].
split; [ now apply Hs; left | ].
split. {
  apply IHll. {
    now intros lb Hlb; apply Hs; right.
  } {
    intros i j Hij a b Ha Hb.
    apply (Hleb (S i) (S j)); [ | easy | easy ].
    now split; apply -> Nat.succ_lt_mono.
  }
}
intros a b Ha Hb.
apply in_concat in Hb.
destruct Hb as (lb & Hlb & Hb).
apply (In_nth _ _ []) in Hlb.
destruct Hlb as (j & Hjl & Hlb).
apply (Hleb 0 (S j)); [ | easy | now cbn; rewrite Hlb ].
split; [ easy | cbn ].
now apply -> Nat.succ_lt_mono.
Qed.

Theorem cart_prod_repeat_seq_ltb_sorted : ∀ i n m,
  sorted (list_ltb Nat.ltb) (cart_prod (repeat (seq i n) m)).
Proof.
intros.
revert i n.
induction m; intros; [ easy | cbn ].
rewrite flat_map_concat_map.
specialize Nat_ltb_antisym as Hant.
specialize Nat_ltb_connected as Hcon.
specialize Nat_ltb_trans as Htra.
apply sorted_concat_iff; [ now apply transitive_list_ltb | ].
rewrite List_map_seq_length.
split. {
  intros ll Hll.
  apply in_map_iff in Hll.
  destruct Hll as (a & Hll & Ha); subst ll.
  apply sorted_sorted_map_cons; [ easy | easy | easy | apply IHm ].
}
intros j k Hjk la lb Ha Hb.
rewrite (List_map_nth' 0) in Ha; [ | rewrite seq_length; flia Hjk ].
rewrite (List_map_nth' 0) in Hb; [ | rewrite seq_length; easy ].
apply in_map_iff in Ha, Hb.
destruct Ha as (lc & Hc & Hlc).
destruct Hb as (ld & Hd & Hld).
move ld before lc.
subst la lb; cbn.
unfold "<?"; cbn.
rename lc into la; rename ld into lb.
remember (nth k (seq i n) 0) as a eqn:Ha; symmetry in Ha.
remember (nth j (seq i n) 0) as b eqn:Hb; symmetry in Hb.
rewrite seq_nth in Ha; [ | easy ].
rewrite seq_nth in Hb; [ | flia Hjk ].
subst a b.
destruct k; [ easy | ].
rewrite Nat.add_comm; cbn.
rewrite if_leb_le_dec.
destruct (le_dec (i + j) (k + i)) as [H| H]; [ easy | flia Hjk H].
Qed.

Theorem list_ltb_leb_incl : ∀ la lb,
  list_ltb Nat.ltb la lb = true
  → list_leb Nat.leb la lb = true.
Proof.
intros * Hlab.
revert lb Hlab.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | ].
cbn in Hlab.
unfold "<?" in Hlab; cbn in Hlab.
destruct b. {
  destruct a; [ now apply IHla | easy ].
}
rewrite if_leb_le_dec in Hlab.
destruct (le_dec a b) as [Hab| Hab]. {
  do 2 rewrite if_leb_le_dec.
  destruct (le_dec a (S b)) as [H| H]; [ clear H | flia Hab H ].
  destruct (le_dec (S b) a) as [H| H]; [ flia Hab H | easy ].
}
destruct a; [ easy | cbn ].
apply Nat.nle_gt in Hab.
rewrite if_leb_le_dec in Hlab.
destruct (le_dec (S b) a) as [Hsba| Hsba]; [ easy | ].
apply Nat.nle_gt in Hsba.
replace b with a by flia Hab Hsba.
rewrite Nat.leb_refl.
now apply IHla.
Qed.

Theorem sorted_list_ltb_leb_incl : ∀ lla,
  sorted (list_ltb Nat.ltb) lla → sorted (list_leb Nat.leb) lla.
Proof.
intros * Hs.
assert (Htralt : transitive (list_ltb Nat.ltb)). {
  apply transitive_list_ltb. {
    apply Nat_ltb_antisym.
  } {
    apply Nat_ltb_connected.
  } {
    apply Nat_ltb_trans.
  }
}
assert (Htrale : transitive (list_leb Nat.leb)). {
  apply transitive_list_leb, Nat_leb_trans.
}
specialize Nat_ltb_trans as Htra.
induction lla as [| la]; [ easy | ].
apply sorted_cons_iff in Hs; [ | easy ].
apply sorted_cons_iff; [ easy | ].
destruct Hs as (Hs, Hab).
split; [ now apply IHlla | ].
intros lb Hlb.
apply list_ltb_leb_incl.
now apply Hab.
Qed.

Theorem NoDup_sorted_nat_leb_ltb : ∀ l,
  NoDup l → sorted Nat.leb l → sorted Nat.ltb l.
Proof.
intros * Hns Hs.
induction l as [| a]; [ easy | cbn ].
assert (H : NoDup l) by now apply NoDup_cons_iff in Hns.
specialize (IHl H); clear H.
assert (H : sorted Nat.leb l). {
  apply sorted_cons_iff in Hs; [ easy | apply Nat_leb_trans ].
}
specialize (IHl H); clear H.
apply sorted_cons_iff; [ apply Nat_ltb_trans | ].
split; [ easy | ].
intros b Hb.
apply Nat.ltb_lt.
apply NoDup_cons_iff in Hns.
destruct Hns as (Hal, Hnd).
apply sorted_cons_iff in Hs; [ | apply Nat_leb_trans ].
destruct Hs as (Hs & Hab).
specialize (Hab _ Hb) as H1.
apply Nat.leb_le in H1.
destruct (Nat.eq_dec a b) as [H| H]; [ now subst b | ].
flia H1 H.
Qed.

Theorem sorted_cons_isort_insert : ∀ A (rel : A → _),
  transitive rel →
  ∀ a lsorted,
  sorted rel (a :: lsorted)
  → isort_insert rel a lsorted = a :: lsorted.
Proof.
intros * Htran * Hs.
revert a Hs.
induction lsorted as [| b]; intros; [ easy | cbn ].
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ easy | ].
apply sorted_cons_iff in Hs; [ | easy ].
destruct Hs as (Hs & Habs).
specialize (Habs _ (or_introl eq_refl)).
congruence.
Qed.

Theorem isort_insert_sorted_cons : ∀ A (rel : A → _),
  transitive rel
  → ∀ a la lb,
  sorted rel la
  → isort_insert rel a la = a :: lb
  → la = lb.
Proof.
intros * Htra * Hs His.
destruct la as [| b]. {
  injection His; clear His; intros; subst lb.
  easy.
}
cbn in His.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  now injection His; clear His; intros; subst lb.
} {
  injection His; clear His; intros; subst b lb.
  now symmetry; apply sorted_cons_isort_insert.
}
Qed.

Theorem isort_insert_sorted_cons2 : ∀ A (rel : A → _),
  transitive rel
  → ∀ a b la lb,
  sorted rel la
  → isort_insert rel a la = b :: a :: lb
  → la = b :: lb.
Proof.
intros * Htra * Hs His.
destruct la as [| c]; [ easy | ].
cbn in His.
remember (rel a c) as ac eqn:Hac; symmetry in Hac.
destruct ac. {
  now injection His; clear His; intros; subst b c lb.
} {
  injection His; clear His; intros His H; subst c.
  f_equal.
  apply sorted_cons in Hs.
  now apply isort_insert_sorted_cons in His.
}
Qed.

Theorem neq_isort_insert_nil : ∀ A rel a (la : list A),
  isort_insert rel a la ≠ [].
Proof.
intros.
destruct la as [| b]; [ easy | cbn ].
now destruct (rel a b).
Qed.

Theorem eq_isort_nil : ∀ A rel (la : list A), isort rel la = [] → la = [].
Proof.
intros * Hla.
destruct la as [| a]; [ easy | exfalso ].
cbn in Hla; revert Hla.
apply neq_isort_insert_nil.
Qed.

Theorem eq_isort_insert_unit : ∀ A rel a b (la : list A),
  isort_insert rel a la = [b] → a = b ∧ la = [].
Proof.
intros * Hab.
destruct la as [| c]; cbn. {
  cbn in Hab.
  now injection Hab; clear Hab; intros; subst b.
}
cbn in Hab.
destruct (rel a c); [ easy | ].
injection Hab; clear Hab; intros Hab H; subst c.
exfalso; revert Hab.
apply neq_isort_insert_nil.
Qed.

Theorem eq_isort_unit : ∀ A rel a (la : list A),
  isort rel la = [a] → la = [a].
Proof.
intros * Hla.
destruct la as [| b]; [ easy | ].
cbn in Hla.
apply eq_isort_insert_unit in Hla.
destruct Hla as (Hab, Hla); subst b.
now apply eq_isort_nil in Hla; subst la.
Qed.

Theorem eq_isort_insert_cons_iff : ∀ A (rel : A → _),
  reflexive rel →
  ∀ a b la lb,
  isort_insert rel a la = b :: lb
  ↔ a = b ∧ la = lb ∧ rel a (hd a la) = true ∨
    rel a b = false ∧ hd a la = b ∧ isort_insert rel a (tl la) = lb.
Proof.
intros * Href *.
split; intros Hs. {
  destruct la as [| c]. {
    cbn in Hs.
    injection Hs; clear Hs; intros; subst b lb; left.
    split; [ easy | ].
    split; [ easy | ].
    apply Href.
  }
  cbn in Hs.
  rewrite if_bool_if_dec in Hs.
  destruct (Sumbool.sumbool_of_bool (rel a c)) as [Hac| Hac]. {
    injection Hs; clear Hs; intros; subst b lb; left.
    split; [ easy | ].
    split; [ easy | ].
    now cbn; rewrite Hac.
  }
  now injection Hs; clear Hs; intros; subst c; right.
} {
  destruct Hs as [(Hab & Hlab & Hs)| (Hab & Hla & Hs)]. {
    subst b lb.
    destruct la as [| b]; [ easy | ].
    cbn in Hs |-*.
    now rewrite Hs.
  }
  destruct la as [| c]. {
    cbn in Hla; subst b.
    now rewrite Href in Hab.
  }
  cbn in Hla, Hs |-*; subst c.
  now rewrite Hab; subst lb.
}
Qed.

Theorem eq_isort_cons_iff : ∀ A (rel : A → _),
  reflexive rel →
  ∀ a la lb,
  isort rel la = a :: lb
  ↔ la ≠ [] ∧
    (hd a la = a ∧ isort rel (tl la) = lb ∧
       rel (hd a la) (hd a lb) = true ∨
     rel (hd a la) a = false ∧ hd a (isort rel (tl la)) = a ∧
       isort_insert rel (hd a la) (tl (isort rel (tl la))) = lb ∧
       tl la ≠ []).
Proof.
intros * Href *.
split; intros Hs. {
  destruct la as [| b]; [ easy | cbn ].
  split; [ easy | ].
  cbn in Hs.
  apply (eq_isort_insert_cons_iff Href) in Hs.
  destruct Hs as [(H1 & H2 & H3)| (H1 & H2 & H3)]. {
    left; subst b.
    split; [ easy | ].
    split; [ easy | ].
    now rewrite H2 in H3.
  } {
    right.
    split; [ easy | ].
    split; [ now destruct (isort rel la) | ].
    split; [ easy | ].
    destruct la as [| c]; [ | easy ].
    cbn in H2; subst b.
    now rewrite Href in H1.
  }
} {
  destruct Hs as (Hlaz, Hs).
  destruct Hs as [(H1 & H2 & H3)| (H1 & H2 & H3 & H4)]. {
    destruct la as [| b]; [ easy | clear Hlaz ].
    cbn in H1, H2, H3 |-*; subst b.
    rewrite H2.
    destruct lb as [| b]; [ easy | ].
    cbn in H3 |-*.
    now rewrite H3.
  } {
    destruct la as [| b]; [ easy | clear Hlaz ].
    cbn in H1, H2, H3, H4 |-*.
    apply (eq_isort_insert_cons_iff Href).
    right.
    split; [ easy | ].
    split; [ | easy ].
    destruct la as [| c]; [ easy | clear H4 ].
    cbn in H2, H3 |-*.
    remember (isort_insert rel c (isort rel la)) as lc eqn:Hlc.
    symmetry in Hlc.
    destruct lc as [| d]. {
      now apply neq_isort_insert_nil in Hlc.
    }
    now cbn in H2 |-*.
  }
}
Qed.

Theorem sorted_filter : ∀ A (rel : A → _),
  transitive rel →
  ∀ l f,
  sorted rel l → sorted rel (filter f l).
Proof.
intros * Htra * Hs.
induction l as [| a]; [ easy | cbn ].
remember (f a) as fa eqn:Hfa; symmetry in Hfa.
destruct fa. {
  apply sorted_cons_iff; [ easy | ].
  apply sorted_cons_iff in Hs; [ | easy ].
  destruct Hs as (Hs & Hr).
  split; [ now apply IHl | ].
  intros b Hb.
  apply filter_In in Hb.
  now apply Hr.
}
apply sorted_cons in Hs.
now apply IHl.
Qed.

Theorem sorted_isort_insert_filter : ∀ A (rel : A → _),
  transitive rel →
  ∀ f a la,
  sorted rel la
  → filter f (isort_insert rel a la) =
     if f a then isort_insert rel a (filter f la)
     else filter f la.
Proof.
intros * Htra * Hla.
revert a.
induction la as [| b]; intros; cbn; [ easy | ].
assert (H : sorted rel la) by now apply sorted_cons in Hla.
specialize (IHla H); clear H.
remember (f a) as fa eqn:Hfa; symmetry in Hfa.
remember (f b) as fb eqn:Hfb; symmetry in Hfb.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  cbn; rewrite Hfa, Hfb.
  destruct fa; [ | easy ].
  destruct fb; cbn; [ now rewrite Hab | ].
  specialize (IHla a) as H1.
  rewrite Hfa in H1.
  rewrite <- H1.
  destruct la as [| c]; [ easy | cbn ].
  remember (f c) as fc eqn:Hfc; symmetry in Hfc.
  remember (rel a c) as ac eqn:Hac; symmetry in Hac.
  destruct fc; cbn. {
    destruct ac; cbn; rewrite Hfc; [ now rewrite Hfa | ].
    apply (sorted_cons_iff Htra) in Hla.
    destruct Hla as (Hsca, Hcla).
    specialize (Hcla _ (or_introl eq_refl)) as Hbc.
    now rewrite (Htra a b c Hab Hbc) in Hac.
  }
  destruct ac; cbn; rewrite Hfc; [ now rewrite Hfa | ].
  apply (sorted_cons_iff Htra) in Hla.
  destruct Hla as (Hsca, Hcla).
  specialize (Hcla _ (or_introl eq_refl)) as Hbc.
  now rewrite (Htra a b c Hab Hbc) in Hac.
}
cbn; rewrite Hfb.
destruct fa. {
  destruct fb. {
    cbn; rewrite Hab; f_equal.
    now rewrite IHla, Hfa.
  }
  now rewrite IHla, Hfa.
}
now destruct fb; rewrite IHla, Hfa.
Qed.

Theorem sorted_isort_filter : ∀ A (rel : A → _),
  transitive rel →
  total_relation rel →
  ∀ f la, isort rel (filter f la) = filter f (isort rel la).
Proof.
intros * Htra Htot *.
induction la as [| a]; [ easy | cbn ].
remember (f a) as fa eqn:Hfa; symmetry in Hfa.
destruct fa; cbn. {
  rewrite IHla.
  rewrite (sorted_isort_insert_filter Htra); [ now rewrite Hfa | ].
  now apply sorted_isort.
}
rewrite IHla.
rewrite (sorted_isort_insert_filter Htra); [ now rewrite Hfa | ].
now apply sorted_isort.
Qed.

Theorem sorted_map : ∀ A B (rel : A → _),
  transitive rel →
  ∀ la (f : B → A),
  sorted (λ a b, rel (f a) (f b)) la → sorted rel (map f la).
Proof.
intros * Htra * Hs.
induction la as [| a]; [ easy | cbn ].
apply sorted_cons_iff; [ easy | ].
split. {
  apply IHla.
  apply sorted_cons_iff in Hs; [ easy | ].
  intros x y z Hxy Hyz.
  now apply (Htra (f x) (f y) (f z)).
}
intros b Hb.
apply in_map_iff in Hb.
destruct Hb as (c & Hb & Hc); subst b.
apply sorted_cons_iff in Hs. 2: {
  intros x y z Hxy Hyz.
  now apply (Htra (f x) (f y) (f z)).
}
now apply Hs.
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

Theorem permutation_app_merge : ∀ A (eqb rel : A → _),
  equality eqb →
  ∀ la lb,
  permutation eqb (la ++ lb) (merge rel la lb).
Proof.
intros * Heqb *.
revert la.
induction lb as [| b]; intros. {
  rewrite app_nil_r, merge_nil_r.
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
rewrite app_assoc.
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
