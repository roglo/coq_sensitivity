(* Sorted by relation functions *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Permutation.
Import List List.ListNotations.

Require Import Misc.

(* relation properties *)

Definition reflexive A (rel : A → A → bool) :=
  ∀ a, rel a a = true.

Definition antisymmetric A (rel : A → A → bool) :=
  ∀ a b, rel a b = true → rel b a = true → a = b.

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

Fixpoint sorted {A} (rel : A → A → bool) l :=
  match l with
  | [] => true
  | [a] => true
  | a :: (b :: _) as la => (rel a b && sorted rel la)%bool
  end.

Fixpoint all_sorted A (rel : A → A → bool) a l :=
  match l with
  | [] => true
  | b :: l' => (rel a b && all_sorted rel a l')%bool
  end.

Fixpoint strongly_sorted A (rel : A → A → bool) l :=
  match l with
  | [] => true
  | a :: l' => (all_sorted rel a l' && strongly_sorted rel l')%bool
  end.

Theorem sorted_cons : ∀ A (rel : A → _) a la,
  sorted rel (a :: la) = true → sorted rel la = true.
Proof.
intros * Hs.
cbn in Hs.
destruct la as [| a']; [ easy | ].
now apply Bool.andb_true_iff in Hs.
Qed.

Theorem sorted_strongly_sorted : ∀ A (rel : A → A → bool),
  transitive rel →
  ∀ l, sorted rel l = true → strongly_sorted rel l = true.
Proof.
intros * Htra * Hs.
induction l as [| a]; [ easy | cbn ].
rewrite IHl; [ | now apply sorted_cons in Hs ].
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
  ∀ l, strongly_sorted rel l = true → sorted rel l = true.
Proof.
intros * Hs.
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

Theorem sorted_cons_cons_true_iff : ∀ A (rel : A → A -> bool) a b l,
  sorted rel (a :: b :: l) = true
  ↔ rel a b = true ∧ sorted rel (b :: l) = true.
Proof.
intros.
apply Bool.andb_true_iff.
Qed.

Theorem sorted_extends : ∀ A (rel : A → _),
  transitive rel →
  ∀ a l,
  sorted rel (a :: l) = true
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

Theorem sorted_app : ∀ A rel (la lb : list A),
  sorted rel (la ++ lb) = true
  → sorted rel la = true ∧ sorted rel lb = true ∧
    (transitive rel → ∀ a b, a ∈ la → b ∈ lb → rel a b = true).
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

Theorem sorted_trans : ∀ A (rel : A → _),
  transitive rel →
  ∀ a b la,
  sorted rel (a :: la ++ [b]) = true →
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
  sorted rel (a :: la ++ [a]) = true
  → la = repeat a (length la).
Proof.
intros * Hant Htra * Hs.
revert a Hs.
induction la as [| b]; intros; [ easy | cbn ].
remember (b :: la) as lb; cbn in Hs; subst lb.
rewrite <- app_comm_cons in Hs.
apply Bool.andb_true_iff in Hs.
destruct Hs as (Hab, Hs).
specialize (sorted_trans Htra _ _ _ Hs) as Hba.
specialize (Hant a b Hab Hba) as H1; subst b.
f_equal.
now apply IHla.
Qed.

(* isort: sort by insertion *)

Fixpoint isort_insert {A} (rel : A → A → bool) a lsorted :=
  match lsorted with
  | [] => [a]
  | b :: l =>
      if rel a b then a :: lsorted
      else b :: isort_insert rel a l
  end.

Fixpoint isort_loop {A} (rel : A → A → bool) lsorted l :=
  match l with
  | [] => lsorted
  | a :: l' => isort_loop rel (isort_insert rel a lsorted) l'
  end.

Definition isort {A} (rel : A → A → bool) := isort_loop rel [].

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

(*
Compute (bsort Nat.leb [7;5;3;22;8]).
Definition succ_when_ge k a := a + Nat.b2n (k <=? a).
Fixpoint canon_sym_gr_list n k : list nat :=
  match n with
  | 0 => []
  | S n' =>
      k / n'! ::
      map (succ_when_ge (k / n'!)) (canon_sym_gr_list n' (k mod n'!))
  end.
Definition canon_sym_gr_list_list n : list (list nat) :=
  map (canon_sym_gr_list n) (seq 0 n!).
Compute (map (λ l, bsort Nat.leb l) (canon_sym_gr_list_list 5)).
*)

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

Fixpoint split {A} (la : list A) :=
  match la with
  | [] | [_] => (la, [])
  | a :: b :: lb =>
      let (l1, l2) := split lb in
      (a :: l1, b :: l2)
  end.

Fixpoint split2 {A} (la : list A) :=
  match la with
  | [] | [_] => ([], la)
  | a :: b :: lb =>
      let (l1, l2) := split2 lb in
      (a :: l1, b :: l2)
  end.

Fixpoint msort_loop {A} (rel : A → A → bool) it la :=
  match it with
  | 0 => la
  | S it' =>
      let (l1, l2) := split la in
      let l3 := msort_loop rel it' l1 in
      let l4 := msort_loop rel it' l2 in
      msort_loop rel it' (merge rel l3 l4)
  end.

Definition msort {A} (rel : A → _) la :=
  msort_loop rel (length la) la.

Fixpoint msort_loop2 {A} (rel : A → A → bool) it la :=
  match it with
  | 0 => la
  | S it' =>
      let (l1, l2) := split2 la in
      let l3 := msort_loop2 rel it' l1 in
      let l4 := msort_loop2 rel it' l2 in
      msort_loop2 rel it' (merge rel l3 l4)
  end.

Definition msort2 {A} (rel : A → _) la :=
  msort_loop2 rel (length la) la.

(*
Compute (msort Nat.leb [7;5;3;22;8]).
Compute (msort2 Nat.leb [7;5;3;22;8]).
Definition succ_when_ge k a := a + Nat.b2n (k <=? a).
Fixpoint canon_sym_gr_list n k : list nat :=
  match n with
  | 0 => []
  | S n' =>
      k / n'! ::
      map (succ_when_ge (k / n'!)) (canon_sym_gr_list n' (k mod n'!))
  end.
Definition canon_sym_gr_list_list n : list (list nat) :=
  map (canon_sym_gr_list n) (seq 0 n!).
Compute (map (λ l, msort Nat.leb l) (canon_sym_gr_list_list 4)).
Compute (map (λ l, msort2 Nat.leb l) (canon_sym_gr_list_list 4)).
*)

Theorem split_nil_l : ∀ A (la lb : list A),
  split la = ([], lb) → la = [] ∧ lb = [].
Proof.
intros * Hab.
destruct la as [| a]; cbn in Hab |-*. {
  now injection Hab; clear Hab; intros; subst lb.
}
exfalso.
destruct la as [| b]; [ easy | ].
now destruct (split la).
Qed.

Theorem split_nil_r : ∀ A (la lb : list A),
  split la = (lb, []) → la = lb ∧ length la ≤ 1.
Proof.
intros * Hab.
destruct la as [| a]; cbn in Hab |-*. {
  now injection Hab; clear Hab; intros; subst lb.
}
destruct la as [| b]. {
  now injection Hab; clear Hab; intros; subst lb.
}
now destruct (split la).
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

Theorem split_length : ∀ A la (lb lc : list A),
  split la = (lb, lc)
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
remember (split la) as ll eqn:Hll; symmetry in Hll.
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
remember (split la) as ll eqn:Hll; symmetry in Hll.
destruct ll as (lb, lc).
rewrite IHit.
rewrite merge_length.
rewrite app_length.
do 2 rewrite IHit.
now symmetry; apply split_length.
Qed.

Theorem msort_loop_nil : ∀ A (rel : A → _) it,
  msort_loop rel it [] = [].
Proof.
intros.
induction it; [ easy | cbn ].
now rewrite IHit; cbn.
Qed.

Theorem msort_loop_single : ∀ A (rel : A → _) it a,
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
do 2 rewrite msort_loop_single; cbn.
now rewrite Hab.
Qed.

Theorem split_cons_cons : ∀ A (l la lb : list A) a b,
  split l = (a :: la, b :: lb)
  → ∃ l', split l' = (la, lb) ∧ l = a :: b :: l'.
Proof.
intros * Hs.
destruct l as [| c]; [ easy | ].
destruct l as [| d]; [ easy | ].
cbn in Hs.
remember (split l) as l' eqn:Hl'; symmetry in Hl'.
destruct l' as (lc, ld).
injection Hs; clear Hs; intros; subst lc ld c d.
now exists l.
Qed.

Theorem sorted_cons_cons_split : ∀ A (rel : A → _),
  transitive rel →
  ∀ a b la lb l,
  sorted rel (a :: b :: l) = true
  → split l = (la, lb)
  → sorted rel (a :: la) = true ∧ sorted rel (b :: lb) = true.
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
remember (split l) as lc eqn:Hlc; symmetry in Hlc.
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
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
destruct ab; [ rewrite Bool.andb_true_l in Hs | easy ].
destruct bc; [ rewrite Bool.andb_true_l in Hs | easy ].
rewrite (Htra a b c Hab Hbc), Bool.andb_true_l.
assert (H : sorted rel (a :: b :: l) = true). {
  remember (b :: l) as l'; cbn; subst l'.
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

Theorem fold_merge : ∀ A (rel : A → _) la lb,
  merge_loop rel (length la + length lb) la lb = merge rel la lb.
Proof. easy. Qed.

(*
Theorem sorted_merge_cons_r : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  ∀ l la lb b,
  sorted rel (b :: l) = true
  → split l = (la, lb)
  → merge rel la (b :: lb) = b :: merge rel la lb.
Proof.
intros * Hant Htra * Hs Hll.
unfold merge.
rewrite List_cons_length.
rewrite Nat.add_succ_r.
rewrite <- split_length with (la := l); [ | easy ].
cbn.
destruct la as [| a]. 2: {
  remember (rel a b) as ab eqn:Hab; symmetry in Hab.
  destruct ab; [ | easy ].
Print merge_loop.
...
intros * Hant Htra * Hs Hll.
remember (length l) as len eqn:Hlen.
symmetry in Hlen.
revert l la lb b Hs Hll Hlen.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct l as [| a]. {
  unfold merge; cbn.
  rewrite Nat.add_succ_r; cbn.
  cbn in Hll.
  now injection Hll; clear Hll; intros; subst la lb.
}
destruct l as [| c]. {
  injection Hll; clear Hll; intros; subst la lb.
  cbn in Hs |-*.
  rewrite Bool.andb_true_r in Hs.
  rename Hs into Hba.
  remember (rel a b) as ab eqn:Hab; symmetry in Hab.
  destruct ab; [ | easy ].
  now specialize (Hant a b Hab Hba) as H; subst b.
}
cbn in Hll.
remember (split l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hll; clear Hll; intros; subst la lb.
rename lc into la; rename ld into lb.
cbn in Hlen.
destruct len; [ easy | ].
destruct len; [ easy | ].
do 2 apply Nat.succ_inj in Hlen.
...
specialize (IHlen len) as H1.
assert (H : len < S (S len)) by now transitivity (S len).
specialize (H1 H); clear H.
specialize (H1 l la lb); cbn.
remember (c :: l) as l'; cbn in Hs; subst l'.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
remember (rel b a) as ba eqn:Hba; symmetry in Hba.
remember (rel a c) as ac eqn:Hac; symmetry in Hac.
destruct ba; [ | easy ].
destruct ac; [ | easy ].
do 2 rewrite Bool.andb_true_l in Hs.
destruct ab. {
  specialize (Hant a b Hab Hba) as H; subst b.
  clear Hab; rename Hba into Haa.
  f_equal.
  specialize (fold_merge rel la (a :: c :: lb)) as H2.
  cbn in H2; rewrite H2; clear H2.
  specialize (fold_merge rel la (c :: lb)) as H2.
  cbn in H2; rewrite H2; clear H2.
  specialize (H1 a).
  assert (H : sorted rel (a :: l) = true). {
    cbn.
    destruct l as [| b]; [ easy | ].
    remember (b :: l) as l'; cbn in Hs; subst l'.
    apply Bool.andb_true_iff in Hs.
    destruct Hs as (Hcb, Hs); rewrite Hs, Bool.andb_true_r.
    now apply Htra with (b := c).
  }
  specialize (H1 H Hlc Hlen); clear H.
...
intros * Hant Htra * Hs Hll.
revert la lb b Hs Hll.
induction l as [| a]; intros. {
  unfold merge; cbn.
  rewrite Nat.add_succ_r; cbn.
  cbn in Hll.
  now injection Hll; clear Hll; intros; subst la lb.
}
destruct l as [| c]. {
  injection Hll; clear Hll; intros; subst la lb.
  cbn in Hs |-*.
  rewrite Bool.andb_true_r in Hs.
  rename Hs into Hba.
  remember (rel a b) as ab eqn:Hab; symmetry in Hab.
  destruct ab; [ | easy ].
  now specialize (Hant a b Hab Hba) as H; subst b.
}
cbn in Hll.
remember (split l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hll; clear Hll; intros; subst la lb.
rename lc into la; rename ld into lb.
remember (a :: c :: l) as l'; cbn in Hs; subst l'.
cbn.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
remember (rel b a) as ba eqn:Hba; symmetry in Hba.
destruct ba; [ | easy ].
rewrite Bool.andb_true_l in Hs.
destruct ab. {
  specialize (Hant a b Hab Hba) as H; subst b.
  f_equal.
  rename Hba into Haa; clear Hab.
...
  remember (c :: l) as l'; cbn in Hs; subst l'.
  remember (rel a c) as ac eqn:Hac; symmetry in Hac.
  destruct ac; [ | easy ].
  rewrite Bool.andb_true_l in Hs.
  destruct l as [| b]. {
    cbn in Hlc.
    now injection Hlc; clear Hlc; intros; subst lc ld.
  }
  destruct l as [| d]. {
    cbn in Hlc.
    injection Hlc; clear Hlc; intros; subst lc ld.
    cbn in Hs.
    rewrite Bool.andb_true_r in Hs.
    rename Hs into Hcb.
    specialize (Htra a c b Hac Hcb) as Hab.
    remember (rel b a) as ba eqn:Hba; symmetry in Hba.
    destruct ba; [ | easy ].
    specialize (Hant a b Hab Hba) as H; subst b.
    clear Hba Hab; f_equal.
    now cbn; rewrite Hac.
  }
  cbn in Hlc.
  remember (split l) as le eqn:Hle; symmetry in Hle.
  destruct le as (le, lf).
  injection Hlc; clear Hlc; intros; subst lc ld.
...
*)

(* to be completed
Theorem sorted_merge_cons_cons : ∀ A (rel : A → _),
  antisymmetric rel →
  ∀ l la lb a b,
  sorted rel (a :: b :: l) = true
  → split l = (la, lb)
  → merge rel (a :: la) (b :: lb) = a :: b :: merge rel la lb.
Proof.
intros * Hant * Hs Hla.
unfold merge.
Theorem sorted_merge_loop_cons_cons : ∀ A (rel : A → _),
  antisymmetric rel →
  ∀ it l la lb a b,
  length l ≤ it
  → sorted rel (a :: b :: l) = true
  → split l = (la, lb)
  → merge_loop rel (S (S it)) (a :: la) (b :: lb) =
    a :: b :: merge_loop rel it la lb.
Proof.
intros * Hant * Hit Hs Hla.
revert l la lb a b Hit Hs Hla.
induction it; intros; cbn. {
  cbn in Hs.
  remember (rel a b) as ab eqn:Hab; symmetry in Hab.
  destruct ab; [ | easy ].
  rewrite Bool.andb_true_l in Hs.
  f_equal.
  apply Nat.le_0_r, length_zero_iff_nil in Hit; subst l.
  now injection Hla; intros; subst la lb.
}
cbn in Hs.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ | easy ].
rewrite Bool.andb_true_l in Hs.
f_equal.
destruct l as [| c]. {
  now injection Hla; intros; subst la lb.
}
cbn in Hit; apply Nat.succ_le_mono in Hit.
destruct l as [| d]. {
  injection Hla; clear Hla; intros; subst la lb.
  remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
  remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
  destruct bc; [ | easy ].
  destruct cb; [ | easy ].
  now specialize (Hant b c Hbc Hcb) as H; subst c.
}
cbn in Hit.
destruct (Nat.eq_dec (S (length l)) it) as [Hli| Hli]. 2: {
  cbn in Hla.
  remember (split l) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as (lc, ld).
  injection Hla; clear Hla; intros; subst la lb.
  rename lc into la; rename ld into lb; rename Hlc into Hla.
  specialize (IHit l la lb c d) as H1.
  assert (H : length l ≤ it) by flia Hit Hli.
  specialize (H1 H); clear H.
  assert (H : sorted rel (c :: d :: l) = true) by admit.
  specialize (H1 H Hla); clear H.
  cbn in H1, Hs.
  remember (rel c d) as cd eqn:Hcd; symmetry in Hcd.
  destruct cd; [ | now rewrite Bool.andb_false_r in Hs ].
  injection H1; clear H1; intros H1.
  remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
  remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
  destruct bc; [ | easy ].
  destruct cb. {
    specialize (Hant b c Hbc Hcb) as H; subst c.
    f_equal.
...
  specialize (IHit l (c :: la) (d :: lb) b c) as H1.
  assert (H : length l ≤ it) by flia Hit Hli.
  specialize (H1 H); clear H.
  assert (H : sorted rel (b :: c :: l) = true) by admit.
  specialize (H1 H); clear H.
  assert (H : split l = (c :: la, d :: lb)). {
    cbn in Hla.
    remember (split l) as lc eqn:Hlc; symmetry in Hlc.
    destruct lc as (lc, ld).
    injection Hla; clear Hla; intros; subst la lb.
...
intros * Hant * Hs Hla.
revert la lb a b Hs Hla.
induction l as [| c]; intros; cbn. {
  injection Hla; intros; subst la lb; cbn.
  cbn in Hs.
  now destruct (rel a b).
}
remember (b :: c :: l) as l'; cbn in Hs; subst l'.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ | easy ].
rewrite Bool.andb_true_l in Hs.
f_equal.
specialize (fold_merge rel la (b :: lb)) as H1.
rewrite List_cons_length in H1.
rewrite H1; clear H1.
clear a Hab.
destruct l as [| a]. {
  cbn in Hla.
  injection Hla; clear Hla; intros; subst la lb.
  cbn in Hs |-*.
  remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
  remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
  destruct bc; [ | easy ].
  destruct cb; [ | easy ].
  now specialize (Hant b c Hbc Hcb) as H; subst c.
}
cbn in Hla.
remember (split l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hla; clear Hla; intros; subst la lb.
...
intros * Hant * Hs Hla.
unfold merge.
do 2 rewrite List_cons_length.
rewrite Nat.add_succ_r, Nat.add_succ_l.
rewrite <- split_length with (la := l); [ | easy ].
remember (length l)  as it eqn:H.
assert (Hit : length l ≤ it) by flia H; clear H.
revert l la lb a b Hit Hs Hla.
induction it as (it, IHit) using lt_wf_rec; intros.
cbn in Hs |-*.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ | easy ].
rewrite Bool.andb_true_l in Hs.
destruct l as [| c]. {
  injection Hla; clear Hla; intros; subst la lb.
  now destruct it.
}
destruct l as [| d]. {
  injection Hla; clear Hla; intros; subst la lb.
  f_equal.
  remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
  remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
  destruct bc; [ clear Hs | easy ].
  destruct cb; [ | easy ].
  specialize (Hant b c Hbc Hcb) as H; subst c.
  clear Hbc; rename Hcb into Hbb.
  now destruct it.
}
f_equal.
cbn in Hla.
remember (split l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hla; clear Hla; intros; subst la lb.
rename lc into la; rename ld into lb; rename Hlc into Hla.
remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
destruct bc; [ | easy ].
rewrite Bool.andb_true_l in Hs.
destruct cb. {
  specialize (Hant c b Hcb Hbc) as H; subst c.
  rename Hbc into Hbb.
  f_equal; clear Hcb.
  destruct it; [ easy | ].
  cbn in Hit; apply Nat.succ_le_mono in Hit.
  destruct it; [ easy | ].
  apply Nat.succ_le_mono in Hit.
  specialize (IHit it) as H1.
  assert (H : it < S (S it)) by now transitivity (S it).
  specialize (H1 H l la lb b d Hit Hs Hla); clear H.
  cbn in H1 |-*.
  cbn in Hs.
  remember (rel b d) as bd eqn:Hbd; symmetry in Hbd.
  destruct bd; [ | easy ].
  injection H1; clear H1; intros H1.
  destruct la as [| c]; [ easy | ].
  remember (rel c d) as cd eqn:Hcd; symmetry in Hcd.
  destruct cd. {
    injection H1; clear H1; intros H1 H; subst d.
    rename Hbd into Hbc; rename Hcd into Hcc.
    remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
    destruct cb. {
      specialize (Hant b c Hbc Hcb) as H; subst c.
      clear Hcb Hcc Hbc.
      f_equal.
      destruct la as [| c]. {
        f_equal.
        destruct it; [ | easy ].
        now apply Nat.le_0_r, length_zero_iff_nil in Hit; subst l.
      }
      remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
      destruct cb. {
...
intros * Hant * Hs Hla.
remember (length l)  as len eqn:Hlen; symmetry in Hlen.
revert l la lb a b Hlen Hs Hla.
induction len as (len, IHlen) using lt_wf_rec; intros.
(**)
destruct len. {
  apply length_zero_iff_nil in Hlen; subst l.
  injection Hla; clear Hla; intros; subst la lb.
  cbn in Hs |-*.
  now destruct (rel a b).
}
destruct l as [| c]; [ easy | ].
cbn in Hlen; apply Nat.succ_inj in Hlen.
specialize (IHlen len (Nat.lt_succ_diag_r _) (c :: l) la lb) as H1.
Print merge.
Print merge_loop.
...
cbn.
remember (b :: l) as l'; cbn in Hs; subst l'.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ | easy ].
rewrite Bool.andb_true_l in Hs.
f_equal.
specialize (fold_merge rel la (b :: lb)) as H.
cbn in H; rewrite H; clear H.
(* y a un blème : "a" et "Hab" n'interviennent plus, mais rien ne prouve que
   le premier élément de "la" est supérieur à "b" *)
...
now apply (sorted_merge_cons_r rel l).
...
intros;
rewrite Nat.add_succ_r.
rewrite <- split_length with (la := l); [ | easy ].
Print merge.
...
remember (b :: l) as l'; cbn in Hs; subst l'.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ | easy ].
rewrite Bool.andb_true_l in Hs.
cbn; rewrite Hab.
f_equal.
rewrite Nat.add_succ_r.
rewrite <- split_length with (la := l); [ | easy ].
destruct l as [| c]. {
  cbn in Hla.
  now injection Hla; clear Hla; intros; subst la lb.
}
cbn in Hla.
destruct l as [| d]. {
  injection Hla; clear Hla; intros; subst la lb.
  cbn in Hs.
  remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
  destruct bc; [ clear Hs | easy ].
  remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
  destruct cb; [ | easy ].
  now specialize (Hant c b Hcb Hbc) as H; subst c.
}
remember (split l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hla; clear Hla; intros; subst la lb.
rename lc into la; rename ld into lb; rename Hlc into Hla.
cbn in Hs.
remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
destruct bc; [ | easy ].
rewrite Bool.andb_true_l in Hs.
remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
destruct cb. {
  specialize (Hant c b Hcb Hbc) as H; subst c.
  ...
  destruct la as [| c]. {
    apply split_nil_l in Hla.
    now destruct Hla; subst lb.
  }
...

Theorem sorted_msort_loop : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ l it,
  length l ≤ it
  → sorted rel l = true
  → msort_loop rel it l = l.
Proof.
intros * Hant Htra Htot * Hit Hs.
revert l Hit Hs.
induction it as (it, IHit) using lt_wf_rec; intros.
destruct it; [ easy | cbn ].
remember (split l) as ll eqn:Hll.
symmetry in Hll.
destruct ll as (la, lb).
destruct l as [| a]. {
  injection Hll; clear Hll; intros; subst la lb; cbn.
  rewrite msort_loop_nil; cbn.
  apply msort_loop_nil.
}
destruct l as [| b]. {
  injection Hll; clear Hll; intros; subst la lb; cbn.
  rewrite msort_loop_single, msort_loop_nil; cbn.
  apply msort_loop_single.
}
cbn in Hit; apply Nat.succ_le_mono in Hit.
cbn in Hll.
remember (split l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hll; clear Hll; intros; subst la lb.
rename lc into la; rename ld into lb; rename Hlc into Hla.
rewrite IHit with (l := a :: la); [ | easy | | ]; cycle 1. {
  apply split_length in Hla.
  cbn; flia Hit Hla.
} {
  clear - Hant Htra Htot Hs Hla.
  apply (sorted_cons_cons_split Htra _ _ _ Hs Hla).
}
rewrite IHit with (l := b :: lb); [ | easy | | ]; cycle 1. {
  apply split_length in Hla.
  cbn; flia Hit Hla.
} {
  clear - Hant Htra Htot Hs Hla.
  apply (sorted_cons_cons_split Htra _ _ _ Hs Hla).
}
(**)
clear IHit.
replace (merge rel (a :: la) (b :: lb)) with (a :: b :: merge rel la lb). 2: {
  clear it Hit.
...
  symmetry.
  now apply (sorted_merge_cons_cons rel l).
...
remember (b :: l) as l'; cbn in Hs; subst l'.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ | easy ].
rewrite Bool.andb_true_l in Hs.
cbn.
rewrite Hab.
rewrite Nat.add_succ_r.
rewrite <- split_length with (la := l); [ | easy ].
destruct l as [| c]. {
  injection Hla; clear Hla; intros; subst la lb.
  clear IHit Hit.
  induction it; [ easy | cbn ].
  do 2 rewrite msort_loop_single; cbn.
  now rewrite Hab.
}
destruct l as [| d]. {
  injection Hla; clear Hla; intros; subst la lb.
  cbn in Hs |-*.
  rewrite Bool.andb_true_r in Hs.
  rename Hs into Hbc.
  remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
  destruct cb. {
    rewrite (Hant b c Hbc Hcb).
    clear IHit Hit.
    specialize (Htra a b c Hab Hbc) as Hac.
    clear b Hab Hbc Hcb.
    rename c into b; rename Hac into Hab.
    induction it; [ easy | cbn ].
    rewrite msort_loop_single.
    rewrite msort_loop_pair; [ cbn | easy ].
    rewrite Hab.
    now destruct (rel b b).
  }
  clear IHit Hit Hcb.
  induction it; [ easy | cbn ].
  rewrite msort_loop_single.
  rewrite msort_loop_pair; [ cbn | apply (Htra a b c Hab Hbc) ].
  rewrite Hab.
  remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
  destruct cb; [ | easy ].
  now rewrite (Hant b c Hbc Hcb) in IHit |-*.
}
do 2 rewrite List_cons_length.
cbn in Hla.
remember (split l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hla; clear Hla; intros; subst la lb.
remember (S (S (S (length l)))) as it1 eqn:H.
assert (Hit1 : S (S (S (length l))) ≤ it1) by now rewrite H.
move it1 before it; move Hit1 before Hit.
clear H; cbn in Hit.
destruct it; [ easy | cbn ].
apply Nat.succ_le_mono in Hit.
remember (merge_loop rel it1 (c :: la) (b :: d :: lb)) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [| e]. {
  destruct it1; [ easy | ].
  cbn in Hlc.
  now destruct (rel c b).
}
remember (split lc) as ld eqn:Hld; symmetry in Hld.
destruct ld as (ld, le).
...
rewrite IHit with (l := e :: le); [ | flia | | ]; cycle 1. {
  cbn.
  apply (f_equal length) in Hlc.
  rewrite merge_loop_length in Hlc. 2: {
    rewrite app_length; cbn.
    do 2 rewrite Nat.add_succ_r.
    now rewrite <- split_length with (la := l).
  }
  rewrite app_length in Hlc; cbn in Hlc.
  do 2 rewrite Nat.add_succ_r in Hlc.
  apply Nat.succ_inj in Hlc.
  rewrite <- split_length with (la := l) in Hlc; [ | easy ].
  apply split_length in Hld.
  rewrite Hlc in Hit.
...
  rewrite Hld in H.
...
  rewrite app_length in Hlc; cbn in Hlc.
  do 2 rewrite Nat.add_succ_r in Hlc.
  apply Nat.succ_inj in Hlc.
  rewrite <- split_length with (la := l) in Hlc; [ | easy ].
  rewrite <- Hlc.
...
rewrite IHit; [ | flia | | ]; cycle 1. {
  rewrite merge_length, app_length.
  do 2 rewrite msort_loop_length; cbn.
  rewrite Nat.add_succ_r.
  rewrite <- split_length with (la := lc); [ | easy ].
  apply (f_equal length) in Hlc.
  rewrite merge_loop_length in Hlc. 2: {
    rewrite app_length; cbn.
    do 2 rewrite Nat.add_succ_r.
    now rewrite <- split_length with (la := l).
  }
  rewrite app_length in Hlc; cbn in Hlc.
  do 2 rewrite Nat.add_succ_r in Hlc.
  apply Nat.succ_inj in Hlc.
  rewrite <- split_length with (la := l) in Hlc; [ | easy ].
  rewrite <- Hlc.
...
remember (length (c :: d :: l)) as x; cbn; subst x.
remember (c :: d :: l) as l'; cbn in Hs; subst l'.
remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
destruct bc; [ | easy ].
rewrite Bool.andb_true_l in Hs.
remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
destruct cb. {
  specialize (Hant b c Hbc Hcb) as H; subst c.
  clear Hcb; rename Hbc into Hbb.
  remember (b :: d :: lb) as x.
  remember (d :: l) as y.
  cbn - [ merge_loop ].
  subst x y.
...
  rewrite IHit; [ | easy | | ]; cycle 1. {
    cbn.
    destruct la; cbn.
    apply split_nil_l in Hla.
    destruct Hla; subst l lb; cbn in Hit |-*.
...
  rename d into c.
  destruct l as [| d]. {
    cbn in Hla.
    injection Hla; clear Hla; intros; subst la lb.
    cbn in Hs; rewrite Bool.andb_true_r in Hs.
    rename Hs into Hbc.
    clear IHit Hit Hbb.
    revert a b c Hab Hbc.
    induction it; intros; [ easy | cbn ].
    rewrite msort_loop_pair; [ | easy ].
    rewrite msort_loop_pair; [ cbn | easy ].
    rewrite Hab, Hbc.
    now destruct (rel b b); apply IHit.
  }
  destruct l as [| e]. {
    cbn in Hla.
    injection Hla; clear Hla; intros; subst la lb.
    cbn in Hs.
    remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
    remember (rel c d) as cd eqn:Hcd; symmetry in Hcd.
    destruct bc; [ | easy ].
    destruct cd; [ | easy ].
    remember (rel d b) as db eqn:Hdb; symmetry in Hdb.
    remember (rel d c) as dc eqn:Hdc; symmetry in Hdc.
    destruct db. {
      specialize (Htra b c d Hbc Hcd) as Hbd.
      specialize (Hant d b Hdb Hbd) as H; subst d.
      specialize (Hant c b Hcd Hbc) as H; subst c.
      clear - Hab.
      induction it; [ easy | cbn ].
...
  revert a b la lb Hs Hla.
  induction l as [| c]; intros. {
    now injection Hla; clear Hla; intros; subst la lb.
  }
...
  cbn in Hs |-*.
  destruct la as [| c]; [ easy | ].
  remember (rel a b) as ab eqn:Hab; symmetry in Hab.
  destruct ab; [ | easy ].
  rewrite Bool.andb_true_l in Hs.
  destruct l as [| d]. {
    now injection Hla; clear Hla; intros.
  }
  cbn in Hla.
  destruct l as [| e]. {
    injection Hla; clear Hla; intros; subst la lb d.
    remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
    destruct bc; [ | easy ].
    now rewrite (Htra a b c Hab Hbc).
  }
  remember (split l) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as (lc, ld).
  injection Hla; clear Hla; intros; subst d lc lb.
  remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
  destruct bc; [ | easy ].
  rewrite (Htra a b c Hab Hbc).
...
  revert a b la lb Hs Hla.
  induction l as [| c]; intros. {
    now injection Hla; clear Hla; intros; subst la lb.
  }
(*
  remember (b :: c :: l) as l'; cbn in Hs; subst l'.
  apply Bool.andb_true_iff in Hs.
  destruct Hs as (Hab, Hs).
  specialize (IHl b c (c :: la) lb Hs) as H1.
*)
  destruct l as [| d]. {
    injection Hla; clear Hla; intros; subst la lb.
    cbn in Hs |-*.
    rewrite (Htra a b c); [ easy | | ]. {
      now destruct (rel a b).
    } {
      destruct (rel b c); [ easy | ].
      now rewrite Bool.andb_false_r in Hs.
    }
  }
  cbn in Hla.
  remember (split l) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as (lc, ld).
  injection Hla; clear Hla; intros; subst la lb.
  rename lc into la; rename ld into lb; rename Hlc into Hla.
...
  remember (c :: la) as l'; cbn; subst l'.
  apply Bool.andb_true_iff.
  split. 2: {
    eapply IHl.
...
  remember (d :: l) as l'; cbn in Hs; subst l'.
  apply Bool.andb_true_iff in Hs.
  destruct Hs as (Hab, Hs).
  apply Bool.andb_true_iff in Hs.
  destruct Hs as (Hbc, Hs).
  apply Bool.andb_true_iff in Hs.
  destruct Hs as (Hcd, Hs).
  rewrite (Htra a b c Hab Hbc).
  rewrite Bool.andb_true_l.
  destruct l as [| e]. {
    now injection Hla; clear Hla; intros; subst la lb.
  }
  destruct l as [| f]. {
    injection Hla; clear Hla; intros; subst la lb.
    cbn in Hs |-*.
    rewrite Bool.andb_true_r in Hs |-*.
    now rewrite (Htra c d e Hcd Hs).
  }
  cbn in Hla.
  remember (split l) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as (lc, ld).
  injection Hla; clear Hla; intros; subst la lb.
...
  remember (b :: l) as l'; cbn in Hs; subst l'.
  remember (rel a b) as ab eqn:Hab; symmetry in Hab.
  destruct ab; [ | easy ].
  rewrite Bool.andb_true_l in Hs.
...
(*
cbn in Hll.
remember (split l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hll; clear Hll; intros; subst la lb.
remember (split (a :: la)) as lc eqn:Hlc.
*)
Theorem glop : ∀ A (rel : A → _) a b l la lb it ita itb,
  S (length l) ≤ it
  → sorted rel (a :: b :: l) = true
  → split (a :: b :: l) = (la, lb)
  → msort_loop rel it
      (merge rel (msort_loop rel ita la) (msort_loop rel itb lb)) =
      a :: b :: l.
Proof.
intros * Hit Hs Hll.
clear Hit.
revert a b l la lb ita itb Hs Hll.
induction it; intros. {
  cbn in Hll.
  remember (split l) as ll eqn:Hll'.
  symmetry in Hll'.
  destruct ll as (lc, ld).
  injection Hll; clear Hll; intros; subst la lb.
  rename lc into la; rename ld into lb; rename Hll' into Hll.
  cbn.
...
; [ easy | cbn ].
cbn in Hll.
remember (split l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hll; clear Hll; intros; subst la lb.
rename lc into la; rename ld into lb; rename Hlc into Hla.
destruct l as [| c]. {
  cbn in Hla.
  injection Hla; clear Hla; intros; subst la lb; cbn.
  do 2 rewrite msort_loop_single; cbn.
  cbn in Hs.
  rewrite Bool.andb_true_r in Hs.
  rename Hs into Hab.
  rewrite Hab; cbn.
  do 2 rewrite msort_loop_single; cbn.
  clear IHit Hit.
  rewrite Hab; cbn.
  induction it; [ easy | cbn ].
  do 2 rewrite msort_loop_single; cbn.
  now rewrite Hab; cbn.
}
destruct l as [| d]. {
  cbn in Hla.
  injection Hla; clear Hla; intros; subst la lb; cbn.
  cbn in Hs.
  remember (rel a b) as ab eqn:Hab; symmetry in Hab.
  destruct ab; [ | easy ].
  remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
  destruct bc; [ clear Hs | easy ].
  remember (split (merge rel _ _)) as ll eqn:Hll; symmetry in Hll.
  destruct ll as (lc, ld).
...
  rewrite msort_loop_nil; cbn.
  do 2 rewrite msort_loop_single.
  do 2 rewrite msort_loop_length.
  do 2 rewrite merge_length; cbn.
  rewrite msort_loop_single; cbn.
  rewrite (Htra a b c Hab Hbc).
  destruct it; [ cbn in Hit; flia Hit | cbn ].
...
intros * Hant Htra Htot * Hit Hs.
destruct it; [ easy | cbn ].
remember (split l) as ll eqn:Hll.
symmetry in Hll.
destruct ll as (la, lb).
destruct it. {
  cbn.
...
  now apply sorted_merge_loop.
...
intros * Hant Htra Htot * Hit Hs.
revert l Hit Hs.
induction it as (it, IHit) using lt_wf_rec; intros.
destruct it; [ easy | cbn ].
remember (split l) as ll eqn:Hll.
symmetry in Hll.
destruct ll as (la, lb).
destruct (Nat.eq_dec (length l) (S it)) as [Hit1| Hit1]. {
  destruct l as [| a]; [ easy | ].
  destruct l as [| b]. {
    cbn in Hll.
    injection Hll; clear Hll; intros; subst la lb.
    cbn in Hit1.
    now apply Nat.succ_inj in Hit1; subst it; cbn.
  }
  cbn in Hit1.
  apply Nat.succ_inj in Hit1.
  clear Hit.
  cbn in Hll.
  remember (split l) as ll eqn:Hll1; symmetry in Hll1.
  destruct ll as (lc, ld).
  injection Hll; clear Hll; intros; subst la lb.
  rename lc into la; rename ld into lb.
  remember (b :: l) as lc; cbn in Hs; subst lc.
  apply Bool.andb_true_iff in Hs.
  destruct Hs as (Hab, Hs).
  cbn in Hs.
  destruct l as [| c]. {
    injection Hll1; clear Hll1; intros; subst la lb.
    subst it; cbn.
    rewrite Hab; cbn.
    now rewrite Hab; cbn.
  }
  cbn in Hit1.
  apply Bool.andb_true_iff in Hs.
  destruct Hs as (Hbc, Hs).
  cbn in Hs.
  destruct l as [| d]. {
    clear Hs.
    cbn in Hll1.
    injection Hll1; clear Hll1; intros; subst la lb.
    cbn in Hit1; subst it; cbn.
    specialize (Htra a b c Hab Hbc) as Hac.
    rewrite Hac; cbn.
    rewrite Hac; cbn.
    rewrite Hab; cbn.
    remember (rel c b) as cb eqn:Hcb.
    symmetry in Hcb.
    destruct cb. {
      specialize (Hant b c Hbc Hcb) as H1.
      subst c; cbn.
      rewrite Hab; cbn.
      rewrite Hab; cbn.
      rewrite Hbc; cbn.
      rewrite Hab; cbn.
      now rewrite Hbc.
    }
    cbn.
    rewrite Hac; cbn.
    rewrite Hab; cbn.
    rewrite Hcb; cbn.
    now rewrite Hab, Hcb; cbn.
  }
  apply Bool.andb_true_iff in Hs.
  destruct Hs as (Hcd, Hs).
...
    destruct it; [ easy | cbn ].
    apply Nat.succ_inj
...
rewrite IHit with (l := la); [ | easy | | ]; cycle 1. {
  specialize (split_length _ Hll) as H1.
  rewrite H1 in Hit.
  destruct lb as [| b]. {
    apply split_nil_r in Hll.
    destruct Hll as (Hla, Hll); subst l.
    destruct la as [| a]; [ easy | ].
    destruct la; [ | cbn in Hll; flia Hll ].
    cbn.
    cbn in Hit.
    destruct it.
...
destruct l as [| a]. {
  injection Hll; clear Hll; intros; subst la lb.
  rewrite msort_loop_nil; cbn.
  apply msort_loop_nil.
}
destruct l as [| b]. {
  injection Hll; clear Hll; intros; subst la lb.
  rewrite msort_loop_nil; cbn.
  destruct it; [ easy | cbn ].
  rewrite msort_loop_length.
  rewrite merge_length.
  rewrite app_length.
  do 2 rewrite msort_loop_length; cbn.
  rewrite msort_loop_nil, msort_loop_single; cbn.
  rewrite msort_loop_single; cbn.
  rewrite msort_loop_single, msort_loop_nil; cbn.
  apply msort_loop_single.
}
cbn in Hll.
remember (split l) as ll eqn:Hll2; symmetry in Hll2.
destruct ll as (lc, ld).
injection Hll; clear Hll; intros; subst la lb; cbn.
cbn in Hit.
rewrite <- Nat.succ_le_mono in Hit.
destruct it; [ easy | ].
apply Nat.succ_le_mono in Hit.
rewrite IHit; [ | easy | | ]; cycle 1. {
  rewrite merge_length, app_length.
  do 2 rewrite msort_loop_length; cbn.
  apply -> Nat.succ_le_mono.
  rewrite Nat.add_succ_r.
  rewrite <- split_length with (la := l); [ | easy ].
...
rewrite IHit; [ | easy | | ]; cycle 1. {
  rewrite merge_length, app_length.
  do 2 rewrite msort_loop_length.
  cbn in Hll.
  remember (split l) as ll eqn:Hll2; symmetry in Hll2.
  destruct ll as (lc, ld).
  injection Hll; clear Hll; intros; subst la lb; cbn.
  cbn in Hit.
  rewrite Nat.add_succ_r.
  rewrite <- split_length with (la := l); [ | easy ].
  cbn in Hit.
...
rewrite IHit; [ | easy | | ]; cycle 1. {
  rewrite merge_length, app_length.
  do 2 rewrite msort_loop_length.
  rewrite <- split_length with (la := l); [ | easy ].
...
intros * Hant * Hit Hs.
revert l Hit Hs.
induction it; intros; [ easy | cbn ].
remember (split l) as ll eqn:Hll.
symmetry in Hll.
destruct ll as (la, lb).
(**)
specialize split_length as H1.
specialize (H1 _ _ _ _ Hll).
...
rewrite IHit; cycle 1. {
  rewrite merge_length, app_length.
  do 2 rewrite msort_loop_length.
...
  rewrite <- split_length with (la := l); [ | easy ].
...
destruct l as [| a]. {
  cbn in Hll.
  injection Hll; clear Hll; intros; subst la lb; cbn.
  now clear; induction it.
}
cbn in Hll.
destruct l as [| b]. {
  injection Hll; clear Hll; intros; subst la lb; cbn.
  now clear; induction it.
}
remember (split l) as ll2 eqn:Hll2.
symmetry in Hll2.
destruct ll2 as (la2, lb2).
injection Hll; clear Hll; intros; subst la lb.
rename la2 into la.
rename lb2 into lb; cbn.
remember (rel a b) as ab eqn:Hab.
symmetry in Hab.
destruct ab. {
  cbn in Hit.
  apply Nat.succ_le_mono in Hit.
  destruct it; [ easy | ].
  apply Nat.succ_le_mono in Hit; cbn.
  rewrite Nat.add_succ_r; cbn.
  destruct la as [| c]. {
    apply split_nil_l in Hll2.
    destruct Hll2; subst l lb; cbn.
    rewrite Hab.
    clear - Hab.
    induction it; [ easy | cbn ].
    now rewrite Hab.
  }
  remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
  destruct cb. {
    destruct la as [| d]. {
      cbn.
      destruct lb as [| e]. {
        apply split_nil_r in Hll2.
        destruct Hll2 as (H1, _); subst l.
        cbn in Hs.
        rewrite Hab in Hs; cbn in Hs.
        rewrite Bool.andb_true_r in Hs; cbn.
        rename Hs into Hbc.
        rewrite Hbc.
        specialize (Hant c b Hcb Hbc) as H1; subst c.
        rewrite Hab.
        clear IHit Hit.
        induction it; [ easy | cbn ].
        now rewrite Hab, Hcb.
      }
      remember (split lb) as la eqn:Hla; symmetry in Hla.
      destruct la as (la, lc).
      cbn in Hs.
      rewrite Hab, Bool.andb_true_l in Hs.
      destruct l as [| d]; [ easy | ].
      apply Bool.andb_true_iff in Hs.
      destruct Hs as (Hbd, Hs).
      destruct it; [ easy | ].
      cbn in Hll2, Hs |-*.
      destruct l as [| f]; [ easy | ].
      apply Bool.andb_true_iff in Hs.
      destruct Hs as (Hdf & Hs).
      cbn in Hs.
      remember (split l) as ll eqn:Hll; symmetry in Hll.
      destruct ll as (ld, le).
      injection Hll2; clear Hll2; intros; subst d ld f le.
      rewrite Hbd.
      specialize (Hant b c Hbd Hcb) as H1; subst c.
      rewrite Hab; cbn.
      apply split_nil_l in Hll.
      destruct Hll; subst l lb.
      cbn in Hla.
      injection Hla; clear Hla; intros; subst la lc; cbn.
      rewrite Hab, Hbd.
      clear IHit Hit.
      induction it; [ easy | cbn ].
      now rewrite Hab, Hbd.
    }
...
    cbn in Hs.
    rewrite Hab in Hs; cbn in Hs.
    remember (rel d b) as db eqn:Hdb; symmetry in Hdb.
    destruct db. {
      cbn.
      destruct la as [| e]; cbn. {
        remember (split lb) as lc eqn:Hlc; symmetry in Hlc.
        destruct lc as (ld, le); cbn.
        rewrite Hab.
        remember (rel a c) as ac eqn:Hac; symmetry in Hac.
        destruct ac. {
          remember (rel d c) as dc eqn:Hdc; symmetry in Hdc.
          destruct dc. {
            destruct it. {
              now apply Nat.le_0_r, length_zero_iff_nil in Hit; subst l.
            }
            cbn.
            rewrite Nat.add_succ_r; cbn.
            destruct ld as [| e]. {
              apply split_nil_l in Hlc.
              destruct Hlc; subst lb le; cbn.
              apply split_nil_r in Hll2.
              destruct Hll2 as (H1, H2); subst l.
              cbn in H2; flia H2.
            }
            remember (rel e c) as ec eqn:Hec; symmetry in Hec.
            destruct ec. {
              cbn.
              destruct ld as [| f]. {
                cbn.
                destruct le as [| g]. {
                  apply split_nil_r in Hlc.
                  destruct Hlc as (H1, _); subst lb.
                  cbn.
                  rewrite Hac, Hec.
                  remember (rel a d) as ad eqn:Had.
                  symmetry in Had.
                  destruct ad. {
                    remember (rel e d) as ed eqn:Hed; symmetry in Hed.
                    destruct ed. {
                      destruct it. {
                        cbn.
...

Theorem sorted_msort : ∀ A (rel : A → _),
  ∀ l,
  sorted rel l = true
  → msort rel l = l.
Proof.
intros * Hs.
unfold msort.
...
apply sorted_msort_loop; [ | easy | easy ].
*)

(* isort length *)

Theorem isort_insert_length : ∀ A rel (a : A) lsorted,
  length (isort_insert rel a lsorted) = S (length lsorted).
Proof.
intros.
induction lsorted as [| b]; intros; [ easy | cbn ].
destruct (rel a b); [ easy | ].
cbn; f_equal.
apply IHlsorted.
Qed.

Theorem isort_loop_length : ∀ A rel (lsorted l : list A),
  length (isort_loop rel lsorted l) = length lsorted + length l.
Proof.
intros.
revert lsorted.
induction l as [| a]; intros; [ now cbn; rewrite Nat.add_0_r | cbn ].
rewrite IHl, <- Nat.add_succ_comm; f_equal.
apply isort_insert_length.
Qed.

Theorem isort_length : ∀ A rel (l : list A), length (isort rel l) = length l.
Proof.
intros.
apply isort_loop_length.
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

Theorem Permutation_cons_isort_insert : ∀ A (rel : A → _) a la lb,
  Permutation la lb
  → Permutation (a :: la) (isort_insert rel a lb).
Proof.
intros * Hab.
revert a la Hab.
induction lb as [| b]; intros; cbn. {
  apply Permutation_sym in Hab.
  now apply Permutation_nil in Hab; subst la.
}
remember (rel a b) as x eqn:Hx; symmetry in Hx.
destruct x; [ now constructor | ].
replace (b :: lb) with ([b] ++ lb) in Hab by easy.
apply Permutation_cons_app with (a := a) in Hab.
eapply Permutation_trans; [ apply Hab | cbn ].
apply perm_skip.
now apply IHlb.
Qed.

Theorem Permutation_isort_insert_sorted : ∀ A (rel : A → _) la lb c,
  Permutation la lb
  → Permutation (isort_insert rel c la) (isort_insert rel c lb).
Proof.
intros * Hp.
revert la Hp.
induction lb as [| b]; intros; cbn. {
  now apply Permutation_sym, Permutation_nil in Hp; subst la; cbn.
}
remember (rel c b) as x eqn:Hx; symmetry in Hx.
destruct x. {
  apply Permutation_sym.
  apply Permutation_cons_isort_insert.
  now apply Permutation_sym.
} {
  apply Permutation_sym.
  eapply Permutation_trans. 2: {
    apply Permutation_cons_isort_insert.
    apply Permutation_sym.
    apply Hp.
  }
  replace (c :: b :: lb) with ([c] ++ b :: lb) by easy.
  eapply Permutation_trans; [ | now apply Permutation_cons_app ]; cbn.
  constructor.
  apply Permutation_sym.
  eapply Permutation_trans; [ | apply IHlb; easy ].
  now apply Permutation_cons_isort_insert.
}
Qed.

Theorem Permutation_isort_loop_sorted : ∀ A (rel : A → _) la lb lc,
  Permutation la lb
  → Permutation (isort_loop rel la lc) (isort_loop rel lb lc).
Proof.
intros * Hp.
revert la lb Hp.
induction lc as [| c]; intros; [ easy | cbn ].
apply IHlc.
now apply Permutation_isort_insert_sorted.
Qed.

Theorem Permutation_isort_loop : ∀ A (rel : A → _) la lb,
  Permutation (la ++ lb) (isort_loop rel la lb).
Proof.
intros.
revert la.
induction lb as [| b]; intros; [ now rewrite app_nil_r | ].
specialize (IHlb (la ++ [b])) as H1.
rewrite <- app_assoc in H1; cbn in H1.
eapply Permutation_trans; [ apply H1 | ].
cbn.
clear IHlb H1.
revert lb b.
induction la as [| a]; intros; [ easy | ].
cbn.
remember (rel b a) as x eqn:Hx; symmetry in Hx.
destruct x. {
  apply Permutation_isort_loop_sorted.
  rewrite app_comm_cons.
  replace (b :: a :: la) with ([b] ++ (a :: la)) by easy.
  apply Permutation_app_comm.
} {
  apply Permutation_isort_loop_sorted.
  constructor.
  eapply Permutation_trans. 2: {
    now apply Permutation_cons_isort_insert.
  }
  apply Permutation_app_comm.
}
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
cbn in Ha.
destruct Ha as [Ha| Ha]; [ now right; left | ].
apply IHlsorted in Ha.
destruct Ha as [Ha| Ha]; [ now left | now right; right ].
Qed.

Theorem in_isort_loop : ∀ A (rel : A → A → bool) a lsorted l,
  a ∈ isort_loop rel lsorted l
  → a ∈ lsorted ∨ a ∈ l.
Proof.
intros * Ha.
revert a lsorted Ha.
induction l as [| b]; intros; [ now left | ].
cbn in Ha.
apply IHl in Ha.
destruct Ha as [Ha| Ha]. {
  apply in_isort_insert in Ha.
  destruct Ha as [Ha| Ha]; [ now right; left | now left ].
} {
  now right; right.
}
Qed.

Theorem in_isort : ∀ A (rel : A → A → bool) a l, a ∈ isort rel l → a ∈ l.
Proof.
intros * Ha.
apply in_isort_loop in Ha.
now destruct Ha.
Qed.

Theorem isort_insert_isort_rank_insert : ∀ A B rel ia (f : B → A) lrank,
  isort_insert rel (f ia) (map f lrank) =
  map f (isort_rank_insert rel f ia lrank).
Proof.
intros.
induction lrank as [| ib]; [ easy | cbn ].
destruct (rel (f ia) (f ib)); [ easy | ].
cbn; f_equal.
apply IHlrank.
Qed.

Theorem isort_loop_isort_rank_loop : ∀ A rel d (f : nat → A) lrank l,
  (∀ i, i < length l → f (length lrank + i) = nth i l d)
  → isort_loop rel (map f lrank) l = map f (isort_rank_loop rel f lrank l).
Proof.
intros * Hia.
revert lrank Hia.
induction l as [| a]; intros; [ easy | cbn ].
specialize (Hia 0 (Nat.lt_0_succ _)) as H1.
cbn in H1; rewrite Nat.add_0_r in H1.
rewrite <- H1.
rewrite isort_insert_isort_rank_insert.
rewrite IHl; [ easy | ].
intros i Hi.
rewrite isort_rank_insert_length.
apply Nat.succ_lt_mono in Hi.
specialize (Hia (S i) Hi) as H2.
now rewrite <- Nat.add_succ_comm in H2.
Qed.

Theorem isort_isort_rank : ∀ A (rel : A → A → bool) (d : A) l,
  isort rel l = map (λ i, nth i l d) (isort_rank rel l).
Proof.
intros.
destruct l as [| d' l]; [ easy | ].
cbn - [ nth ].
replace [d'] with (map (λ i, nth i (d' :: l) d) [0]) by easy.
rewrite isort_loop_isort_rank_loop with (d := d').
cbn - [ nth ].
f_equal. 2: {
  intros i Hi; cbn.
  now apply nth_indep.
}
apply isort_rank_loop_nth_indep; [ easy | ].
intros i Hi.
destruct Hi as [Hi| Hi]; [ subst i; cbn; easy | easy ].
Qed.

Theorem isort_insert_trans_r : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  ∀ a b la,
  rel a b = true
  → isort_insert rel a la = la ++ [a]
  → isort_insert rel b (la ++ [a]) = la ++ [a; b].
Proof.
intros * Hant Htra * Hab Hs.
induction la as [| c]; cbn. {
  remember (rel b a) as ba eqn:Hba; symmetry in Hba.
  destruct ba; [ | easy ].
  now rewrite (Hant a b Hab Hba).
}
remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
destruct bc. {
  cbn in Hs.
  remember (rel a c) as ac eqn:Hac; symmetry in Hac.
  destruct ac. {
    injection Hs; clear Hs; intros Hs H1; subst c.
    specialize (Hant a b Hab Hbc) as H1; subst b.
    f_equal.
    now rewrite app_comm_cons, Hs, <- app_assoc.
  }
  specialize (Htra a b c Hab Hbc) as H1.
  congruence.
}
f_equal.
apply IHla.
cbn in Hs.
remember (rel a c) as ac eqn:Hac; symmetry in Hac.
destruct ac; [ | now injection Hs ].
injection Hs; clear Hs; intros Hs H1; subst c.
apply cons_app_repeat in Hs.
rewrite Hs.
remember (length la) as len eqn:Hlen.
clear - Hant Htra.
induction len; [ easy | cbn ].
destruct (rel a a). {
  f_equal.
  apply repeat_cons.
}
f_equal.
apply IHlen.
Qed.

Theorem select_first_Permutation : ∀ A (rel : A → _) a b la lb,
  select_first rel a la = (b, lb)
  → Permutation (a :: la) (b :: lb).
Proof.
intros * Hab.
revert a b lb Hab.
induction la as [| c]; intros. {
  cbn in Hab.
  now injection Hab; clear Hab; intros; subst b lb.
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
destruct ac; subst x. {
  etransitivity; [ apply perm_swap | symmetry ].
  etransitivity; [ apply perm_swap | symmetry ].
  now apply perm_skip.
} {
  symmetry.
  etransitivity; [ apply perm_swap | symmetry ].
  now apply perm_skip.
}
Qed.

Theorem select_first_if : ∀ A (rel : A → _),
  transitive rel →
  total_relation rel →
  ∀ a b la lb,
  select_first rel a la = (b, lb)
  → (∀ c, c ∈ a :: la → rel b c = true) ∧
    (∀ c, c ∈ lb → rel b c = true) ∧
    Permutation (a :: la) (b :: lb).
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
destruct H1 as (H1 & H2 & H3).
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
split. {
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
}
destruct ac; subst x. {
  etransitivity; [ apply perm_swap | symmetry ].
  etransitivity; [ apply perm_swap | symmetry ].
  now apply perm_skip.
} {
  symmetry.
  etransitivity; [ apply perm_swap | symmetry ].
  now apply perm_skip.
}
Qed.

Theorem Permutation_ssort_loop : ∀ A (rel : A → _) la len,
  length la ≤ len
  → Permutation la (ssort_loop rel len la).
Proof.
intros * Hlen.
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
apply (select_first_Permutation rel) in Hlc.
transitivity (c :: lc); [ easy | ].
now constructor.
Qed.

(* isort is sorted *)

Theorem isort_insert_is_sorted : ∀ A (rel : A → _),
  total_relation rel →
  ∀ a lsorted,
  sorted rel lsorted = true
  → sorted rel (isort_insert rel a lsorted) = true.
Proof.
intros * Hto * Hs.
induction lsorted as [| b]; [ easy | cbn ].
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  remember (b :: lsorted) as l; cbn; subst l.
  now apply Bool.andb_true_iff.
} {
  specialize (Hto a b) as Hba.
  rewrite Hab in Hba; cbn in Hba.
  destruct lsorted as [| c]; [ now cbn; rewrite Hba | ].
  remember (c :: lsorted) as l; cbn in Hs |-*; subst l.
  apply Bool.andb_true_iff in Hs.
  destruct Hs as (Hbc, Hs).
  rewrite IHlsorted; [ | easy ].
  cbn.
  remember (rel a c) as ac eqn:Hac; symmetry in Hac.
  destruct ac; [ now rewrite Hba | now rewrite Hbc ].
}
Qed.

Theorem isort_loop_is_sorted : ∀ A (rel : A → _),
  total_relation rel →
  ∀ lsorted l,
  sorted rel lsorted = true
  → sorted rel (isort_loop rel lsorted l) = true.
Proof.
intros * Hto * Hs.
revert lsorted Hs.
induction l as [| a]; intros; [ easy | cbn ].
now apply IHl, isort_insert_is_sorted.
Qed.

Theorem sorted_isort_insert_r : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  ∀ a la,
  sorted rel (la ++ [a]) = true
  → isort_insert rel a la = la ++ [a].
Proof.
intros * Hant Htra * Hla.
revert a Hla.
induction la as [| b] using rev_ind; intros; [ easy | cbn ].
apply sorted_app in Hla.
destruct Hla as (Hla & _ & Htrr).
specialize (Htrr Htra).
specialize (IHla _ Hla) as H1.
destruct la as [| c]; cbn. {
  clear Hla H1.
  specialize (Htrr b a (or_introl eq_refl) (or_introl eq_refl)).
  rename Htrr into Hba.
  remember (rel a b) as ab eqn:Hab; symmetry in Hab.
  destruct ab; [ | easy ].
  apply Hant in Hba.
  now rewrite (Hba Hab).
}
specialize (Htrr c a (or_introl eq_refl) (or_introl eq_refl)) as Hca.
remember (rel a c) as ac eqn:Hac; symmetry in Hac.
destruct ac. {
  apply Hant in Hca.
  specialize (Hca Hac); subst c.
  f_equal.
  cbn in H1.
  remember (rel b a) as ba eqn:Hba; symmetry in Hba.
  destruct ba. {
    injection H1; clear H1; intros H1 H2; subst b.
    rewrite <- H1; cbn.
    now f_equal.
  }
  injection H1; clear H1; intros H1.
  apply Bool.not_true_iff_false in Hba.
  exfalso; apply Hba.
  apply Htrr; [ | now left ].
  now apply in_or_app; right; left.
}
f_equal.
cbn in H1.
remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
destruct bc. {
  injection H1; clear H1; intros H1 H2; subst c.
  rewrite <- H1; cbn.
  rewrite Hac.
  f_equal.
  rewrite <- app_comm_cons in Hla.
  specialize (sorted_repeat Hant Htra b la Hla) as Har.
  rewrite Har.
  remember (length la) as len eqn:Hlen; symmetry in Hlen.
  clear - Hac.
  induction len; [ easy | cbn ].
  rewrite Hac.
  f_equal; apply IHlen.
}
injection H1; clear H1; intros H1.
rewrite <- app_assoc; cbn.
specialize (Htrr b a) as Hba.
assert (H : b ∈ c :: la ++ [b]). {
  rewrite app_comm_cons.
  now apply in_or_app; right; left.
}
specialize (Hba H (or_introl eq_refl)); clear H.
now apply isort_insert_trans_r.
Qed.

Theorem sorted_isort_loop : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  ∀ ls l,
  sorted rel (ls ++ l) = true
  → isort_loop rel ls l = ls ++ l.
Proof.
intros * Hant Htra * Hs.
revert ls Hs.
induction l as [| a]; intros; cbn; [ now rewrite app_nil_r | ].
assert (H : isort_insert rel a ls = ls ++ [a]). {
  clear IHl.
  assert (H : sorted rel (ls ++ [a]) = true). {
    rewrite List_app_cons, app_assoc in Hs.
    now apply sorted_app in Hs.
  }
  clear l Hs; rename H into Hs.
  now apply sorted_isort_insert_r.
}
rewrite H.
symmetry.
rewrite List_app_cons, app_assoc.
symmetry.
apply IHl.
now rewrite <- app_assoc.
Qed.

Theorem select_first_sorted : ∀ A rel,
  transitive rel → ∀ (a b : A) la lb,
  sorted rel (a :: la) = true
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

Theorem sorted_ssort_loop : ∀ A (rel : A → _),
  transitive rel →
  ∀ it l,
  length l ≤ it
  → sorted rel l = true
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
specialize (select_first_sorted Htr _ _ Hs Hlb) as H1.
destruct H1; subst b lb.
f_equal.
apply IHit; [ easy | ].
cbn in Hs.
destruct la as [| b]; [ easy | ].
now apply Bool.andb_true_iff in Hs.
Qed.

Theorem ssort_loop_is_sorted : ∀ A (rel : A → _),
  transitive rel →
  total_relation rel →
  ∀ l len,
  length l ≤ len
  → sorted rel (ssort_loop rel len l) = true.
Proof.
intros * Htr Htot * Hlen.
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
specialize (Permutation_ssort_loop rel lb) as H1.
assert (H : length lb ≤ len). {
  apply select_first_length in Hlb.
  congruence.
}
specialize (H1 _ H); clear H.
apply (select_first_if Htr Htot) in Hlb.
destruct Hlb as (_ & H2 & _).
specialize (H2 c).
assert (H : c ∈ lb). {
  rewrite Hlc in H1.
  apply Permutation_sym in H1.
  apply Permutation_in with (l := c :: lc); [ easy | now left ].
}
specialize (H2 H); clear H.
now rewrite H2 in Hbc.
Qed.

Theorem sorted_bsort_swap : ∀ A (rel : A → _),
  ∀ la,
  sorted rel la = true
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

Theorem sorted_bsort_loop : ∀ A (rel : A → _),
  ∀ it l,
  sorted rel l = true
  → bsort_loop rel it l = l.
Proof.
intros * Hs.
rename l into la.
revert la Hs.
induction it; intros; [ easy | cbn ].
remember (bsort_swap rel la) as lb eqn:Hlb.
symmetry in Hlb.
destruct lb as [lb| ]; [ | easy ].
now rewrite sorted_bsort_swap in Hlb.
Qed.

Theorem bsort_swap_None : ∀ A (rel : A → _) la,
  bsort_swap rel la = None
  → sorted rel la = true.
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
now rewrite (IHla eq_refl).
Qed.

Theorem bsort_swap_Some : ∀ A (rel : A → _) la lb,
  bsort_swap rel la = Some lb
  → sorted rel la = false ∧
    ∃ a b lc ld, rel a b = false ∧
    sorted rel (lc ++ [a]) = true ∧
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
    now rewrite Hab.
  }
  cbn in Hlc.
  injection Hlc; clear Hlc; intros Hlc H; subst e.
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

(*
Compute (nb_disorder Nat.leb [7;5;3;22;8]).
Definition succ_when_ge k a := a + Nat.b2n (k <=? a).
Fixpoint canon_sym_gr_list n k : list nat :=
  match n with
  | 0 => []
  | S n' =>
      k / n'! ::
      map (succ_when_ge (k / n'!)) (canon_sym_gr_list n' (k mod n'!))
  end.
Definition canon_sym_gr_list_list n : list (list nat) :=
  map (canon_sym_gr_list n) (seq 0 n!).
Compute (map (λ l, (l, nb_disorder Nat.leb l)) (canon_sym_gr_list_list 5)).
Compute (map (λ l, list_eqb Nat.eqb (bsort_loop Nat.leb (nb_disorder Nat.leb l(* - 1*)) l) (seq 0 5)) (canon_sym_gr_list_list 5)).
*)

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

Theorem bsort_loop_enough_iter : ∀ A (rel : A → _),
  total_relation rel →
  ∀ l it1 it2,
  nb_disorder rel l ≤ it1
  → nb_disorder rel l ≤ it2
  → bsort_loop rel it1 l = bsort_loop rel it2 l.
Proof.
intros * Htot * Hit1 Hit2.
rename l into la.
revert la it2 Hit1 Hit2.
induction it1; intros; cbn. {
  apply Nat.le_0_r in Hit1.
  clear Hit2.
  destruct it2; [ easy | cbn ].
  remember (bsort_swap rel la) as lb eqn:Hlb.
  symmetry in Hlb.
  destruct lb as [lb| ]; [ | easy ].
  apply bsort_swap_Some in Hlb.
  destruct Hlb as (Hs & c & d & lc & ld & Hlb).
  destruct Hlb as (Hcd & Hrc & Hbla & Hlbc).
  rewrite Hbla in Hit1.
  exfalso; clear - Hit1 Hcd.
  induction lc as [| a]; cbn in Hit1; [ now rewrite Hcd in Hit1 | ].
  apply IHlc.
  now apply Nat.eq_add_0 in Hit1.
}
destruct it2. {
  apply Nat.le_0_r in Hit2.
  clear Hit1.
  remember (bsort_swap rel la) as lb eqn:Hlb; symmetry in Hlb.
  destruct lb as [lb| ]; [ | easy ].
  apply bsort_swap_Some in Hlb.
  destruct Hlb as (Hs & c & d & lc & ld & Hlb).
  destruct Hlb as (Hcd & Hrc & Hbla & Hlbc).
  rewrite Hbla in Hit2.
  exfalso; clear - Hit2 Hcd.
  induction lc as [| a]; cbn in Hit2; [ now rewrite Hcd in Hit2 | ].
  apply IHlc.
  now apply Nat.eq_add_0 in Hit2.
}
cbn.
remember (bsort_swap rel la) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [lb| ]; [ | easy ].
apply IHit1. {
  now apply bsort_swap_nb_disorder with (la := la).
} {
  now apply bsort_swap_nb_disorder with (la := la).
}
Qed.

Theorem bsort_bsort_loop_nb_disorder : ∀ A (rel : A → _),
  total_relation rel →
  ∀ l,
  bsort rel l = bsort_loop rel (nb_disorder rel l) l.
Proof.
intros * Htot *.
apply bsort_loop_enough_iter; [ easy | | easy ].
apply nb_disorder_le_square.
Qed.

Theorem bsort_loop_is_sorted_nb_disorder : ∀ A (rel : A → _),
  total_relation rel →
  ∀ it la,
  nb_disorder rel la ≤ it
  → sorted rel (bsort_loop rel it la) = true.
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

Theorem bsort_loop_is_sorted : ∀ A (rel : A → _),
  total_relation rel →
  ∀ it l,
  length l * length l ≤ it
  → sorted rel (bsort_loop rel it l) = true.
Proof.
intros * Htot * Hit.
rename l into la.
eapply le_trans in Hit. 2: {
  apply (nb_disorder_le_square rel).
}
now apply bsort_loop_is_sorted_nb_disorder.
Qed.

(* unicity of sorting algorithm *)

Theorem permutted_sorted_unique : ∀ A (rel : A → A → bool),
  reflexive rel →
  antisymmetric rel →
  transitive rel →
  ∀ la lb,
  Permutation la lb
  → sorted rel la = true
  → sorted rel lb = true
  → la = lb.
Proof.
intros * Hrefl Hant Htra * Hpab Hsa Hsb.
revert lb Hpab Hsb.
induction la as [| a]; intros; [ now apply Permutation_nil in Hpab | ].
destruct lb as [| b]; intros. {
  now apply Permutation_sym, Permutation_nil in Hpab.
}
move b before a; move lb before la; move Hsb before Hsa.
apply (sorted_strongly_sorted Htra) in Hsa, Hsb.
cbn in Hsa, Hsb.
apply Bool.andb_true_iff in Hsa, Hsb.
destruct Hsa as (Hla, Hsa).
destruct Hsb as (Hlb, Hsb).
move Hlb before Hla.
assert (Hab : a = b). {
  apply Hant. {
    apply all_sorted_forall with (l := a :: la). 2: {
      apply Permutation_in with (l := b :: lb); [ | now left ].
      now apply Permutation_sym.
    }
    now cbn; rewrite Hrefl, Hla.
  } {
    apply all_sorted_forall with (l := b :: lb). 2: {
      apply Permutation_in with (l := a :: la); [ | now left ].
      easy.
    }
    now cbn; rewrite Hrefl, Hlb.
  }
}
subst b; f_equal.
apply Permutation_cons_inv in Hpab.
apply IHla; [ | easy | ]. {
  now apply strongly_sorted_sorted.
} {
  now apply strongly_sorted_sorted.
}
Qed.

Theorem sorted_unique : ∀ A (rel : A → A → bool),
  reflexive rel →
  antisymmetric rel →
  transitive rel →
  ∀ (s1 s2 : list A → _),
  (∀ l, Permutation (s1 l) l ∧ sorted rel (s1 l) = true)
  → (∀ l, Permutation (s2 l) l ∧ sorted rel (s2 l) = true)
  → ∀ l, s1 l = s2 l.
Proof.
intros * Href Hant Htra * Hps1 Hps2 l.
apply (permutted_sorted_unique Href Hant Htra); [ | apply Hps1 | apply Hps2 ].
specialize (Hps1 l) as H1.
specialize (Hps2 l) as H2.
transitivity l; [ easy | ].
now apply Permutation_sym.
Qed.

Theorem sorted_middle : ∀ A rel (a b : A) la lb lc,
  transitive rel
  → sorted rel (la ++ a :: lb ++ b :: lc) = true
  → rel a b = true.
Proof.
intros * Htrans Hsort.
replace (la ++ a :: lb ++ b :: lc) with (la ++ [a] ++ lb ++ [b] ++ lc)
  in Hsort by easy.
rewrite app_assoc in Hsort.
apply sorted_app in Hsort.
destruct Hsort as (Hla & Hsort & H1).
specialize (H1 Htrans).
apply H1; [ now apply in_or_app; right; left | ].
apply in_or_app; right.
now apply in_or_app; left; left.
Qed.

Theorem sorted_any : ∀ A (rel : A → A → bool) i j d l,
  transitive rel
  → sorted rel l = true
  → i < j
  → j < length l
  → rel (nth i l d) (nth j l d) = true.
Proof.
intros * Htrans Hsort Hij Hj.
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

Theorem sorted_ltb_leb_incl : ∀ l,
  sorted Nat.ltb l = true → sorted Nat.leb l = true.
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

Theorem nth_isort_rank_loop_of_nodup_sorted : ∀ A d (rel : A → _),
  antisymmetric rel
  → transitive rel
  → ∀ l_ini n l i,
  NoDup l_ini
  → sorted rel l_ini = true
  → n + length l = length l_ini
  → i < length l_ini
  → nth i (isort_rank_loop rel (λ j, nth j l_ini d) (seq 0 n) l) 0 = i.
Proof.
intros * Hant Htra * Hndi Hsi Hnl Hil.
revert n Hnl.
induction l; intros; cbn. {
  rewrite seq_nth; [ easy | ].
  now rewrite Nat.add_0_r in Hnl; subst n.
}
rewrite seq_length.
replace (isort_rank_insert _ _ _ _) with (seq 0 (S n)). 2: {
  symmetry.
  rewrite nth_isort_rank_insert_of_sorted; try easy. {
    symmetry; apply seq_S.
  }
  intros j Hj.
  apply in_seq in Hj.
  destruct Hj as (_, Hj); cbn in Hj.
  enough (H : rel (nth j l_ini d) (nth n l_ini d) = true). {
    specialize (Hant (nth j l_ini d) (nth n l_ini d) H) as H1.
    apply Bool.not_true_is_false.
    intros H'.
    specialize (H1 H').
    clear H H'.
    apply NoDup_nth in H1; [ | easy | | ]; cycle 1. {
      rewrite <- Hnl; cbn; flia Hj.
    } {
      rewrite <- Hnl; cbn; flia.
    }
    flia Hj H1.
  }
  apply sorted_any; [ easy | easy | easy | ].
  rewrite <- Hnl; cbn; flia.
}
cbn in Hnl.
rewrite <- Nat.add_succ_comm in Hnl.
now apply IHl.
Qed.

Theorem nth_isort_rank_of_nodup_sorted : ∀ A (rel : A → _),
  antisymmetric rel
  → transitive rel
  → ∀ l i,
  NoDup l
  → sorted rel l = true
  → i < length l
  → nth i (isort_rank rel l) 0 = i.
Proof.
intros * Hant Htra * Hnd Hs Hil.
destruct l as [| d]; [ easy | ].
cbn - [ isort_rank_loop nth ].
remember (d :: l) as l' eqn:Hl'.
clear l Hl'; rename l' into l.
replace [] with (seq 0 0) by easy.
now apply nth_isort_rank_loop_of_nodup_sorted.
Qed.

Theorem isort_rank_of_nodup_sorted : ∀ A (rel : A → _),
  antisymmetric rel
  → transitive rel
  → ∀ l,
  NoDup l
  → sorted rel l = true
  → isort_rank rel l = seq 0 (length l).
Proof.
intros * Hant Htra * Hnd Hs.
apply List_eq_iff.
rewrite isort_rank_length, seq_length.
split; [ easy | ].
intros d i.
destruct (lt_dec i (length l)) as [Hil| Hil]. 2: {
  apply Nat.nlt_ge in Hil.
  rewrite nth_overflow; [ | now rewrite isort_rank_length ].
  rewrite nth_overflow; [ | now rewrite seq_length ].
  easy.
}
rewrite seq_nth; [ cbn | easy ].
rewrite nth_indep with (d' := 0); [ | now rewrite isort_rank_length ].
clear d.
now apply nth_isort_rank_of_nodup_sorted.
Qed.

Theorem Permutation_bsort_loop : ∀ A (rel : A → _),
  ∀ la it, Permutation la (bsort_loop rel it la).
Proof.
intros.
revert la.
induction it; intros; [ easy | cbn ].
remember (bsort_swap rel la) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [lb| ]; [ | easy ].
apply bsort_swap_Some in Hlb.
destruct Hlb as (Hs & c & d & lc & ld & Hlb).
destruct Hlb as (Hcd & Hrc & Hbla & Hlbc).
transitivity lb; [ | apply IHit ].
subst la lb.
apply Permutation_app_head.
constructor.
Qed.

(* *)

Theorem sorted_isort : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  ∀ l,
  sorted rel l = true
  → isort rel l = l.
Proof.
intros * Hant Htra * Hs.
now apply sorted_isort_loop.
Qed.

Theorem sorted_ssort : ∀ A (rel : A → _),
  transitive rel →
  ∀ l,
  sorted rel l = true
  → ssort rel l = l.
Proof.
intros * Htr * Hs.
unfold ssort.
now apply sorted_ssort_loop.
Qed.

Theorem sorted_bsort : ∀ A (rel : A → _),
  ∀ l,
  sorted rel l = true
  → bsort rel l = l.
Proof.
intros * Hs.
now apply sorted_bsort_loop.
Qed.

(* *)

Theorem isort_is_sorted : ∀ A (rel : A → _),
  total_relation rel
  → ∀ l, sorted rel (isort rel l) = true.
Proof.
intros * Hto *.
destruct l as [| a]; [ easy | cbn ].
now apply isort_loop_is_sorted.
Qed.

Theorem ssort_is_sorted : ∀ A (rel : A → _),
  transitive rel →
  total_relation rel →
  ∀ l, sorted rel (ssort rel l) = true.
Proof.
intros * Htr Htot *.
now apply ssort_loop_is_sorted.
Qed.

Theorem bsort_is_sorted : ∀ A (rel : A → _),
  total_relation rel →
  ∀ l, sorted rel (bsort rel l) = true.
Proof.
intros * Htot *.
unfold bsort.
now apply bsort_loop_is_sorted.
Qed.

(* *)

Theorem Permutation_isort : ∀ A (rel : A → _) l, Permutation l (isort rel l).
Proof.
intros.
destruct l as [| a]; [ easy | cbn ].
specialize Permutation_isort_loop as H1.
apply (H1 _ rel [a] l).
Qed.

Theorem Permutation_ssort : ∀ A (rel : A → _) l, Permutation l (ssort rel l).
Proof.
intros.
destruct l as [| a]; [ easy | ].
specialize (Permutation_ssort_loop rel) as H1.
now apply H1 with (len := length (a :: l)).
Qed.

Theorem Permutation_bsort : ∀ A (rel : A → _) l, Permutation l (bsort rel l).
Proof.
intros.
now apply Permutation_bsort_loop.
Qed.

(* isort and ssort return same *)

Theorem isort_ssort : ∀ (A : Type) (rel : A → A → bool),
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ l, isort rel l = ssort rel l.
Proof.
intros * Hant Htra Htot *.
specialize (total_relation_is_reflexive Htot) as Href.
apply (sorted_unique Href Hant Htra). {
  clear l; intros l.
  split; [ | now apply isort_is_sorted ].
  apply Permutation_sym, Permutation_isort.
} {
  clear l; intros l.
  split; [ | now apply ssort_is_sorted ].
  apply Permutation_sym, Permutation_ssort.
}
Qed.

(* ssort and bsort return same *)

Theorem ssort_bsort : ∀ (A : Type) (rel : A → A → bool),
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ l, ssort rel l = bsort rel l.
Proof.
intros * Hant Htra Htot *.
specialize (total_relation_is_reflexive Htot) as Href.
apply (sorted_unique Href Hant Htra). {
  clear l; intros l.
  split; [ | now apply ssort_is_sorted ].
  now apply Permutation_sym, Permutation_ssort.
} {
  clear l; intros l.
  split; [ | now apply bsort_is_sorted ].
  now apply Permutation_sym, Permutation_bsort.
}
Qed.

(* bsort and isort return same *)

Theorem bsort_isort : ∀ (A : Type) (rel : A → A → bool),
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ l, bsort rel l = isort rel l.
Proof.
intros * Hant Htra Htot *.
specialize (total_relation_is_reflexive Htot) as Href.
apply (sorted_unique Href Hant Htra). {
  clear l; intros l.
  split; [ | now apply bsort_is_sorted ].
  now apply Permutation_sym, Permutation_bsort.
} {
  clear l; intros l.
  split; [ | now apply isort_is_sorted ].
  apply Permutation_sym, Permutation_isort.
}
Qed.

(* *)

Theorem Nat_leb_is_total_relation : total_relation Nat.leb.
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

Theorem Nat_leb_refl : reflexive Nat.leb.
Proof.
intros a.
apply Nat.leb_refl.
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

Theorem Nat_ltb_trans : transitive Nat.ltb.
Proof.
intros a b c Hab Hbc.
apply Nat.ltb_lt in Hab, Hbc.
apply Nat.ltb_lt.
now transitivity b.
Qed.
