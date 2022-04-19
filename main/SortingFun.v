(* Sorting algorithms : bubble, selection, insertion, merge *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Permutation.
Import List List.ListNotations.

Require Import Misc PermutationFun.

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

Fixpoint msort_loop {A} (rel : A → A → bool) it la :=
  match it with
  | 0 => la
  | S it' =>
      let (l1, l2) := split la in
      let l3 := msort_loop rel it' l1 in
      let l4 := msort_loop rel it' l2 in
      merge rel l3 l4
  end.

Definition msort {A} (rel : A → _) la :=
  msort_loop rel (length la) la.

(*
Compute (msort Nat.leb [7;5;3;22;8]).
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
Compute (map (λ l, msort Nat.leb l) (canon_sym_gr_list_list 5)).
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

Fixpoint split_inv {A} (la lb : list A) :=
  match la, lb with
  | _, [] => la
  | [], _ => lb
  | a :: la, b :: lb => a :: b :: split_inv la lb
  end.

Theorem split_split_inv : ∀ A (la lb : list A),
  (length la = length lb ∨ length la = S (length lb))
  → split (split_inv la lb) = (la, lb).
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

Theorem split_lengths : ∀ A (l la lb : list A),
  split l = (la, lb)
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
remember (split l) as ll eqn:H; symmetry in H.
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
remember (split la) as ll eqn:Hll; symmetry in Hll.
destruct ll as (lb, lc).
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

Theorem sorted_cons_cons_split' : ∀ A (rel : A → _),
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

Theorem sorted_split : ∀ A (rel : A → _),
  transitive rel →
  ∀ la lb l,
  sorted rel l = true
  → split l = (la, lb)
  → sorted rel la = true ∧ sorted rel lb = true.
Proof.
intros * Htra * Hs Hla.
destruct l as [| a]; [ now injection Hla; intros; subst la lb | ].
destruct l as [| b]; [ now injection Hla; intros; subst la lb | ].
cbn in Hla.
remember (split l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hla; clear Hla; intros; subst la lb.
now apply sorted_cons_cons_split' with (l := l).
Qed.

Theorem sorted_merge_loop_cons_cons_r_aux : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  ∀ n it l la lb a b,
  length (repeat a (n + n) ++ a :: b :: l) ≤ n + it
  → rel a a = true
  → sorted rel (a :: b :: l) = true
  → split l = (la, lb)
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
remember (split l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hla; clear Hla; intros; subst la lb.
rename lc into la; rename ld into lb; rename Hlc into Hla; cbn.
remember (d :: l) as l'; cbn in Hs; subst l'.
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
  cbn in Hit.
  cbn - [ merge_loop sorted ] in H1.
  assert (H : S (S (S (length l))) ≤ it) by flia Hit.
  specialize (H1 H Haa); clear H.
  assert (H : sorted rel (a :: b :: l) = true). {
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
  now rewrite Hcd, Hs.
} {
  f_equal.
  rewrite IHit with (l := c :: d :: l); [ | flia Hit | easy | | ]; cycle 1. {
    remember (d :: l) as l'; cbn; subst l'.
    now rewrite Hab, Hbc, Hcd, Hs.
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
   → sorted rel (a :: b :: l) = true
   → split l = (la, lb)
   → merge_loop rel it la (a :: b :: lb) =
     merge_loop rel it (a :: la) (b :: lb).
Proof.
intros * Hant Htra * Hit Haa Hs Hll.
specialize (sorted_merge_loop_cons_cons_r_aux Hant Htra 0) as H1.
cbn - [ sorted ] in H1.
now apply (H1 it l).
Qed.

Theorem sorted_merge_loop_cons_cons : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  ∀ it l la lb a b,
  length l ≤ it
  → sorted rel (a :: b :: l) = true
  → split l = (la, lb)
  → merge_loop rel (S (S it)) (a :: la) (b :: lb) =
    a :: b :: merge_loop rel it la lb.
Proof.
intros * Hant Htra * Hit Hs Hla.
remember (S it) as sit; cbn; subst sit.
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
remember (split l) as lc eqn:Hlc; symmetry in Hlc.
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
  sorted rel (a :: b :: l) = true
  → split l = (la, lb)
  → merge rel (a :: la) (b :: lb) = a :: b :: merge rel la lb.
Proof.
intros * Hant Htra * Hs Hla.
unfold merge.
do 2 rewrite List_cons_length.
rewrite Nat.add_succ_r, Nat.add_succ_l.
apply (sorted_merge_loop_cons_cons Hant Htra l); [ | easy | easy ].
apply split_length in Hla.
now rewrite Hla.
Qed.

Theorem merge_loop_is_sorted : ∀ A (rel : A → _),
  total_relation rel →
  ∀ it la lb,
  length la + length lb ≤ it
  → sorted rel la = true
  → sorted rel lb = true
  → sorted rel (merge_loop rel it la lb) = true.
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
  assert (H : sorted rel la = true) by now apply sorted_cons in Hla.
  specialize (H1 H Hlb); clear H.
  rewrite Hlc in H1.
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
assert (H : sorted rel lb = true) by now apply sorted_cons in Hlb.
specialize (H1 Hla H); clear H.
rewrite Hlc in H1.
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
now destruct (rel b c).
Qed.

Theorem merge_is_sorted : ∀ A (rel : A → _),
  total_relation rel →
  ∀ la lb,
  sorted rel la = true
  → sorted rel lb = true
  → sorted rel (merge rel la lb) = true.
Proof.
intros * Htot * Hla Hlb.
unfold merge.
now apply merge_loop_is_sorted.
Qed.

Theorem msort_loop_is_sorted : ∀ A (rel : A → _),
  total_relation rel →
  ∀ l it,
  length l ≤ it
  → sorted rel (msort_loop rel it l) = true.
Proof.
intros * Htot * Hit.
revert l Hit.
induction it; intros; cbn. {
  now apply Nat.le_0_r, length_zero_iff_nil in Hit; subst l.
}
remember (split l) as la eqn:Hla; symmetry in Hla.
destruct la as (la, lb).
destruct l as [| a]. {
  injection Hla; clear Hla; intros; subst la lb; cbn.
  now rewrite msort_loop_nil.
}
destruct l as [| b]. {
  injection Hla; clear Hla; intros; subst la lb; cbn.
  now rewrite msort_loop_single, msort_loop_nil.
}
cbn in Hla.
remember (split l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hla; clear Hla; intros; subst la lb.
cbn in Hit.
apply Nat.succ_le_mono in Hit.
apply split_length in Hlc.
apply merge_is_sorted; [ easy | | ]. {
  apply IHit; cbn; flia Hit Hlc.
} {
  apply IHit; cbn; flia Hit Hlc.
}
Qed.

Theorem fold_merge : ∀ A (rel : A → _) la lb,
  merge_loop rel (length la + length lb) la lb = merge rel la lb.
Proof. easy. Qed.

Theorem sorted_merge_loop : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  ∀ it l la lb,
  length l ≤ it
  → sorted rel l = true
  → split l = (la, lb)
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
remember (split l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hll; clear Hll; intros; subst la lb.
rename lc into la; rename ld into lb; rename Hlc into Hll.
destruct it; [ cbn in Hit; flia Hit | ].
cbn.
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
remember (split l) as lc eqn:Hlc; symmetry in Hlc.
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
    now rewrite Hab, Hs.
  }
  replace it with (S (S (it - 2))) by flia Hit.
  rewrite sorted_merge_loop_cons_cons with (l := l); try easy; cycle 1. {
    flia Hit.
  } {
    remember (b :: l) as l'; cbn; subst l'.
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
  now rewrite Hbc, Hs.
}
cbn.
now rewrite Hll.
Qed.

Theorem sorted_merge : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  ∀ l la lb,
  sorted rel l = true
  → split l = (la, lb)
  → merge rel la lb = l.
Proof.
intros * Hant Htra * Hs Hll.
unfold merge.
apply (sorted_merge_loop Hant Htra); [ | easy | easy ].
apply split_length in Hll.
now rewrite Hll.
Qed.

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
induction it; intros; [ easy | cbn ].
remember (split l) as la eqn:Hla; symmetry in Hla.
destruct la as (la, lb).
destruct l as [| a]. {
  injection Hla; intros; subst la lb.
  now rewrite msort_loop_nil.
}
destruct l as [| b]. {
  injection Hla; clear Hla; intros; subst la lb.
  now rewrite msort_loop_single, msort_loop_nil.
}
cbn in Hla.
remember (split l) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as (lc, ld).
injection Hla; clear Hla; intros; subst la lb.
rename lc into la; rename ld into lb; rename Hlc into Hla.
cbn in Hit.
apply Nat.succ_le_mono in Hit.
rewrite IHit; cycle 1. {
  apply split_length in Hla.
  cbn; flia Hit Hla.
} {
  now apply sorted_cons_cons_split' with (la := la) (lb := lb) in Hs.
}
rewrite IHit; cycle 1. {
  apply split_length in Hla.
  cbn; flia Hit Hla.
} {
  now apply sorted_cons_cons_split' with (la := la) (lb := lb) in Hs.
}
rewrite sorted_merge_cons_cons with (l := l); [ | easy | easy | easy | easy ].
f_equal; f_equal.
do 2 apply sorted_cons in Hs.
now apply sorted_merge.
Qed.

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

Theorem in_isort_insert_id : ∀ A (rel : A → _) a l,
  a ∈ isort_insert rel a l.
Proof.
intros.
induction l as [| b]; [ now left | cbn ].
now destruct (rel a b); [ left | right ].
Qed.

(* to be completed
Theorem permutation_cons_isort_insert : ∀ A (eqb rel : A → _),
  equality eqb →
  ∀ a la lb,
  is_permutation eqb la lb = true
  → is_permutation eqb (a :: la) (isort_insert rel a lb) = true.
Proof.
intros * Heqb * Hab; cbn.
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
...
replace (bef ++ aft) with lb; [ easy | ].
clear Hab Hbef la.
revert a bef aft Hli.
induction lb as [| b]; intros; cbn. {
  cbn in Hli.
  symmetry in Hli.
  apply app_eq_unit in Hli.
  destruct Hli as [(H1, H2)| ]; [ | easy ].
  now injection H2; clear H2; intros; subst bef aft.
}
cbn in Hli.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. 2: {
  destruct bef as [| c]. {
    cbn in Hli |-*.
    injection Hli; clear Hli; intros Hli H; subst b.
    clear IHlb.
    clear Hab.
    revert a aft Hli.
    induction lb as [| c]; intros; [ easy | ].
    cbn in Hli.
    remember (rel a c) as ac eqn:Hac; symmetry in Hac.
    destruct ac; [ easy | ].
    destruct aft as [| b]; [ easy | ].
    injection Hli; clear Hli; intros Hli H; subst c.
    specialize (IHlb a aft Hli) as H1.
    rewrite <- H1.
...
intros * Heqb * Hab.
revert a lb Hab.
induction la as [| b]; intros; cbn in Hab |-*. {
  destruct lb; [ cbn | easy ].
  now rewrite (equality_refl Heqb).
}
remember (extract (eqb a) (isort_insert rel a lb)) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl a) as H1.
  specialize (equality_refl Heqb a) as H2.
  apply Bool.not_false_iff_true in H2.
  exfalso; apply H2, H1.
  clear.
  induction lb as [| b]; [ now left | cbn ].
  now destruct (rel a b); [ left | right ].
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hli).
apply Heqb in H; subst x.
remember (extract (eqb b) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef', x), aft')| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef' & H & Hlb).
apply Heqb in H; subst x.
subst lb.
...
enough (H : is_permutation eqb (b :: la) (bef' ++ b :: aft') = true).
Check Permutation_cons_app.
cbn in H.
...
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef' & H & Hlb).
apply Heqb in H; subst x.
remember (extract (eqb b) (bef ++ aft)) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef'', x), aft'')| ]. 2: {
  specialize (extract_None_iff _ _ Hlxl) as H1.
  assert (Ha : a ∉ bef). {
    intros Ha.
    specialize (Hbef _ Ha) as H2.
    now rewrite (equality_refl Heqb) in H2.
  }
...
  remember (eqb b a) as eba eqn:Heba; symmetry in Heba.
  destruct eba. {
...
  specialize (equality_refl Heqb a) as H2.
  apply Bool.not_false_iff_true in H2.
  exfalso; apply H2, H1.
  clear.
  induction lb as [| b]; [ now left | cbn ].
  now destruct (rel a b); [ left | right ].
...
specialize (IHla a _ Hab) as H1; cbn in H1.
specialize (IHla b _ Hab) as H2; cbn in H2.
remember (extract (eqb a) (isort_insert rel a lb)) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef', x), aft')| ]. {
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef' & H & Hli).
  apply Heqb in H; subst x.
  remember (extract (eqb b) (bef' ++ aft')) as lxl eqn:Hlxl.
  symmetry in Hlxl.
  destruct lxl as [((bef'', x), aft'')| ]. {
    apply extract_Some_iff in Hlxl.
    destruct Hlxl as (Hbef'' & H & Hli').
    apply Heqb in H; subst x.
    move bef' before bef; move bef'' before bef'.
    move aft' before aft; move aft'' before aft'.
    move Hbef' before Hbef; move Hbef'' before Hbef'.
    subst lb.
    assert (Hb : b ∈ bef' ++ aft'). {
      rewrite Hli'.
      now apply in_or_app; right; left.
    }
    apply in_app_or in Hb.
    destruct Hb as [Hb| Hb]. {
      specialize (Hbef' b Hb) as H3.
...
    specialize (IHla a _ Hab) as H1.
    remember (extract (eqb b) (bef' ++ aft')) as lxl eqn:Hlxl.
    symmetry in Hlxl.
...
*)

Theorem permutation_cons_isort_insert' : ∀ A (eqb rel : A → _),
  equality eqb →
  ∀ a la lb,
  is_permutation eqb la lb = true
  → is_permutation eqb (a :: la) (isort_insert rel a lb) = true.
Proof.
intros * Heqb * Hab.
apply Permutation_permutation in Hab; [ | easy ].
apply Permutation_permutation; [ easy | ].
now apply Permutation_cons_isort_insert.
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

Theorem sorted_msort : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ l,
  sorted rel l = true
  → msort rel l = l.
Proof.
intros * Hant Htra Htot * Hs.
unfold msort.
now apply sorted_msort_loop.
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
now apply bsort_loop_is_sorted.
Qed.

Theorem msort_is_sorted : ∀ A (rel : A → _),
  total_relation rel →
  ∀ l, sorted rel (msort rel l) = true.
Proof.
intros * Htot *.
now apply msort_loop_is_sorted.
Qed.

(* *)

Theorem Permutation_isort : ∀ A (rel : A → _) l, Permutation l (isort rel l).
Proof.
intros.
apply (Permutation_isort_loop rel [] l).
Qed.

Theorem Permutation_ssort : ∀ A (rel : A → _) l, Permutation l (ssort rel l).
Proof.
intros.
now apply Permutation_ssort_loop.
Qed.

Theorem Permutation_bsort : ∀ A (rel : A → _) l, Permutation l (bsort rel l).
Proof.
intros.
apply Permutation_bsort_loop.
Qed.

(* to be completed
Theorem Permutation_merge_loop : ∀ A (rel : A → _) it l la lb,
  length l ≤ it
  → split l = (la, lb)
  → Permutation l (merge_loop rel it la lb).
Proof.
intros * Hit Hll.
...
intros * Hit Hll.
destruct it. {
  now apply Nat.le_0_r, length_zero_iff_nil in Hit; subst l.
}
destruct l as [| a]; [ now injection Hll; intros; subst la lb | ].
destruct l as [| b]; [ now injection Hll; intros; subst la lb | ].
cbn in Hll.
remember (split l) as ll eqn:H; symmetry in H.
destruct ll as (lc, ld).
injection Hll; clear Hll; intros; subst la lb.
rename lc into la; rename ld into lb; rename H into Hll.
cbn in Hit; apply Nat.succ_le_mono in Hit.
cbn.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  constructor.
  destruct it; [ easy | ].
  apply Nat.succ_le_mono in Hit.
  clear a Hab.
(**)
  destruct l as [| a]; [ now injection Hll; intros; subst la lb | ].
  destruct l as [| c]. {
    injection Hll; clear Hll; intros; subst la lb; cbn.
    remember (rel a b) as ab eqn:Hab; symmetry in Hab.
    destruct ab. {
      destruct it; [ easy | constructor ].
    }
    constructor.
    destruct it; [ easy | now constructor ].
  }
  cbn in Hll.
  remember (split l) as ll eqn:H; symmetry in H.
  destruct ll as (lc, ld).
  injection Hll; clear Hll; intros; subst la lb.
  rename lc into la; rename ld into lb; rename H into Hll; cbn.
  remember (rel a b) as ab eqn:Hab; symmetry in Hab.
  destruct ab. {
    transitivity (a :: b :: c :: l); [ constructor | ].
    constructor.
    cbn in Hit.
    clear a Hab.
    rename b into a; rename c into b.
    destruct l as [| c]. {
      injection Hll; intros; subst la lb.
      destruct it; [ cbn in Hit; flia Hit | easy ].
    }
    destruct l as [| d]. {
      injection Hll; clear Hll; intros; subst la lb; cbn.
      destruct it; [ easy | cbn ].
      apply Nat.succ_le_mono in Hit.
      remember (rel c a) as ca eqn:Hca; symmetry in Hca.
      destruct ca. {
        destruct it; [ easy | cbn ].
        apply Permutation_sym.
        transitivity [a; c; b]; constructor; constructor.
      }
      constructor.
      destruct it; [ easy | cbn ].
      apply Nat.succ_le_mono in Hit.
      remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
      destruct cb. {
        destruct it; [ cbn in Hit; flia Hit | constructor ].
      }
      constructor.
      destruct it; [ cbn in Hit; flia Hit | now constructor ].
    }
    cbn in Hll.
    destruct it; [ cbn in Hit; flia Hit | ].
    cbn in Hit; apply Nat.succ_le_mono in Hit.
    remember (split l) as ll eqn:H; symmetry in H.
    destruct ll as (lc, ld).
    injection Hll; clear Hll; intros; subst la lb.
    rename lc into la; rename ld into lb; rename H into Hll; cbn.
    remember (rel c a) as ca eqn:Hca; symmetry in Hca.
    destruct ca. {
      transitivity (c :: a :: b :: d :: l). {
        replace (a :: b :: c :: d :: l) with ([a; b; c] ++ (d :: l))
          by easy.
        replace (c :: a :: b :: d :: l) with ([c; a; b] ++ (d :: l))
          by easy.
        apply Permutation_app_tail.
        apply Permutation_sym.
        transitivity [a; c; b]; constructor.
        constructor.
      }
      constructor.
      clear c Hca.
      rename d into c.
      destruct it; [ easy | cbn ].
      apply Nat.succ_le_mono in Hit.
      remember (split l) as ll eqn:H; symmetry in H.
      destruct ll as (lc, ld).
      injection Hll; clear Hll; intros; subst la lb.
      rename lc into la; rename ld into lb; rename H into Hll; cbn.
      destruct l as [| d]. {
        now injection Hll; intros; subst la lb; destruct it.
      }
      cbn in Hit.
      destruct l as [| e]. {
        injection Hll; intros; clear Hll; subst la lb.
        remember (rel d a) as da eqn:Hda; symmetry in Hda.
        destruct da. {
          destruct it; [ easy | cbn ].
          apply Permutation_sym.
          transitivity [a; d; b; c]; constructor.
          transitivity [b; d; c]; constructor.
          constructor.
        }
        destruct it; [ easy | ].
        apply Nat.succ_le_mono in Hit.
        constructor; cbn.
        remember (rel d b) as db eqn:Hdb; symmetry in Hdb.
        destruct db. {
          destruct it; [ easy | cbn ].
          apply Nat.succ_le_mono in Hit.
          apply Permutation_sym.
          transitivity [b; d; c]; constructor.
          constructor.
        }
        constructor.
        destruct it; [ easy | cbn ].
        apply Nat.succ_le_mono in Hit.
        remember (rel d c) as dc eqn:Hdc; symmetry in Hdc.
        destruct dc; [ | now destruct it ].
        destruct it; [ easy | constructor ].
      }
      cbn in Hit, Hll.
      remember (split l) as ll eqn:H; symmetry in H.
      destruct ll as (lc, ld).
      injection Hll; clear Hll; intros; subst la lb.
      rename lc into la; rename ld into lb; rename H into Hll; cbn.
      remember (rel d a) as da eqn:Hda; symmetry in Hda.
      destruct da. {
...
  destruct l as [| c]; [ now injection Hll; intros; subst la lb | ].
  destruct l as [| d]. {
    injection Hll; clear Hll; intros; subst la lb; cbn.
    remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
    destruct cb. {
      destruct it; [ easy | constructor ].
    }
    constructor.
    destruct it; [ easy | now constructor ].
  }
  cbn in Hll.
  remember (split l) as ll eqn:H; symmetry in H.
  destruct ll as (lc, ld).
  injection Hll; clear Hll; intros; subst la lb.
  rename lc into la; rename ld into lb; rename H into Hll; cbn.
  remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
  destruct cb. {
    transitivity (c :: b :: d :: l); [ constructor | ].
    constructor.
...
intros * Hit Hll.
revert l la lb Hit Hll.
induction it as (it, IHit) using lt_wf_rec; intros.
destruct it. {
  now apply Nat.le_0_r, length_zero_iff_nil in Hit; subst l.
}
destruct l as [| a]; [ now injection Hll; intros; subst la lb | ].
destruct l as [| b]; [ now injection Hll; intros; subst la lb | ].
cbn in Hll.
remember (split l) as ll eqn:H; symmetry in H.
destruct ll as (lc, ld).
injection Hll; clear Hll; intros; subst la lb.
rename lc into la; rename ld into lb; rename H into Hll.
cbn in Hit; apply Nat.succ_le_mono in Hit.
cbn.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  constructor.
  destruct it; [ easy | ].
(* apply IHit. marche pas *)
  apply Nat.succ_le_mono in Hit.
  destruct l as [| c]; [ now injection Hll; intros; subst la lb | ].
  destruct l as [| d]. {
    injection Hll; clear Hll; intros; subst la lb; cbn.
    remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
    destruct cb. {
      destruct it; [ easy | constructor ].
    }
    constructor.
    destruct it; [ easy | now constructor ].
  }
  cbn in Hll.
  remember (split l) as ll eqn:H; symmetry in H.
  destruct ll as (lc, ld).
  injection Hll; clear Hll; intros; subst la lb.
  rename lc into la; rename ld into lb; rename H into Hll; cbn.
  remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
  destruct cb. {
    transitivity (c :: b :: d :: l); [ constructor | ].
    constructor.
(* apply IHit. marche pas *)
...
intros * Hit Hll.
remember (length l) as len eqn:Hlen.
rewrite Hlen in Hit.
revert it l la lb Hlen Hit Hll.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct l as [| a]. {
  now injection Hll; intros; subst la lb; destruct it.
}
destruct l as [| b]. {
  now injection Hll; intros; subst la lb; destruct it.
}
cbn in Hll.
remember (split l) as ll eqn:H; symmetry in H.
destruct ll as (lc, ld).
injection Hll; clear Hll; intros; subst la lb.
rename lc into la; rename ld into lb; rename H into Hll.
cbn in Hit.
destruct it; [ easy | apply Nat.succ_le_mono in Hit ].
destruct it; [ easy | apply Nat.succ_le_mono in Hit ].
remember (S it) as it'; cbn; subst it'.
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  constructor; cbn in Hlen.
  destruct len; [ easy | apply Nat.succ_inj in Hlen ].
  destruct len; [ easy | apply Nat.succ_inj in Hlen ].
  specialize (IHlen len) as H1.
  assert (H : len < S (S len)) by now transitivity (S len).
  specialize (H1 H it); clear H.
  specialize (H1 l la lb Hlen Hit Hll).
  cbn.
  destruct l as [| c]. {
    now injection Hll; intros; subst la lb.
  }
  destruct l as [| d]. {
    injection Hll; intros; subst la lb.
    remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
    destruct cb; [ | now destruct it ].
    destruct it; [ | constructor ].
    now apply Permutation_sym, Permutation_nil in H1.
  }
  cbn in Hll.
  remember (split l) as ll eqn:H; symmetry in H.
  destruct ll as (lc, ld).
  injection Hll; clear Hll; intros; subst la lb.
  rename lc into la; rename ld into lb; rename H into Hll.
  cbn in Hit.
  remember (rel c b) as cb eqn:Hcb; symmetry in Hcb.
  destruct cb. {
    destruct it; [ easy | ].
    apply Nat.succ_le_mono in Hit.
    apply perm_trans with (l' := c :: b :: d :: l); [ constructor | ].
    constructor.
    cbn in H1.
... ça, c'est pas bon, ci-dessous
    apply (IHlen len).
...
  destruct cb; [ now destruct it | ].
    destruct it; [ | constructor ].
    now apply Permutation_sym, Permutation_nil in H1.
...

Theorem Permutation_merge : ∀ A (rel : A → _) l la lb,
  split l = (la, lb)
  → Permutation l (merge rel la lb).
Proof.
intros * Hll.
unfold merge.
rewrite <- (split_length l); [ | easy ].
...
now apply Permutation_merge_loop.
...

Theorem Permutation_msort : ∀ A (rel : A → _) l, Permutation l (msort rel l).
Proof.
intros.
unfold msort.
Theorem Permutation_msort_loop : ∀ A (rel : A → _) it l,
  length l ≤ it
  → Permutation l (msort_loop rel it l).
Proof.
intros * Hit.
revert l Hit.
induction it; intros; [ easy | cbn ].
remember (split l) as la eqn:Hll; symmetry in Hll.
destruct la as (la, lb).
destruct l as [| a]. {
  injection Hll; intros; subst la lb.
  now rewrite msort_loop_nil.
}
destruct l as [| b]. {
  injection Hll; intros; subst la lb.
  now rewrite msort_loop_single, msort_loop_nil.
}
cbn in Hll.
remember (split l) as lc eqn:Hll'; symmetry in Hll'.
destruct lc as (lc, ld).
injection Hll; clear Hll; intros; subst la lb.
rename lc into la; rename ld into lb; rename Hll' into Hll.
cbn in Hit; apply Nat.succ_le_mono in Hit.
remember (msort_loop rel it (a :: la)) as lc eqn:Hlc.
remember (msort_loop rel it (b :: lb)) as ld eqn:Hld.
...
destruct l as [| a]. {
  injection Hs; intros; subst la lb.
  now apply Permutation_nil in Hac, Hbd; subst lc ld.
}
...
transitivity (split_inv lc ld). 2: {
  apply Permutation_merge.
  apply split_split_inv.
  subst lc ld.
  do 2 rewrite msort_loop_length; cbn; f_equal.
  apply split_lengths in Hll.
  now destruct Hll as [Hll| Hll]; rewrite Hll; [ left | right ].
}
...
apply (Permutation_merge rel) with (la := a :: la) (lb := b :: lb); cycle 1. {
  apply split_length in Hll.
  apply IHit; cbn; flia Hit Hll.
} {
  apply split_length in Hll.
  apply IHit; cbn; flia Hit Hll.
}
now cbn; rewrite Hll.
...
Qed.
*)

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
