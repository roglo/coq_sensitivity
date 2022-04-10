(* Sorted by relation functions *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Permutation.
Import List List.ListNotations.

Require Import Misc.

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

Theorem sorted_app_iff : ∀ A rel,
  transitive rel →
  ∀ (la lb : list A),
  sorted rel (la ++ lb) = true
  ↔ sorted rel la = true ∧ sorted rel lb = true ∧
    (∀ a b, a ∈ la → b ∈ lb → rel a b = true).
Proof.
intros * Htra *.
split. {
  intros Hab.
  apply sorted_app in Hab.
  split; [ easy | ].
  split; [ easy | ].
  intros a b Ha Hb.
  now apply Hab.
} {
  intros (Ha & Hb & Hab).
  revert lb Hb Hab.
  induction la as [| a] using rev_ind; intros; [ easy | cbn ].
  rewrite <- app_assoc; cbn.
  apply IHla. {
    now apply sorted_app in Ha.
  } {
    cbn.
    destruct lb as [| b]; [ easy | ].
    rewrite Hab; cycle 1. {
      now apply in_or_app; right; left.
    } {
      now left.
    }
    now rewrite Hb.
  }
  intros a' b' Ha' Hb'.
  destruct Hb' as [Hb'| Hb']. {
    apply sorted_app in Ha.
    subst b'.
    apply Ha; [ easy | easy | now left ].
  } {
    apply Hab; [ | easy ].
    now apply in_or_app; left.
  }
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

Theorem ssort_loop_length : ∀ A rel it (l : list A),
  length (ssort_loop rel it l) = length l.
Proof.
intros.
revert l.
induction it; intros; [ easy | cbn ].
destruct l as [| a]; [ easy | cbn ].
remember (select_first rel a l) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as (a', la'); cbn; f_equal.
rewrite IHit.
now apply select_first_length in Hlb.
Qed.

Theorem ssort_length : ∀ A rel (l : list A), length (ssort rel l) = length l.
Proof.
intros.
apply ssort_loop_length.
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

Theorem Permutation_isort : ∀ A (rel : A → _) l, Permutation l (isort rel l).
Proof.
intros.
induction l as [| a]; [ easy | cbn ].
specialize Permutation_isort_loop as H1.
apply (H1 _ rel [a] l).
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

Theorem ssort_loop_cons : ∀ A rel it a b (la lb : list A),
  length la ≤ it
  → select_first rel a la = (b, lb)
  → ssort_loop rel it (a :: la) = b :: ssort_loop rel it lb.
Proof.
intros * Hit Hab.
revert a b la lb Hit Hab.
induction it; intros; cbn. {
  apply Nat.le_0_r, length_zero_iff_nil in Hit; subst la.
  cbn in Hab.
  now injection Hab; clear Hab; intros; subst b lb.
}
destruct la as [| a']. {
  cbn in Hab.
  injection Hab; clear Hab; intros; subst b lb.
  now destruct it.
}
cbn in Hit.
apply Nat.succ_le_mono in Hit.
cbn in Hab |-*.
remember (rel a a') as x eqn:Hx; symmetry in Hx.
remember (select_first rel (if x then a else a') la) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as (c, lc).
injection Hab; clear Hab; intros; subst c lb.
f_equal.
remember (select_first rel (if x then a' else a) lc) as ld eqn:Hld.
symmetry in Hld.
destruct ld as (d, ld).
apply IHit; [ | easy ].
specialize select_first_length as H1.
specialize (H1 _ rel (if x then a else a') la b lc Hlc).
now rewrite H1.
Qed.

Theorem eq_ssort_loop_nil : ∀ A rel it (l : list A),
  ssort_loop rel it l = [] → l = [].
Proof.
intros * Hit.
revert l Hit.
induction it; intros; [ easy | ].
cbn in Hit.
destruct l as [| a la]; [ easy | exfalso ].
now destruct (select_first rel a la).
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

Theorem Permutation_select_first : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ a a' b' la lb la' lb',
  Permutation la lb
  → select_first rel a la = (a', la')
  → select_first rel a lb = (b', lb')
  → a' = b' ∧ Permutation la' lb'.
Proof.
intros * Hant Htr Htot * Hab Ha Hb.
revert a a' b' la' lb' Ha Hb.
induction Hab; intros. {
  cbn in Ha, Hb.
  injection Ha; intros; subst a' la'.
  injection Hb; intros; subst b' lb'.
  easy.
} {
  cbn in Ha, Hb.
  remember (rel a x) as ax eqn:Hax; symmetry in Hax.
  remember (if ax then a else x) as y eqn:Hy.
  remember (select_first rel y l) as ld eqn:Hld.
  remember (select_first rel y l') as le eqn:Hle.
  symmetry in Hld, Hle.
  destruct ld as (d, ld).
  destruct le as (e, le).
  injection Ha; clear Ha; intros; subst d la'.
  injection Hb; clear Hb; intros; subst e lb'.
  specialize (IHHab _ _ _ _ _ Hld Hle) as H1.
  split; [ easy | ].
  now apply Permutation_cons.
} {
  cbn in Ha, Hb.
  remember (if rel a y then a else y) as u eqn:Hu.
  remember (if rel a x then a else x) as v eqn:Hv.
  remember (rel u x) as ux eqn:Hux.
  remember (rel v y) as vy eqn:Hvy.
  remember (rel a x) as ax eqn:Hax.
  remember (rel a y) as ay eqn:Hay.
  symmetry in Hux, Hvy, Hax, Hay.
  move a before y; move a' before a; move b' before a'.
  move u before b'; move v before u.
  move ax after ay; move ux before ay; move vy before ux.
  remember (select_first rel (if ux then u else x) l) as ld eqn:Hld.
  remember (select_first rel (if vy then v else y) l) as le eqn:Hle.
  symmetry in Hld, Hle.
  destruct ld as (d, ld).
  destruct le as (e, le).
  injection Ha; clear Ha; intros; subst a' la'.
  injection Hb; clear Hb; intros; subst b' lb'.
  destruct ax; subst v. {
    destruct ay; subst u. {
      rewrite Hax in Hux; subst ux.
      rewrite Hay in Hvy; subst vy.
      rewrite Hld in Hle.
      injection Hle; intros; subst e le.
      split; [ easy | apply perm_swap ].
    }
    rewrite Hay in Hvy; subst vy.
    destruct ux. {
      rewrite Hld in Hle.
      injection Hle; intros; subst e le.
      split; [ easy | apply perm_swap ].
    }
    specialize (Htot y x) as H1.
    rewrite Hux in H1; cbn in H1.
    specialize (Htot a y) as H2.
    rewrite Hay in H2; cbn in H2.
    specialize (Htr x y a H1 H2) as H3.
    apply (Hant _ _ Hax) in H3; subst x.
    apply (Hant _ _ H1) in H2; subst y.
    rewrite Hld in Hle.
    now injection Hle; intros; subst e le.
  } {
    destruct ay; subst u. {
      rewrite Hax in Hux; subst ux.
      destruct vy. {
        rewrite Hld in Hle.
        injection Hle; intros; subst e le.
        split; [ easy | apply perm_swap ].
      }
      specialize (Htot x y) as H1.
      rewrite Hvy in H1; cbn in H1.
      specialize (Htot a x) as H2.
      rewrite Hax in H2; cbn in H2.
      specialize (Htr y x a H1 H2) as H3.
      apply (Hant _ _ Hay) in H3; subst y.
      apply (Hant _ _ H1) in H2; subst x.
      rewrite Hld in Hle.
      now injection Hle; intros; subst e le.
    }
    destruct ux. {
      destruct vy. {
        specialize (Hant _ _ Hux Hvy) as H1; subst y.
        rewrite Hld in Hle.
        now injection Hle; intros; subst e le.
      }
      rewrite Hld in Hle.
      now injection Hle; intros; subst e le.
    }
    destruct vy. {
      rewrite Hld in Hle.
      now injection Hle; intros; subst e le.
    }
    specialize (Htot x y) as H1.
    now rewrite Hux, Hvy in H1.
  }
} {
  remember (select_first rel a l') as lc eqn:Hlc.
  symmetry in Hlc.
  destruct lc as (c, lc).
  specialize (IHHab1 _ _ _ _ _ Ha Hlc) as H1.
  specialize (IHHab2 _ _ _ _ _ Hlc Hb) as H2.
  destruct H2 as (H3, H4).
  destruct H1 as (H1, H2).
  split; [ congruence | ].
  now transitivity lc.
}
Qed.

Theorem Permutation_ssort_loop : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ it la lb,
  length la = length lb
  → length la ≤ it
  → Permutation la lb
  → ssort_loop rel it la = ssort_loop rel it lb.
Proof.
intros * Hant Htr Htot * Hlab Hit Hab.
revert la lb Hlab Hit Hab.
induction it; intros; cbn. {
  apply Nat.le_0_r, length_zero_iff_nil in Hit; subst la.
  symmetry in Hlab.
  now apply length_zero_iff_nil in Hlab; subst lb.
}
destruct la as [| a]. {
  symmetry in Hlab.
  now apply length_zero_iff_nil in Hlab; subst lb.
}
destruct lb as [| b]; [ easy | ].
cbn in Hlab; apply Nat.succ_inj in Hlab.
cbn in Hit; apply Nat.succ_le_mono in Hit.
remember (select_first rel a la) as la' eqn:Hla'.
symmetry in Hla'.
destruct la' as (a', la').
remember (select_first rel b lb) as lb' eqn:Hlb'.
symmetry in Hlb'.
destruct lb' as (b', lb').
move b' before a'; move lb' before la'.
inversion Hab; subst. {
  rename H0 into Hpab.
  specialize (Permutation_select_first Hant Htr Htot) as H1.
  specialize (H1 _ _ _ _ _ _ _ Hpab Hla' Hlb').
  destruct H1 as (H1, H2); subst b'; f_equal.
  apply IHit; [ | | easy ]. {
    apply select_first_length in Hla', Hlb'; congruence.
  } {
    apply select_first_length in Hla', Hlb'; congruence.
  }
} {
  cbn in Hla', Hlb'.
  rename Hab into Hpab.
  remember (rel a b) as ab eqn:Hab; symmetry in Hab.
  remember (rel b a) as ba eqn:Hba; symmetry in Hba.
  remember (if ab then a else b) as abab eqn:Habab.
  remember (if ba then b else a) as baba eqn:Hbaba.
  remember (select_first rel abab l) as lc eqn:Hlc.
  remember (select_first rel baba l) as ld eqn:Hld.
  symmetry in Hlc, Hld.
  destruct lc as (c, lc).
  destruct ld as (d, ld).
  injection Hla'; clear Hla'; intros; subst c la'.
  injection Hlb'; clear Hlb'; intros; subst d lb'.
  destruct ab; subst abab. {
    destruct ba; subst baba. {
      specialize (Hant _ _ Hab Hba) as H1; subst b.
      rewrite Hlc in Hld.
      now injection Hld; intros; subst b' ld.
    }
    rewrite Hlc in Hld.
    now injection Hld; intros; subst b' ld.
  } {
    destruct ba; subst baba. {
      rewrite Hlc in Hld.
      now injection Hld; intros; subst b' ld.
    }
    specialize (Htot a b) as H1.
    now rewrite Hab, Hba in H1.
  }
} {
  rename l' into l.
  rename H into Haal.
  rename H0 into Hlbb.
  specialize (select_first_length rel a la Hla') as H1.
  specialize (select_first_length rel b lb Hlb') as H2.
  assert (Hab' : a' = b'). {
    apply (select_first_if Htr Htot) in Hla', Hlb'.
    destruct Hla' as (Hla1 & Hla2 & Hla3).
    destruct Hlb' as (Hlb1 & Hlb2 & Hlb3).
    specialize (Hla1 b') as H3.
    assert (H : b' ∈ a :: la). {
      apply perm_trans with (l := a :: la) in Hlb3; [ | easy ].
      apply Permutation_sym in Hlb3.
      specialize (Permutation_in b' Hlb3 (or_introl eq_refl)) as H4.
      easy.
    }
    specialize (H3 H); clear H.
    specialize (Hlb1 a') as H4.
    assert (H : a' ∈ b :: lb). {
      apply perm_trans with (l := b :: lb) in Hla3; [ | easy ].
      apply Permutation_sym in Hla3.
      specialize (Permutation_in a' Hla3 (or_introl eq_refl)) as H5.
      easy.
    }
    specialize (H4 H); clear H.
    now apply Hant.
  }
  subst b'; f_equal.
  apply IHit; [ congruence | congruence | ].
  apply (select_first_if Htr Htot) in Hla', Hlb'.
  destruct Hla' as (Hla1 & Hla2 & Hla3).
  destruct Hlb' as (Hlb1 & Hlb2 & Hlb3).
  apply Permutation_trans with (l := a' :: la') in Hab; [ | easy ].
  apply Permutation_sym in Hab, Hlb3.
  apply Permutation_trans with (l := a' :: lb') in Hab; [ | easy ].
  now apply Permutation_cons_inv, Permutation_sym in Hab.
}
Qed.

Theorem ssort_loop_Permutation : ∀ A (rel : A → _) la lb len,
  length la ≤ len
  → ssort_loop rel len la = lb
  → Permutation la lb.
Proof.
intros * Hlen Hs.
revert la lb Hlen Hs.
induction len; intros. {
  apply Nat.le_0_r, length_zero_iff_nil in Hlen; subst la.
  now cbn in Hs; subst lb.
}
cbn in Hs.
destruct la as [| a]; [ now subst lb | ].
cbn in Hlen; apply Nat.succ_le_mono in Hlen.
remember (select_first rel a la) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as (c, lc).
destruct lb as [| b]; [ easy | ].
injection Hs; clear Hs; intros Hs H; subst c.
specialize (IHlen lc lb) as H1.
assert (H : length lc ≤ len). {
  apply select_first_length in Hlc.
  congruence.
}
specialize (H1 H Hs); clear H.
apply (select_first_Permutation rel) in Hlc.
transitivity (b :: lc); [ easy | ].
now constructor.
Qed.

Theorem Permutation_ssort : ∀ A (rel : A → _) l, Permutation l (ssort rel l).
Proof.
intros.
induction l as [| a]; [ easy | ].
specialize (ssort_loop_Permutation rel) as H1.
now apply H1 with (len := length (a :: l)).
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
apply ssort_loop_Permutation in Hlc. 2: {
  apply select_first_length in Hlb.
  congruence.
}
apply (select_first_if Htr Htot) in Hlb.
destruct Hlb as (_ & H2 & _).
specialize (H2 c).
assert (H : c ∈ lb). {
  apply Permutation_sym in Hlc.
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

Theorem Permutation_bsort : ∀ A (rel : A → _),
  total_relation rel →
  ∀ l, Permutation l (bsort rel l).
Proof.
intros * Htot *.
rename l into la.
rewrite (bsort_bsort_loop_nb_disorder Htot).
remember (nb_disorder rel la) as it eqn:H.
assert (Hit : nb_disorder rel la ≤ it) by flia H.
clear H.
revert la Hit.
induction it; intros; [ easy | cbn ].
remember (bsort_swap rel la) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [lb| ]; [ | easy ].
specialize (bsort_swap_nb_disorder Htot) as H1.
specialize (H1 _ _ _ Hlb Hit).
specialize (IHit _ H1) as H2.
transitivity lb; [ | easy ].
apply bsort_swap_Some in Hlb.
destruct Hlb as (Hs & c & d & lc & ld & Hlb).
destruct Hlb as (Hcd & Hrc & Hbla & Hlbc).
subst la lb.
apply Permutation_app_head.
constructor.
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
  transitive rel → ∀ l,
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
