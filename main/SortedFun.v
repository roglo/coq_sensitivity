(* Sorted by relation functions *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith (* Psatz Sorted *) Permutation (* Decidable *).
Import List List.ListNotations (*Init.Nat*).

Require Import Misc.
(*
Arguments length {A}.
*)

(*
Global Hint Resolve Nat.le_0_l : core.
Global Hint Resolve Nat.lt_0_succ : core.
Global Hint Resolve Nat.lt_succ_diag_r : core.
*)

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
