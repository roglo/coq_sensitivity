(* ssort: sort by selection *)

Set Nested Proofs Allowed.

From Stdlib Require Import Arith.
Import List.ListNotations.
From RingLike Require Import Utf8.
Require Import RingLike.PermutationFun.

Require Import Misc.
Require Import SortingFun_common.

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

Theorem select_first_permutation :
  ∀ {A} {eqb : A → _} (rel : A → _) (Heqb : equality eqb),
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
  remember (List_extract (eqb a) ld) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef, x), aft)| ]; [ | easy ].
  apply List_extract_Some_iff in Hlxl.
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
  now apply Nat.le_0_r, List.length_zero_iff_nil in Hlen; subst la.
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

Theorem select_first_if : ∀ {A} {rel : A → _},
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
  now apply Nat.le_0_r, List.length_zero_iff_nil in Hlen; subst l.
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

Theorem select_first_sorted : ∀ {A rel},
  transitive rel → ∀ {a b : A} {la lb},
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

(* main *)

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

(* *)

Theorem sorted_ssort : ∀ [A] {rel : A → _},
  transitive rel →
  total_relation rel →
  ∀ l, sorted rel (ssort rel l).
Proof.
intros * Htr Htot *.
now apply sorted_ssort_loop.
Qed.

(* *)

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

(* *)

Theorem permuted_ssort : ∀ {A} {eqb : A → _} rel (Heqb : equality eqb),
  ∀ l, permutation eqb l (ssort rel l).
Proof.
intros.
now apply permuted_ssort_loop.
Qed.

(* *)

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
