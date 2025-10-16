Set Nested Proofs Allowed.

From Stdlib Require Import Arith.
Import List.ListNotations.
From RingLike Require Import Utf8.

Require Import RingLike.PermutationFun.
Require Import Misc.

(* relation properties *)

Definition irreflexive {A} (rel : A → A → bool) :=
  ∀ a, rel a a = false.

Definition antisymmetric {A} (rel : A → A → bool) :=
  ∀ a b, rel a b = true → rel b a = true → a = b.

(* https://ncatlab.org/nlab/show/connected+relation *)
Definition connected_relation {A} (rel : A → A → bool) :=
  ∀ a b, rel a b = false → rel b a = false → a = b.

Definition transitive {A} (rel : A → A → bool) :=
  ∀ a b c, rel a b = true → rel b c = true → rel a c = true.

Definition total_relation {A} (rel : A → _) := ∀ a b,
  (rel a b || rel b a)%bool = true.

Theorem total_relation_is_reflexive : ∀ {A} {rel : A → _},
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

Fixpoint all_sorted {A} (rel : A → A → bool) a l :=
  match l with
  | [] => true
  | b :: l' => (rel a b && all_sorted rel a l')%bool
  end.

Fixpoint is_strongly_sorted {A} (rel : A → A → bool) l :=
  match l with
  | [] => true
  | a :: l' => (all_sorted rel a l' && is_strongly_sorted rel l')%bool
  end.

Definition sorted {A} (rel : A → _) l :=
  is_sorted rel l = true.
Definition strongly_sorted {A} (rel : A → _) l :=
  is_strongly_sorted rel l = true.

Theorem sorted_cons : ∀ A (rel : A → _) a la,
  sorted rel (a :: la) → sorted rel la.
Proof.
intros * Hs.
cbn in Hs.
destruct la as [| a']; [ easy | ].
now apply Bool.andb_true_iff in Hs.
Qed.

Theorem sorted_cons_cons_true_iff : ∀ A (rel : A → A -> bool) a b l,
  sorted rel (a :: b :: l)
  ↔ rel a b = true ∧ sorted rel (b :: l).
Proof.
intros.
apply Bool.andb_true_iff.
Qed.

Theorem sorted_extends : ∀ {A} {rel : A → _},
  transitive rel →
  ∀ {a l},
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

Theorem sorted_app_iff : ∀ {A} {rel : A → _},
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
    now apply List.in_or_app; right.
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

Theorem sorted_middle : ∀ A (rel : A → _),
  transitive rel →
  ∀ a b la lb lc,
  sorted rel (la ++ a :: lb ++ b :: lc)
  → rel a b = true.
Proof.
intros * Htra * Hsort.
rewrite (List_cons_is_app a) in Hsort.
rewrite (List_cons_is_app b) in Hsort.
rewrite List.app_assoc in Hsort.
apply (sorted_app_iff Htra) in Hsort.
destruct Hsort as (Hla & Hsort & H1).
apply H1; [ now apply List.in_or_app; right; left | ].
apply List.in_or_app; right.
now apply List.in_or_app; left; left.
Qed.

Theorem sorted_sorted_permuted : ∀ [A] {eqb rel : A → _},
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
remember (List_extract (eqb a) lb) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((befa, x), afta)| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbefa & H & Hlb).
apply Heqb in H; subst x.
subst lb.
apply (permutation_sym Heqb) in Hpab.
cbn in Hpab.
apply permutation_cons_l_iff in Hpab.
remember (List_extract (eqb b) la) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((befb, x), aftb)| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
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

Theorem sorted_strongly_sorted : ∀ [A] {rel : A → A → bool},
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

Theorem sorted_cons_iff : ∀ {A} {rel : A → _},
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
