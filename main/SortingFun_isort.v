(* isort: sort by insertion *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Import List.ListNotations.
(*
Import Init.Nat.
*)

Require Import Misc PermutationFun.

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

Theorem in_isort_insert_id : ∀ {A} (rel : A → _) a l,
  a ∈ isort_insert rel a l.
Proof.
intros.
induction l as [| b]; [ now left | cbn ].
now destruct (rel a b); [ left | right ].
Qed.

Theorem permutation_cons_isort_insert_id : ∀ {A} {eqb : A → _} (rel : A → _),
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

Theorem permutation_cons_isort_insert : ∀ {A} {eqb : A → _} (rel : A → _),
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
