(* isort: sort by insertion *)

Set Nested Proofs Allowed.

From Stdlib Require Import Arith.
Import List.ListNotations.
From RingLike Require Import Utf8.
Require Import RingLike.PermutationFun.

Require Import Misc.
Require Import SortingFun_common.

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
remember (List_extract (eqb a) (isort_insert rel a lb)) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (List_extract_None_iff _ _) Hlxl a) as H1.
  specialize (in_isort_insert_id rel a lb) as H.
  specialize (H1 H); clear H.
  now rewrite (equality_refl Heqb) in H1.
}
apply List_extract_Some_iff in Hlxl.
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

Theorem sorted_isort : ∀ [A] {rel : A → _},
  total_relation rel
  → ∀ l, sorted rel (isort rel l).
Proof.
intros * Hto *.
induction l as [| a]; [ easy | cbn ].
now apply sorted_isort_insert.
Qed.

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

Theorem permuted_isort : ∀ {A} {eqb : A → _} rel (Heqb : equality eqb),
  ∀ l, permutation eqb l (isort rel l).
Proof.
intros.
induction l as [| a]; [ apply (permutation_refl Heqb) | cbn ].
now apply permutation_cons_isort_insert.
Qed.

Theorem isort_when_permuted : ∀ {A} [eqb rel : A → _],
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

Theorem permut_if_isort : ∀ {A} {eqb : A → _} rel,
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

Theorem eq_isort_insert_cons_iff : ∀ {A} {rel : A → _},
  reflexive rel →
  ∀ a b la lb,
  isort_insert rel a la = b :: lb
  ↔ a = b ∧ la = lb ∧ rel a (List.hd a la) = true ∨
    rel a b = false ∧ List.hd a la = b ∧ isort_insert rel a (List.tl la) = lb.
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
    (List.hd a la = a ∧ isort rel (List.tl la) = lb ∧
       rel (List.hd a la) (List.hd a lb) = true ∨
     rel (List.hd a la) a = false ∧ List.hd a (isort rel (List.tl la)) = a ∧
       isort_insert rel (List.hd a la) (List.tl (isort rel (List.tl la))) =
         lb ∧
       List.tl la ≠ []).
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

Theorem sorted_isort_insert_filter : ∀ {A} {rel : A → _},
  transitive rel →
  ∀ f a la,
  sorted rel la
  → List.filter f (isort_insert rel a la) =
     if f a then isort_insert rel a (List.filter f la)
     else List.filter f la.
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
  ∀ f la, isort rel (List.filter f la) = List.filter f (isort rel la).
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
