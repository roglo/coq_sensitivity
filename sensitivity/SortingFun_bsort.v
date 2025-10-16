(* bsort: bubble sort *)

Set Nested Proofs Allowed.

Require Import Stdlib.Arith.Arith.
Import List.ListNotations.
Require Import RingLike.Utf8.
Require Import RingLike.PermutationFun.

Require Import Misc.
Require Import SortingFun_common.

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

Definition bsort {A} (rel : A → _) l :=
  bsort_loop rel (length l * length l) l.

(* *)

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

Theorem bsort_swap_Some : ∀ {A} {rel : A → _} {la lb},
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

Fixpoint nb_nrel {A} (rel : A → A → bool) a l :=
  match l with
  | [] => 0
  | b :: l' => (if rel a b then 0 else 1) + nb_nrel rel a l'
  end.

Fixpoint nb_disorder {A} (rel : A → _) l :=
  match l with
  | [] => 0
  | a :: l' => nb_nrel rel a l' + nb_disorder rel l'
  end.

Theorem bsort_swap_nb_disorder : ∀ {A} {rel : A → _},
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
    specialize (bsort_swap_Some Hlc) as H2.
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
      specialize (bsort_swap_Some Hlc) as H2.
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

Theorem nb_disorder_le_square : ∀ {A} (rel : A → _) l,
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

Theorem sorted_bsort_loop : ∀ A (rel : A → _),
  total_relation rel →
  ∀ it l,
  length l * length l ≤ it
  → sorted rel (bsort_loop rel it l).
Proof.
intros * Htot * Hit.
rename l into la.
eapply Nat.le_trans in Hit. 2: {
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

(* main *)

Theorem bsort_when_sorted : ∀ A (rel : A → _),
  ∀ l,
  sorted rel l
  → bsort rel l = l.
Proof.
intros * Hs.
now apply bsort_loop_when_sorted.
Qed.

(* *)

Theorem sorted_bsort : ∀ [A] {rel : A → _},
  total_relation rel →
  ∀ l, sorted rel (bsort rel l).
Proof.
intros * Htot *.
now apply sorted_bsort_loop.
Qed.

(* *)

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

(* *)

Theorem permuted_bsort : ∀ {A} {eqb : A → _} rel (Heqb : equality eqb),
  ∀ l, permutation eqb l (bsort rel l).
Proof.
intros.
now apply permuted_bsort_loop.
Qed.

(* *)

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
