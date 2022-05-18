(* permutations of sequences of natural numbers between 0 and n-1 *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Bool.
Import List List.ListNotations.
Import Init.Nat.
Require Import Permutation.

Require Import Misc PermutationFun SortingFun.
Require Import IterAnd.
Require Import Pigeonhole.

Definition ff_app l i := nth i l 0.

Definition comp {A B C} (f : B → C) (g : A → B) x := f (g x).
Definition comp_list (la lb : list nat) := map (ff_app la) lb.

Notation "σ₁ ° σ₂" := (comp_list σ₁ σ₂) (at level 40, left associativity).

(* *)

(* Permutations of {0, 1, 2, ... n-1} *)

Definition is_permut_list l := AllLt l (length l) ∧ NoDup l.

Definition is_permut_list_bool l :=
  (⋀ (a ∈ l), (a <? length l)) &&
  (⋀ (i = 1, length l),
     (⋀ (j = 1, length l),
        ((ff_app l (i - 1) ≠? ff_app l (j - 1)) || (i =? j)))).

(* bof, faut voir...
Require Import PermutationFun.

Definition permut_list l := permutation Nat.eqb l (seq 0 (length l)).

Theorem is_permut_list_bool_permut_list : ∀ l,
  is_permut_list_bool l = true ↔ permut_list l.
Proof.
intros l.
split. {
  intros Hl.
  unfold permut_list.
  induction l as [| a]; intros; [ apply permutation_nil_nil | ].
  unfold is_permut_list_bool in Hl.
  apply Bool.andb_true_iff in Hl.
  destruct Hl as (H1, H2).
  cbn in H1, H2.
...
*)

Definition is_permut n f := is_permut_list f ∧ length f = n.

Theorem fold_ff_app : ∀ l i, nth i l 0 = ff_app l i.
Proof. easy. Qed.

Theorem comp_map_seq : ∀ la lb,
  la ° lb = map (λ i, ff_app la (ff_app lb i)) (seq 0 (length lb)).
Proof.
intros.
unfold "°".
symmetry.
rewrite List_map_nth_seq with (d := 0).
rewrite map_length.
apply map_ext_in.
intros i Hi.
apply in_seq in Hi.
now rewrite (List_map_nth' 0).
Qed.

Theorem List_map_ff_app_seq : ∀ l, l = map (ff_app l) (seq 0 (length l)).
Proof. intros; apply List_map_nth_seq. Qed.

Theorem NoDup_nat : ∀ l,
  NoDup l
  → (∀ i j, i < length l → j < length l → ff_app l i = ff_app l j → i = j).
Proof.
intros * Hnd.
now apply NoDup_nth.
Qed.
Arguments NoDup_nat : clear implicits.

Theorem nat_NoDup : ∀ l,
  (∀ i j, i < length l → j < length l → ff_app l i = ff_app l j → i = j)
  → NoDup l.
Proof.
intros * Hnd.
now apply NoDup_nth in Hnd.
Qed.

Theorem permut_comp_assoc : ∀ n f g h,
  length g = n
  → is_permut n h
  → f ° (g ° h) = (f ° g) ° h.
Proof.
intros * Hg (Hph, Hh).
unfold "°", comp_list; cbn.
rewrite map_map.
apply map_ext_in.
intros i Hi.
unfold ff_app.
rewrite (List_map_nth' 0); [ easy | ].
rewrite Hg, <- Hh.
now apply Hph.
Qed.

Arguments permut_comp_assoc n%nat [f g h]%list.

Theorem is_permut_list_is_permut_list_bool : ∀ l,
  is_permut_list l ↔ is_permut_list_bool l = true.
Proof.
intros.
split. {
  intros (H1, H2).
  unfold is_permut_list_bool.
  apply andb_true_iff.
  split. {
    apply all_true_and_list_true_iff.
    intros i Hi.
    apply Nat.ltb_lt.
    now apply H1.
  } {
    apply all_true_and_seq_true_iff.
    intros i Hi.
    apply all_true_and_seq_true_iff.
    intros j Hj.
    apply orb_true_iff.
    specialize (NoDup_nat _ H2 (i - 1) (j - 1)) as H3.
    assert (H : i - 1 < length l) by flia Hi.
    specialize (H3 H); clear H.
    assert (H : j - 1 < length l) by flia Hj.
    specialize (H3 H); clear H.
    destruct (Nat.eq_dec i j) as [Hij| Hij]. {
      subst j.
      now right; rewrite Nat.eqb_eq.
    }
    left.
    apply negb_true_iff.
    apply Nat.eqb_neq.
    intros H.
    specialize (H3 H).
    flia Hi Hj H3 Hij.
  }
} {
  intros Hb.
  unfold is_permut_list_bool in Hb.
  apply andb_true_iff in Hb.
  destruct Hb as (H1, H2).
  split. {
    intros i Hi.
    specialize (proj2 (all_true_and_list_true_iff _ _ _) H1) as H3.
    specialize (H3 _ Hi).
    now apply Nat.ltb_lt.
  } {
    clear H1.
    apply nat_NoDup.
    intros i j Hi Hj Hij.
    specialize (proj2 (all_true_and_list_true_iff _ _ _) H2) as H3.
    rewrite Nat_sub_succ_1 in H3.
    specialize (H3 (S i)).
    rewrite Nat_sub_succ_1 in H3.
    assert (H : S i ∈ seq 1 (length l)) by (apply in_seq; flia Hi).
    specialize (H3 H); clear H.
    specialize (proj2 (all_true_and_list_true_iff _ _ _) H3) as H4.
    rewrite Nat_sub_succ_1 in H4.
    specialize (H4 (S j)).
    rewrite Nat_sub_succ_1 in H4; cbn in H4.
    assert (H : S j ∈ seq 1 (length l)) by (apply in_seq; flia Hj).
    specialize (H4 H); clear H.
    apply orb_true_iff in H4.
    rewrite Nat.eqb_eq in H4.
    destruct H4 as [H4| H4]; [ | easy ].
    apply negb_true_iff in H4.
    now apply Nat.eqb_neq in H4.
  }
}
Qed.

(*
   Canonical Symmetric Group.

   In set theory, there is one only symmetric group of order n.

   Here, a symmetric group (of order n) is a list of n! permutations,
   which can be ordered in any order. There are actually n!! (factorial
   of factorial n) possible orders.

   There is one that we call "canonical" because the generated permutation
   are in alphabetic order.

   The canonical symmetric group is built this way. The k-th permutation
   is a vector of size n where
   - the first value is k/fact(n-1)
   - the rest is the (k mod fact(n-1))-th permutation of n-1 values
     (from 0 to n-2) where
     * all values less than the first value (k/fact(n-1)) are unchanged
     * all values greater or equal to it are increased by 1
   Example. For n=4 and k=0
   - first value: 0
   - rest: shift of 0;1;2 by 1, i.e. 1;2;3
   Result : 0;1;2;3
   Other example. For n=4 and k=13
   - first value: 13/3! = 13/6 = 2
   - rest: k' = 13 mod 3! = 13 mod 6 = 1 for n'=3, resulting 0;2;1
     0 and 1 are not shifted (both < 2), 2 is shifted, resulting 0;3;1
     final result: 2;0;3;1
  *)

Definition succ_when_ge k a := a + Nat.b2n (k <=? a).

(* k-th canonic permutation of order n *)
Fixpoint canon_sym_gr_list n k : list nat :=
  match n with
  | 0 => []
  | S n' =>
      k / n'! ::
      map (succ_when_ge (k / n'!)) (canon_sym_gr_list n' (k mod n'!))
  end.

(* all canonic permutations *)
Definition canon_sym_gr_list_list n : list (list nat) :=
  map (canon_sym_gr_list n) (seq 0 n!).

Definition is_sym_gr_list n (ll : list (list nat)) :=
  (∀ i, i < length ll →
   length (nth i ll []) = n ∧
   is_permut_list (nth i ll [])) ∧
  (∀ i j, i < length ll → j < length ll →
   nth i ll [] = nth j ll [] → i = j) ∧
  (∀ l, is_permut n l → l ∈ ll).

Theorem permut_list_without : ∀ n l,
  is_permut_list l
  → n < length l
  → (∀ i, i < length l → nth i l 0 ≠ n)
  → False.
Proof.
intros * Hp Hn Hnn.
destruct Hp as (Hp1, Hp2).
specialize (pigeonhole_list (length l) (n :: l)) as H1.
specialize (H1 (Nat.lt_succ_diag_r _)).
assert (H : ∀ x, x ∈ n :: l → x < length l). {
  intros z Hz.
  destruct Hz as [Hz| Hz]; [ now subst z | now apply Hp1 ].
}
specialize (H1 H); clear H.
remember (pigeonhole_comp_list (n :: l)) as xx eqn:Hxx.
symmetry in Hxx.
destruct xx as (x, x').
specialize (H1 x x' eq_refl).
destruct H1 as (Hxl & Hx'l & Hxx' & Hnxx).
destruct x. {
  destruct x'; [ easy | cbn in Hnxx ].
  cbn in Hx'l; apply Nat.succ_lt_mono in Hx'l.
  specialize (Hnn x' Hx'l).
  now symmetry in Hnxx.
} {
  cbn in Hxl; apply Nat.succ_lt_mono in Hxl.
  destruct x'. {
    cbn in Hnxx.
    now specialize (Hnn x Hxl).
  }
  cbn in Hnxx.
  cbn in Hx'l; apply Nat.succ_lt_mono in Hx'l.
  specialize (NoDup_nat _ Hp2 x x' Hxl Hx'l Hnxx) as H1.
  now destruct H1.
}
Qed.

Theorem comp_length : ∀ la lb,
  length (la ° lb) = length lb.
Proof.
intros.
unfold "°"; cbn.
now rewrite map_length.
Qed.

Theorem comp_isort_rank_r : ∀ ord l,
  l ° isort_rank ord l = isort ord l.
Proof.
intros.
apply List_eq_iff.
rewrite comp_length, isort_rank_length, isort_length.
split; [ easy | ].
intros d i.
destruct (lt_dec i (length l)) as [Hil| Hil]. 2: {
  apply Nat.nlt_ge in Hil.
  rewrite nth_overflow; [ | now rewrite comp_length, isort_rank_length ].
  rewrite nth_overflow; [ easy | now rewrite isort_length ].
}
rewrite nth_indep with (d' := 0). 2: {
  now rewrite comp_length, isort_rank_length.
}
symmetry.
rewrite nth_indep with (d' := 0); [ | now rewrite isort_length ].
symmetry.
unfold "°".
rewrite (List_map_nth' 0); [ | now rewrite isort_rank_length ].
specialize (isort_isort_rank ord 0 l) as H1.
do 2 rewrite fold_ff_app; cbn.
apply (f_equal (λ l, nth i l 0)) in H1.
rewrite (List_map_nth' 0) in H1; [ | now rewrite isort_rank_length ].
do 3 rewrite fold_ff_app in H1.
easy.
Qed.

(* *)

Theorem Permutation_permut : ∀ la lb,
  Permutation la lb
  → is_permut_list la
  → is_permut_list lb.
Proof.
intros * Hab Ha.
assert (Hlab : length la = length lb). {
  now apply Permutation_length.
}
split. {
  intros i Hi.
  rewrite <- Hlab.
  apply Ha.
  apply Permutation_in with (l := lb); [ | easy ].
  now apply Permutation_sym.
} {
  apply nat_NoDup.
  intros i j Hi Hj Hij.
  unfold ff_app in Hij.
  rewrite <- Hlab in Hi, Hj.
  destruct Ha as (Hap, Hal).
  specialize (proj1 (Permutation_nth _ _ 0) Hab) as H1.
  destruct H1 as (H1 & f & H2 & H3 & H4).
  rewrite H4 in Hij; [ | easy ].
  rewrite H4 in Hij; [ | easy ].
  do 2 rewrite fold_ff_app in Hij.
  apply (NoDup_nat _ Hal) in Hij; [ | now apply H2 | now apply H2 ].
  now apply H3.
}
Qed.

Theorem is_permut_list_app_max : ∀ l,
  is_permut_list (l ++ [length l])
  → is_permut_list l.
Proof.
intros * Hp.
destruct Hp as (Hp, Hl).
unfold AllLt in Hp.
rewrite app_length, Nat.add_comm in Hp.
cbn in Hp.
split. {
  intros i Hi.
  specialize (Hp i) as H1.
  assert (H : i ∈ l ++ [length l]) by now apply in_or_app; left.
  specialize (H1 H); clear H.
  destruct (Nat.eq_dec i (length l)) as [Hil| Hil]; [ | flia H1 Hil ].
  clear H1; exfalso.
  apply (In_nth _ _ 0) in Hi.
  destruct Hi as (j & Hjl & Hji).
  specialize (NoDup_nat _ Hl) as H1.
  rewrite app_length, Nat.add_comm in H1; cbn in H1.
  specialize (H1 j (length l)).
  assert (H : j < S (length l)) by flia Hjl.
  specialize (H1 H); clear H.
  specialize (H1 (Nat.lt_succ_diag_r _)).
  unfold ff_app in H1.
  rewrite app_nth1 in H1; [ | easy ].
  rewrite app_nth2 in H1; [ | now unfold ge ].
  rewrite Nat.sub_diag, Hji in H1.
  specialize (H1 Hil).
  flia Hjl H1.
} {
  now apply NoDup_app_remove_r in Hl.
}
Qed.

Theorem sorted_permut : ∀ l,
  is_permut_list l
  → sorted Nat.leb l
  → l = seq 0 (length l).
Proof.
intros * Hl Hs.
induction l as [| a] using rev_ind; [ easy | ].
rewrite app_length; cbn.
rewrite Nat.add_1_r.
rewrite seq_S; cbn.
assert (Hal : a = length l). {
  destruct Hl as (H1, H2).
  rewrite app_length, Nat.add_comm in H1; cbn in H1.
  unfold AllLt in H1.
  specialize (H1 a) as H3.
  assert (H : a ∈ l ++ [a]) by now apply in_or_app; right; left.
  specialize (H3 H); clear H.
  assert (H4 : ∀ c, c ∈ l → c ≤ a). {
    intros c Hc.
    specialize (sorted_app _ _ Hs) as H4.
    destruct H4 as (_ & _ & H4).
    specialize (H4 Nat_leb_trans c a Hc (or_introl eq_refl)).
    now apply Nat.leb_le in H4.
  }
  destruct (Nat.eq_dec a (length l)) as [Hal| Hal]; [ easy | exfalso ].
  assert (H5 : a < length l) by flia H3 Hal; clear H3 Hal.
  specialize (pigeonhole (length l) a) as H3.
  specialize (H3 (λ i, nth i l 0)).
  specialize (H3 H5).
  cbn in H3.
  assert (H : ∀ x, x < length l → nth x l 0 < a). {
    intros x Hx.
    specialize (H4 (nth x l 0)) as H7.
    assert (H : nth x l 0 ∈ l) by now apply nth_In.
    specialize (H7 H); clear H.
    destruct (Nat.eq_dec (nth x l 0) a) as [Hxa| Hxa]; [ | flia H7 Hxa ].
    replace a with (nth (length l) (l ++ [a]) 0) in Hxa. 2: {
      rewrite app_nth2; [ | now unfold ge ].
      now rewrite Nat.sub_diag.
    }
    replace (nth x l 0) with (nth x (l ++ [a]) 0) in Hxa. 2: {
      now rewrite app_nth1.
    }
    apply (NoDup_nat _ H2) in Hxa; cycle 1. {
      rewrite app_length, Nat.add_comm; cbn.
      flia Hx.
    } {
      now rewrite app_length, Nat.add_comm; cbn.
    }
    flia Hx Hxa.
  }
  specialize (H3 H); clear H.
  remember (pigeonhole_fun (length l) (λ i : nat, nth i l 0)) as xx eqn:Hxx.
  symmetry in Hxx.
  destruct xx as (x, x').
  specialize (H3 x x' eq_refl).
  destruct H3 as (H3 & H6 & H7 & H8).
  specialize (NoDup_nat _ H2) as H9.
  specialize (H9 x x').
  rewrite app_length, Nat.add_comm in H9; cbn in H9.
  assert (H : x < S (length l)) by flia H3.
  specialize (H9 H); clear H.
  assert (H : x' < S (length l)) by flia H6.
  specialize (H9 H); clear H.
  unfold ff_app in H9.
  apply H7, H9.
  rewrite app_nth1; [ | easy ].
  rewrite app_nth1; [ | easy ].
  easy.
}
rewrite Hal; f_equal.
apply IHl; [ | apply (sorted_app l [a] Hs) ].
subst a.
now apply is_permut_list_app_max.
Qed.

Theorem permut_isort_leb : ∀ l,
  is_permut_list l
  → isort Nat.leb l = seq 0 (length l).
Proof.
intros * Hp.
specialize (sorted_isort Nat_leb_is_total_relation l) as Hbs.
(*
specialize (permuted_isort Nat.eqb Nat_eqb_equality l) as Hps.
*)
specialize (Permutation_isort Nat.leb l) as Hps.
(**)
remember (isort Nat.leb l) as l'; clear Heql'.
specialize (Permutation_permut) as Hpl'.
specialize (Hpl' l l' Hps Hp).
move l' before l; move Hpl' before Hp.
replace (length l) with (length l') by now apply Permutation_length.
clear l Hp Hps.
rename l' into l.
now apply sorted_permut.
Qed.

Theorem permut_comp_isort_rank_r : ∀ l,
  is_permut_list l
  → l ° isort_rank Nat.leb l = seq 0 (length l).
Proof.
intros * Hp.
rewrite comp_isort_rank_r.
now apply permut_isort_leb.
Qed.

Theorem permut_isort_permut : ∀ i l,
  is_permut_list l
  → i < length l
  → ff_app (isort_rank Nat.leb l) (ff_app l i) = i.
Proof.
intros * Hp Hil.
specialize (permut_comp_isort_rank_r Hp) as H1.
apply List_eq_iff in H1.
destruct H1 as (_, H1).
specialize (H1 0).
unfold "°" in H1.
assert
  (H2 : ∀ j, j < length l → ff_app l (ff_app (isort_rank Nat.leb l) j) = j). {
  intros j Hj.
  specialize (H1 j).
  rewrite (List_map_nth' 0) in H1; [ | now rewrite isort_rank_length ].
  now rewrite seq_nth in H1.
}
clear H1.
specialize (H2 (ff_app l i)) as H2.
assert (H : ff_app l i < length l) by now apply Hp, nth_In.
specialize (H2 H); clear H.
destruct Hp as (Ha, Hp).
apply (NoDup_nat _ Hp) in H2; [ easy | | easy ].
apply isort_rank_ub.
now intros H; subst l.
Qed.

Theorem permut_comp_isort_rank_l : ∀ l,
  is_permut_list l
  → isort_rank Nat.leb l ° l = seq 0 (length l).
Proof.
intros * Hp.
apply List_eq_iff.
rewrite comp_length, seq_length.
split; [ easy | ].
intros d i.
destruct (lt_dec i (length l)) as [Hil| Hil]. 2: {
  apply Nat.nlt_ge in Hil.
  rewrite nth_overflow; [ | now rewrite comp_length ].
  rewrite nth_overflow; [ easy | now rewrite seq_length ].
}
rewrite seq_nth; [ | easy ].
rewrite nth_indep with (d' := 0); [ | now rewrite comp_length ].
clear d.
unfold "°".
rewrite (List_map_nth' 0); [ | easy ].
rewrite fold_ff_app; cbn.
now apply permut_isort_permut.
Qed.

Theorem permut_permut_isort : ∀ i l,
  is_permut_list l
  → i < length l
  → ff_app l (ff_app (isort_rank Nat.leb l) i) = i.
Proof.
intros * Hp Hil.
specialize (permut_comp_isort_rank_l Hp) as H1.
apply List_eq_iff in H1.
destruct H1 as (_, H1).
specialize (H1 0).
unfold "°" in H1.
assert
  (H2 : ∀ j, j < length l → ff_app (isort_rank Nat.leb l) (ff_app l j) = j). {
  intros j Hj.
  specialize (H1 j).
  rewrite (List_map_nth' 0) in H1; [ | easy ].
  now rewrite seq_nth in H1.
}
clear H1.
specialize (H2 (ff_app (isort_rank Nat.leb l) i)) as H2.
assert (H : ff_app (isort_rank Nat.leb l) i < length l). {
  apply isort_rank_ub.
  now intros H; subst l.
}
specialize (H2 H); clear H.
destruct Hp as (Ha, Hp).
specialize (NoDup_isort_rank Nat.leb l) as H3.
apply (NoDup_nat _ H3) in H2; [ easy | | ]. 2: {
  now rewrite isort_rank_length.
}
rewrite isort_rank_length.
apply Ha, nth_In.
apply isort_rank_ub.
now intros H; subst l.
Qed.

(**)

Definition option_eqb {A} (eqb : A → A → bool) ao bo :=
  match (ao, bo) with
  | (Some a, Some b) => eqb a b
  | _ => false
  end.

Fixpoint permutation_assoc_loop {A} eqb (la : list A) lbo :=
  match la with
  | [] => []
  | a :: la' =>
      match extract (λ bo, option_eqb eqb bo (Some a)) lbo with
      | Some (befo, _, afto) =>
          length befo :: permutation_assoc_loop eqb la' (befo ++ None :: afto)
      | None => []
      end
  end.

Definition permutation_assoc {A} (eqb : A → _) la lb :=
  permutation_assoc_loop eqb la (map Some lb).

Definition permutation_fun {A} (eqb : A → _) la lb i :=
  unsome 0 (List_rank (Nat.eqb i) (permutation_assoc eqb la lb)).

Fixpoint filter_Some {A} (lao : list (option A)) :=
  match lao with
  | [] => []
  | Some ao :: lao' => ao :: filter_Some lao'
  | None :: lao' => filter_Some lao'
  end.

Theorem fold_permutation_assoc : ∀ A (eqb : A → _) la lb,
  permutation_assoc_loop eqb la (map Some lb) = permutation_assoc eqb la lb.
Proof. easy. Qed.

Theorem filter_Some_app : ∀ A (l1 l2 : list (option A)),
  filter_Some (l1 ++ l2) = filter_Some l1 ++ filter_Some l2.
Proof.
intros.
revert l2.
induction l1 as [| xo]; intros; [ easy | cbn ].
destruct xo as [x| ]; [ | apply IHl1 ].
cbn; f_equal; apply IHl1.
Qed.

Theorem filter_Some_inside : ∀ A l1 l2 (x : option A),
  filter_Some (l1 ++ x :: l2) =
    filter_Some l1 ++
    match x with
    | Some a => a :: filter_Some l2
    | None => filter_Some l2
    end.
Proof.
intros.
revert x l2.
induction l1 as [| yo]; intros; [ easy | ].
cbn - [ option_eqb ].
destruct yo; [ | apply IHl1 ].
cbn; f_equal; apply IHl1.
Qed.

Theorem permutation_assoc_loop_length : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lbo,
  permutation eqb la (filter_Some lbo)
  → length (permutation_assoc_loop eqb la lbo) = length la.
Proof.
intros * Heqb * Hpab.
revert lbo Hpab.
induction la as [| a]; intros; [ easy | ].
cbn - [ option_eqb ].
remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  cbn - [ option_eqb ] in H1.
  specialize (H1 (Some a)).
  assert (H : Some a ∈ lbo). {
    specialize (permutation_in Heqb) as H2.
    specialize (proj1 (H2 _ _ Hpab a) (or_introl eq_refl)) as H3.
    clear - H3.
    induction lbo as [| bo]; [ easy | cbn in H3 ].
    destruct bo as [b| ]. {
      destruct H3 as [H3| H3]; [ now subst b; left | ].
      now right; apply IHlbo.
    }
    now right; apply IHlbo.
  }
  specialize (H1 H); clear H.
  cbn in H1.
  now rewrite (equality_refl Heqb) in H1.
}
cbn; f_equal.
apply IHla.
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & Hxa & Hlbo).
cbn in Hxa.
destruct x as [b| ]; [ | easy ].
apply Heqb in Hxa; subst b.
subst lbo.
rewrite filter_Some_inside in Hpab |-*.
apply (permutation_app_inv Heqb [] _ _ _ _ Hpab).
Qed.

Theorem filter_Some_map_Some : ∀ A (la : list A),
  filter_Some (map Some la) = la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
now f_equal.
Qed.

(*
Theorem permutation_assoc_length : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb,
  permutation eqb la lb
  → length (permutation_assoc eqb la lb) = length la.
Proof.
intros * Heqb * Hpab.
apply (permutation_assoc_loop_length Heqb).
now rewrite filter_Some_map_Some.
Qed.
*)

Theorem permutation_assoc_loop_ub : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lbo i,
  permutation eqb la (filter_Some lbo)
  → i < length la
  → nth i (permutation_assoc_loop eqb la lbo) 0 < length lbo.
Proof.
intros * Heqb * Hpab Hla.
revert lbo i Hpab Hla.
induction la as [| a]; intros; [ easy | ].
cbn - [ option_eqb ].
remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  rewrite List_nth_nil.
  destruct lbo; [ | now cbn ].
  cbn in Hpab.
  now apply permutation_nil_r in Hpab.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
cbn in H.
destruct x as [b| ]; [ | easy ].
apply Heqb in H; subst b.
destruct i. {
  rewrite List_nth_0_cons.
  apply (f_equal length) in Hlb.
  rewrite app_length in Hlb; cbn in Hlb.
  rewrite Hlb; flia.
}
cbn in Hla; apply Nat.succ_lt_mono in Hla.
rewrite List_nth_succ_cons.
replace (length lbo) with (length (bef ++ None :: aft)). 2: {
  rewrite Hlb.
  now do 2 rewrite app_length.
}
apply IHla; [ | easy ].
subst lbo.
rewrite filter_Some_inside in Hpab |-*.
apply (permutation_app_inv Heqb [] _ _ _ _ Hpab).
Qed.

(*
Theorem first_non_excl_ub : ∀ excl a la len,
  (∀ b, b ∈ a :: la → b < len)
  → first_non_excl Nat.eqb excl a la < len.
Proof.
intros * Hla.
revert a len Hla.
induction la as [| b]; intros; [ now apply Hla; left | cbn ].
remember (existsb (Nat.eqb a) excl) as x eqn:Hx; symmetry in Hx.
destruct x; [ | now apply Hla; left ].
apply IHla.
intros c Hc.
now apply Hla; right.
Qed.

Theorem nth_permutation_assoc_ub : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb i,
  permutation eqb la lb
  → i < length la
  → nth i (permutation_assoc eqb la lb) 0 < length la.
Proof.
intros * Heqb * Hpab Hla.
unfold permutation_assoc.
unfold canon_assoc_of_multiv.
rewrite <- (multivalued_length eqb) with (lb := lb).
apply nth_canon_assoc_of_multiv_loop_ub; [ | | now rewrite multivalued_length ]. {
  rewrite multivalued_length.
  now destruct la.
}
intros lc Hlc a Ha.
rewrite multivalued_length.
rewrite (permutation_length Heqb Hpab).
now apply multivalued_ub with (a := a) in Hlc.
Qed.
*)

Theorem permutation_assoc_loop_cons_None : ∀ A (eqb : A → _),
  ∀ la lbo,
  permutation_assoc_loop eqb la (None :: lbo) =
  map S (permutation_assoc_loop eqb la lbo).
Proof.
intros.
revert lbo.
induction la as [| a]; intros; [ easy | ].
cbn - [ option_eqb ].
unfold option_eqb at 1.
remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
cbn; f_equal.
apply IHla.
Qed.

(*
Theorem first_non_excl_nil_l : ∀ A (eqb : A → _) a la,
  first_non_excl eqb [] a la = a.
Proof. now intros; destruct la. Qed.

Theorem multivalued_elem_inside : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb lc a c i,
  (∀ x, x ∈ la → eqb a x = false)
  → multivalued_elem eqb (la ++ a :: lb) i a = c :: lc
  → c = i + length la.
Proof.
intros * Heqb * Hla Hlc.
revert lb lc a c i Hla Hlc.
induction la as [| b]; intros; cbn in Hlc. {
  rewrite (equality_refl Heqb) in Hlc.
  injection Hlc; clear Hlc; intros Hlc H; subst c.
  symmetry; apply Nat.add_0_r.
}
remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  injection Hlc; clear Hlc; intros Hlc H; subst c.
  apply Heqb in Hab; subst b.
  specialize (Hla _ (or_introl eq_refl)).
  now rewrite (equality_refl Heqb) in Hla.
}
cbn; rewrite <- Nat.add_succ_comm.
apply IHla in Hlc; [ easy | ].
intros x Hx.
now apply Hla; right.
Qed.

Theorem canon_assoc_of_multiv_loop_map_multiv_is_permut_list :
  ∀ A (eqb : A → _),
  ∀ la lb i,
  is_permut_list
    (map (λ j, j - i)
      (canon_assoc_of_multiv_loop Nat.eqb []
         (map (multivalued_elem eqb lb i) la))).
Proof.
intros.
split. {
  unfold AllLt.
  intros j Hj.
  rewrite map_length.
  apply in_map_iff in Hj.
  destruct Hj as (k & Hk & Hj).
  subst j.
  destruct (Nat.eq_dec (length lb) 0) as [Hbz| Hbz]. {
    apply length_zero_iff_nil in Hbz; subst lb.
    cbn in Hj |-*.
    rewrite List_map_const_is_repeat with (b := []) in Hj; [ | easy ].
    exfalso; clear i.
    now destruct la.
  }
  destruct la as [| a]; [ easy | ].
  cbn in Hj |-*.
  remember (multivalued_elem eqb lb i a) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as [| c]; [ easy | ].
  cbn in Hj |-*.
  move i before a; move c before a; move k before i.
  destruct Hj as [Hj| Hj]. {
    destruct la as [| a2]. {
      cbn.
      enough (Hki : k ≤ i) by flia Hki.
      subst k.
      destruct lb as [| b]; [ easy | clear Hbz ].
      cbn in Hlc.
      remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
      destruct ab. {
        injection Hlc; clear Hlc; intros Hlc H; subst c.
        clear b Hab.
        subst lc.
        remember 1 as k.
        replace (S i) with (k + i) by flia Heqk.
        clear Heqk.
        (* a lemma, perhaps? *)
        revert i k.
        induction lb as [| b]; intros; [ easy | cbn ].
        remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
        destruct ab; [ easy | ].
        clear b Hab.
        rewrite <- Nat.add_succ_l.
        apply IHlb.
      }
      clear b Hab.
      destruct lb as [| b]; [ easy | ].
      cbn in Hlc.
      remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
      destruct ab. {
        clear b Hab.
        injection Hlc; clear Hlc; intros; subst c lc.
        remember 1 as k.
        replace (S i) with (k + i) by flia Heqk.
        clear Heqk.
        revert i k.
        induction lb as [| b]; intros. {
          cbn.
(* bin c'est faux *)
...
        destruct lc as [| c]; [ easy | cbn ].
        remember (existsb (Nat.eqb i) excl) as x eqn:Hx; symmetry in Hx.
        destruct x; [ | easy ].
        apply existsb_exists in Hx.
        destruct Hx as (j & Hi & Hij).
        apply Nat.eqb_eq in Hij; subst j.
        destruct lb as [| b]; [ easy | ].
        cbn in Hlc.
        remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
        destruct ab. {
          injection Hlc; clear Hlc; intros Hlc H; subst c.
          apply Heqb in Hab; subst b.
...
  rewrite canon_assoc_of_multiv_loop_length. 2: {
    intros lc Hlc H; subst lc.
    apply in_map_iff in Hlc.
    destruct Hlc as (c & Hlc & Hc).
    destruct lb as [| b]; [ easy | ].
    cbn in Hlc.
    remember (eqb c b) as cb eqn:Hcb; symmetry in Hcb.
    destruct cb; [ easy | ].
    clear Hbz.
    destruct lb as [| b2]. {
      clear Hlc; cbn in Hj.
      destruct la as [| a]; [ easy | ].
      cbn in Hj.
      destruct Hc as [Hc| Hc]. {
        subst c.
        now rewrite Hcb in Hj.
      }
      remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
      destruct ab; [ | easy ].
      apply Heqb in Hab; subst b.
      cbn in Hj.
      destruct Hj as [Hj| Hj]. {
        clear i k Hj.
(* mort *)
...
revert lb i excl.
induction la as [| a]; intros. {
  split; [ easy | apply NoDup_nil ].
}
remember (multivalued_elem eqb lb i a) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [| c]. {
  split; [ easy | apply NoDup_nil ].
}
...
Compute (
let la := [2;3;5;3;2;1] in
let lb := [1;5;2;3;2;3] in
let eqb := Nat.eqb in
let i := 2 in
let excl := [24] in
    (map (λ j, j - i)
      (canon_assoc_of_multiv_loop Nat.eqb excl
         (map (multivalued_elem eqb lb i) la)))).
...
*)

(* to be completed if required
   ("permutation_permut" uses "permutation" instead of "Permutation")
(*
Theorem permutation_assoc_permutation_assoc_inv : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb i,
  permutation eqb la lb
  → i < length la
  → ff_app (permutation_assoc eqb la lb)
      (ff_app (permutation_assoc eqb lb la) i) = i.
Proof.
intros * Heqb * Hpab Hla.
...
*)

Theorem perm_assoc_is_permut_list : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb,
  permutation eqb la lb
  → is_permut_list (permutation_assoc eqb la lb).
Proof.
intros * Heqb * Hpab.
unfold permutation_assoc.
specialize (permutation_assoc_loop_length Heqb) as Hlen.
specialize (Hlen la (map Some lb)).
rewrite filter_Some_map_Some in Hlen.
specialize (Hlen Hpab).
split. {
  intros i Hi.
  rewrite Hlen.
  apply (In_nth _ _ 0) in Hi.
  rewrite Hlen in Hi.
  destruct Hi as (j & Hj & Hi).
  subst i.
  eapply lt_le_trans. {
    apply (permutation_assoc_loop_ub Heqb); [ | easy ].
    now rewrite filter_Some_map_Some.
  }
  rewrite map_length.
  now rewrite (permutation_length Heqb Hpab).
}  {
  apply nat_NoDup.
  rewrite Hlen.
  intros * Hi Hj Hij.
  rewrite fold_permutation_assoc in Hij.
  unfold permutation_assoc in Hij.
  destruct la as [| a]; [ easy | ].
  cbn - [ option_eqb ] in Hij.
  cbn - [ option_eqb ] in Hlen.
  remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef, x), aft)| ]; [ | easy ].
  cbn in Hlen.
  apply Nat.succ_inj in Hlen.
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef & Hx & Hlb).
  cbn in Hx.
  destruct x as [x| ]; [ | easy ].
  apply Heqb in Hx; subst x.
  destruct i. {
    destruct j; [ easy | exfalso ].
    cbn in Hij.
    symmetry in Hij.
    cbn in Hj.
    apply Nat.succ_lt_mono in Hj.
    clear Hi.
    assert (H : ∃ lc, bef = map Some lc). {
      exists (filter_Some bef).
      clear - Hlb.
      revert lb Hlb.
      induction bef as [| bo]; intros; [ easy | cbn ].
      cbn in Hlb.
      destruct lb as [| b]; [ easy | ].
      cbn in Hlb.
      injection Hlb; clear Hlb; intros Hlb H; subst bo.
      cbn; f_equal.
      now apply (IHbef lb).
    }
    destruct H as (lc & H); subst bef.
    assert (H : ∃ ld, aft = map Some ld). {
      exists (filter_Some aft).
      clear - Hlb.
      rewrite List_cons_is_app, app_assoc in Hlb.
      replace (map Some lc ++ [Some a]) with (map Some (lc ++ [a]))
        in Hlb. 2: {
        now rewrite map_app.
      }
      remember (lc ++ [a]) as la eqn:Hla.
      clear a lc Hla.
      revert lb aft Hlb.
      induction la as [| a]; intros; cbn. {
        cbn in Hlb; subst aft.
        symmetry; f_equal; apply filter_Some_map_Some.
      }
      cbn in Hlb.
      destruct lb as [| b]; [ easy | ].
      cbn in Hlb.
      injection Hlb; clear Hlb; intros Hlb H.
      clear b H.
      now apply (IHla lb).
    }
    destruct H as (ld & H); subst aft.
    apply (f_equal filter_Some) in Hlb.
    rewrite filter_Some_map_Some in Hlb.
    rewrite filter_Some_app in Hlb; cbn in Hlb.
    do 2 rewrite filter_Some_map_Some in Hlb.
    subst lb.
    specialize (permutation_app_inv Heqb) as H.
    specialize (H [] _ _ _ _ Hpab).
    cbn in H; move H before Hpab; clear Hpab; rename H into Hpab.
    rename lc into lb.
    rename ld into lc.
    rewrite map_length in Hij.
    clear a Hbef Hlen.
Print permutation_assoc_loop.
Theorem glop : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lbo lco i,
  permutation eqb la (filter_Some lbo ++ filter_Some lco)
  → i < length la
  → nth i (permutation_assoc_loop eqb la (lbo ++ None :: lco)) 0 =
     length (filter_Some lbo)
  → False.
Proof.
intros * Heqb * Hpa Hi Hlb.
revert lbo lco i Hpa Hi Hlb.
induction la as [| a]; intros; [ easy | ].
cbn - [ option_eqb ] in Hlb.
remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  rewrite List_nth_nil in Hlb; symmetry in Hlb.
  apply length_zero_iff_nil in Hlb.
...
rewrite Hlb in Hpa; cbn in Hpa.
...
specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
cbn - [ option_eqb ] in H1.
...
Print filter_Some.
Search (filter_Some _ = []).
  apply length_zero_iff_nil in Hlb; subst lbo.
  cbn - [ option_eqb ] in Hlxl.
  unfold option_eqb in Hlxl at 1.
  cbn in Hpa.
  remember (extract _ _) as lxl eqn:Hlxl'; symmetry in Hlxl'.
  destruct lxl as [((bef', x), aft')| ]; [ easy | clear Hlxl ].
  specialize (proj1 (extract_None_iff _ _) Hlxl') as H1.
  cbn - [ option_eqb ] in H1.
  specialize (H1 (Some a)).
  assert (H : Some a ∈ lco). {
    specialize (permutation_in Heqb Hpa) as H2.
    specialize (proj1 (H2 a) (or_introl eq_refl)) as H3.
    clear - H3.
    induction lco as [| co]; [ easy | ].
    cbn in H3.
    destruct co as [c| ]. {
      destruct H3 as [H3| H3]; [ now left; subst c | ].
      now right; apply IHlco.
    }
    now right; apply IHlco.
  }
  specialize (H1 H); clear H; cbn in H1.
  now rewrite (equality_refl Heqb) in H1.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlbo).
cbn in H.
destruct x as [x| ]; [ | easy ].
apply Heqb in H; subst x.
destruct i. {
  cbn in Hlb.
  now apply List_app_eq_app' in Hlbo.
}
cbn in Hlb.
...
specialize glop as H1.
specialize (H1 _ eqb Heqb la (map Some lb) (map Some lc) j).
do 2 rewrite filter_Some_map_Some in H1.
specialize (H1 Hpab Hj).
congruence.
...
(**)
    revert lb lc j Hpab Hj Hij.
    induction la as [| a]; intros; [ easy | cbn ].
    cbn - [ option_eqb ] in Hij.
    remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
    destruct lxl as [((bef, x), aft)| ]. 2: {
      specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
      clear Hlxl; cbn - [ option_eqb ] in H1.
      rewrite List_nth_nil in Hij.
      symmetry in Hij.
      apply length_zero_iff_nil in Hij; subst lb.
      cbn - [ option_eqb In ] in Hpab, H1.
      specialize (H1 (Some a)).
      assert (H : Some a ∈ None :: map Some lc). {
        right.
        apply in_map_iff.
        exists a; split; [ easy | ].
        specialize (permutation_in Heqb Hpab) as H2.
        apply (proj1 (H2 a) (or_introl eq_refl)).
      }
      specialize (H1 H); clear H.
      cbn in H1.
      now rewrite (equality_refl Heqb) in H1.
    }
    apply extract_Some_iff in Hlxl.
    destruct Hlxl as (Hbef & H & Hlb).
    cbn in H.
    destruct x as [x| ]; [ | easy ].
    apply Heqb in H; subst x.
    destruct j. {
      cbn in Hij.
      apply List_app_eq_app' in Hlb; [ easy | now rewrite map_length ].
    }
    cbn in Hij.
    cbn in Hj; apply Nat.succ_lt_mono in Hj.
    destruct lb as [| b]. {
      cbn in Hlb, Hij.
      destruct bef as [| c]; [ easy | ].
      cbn in Hlb.
      injection Hlb; clear Hlb; intros Hlb H; subst c.
      cbn in Hij.
      rewrite permutation_assoc_loop_cons_None in Hij.
      rewrite (List_map_nth' 0) in Hij; [ easy | ].
      rewrite (permutation_assoc_loop_length Heqb); [ easy | ].
      rewrite filter_Some_app; cbn.
      rewrite <- filter_Some_app.
Print permutation_assoc_loop.
...
    revert j la lc Hpab Hj Hij.
    induction lb as [| b]; intros. {
      cbn in Hpab, Hij.
      rewrite permutation_assoc_loop_cons_None in Hij.
      rewrite (List_map_nth' 0) in Hij; [ easy | ].
      rewrite (permutation_assoc_loop_length Heqb); [ easy | ].
      now rewrite filter_Some_map_Some.
    }
    cbn in Hij.
...
apply (permutation_sym Heqb) in Hpab.
cbn in Hpab.
apply permutation_cons_l_iff in Hpab.
remember (extract (eqb b) la) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hla).
apply Heqb in H; subst x la.
apply (permutation_sym Heqb) in Hpab.
destruct j. {
  destruct bef as [| b']. {
    cbn in Hij.
    now rewrite (equality_refl Heqb) in Hij.
  }
  cbn - [ option_eqb ] in Hij.
  unfold option_eqb in Hij at 1.
  rewrite Hbef in Hij; [ | now left ].
...
    destruct la as [| a]; [ easy | ].
    cbn - [ option_eqb ] in Hij.
    unfold option_eqb in Hij at 1.
    remember (eqb b a) as ba eqn:Hba; symmetry in Hba.
    destruct ba. {
      apply Heqb in Hba; subst b.
      cbn in Hpab.
      apply (permutation_cons_inv Heqb) in Hpab.
      cbn in Hij.
      destruct j; [ easy | ].
      cbn in Hj; apply Nat.succ_lt_mono in Hj.
      rewrite permutation_assoc_loop_cons_None in Hij.
      rewrite (List_map_nth' 0) in Hij. 2: {
        rewrite (permutation_assoc_loop_length Heqb); [ easy | ].
        rewrite filter_Some_app; cbn.
        now do 2 rewrite filter_Some_map_Some.
      }
      apply Nat.succ_inj in Hij.
      now apply IHlb in Hij.
    }
...
Search (permutation_assoc_loop _ _ (_ ++ _)).
Print permutation_assoc_loop.
Search (length (permutation_assoc_loop _ _ _)).
...
    destruct (lt_eq_lt_dec j (length bef)) as [[Hjb| Hjb]| Hjb]. {
      clear Hi Hj Hlen.
      revert j la lb Hpab Hlb Hij Hjb.
      induction bef as [| bo]; intros; [ easy | ].
      destruct lb as [| b]; [ easy | ].
      cbn in Hlb.
      injection Hlb; clear Hlb; intros Hlb H; subst bo.
      cbn in Hjb, Hij.
      destruct j. {
        destruct la as [| a']; [ easy | ].
        cbn - [ option_eqb ] in Hij.
        unfold option_eqb in Hij at 1.
        remember (eqb b a') as ba' eqn:Hba'; symmetry in Hba'.
        destruct ba'; [ easy | ].
        remember (extract (λ bo, option_eqb eqb bo (Some a')) (bef ++ None :: aft)) as lxl eqn:Hlxl.
        symmetry in Hlxl.
        destruct lxl as [((bef', x), aft')| ]; [ | easy ].
        cbn in Hij.
        apply Nat.succ_inj in Hij.
        apply extract_Some_iff in Hlxl.
        destruct Hlxl as (Hbef' & H & Hbna).
        cbn in H.
        destruct x as [x| ]; [ | easy ].
        apply Heqb in H; subst x.
        now apply List_app_eq_app' in Hbna.
      }
      apply Nat.succ_lt_mono in Hjb.
      destruct la as [| a']; [ easy | ].
      cbn - [ option_eqb ] in Hij.
      unfold option_eqb in Hij at 1.
      remember (eqb b a') as ba' eqn:Hba'; symmetry in Hba'.
      destruct ba'. {
        cbn in Hij.
        apply Heqb in Hba'; subst a'.
        apply (permutation_trans Heqb) with (la := b :: a :: la) in Hpab. 2: {
          now apply permutation_swap.
        }
        apply (permutation_cons_inv Heqb) in Hpab.
        destruct la as [| a']. {
          cbn in Hij.
          now rewrite Tauto_match_nat_same in Hij.
        }
        cbn - [ option_eqb ] in Hij.
        unfold option_eqb in Hij at 1.
        remember (extract (λ bo, option_eqb eqb bo (Some a')) (bef ++ None :: aft)) as lxl eqn:Hlxl.
        symmetry in Hlxl.
        destruct lxl as [((bef', x), aft')| ]. 2: {
          now rewrite List_nth_nil in Hij.
        }
        apply extract_Some_iff in Hlxl.
        destruct Hlxl as (Hbef' & H & Hbna).
        cbn in H.
        destruct x as [x| ]; [ | easy ].
        apply Heqb in H; subst x.
        cbn in Hij.
        destruct j. {
          apply Nat.succ_inj in Hij.
          now apply List_app_eq_app' in Hbna.
        }
        rewrite permutation_assoc_loop_cons_None in Hij.
        rewrite (List_map_nth' 0) in Hij. 2: {
          rewrite (permutation_assoc_loop_length Heqb). 2: {
            rewrite filter_Some_inside.
            rewrite <- filter_Some_app.
...
(* marche pas, il faudrait démontrer que c'est une permut_list :
   ça boucle *)
  apply (f_equal (ff_app (permutation_assoc eqb lb la))) in Hij.
...
  rewrite (permutation_assoc_permutation_assoc_inv Heqb) in Hij.
...
specialize canon_assoc_of_multiv_loop_map_multiv_is_permut_list as H1.
specialize (H1 _ eqb la lb 0 []).
erewrite map_ext_in in H1. 2: {
  intros j Hj.
  now rewrite Nat.sub_0_r.
}
now rewrite map_id in H1.
...

Theorem permutation_fun_nth : ∀ A (eqb : A → _),
  equality eqb →
  ∀ d la lb i,
  permutation eqb la lb
  → i < length la
  → nth i lb d = nth (permutation_fun eqb la lb i) la d.
Proof.
intros * Heqb * Hpab Hi.
unfold permutation_fun.
set (l := permutation_assoc eqb la lb).
unfold unsome.
remember (List_rank (Nat.eqb i) l) as j eqn:Hj; symmetry in Hj.
destruct j as [j| ]. 2: {
  specialize (List_rank_None 0 (Nat.eqb i) l Hj) as H1.
(*
  subst l.
  rewrite (permutation_assoc_length Heqb) in H1; [ | easy ].
  set (l := permutation_assoc eqb la lb) in H1.
*)
  set (l' := permutation_assoc eqb lb la).
  specialize (H1 (nth i l' 0)).
  assert (H : nth i l' 0 < length l). {
    unfold l.
    rewrite (permutation_assoc_length Heqb); [ | easy ].
    specialize (permutation_length Heqb Hpab) as Hlab.
    rewrite Hlab.
    unfold l'.
    apply (permutation_sym Heqb) in Hpab.
    apply (nth_permutation_assoc_ub Heqb); [ easy | congruence ].
  }
  specialize (H1 H); clear H.
  apply Nat.eqb_neq in H1.
  exfalso; apply H1; clear H1.
  unfold l, l'; symmetry.
  do 2 rewrite fold_ff_app.
...
  now apply permutation_assoc_permutation_assoc_inv.
...

Theorem permutation_permut : ∀ la lb,
  permutation Nat.eqb la lb
  → is_permut_list la
  → is_permut_list lb.
Proof.
intros * Hab Ha.
assert (Hlab : length la = length lb). {
  now apply (permutation_length Nat_eqb_equality).
}
split. {
  intros i Hi.
  rewrite <- Hlab.
  apply Ha.
  apply (permutation_in Nat_eqb_equality) with (la := lb); [ | easy ].
  now apply (permutation_sym Nat_eqb_equality).
} {
  destruct Ha as (Hap, Hal).
  specialize (NoDup_nat _ Hal) as H1.
  unfold ff_app in H1.
  apply nat_NoDup.
  intros i j Hi Hj Hij.
  unfold ff_app in Hij.
  rewrite <- Hlab in Hi, Hj.
...
  rewrite (permutation_fun_nth Nat_eqb_equality 0 Hab Hi) in Hij.
   rewrite (permutation_fun_nth Nat_eqb_equality 0 Hab Hj) in Hij.
...
unfold permutation_fun.
set (l := permutation_assoc eqb la lb).
unfold unsome.
remember (List_rank (Nat.eqb i) l) as j eqn:Hj; symmetry in Hj.
destruct j as [j| ]. 2: {
  specialize (List_rank_None 0 (Nat.eqb i) l Hj) as H1.
  set (l' := permutation_assoc eqb lb la).
  specialize (H1 (nth i l' 0)).
  assert (H : nth i l' 0 < length l). {
    unfold l.
    rewrite (permutation_assoc_length Heqb); [ | easy ].
    specialize (permutation_length Heqb Hpab) as Hlab.
    rewrite Hlab.
    unfold l'.
    apply (permutation_sym Heqb) in Hpab.
    apply (nth_permutation_assoc_ub Heqb); [ easy | congruence ].
  }
  specialize (H1 H); clear H.
  apply Nat.eqb_neq in H1.
  exfalso; apply H1; clear H1.
  unfold l, l'; symmetry.
  do 2 rewrite fold_ff_app.
Search (nth (nth _ (permutation_assoc _ _ _) _)).
Search (ff_app (permutation_assoc _ _ _) _).
Theorem permutation_assoc_permutation_assoc_inv : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb i,
  permutation eqb la lb
  → i < length la
  → ff_app (permutation_assoc eqb la lb)
      (ff_app (permutation_assoc eqb lb la) i) = i.
Proof.
intros * Heqb * Hpab Hla.
unfold permutation_assoc.
Print canon_assoc_of_multiv_loop.
(**)
Compute (
let la := [2;3;5;3;2;1] in
let lb := [1;5;2;3;2;3] in
let eqb := Nat.eqb in
(multivalued eqb la lb, multivalued eqb lb la)).
...
Compute (
let la := [2;3;5;3;2;1] in
let lb := [1;5;2;3;2;3] in
let eqb := Nat.eqb in
(canon_assoc_of_multiv Nat.eqb (multivalued eqb la lb),
 canon_assoc_of_multiv Nat.eqb (multivalued eqb lb la))).
Compute (
let la := [2;3;5;3;2;1] in
let lb := [1;5;2;3;2;3] in
let eqb := Nat.eqb in
(canon_assoc_of_multiv Nat.eqb (multivalued eqb la lb),
 isort_rank Nat.leb (canon_assoc_of_multiv Nat.eqb (multivalued eqb lb la)))).
Search isort_rank.
...
let i := 0 in

nth i (multivalued eqb la lb) []).
...
revert lb i Hpab Hla.
induction la as [| a]; intros; [ easy | cbn ].
rewrite fold_ff_app.
(**)
apply permutation_cons_l_iff in Hpab.
remember (extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x.
subst lb.
remember (multivalued_elem eqb (bef ++ a :: aft) 0 a) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [| c]. {
  exfalso; revert Hlc.
  apply (multivalued_elem_neq_nil Heqb).
  now apply in_or_app; right; left.
}
cbn.
rewrite first_non_excl_nil_l.
generalize Hlc; intros H.
apply (multivalued_elem_inside Heqb) in H; [ | easy ].
cbn in H; subst c.
remember (ff_app _ _) as j eqn:Hj; symmetry in Hj.
cbn in Hj.
destruct j. {
  induction bef as [| b]. {
    cbn in Hlc, Hj.
    rewrite (equality_refl Heqb) in Hlc, Hj.
    injection Hlc; clear Hlc; intros Hlc.
    destruct i; [ easy | exfalso ].
    cbn in Hj, Hla, Hpab.
    apply Nat.succ_lt_mono in Hla.
    specialize (IHla aft i Hpab Hla) as H1.
    unfold canon_assoc_of_multiv in H1.
    unfold multivalued in H1.
...
destruct lb as [| b]; [ now apply permutation_nil_r in Hpab | ].
...
destruct j. 2: {
  unfold multivalued in Hj.
Print canon_assoc_of_multiv_loop.


Print multivalued_elem.
...
...
Search first_non_excl.
cbn.
Search (first_non_excl).
Print canon_assoc_of_multiv.
Print canon_assoc_of_multiv_loop.
...
remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  cbn - [ option_eqb ] in H1.
  specialize (H1 (Some a)) as H2; cbn in H2.
  assert (H : Some a ∈ map Some lb). {
    apply in_map_iff.
    exists a; split; [ easy | ].
    specialize (proj1 (permutation_in Heqb Hpab a)) as H3.
    now apply H3; left.
  }
  specialize (H2 H); clear H.
  now rewrite (equality_refl Heqb) in H2.
}
cbn.
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & Hx & Hsome).
cbn in Hx.
destruct x as [b| ]; [ | easy ].
apply Heqb in Hx; subst b.
remember (permutation_assoc_loop eqb lb (Some a :: map Some la)) as l eqn:Hl.
remember (ff_app l i) as j eqn:Hj; symmetry in Hj.
destruct j. {
  apply (f_equal length) in Hsome.
  rewrite map_length, app_length in Hsome; cbn in Hsome.
  subst l.

Theorem glop : ∀ A (eqb : A → _),
  equality eqb →
  ∀ d la lb i j,
  permutation eqb la lb
  → ff_app (permutation_assoc_loop eqb la (map Some lb)) i = j
  → nth i la d = nth j lb d.
Proof.
intros * Heqb * Hpab Hij.
revert d lb i j Hpab Hij.
induction la as [| a]; intros; cbn. {
  apply permutation_nil_l in Hpab; subst lb.
  cbn in Hij.
  destruct i; [ now subst j | ].
  now subst j.
}
destruct i. {
  cbn - [ option_eqb ] in Hij.
  remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef, x), aft)| ]. 2: {
    specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
    specialize (H1 (Some a)).
    cbn in H1.
    rewrite (equality_refl Heqb) in H1.
    assert (H : Some a ∈ map Some lb). {
      apply in_map_iff.
      exists a; split; [ easy | ].
      specialize (proj1 (permutation_in Heqb Hpab a)) as H2.
      apply (H2 (or_introl eq_refl)).
    }
    now specialize (H1 H); clear H.
  }
  cbn in Hij; subst j.
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef & Hx & Hsome).
  cbn in Hx.
  destruct x as [x| ]; [ | easy ].
  apply Heqb in Hx; subst x.
  assert (H : nth (length bef) (map Some lb) None = Some a). {
    rewrite Hsome.
    rewrite app_nth2; [ | now unfold ge ].
    now rewrite Nat.sub_diag.
  }
  rewrite (List_map_nth' d) in H. 2: {
    apply (f_equal length) in Hsome.
    rewrite map_length, app_length in Hsome; cbn in Hsome.
    flia Hsome.
  }
  now injection H; clear H; intros.
}
cbn - [ option_eqb ] in Hij.
(**)
apply permutation_cons_l_iff in Hpab.
remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & Hx & Hsome).
cbn in Hx.
apply Heqb in Hx; subst x.
subst lb.
remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef', x), aft')| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  specialize (H1 (Some a)).
  cbn in H1.
  rewrite (equality_refl Heqb) in H1.
  assert (H : Some a ∈ map Some (bef ++ a :: aft)). {
    apply in_map_iff.
    exists a; split; [ easy | ].
    now apply in_or_app; right; left.
  }
  now specialize (H1 H); clear H.
}
cbn in Hij; subst j.
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef' & Hx & Hsome).
cbn in Hx.
destruct x as [x| ]; [ | easy ].
apply Heqb in Hx; subst x.
rewrite map_app in Hsome; cbn in Hsome.
assert (H : map Some bef = bef'). {
  clear Hpab.
  revert bef Hbef Hsome.
  induction bef' as [| b']; intros. {
    destruct bef as [| b]; [ easy | exfalso ].
    cbn in Hsome.
    injection Hsome; clear Hsome; intros Hsome H; subst b.
    specialize (Hbef a (or_introl eq_refl)) as H1.
    now rewrite (equality_refl Heqb) in H1.
  }
  cbn in Hsome.
  destruct bef as [| b]. {
    exfalso.
    cbn in Hsome.
    injection Hsome; clear Hsome; intros Hsome H; subst b'.
    specialize (Hbef' _ (or_introl eq_refl)) as H1; cbn in H1.
    now rewrite (equality_refl Heqb) in H1.
  }
  cbn in Hsome |-*.
  injection Hsome; clear Hsome; intros Hsome H; subst b'.
  f_equal.
  apply IHbef'; [ | | easy ]. {
    intros bo Hbo.
    apply (Hbef' bo (or_intror Hbo)).
  } {
    intros b' Hb'.
    now apply Hbef; right.
  }
}
subst bef'.
apply app_inv_head in Hsome.
injection Hsome; clear Hsome; intros; subst aft'.
remember (permutation_assoc_loop _ _ _) as lbo eqn:Hlbo; symmetry in Hlbo.
destruct (lt_dec (nth i lbo 0) (length bef)) as [Hib| Hib]. {
  rewrite app_nth1; [ | easy ].
  specialize app_nth1 as H1.
  specialize (H1 _ bef aft).
  rewrite <- H1; [ | easy ].
  clear H1.
  apply IHla; [ easy | ].
  rewrite map_app.

Theorem permutation_assoc_loop_cons_None' : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lbo lco,
  permutation_assoc_loop eqb la (lbo ++ None :: lco) =
  permutation_assoc_loop eqb la lbo ++
  map S (permutation_assoc_loop eqb la lco).
Proof.
intros * Heqb *.
revert lbo lco.
induction la as [| a]; intros; [ easy | ].
cbn - [ option_eqb ].
remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  cbn - [ option_eqb ] in H1.
  clear Hlxl.
  remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef, x), aft)| ]. 2: {
    specialize (proj1 (extract_None_iff _ _) Hlxl) as H2.
    cbn - [ option_eqb ] in H2.
    clear Hlxl.
    remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
    destruct lxl as [((bef, x), aft)| ]; [ exfalso | easy ].
    apply extract_Some_iff in Hlxl.
    destruct Hlxl as (Hbef & H & Hlco).
    cbn in H.
    destruct x as [x| ]; [ | easy ].
    apply Heqb in H; subst x.
    specialize (H1 (Some a)).
    assert (H : Some a ∈ lbo ++ None :: lco). {
      apply in_or_app; right; right.
      rewrite Hlco.
      now apply in_or_app; right; left.
    }
    specialize (H1 H); clear H; cbn in H1.
    now rewrite (equality_refl Heqb) in H1.
  }
  exfalso.
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef & H & Hlbo).
  cbn in H.
  destruct x as [x| ]; [ | easy ].
  apply Heqb in H; subst x.
  specialize (H1 (Some a)).
  assert (H : Some a ∈ lbo ++ None :: lco). {
    apply in_or_app; left.
    rewrite Hlbo.
    now apply in_or_app; right; left.
  }
  specialize (H1 H); clear H; cbn in H1.
  now rewrite (equality_refl Heqb) in H1.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlbo).
cbn in H.
destruct x as [x| ]; [ | easy ].
apply Heqb in H; subst x.
remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef', x), aft')| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  cbn - [ option_eqb ] in H1.
  clear Hlxl.
  remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef', x), aft')| ]. 2: {
    specialize (proj1 (extract_None_iff _ _) Hlxl) as H2.
    cbn - [ option_eqb ] in H2.
    clear Hlxl; exfalso.
    specialize (@in_dec (option A)) as H3.
    specialize (H3 (option_eq_dec (equality_dec Heqb))).
    destruct (H3 (Some a) lbo) as [H4| H4]. {
      specialize (H1 _ H4); cbn in H1.
      now rewrite (equality_refl Heqb) in H1.
    }
    destruct (H3 (Some a) lco) as [H5| H5]. {
      specialize (H2 _ H5); cbn in H2.
      now rewrite (equality_refl Heqb) in H2.
    }
    assert (H6 : Some a ∉ lbo ++ None :: lco). {
      intros H.
      apply in_app_or in H.
      now destruct H as [H| [H| H]].
    }
    rewrite Hlbo in H6; apply H6; clear H6.
    now apply in_or_app; right; left.
  }
  cbn.
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef' & H & Hlco).
  cbn in H.
  destruct x as [x| ]; [ | easy ].
  apply Heqb in H; subst x.
  rewrite Hlco in Hlbo.
  f_equal. 2: {
    assert (H : bef = lbo ++ None :: bef'). {
      induction lbo as [| bo]. {
        cbn in Hlbo |-*.
        induction bef as [| b]; [ easy | ].
        cbn in Hlbo.
        injection Hlbo; clear Hlbo; intros Hlbo H; subst b.
        f_equal.
...
    rewrite H.
    rewrite <- app_assoc; cbn.
    rewrite IHla.
(* ouais, chais pas, faut voir *)
...
    rewrite IHla.
    rewrite IHla.
    rewrite map_app, map_map.
    f_equal. {
...
    assert (H : ∃ lb1, bef = map Some lb1). {
      induction bef as [| bo]; [ now exists [] | cbn ].
      destruct lb1 as [| b]. {
        cbn in Hb1.
        injection Hb1; clear Hb1; intros Hb1 H; subst bo.
        exfalso.
      specialize (Hbef _ (or_introl eq_refl)).
      cbn in Hbef.

...
    apply extract_Some_iff in Hlxl.
    destruct Hlxl as (Hbef & H & Hb2).
    cbn in H.
    destruct x as [x| ]; [ | easy ].
    apply Heqb in H; subst x.
    specialize (H1 (Some a)).
    assert (H : Some a ∈ map Some lb1 ++ None :: map Some lb2). {
      apply in_or_app; right; right.
      rewrite Hb2.
      now apply in_or_app; right; left.
    }
    specialize (H1 H); clear H; cbn in H1.
    now rewrite (equality_refl Heqb) in H1.
  }
...
induction lbo1 as [| bo]; intros; cbn. {
...
permutation_assoc_loop_cons_None:
  ∀ (A : Type) (eqb : A → A → bool) (la : list A) (lbo : list (option A)),
    permutation_assoc_loop eqb la (None :: lbo) =
    map S (permutation_assoc_loop eqb la lbo)
...
apply glop with (d := a) in Hj.
cbn in Hj.
injection Hj; clear Hj; intros Hj.
...
Theorem permutation_assoc_loop_permutation_assoc_loop_inv : ∀ A (eqb : A → _),
  equality eqb →
  ∀ lao lbo i,
  permutation eqb (filter_Some lao) (filter_Some lbo)
  → i < length (filter_Some lao)
  → ff_app
      (permutation_assoc_loop eqb (filter_Some lao)
          (map Some (filter_Some lbo)))
      (ff_app
         (permutation_assoc_loop eqb (filter_Some lbo)
            (map Some (filter_Some lao))) i) = i.
Proof.
intros * Heqb * Hpab Hab.
revert lbo i Hpab Hab.
induction lao as [| ao]; intros; [ easy | cbn ].
destruct ao as [a| ]. 2: {
  rewrite fold_ff_app.
  cbn in Hpab, Hab.
  now apply IHlao.
}
cbn in Hpab, Hab.
cbn - [ option_eqb map ].
remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  specialize (H1 (Some a)).
  cbn in H1.
  rewrite (equality_refl Heqb) in H1.
  assert (H : Some a ∈ map Some (filter_Some lbo)). {
    apply in_map_iff.
    exists a; split; [ easy | ].
    specialize (proj1 (permutation_in Heqb Hpab a)) as H2.
    apply (H2 (or_introl eq_refl)).
  }
  now specialize (H1 H); clear H.
}
cbn.
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & Hx & Hsome).
cbn in Hx.
destruct x as [b| ]; [ | easy ].
apply Heqb in Hx; subst b.
apply permutation_cons_l_iff in Hpab.
remember (extract (eqb a) (filter_Some lbo)) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef', x), aft')| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef' & Hx & Hfil).
apply Heqb in Hx; subst x.
rewrite Hfil in Hsome |-*.
rewrite map_app in Hsome; cbn in Hsome.
assert (H : map Some bef' = bef). {
  clear Hfil Hpab.
  revert bef' Hbef' Hsome.
  induction bef as [| b]; intros. {
    destruct bef' as [| b']; [ easy | exfalso ].
    cbn in Hsome.
    injection Hsome; clear Hsome; intros Hsome H; subst b'.
    specialize (Hbef' a (or_introl eq_refl)) as H1.
    now rewrite (equality_refl Heqb) in H1.
  }
  cbn in Hsome.
  destruct bef' as [| b']. {
    exfalso.
    cbn in Hsome.
    injection Hsome; clear Hsome; intros Hsome H; subst b.
    specialize (Hbef _ (or_introl eq_refl)) as H1; cbn in H1.
    now rewrite (equality_refl Heqb) in H1.
  }
  cbn in Hsome |-*.
  injection Hsome; clear Hsome; intros Hsome H; subst b.
  f_equal.
  apply IHbef; [ | | easy ]. {
    intros bo Hbo.
    apply (Hbef bo (or_intror Hbo)).
  } {
    intros b Hb.
    now apply Hbef'; right.
  }
}
subst bef.
rewrite map_length.
apply app_inv_head in Hsome.
injection Hsome; clear Hsome; intros; subst aft.
rename bef' into bef; rename aft' into aft.
remember (ff_app _ _) as j eqn:Hj; symmetry in Hj.
destruct j. {
  revert i Hab Hj.
  induction bef as [| b]; intros. {
    cbn in Hj.
    rewrite (equality_refl Heqb) in Hj.
    cbn in Hj.
    destruct i; [ easy | exfalso ].
    rewrite permutation_assoc_loop_cons_None in Hj.
    rewrite (List_map_nth' 0) in Hj; [ easy | ].
    rewrite (permutation_assoc_loop_length Heqb). 2: {
      rewrite filter_Some_map_Some.
      now apply permutation_sym.
    }
    apply Nat.succ_lt_mono in Hab.
    now rewrite (permutation_length Heqb Hpab) in Hab.
  }
  cbn - [ option_eqb ] in Hj.
  unfold option_eqb in Hj at 1.
  rewrite Hbef' in Hj; [ | now left ].
  remember (extract _ _) as lxl eqn:Hlxl.
  symmetry in Hlxl.
  destruct lxl as [((bef', x), aft')| ]. 2: {
    clear Hj; cbn.
    specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
    cbn - [ option_eqb ] in H1.
    specialize (H1 (Some b)) as H2.
    assert (H : Some b ∈ map Some (filter_Some lao)). {
      apply in_map_iff.
      exists b; split; [ easy | ].
      now apply (permutation_in Heqb Hpab); cbn; left.
    }
    specialize (H2 H); clear H; cbn in H2.
    now rewrite (equality_refl Heqb) in H2.
  }
  cbn in Hj.
  destruct i; [ easy | ].
  cbn; f_equal.
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef'' & Hx & Hmap).
  cbn in Hx.
  destruct x as [x| ]; [ | easy ].
  apply Heqb in Hx; subst x.
(* c'est possible que je puisse y arriver ; pas sûr ;
   en tous cas, c'est compliqué, par cette voie *)
...
destruct j. {
  generalize Hsome; intros H.
  apply (f_equal length) in H.
  rewrite map_length, app_length in H; cbn in H.
  destruct bef as [| b]. {
    cbn in Hsome, H; clear Hbef.
    destruct i; [ easy | exfalso ].
...
specialize permutation_assoc_loop_permutation_assoc_loop_inv as H1.
specialize (H1 _ eqb (map Some la) (map Some lb)).
do 2 rewrite filter_Some_map_Some in H1.
rewrite map_length in H1.
now apply H1.
...
intros * Heqb * Hlab Hla.
revert lb i Hlab Hla.
induction la as [| a]; intros; cbn; [ easy | ].
destruct lb as [| b]; [ easy | cbn ].
remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  apply Heqb in Hab; subst b.
  rewrite (equality_refl Heqb); cbn.
  destruct i; [ easy | ].
  rewrite fold_ff_app.
...
Search (permutation_assoc _ _ []).
Theorem permutation_assoc_nil_r : ∀ A (eqb : A → _) la,
  permutation_assoc eqb la [] = [].
Proof. now intros; destruct la. Qed.
rewrite permutation_assoc_nil_r; cbn.
...
apply permutation_assoc_permutation_assoc_inv.
...
intros * Heqb * Hpab.
revert lb Hpab.
induction la as [| a]; intros; [ easy | ].
cbn - [ option_eqb ].
remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  destruct lb as [| b]; [ easy | ].
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  specialize (permutation_in Heqb Hpab) as H2.
  specialize (H1 (Some a)).
  assert (H : Some a ∈ map Some (b :: lb)). {
    now apply in_map, H2; left.
  }
  specialize (H1 H); clear H.
  cbn in H1.
  now rewrite (equality_refl Heqb) in H1.
}
cbn; f_equal.
...
apply IHla.
Print permutation_assoc_loop.
...
Theorem permutation_assoc_loop_length : ∀ A (eqb : A → _) la lbo,
  length (permutation_assoc_loop eqb la lbo) = length la.
Proof.
intros.
Print permutation_assoc_loop.
...
revert lbo.
induction la as [| a]; intros; [ easy | ].
cbn - [ option_eqb ].
remember (extract _ lbo) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  destruct lbo as [bo| ]. {
    cbn in Hlxl.
...
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  specialize (H1 None); cbn in H1.
...
  rewrite permutation_assoc_loop_length.
...
(*
Search (nth _ _ _ < length _).
...
  specialize (List_rank_None 0 (Nat.eqb i) Hj) as H1.
  apply List_rank_None in Hj.
Search (nth (unsome _ _)).
Search unsome.
Print unsome.
...
Theorem nth_unsome : ∀ A (d : A) la l, nth (unsome 0 l) la d = nth
Theorem permutation_assoc_loop_nth : ∀ A (eqb : A → _) d la lbo i,
  i < length la
  → nth i lb d = nth (unsome 0 (List_rank (Nat.eqb i) (permutation_assoc_loop eqb la lbo))) la d.


revert d lb i Hi.
induction la as [| a]; intros; [ easy | cbn ].
...

*)
Admitted.
Show.
  set (f := permutation_fun Nat.eqb la lb).
  set (g := permutation_fun Nat.eqb lb la).
  rewrite <- Hlab in Hi, Hj.
  specialize (H1 (f i) (f j)).
  assert (H : f i < length la). {
    unfold f.
...
  specialize (H1 H); clear H.
  assert (H : f j < length la) by admit.
  specialize (H1 H); clear H.
  assert (H2 : nth (f i) la 0 = nth i lb 0) by admit.
  assert (H3 : nth (f j) la 0 = nth j lb 0) by admit.
  assert (H : nth (f i) la 0 = nth (f j) la 0) by congruence.
  specialize (H1 H); clear H.
  apply (f_equal g) in H1.
Theorem permutation_fun_inv_permutation_fun : ∀ A (eqb : A → _) la lb i,
  permutation_fun eqb la lb (permutation_fun eqb lb la i) = i.
Admitted.
  unfold f, g in H1.
  rewrite (permutation_fun_inv_permutation_fun Nat.eqb lb la) in H1.
  rewrite (permutation_fun_inv_permutation_fun Nat.eqb lb la) in H1.
  easy.
...
  specialize (proj1 (Permutation_nth _ _ 0) Hab) as H1.
  destruct H1 as (H1 & f & H2 & H3 & H4).
  rewrite H4 in Hij; [ | easy ].
  rewrite H4 in Hij; [ | easy ].
  do 2 rewrite fold_ff_app in Hij.
  apply (NoDup_nat _ Hal) in Hij; [ | now apply H2 | now apply H2 ].
  now apply H3.
...
  specialize (proj1 (permutation_nth _ _ 0) Hab) as H1.
  destruct H1 as (H1 & f & H2 & H3 & H4).
  rewrite H4 in Hij; [ | easy ].
  rewrite H4 in Hij; [ | easy ].
  do 2 rewrite fold_ff_app in Hij.
  apply (NoDup_nat _ Hal) in Hij; [ | now apply H2 | now apply H2 ].
  now apply H3.
...
Permutation_nth
     : ∀ (A : Type) (l l' : list A) (d : A),
         Permutation l l'
         ↔ (let n := length l in
            length l' = n
            ∧ (∃ f : nat → nat,
                 FinFun.bFun n f ∧ FinFun.bInjective n f ∧ (∀ x : nat, x < n → nth x l' d = nth (f x) l d)))

(*
  rewrite <- Hlab in Hi, Hj.
  specialize (permutation_in Nat_eqb_equality Hab) as H2.
  assert (Hib : nth i lb 0 ∈ lb) by now apply nth_In.
  assert (Hjb : nth j lb 0 ∈ lb) by now apply nth_In.
  apply H2 in Hib, Hjb.
  apply (In_nth _ _ 0) in Hib.
  apply (In_nth _ _ 0) in Hjb.
  destruct Hib as (i' & Hi' & Hi'i).
  destruct Hjb as (j' & Hj' & Hj'j).
  rewrite Hij, <- Hj'j in Hi'i.
  apply H1 in Hi'i; [ | easy | easy ].
(* oui, non, bon *)
Check Permutation_nth.
Check list_eqb.
Print list_eqb.
*)
...
Search permutation.
About Permutation_nth.
  specialize (proj1 (Permutation_nth _ _ 0) Hab) as H1.
  destruct H1 as (H1 & f & H2 & H3 & H4).
  rewrite H4 in Hij; [ | easy ].
  rewrite H4 in Hij; [ | easy ].
  do 2 rewrite fold_ff_app in Hij.
  apply (NoDup_nat _ Hal) in Hij; [ | now apply H2 | now apply H2 ].
  now apply H3.
}
Qed.
*)

(* transposition *)

Definition transposition i j k :=
  if k =? i then j else if k =? j then i else k.

Definition list_swap_elem {A} d (l : list A) i j :=
  map (λ k, nth (transposition i j k) l d) (seq 0 (length l)).

Theorem fold_transposition : ∀ i j k,
  (if k =? i then j else if k =? j then i else k) = transposition i j k.
Proof. easy. Qed.

Theorem transposition_lt : ∀ i j k n,
  i < n
  → j < n
  → k < n
  → transposition i j k < n.
Proof.
intros * Hi Hj Hk.
unfold transposition.
do 2 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec k i); [ easy | ].
now destruct (Nat.eq_dec k j).
Qed.

Theorem transposition_involutive : ∀ p q i,
  transposition p q (transposition p q i) = i.
Proof.
intros.
unfold transposition.
do 4 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec i p) as [Hip| Hip]. {
  destruct (Nat.eq_dec q p) as [Hqp| Hqp]; [ congruence | ].
  destruct (Nat.eq_dec q q) as [H| H]; [ congruence | easy ].
}
destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
  destruct (Nat.eq_dec p p) as [H| H]; [ congruence | easy ].
}
destruct (Nat.eq_dec i p) as [H| H]; [ easy | clear H ].
destruct (Nat.eq_dec i q) as [H| H]; [ easy | clear H ].
easy.
Qed.

Theorem list_swap_elem_length : ∀ A (d : A) l p q,
  length (list_swap_elem d l p q) = length l.
Proof.
intros.
unfold list_swap_elem.
now rewrite map_length, seq_length.
Qed.

Theorem list_swap_elem_involutive : ∀ A (d : A) l i j,
  i < length l
  → j < length l
  → list_swap_elem d (list_swap_elem d l i j) i j = l.
Proof.
intros * Hi Hj.
unfold list_swap_elem.
rewrite map_length, seq_length.
erewrite map_ext_in. 2: {
  intros k Hk; apply in_seq in Hk.
  rewrite (List_map_nth' 0). 2: {
    now rewrite seq_length; apply transposition_lt.
  }
  rewrite seq_nth; [ | now apply transposition_lt ].
  rewrite Nat.add_0_l.
  now rewrite transposition_involutive.
}
symmetry.
apply List_map_nth_seq.
Qed.

Theorem permut_list_ub : ∀ l i,
  is_permut_list l → i < length l → nth i l 0 < length l.
Proof.
intros * Hp Hin.
destruct Hp as (Hp1, Hp2).
clear Hp2.
now apply Hp1, nth_In.
Qed.

Theorem transposition_out : ∀ i j k, k ≠ i → k ≠ j → transposition i j k = k.
Proof.
intros * Hi Hj.
unfold transposition.
do 2 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec k i) as [H| H]; [ easy | clear H ].
now destruct (Nat.eq_dec k j).
Qed.

Theorem transposition_1 : ∀ i j, transposition i j i = j.
Proof.
intros.
unfold transposition.
now rewrite Nat.eqb_refl.
Qed.

Theorem transposition_2 : ∀ i j, transposition i j j = i.
Proof.
intros.
unfold transposition.
rewrite Nat.eqb_refl.
rewrite if_eqb_eq_dec.
now destruct (Nat.eq_dec j i).
Qed.

Theorem transposition_id : ∀ i j, transposition i i j = j.
Proof.
intros.
unfold transposition.
do 2 rewrite if_eqb_eq_dec.
now destruct (Nat.eq_dec j i).
Qed.

Theorem transposition_comm : ∀ i j k, transposition i j k = transposition j i k.
Proof.
intros.
unfold transposition.
do 4 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec k i) as [Hki| Hki]. {
  destruct (Nat.eq_dec k j) as [Hkj| Hkj]; [ congruence | easy ].
} {
  destruct (Nat.eq_dec k j) as [Hkj| Hkj]; [ congruence | easy ].
}
Qed.

Theorem list_swap_elem_is_permut_list : ∀ σ p q,
  p < length σ
  → q < length σ
  → is_permut_list σ
  → is_permut_list (list_swap_elem 0 σ p q).
Proof.
intros * Hp Hq Hσ.
unfold is_permut_list, list_swap_elem.
rewrite map_length, seq_length.
split; cbn. {
  intros i Hi.
  apply in_map_iff in Hi.
  destruct Hi as (j & Hji & Hj).
  apply in_seq in Hj.
  rewrite <- Hji.
  apply permut_list_ub; [ easy | ].
  now apply transposition_lt.
} {
  apply nat_NoDup.
  rewrite List_map_seq_length.
  intros i j Hi Hj Hij.
  unfold ff_app in Hij.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  do 2 rewrite Nat.add_0_l in Hij.
  unfold transposition in Hij.
  do 4 rewrite if_eqb_eq_dec in Hij.
  destruct (Nat.eq_dec i p) as [Hip| Hip]. {
    subst i.
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ congruence | ].
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]. {
      now subst j; apply (NoDup_nat _ (proj2 Hσ)).
    }
    apply Nat.neq_sym in Hjq.
    now exfalso; apply Hjq, (NoDup_nat _ (proj2 Hσ)).
  }
  destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]. {
      now subst i j; apply (NoDup_nat _ (proj2 Hσ)).
    }
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ congruence | ].
    apply Nat.neq_sym in Hjp; exfalso; apply Hjp.
    now apply (NoDup_nat _ (proj2 Hσ)).
  }
  destruct (Nat.eq_dec j p) as [Hjp| Hjp]. {
    now exfalso; apply Hiq, (NoDup_nat _ (proj2 Hσ)).
  }
  destruct (Nat.eq_dec j q) as [Hjq| Hjq]. {
    now exfalso; apply Hip, (NoDup_nat _ (proj2 Hσ)).
  }
  now apply (NoDup_nat _ (proj2 Hσ)).
}
Qed.

Theorem list_swap_elem_is_permut : ∀ n σ p q,
  p < n
  → q < n
  → is_permut n σ
  → is_permut n (list_swap_elem 0 σ p q).
Proof.
intros * Hp Hq Hσ.
split; [ | now rewrite list_swap_elem_length; destruct Hσ ].
destruct Hσ as (H1, H2).
rewrite <- H2 in Hp, Hq.
now apply list_swap_elem_is_permut_list.
Qed.

(* *)

Definition sym_gr_inv (sg : list (list nat)) σ :=
  unsome 0 (List_rank (list_eqb Nat.eqb σ) sg).

Theorem sym_gr_inv_inj : ∀ n sg la lb,
  is_sym_gr_list n sg
  → is_permut n la
  → is_permut n lb
  → sym_gr_inv sg la = sym_gr_inv sg lb
  → la = lb.
Proof.
intros * Hsg Hna Hnb Hab.
unfold sym_gr_inv, unsome in Hab.
remember (List_rank (list_eqb Nat.eqb la) sg) as x eqn:Hx.
remember (List_rank (list_eqb Nat.eqb lb) sg) as y eqn:Hy.
move y before x.
symmetry in Hx, Hy.
destruct x as [x| ]. {
  apply (List_rank_Some []) in Hx.
  destruct Hx as (Hxs & Hbefx & Hx).
  apply (list_eqb_eq Nat_eqb_equality) in Hx.
  destruct y as [y| ]. {
    apply (List_rank_Some []) in Hy.
    destruct Hy as (Hys & Hbefy & Hy).
    apply (list_eqb_eq Nat_eqb_equality) in Hy.
    congruence.
  }
  specialize (List_rank_None [] _ _ Hy) as H1; cbn.
  destruct Hsg as (Hsg & Hsg_inj & Hsg_surj).
  specialize (Hsg_surj lb Hnb) as H2.
  apply In_nth with (d := []) in H2.
  destruct H2 as (k & Hk & Hkb).
  specialize (H1 k Hk).
  apply (list_eqb_neq Nat_eqb_equality) in H1.
  now symmetry in Hkb.
}
specialize (List_rank_None [] _ _ Hx) as H1; cbn.
destruct Hsg as (Hsg & Hsg_inj & Hsg_surj).
specialize (Hsg_surj la Hna) as H2.
apply In_nth with (d := []) in H2.
destruct H2 as (k & Hk & Hka).
specialize (H1 k Hk).
apply (list_eqb_neq Nat_eqb_equality) in H1.
now symmetry in Hka.
Qed.

Theorem seq_is_permut_list : ∀ n, is_permut_list (seq 0 n).
Proof.
intros.
split. {
  cbn; rewrite seq_length.
  intros i Hin.
  now rewrite in_seq in Hin.
} {
  apply nat_NoDup.
  cbn; rewrite seq_length.
  intros i j Hi Hj Hij.
  unfold ff_app in Hij.
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  easy.
}
Qed.

Theorem seq_is_permut : ∀ n, is_permut n (seq 0 n).
Proof.
intros.
split; [ | apply seq_length ].
apply seq_is_permut_list.
Qed.

Theorem sym_gr_inv_lt : ∀ n sg v,
  n ≠ 0
  → is_sym_gr_list n sg
  → sym_gr_inv sg v < length sg.
Proof.
intros * Hnz Hsg.
unfold sym_gr_inv.
unfold unsome.
remember (List_rank _ _) as i eqn:Hi; symmetry in Hi.
destruct i as [i| ]; [ now apply List_rank_Some_lt in Hi | ].
clear Hi.
destruct (lt_dec 0 (length sg)) as [Hs| Hs]; [ easy | ].
apply Nat.nlt_ge in Hs; exfalso.
apply Nat.le_0_r in Hs.
apply length_zero_iff_nil in Hs; subst sg.
destruct Hsg as (_ & _ & Hsurj).
cbn in Hsurj.
apply (Hsurj (seq 0 n)).
apply seq_is_permut.
Qed.

Theorem nth_sym_gr_inv_sym_gr : ∀ sg l n,
  is_sym_gr_list n sg
  → is_permut n l
  → nth (sym_gr_inv sg l) sg [] = l.
Proof.
intros * Hsg (Hp, Hs).
unfold sym_gr_inv, unsome.
remember (List_rank _ _) as i eqn:Hi; symmetry in Hi.
destruct i as [i| ]. {
  apply List_rank_Some with (d := []) in Hi.
  destruct Hi as (His & Hji & Hi).
  now apply (list_eqb_eq Nat_eqb_equality) in Hi.
}
assert (H : l ∉ sg). {
  intros H.
  apply In_nth with (d := []) in H.
  destruct H as (j & Hj & Hjv).
  specialize (List_rank_None [] _ _ Hi Hj) as H.
  apply (list_eqb_neq Nat_eqb_equality) in H.
  now symmetry in Hjv.
}
exfalso; apply H; clear H.
now apply Hsg.
Qed.

Theorem sym_gr_inv_list_el : ∀ n sg i,
  n ≠ 0
  → is_sym_gr_list n sg
  → i < length sg
  → sym_gr_inv sg (nth i sg []) = i.
Proof.
intros * Hnz Hsg Hi.
unfold sym_gr_inv, unsome.
remember (List_rank _ _) as j eqn:Hj; symmetry in Hj.
destruct j as [j| ]. {
  apply List_rank_Some with (d := []) in Hj.
  destruct Hj as (His & Hji & Hj).
  apply (list_eqb_eq Nat_eqb_equality) in Hj.
  destruct Hsg as (Hsg & Hinj & Hsurj).
  assert (Hjs : j < length sg). {
    destruct (lt_dec j (length sg)) as [Hjs| Hjs]; [ easy | exfalso ].
    apply Nat.nlt_ge in Hjs.
    rewrite (@nth_overflow _ _ j) in Hj; [ | easy ].
    specialize (Hsg i Hi) as H1.
    destruct H1 as (H1, H2).
    now rewrite Hj in H1; cbn in H1; subst n.
  }
  now apply Hinj.
}
specialize (List_rank_None [] _ _ Hj Hi) as H1.
now apply (list_eqb_neq Nat_eqb_equality) in H1.
Qed.

Theorem length_of_empty_sym_gr : ∀ sg,
  is_sym_gr_list 0 sg → length sg = 1.
Proof.
intros * Hsg.
destruct Hsg as (Hsg & Hinj & Hsurj).
assert (H : is_permut 0 []). {
  split; [ | easy ].
  now apply is_permut_list_is_permut_list_bool.
}
specialize (Hsurj _ H) as H1; clear H.
apply (In_nth _ _ []) in H1.
destruct H1 as (i & Hil & Hi).
destruct (Nat.eq_dec (length sg) 0) as [Hvz| Hvz]. {
  now rewrite Hvz in Hil.
}
destruct (Nat.eq_dec (length sg) 1) as [Hv1| Hv1]; [ easy | ].
specialize (Hsg 0) as H1.
specialize (Hsg 1) as H2.
specialize (Hinj 0 1) as H3.
assert (H : 0 < length sg) by flia Hvz.
specialize (H1 H); specialize (H3 H); clear H.
assert (H : 1 < length sg) by flia Hvz Hv1.
specialize (H2 H); specialize (H3 H); clear H.
destruct H1 as (H4, H5).
destruct H2 as (H6, H7).
enough (H : nth 0 sg [] = nth 1 sg []). {
  rewrite H in H3.
  now specialize (H3 eq_refl).
}
apply length_zero_iff_nil in H4, H6.
congruence.
Qed.

Fixpoint canon_sym_gr_inv_elem n k (j : nat) :=
  match n with
  | 0 => 0
  | S n' =>
      if lt_dec j (k / n'!) then
        S (canon_sym_gr_inv_elem n' (k mod n'!) j)
      else if lt_dec (k / n'!) j then
        S (canon_sym_gr_inv_elem n' (k mod n'!) (j - 1))
      else 0
  end.

Definition canon_sym_gr_inv_list n k : list nat :=
  map (canon_sym_gr_inv_elem n k) (seq 0 n).

Theorem canon_sym_gr_list_length : ∀ k n,
  length (canon_sym_gr_list n k) = n.
Proof.
intros.
revert k.
induction n; intros; [ easy | cbn ].
f_equal; rewrite map_length.
apply IHn.
Qed.

Theorem canon_sym_gr_list_ub : ∀ n k i,
  k < n!
  → i < n
  → ff_app (canon_sym_gr_list n k) i < n.
Proof.
intros * Hkn Hi.
revert i k Hkn Hi.
induction n; intros; [ easy | cbn ].
destruct i. {
  apply Nat.div_lt_upper_bound; [ apply fact_neq_0 | ].
  now rewrite Nat.mul_succ_r, Nat.add_comm, Nat.mul_comm.
}
apply Nat.succ_lt_mono in Hi.
rewrite (List_map_nth' 0); [ | now rewrite canon_sym_gr_list_length ].
unfold succ_when_ge.
rewrite <- Nat.add_1_r.
apply Nat.add_lt_le_mono; [ | apply Nat_b2n_upper_bound ].
now apply IHn.
Qed.

Theorem canon_sym_gr_inv_list_ub : ∀ n k j,
  k < n!
  → j < n
  → ff_app (canon_sym_gr_inv_list n k) j < n.
Proof.
intros * Hkn Hjn.
unfold canon_sym_gr_inv_list, ff_app.
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ cbn | easy ].
revert k j Hkn Hjn.
induction n; intros; [ easy | cbn ].
destruct (lt_dec j (k / fact n)) as [Hjkn| Hjkn]. {
  apply -> Nat.succ_lt_mono.
  destruct n. {
    cbn in Hkn.
    apply Nat.lt_1_r in Hkn; subst k.
    easy.
  }
  destruct (Nat.eq_dec j (S n)) as [Hjsn| Hjsn]. {
    subst j.
    clear Hjn.
    exfalso; apply Nat.nle_gt in Hjkn; apply Hjkn; clear Hjkn.
    rewrite Nat_fact_succ in Hkn.
    rewrite Nat.mul_comm in Hkn.
    apply Nat.lt_succ_r.
    apply Nat.div_lt_upper_bound; [ | easy ].
    apply fact_neq_0.
  } {
    apply IHn; [ easy | flia Hjn Hjsn ].
  }
} {
  apply Nat.nlt_ge in Hjkn.
  destruct (lt_dec (k / fact n) j) as [Hknj| Hknj]; [ | easy ].
  apply -> Nat.succ_lt_mono.
  destruct n. {
    now apply Nat.lt_1_r in Hjn; subst j.
  }
  apply IHn; [ easy | flia Hjn Hknj ].
}
Qed.

Theorem canon_sym_gr_inv_sym_gr : ∀ n k i,
  k < n!
  → i < n
  → ff_app (canon_sym_gr_inv_list n k) (ff_app (canon_sym_gr_list n k) i) = i.
Proof.
intros * Hkn Hi.
unfold canon_sym_gr_inv_list.
unfold ff_app.
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  now apply canon_sym_gr_list_ub.
}
rewrite seq_nth; [ | now apply canon_sym_gr_list_ub ].
rewrite Nat.add_0_l.
revert k i Hi Hkn.
induction n; intros; [ easy | cbn ].
destruct i. {
  do 2 rewrite <- if_ltb_lt_dec.
  now rewrite Nat.ltb_irrefl.
}
apply Nat.succ_lt_mono in Hi.
rewrite (List_map_nth' 0); [ | now rewrite canon_sym_gr_list_length ].
unfold succ_when_ge.
unfold Nat.b2n.
rewrite if_leb_le_dec.
destruct (le_dec (k / n!) _) as [H1| H1]. {
  destruct (lt_dec _ (k / n!)) as [H| H]; [ flia H1 H | clear H ].
  destruct (lt_dec (k / n!) _) as [H| H]; [ clear H | flia H1 H ].
  f_equal; rewrite Nat.add_sub.
  now apply IHn.
} {
  rewrite Nat.add_0_r.
  destruct (lt_dec _ (k / n!)) as [H| H]; [ clear H | flia H1 H ].
  f_equal.
  now apply IHn.
}
Qed.

Theorem canon_sym_gr_inv_elem_ub : ∀ n k i,
  k < n!
  → i < n
  → canon_sym_gr_inv_elem n k i < n.
Proof.
intros * Hkn Hi.
revert i k Hkn Hi.
induction n; intros; [ easy | cbn ].
destruct (lt_dec i (k / n!)) as [Hikn| Hikn]. {
  apply -> Nat.succ_lt_mono.
  destruct (Nat.eq_dec i n) as [Hin| Hin]. {
    exfalso.
    subst i; clear Hi.
    rewrite Nat_fact_succ in Hkn.
    assert (Hkns : k / n! < S n). {
      apply Nat.div_lt_upper_bound; [ apply fact_neq_0 | ].
      now rewrite Nat.mul_comm.
    }
    flia Hikn Hkns.
  }
  apply IHn; [ easy | flia Hi Hin ].
}
destruct (lt_dec (k / n!) i) as [Hkni| Hkni]; [ | easy ].
apply -> Nat.succ_lt_mono.
apply IHn; [ easy | flia Hi Hkni ].
Qed.

Theorem canon_sym_gr_sym_gr_inv : ∀ n k i,
  k < n!
  → i < n
  → ff_app (canon_sym_gr_list n k) (ff_app (canon_sym_gr_inv_list n k) i) = i.
Proof.
intros * Hkn Hi.
unfold canon_sym_gr_inv_list.
unfold ff_app.
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
rewrite Nat.add_0_l.
revert k i Hi Hkn.
induction n; intros; [ easy | cbn ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  now apply Nat.lt_1_r in Hkn, Hi; subst k i.
}
apply Nat.neq_0_lt_0 in Hnz.
destruct i. {
  destruct (lt_dec 0 (k / n!)) as [Hzkn| Hzkn]. {
    unfold succ_when_ge.
    rewrite (List_map_nth' 0). 2: {
      rewrite canon_sym_gr_list_length.
      now apply canon_sym_gr_inv_elem_ub.
    }
    rewrite IHn; [ | easy | easy ].
    unfold Nat.b2n.
    rewrite if_leb_le_dec.
    destruct (le_dec (k / n!) 0) as [Hknz| Hknz]; [ | easy ].
    now apply Nat.nlt_ge in Hknz.
  }
  apply Nat.nlt_ge in Hzkn.
  apply Nat.le_0_r in Hzkn.
  now rewrite Hzkn; cbn.
}
apply Nat.succ_lt_mono in Hi.
destruct (lt_dec (S i) (k / n!)) as [Hsikn| Hsikn]. {
  destruct (Nat.eq_dec (S i) n) as [Hsin| Hsin]. {
    rewrite Hsin in Hsikn.
    rewrite Nat_fact_succ in Hkn.
    assert (Hkns : k / n! < S n). {
      apply Nat.div_lt_upper_bound; [ apply fact_neq_0 | ].
      now rewrite Nat.mul_comm.
    }
    flia Hsikn Hkns.
  }
  rewrite (List_map_nth' 0). 2: {
    rewrite canon_sym_gr_list_length.
    apply canon_sym_gr_inv_elem_ub; [ easy | flia Hi Hsin ].
  }
  rewrite IHn; [ | flia Hi Hsin | easy ].
  unfold succ_when_ge, Nat.b2n.
  apply Nat.nle_gt in Hsikn.
  apply Nat.leb_nle in Hsikn.
  now rewrite Hsikn, Nat.add_0_r.
}
apply Nat.nlt_ge in Hsikn.
destruct (lt_dec (k / n!) (S i)) as [Hknsi| Hknsi]; [ | flia Hsikn Hknsi ].
rewrite Nat_sub_succ_1.
rewrite (List_map_nth' 0).  2: {
  rewrite canon_sym_gr_list_length.
  now apply canon_sym_gr_inv_elem_ub.
}
rewrite IHn; [ | easy | easy ].
unfold succ_when_ge.
unfold Nat.b2n.
rewrite if_leb_le_dec.
destruct (le_dec (k / n!) i) as [Hkni| Hkni]; [ apply Nat.add_1_r | ].
now apply Nat.succ_le_mono in Hknsi.
Qed.

Theorem nth_canon_sym_gr_list_inj1 : ∀ n k i j,
  k < fact n
  → i < n
  → j < n
  → ff_app (canon_sym_gr_list n k) i = ff_app (canon_sym_gr_list n k) j
  → i = j.
Proof.
intros * Hk Hi Hj Hij.
rewrite <- canon_sym_gr_inv_sym_gr with (n := n) (k := k); [ | easy | easy ].
symmetry.
rewrite <- canon_sym_gr_inv_sym_gr with (n := n) (k := k); [ | easy | easy ].
symmetry.
now rewrite Hij.
Qed.

Theorem nth_canon_sym_gr_list_inj2 : ∀ n i j,
  i < n!
  → j < n!
  → (∀ k, k < n →
     nth k (canon_sym_gr_list n i) 0 = nth k (canon_sym_gr_list n j) 0)
  → i = j.
Proof.
intros * Hin Hjn Hij.
revert i j Hin Hjn Hij.
induction n; intros; [ apply Nat.lt_1_r in Hin, Hjn; congruence | ].
destruct (Nat.eq_dec (i / n!) (j / n!)) as [Hijd| Hijd]. 2: {
  now specialize (Hij 0 (Nat.lt_0_succ _)).
}
destruct (Nat.eq_dec (i mod n!) (j mod n!)) as [Hijm| Hijm]. {
  specialize (Nat.div_mod i n! (fact_neq_0 _)) as Hi.
  specialize (Nat.div_mod j n! (fact_neq_0 _)) as Hj.
  congruence.
}
exfalso; apply Hijm; clear Hijm.
apply IHn. {
  apply Nat.mod_upper_bound, fact_neq_0.
} {
  apply Nat.mod_upper_bound, fact_neq_0.
}
intros k Hk.
cbn - [ fact nth ] in Hij |-*.
specialize (Hij (S k)) as H1.
assert (H : S k < S n) by flia Hk.
specialize (H1 H); clear H.
cbn - [ fact ] in H1.
rewrite Hijd in H1.
rewrite (List_map_nth' 0) in H1; [ | now rewrite canon_sym_gr_list_length ].
rewrite (List_map_nth' 0) in H1; [ | now rewrite canon_sym_gr_list_length ].
unfold succ_when_ge, Nat.b2n in H1.
do 2 rewrite if_leb_le_dec in H1.
destruct (le_dec (j / n!) _) as [H2| H2]. {
  destruct (le_dec (j / n!) _) as [H3| H3]; [ | flia H1 H2 H3 ].
  now apply Nat.add_cancel_r in H1.
}
destruct (le_dec (j / n!) _) as [H3| H3]; [ flia H1 H2 H3 | flia H1 ].
Qed.

Theorem length_canon_sym_gr_inv_list : ∀ n i,
  length (canon_sym_gr_inv_list n i) = n.
Proof.
intros.
unfold canon_sym_gr_inv_list.
apply List_map_seq_length.
Qed.

Theorem NoDup_canon_sym_gr_inv_list : ∀ n i,
  i < n!
  → NoDup (canon_sym_gr_inv_list n i).
Proof.
intros * Hi.
apply nat_NoDup.
rewrite length_canon_sym_gr_inv_list.
intros j k Hj Hk Hjk.
apply (f_equal (ff_app (canon_sym_gr_list n i))) in Hjk.
rewrite canon_sym_gr_sym_gr_inv in Hjk; [ | easy | easy ].
rewrite canon_sym_gr_sym_gr_inv in Hjk; [ | easy | easy ].
easy.
Qed.

Theorem canon_sym_gr_inv_list_is_permut_list : ∀ n i,
  i < n!
  → is_permut_list (canon_sym_gr_inv_list n i).
Proof.
intros * Hi.
split. {
  unfold canon_sym_gr_inv_list.
  rewrite List_map_seq_length.
  intros j Hj.
  apply in_map_iff in Hj.
  destruct Hj as (k & Hkj & Hk).
  apply in_seq in Hk.
  rewrite <- Hkj.
  now apply canon_sym_gr_inv_elem_ub.
} {
  now apply NoDup_canon_sym_gr_inv_list.
}
Qed.

(* *)

Definition sub_canon_permut_list (l : list nat) :=
  map (λ a, a - Nat.b2n (hd 0 l <? a)) (tl l).

Fixpoint canon_sym_gr_list_inv n (l : list nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
      hd 0 l * n'! +
      canon_sym_gr_list_inv n' (sub_canon_permut_list l)
  end.

Theorem sub_canon_permut_list_elem_ub : ∀ l i,
  is_permut_list l
  → S i < length l
  → nth i (sub_canon_permut_list l) 0 < length l - 1.
Proof.
intros * (Hvn, Hn) Hin.
destruct l as [| a]; [ easy | ].
cbn - [ "<?" ] in Hin |-*.
rewrite Nat.sub_0_r.
apply Nat.succ_lt_mono in Hin.
rewrite (List_map_nth' 0); [ | easy ].
unfold Nat.b2n.
rewrite if_ltb_lt_dec.
destruct (lt_dec a (nth i l 0)) as [Hal| Hal]. {
  enough (H : nth i l 0 < S (length l)) by flia Hal H.
  now apply Hvn; right; apply nth_In.
}
apply Nat.nlt_ge in Hal.
rewrite Nat.sub_0_r.
destruct (Nat.eq_dec (nth i l 0) a) as [Hia| Hia]. {
  rewrite Hia.
  apply Nat.succ_lt_mono in Hin.
  symmetry in Hia.
  now specialize (NoDup_nat _ Hn 0 (S i) (Nat.lt_0_succ _) Hin Hia).
}
specialize (Hvn a (or_introl eq_refl)); cbn in Hvn.
flia Hvn Hal Hia.
Qed.

Theorem sub_canon_sym_gr_elem_inj1 : ∀ l i j,
  is_permut_list l
  → S i < length l
  → S j < length l
  → nth i (sub_canon_permut_list l) 0 = nth j (sub_canon_permut_list l) 0
  → i = j.
Proof.
intros * (Hvn, Hn) Hin Hjn Hij.
destruct l as [| a]; [ easy | ].
cbn - [ "<?" ] in Hin, Hjn, Hij.
apply Nat.succ_lt_mono in Hin, Hjn.
rewrite (List_map_nth' 0) in Hij; [ | easy ].
rewrite (List_map_nth' 0) in Hij; [ | easy ].
unfold Nat.b2n in Hij.
do 2 rewrite if_ltb_lt_dec in Hij.
destruct (lt_dec a (nth i l 0)) as [Hai| Hai]. {
  destruct (lt_dec a (nth j l 0)) as [Haj| Haj]. {
    apply Nat.succ_inj.
    apply Nat.succ_lt_mono in Hin, Hjn.
    apply (NoDup_nat _ Hn); [ easy | easy | ].
    cbn; flia Hai Haj Hij.
  }
  apply Nat.nlt_ge in Haj.
  rewrite Nat.sub_0_r in Hij.
  apply Nat.succ_lt_mono in Hjn.
  specialize (NoDup_nat _ Hn 0 (S j) (Nat.lt_0_succ _) Hjn) as H1.
  cbn in H1.
  replace (nth j l 0) with a in H1 by flia Hai Haj Hij.
  now specialize (H1 eq_refl).
}
apply Nat.nlt_ge in Hai.
rewrite Nat.sub_0_r in Hij.
destruct (lt_dec a (nth j l 0)) as [Haj| Haj]. {
  apply Nat.succ_lt_mono in Hin.
  specialize (NoDup_nat _ Hn (S i) 0 Hin (Nat.lt_0_succ _)) as H1.
  cbn in H1.
  replace (nth i l 0) with a in H1 by flia Hai Haj Hij.
  now specialize (H1 eq_refl).
}
rewrite Nat.sub_0_r in Hij.
apply Nat.succ_inj.
apply Nat.succ_lt_mono in Hin, Hjn.
now apply (NoDup_nat _ Hn).
Qed.

Theorem length_sub_canon_permut_list : ∀ l,
  length (sub_canon_permut_list l) = length l - 1.
Proof.
intros.
destruct l as [| a]; [ easy | ].
now cbn; rewrite map_length, Nat.sub_0_r.
Qed.

Theorem canon_sym_gr_list_inv_ub : ∀ n l,
  is_permut n l
  → canon_sym_gr_list_inv n l < n!.
Proof.
intros * ((Hvn, Hn), Hln).
revert l Hvn Hn Hln.
induction n; intros; cbn; [ easy | ].
rewrite Nat.add_comm.
apply Nat.add_lt_le_mono. {
  apply IHn. {
    intros i Hi.
    apply (In_nth _ _ 0) in Hi.
    destruct Hi as (j & Hj & Hji).
    rewrite <- Hji.
    rewrite length_sub_canon_permut_list in Hj |-*.
    apply sub_canon_permut_list_elem_ub; [ easy | flia Hj ].
  } {
    apply nat_NoDup.
    intros i j Hi Hj.
    rewrite length_sub_canon_permut_list in Hi, Hj.
    apply sub_canon_sym_gr_elem_inj1; [ easy | flia Hi | flia Hj ].
  }
  now rewrite length_sub_canon_permut_list, Hln, Nat_sub_succ_1.
}
apply Nat.mul_le_mono_r.
specialize (Hvn (hd 0 l)).
assert (H : hd 0 l ∈ l) by now apply List_hd_in; rewrite Hln.
specialize (Hvn H); clear H.
rewrite Hln in Hvn.
now apply Nat.succ_le_mono in Hvn.
Qed.

Theorem sub_canon_permut_list_is_permut : ∀ l,
  is_permut_list l
  → is_permut_list (sub_canon_permut_list l).
Proof.
intros * Hl.
split. {
  intros i Hi.
  apply (In_nth _ _ 0) in Hi.
  destruct Hi as (j & Hj & Hji).
  rewrite <- Hji.
  rewrite length_sub_canon_permut_list in Hj |-*.
  apply sub_canon_permut_list_elem_ub; [ easy | flia Hj ].
} {
  apply nat_NoDup.
  intros i j Hi Hj Hij.
  rewrite length_sub_canon_permut_list in Hi, Hj.
  apply sub_canon_sym_gr_elem_inj1 in Hij; [ easy | easy | | ]. {
    flia Hi.
  } {
    flia Hj.
  }
}
Qed.

Theorem canon_sym_gr_list_canon_sym_gr_list_inv : ∀ n l,
  is_permut n l
  → canon_sym_gr_list n (canon_sym_gr_list_inv n l) = l.
Proof.
intros * ((Hvn, Hn), Hln).
revert l Hvn Hn Hln.
induction n; intros; [ now apply length_zero_iff_nil in Hln | cbn ].
destruct l as [| a]; [ easy | ].
f_equal. {
  cbn - [ sub_canon_permut_list ].
  rewrite Nat.div_add_l; [ | apply fact_neq_0 ].
  rewrite <- Nat.add_0_r; f_equal.
  apply Nat.div_small.
  apply canon_sym_gr_list_inv_ub.
  split. {
    now apply sub_canon_permut_list_is_permut.
  } {
    cbn; rewrite map_length.
    now cbn in Hln; apply Nat.succ_inj in Hln.
  }
} {
  cbn in Hln.
  apply Nat.succ_inj in Hln.
  rewrite Nat.div_add_l; [ | apply fact_neq_0 ].
  rewrite Nat_mod_add_l_mul_r; [ | apply fact_neq_0 ].
  rewrite Nat.mod_small. 2: {
    apply canon_sym_gr_list_inv_ub.
    split. {
      now apply sub_canon_permut_list_is_permut.
    } {
      rewrite length_sub_canon_permut_list; cbn.
      now rewrite Hln, Nat.sub_0_r.
    }
  }
  rewrite IHn; cycle 1. {
    intros i Hi.
    apply (In_nth _ _ 0) in Hi.
    destruct Hi as (j & Hj & Hji).
    rewrite <- Hji.
    apply permut_list_ub; [ | easy ].
    now apply sub_canon_permut_list_is_permut.
  } {
    apply nat_NoDup.
    intros i j Hi Hj.
    rewrite length_sub_canon_permut_list in Hi, Hj.
    cbn in Hi, Hj.
    rewrite Nat.sub_0_r in Hi, Hj.
    apply sub_canon_sym_gr_elem_inj1; [ easy | cbn; flia Hi | cbn; flia Hj ].
  } {
    rewrite length_sub_canon_permut_list; cbn.
    now rewrite Nat.sub_0_r.
  }
  cbn - [ sub_canon_permut_list ].
  unfold succ_when_ge.
  remember (canon_sym_gr_list_inv _ _) as x.
  cbn - [ "<=?" ]; subst x.
  rewrite map_map.
  rewrite List_map_map_seq with (d := 0).
  rewrite List_map_nth_seq with (d := 0).
  apply map_ext_in_iff.
  intros i Hi; apply in_seq in Hi.
  unfold Nat.b2n.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec a (nth i l 0)) as [Hai| Hai]. {
    rewrite if_leb_le_dec.
    destruct (le_dec _ _) as [H1| H1]; [ apply Nat.sub_add; flia Hai | ].
    exfalso.
    apply H1; clear H1.
    rewrite Nat.div_small; [ flia Hai | ].
    apply canon_sym_gr_list_inv_ub.
    split; [ | now cbn; rewrite map_length ].
    now apply sub_canon_permut_list_is_permut.
  }
  apply Nat.nlt_ge in Hai.
  rewrite Nat.sub_0_r.
  rewrite Nat.div_small. 2: {
    apply canon_sym_gr_list_inv_ub.
    split. {
      now apply sub_canon_permut_list_is_permut.
    } {
      rewrite length_sub_canon_permut_list; cbn; rewrite Hln.
      apply Nat.sub_0_r.
    }
  }
  rewrite Nat.add_0_r, if_leb_le_dec.
  destruct (le_dec _ _) as [H1| H1]; [ | apply Nat.add_0_r ].
  exfalso.
  apply Nat.le_antisymm in H1; [ symmetry in H1 | easy ].
  specialize (NoDup_nat _ Hn 0 (S i) (Nat.lt_0_succ _)) as H2.
  assert (H : S i < length (a :: l)) by (cbn; flia Hi).
  now specialize (H2 H H1); clear H.
}
Qed.

Theorem canon_sym_gr_list_is_permut_list : ∀ n k,
  k < n!
  → is_permut_list (canon_sym_gr_list n k).
Proof.
intros * Hkn.
split. {
  intros i Hi.
  rewrite canon_sym_gr_list_length.
  apply (In_nth _ _ 0) in Hi.
  destruct Hi as (j & Hj & Hji).
  rewrite canon_sym_gr_list_length in Hj.
  rewrite <- Hji.
  now apply canon_sym_gr_list_ub.
} {
  apply nat_NoDup.
  intros * Hi Hj Hij.
  rewrite canon_sym_gr_list_length in Hi, Hj.
  now apply nth_canon_sym_gr_list_inj1 in Hij.
}
Qed.

Theorem canon_sym_gr_list_is_permut : ∀ n k,
  k < n!
  → is_permut n (canon_sym_gr_list n k).
Proof.
intros * Hkn.
split; [ now apply canon_sym_gr_list_is_permut_list | ].
apply canon_sym_gr_list_length.
Qed.

Theorem canon_sym_gr_sub_canon_permut_list : ∀ n k,
  canon_sym_gr_list n (k mod n!) =
  sub_canon_permut_list (canon_sym_gr_list (S n) k).
Proof.
intros.
destruct n; intros; [ easy | ].
cbn - [ "<?" fact ].
f_equal. {
  unfold succ_when_ge.
  rewrite <- Nat.add_sub_assoc. 2: {
    unfold Nat.b2n.
    rewrite if_leb_le_dec, if_ltb_lt_dec.
    destruct (le_dec _ _) as [H| H]; [ destruct (lt_dec _ _); cbn; flia | ].
    rewrite Nat.add_0_r.
    apply Nat.nle_gt in H.
    destruct (lt_dec _ _) as [Hqr| Hqr]; [ flia H Hqr | easy ].
  }
  symmetry; rewrite <- Nat.add_0_r; f_equal.
  unfold Nat.b2n.
  rewrite if_leb_le_dec, if_ltb_lt_dec.
  destruct (le_dec _ _) as [H1| H1]; [ | easy ].
  destruct (lt_dec _ _) as [H2| H2]; [ easy | flia H1 H2 ].
}
rewrite map_map.
rewrite map_map.
apply map_ext_in.
intros i Hi.
remember (succ_when_ge (_ mod _ / _) _) as x eqn:Hx.
unfold succ_when_ge, Nat.b2n.
rewrite if_leb_le_dec, if_ltb_lt_dec.
rewrite <- Nat.add_sub_assoc. 2: {
  destruct (le_dec _ _) as [H| H]; [ destruct (lt_dec _ _); cbn; flia | ].
  rewrite Nat.add_0_r.
  apply Nat.nle_gt in H.
  destruct (lt_dec _ _) as [Hqr| Hqr]; [ flia H Hqr | easy ].
}
symmetry; rewrite <- Nat.add_0_r; f_equal.
destruct (le_dec _ _) as [H1| H1]; [ | easy ].
destruct (lt_dec _ _) as [H2| H2]; [ easy | flia H1 H2 ].
Qed.

Theorem canon_sym_gr_list_inv_canon_sym_gr_list : ∀ n k,
  k < n!
  → canon_sym_gr_list_inv n (canon_sym_gr_list n k) = k.
Proof.
intros * Hkn.
revert k Hkn.
induction n; intros; [ now apply Nat.lt_1_r in Hkn | ].
cbn - [ canon_sym_gr_list ].
remember (sub_canon_permut_list _) as x; cbn; subst x.
specialize (Nat.div_mod k (fact n) (fact_neq_0 _)) as H1.
rewrite Nat.mul_comm in H1.
replace (k / fact n * fact n) with (k - k mod fact n) by flia H1.
rewrite <- Nat.add_sub_swap; [ | apply Nat.mod_le, fact_neq_0 ].
apply Nat.add_sub_eq_r; f_equal.
clear H1.
rewrite <- (IHn (k mod fact n)) at 1; [ | easy ].
f_equal.
apply canon_sym_gr_sub_canon_permut_list.
Qed.

Theorem rank_in_sym_gr_of_rank_in_canon_sym_gr_prop : ∀ n sg,
  is_sym_gr_list n sg
  → ∀ k : fin_t n!,
      (sym_gr_inv sg
         (nth (proj1_sig k) (canon_sym_gr_list_list n) []) <? length sg) =
      true.
Proof.
intros * Hsg k.
apply Nat.ltb_lt.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  destruct k as (k, pk); cbn.
  apply Nat.ltb_lt, Nat.lt_1_r in pk; subst k.
  specialize (length_of_empty_sym_gr Hsg) as Hs.
  destruct sg as [| v]; [ easy | ].
  destruct sg; [ clear Hs | easy ].
  destruct Hsg as (Hsg & _ & _).
  specialize (Hsg 0 Nat.lt_0_1); cbn in Hsg.
  destruct Hsg as (H1, H2).
  apply length_zero_iff_nil in H1; subst v.
  apply Nat.lt_0_1.
}
now apply sym_gr_inv_lt with (n := n).
Qed.

Theorem rank_in_canon_sym_gr_of_rank_in_sym_gr_prop : ∀ n sg,
  is_sym_gr_list n sg
  → ∀ k : fin_t (length sg),
      (canon_sym_gr_list_inv n (nth (proj1_sig k) sg []) <? n!)
      = true.
Proof.
intros * Hsg k.
destruct Hsg as (Hsg & Hinj & Hsurj).
apply Nat.ltb_lt.
destruct k as (k, pk); cbn.
apply Nat.ltb_lt in pk.
specialize (Hsg k pk).
now apply canon_sym_gr_list_inv_ub.
Qed.

Definition rank_in_sym_gr_of_rank_in_canon_sym_gr n sg
    (Hsg : is_sym_gr_list n sg) (k : fin_t n!) : fin_t (length sg) :=
  exist (λ a : nat, (a <? length sg) = true)
    (sym_gr_inv sg
      (nth (proj1_sig k) (canon_sym_gr_list_list n) []))
    (rank_in_sym_gr_of_rank_in_canon_sym_gr_prop Hsg k).

Definition rank_in_canon_sym_gr_of_rank_in_sym_gr  n sg
    (Hsg : is_sym_gr_list n sg) (k : fin_t (length sg)) : fin_t n! :=
  exist (λ a : nat, (a <? n!) = true)
    (canon_sym_gr_list_inv n (nth (proj1_sig k) sg []))
    (rank_in_canon_sym_gr_of_rank_in_sym_gr_prop Hsg k).

Theorem rank_in_sym_gr_of_rank_in_canon_sym_gr_of_its_inverse : ∀ n sg
    (Hsg : is_sym_gr_list n sg) k,
  rank_in_sym_gr_of_rank_in_canon_sym_gr Hsg
    (rank_in_canon_sym_gr_of_rank_in_sym_gr Hsg k) = k.
Proof.
intros.
destruct k as (k, pk); cbn - [ "<?" ].
apply eq_exist_uncurried.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  specialize (length_of_empty_sym_gr Hsg) as Hs.
  specialize (proj1 (Nat.ltb_lt _ _) pk) as Hk.
  rewrite Hs in Hk.
  apply Nat.lt_1_r in Hk; subst k.
  assert (p : sym_gr_inv sg [] = 0). {
    unfold sym_gr_inv, unsome; cbn.
    destruct sg as [| v]; [ easy | ].
    destruct sg; [ cbn | easy ].
    destruct Hsg as (Hsg & _ & _).
    specialize (Hsg 0 Nat.lt_0_1); cbn in Hsg.
    destruct Hsg as (H1, H2).
    now apply length_zero_iff_nil in H1; subst v.
  }
  exists p.
  apply (Eqdep_dec.UIP_dec Bool.bool_dec).
}  
cbn.
assert
  (p :
   sym_gr_inv sg
     (nth (canon_sym_gr_list_inv n (nth k sg []))
        (canon_sym_gr_list_list n) []) = k). {
  apply Nat.ltb_lt in pk.
  destruct Hsg as (Hsg & Hinj & Hsurj).
  specialize (Hsg k pk) as H1.
  unfold canon_sym_gr_list_list.
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length.
    now apply canon_sym_gr_list_inv_ub.
  }
  rewrite seq_nth; [ | now apply canon_sym_gr_list_inv_ub ].
  rewrite Nat.add_0_l.
  rewrite canon_sym_gr_list_canon_sym_gr_list_inv; [ | easy ].
  now apply sym_gr_inv_list_el with (n := n).
}
exists p.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Theorem rank_in_canon_sym_gr_of_rank_in_sym_gr_of_its_inverse : ∀ n sg
    (Hsg : is_sym_gr_list n sg) k,
  rank_in_canon_sym_gr_of_rank_in_sym_gr Hsg
    (rank_in_sym_gr_of_rank_in_canon_sym_gr Hsg k) = k.
Proof.
intros.
destruct k as (k, pk); cbn - [ "<?" ].
apply eq_exist_uncurried; cbn.
assert
  (p :
   canon_sym_gr_list_inv n
     (nth (sym_gr_inv sg (nth k (canon_sym_gr_list_list n) []))
        sg []) = k). {
  specialize (proj1 (Nat.ltb_lt _ _) pk) as Hkn.
  unfold canon_sym_gr_list_list.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ cbn | easy ].
  rewrite (@nth_sym_gr_inv_sym_gr _ _ n); cycle 1. {
    easy.
  } {
    now apply canon_sym_gr_list_is_permut.
  }
  now apply canon_sym_gr_list_inv_canon_sym_gr_list.
}
exists p.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Theorem sym_gr_size : ∀ n sg, is_sym_gr_list n sg → length sg = n!.
Proof.
intros * Hsg.
apply (bijective_fin_t _ _ (rank_in_canon_sym_gr_of_rank_in_sym_gr Hsg)).
exists (rank_in_sym_gr_of_rank_in_canon_sym_gr Hsg).
split. {
  intros x.
  apply rank_in_sym_gr_of_rank_in_canon_sym_gr_of_its_inverse.
} {
  intros y.
  apply rank_in_canon_sym_gr_of_rank_in_sym_gr_of_its_inverse.
}
Qed.

(* *)

Record sym_gr_list n :=
  { sg_list : list (list nat);
    sg_prop : is_sym_gr_list n sg_list }.

Theorem canon_sym_gr_list_inj : ∀ n i j,
  i < fact n
  → j < fact n
  → canon_sym_gr_list n i = canon_sym_gr_list n j
  → i = j.
Proof.
intros * Hi Hj Hij.
apply (f_equal (@canon_sym_gr_list_inv n)) in Hij.
rewrite canon_sym_gr_list_inv_canon_sym_gr_list in Hij; [ | easy ].
rewrite canon_sym_gr_list_inv_canon_sym_gr_list in Hij; [ | easy ].
easy.
Qed.

Theorem rank_of_permut_in_canon_gr_list_inj : ∀ n la lb,
  is_permut n la
  → is_permut n lb
  → canon_sym_gr_list_inv n la =
    canon_sym_gr_list_inv n lb
  → la = lb.
Proof.
intros * (Hla, Han) (Hlb, Hbn) Hrr.
apply (f_equal (canon_sym_gr_list n)) in Hrr.
rewrite canon_sym_gr_list_canon_sym_gr_list_inv in Hrr; [ | easy ].
rewrite canon_sym_gr_list_canon_sym_gr_list_inv in Hrr; [ | easy ].
easy.
Qed.

Theorem isort_rank_inj : ∀ l,
  is_permut_list l
  → ∀ i j, i < length l → j < length l
  → nth i (isort_rank Nat.leb l) 0 = nth j (isort_rank Nat.leb l) 0
  → i = j.
Proof.
intros * Hp * Hi Hj Hij.
rewrite <- (isort_rank_length Nat.leb) in Hi, Hj.
now apply (NoDup_nat _ (NoDup_isort_rank _ _)) in Hij.
Qed.

Theorem isort_rank_is_permut : ∀ A (ord : A → _) n l,
  length l = n
  → is_permut n (isort_rank ord l).
Proof.
intros.
subst n.
split. {
  split. {
    intros i Hi.
    rewrite isort_rank_length.
    apply (In_nth _ _ 0) in Hi.
    rewrite isort_rank_length in Hi.
    destruct Hi as (ia & Hial & Hia).
    rewrite <- Hia.
    apply isort_rank_ub.
    now intros H; rewrite H in Hial.
  } {
    apply NoDup_isort_rank.
  }
}
apply isort_rank_length.
Qed.

Arguments isort_rank_is_permut {A} ord n%nat [l]%list.

Theorem isort_rank_is_permut_list : ∀ A (ord : A → _) l,
  is_permut_list (isort_rank ord l).
Proof.
intros.
now apply (isort_rank_is_permut _ (length l)).
Qed.

Theorem permut_list_Permutation : ∀ l n,
  is_permut n l
  → Permutation l (seq 0 n).
Proof.
intros * (Hp, Hln).
symmetry.
revert l Hp Hln.
induction n; intros. {
  now apply length_zero_iff_nil in Hln; subst l.
}
rewrite seq_S; cbn.
remember (ff_app (isort_rank Nat.leb l) n) as i eqn:Hi.
rewrite (List_map_ff_app_seq l).
remember (seq 0 n) as s eqn:Hs.
rewrite (List_seq_cut i); subst s. 2: {
  subst i.
  apply in_seq.
  split; [ easy | ].
  rewrite <- (isort_rank_length Nat.leb).
  apply permut_list_ub; [ | rewrite isort_rank_length, Hln; flia ].
  now apply isort_rank_is_permut_list.
}
rewrite Nat.sub_0_r; cbn.
rewrite map_app; cbn.
rewrite Hi at 2.
rewrite permut_permut_isort; [ | easy | now rewrite Hln ].
apply Permutation_elt.
rewrite app_nil_r.
rewrite <- map_app.
rewrite Hln; cbn.
assert (Hin : i ≤ n). {
  apply Nat.lt_succ_r.
  rewrite Hi, <- Hln.
  rewrite <- (isort_rank_length Nat.leb).
  apply permut_list_ub; [ apply isort_rank_is_permut_list | ].
  now rewrite isort_rank_length, Hln.
}
apply IHn. 2: {
  rewrite map_length, app_length, seq_length, seq_length.
  rewrite Nat.add_sub_assoc; [ now rewrite Nat.add_comm, Nat.add_sub | easy ].
}
assert (Hn : n = nth i l 0). {
  rewrite Hi; symmetry.
  apply permut_permut_isort; [ easy | now rewrite Hln ].
}
split. {
  intros j Hj.
  rewrite map_length, app_length, seq_length, seq_length.
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  apply in_map_iff in Hj.
  destruct Hj as (k & Hkj & Hk).
  apply in_app_iff in Hk.
  subst j.
  assert (Hkn : nth k l 0 < n). {
    specialize permut_list_ub as H1.
    specialize (H1 l k Hp).
    rewrite Hln in H1.
    assert (H : k < S n). {
      destruct Hk as [Hk| Hk]; apply in_seq in Hk; flia Hk Hin.
    }
    specialize (H1 H); clear H.
    enough (H : nth k l 0 ≠ n) by flia H H1.
    intros H; rewrite Hn in H.
    apply (NoDup_nat _ (proj2 Hp)) in H; [ | | flia Hin Hln ]. 2: {
      rewrite Hln.
      destruct Hk as [Hk| Hk]; apply in_seq in Hk; flia Hk Hin.
    }
    subst k.
    destruct Hk as [Hk| Hk]; apply in_seq in Hk; flia Hk.
  }
  destruct Hk as [Hk| Hk]; [ now apply in_seq in Hk | ].
  apply in_seq in Hk.
  now replace (S i + (n - i)) with (S n) in Hk by flia Hin.
} {
  apply nat_NoDup.
  rewrite map_length, map_app, app_length, seq_length, seq_length.
  unfold ff_app.
  replace (i + (n - i)) with n by flia Hin.
  intros j k Hj Hk Hjk.
  destruct (lt_dec j i) as [Hji| Hji]. {
    rewrite app_nth1 in Hjk; [ | now rewrite map_length, seq_length ].
    rewrite (List_map_nth' 0) in Hjk; [ | now rewrite seq_length ].
    rewrite seq_nth in Hjk; [ | easy ].
    destruct (lt_dec k i) as [Hki| Hki]. {
      rewrite app_nth1 in Hjk; [ | now rewrite map_length, seq_length ].
      rewrite (List_map_nth' 0) in Hjk; [ | now rewrite seq_length ].
      rewrite seq_nth in Hjk; [ | easy ].
      apply (NoDup_nat _ (proj2 Hp)) in Hjk; [ | flia Hln Hj | flia Hln Hk ].
      easy.
    }
    apply Nat.nlt_ge in Hki; exfalso.
    rewrite app_nth2 in Hjk; [ | now rewrite map_length, seq_length ].
    rewrite map_length, seq_length in Hjk.
    rewrite (List_map_nth' 0) in Hjk; [ | rewrite seq_length; flia Hk Hki ].
    rewrite seq_nth in Hjk; [ | flia Hk Hki ].
    replace (S i + (k - i)) with (S k) in Hjk by flia Hki.
    apply (NoDup_nat _ (proj2 Hp)) in Hjk; [ | flia Hln Hj | flia Hln Hk ].
    flia Hjk Hji Hki.
  }
  apply Nat.nlt_ge in Hji.
  rewrite app_nth2 in Hjk; [ | now rewrite map_length, seq_length ].
  rewrite map_length, seq_length in Hjk.
  rewrite (List_map_nth' 0) in Hjk; [ | rewrite seq_length; flia Hj Hji ].
  rewrite seq_nth in Hjk; [ | flia Hj Hji ].
  replace (S i + (j - i)) with (S j) in Hjk by flia Hji.
  destruct (lt_dec k i) as [Hki| Hki]. {
    rewrite app_nth1 in Hjk; [ | now rewrite map_length, seq_length ].
    rewrite (List_map_nth' 0) in Hjk; [ | now rewrite seq_length ].
    rewrite seq_nth in Hjk; [ | easy ].
    apply (NoDup_nat _ (proj2 Hp)) in Hjk; [ | flia Hln Hj | flia Hln Hk ].
    flia Hjk Hji Hki.
  }
  apply Nat.nlt_ge in Hki.
  rewrite app_nth2 in Hjk; [ | now rewrite map_length, seq_length ].
  rewrite map_length, seq_length in Hjk.
  rewrite (List_map_nth' 0) in Hjk; [ | rewrite seq_length; flia Hk Hki ].
  rewrite seq_nth in Hjk; [ | flia Hk Hki ].
  replace (S i + (k - i)) with (S k) in Hjk by flia Hki.
  apply (NoDup_nat _ (proj2 Hp)) in Hjk; [ | flia Hln Hj | flia Hln Hk ].
  flia Hjk Hji Hki.
}
Qed.

Arguments nth_canon_sym_gr_list_inj2 n%nat [i j]%nat.
