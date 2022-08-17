(* isort_rank: like isort but return the rank of what have been
   sorted; its result, when applied to the initial list as an
   operator, returns the sorted list  *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.
Import Init.Nat.

Require Import Misc SortingFun.
(*
Require Import PermutationFun.
*)

Fixpoint isort_rank {A} (rel : A → A → bool) (l : list A) :=
  match l with
  | [] => []
  | d :: l' =>
      isort_insert (λ ia ib, rel (nth ia l d) (nth ib l d)) 0
        (map S (isort_rank rel l'))
  end.

Theorem isort_rank_length : ∀ A rel (l : list A),
  length (isort_rank rel l) = length l.
Proof.
intros.
induction l as [| d]; [ easy | ].
cbn - [ nth ].
rewrite isort_insert_length.
now rewrite map_length; f_equal.
Qed.

Theorem in_isort_rank : ∀ A (rel : A → _) l i,
  i ∈ isort_rank rel l → i < length l.
Proof.
intros * Hi.
revert i Hi.
induction l as [| a]; intros; [ easy | cbn ].
cbn - [ nth ] in Hi.
apply in_isort_insert in Hi.
destruct Hi as [Hi| Hi]; [ now subst i | ].
apply in_map_iff in Hi.
destruct Hi as (j & Hj & Hi); subst i.
apply -> Nat.succ_lt_mono.
now apply IHl.
Qed.

Theorem isort_rank_ub : ∀ A rel (l : list A) i,
  l ≠ [] → nth i (isort_rank rel l) 0 < length l.
Proof.
intros * Hlz.
destruct l as [| ia]; [ easy | clear Hlz ].
cbn - [ nth ].
apply isort_insert_nat_ub; [ easy | ].
intros j Hj.
apply in_map_iff in Hj.
destruct Hj as (k & Hk & Hj); subst j.
apply -> Nat.succ_lt_mono.
now apply in_isort_rank in Hj.
Qed.

Theorem NoDup_isort_rank : ∀ A rel (l : list A), NoDup (isort_rank rel l).
Proof.
intros.
induction l as [| d]; [ constructor | ].
cbn - [ nth ].
apply NoDup_isort_insert.
constructor. {
  intros H; apply in_map_iff in H.
  now destruct H as (i & Hi & H).
}
apply FinFun.Injective_map_NoDup; [ | easy ].
intros i j Hij.
now apply Nat.succ_inj in Hij.
Qed.

Theorem eq_isort_rank_nil : ∀ A (rel : A → _) l,
  isort_rank rel l = [] → l = [].
Proof.
intros * Hl.
apply (f_equal length) in Hl.
rewrite isort_rank_length in Hl.
now apply length_zero_iff_nil in Hl.
Qed.

(* *)

Theorem isort_isort_rank : ∀ A (rel : A → A → bool) (d : A) l,
  isort rel l = map (λ i, nth i l d) (isort_rank rel l).
Proof.
intros.
induction l as [| d' l]; [ easy | ].
cbn - [ nth ].
rewrite IHl.
rewrite isort_insert_nth_indep with (d' := d); [ | now cbn | ]. 2: {
  intros i Hi.
  apply in_map_iff in Hi.
  destruct Hi as (j & Hj & Hi); subst i.
  cbn; apply -> Nat.succ_lt_mono.
  now apply in_isort_rank in Hi.
}
now rewrite (isort_insert_map_nth rel l d).
Qed.

Theorem sorted_isort_rank : ∀ A d (rel : A → _),
  total_relation rel
  → ∀ la, sorted (λ i j, nth i la d <=? nth j la d) (isort_rank Nat.leb la).
Proof.
intros * Hto *.
induction la as [| a]; [ easy | ].
cbn - [ nth ].
rewrite isort_insert_nth_indep with (d' := d); [ | now cbn | ]. 2: {
  intros i Hi.
  apply in_map_iff in Hi.
  destruct Hi as (j & Hj & Hi); subst i.
  cbn; apply -> Nat.succ_lt_mono.
  now apply in_isort_rank in Hi.
}
apply sorted_isort_insert. {
  intros i j.
  apply Bool.orb_true_iff.
  remember (_ <=? _) as x eqn:Hx; symmetry in Hx.
  destruct x; [ now left | right ].
  apply Nat.leb_le.
  apply Nat.leb_nle, Nat.nle_gt in Hx.
  now apply Nat.lt_le_incl.
}
apply sorted_map; [ | apply IHla ].
intros x y z Hx Hy.
apply Nat.leb_le in Hx, Hy.
apply Nat.leb_le.
etransitivity; [ apply Hx | apply Hy ].
Qed.

Theorem eq_sorted_isort_rank_seq : ∀ la,
  sorted Nat.leb la
  → isort_rank Nat.leb la = seq 0 (length la).
Proof.
intros * Hs.
apply List_eq_iff.
rewrite isort_rank_length, seq_length.
split; [ easy | ].
intros d i.
destruct (lt_dec i (length la)) as [Hil| Hil]. 2: {
  apply Nat.nlt_ge in Hil.
  rewrite nth_overflow; [ | now rewrite isort_rank_length ].
  rewrite nth_overflow; [ easy | now rewrite seq_length ].
}
rewrite seq_nth; [ | easy ].
rewrite nth_indep with (d' := 0); [ | now rewrite isort_rank_length ].
clear d; cbn.
revert i Hil.
induction la as [| a]; intros; [ easy | ].
cbn - [ nth ].
rewrite sorted_cons_isort_insert; cycle 1. {
  intros x y z Hxy Hyz.
  apply Nat.leb_le in Hxy, Hyz.
  apply Nat.leb_le.
  etransitivity; [ apply Hxy | easy ].
} {
  apply sorted_cons_iff. {
    intros x y z Hxy Hyz.
    apply Nat.leb_le in Hxy, Hyz.
    apply Nat.leb_le.
    etransitivity; [ apply Hxy | easy ].
  }
  split. {
    apply sorted_map. {
      intros x y z Hxy Hyz.
      apply Nat.leb_le in Hxy, Hyz.
      apply Nat.leb_le.
      now transitivity (nth y (a :: la) a).
    }
    cbn.
    apply (sorted_isort_rank a Nat_leb_total_relation).
  }
  intros j Hj.
  apply in_map_iff in Hj.
  destruct Hj as (k & Hk & Hj); subst j.
  cbn.
  apply in_isort_rank in Hj.
  apply sorted_cons_iff in Hs; [ | apply Nat_leb_trans ].
  destruct Hs as (Hs & Ha).
  apply Ha.
  now apply nth_In.
}
destruct i; [ easy | cbn ].
cbn in Hil; apply Nat.succ_lt_mono in Hil.
rewrite (List_map_nth' 0); [ | now rewrite isort_rank_length ].
f_equal.
apply sorted_cons_iff in Hs; [ now apply IHla | apply Nat_leb_trans ].
Qed.

Theorem isort_rank_map_add_compat : ∀ i j la,
  isort_rank Nat.leb (map (add i) la) = isort_rank Nat.leb (map (add j) la).
Proof.
intros.
induction la as [| a]; [ easy | ].
cbn - [ nth ].
rewrite IHla.
erewrite isort_insert_rel_eq_compat. 2: {
  intros x y Hx Hy.
  rewrite <- map_cons.
  rewrite (List_map_nth' 0). 2: {
    destruct Hx as [Hx| Hx]; [ now subst x; cbn | ].
    apply in_map_iff in Hx.
    destruct Hx as (z & Hz & Hx); subst x.
    cbn; apply -> Nat.succ_lt_mono.
    apply in_isort_rank in Hx.
    now rewrite map_length in Hx.
  }
  rewrite (List_map_nth' 0). 2: {
    destruct Hy as [Hy| Hy]; [ now subst y; cbn | ].
    apply in_map_iff in Hy.
    destruct Hy as (z & Hz & Hy); subst y.
    cbn; apply -> Nat.succ_lt_mono.
    apply in_isort_rank in Hy.
    now rewrite map_length in Hy.
  }
  now rewrite Nat_leb_add_mono_l.
}
symmetry.
erewrite isort_insert_rel_eq_compat. 2: {
  intros x y Hx Hy.
  rewrite <- map_cons.
  rewrite (List_map_nth' 0). 2: {
    destruct Hx as [Hx| Hx]; [ now subst x; cbn | ].
    apply in_map_iff in Hx.
    destruct Hx as (z & Hz & Hx); subst x.
    cbn; apply -> Nat.succ_lt_mono.
    apply in_isort_rank in Hx.
    now rewrite map_length in Hx.
  }
  rewrite (List_map_nth' 0). 2: {
    destruct Hy as [Hy| Hy]; [ now subst y; cbn | ].
    apply in_map_iff in Hy.
    destruct Hy as (z & Hz & Hy); subst y.
    cbn; apply -> Nat.succ_lt_mono.
    apply in_isort_rank in Hy.
    now rewrite map_length in Hy.
  }
  now rewrite Nat_leb_add_mono_l.
}
symmetry.
easy.
Qed.

Theorem nth_nth_isort_rank : ∀ A d ord (l : list A) i,
  i < length l
  → nth (nth i (isort_rank ord l) 0) l d = nth i (isort ord l) d.
Proof.
intros * Hil.
rewrite (isort_isort_rank _ d).
rewrite (List_map_nth' 0); [ easy | ].
now rewrite isort_rank_length.
Qed.

(* collapse: transforms a list of n different naturals into a permutation of
   {0..n-1} such that they are in the same order than the initial list;
   E.g. collapse [3;1;7;2] = [2;0;3;1]; it is the list of the ranks.
   I claim that list has the same ε than the initial list i.e.
      ε (collapse l) = ε l
   I also claim that
      collapse (collapse l) = collapse l
      collapse (la ° lb) = collapse la ° collapse lb
      collapse la = la, if la is a permutation
   And
      collapse is a permutation
      it is the invert permutation of isort_rank
      i.e. isort_rank of isort_rank
      isort_rank ord l = rank of the elements in the sorted list
      e.g.
        isort_rank Nat.leb [19;3;7;6] = [1;3;2;0] means thatn
        - the first element of [1;3;2;0], 1, is the rank of the lowest
          value in [19;3;7;6] which is 3,
        - the second element of [1;3;2;0], 3, is the rank of the next
          lowest value in [19;3;7;6] which is 6,
        - and so on
*)

Definition collapse l := isort_rank Nat.leb (isort_rank Nat.leb l).

Theorem fold_collapse : ∀ l,
  isort_rank Nat.leb (isort_rank Nat.leb l) = collapse l.
Proof. easy. Qed.

Theorem collapse_length : ∀ l, length (collapse l) = length l.
Proof.
intros.
unfold collapse.
now do 2 rewrite isort_rank_length.
Qed.
