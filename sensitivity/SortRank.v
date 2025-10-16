(* isort_rank: like isort but return the rank of what have been
   sorted; its result, when applied to the initial list as an
   operator, returns the sorted list  *)

Set Nested Proofs Allowed.

From Stdlib Require Import Arith.
Import List.ListNotations.
Import Init.Nat.
From RingLike Require Import Utf8.

Require Import Misc SortingFun.

Fixpoint isort_rank_insert {A B} (rel : A → A → bool) (f : B → A) ia lrank :=
  match lrank with
  | [] => [ia]
  | ib :: l =>
      if rel (f ia) (f ib) then ia :: lrank
      else ib :: isort_rank_insert rel f ia l
  end.

Fixpoint isort_rank {A} (rel : A → A → bool) (l : list A) :=
  match l with
  | [] => []
  | d :: l' =>
      isort_rank_insert rel (λ i, List.nth i l d) 0
        (List.map S (isort_rank rel l'))
  end.

Theorem isort_rank_insert_length : ∀ {A B} (rel : A → _) (f : B → A) ia lrank,
  length (isort_rank_insert rel f ia lrank) = S (length lrank).
Proof.
intros.
induction lrank as [| ib]; [ easy | cbn ].
destruct (rel (f ia) (f ib)); [ easy | now cbn; f_equal ].
Qed.

Theorem isort_rank_length : ∀ {A} rel (l : list A),
  length (isort_rank rel l) = length l.
Proof.
intros.
induction l as [| d]; [ easy | ].
cbn - [ List.nth ].
now rewrite isort_rank_insert_length, List.length_map; f_equal.
Qed.

Theorem isort_rank_insert_nth_indep : ∀ A rel (d d' : A) ia lrank l_ini,
  ia < length l_ini
  → (∀ i, i ∈ lrank → i < length l_ini)
  → isort_rank_insert rel (λ i : nat, List.nth i l_ini d) ia lrank =
    isort_rank_insert rel (λ i : nat, List.nth i l_ini d') ia lrank.
Proof.
intros * Hia Hini.
induction lrank as [| ib]; [ easy | ].
cbn - [ List.nth ].
specialize (Hini ib (or_introl eq_refl)) as Hib.
rewrite (List.nth_indep _ _ d' Hia).
rewrite (List.nth_indep _ _ d' Hib).
remember (rel (List.nth ia l_ini d') (List.nth ib l_ini d')) as x eqn:Hx.
symmetry in Hx.
destruct x; [ easy | ].
f_equal.
apply IHlrank.
intros i Hi.
apply Hini.
now right.
Qed.

Theorem in_isort_rank_insert : ∀ A B (rel : A → _) (f : B → A) ia ib lrank,
  ia ∈ isort_rank_insert rel f ib lrank → ia ∈ ib :: lrank.
Proof.
intros * Hia.
induction lrank as [| ic]; [ easy | ].
cbn in Hia.
destruct (rel (f ib) (f ic)); [ easy | ].
destruct Hia as [Hia| Hia]; [ now right; left | ].
specialize (IHlrank Hia).
destruct IHlrank as [H1| H1]; [ now left | now right; right ].
Qed.

Theorem in_isort_rank : ∀ A (rel : A → _) l i,
  i ∈ isort_rank rel l → i < length l.
Proof.
intros * Hi.
revert i Hi.
induction l as [| a]; intros; [ easy | cbn ].
cbn - [ List.nth ] in Hi.
apply in_isort_rank_insert in Hi.
destruct Hi as [Hi| Hi]; [ now subst i | ].
apply List.in_map_iff in Hi.
destruct Hi as (j & Hj & Hi); subst i.
apply -> Nat.succ_lt_mono.
now apply IHl.
Qed.

Theorem isort_rank_insert_ub : ∀ A (rel : A → _) ia lrank f i n,
  ia < n
  → (∀ i, i ∈ lrank → i < n)
  → List.nth i (isort_rank_insert rel f ia lrank) 0 < n.
Proof.
intros * Hia Hn.
revert i.
induction lrank as [| ib]; intros. {
  destruct i; [ easy | cbn ].
  rewrite Tauto_match_nat_same; flia Hia.
}
cbn - [ List.nth ].
remember (rel (f ia) (f ib)) as x eqn:Hx.
symmetry in Hx.
destruct x. {
  destruct i; [ easy | ].
  destruct i; cbn; [ now apply Hn; left | ].
  destruct (lt_dec i (length lrank)) as [Hii| Hii]. 2: {
    apply Nat.nlt_ge in Hii.
    rewrite List.nth_overflow; [ flia Hia | easy ].
  }
  apply Hn; right.
  now apply List.nth_In.
} {
  destruct i; cbn; [ now apply Hn; left | ].
  apply IHlrank.
  intros j Hj.
  now apply Hn; right.
}
Qed.

Theorem isort_rank_ub : ∀ A rel (l : list A) i,
  l ≠ [] → List.nth i (isort_rank rel l) 0 < length l.
Proof.
intros * Hlz.
destruct l as [| ia]; [ easy | clear Hlz ].
cbn - [ List.nth ].
apply isort_rank_insert_ub; [ easy | ].
intros j Hj.
apply List.in_map_iff in Hj.
destruct Hj as (k & Hk & Hj); subst j.
apply -> Nat.succ_lt_mono.
now apply in_isort_rank in Hj.
Qed.

Theorem NoDup_isort_rank_insert : ∀ A (d : A) rel l_ini ia lrank,
  List.NoDup (ia :: lrank)
  → List.NoDup
      (isort_rank_insert rel (λ k : nat, List.nth k l_ini d) ia lrank).
Proof.
intros * Hnd.
revert ia Hnd.
induction lrank as [| ib]; intros. {
  cbn; constructor; [ easy | constructor ].
}
cbn.
destruct (rel (List.nth ia l_ini d) (List.nth ib l_ini d)); [ easy | ].
apply List.NoDup_cons_iff in Hnd.
destruct Hnd as (Hia, Hnd).
apply List.NoDup_cons_iff in Hnd.
destruct Hnd as (Hib, Hnd).
apply List.NoDup_cons. 2: {
  apply IHlrank.
  apply List.NoDup_cons_iff.
  split; [ | easy ].
  now intros H; apply Hia; right.
}
intros Hib'.
apply in_isort_rank_insert in Hib'.
destruct Hib' as [Hib'| Hib']; [ | easy ].
subst ib; apply Hia.
now left.
Qed.

Theorem NoDup_isort_rank :
  ∀ {A} rel (l : list A), List.NoDup (isort_rank rel l).
Proof.
intros.
induction l as [| d]; [ constructor | ].
cbn - [ List.nth ].
apply NoDup_isort_rank_insert.
constructor. {
  intros H; apply List.in_map_iff in H.
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
apply (f_equal (λ l, length l)) in Hl.
rewrite isort_rank_length in Hl.
now apply List.length_zero_iff_nil in Hl.
Qed.

Theorem isort_insert_isort_rank_insert : ∀ A B rel ia (f : B → A) lrank,
  isort_insert rel (f ia) (List.map f lrank) =
  List.map f (isort_rank_insert rel f ia lrank).
Proof.
intros.
induction lrank as [| ib]; [ easy | cbn ].
destruct (rel (f ia) (f ib)); [ easy | ].
now cbn; f_equal.
Qed.

(* *)

Theorem isort_isort_rank : ∀ {A} (rel : A → A → bool) (d : A) l,
  isort rel l = List.map (λ i, List.nth i l d) (isort_rank rel l).
Proof.
intros.
induction l as [| d' l]; [ easy | ].
cbn - [ List.nth ].
rewrite IHl.
rewrite isort_rank_insert_nth_indep with (d' := d); [ | now cbn | ]. 2: {
  intros i Hi.
  apply List.in_map_iff in Hi.
  destruct Hi as (j & Hj & Hi); subst i.
  cbn; apply -> Nat.succ_lt_mono.
  now apply in_isort_rank in Hi.
}
rewrite <- isort_insert_isort_rank_insert.
rewrite List_nth_0_cons.
now rewrite List.map_map.
Qed.

Theorem sorted_isort_rank_insert : ∀ A B (rela : A → _) (relb : B → _),
  transitive relb →
  total_relation relb →
  ∀ f ia lrank,
  (∀ ib ic, ib ∈ ia :: lrank → ic ∈ ia :: lrank →
   rela (f ib) (f ic) = relb ib ic)
  → sorted relb lrank
  → sorted relb (isort_rank_insert rela f ia lrank).
Proof.
intros * Htrab Htotb * Hfab * Hs.
revert ia Hfab.
induction lrank as [| ib]; intros; [ easy | cbn ].
remember (rela (f ia) (f ib)) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  apply sorted_cons_iff; [ easy | ].
  split; [ easy | ].
  intros ic Hic.
  generalize Hab; intros Hiab.
  rewrite Hfab in Hiab; [ | now left | now right; left ].
  destruct Hic as [Hic| Hic]; [ now subst ic | ].
  apply sorted_cons_iff in Hs; [ | easy ].
  destruct Hs as (Hs, Hib).
  specialize (Hib _ Hic) as Hibc.
  now apply (Htrab _ ib).
}
apply sorted_cons_iff; [ easy | ].
apply sorted_cons_iff in Hs; [ | easy ].
destruct Hs as (Hs, Hib).
split. {
  apply IHlrank; [ easy | ].
  intros ic id Hic Hid.
  apply Hfab. {
    destruct Hic as [Hic| Hic]; [ now subst ic; left | now right; right ].
  } {
    destruct Hid as [Hid| Hid]; [ now subst id; left | now right; right ].
  }
}
intros ic Hic.
apply in_isort_rank_insert in Hic.
destruct Hic as [Hic| Hic]. {
  subst ic.
  rewrite Hfab in Hab; [ | now left | now right; left ].
  specialize (Htotb ia ib).
  now rewrite Hab in Htotb.
}
now apply Hib.
Qed.

Theorem eq_sorted_isort_rank_insert_seq : ∀ A (rel : A → _) (ia : A) lrank f,
  (∀ ib, ib ∈ lrank → rel (f ia) (f ib) = true)
  → isort_rank_insert rel f ia lrank = ia :: lrank.
Proof.
intros * Ha.
destruct lrank as [| ib]; [ easy | cbn ].
remember (rel (f ia) (f ib)) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ easy | ].
rewrite Ha in Hab; [ easy | now left ].
Qed.

Theorem eq_sorted_isort_rank_seq : ∀ {rel : nat → _},
  transitive rel →
  ∀ la, sorted rel la
  → isort_rank rel la = List.seq 0 (List.length la).
Proof.
intros * Htra * Hs.
induction la as [| a]; intros; [ easy | ].
cbn - [ List.nth List.seq ].
rewrite IHla; [ | now apply sorted_cons in Hs ].
rewrite List.seq_shift.
cbn - [ List.nth ].
apply eq_sorted_isort_rank_insert_seq.
intros * Hb.
apply List.in_seq in Hb.
rewrite List_nth_0_cons.
apply sorted_cons_iff in Hs; [ | easy ].
destruct Hs as (Hs, Ha).
apply Ha.
destruct ib; [ easy | cbn ].
apply List.nth_In; flia Hb.
Qed.

Theorem isort_rank_insert_eq_compat : ∀ A (f g : A → _) ia lrank,
  (∀ x y, x ∈ ia :: lrank → y ∈ ia :: lrank → (f x <=? f y) = (g x <=? g y))
  → isort_rank_insert Nat.leb f ia lrank =
    isort_rank_insert Nat.leb g ia lrank.
Proof.
intros * Hfg.
induction lrank as [| ib]; [ easy | cbn ].
rewrite Hfg; [ | now left | now right; left ].
rewrite IHlrank; [ easy | ].
intros i j Hi Hj.
apply Hfg. {
  destruct Hi; [ now left | now right; right ].
} {
  destruct Hj; [ now left | now right; right ].
}
Qed.

Theorem isort_rank_map_add_compat : ∀ i j la,
  isort_rank Nat.leb (List.map (add i) la) =
  isort_rank Nat.leb (List.map (add j) la).
Proof.
intros.
induction la as [| a]; [ easy | ].
cbn - [ List.nth ].
rewrite IHla.
apply isort_rank_insert_eq_compat.
intros ia ib Hia Hib.
destruct Hia as [Hia| Hia]. {
  subst ia; do 2 rewrite List_nth_0_cons.
  destruct Hib as [Hib| Hib]. {
    subst ib; do 2 rewrite List_nth_0_cons.
    now do 2 rewrite Nat.leb_refl.
  }
  apply List.in_map_iff in Hib.
  destruct Hib as (ic & H & Hib); subst ib.
  do 2 rewrite List_nth_succ_cons.
  apply in_isort_rank in Hib.
  rewrite List.length_map in Hib.
  rewrite (List_map_nth' 0); [ | easy ].
  rewrite (List_map_nth' 0); [ | easy ].
  now do 2 rewrite Nat_leb_add_mono_l.
}
apply List.in_map_iff in Hia.
destruct Hia as (ic & H & Hic); subst ia.
do 2 rewrite List_nth_succ_cons.
apply in_isort_rank in Hic.
rewrite List.length_map in Hic.
rewrite (List_map_nth' 0); [ | easy ].
rewrite (List_map_nth' 0); [ | easy ].
destruct Hib as [Hib| Hib]. {
  subst ib; do 2 rewrite List_nth_0_cons.
  now do 2 rewrite Nat_leb_add_mono_l.
}
apply List.in_map_iff in Hib.
destruct Hib as (id & H & Hid); subst ib.
do 2 rewrite List_nth_succ_cons.
apply in_isort_rank in Hid.
rewrite List.length_map in Hid.
rewrite (List_map_nth' 0); [ | easy ].
rewrite (List_map_nth' 0); [ | easy ].
now do 2 rewrite Nat_leb_add_mono_l.
Qed.

Theorem nth_nth_isort_rank : ∀ A d rel (l : list A) i,
  i < List.length l
  → List.nth (List.nth i (isort_rank rel l) 0) l d =
    List.nth i (isort rel l) d.
Proof.
intros * Hil.
rewrite (isort_isort_rank _ d).
rewrite (List_map_nth' 0); [ easy | ].
now rewrite isort_rank_length.
Qed.

Theorem neq_isort_rank_insert_nil : ∀ A B rel (f : B → A) ia lrank,
  isort_rank_insert rel f ia lrank ≠ [].
Proof.
intros * Hla.
destruct lrank as [| ib]; [ easy | cbn in Hla ].
now destruct (rel (f ia) (f ib)).
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

Theorem collapse_length : ∀ l, List.length (collapse l) = List.length l.
Proof.
intros.
unfold collapse.
now do 2 rewrite isort_rank_length.
Qed.

Theorem eq_sorted_collapse_seq : ∀ la,
  sorted Nat.leb la → collapse la = List.seq 0 (List.length la).
Proof.
intros * Hs.
unfold collapse.
rewrite eq_sorted_isort_rank_seq; [ | apply Nat_leb_trans | ]. 2: {
  rewrite eq_sorted_isort_rank_seq; [ | apply Nat_leb_trans | easy ].
  apply sorted_nat_ltb_leb_incl.
  apply sorted_seq.
}
now rewrite isort_rank_length.
Qed.
