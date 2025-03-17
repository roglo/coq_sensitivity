Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Import List.ListNotations.

Require Import Misc PermutationFun.
Require Import SortingFun_common.

Theorem strongly_sorted_sorted : ∀ A (rel : A → A → bool),
  ∀ l, strongly_sorted rel l → sorted rel l.
Proof.
intros * Hs.
unfold strongly_sorted in Hs; unfold sorted.
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

Theorem sorted_rel : ∀ A (d : A) rel l,
  sorted rel l
  → ∀ i, S i < length l
  → rel (List.nth i l d) (List.nth (S i) l d) = true.
Proof.
intros * Hs i Hi.
revert i Hi.
induction l as [| a]; intros; [ easy | ].
cbn in Hi.
apply Nat.succ_lt_mono in Hi.
destruct l as [| b]; [ easy | ].
remember (b :: l) as l'; cbn in Hs |-*; subst l'.
apply Bool.andb_true_iff in Hs.
destruct i; [ easy | ].
now apply IHl.
Qed.

Theorem strongly_sorted_if : ∀ A rel,
  transitive rel
  → ∀ l,
  strongly_sorted rel l
  → ∀ (d : A) i j,
    i < length l
    → j < length l
    → i < j
    → rel (List.nth i l d) (List.nth j l d) = true.
Proof.
intros * Htr * Hso * Hi Hj Hij.
remember (j - i) as n eqn:Hn.
replace j with (i + n) in * by flia Hn Hij.
assert (Hnz : n ≠ 0) by flia Hij.
clear Hi Hij Hn.
revert i Hj.
induction n; intros; [ easy | clear Hnz; cbn ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  rewrite Nat.add_1_r in Hj |-*.
  apply sorted_rel; [ | easy ].
  now apply strongly_sorted_sorted.
}
apply Htr with (b := List.nth (S i) l d). 2: {
  rewrite <- Nat.add_succ_comm in Hj.
  rewrite <- Nat.add_succ_comm.
  now apply IHn.
}
apply sorted_rel; [ | flia Hj ].
now apply strongly_sorted_sorted.
Qed.

Theorem sorted_NoDup : ∀ {A} {rel : A → _},
  irreflexive rel →
  transitive rel →
  ∀ l, sorted rel l → List.NoDup l.
Proof.
intros * Hirr Htra * Hsort.
induction l as [| a]; [ constructor | ].
constructor. 2: {
  apply IHl.
  now apply sorted_cons in Hsort.
}
intros Ha.
specialize (sorted_extends Htra Hsort _ Ha) as H1.
now rewrite Hirr in H1.
Qed.

Theorem sorted_nat_ltb_leb_incl : ∀ l,
  sorted Nat.ltb l → sorted Nat.leb l.
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

(* unicity of sorting algorithm *)

Theorem sorted_unique : ∀ {A} {eqb rel : A → _},
  equality eqb →
  reflexive rel →
  antisymmetric rel →
  transitive rel →
  ∀ (sort_algo1 sort_algo2 : list A → _),
  (∀ l, permutation eqb (sort_algo1 l) l ∧ sorted rel (sort_algo1 l))
  → (∀ l, permutation eqb (sort_algo2 l) l ∧ sorted rel (sort_algo2 l))
  → ∀ l, sort_algo1 l = sort_algo2 l.
Proof.
intros * Heqb Href Hant Htra * Hps1 Hps2 l.
specialize (sorted_sorted_permuted Heqb Hant Htra) as H1.
apply H1; [ apply Hps1 | apply Hps2 | clear H1 ].
specialize (Hps1 l) as H1.
specialize (Hps2 l) as H2.
eapply (permutation_trans Heqb); [ apply H1 | ].
now apply (permutation_sym Heqb).
Qed.

Theorem Nat_leb_total_relation : total_relation Nat.leb.
Proof.
intros i j.
apply Bool.orb_true_iff.
destruct (le_dec i j) as [Hij| Hij]. {
  now apply Nat.leb_le in Hij; rewrite Hij; left.
} {
  apply Nat.nle_gt, Nat.lt_le_incl in Hij.
  now apply Nat.leb_le in Hij; rewrite Hij; right.
}
Qed.

Theorem Nat_leb_antisym : antisymmetric Nat.leb.
Proof.
intros a b Hab Hba.
apply Nat.leb_le in Hab, Hba.
now apply Nat.le_antisymm.
Qed.

Theorem Nat_leb_trans : transitive Nat.leb.
Proof.
intros a b c Hab Hbc.
apply Nat.leb_le in Hab, Hbc.
apply Nat.leb_le.
now transitivity b.
Qed.

Theorem Nat_ltb_antisym : antisymmetric Nat.ltb.
Proof.
intros a b Hab Hba.
apply Nat.ltb_lt in Hab, Hba.
apply (Nat.lt_trans b) in Hab; [ | easy ].
now apply Nat.lt_irrefl in Hab.
Qed.

Theorem Nat_ltb_trans : transitive Nat.ltb.
Proof.
intros a b c Hab Hbc.
apply Nat.ltb_lt in Hab, Hbc.
apply Nat.ltb_lt.
now transitivity b.
Qed.

Theorem Nat_ltb_connected : connected_relation Nat.ltb.
Proof.
intros a b Hab Hba.
apply Nat.ltb_ge in Hab, Hba.
now apply Nat.le_antisymm.
Qed.

Theorem sorted_seq : ∀ sta len, sorted Nat.ltb (List.seq sta len).
Proof.
intros.
revert sta.
induction len; intros; [ easy | cbn ].
apply sorted_cons_iff; [ apply Nat_ltb_trans | ].
split; [ apply IHlen | ].
intros a Ha.
apply List.in_seq in Ha.
now apply Nat.ltb_lt.
Qed.

Theorem antisymmetric_list_leb : ∀ A (leb : A → _),
  antisymmetric leb → antisymmetric (list_leb leb).
Proof.
intros * Hant.
intros la lb Hlab Hlba.
revert lb Hlab Hlba.
induction la as [| a]; intros; [ now destruct lb | ].
destruct lb as [| b]; [ easy | ].
cbn in Hlab, Hlba.
remember (leb a b) as ab eqn:Hab; symmetry in Hab.
remember (leb b a) as ba eqn:Hba; symmetry in Hba.
destruct ab; [ | easy ].
destruct ba; [ | easy ].
rewrite (Hant _ _ Hab Hba); f_equal.
now apply IHla.
Qed.

Theorem transitive_list_leb : ∀ A (leb : A → _),
  transitive leb → transitive (list_leb leb).
Proof.
intros * Htra.
intros la lb lc Hlab Hlbc.
revert lb lc Hlab Hlbc.
induction la as [| a]; intros; [ now destruct lb | ].
destruct lb as [| b]; [ easy | ].
destruct lc as [| c]; [ easy | ].
cbn in Hlab, Hlbc |-*.
remember (leb a b) as ab eqn:Hab; symmetry in Hab.
remember (leb b a) as ba eqn:Hba; symmetry in Hba.
remember (leb b c) as bc eqn:Hbc; symmetry in Hbc.
remember (leb c b) as cb eqn:Hcb; symmetry in Hcb.
destruct ab; [ | easy ].
destruct bc; [ | easy ].
rewrite (Htra _ _ _ Hab Hbc).
destruct ba. {
  destruct cb. {
    rewrite (Htra _ _ _ Hcb Hba).
    now apply (IHla lb).
  }
  remember (leb c a) as ca eqn:Hca; symmetry in Hca.
  destruct ca; [ | easy ].
  now rewrite (Htra c a b Hca Hab) in Hcb.
} {
  remember (leb c a) as ca eqn:Hca; symmetry in Hca.
  destruct ca; [ | easy ].
  destruct cb; [ now rewrite (Htra b c a Hbc Hca) in Hba | ].
  now rewrite (Htra _ _ _ Hca Hab) in Hcb.
}
Qed.

Theorem total_relation_list_leb : ∀ A (leb : A → _),
  total_relation leb → total_relation (list_leb leb).
Proof.
intros * Htot.
intros la lb.
revert lb.
induction la as [| a]; intros; [ easy | ].
destruct lb as [| b]; [ easy | cbn ].
specialize (Htot a b).
remember (leb a b) as ab eqn:Hab; symmetry in Hab.
remember (leb b a) as ba eqn:Hba; symmetry in Hba.
destruct ab; [ | now destruct ba ].
destruct ba; [ | easy ].
apply IHla.
Qed.

Theorem transitive_list_ltb : ∀ A (ltb : A → _),
  antisymmetric ltb
  → connected_relation ltb
  → transitive ltb
  → transitive (list_ltb ltb).
Proof.
intros * Hant Hcon Htra.
intros la lb lc Hlab Hlbc.
revert la lb Hlab Hlbc.
induction lc as [| c]; intros; [ now destruct lb | ].
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | ].
cbn in Hlab, Hlbc |-*.
remember (ltb a c) as ac eqn:Hac; symmetry in Hac.
remember (ltb c a) as ca eqn:Hca; symmetry in Hca.
destruct ac; [ easy | ].
remember (ltb a b) as ab eqn:Hab; symmetry in Hab.
remember (ltb b a) as ba eqn:Hba; symmetry in Hba.
remember (ltb b c) as bc eqn:Hbc; symmetry in Hbc.
remember (ltb c b) as cb eqn:Hcb; symmetry in Hcb.
move ba before ab; move bc before ba; move cb before bc.
move ca before cb.
destruct ab. 2: {
  destruct ba; [ easy | ].
  specialize (Hcon _ _ Hab Hba) as H; subst a.
  destruct bc; [ congruence | ].
  destruct cb; [ easy | ].
  destruct ca; [ | now apply (IHlc _ lb) ].
  specialize (Hcon _ _ Hbc Hcb) as H; subst c.
  congruence.
}
destruct ca. 2: {
  specialize (Hcon _ _ Hac Hca) as H; subst c.
  destruct bc. {
    clear Hlab Hlbc.
    specialize (Hant a b Hab Hbc) as H1; subst a.
    congruence.
  }
  destruct cb; [ easy | congruence ].
}
destruct bc. {
  specialize (Htra a b c Hab Hbc) as H1.
  congruence.
}
destruct cb; [ easy | ].
specialize (Hcon b c Hbc Hcb) as H1; subst c.
congruence.
Qed.

Theorem sorted_sorted_map_cons : ∀ A (ltb : A → _),
  antisymmetric ltb →
  transitive ltb →
  connected_relation ltb →
  ∀ ll a,
  sorted (list_ltb ltb) ll → sorted (list_ltb ltb) (List.map (cons a) ll).
Proof.
intros * Hant Htra Hcon * Hs.
induction ll as [| la]; [ easy | cbn ].
apply sorted_cons_iff in Hs; [ | now apply transitive_list_ltb ].
destruct Hs as (Hs, Hlab).
apply sorted_cons_iff; [ now apply transitive_list_ltb | ].
split; [ now apply IHll | ].
intros lb Hlb; cbn.
destruct lb as [| b]. {
  clear IHll Hs Hlab.
  induction ll as [| lb]; [ easy | ].
  cbn in Hlb.
  destruct Hlb as [Hlb| Hlb]; [ easy | ].
  now apply IHll.
}
remember (ltb a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ easy | ].
remember (ltb b a) as ba eqn:Hba; symmetry in Hba.
apply List.in_map_iff in Hlb.
destruct Hlb as (lc & Hll & Hlb).
injection Hll; clear Hll; intros; subst b lc.
destruct ba; [ congruence | ].
now apply Hlab.
Qed.

(* *)

Theorem sorted_concat_iff : ∀ A (rel : A → _),
  transitive rel →
  ∀ ll,
  sorted rel (List.concat ll) ↔
    (∀ l, l ∈ ll → sorted rel l) ∧
    (∀ i j, i < j < length ll →
     ∀ a b, a ∈ List.nth i ll [] → b ∈ List.nth j ll [] → rel a b = true).
Proof.
intros * Htra *.
split. {
  intros Hs.
  split. {
    intros la Hla.
    induction ll as [| lb]; [ easy | ].
    cbn in Hs.
    apply sorted_app_iff in Hs; [ | easy ].
    destruct Hla as [Hla| Hla]; [ now subst lb | ].
    now apply IHll.
  }
  intros i j Hij a b Ha Hb.
  revert i j a b Hij Ha Hb.
  induction ll as [| la]; intros; [ easy | ].
  assert (H : sorted rel (List.concat ll)). {
    now cbn in Hs; apply sorted_app_iff in Hs; [ | easy ].
  }
  specialize (IHll H); clear H.
  cbn in Ha, Hb.
  destruct j; [ easy | ].
  destruct i. {
    cbn in Hs.
    apply sorted_app_iff in Hs; [ | easy ].
    destruct Hs as (Hla & Hs & Hab).
    apply Hab; [ easy | ].
    apply List.in_concat.
    exists (List.nth j ll []).
    split; [ | easy ].
    apply List.nth_In.
    destruct Hij as (_, Hj); cbn in Hj.
    now apply Nat.succ_lt_mono in Hj.
  }
  apply (IHll i j); [ | easy | easy ].
  destruct Hij as (Hi, Hj); cbn in Hj.
  now apply Nat.succ_lt_mono in Hi, Hj.
}
intros (Hs & Hleb).
induction ll as [| la]; [ easy | cbn ].
apply sorted_app_iff; [ easy | ].
split; [ now apply Hs; left | ].
split. {
  apply IHll. {
    now intros lb Hlb; apply Hs; right.
  } {
    intros i j Hij a b Ha Hb.
    apply (Hleb (S i) (S j)); [ | easy | easy ].
    now split; apply -> Nat.succ_lt_mono.
  }
}
intros a b Ha Hb.
apply List.in_concat in Hb.
destruct Hb as (lb & Hlb & Hb).
apply (List.In_nth _ _ []) in Hlb.
destruct Hlb as (j & Hjl & Hlb).
apply (Hleb 0 (S j)); [ | easy | now cbn; rewrite Hlb ].
split; [ easy | cbn ].
now apply -> Nat.succ_lt_mono.
Qed.

Theorem cart_prod_repeat_seq_ltb_sorted : ∀ i n m,
  sorted (list_ltb Nat.ltb) (cart_prod (List.repeat (List.seq i n) m)).
Proof.
intros.
revert i n.
induction m; intros; [ easy | cbn ].
rewrite List.flat_map_concat_map.
specialize Nat_ltb_antisym as Hant.
specialize Nat_ltb_connected as Hcon.
specialize Nat_ltb_trans as Htra.
apply sorted_concat_iff; [ now apply transitive_list_ltb | ].
rewrite List_length_map_seq.
split. {
  intros ll Hll.
  apply List.in_map_iff in Hll.
  destruct Hll as (a & Hll & Ha); subst ll.
  apply sorted_sorted_map_cons; [ easy | easy | easy | apply IHm ].
}
intros j k Hjk la lb Ha Hb.
rewrite (List_map_nth' 0) in Ha; [ | rewrite List.length_seq; flia Hjk ].
rewrite (List_map_nth' 0) in Hb; [ | rewrite List.length_seq; easy ].
apply List.in_map_iff in Ha, Hb.
destruct Ha as (lc & Hc & Hlc).
destruct Hb as (ld & Hd & Hld).
move ld before lc.
subst la lb; cbn.
unfold "<?"; cbn.
rename lc into la; rename ld into lb.
remember (List.nth k (List.seq i n) 0) as a eqn:Ha; symmetry in Ha.
remember (List.nth j (List.seq i n) 0) as b eqn:Hb; symmetry in Hb.
rewrite List.seq_nth in Ha; [ | easy ].
rewrite List.seq_nth in Hb; [ | flia Hjk ].
subst a b.
destruct k; [ easy | ].
rewrite Nat.add_comm; cbn.
rewrite if_leb_le_dec.
destruct (le_dec (i + j) (k + i)) as [H| H]; [ easy | flia Hjk H].
Qed.

Theorem list_ltb_leb_incl : ∀ la lb,
  list_ltb Nat.ltb la lb = true
  → list_leb Nat.leb la lb = true.
Proof.
intros * Hlab.
revert lb Hlab.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | ].
cbn in Hlab.
unfold "<?" in Hlab; cbn in Hlab.
destruct b. {
  destruct a; [ now apply IHla | easy ].
}
rewrite if_leb_le_dec in Hlab.
destruct (le_dec a b) as [Hab| Hab]. {
  do 2 rewrite if_leb_le_dec.
  destruct (le_dec a (S b)) as [H| H]; [ clear H | flia Hab H ].
  destruct (le_dec (S b) a) as [H| H]; [ flia Hab H | easy ].
}
destruct a; [ easy | cbn ].
apply Nat.nle_gt in Hab.
rewrite if_leb_le_dec in Hlab.
destruct (le_dec (S b) a) as [Hsba| Hsba]; [ easy | ].
apply Nat.nle_gt in Hsba.
replace b with a by flia Hab Hsba.
rewrite Nat.leb_refl.
now apply IHla.
Qed.

Theorem sorted_list_ltb_leb_incl : ∀ lla,
  sorted (list_ltb Nat.ltb) lla → sorted (list_leb Nat.leb) lla.
Proof.
intros * Hs.
assert (Htralt : transitive (list_ltb Nat.ltb)). {
  apply transitive_list_ltb. {
    apply Nat_ltb_antisym.
  } {
    apply Nat_ltb_connected.
  } {
    apply Nat_ltb_trans.
  }
}
assert (Htrale : transitive (list_leb Nat.leb)). {
  apply transitive_list_leb, Nat_leb_trans.
}
specialize Nat_ltb_trans as Htra.
induction lla as [| la]; [ easy | ].
apply sorted_cons_iff in Hs; [ | easy ].
apply sorted_cons_iff; [ easy | ].
destruct Hs as (Hs, Hab).
split; [ now apply IHlla | ].
intros lb Hlb.
apply list_ltb_leb_incl.
now apply Hab.
Qed.

Theorem NoDup_sorted_nat_leb_ltb : ∀ l,
  List.NoDup l → sorted Nat.leb l → sorted Nat.ltb l.
Proof.
intros * Hns Hs.
induction l as [| a]; [ easy | cbn ].
assert (H : List.NoDup l) by now apply List.NoDup_cons_iff in Hns.
specialize (IHl H); clear H.
assert (H : sorted Nat.leb l). {
  apply sorted_cons_iff in Hs; [ easy | apply Nat_leb_trans ].
}
specialize (IHl H); clear H.
apply sorted_cons_iff; [ apply Nat_ltb_trans | ].
split; [ easy | ].
intros b Hb.
apply Nat.ltb_lt.
apply List.NoDup_cons_iff in Hns.
destruct Hns as (Hal, Hnd).
apply sorted_cons_iff in Hs; [ | apply Nat_leb_trans ].
destruct Hs as (Hs & Hab).
specialize (Hab _ Hb) as H1.
apply Nat.leb_le in H1.
destruct (Nat.eq_dec a b) as [H| H]; [ now subst b | ].
flia H1 H.
Qed.

Theorem sorted_filter : ∀ A (rel : A → _),
  transitive rel →
  ∀ l f,
  sorted rel l → sorted rel (List.filter f l).
Proof.
intros * Htra * Hs.
induction l as [| a]; [ easy | cbn ].
remember (f a) as fa eqn:Hfa; symmetry in Hfa.
destruct fa. {
  apply sorted_cons_iff; [ easy | ].
  apply sorted_cons_iff in Hs; [ | easy ].
  destruct Hs as (Hs & Hr).
  split; [ now apply IHl | ].
  intros b Hb.
  apply List.filter_In in Hb.
  now apply Hr.
}
apply sorted_cons in Hs.
now apply IHl.
Qed.
