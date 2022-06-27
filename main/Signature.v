(* signatures *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Misc SortingFun PermutationFun RingLike.
Require Import IterMul PermutSeq.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

(* version of signature of a permutation using sign *)

Definition sign_diff u v :=
  match Nat.compare u v with
  | Lt => (-1)%F
  | Eq => 0%F
  | Gt => 1%F
  end.
Definition abs_diff u v := if v <? u then u - v else v - u.

Definition ε (p : list nat) :=
  let n := length p in
  ∏ (i = 0, n - 1), ∏ (j = 0, n - 1),
  if i <? j then sign_diff (ff_app p j) (ff_app p i) else 1.

Definition rngl_sub_nat i j := (rngl_of_nat i - rngl_of_nat j)%F.

(* other definition of ε *)

Definition ε' (p : list nat) :=
  let n := length p in
  ((∏ (i = 0, n - 1), ∏ (j = 0, n - 1),
    if i <? j then rngl_sub_nat (ff_app p j) (ff_app p i) else 1) /
   (∏ (i = 0, n - 1), ∏ (j = 0, n - 1),
    if i <? j then rngl_sub_nat j i else 1))%F.

Definition minus_one_pow n :=
  match n mod 2 with
  | 0 => 1%F
  | _ => (- 1%F)%F
  end.

Theorem fold_ε : ∀ p,
  ∏ (i = 0, length p - 1),
  (∏ (j = 0, length p - 1),
   (if i <? j then sign_diff (ff_app p j) (ff_app p i) else 1)) =
  ε p.
Proof. easy. Qed.

Theorem ε_nil : ε [] = 1%F.
Proof.
unfold ε; cbn.
rewrite rngl_product_only_one.
now rewrite rngl_product_only_one.
Qed.

Theorem ε_map_S : ∀ l, ε (map S l) = ε l.
Proof.
intros.
unfold ε.
rewrite map_length.
apply rngl_product_eq_compat.
intros i (_, Hi).
apply rngl_product_eq_compat.
intros j (_, Hj).
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
unfold sign_diff.
unfold ff_app.
rewrite (List_map_nth' 0); [ | flia Hj Hij ].
rewrite (List_map_nth' 0); [ | flia Hj Hij ].
easy.
Qed.

Theorem minus_one_pow_succ :
  rngl_has_opp = true →
  ∀ i, minus_one_pow (S i) = (- minus_one_pow i)%F.
Proof.
intros Hop *.
unfold minus_one_pow.
remember (i mod 2) as k eqn:Hk; symmetry in Hk.
destruct k. {
  apply Nat.mod_divides in Hk; [ | easy ].
  destruct Hk as (k, Hk); subst i.
  rewrite <- Nat.add_1_l, Nat.mul_comm.
  now rewrite Nat.mod_add.
}
destruct k. {
  rewrite <- Nat.add_1_l.
  rewrite <- Nat.add_mod_idemp_r; [ | easy ].
  rewrite Hk; cbn.
  symmetry.
  now apply rngl_opp_involutive.
}
specialize (Nat.mod_upper_bound i 2) as H1.
assert (H : 2 ≠ 0) by easy.
specialize (H1 H); clear H.
rewrite Hk in H1.
flia H1.
Qed.

Theorem minus_one_pow_succ_succ :
  rngl_has_opp = true →
  ∀ i, minus_one_pow (S (S i)) = minus_one_pow i.
Proof.
intros Hop *.
rewrite minus_one_pow_succ; [ | easy ].
rewrite minus_one_pow_succ; [ | easy ].
now apply rngl_opp_involutive.
Qed.

Theorem minus_one_pow_add_r :
  rngl_has_opp = true →
  ∀ i j, minus_one_pow (i + j) = (minus_one_pow i * minus_one_pow j)%F.
Proof.
intros Hop *.
revert j.
induction i; intros; [ now cbn; rewrite rngl_mul_1_l | ].
rewrite Nat.add_succ_comm.
rewrite IHi.
rewrite minus_one_pow_succ; [ | easy ].
rewrite minus_one_pow_succ; [ | easy ].
rewrite rngl_mul_opp_l; [ | easy ].
rewrite rngl_mul_opp_r; [ | easy ].
easy.
Qed.

(* signature of the k-th permutation of the symmetric group *)

Fixpoint ε_permut n k :=
  match n with
  | 0 => 1%F
  | S n' => (minus_one_pow (k / fact n') * ε_permut n' (k mod fact n'))%F
  end.

Theorem rngl_product_product_if : ∀ b e f,
  (∏ (i = b, e), ∏ (j = b, e), if i <? j then f i j else 1)%F =
  (∏ (i = b, e), ∏ (j = i + 1, e), f i j)%F.
Proof.
intros.
apply rngl_product_eq_compat.
intros i Hi.
rewrite (rngl_product_split i); [ | flia Hi ].
rewrite all_1_rngl_product_1. 2: {
  intros j Hj.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec i j) as [H| H]; [ flia Hj H | easy ].
}
rewrite rngl_mul_1_l.
apply rngl_product_eq_compat.
intros j Hj.
rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [H| H]; [ easy | flia Hj H ].
Qed.

Theorem rngl_of_nat_sub :
  rngl_has_opp = true →
  ∀ i j,
  (rngl_of_nat j - rngl_of_nat i)%F =
     if i <? j then rngl_of_nat (j - i)
     else (- rngl_of_nat (i - j))%F.
Proof.
intros Hom *.
rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [Hij| Hij]. {
  revert j Hij.
  induction i; intros; cbn. {
    rewrite rngl_sub_0_r; f_equal; [ | now left ].
    now destruct j.
  }
  destruct j; [ easy | cbn ].
  rewrite rngl_add_sub_simpl_l; [ | now left ].
  apply IHi.
  now apply Nat.succ_lt_mono in Hij.
} {
  apply Nat.nlt_ge in Hij.
  revert j Hij.
  induction i; intros; cbn. {
    rewrite rngl_sub_0_r; f_equal; [ | now left ].
    rewrite rngl_opp_0; [ | easy ].
    now apply Nat.le_0_r in Hij; subst j.
  }
  destruct j. {
    unfold rngl_sub; rewrite Hom; cbn.
    now rewrite rngl_add_0_l.
  }
  cbn.
  rewrite rngl_add_sub_simpl_l; [ | now left ].
  apply IHi.
  now apply Nat.succ_le_mono in Hij.
}
Qed.

Theorem rngl_of_nat_add : ∀ a b,
  (rngl_of_nat a + rngl_of_nat b)%F = rngl_of_nat (a + b).
Proof.
intros.
induction a; [ apply rngl_add_0_l | ].
now cbn; rewrite <- rngl_add_assoc; f_equal.
Qed.

Theorem rngl_of_nat_mul :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ a b, (rngl_of_nat a * rngl_of_nat b)%F = rngl_of_nat (a * b).
Proof.
intros Hom *.
induction a; [ now apply rngl_mul_0_l | cbn ].
rewrite rngl_mul_add_distr_r.
rewrite rngl_mul_1_l.
rewrite IHa.
apply rngl_of_nat_add.
Qed.

Theorem rngl_product_rngl_of_nat :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ n, (∏ (i = 1, n), rngl_of_nat i)%F = rngl_of_nat (fact n).
Proof.
intros Hom *.
induction n. {
  rewrite rngl_product_empty; [ | easy ].
  symmetry; apply rngl_add_0_r.
}
rewrite rngl_product_split_last; [ | flia ].
rewrite rngl_product_succ_succ.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  now rewrite Nat_sub_succ_1.
}
rewrite IHn.
rewrite Nat_fact_succ.
rewrite Nat.mul_comm.
now apply rngl_of_nat_mul.
Qed.

Definition sign_diff' u v := if u <? v then (-1)%F else 1%F.

Theorem sign_diff'_sign_diff : ∀ u v,
  u ≠ v → sign_diff' u v = sign_diff u v.
Proof.
intros * Huv.
unfold sign_diff', sign_diff.
rewrite if_ltb_lt_dec.
destruct (lt_dec u v) as [Huv1| Huv1]. {
  now apply Nat.compare_lt_iff in Huv1; rewrite Huv1.
}
destruct (lt_dec v u) as [Hvu1| Hvu1]. {
  now apply Nat.compare_gt_iff in Hvu1; rewrite Hvu1.
}
apply Nat.nlt_ge in Huv1, Hvu1.
exfalso; apply Huv; clear Huv.
now apply Nat.le_antisymm.
Qed.

Theorem rngl_sub_is_mul_sign_abs :
  rngl_has_opp = true →
  ∀ a b,
  (rngl_of_nat a - rngl_of_nat b)%F =
  (sign_diff a b * rngl_of_nat (abs_diff a b))%F.
Proof.
intros Hop *.
unfold sign_diff, abs_diff.
rewrite if_ltb_lt_dec.
remember (a ?= b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  apply Nat.compare_eq in Hab; subst b.
  rewrite rngl_sub_diag; [ | now left ].
  rewrite rngl_mul_0_l; [ easy | now left ].
} {
  apply nat_compare_lt in Hab.
  destruct (lt_dec b a) as [H| H]; [ flia Hab H | clear H ].
  rewrite <- rngl_opp_sub_distr; [ | easy ].
  rewrite rngl_of_nat_sub; [ | easy ].
  apply Nat.ltb_lt in Hab; rewrite Hab.
  rewrite rngl_mul_opp_l; [ | easy ].
  now rewrite rngl_mul_1_l.
} {
  apply nat_compare_gt in Hab.
  rewrite rngl_mul_1_l.
  destruct (lt_dec b a) as [H| H]; [ clear H | flia Hab H ].
  rewrite rngl_of_nat_sub; [ | easy ].
  now apply Nat.ltb_lt in Hab; rewrite Hab.
}
Qed.

Theorem rngl_sign_diff'_sub_div_abs :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_characteristic = 0 →
  ∀ a b,
  a ≠ b
  → sign_diff' a b =
       ((rngl_of_nat a - rngl_of_nat b) / rngl_of_nat (abs_diff a b))%F.
Proof.
intros Hop Hiv Hch * Hab.
assert (Hnz : rngl_of_nat (abs_diff a b) ≠ 0%F). {
  unfold abs_diff.
  rewrite if_ltb_lt_dec.
  intros H.
  destruct (lt_dec b a) as [Hba| Hba]. {
    apply eq_rngl_of_nat_0 in H; [ | easy ].
    flia Hba H.
  } {
    apply eq_rngl_of_nat_0 in H; [ | easy ].
    flia Hab Hba H.
  }
}
apply rngl_mul_cancel_r with (c := rngl_of_nat (abs_diff a b)). {
  now left.
} {
  easy.
}
rewrite rngl_div_mul; [ | easy | easy ].
rewrite rngl_sub_is_mul_sign_abs; [ | easy ].
f_equal.
unfold sign_diff', sign_diff.
rewrite if_ltb_lt_dec.
destruct (lt_dec a b) as [Hab1| Hab1]. {
  now apply Nat.compare_lt_iff in Hab1; rewrite Hab1.
} {
  apply Nat.nlt_ge in Hab1.
  assert (H : b < a) by flia Hab Hab1.
  now apply Nat.compare_gt_iff in H; rewrite H.
}
Qed.

Theorem rngl_product_change_var : ∀ A b e f g (h : _ → A),
  (∀ i, b ≤ i ≤ e → g (h i) = i)
  → (∏ (i = b, e), f i = ∏ (i ∈ map h (seq b (S e - b))), f (g i))%F.
Proof.
intros * Hgh.
unfold iter_seq, iter_list.
rewrite List_fold_left_map.
apply List_fold_left_ext_in.
intros i c Hi.
f_equal; f_equal; symmetry.
apply Hgh.
apply in_seq in Hi.
flia Hi.
Qed.

Theorem rngl_product_change_list : ∀ A (eqb : A → _),
  equality eqb →
  rngl_is_comm = true →
  ∀ la lb f,
  permutation eqb la lb
  → (∏ (i ∈ la), f i = ∏ (i ∈ lb), f i)%F.
Proof.
intros * Heqb Hic * Hpab.
revert lb Hpab.
induction la as [| a]; intros. {
  now apply permutation_nil_l in Hpab; subst lb.
}
apply permutation_cons_l_iff in Hpab.
remember (extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x lb.
rewrite rngl_product_list_app.
do 2 rewrite rngl_product_list_cons.
rewrite (rngl_mul_comm Hic (∏ (i ∈ bef), f i)).
rewrite <- rngl_mul_assoc; f_equal.
rewrite (rngl_mul_comm Hic).
rewrite <- rngl_product_list_app.
now apply IHla.
Qed.

Theorem rngl_product_product_div_eq_1 :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_is_comm = true →
  rngl_has_inv = true →
  rngl_is_integral = true →
  rngl_has_1_neq_0 = true →
  rngl_has_eqb = true →
  ∀ n f g,
  (∀ i j, i < n → j < n → g i j ≠ 0%F)
  → (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), (f i j / g i j)))%F = 1%F
  → (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), f i j))%F =
    (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), g i j))%F.
Proof.
intros Hom Hic Hid Hin H10 Heq * Hg Hs.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
remember (∏ (i ∈ _), _)%F as a eqn:Ha in |-*.
remember (∏ (i ∈ _), _)%F as b eqn:Hb in |-*.
remember (rngl_eqb b 0%F) as bz eqn:Hbz; symmetry in Hbz.
destruct bz. {
  apply (rngl_eqb_eq Heq) in Hbz.
  rewrite Hbz in Hb |-*; clear Hbz; subst a; symmetry in Hb.
  apply rngl_product_list_integral in Hb; [ | easy | easy | easy ].
  destruct Hb as (i & His & Hb).
  apply rngl_product_list_integral in Hb; [ | easy | easy | easy ].
  destruct Hb as (j & Hjs & Hb).
  move j before i.
  exfalso; revert Hb.
  apply in_seq in His.
  apply in_seq in Hjs.
  now apply Hg.
}
apply (rngl_eqb_neq Heq) in Hbz.
apply rngl_mul_cancel_r with (c := (b⁻¹)%F); [ now left | | ]. {
  intros Hbiz.
  apply (f_equal (rngl_mul b)) in Hbiz.
  rewrite fold_rngl_div in Hbiz; [ | easy ].
  rewrite rngl_mul_inv_r in Hbiz; [ | now left | easy ].
  rewrite rngl_mul_0_r in Hbiz; [ | easy ].
  now apply rngl_1_neq_0 in Hbiz.
}
remember (_ * _)%F as c.
rewrite fold_rngl_div; [ | easy ].
rewrite rngl_mul_inv_r; [ | now left | easy ].
subst c b.
rewrite rngl_inv_product_list; [ | easy | easy | easy | easy | ]. 2: {
  intros i Hi H1.
  apply rngl_product_list_integral in H1; [ | easy | easy | easy ].
  destruct H1 as (j & Hjs & Hijz).
  exfalso.
  revert Hijz.
  apply in_seq in Hi.
  apply in_seq in Hjs.
  now apply Hg.
}
subst a.
erewrite (rngl_product_list_permut _ _ Nat.eqb_eq) with
    (l1 := rev _); [ | easy | ]. 2: {
  apply (permutation_rev_l Nat.eqb_eq).
}
rewrite <- rngl_product_list_mul_distr; [ | easy ].
erewrite rngl_product_list_eq_compat. 2 :{
  intros i Hi.
  rewrite rngl_inv_product_list; [ | easy | easy | easy | easy | ]. 2: {
    intros j Hj.
    apply in_seq in Hi.
    apply in_seq in Hj.
    now apply Hg.
  }
  erewrite (rngl_product_list_permut _ _ Nat.eqb_eq) with
      (l1 := rev _); [ | easy | ]. 2: {
    apply (permutation_rev_l Nat.eqb_eq).
  }
  rewrite <- rngl_product_list_mul_distr; [ | easy ].
  erewrite rngl_product_list_eq_compat. 2: {
    intros j Hj.
    rewrite fold_rngl_div; [ | easy ].
    easy.
  }
  easy.
}
easy.
Qed.

Theorem rngl_product_product_by_swap :
  rngl_is_comm = true →
  ∀ n f,
  (∏ (i ∈ seq 0 n), ∏ (j ∈ seq 0 n), f i j)%F =
  ((∏ (i ∈ seq 0 n), f i i) *
   (∏ (i ∈ seq 0 (n - 1)), ∏ (j = i + 1, n - 1), (f i j * f j i)))%F.
Proof.
intros Hic *.
induction n. {
  unfold iter_seq, iter_list; cbn.
  now rewrite rngl_mul_1_l.
}
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; unfold iter_list; cbn.
  now rewrite rngl_mul_1_l, rngl_mul_1_r.
}
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]. {
  subst n; unfold iter_seq, iter_list; cbn.
  do 5 rewrite rngl_mul_1_l.
  repeat rewrite <- rngl_mul_assoc.
  f_equal; symmetry.
  rewrite rngl_mul_comm; [ | easy ].
  now rewrite rngl_mul_assoc.
}
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite seq_S.
  rewrite iter_list_app.
  unfold iter_list at 1; cbn.
  easy.
}
cbn - [ seq ].
rewrite Nat.sub_0_r.
rewrite rngl_product_list_mul_distr; [ | easy ].
rewrite seq_S.
rewrite iter_list_app.
unfold iter_list at 1; cbn.
rewrite IHn.
rewrite iter_list_app; cbn.
rewrite iter_list_app; cbn.
unfold iter_list at 4 6; cbn.
do 3 rewrite <- rngl_mul_assoc.
f_equal.
rewrite (rngl_mul_comm Hic (f n n)).
do 2 rewrite rngl_mul_assoc.
f_equal.
symmetry.
rewrite rngl_product_seq_product; [ | easy ].
cbn - [ seq ].
rewrite rngl_product_split_last; [ | flia Hnz ].
rewrite (rngl_product_shift 1); [ | flia Hnz Hn1 ].
rewrite Nat.sub_diag.
rewrite Nat.sub_add; [ | flia Hnz ].
unfold iter_seq.
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hnz Hn1 ].
rewrite Nat_sub_succ_1.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite (Nat.add_comm 1), Nat.add_sub.
  rewrite Nat.add_1_r.
  rewrite Nat.sub_succ.
  apply in_seq in Hi.
  rewrite Nat_succ_sub_succ_r by flia Hnz Hn1 Hi.
  rewrite seq_S.
  rewrite Nat.add_comm, Nat.sub_add; [ | flia Hnz Hn1 Hi ].
  unfold iter_list.
  rewrite fold_left_app.
  cbn - [ seq ].
  rewrite fold_iter_list.
  easy.
}
cbn - [ seq "-" ].
symmetry.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite <- Nat_succ_sub_succ_r; [ | flia Hnz ].
  now rewrite Nat.sub_0_r, Nat.add_1_r.
}
cbn - [ seq "-" ].
rewrite rngl_product_list_mul_distr; [ | easy ].
do 2 rewrite <- rngl_mul_assoc.
f_equal.
rewrite Nat.sub_succ_l; [ | easy ].
rewrite Nat.sub_diag.
unfold iter_list at 4; cbn.
rewrite rngl_mul_1_l.
rewrite rngl_product_seq_product; [ | easy ].
cbn - [ seq ].
rewrite rngl_product_split_last; [ | flia Hnz ].
rewrite (rngl_product_shift 1); [ | flia Hnz Hn1 ].
rewrite Nat.sub_diag.
unfold iter_seq.
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hnz Hn1 ].
rewrite Nat_sub_succ_1.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite (Nat.add_comm 1), Nat.add_sub.
  easy.
}
rewrite rngl_product_list_mul_distr; [ | easy ].
symmetry.
rewrite <- rngl_mul_assoc.
rewrite rngl_mul_comm; [ | easy ].
do 3 rewrite <- rngl_mul_assoc.
f_equal.
rewrite rngl_mul_comm; [ | easy ].
rewrite <- rngl_mul_assoc.
f_equal.
symmetry.
rewrite rngl_product_seq_product; [ | easy ].
cbn - [ seq ].
rewrite rngl_product_split_last; [ | flia Hnz ].
rewrite (rngl_product_shift 1); [ | flia Hnz Hn1 ].
rewrite Nat.sub_diag.
unfold iter_seq.
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hnz Hn1 ].
rewrite Nat_sub_succ_1.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite (Nat.add_comm 1), Nat.add_sub.
  easy.
}
easy.
Qed.

Theorem permut_swap_mul_cancel : ∀ n σ f,
  rngl_is_comm = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  is_permut n σ
  → (∀ i j, f i j = f j i)
  → (∀ i j, i < n → j < n → i ≠ j → f i j ≠ 0%F)
  → ∀ i j, i < n → j < n →
    ((if ff_app σ i <? ff_app σ j then f i j else 1) /
      (if i <? j then f i j else 1) *
     ((if ff_app σ j <? ff_app σ i then f j i else 1) /
      (if j <? i then f j i else 1)))%F = 1%F.
Proof.
intros * Hic Hin H10 (Hp, Hn) Hfij Hfijnz * Hlin Hljn.
do 4 rewrite if_ltb_lt_dec.
destruct (lt_dec (ff_app σ i) (ff_app σ j)) as [H1| H1]. {
  destruct (lt_dec (ff_app σ j) (ff_app σ i)) as [H| H]; [ flia H1 H | ].
  clear H.
  destruct (lt_dec i j) as [H3| H3]. {
    destruct (lt_dec j i) as [H| H]; [ flia H3 H | clear H ].
    rewrite Hfij.
    rewrite rngl_mul_inv_r; [ | now left | ]. 2: {
      apply Hfijnz; [ easy | easy | flia H3 ].
    }
    rewrite rngl_mul_1_l.
    apply rngl_mul_inv_r; [ now left | now apply rngl_1_neq_0 ].
  }
  destruct (lt_dec j i) as [H4| H4]. {
    rewrite Hfij.
    rewrite rngl_div_1_r; [ | now left | easy ].
    rewrite rngl_div_1_l; [ | easy ].
    rewrite fold_rngl_div; [ | easy ].
    apply rngl_mul_inv_r; [ now left | ].
    apply Hfijnz; [ easy | easy | flia H4 ].
  }
  exfalso.
  apply Nat.nlt_ge in H3.
  apply Nat.nlt_ge in H4.
  apply Nat.le_antisymm in H3; [ | easy ].
  subst j; flia H1.
}
destruct (lt_dec (ff_app σ j) (ff_app σ i)) as [H2| H2]. {
  destruct (lt_dec i j) as [H3| H3]. {
    destruct (lt_dec j i) as [H| H]; [ flia H3 H | clear H ].
    rewrite Hfij.
    rewrite rngl_div_1_r; [ | now left | easy ].
    rewrite rngl_div_1_l; [ | easy ].
    rewrite rngl_mul_comm; [ | easy ].
    rewrite fold_rngl_div; [ | easy ].
    apply rngl_mul_inv_r; [ now left | ].
    apply Hfijnz; [ easy | easy | flia H3 ].
  }
  destruct (lt_dec j i) as [H4| H4]. {
    rewrite Hfij.
    rewrite rngl_div_1_r; [ | now left | easy ].
    rewrite rngl_mul_1_l.
    apply rngl_mul_inv_r; [ now left | ].
    apply Hfijnz; [ easy | easy | flia H4 ].
  }
  exfalso.
  apply Nat.nlt_ge in H3.
  apply Nat.nlt_ge in H4.
  apply Nat.le_antisymm in H3; [ | easy ].
  subst j; flia H2.
}
apply Nat.nlt_ge in H1.
apply Nat.nlt_ge in H2.
apply Nat.le_antisymm in H1; [ | easy ].
destruct (lt_dec i j) as [H3| H3]. {
  destruct (lt_dec j i) as [H| H]; [ flia H3 H | clear H ].
  destruct Hp as (_, Hp).
  apply (NoDup_nat _ Hp) in H1; [ | now rewrite Hn | now rewrite Hn ].
  flia H1 H3.
}
destruct (lt_dec j i) as [H4| H4]. {
  destruct Hp as (_, Hp).
  apply (NoDup_nat _ Hp) in H1; [ | now rewrite Hn | now rewrite Hn ].
  flia H1 H4.
}
rewrite rngl_div_1_r; [ | now left | easy ].
apply rngl_mul_1_l.
Qed.

Theorem product_product_if_permut_div :
  rngl_is_comm = true →
  rngl_has_1_neq_0 = true →
  rngl_has_inv = true →
  ∀ n σ f,
  is_permut n σ
  → (∀ i j, f i j = f j i)
  → (∀ i j, i < n → j < n → i ≠ j → f i j ≠ 0%F)
  → (∏ (i ∈ seq 0 n), ∏ (j ∈ seq 0 n),
      ((if ff_app σ i <? ff_app σ j then f i j else 1) /
       (if i <? j then f i j else 1)))%F =
     1%F.
Proof.
intros Hic H10 Hin * (Hp, Hn) Hfij Hfijnz.
rewrite rngl_product_product_by_swap; [ | easy ].
rewrite all_1_rngl_product_list_1; [ | easy | ]. 2: {
  intros i Hi.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec _ _) as [H| H]; [ flia H | clear H ].
  destruct (lt_dec _ _) as [H| H]; [ flia H | clear H ].
  apply rngl_div_1_r; [ now left | easy ].
}
rewrite rngl_mul_1_l.
apply all_1_rngl_product_list_1; [ easy | ].
intros i Hi.
apply all_1_rngl_product_list_1; [ easy | ].
intros j Hj.
apply in_seq in Hi.
apply in_seq in Hj.
apply (@permut_swap_mul_cancel n); try easy; [ flia Hi | flia Hj ].
Qed.

Theorem product_product_if_permut :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_is_comm = true →
  rngl_has_inv = true →
  rngl_is_integral = true →
  rngl_has_1_neq_0 = true →
  rngl_has_eqb = true →
  ∀ n σ f,
  is_permut n σ
  → (∀ i j, f i j = f j i)
  → (∀ i j, i < n → j < n → i ≠ j → f i j ≠ 0%F)
  → (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n),
        if ff_app σ i <? ff_app σ j then f i j else 1))%F =
    (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n),
        if i <? j then f i j else 1))%F.
Proof.
intros Hom Hic Hid Hin H10 Heq * (Hp, Hn) Hfij Hfijnz.
apply rngl_product_product_div_eq_1; try easy. {
  intros i j Hi Hj.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec i j) as [Hij| Hij]; [ | now apply rngl_1_neq_0 ].
  apply Hfijnz; [ easy | easy | flia Hij ].
}
now apply product_product_if_permut_div.
Qed.

Theorem rngl_product_product_abs_diff_div_diff : in_charac_0_field →
  ∀ p,
  is_permut_list p
  → ∏ (i = 0, length p - 1),
    (∏ (j = 0, length p - 1),
     (if i <? j then
        rngl_of_nat (abs_diff (ff_app p j) (ff_app p i)) /
        rngl_of_nat (j - i)
      else 1)) = 1%F.
Proof.
intros (Hic & Hop & Hin & H10 & Hit & Hde & Hch) * Hp.
destruct (le_dec (length p) 1) as [Hn1| Hn1]. {
  replace (length p - 1) with 0 by flia Hn1.
  now do 2 rewrite rngl_product_only_one.
}
rewrite rngl_product_product_if.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_div_distr; try easy; [ now left | ].
  intros j Hj.
  intros H.
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  flia Hj H.
}
cbn.
rewrite rngl_product_div_distr; try easy; [ | now left | ]. 2: {
  intros i Hi H.
  apply (rngl_product_integral (or_introl Hop) Hit H10) in H.
  destruct H as (j & Hj & Hji).
  apply eq_rngl_of_nat_0 in Hji; [ | easy ].
  flia Hj Hji.
}
apply eq_rngl_div_1; [ now left | | ]. {
  intros H.
  apply (rngl_product_integral (or_introl Hop) Hit H10) in H.
  destruct H as (i & Hi & H).
  apply (rngl_product_integral (or_introl Hop) Hit H10) in H.
  destruct H as (j & Hj & H).
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  flia Hj H.
}
rewrite <- rngl_product_product_if; symmetry.
rewrite <- rngl_product_product_if; symmetry.
apply Nat.nle_gt in Hn1.
(* changt of var *)
rewrite rngl_product_change_var with
  (g := ff_app (isort_rank Nat.leb p)) (h := ff_app p). 2: {
  intros i Hi.
  destruct Hp as (Hp1, Hp2).
  apply permut_isort_permut; [ easy | flia Hi Hn1 ].
}
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hn1 ].
rewrite Nat_sub_succ_1.
rewrite <- List_map_ff_app_seq.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_change_var with
    (g := ff_app (isort_rank Nat.leb p)) (h := ff_app p). 2: {
    intros j Hj.
    destruct Hp as (Hp1, Hp2).
    apply permut_isort_permut; [ easy | flia Hj Hn1 ].
  }
  rewrite <- Nat.sub_succ_l; [ | flia Hn1 ].
  rewrite Nat_sub_succ_1, Nat.sub_0_r.
  rewrite <- List_map_ff_app_seq.
  apply (In_nth _ _ 0) in Hi.
  destruct Hi as (u & Hu & Hui).
  replace (ff_app _ (ff_app _ i)) with i. 2: {
    symmetry.
    apply permut_permut_isort; [ easy | ].
    rewrite <- Hui.
    now apply permut_list_ub.
  }
  erewrite rngl_product_list_eq_compat. 2: {
    intros j Hj.
    apply (In_nth _ _ 0) in Hj.
    destruct Hj as (v & Hv & Hvj).
    replace (ff_app _ (ff_app _ j)) with j. 2: {
      symmetry.
      apply permut_permut_isort; [ easy | ].
      rewrite <- Hvj.
      now apply permut_list_ub.
    }
    easy.
  }
  cbn - [ "<?" ].
  easy.
}
cbn - [ "<?" ].
rewrite (rngl_product_list_permut _ _ Nat.eqb_eq) with
    (l2 := seq 0 (length p)); cycle 1. {
  easy.
} {
  now apply permut_list_permutation_iff.
}
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite (rngl_product_change_list Nat.eqb_eq) with
    (lb := seq 0 (length p)); cycle 1. {
    easy.
  } {
    now apply permut_list_permutation_iff.
  }
  easy.
}
cbn - [ "<?" ].
rewrite product_product_if_permut; try easy; cycle 1. {
  now left.
} {
  now apply (isort_rank_is_permut _ (length p)).
} {
  intros.
  unfold abs_diff.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec i j) as [Hij| Hij]. {
    destruct (lt_dec j i) as [Hji| Hji]; [ flia Hij Hji | easy ].
  } {
    destruct (lt_dec j i) as [Hji| Hji]; [ easy | ].
    now replace i with j by flia Hij Hji.
  }
} {
  intros * Hi Hj Hij H.
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  unfold abs_diff in H.
  rewrite if_ltb_lt_dec in H.
  destruct (lt_dec i j) as [Hlij| Hlij]; flia Hij Hlij H.
}
rewrite rngl_product_seq_product; [ | flia Hn1 ].
rewrite Nat.add_0_l.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_seq_product; [ | flia Hn1 ].
  rewrite Nat.add_0_l.
  easy.
}
cbn - [ "<?" ].
unfold abs_diff.
apply rngl_product_eq_compat.
intros i Hi.
apply rngl_product_eq_compat.
intros j Hj.
do 3 rewrite if_ltb_lt_dec.
now destruct (lt_dec i j).
Qed.

Theorem ε'_ε_1 : in_charac_0_field →
  ∀ p,
  (∏ (i = 0, length p - 1),
   ∏ (j = 0, length p - 1),
   if i <? j then
      rngl_of_nat (abs_diff (ff_app p j) (ff_app p i)) / rngl_of_nat (j - i)
   else 1) = 1%F
  → ε' p = ε p.
Proof.
intros Hif * Hij1.
destruct Hif as (Hic & Hop & Hin & H10 & Hit & _ & Hch).
unfold ε', rngl_sub_nat.
do 2 rewrite rngl_product_product_if.
destruct (le_dec (length p) 1) as [Hn1| Hn1]. {
  unfold ε.
  rewrite rngl_product_product_if.
  replace (length p - 1) with 0 by flia Hn1.
  do 3 rewrite rngl_product_only_one.
  rewrite rngl_product_empty; [ | now cbn ].
  rewrite rngl_product_empty; [ | now cbn ].
  rewrite rngl_product_empty; [ | now cbn ].
  apply rngl_div_1_r; [ now left | easy ].
}
apply Nat.nle_gt in Hn1.
rewrite <- rngl_product_div_distr; try easy; [ | now left | ]. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite rngl_of_nat_sub; [ | easy ].
    rewrite if_ltb_lt_dec.
    destruct (lt_dec i j) as [Hij| Hij]; [ | flia Hj Hij ].
    easy.
  }
  cbn.
  destruct (Nat.eq_dec i (length p - 1)) as [Hein| Hein]. {
    subst i.
    rewrite rngl_product_empty; [ now apply rngl_1_neq_0 | flia ].
  }
  rewrite (rngl_product_shift (i + 1)); [ | flia Hi Hein ].
  rewrite Nat.sub_diag.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    replace (i + 1 + j - i) with (S j) by flia.
    easy.
  }
  cbn - [ rngl_of_nat ].
  erewrite <- rngl_product_succ_succ.
  replace (S (length p - 1 - (i + 1))) with (length p - S i) by flia Hi Hein.
  rewrite rngl_product_rngl_of_nat; [ | now left ].
  intros H.
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  now apply fact_neq_0 in H.
}
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite <- rngl_product_div_distr; try easy; [ now left | ].
  intros j Hj.
  intros H.
  apply -> rngl_sub_move_0_r in H; [ | easy ].
  apply rngl_of_nat_inj in H; [ | now left | easy ].
  flia Hj H.
}
cbn.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite rngl_sub_is_mul_sign_abs; [ | easy ].
    rewrite rngl_sub_is_mul_sign_abs; [ | easy ].
    replace (sign_diff j i) with 1%F. 2: {
      unfold sign_diff.
      remember (j ?= i) as b eqn:Hb; symmetry in Hb.
      destruct b; [ | | easy ]. {
        apply Nat.compare_eq in Hb; subst j; flia Hj.
      } {
        apply nat_compare_lt in Hb; flia Hj Hb.
      }
    }
    rewrite rngl_mul_1_l.
    replace (rngl_of_nat (abs_diff j i)) with (rngl_of_nat (j - i)). 2: {
      unfold abs_diff.
      rewrite if_ltb_lt_dec.
      destruct (lt_dec i j) as [H| H]; [ easy | flia Hj H ].
    }
    easy.
  }
  easy.
}
cbn.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    unfold rngl_div.
    rewrite Hin.
    rewrite <- rngl_mul_assoc.
    easy.
  }
  cbn.
  rewrite rngl_product_mul_distr; [ | easy ].
  easy.
}
cbn.
rewrite rngl_product_mul_distr; [ | easy ].
rewrite <- rngl_product_product_if.
rewrite fold_ε.
rewrite <- rngl_product_product_if.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    now rewrite fold_rngl_div.
  }
  easy.
}
cbn - [ "<?" ].
rewrite Hij1.
apply rngl_mul_1_r.
Qed.

Theorem ε'_ε : in_charac_0_field →
  ∀ p, is_permut_list p → ε' p = ε p.
Proof.
intros Hif * Hp.
apply ε'_ε_1; [ easy | ].
now rewrite rngl_product_product_abs_diff_div_diff.
Qed.

Theorem transposition_is_permut : ∀ p q n,
  p < n → q < n → is_permut n (map (transposition p q) (seq 0 n)).
Proof.
intros * Hp Hq.
split. {
  split. {
    intros i Hi.
    unfold transposition.
    rewrite map_length, seq_length.
    apply in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj).
    apply in_seq in Hj.
    rewrite <- Hji.
    now apply transposition_lt.
  } {
    apply nat_NoDup.
    rewrite List_map_seq_length.
    intros i j Hi Hj Hs.
    unfold transposition in Hs.
    unfold ff_app in Hs.
    rewrite (List_map_nth' 0) in Hs; [ | now rewrite seq_length ].
    rewrite (List_map_nth' 0) in Hs; [ | now rewrite seq_length ].
    rewrite seq_nth in Hs; [ | easy ].
    rewrite seq_nth in Hs; [ | easy ].
    do 4 rewrite if_eqb_eq_dec in Hs.
    do 2 rewrite Nat.add_0_l in Hs.
    destruct (Nat.eq_dec i p) as [Hip| Hip]. {
      destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ congruence | ].
      destruct (Nat.eq_dec j q) as [Hjq| Hjq]; congruence.
    }
    destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
      destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ congruence | ].
      destruct (Nat.eq_dec j q) as [Hjq| Hjq]; congruence.
    }
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ easy | ].
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ easy | ].
    easy.
  }
}
now rewrite map_length, seq_length.
Qed.

Theorem transposition_signature_lt :
  rngl_is_comm = true →
  rngl_has_opp = true →
  ∀ n p q,
  p < q
  → q < n
  → ε (map (transposition p q) (seq 0 n)) = (-1)%F.
Proof.
intros Hic Hop * Hpq Hq.
unfold ε; cbn - [ "<?" ].
rewrite List_map_seq_length.
unfold sign_diff.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    unfold transposition, ff_app.
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hj Hq ].
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hi Hq ].
    rewrite seq_nth; [ | flia Hj Hq ].
    rewrite seq_nth; [ | flia Hi Hq ].
    do 2 rewrite Nat.add_0_l.
    do 2 rewrite fold_transposition.
    easy.
  }
  easy.
}
cbn - [ "<?" ].
rewrite (rngl_product_split3 p); [ | flia Hpq Hq ].
cbn - [ "<?" ].
assert (Hp : p < n) by now transitivity q.
rewrite all_1_rngl_product_1. 2: {
  intros i Hi.
  apply all_1_rngl_product_1.
  intros j Hj.
  unfold transposition.
  rewrite if_ltb_lt_dec.
  do 4 rewrite if_eqb_eq_dec.
  destruct (lt_dec (i - 1) j) as [Hij| Hij]; [ | easy ].
  destruct (Nat.eq_dec (i - 1) p) as [H| H]; [ flia Hi H | clear H ].
  destruct (Nat.eq_dec (i - 1) q) as [H| H]; [ flia Hi Hpq H | clear H ].
  destruct (Nat.eq_dec j p) as [Hjp| Hjp]. {
    remember (q ?= i - 1) as b eqn:Hb; symmetry in Hb.
    destruct b; [ | | easy ]. {
      apply Nat.compare_eq in Hb; flia Hij Hjp Hb Hpq.
    } {
      apply nat_compare_lt in Hb; flia Hij Hjp Hb Hpq.
    }
  }
  destruct (Nat.eq_dec j q) as [Hjq| Hjq]. {
    remember (p ?= i - 1) as b eqn:Hb; symmetry in Hb.
    destruct b; [ | | easy ]. {
      apply Nat.compare_eq in Hb; flia Hi Hb.
    } {
      apply nat_compare_lt in Hb; flia Hi Hb.
    }
  }
  remember (j ?= i - 1) as b eqn:Hb; symmetry in Hb.
  destruct b; [ | | easy ]. {
    apply Nat.compare_eq in Hb; flia Hij Hb.
  } {
    apply nat_compare_lt in Hb; flia Hij Hb.
  }
}
rewrite rngl_mul_1_l.
rewrite transposition_1.
rewrite (rngl_product_split3 p); [ | flia Hpq Hq ].
unfold transposition at 2.
rewrite Nat.eqb_refl.
rewrite Nat.ltb_irrefl.
rewrite rngl_mul_1_r.
rewrite all_1_rngl_product_1. 2: {
  intros i Hi.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec p (i - 1)) as [H| H]; [ flia Hi H | easy ].
}
rewrite rngl_mul_1_l.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec p i) as [H| H]; [ clear H | flia Hi H ].
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec i p) as [H| H]; [ flia Hi H | clear H ].
  easy.
}
cbn - [ "<?" ].
rewrite <- rngl_product_mul_distr; [ | easy ].
rewrite (rngl_product_split3 q); [ | flia Hpq Hq ].
rewrite transposition_2.
destruct (Nat.eq_dec q q) as [H| H]; [ clear H | easy ].
replace (p ?= q) with Lt by now symmetry; apply nat_compare_lt.
destruct (lt_dec q p) as [H| H]; [ flia Hpq H | clear H ].
rewrite <- rngl_mul_assoc.
rewrite rngl_mul_comm; [ | easy ].
rewrite (rngl_product_split3 q); [ | flia Hpq Hq ].
rewrite if_ltb_lt_dec.
destruct (lt_dec q q) as [H| H]; [ flia H | clear H ].
rewrite rngl_mul_1_r.
rewrite all_1_rngl_product_1. 2: {
  intros i Hi.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec q (i - 1)) as [H| H]; [ flia Hi H | easy ].
}
rewrite rngl_mul_1_l.
do 2 rewrite <- rngl_mul_assoc.
rewrite rngl_mul_comm; [ | easy ].
rewrite rngl_mul_assoc.
rewrite <- rngl_product_mul_distr; [ | easy ].
rewrite all_1_rngl_product_1. 2: {
  intros i Hi.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec q i) as [H| H]; [ clear H | flia Hi H ].
  rewrite rngl_mul_assoc.
  rewrite transposition_out; [ | flia Hpq Hi | flia Hi ].
  replace (i ?= p) with Gt by now symmetry; apply nat_compare_gt; flia Hi Hpq.
  rewrite rngl_mul_1_l.
  destruct (Nat.eq_dec i q) as [H| H]; [ flia Hi H | clear H ].
  replace (i ?= q) with Gt by now symmetry; apply nat_compare_gt; flia Hi.
  rewrite rngl_mul_1_l.
  apply all_1_rngl_product_1.
  intros j Hj.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
  rewrite transposition_out; [ | flia Hpq Hi Hij | flia Hi Hij ].
  replace (j ?= i) with Gt by now symmetry; apply nat_compare_gt; flia Hij.
  easy.
}
rewrite rngl_mul_1_l.
rewrite all_1_rngl_product_1; [ apply rngl_mul_1_l | ].
intros i Hi.
rewrite transposition_out; [ | flia Hi | flia Hi ].
destruct (Nat.eq_dec (i - 1) q) as [H| H]; [ flia Hi H | clear H ].
replace (i - 1 ?= q) with Lt by now symmetry; apply nat_compare_lt; flia Hi.
rewrite (rngl_product_split3 p); [ | flia Hp ].
rewrite transposition_1.
rewrite if_ltb_lt_dec.
destruct (lt_dec (i - 1) p) as [H| H]; [ flia Hi H | clear H ].
rewrite rngl_mul_1_r.
rewrite all_1_rngl_product_1. 2: {
  intros j Hj.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec (i - 1) (j - 1)) as [H| H]; [ flia Hi Hj H | easy ].
}
rewrite rngl_mul_1_l.
rewrite (rngl_product_split3 q); [ | flia Hpq Hq ].
rewrite if_ltb_lt_dec.
destruct (lt_dec (i - 1) q) as [H| H]; [ clear H | flia Hi H ].
rewrite transposition_2.
replace (p ?= i - 1) with Lt by now symmetry; apply nat_compare_lt; flia Hi.
rewrite rngl_mul_mul_swap; [ | easy ].
rewrite rngl_mul_comm; [ | easy ].
rewrite <- rngl_mul_assoc.
rewrite rngl_squ_opp_1; [ | easy ].
rewrite rngl_mul_1_r.
rewrite (all_1_rngl_product_1 (q + 1)). 2: {
  intros j Hj.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec (i - 1) j) as [H| H]; [ clear H | flia Hi Hj H ].
  rewrite transposition_out; [ | flia Hpq Hj | flia Hj ].
  replace (j ?= i - 1) with Gt. 2: {
    symmetry; apply nat_compare_gt; flia Hi Hj.
  }
  easy.
}
rewrite rngl_mul_1_r.
apply all_1_rngl_product_1.
intros j Hj.
rewrite transposition_out; [ | flia Hj | flia Hj ].
rewrite if_ltb_lt_dec.
destruct (lt_dec (i - 1) (j - 1)) as [Hij| Hij]; [ | easy ].
apply nat_compare_gt in Hij.
now rewrite Hij.
Qed.

Theorem transposition_signature :
  rngl_is_comm = true →
  rngl_has_opp = true →
  ∀ n p q,
  p ≠ q
  → p < n
  → q < n
  → ε (map (transposition p q) (seq 0 n)) = (-1)%F.
Proof.
intros Hic Hop * Hpq Hp Hq.
destruct (lt_dec p q) as [Hpq'| Hpq']. {
  now apply transposition_signature_lt.
}
apply Nat.nlt_ge in Hpq'.
assert (H : q < p) by flia Hpq Hpq'.
rewrite <- transposition_signature_lt with (p := q) (q := p) (n := n); try easy.
f_equal.
apply map_ext_in.
intros i Hi.
apply transposition_comm.
Qed.

Theorem comp_is_permut_list : ∀ n σ₁ σ₂,
  is_permut n σ₁
  → is_permut n σ₂
  → is_permut_list (σ₁ ° σ₂).
Proof.
intros * (Hp11, Hp12) (Hp21, Hp22).
split. {
  intros i Hi.
  unfold comp_list in Hi |-*.
  rewrite map_length.
  apply in_map_iff in Hi.
  destruct Hi as (j & Hji & Hj).
  subst i.
  rewrite Hp22, <- Hp12.
  apply permut_list_ub; [ easy | ].
  apply Hp21 in Hj.
  congruence.
} {
  unfold comp_list.
  apply nat_NoDup.
  rewrite map_length.
  intros i j Hi Hj.
  unfold ff_app.
  rewrite (List_map_nth' 0); [ | easy ].
  rewrite (List_map_nth' 0); [ | easy ].
  intros Hij.
  destruct Hp11 as (_, Hp11).
  apply (NoDup_nat _ Hp11) in Hij; cycle 1. {
    rewrite Hp12, <- Hp22.
    now apply Hp21, nth_In.
  } {
    rewrite Hp12, <- Hp22.
    now apply Hp21, nth_In.
  }
  destruct Hp21 as (_, Hp21).
  now apply (NoDup_nat _ Hp21) in Hij.
}
Qed.

Arguments comp_is_permut_list n%nat [σ₁ σ₂]%list_scope.

Theorem comp_is_permut : ∀ n σ₁ σ₂,
  is_permut n σ₁
  → is_permut n σ₂
  → is_permut n (σ₁ ° σ₂).
Proof.
intros * Hp1 Hp2.
split; [ now apply (comp_is_permut_list n) | ].
unfold "°".
rewrite map_length.
now destruct Hp2.
Qed.

(* ε (σ₁ ° σ₂) = ε σ₁ * ε σ₂ *)

Theorem signature_comp_fun_expand_1 : in_charac_0_field →
  ∀ n f g,
  is_permut n f
  → is_permut n g
  → (∏ (i = 0, n - 1),
        (∏ (j = 0, n - 1),
         if i <? j then
           rngl_sub_nat (ff_app f (ff_app g j)) (ff_app f (ff_app g i))
         else 1) /
      ∏ (i = 0, n - 1),
        (∏ (j = 0, n - 1),
         if i <? j then rngl_sub_nat (ff_app g j) (ff_app g i)
         else 1))%F =
    (∏ (i = 0, n - 1),
       (∏ (j = 0, n - 1),
        if i <? j then rngl_sub_nat (ff_app f j) (ff_app f i) else 1) /
      ∏ (i = 0, n - 1),
       (∏ (j = 0, n - 1),
        if i <? j then rngl_sub_nat j i else 1))%F
  → ε (f ° g) = (ε f * ε g)%F.
Proof.
intros Hif * (Hfp, Hfn) (Hgp, Hgn) Hs.
rewrite <- ε'_ε; [ | easy | now apply (comp_is_permut_list n) ].
rewrite <- ε'_ε; [ | easy | easy ].
rewrite <- ε'_ε; [ | easy | easy ].
unfold ε', comp_list; cbn - [ "<?" ].
rewrite map_length, Hfn, Hgn.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  do 8 rewrite rngl_product_only_one; cbn.
  symmetry.
  rewrite rngl_div_1_r; [ | now destruct Hif; left | now destruct Hif ].
  apply rngl_mul_1_l.
}
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    unfold ff_app.
    rewrite (List_map_nth' 0); [ | flia Hj Hgn Hnz ].
    rewrite (List_map_nth' 0); [ | flia Hi Hgn Hnz ].
    easy.
  }
  easy.
}
rewrite <- Hs; symmetry.
destruct Hif as (Hop & Hic & Hin & H10 & Hit & Hde & Hch).
apply rngl_div_mul_div; [ easy | ].
intros Hij.
apply rngl_product_integral in Hij; [ | now left | easy | easy ].
destruct Hij as (i & Hi & Hij).
apply rngl_product_integral in Hij; [ | now left | easy | easy ].
destruct Hij as (j & Hj & Hij).
rewrite if_ltb_lt_dec in Hij.
destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 ].
apply -> rngl_sub_move_0_r in Hij; [ | easy ].
apply rngl_of_nat_inj in Hij; [ | now left | easy ].
destruct Hgp as (_, Hgp).
apply (NoDup_nat _ Hgp) in Hij; [ | flia Hj Hgn Hnz | flia Hi Hgn Hnz ].
flia Hi Hj Hlij Hij.
Qed.

Arguments signature_comp_fun_expand_1 _ n%nat [f g]%list.

Theorem signature_comp_fun_expand_2_1 :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_is_comm = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f g,
  is_permut n g
  → (∏ (i = 0, n - 1),
      (∏ (j = 0, n - 1),
       if i <? j then
         rngl_sub_nat (ff_app f (ff_app g j)) (ff_app f (ff_app g i))
       else 1) /
     ∏ (i = 0, n - 1),
      (∏ (j = 0, n - 1),
       if i <? j then rngl_sub_nat (ff_app g j) (ff_app g i)
       else 1))%F =
    (∏ (i = 0, n - 1),
      (∏ (j = 0, n - 1),
       (if i <? j then
         (rngl_of_nat (ff_app f (ff_app g j)) -
          rngl_of_nat (ff_app f (ff_app g i))) /
         (rngl_of_nat (ff_app g j) - rngl_of_nat (ff_app g i))
       else 1)))%F.
Proof.
intros Hop Hin Hic H10 Hit Hch * (Hp2, Hn).
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  do 6 rewrite rngl_product_only_one; cbn.
  apply rngl_div_1_r; [ now left | easy ].
}
unfold rngl_div; rewrite Hin.
rewrite rngl_inv_product_comm; [ | | easy | easy | easy | easy | ]; cycle 1. {
  now left.
} {
  intros i Hi Hij.
  apply rngl_product_integral in Hij; [ | now left | easy | easy ].
  destruct Hij as (j & Hj & Hij).
  rewrite <- Hn in Hi, Hj.
  rewrite if_ltb_lt_dec in Hij.
  destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 in Hij ].
  apply -> rngl_sub_move_0_r in Hij; [ | easy ].
  apply rngl_of_nat_inj in Hij; [ | now left | easy ].
  rewrite <- Hn in Hnz.
  destruct Hp2 as (_, Hp2).
  apply (NoDup_nat _ Hp2) in Hij; [ | flia Hj Hnz | flia Hi Hnz ].
  flia Hi Hj Hlij Hij.
}
erewrite <- rngl_product_mul_distr; [ | easy ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_inv_product_comm;
      [ | now left | easy | easy | easy | easy | ]. 2: {
    intros j Hj Hij.
    rewrite <- Hn in Hi, Hj.
    rewrite if_ltb_lt_dec in Hij.
    destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 in Hij ].
    apply -> rngl_sub_move_0_r in Hij; [ | easy ].
    apply rngl_of_nat_inj in Hij; [ | now left | easy ].
    rewrite <- Hn in Hnz.
    destruct Hp2 as (_, Hp2).
    apply (NoDup_nat _ Hp2) in Hij; [ | flia Hj Hnz | flia Hi Hnz ].
    flia Hi Hj Hlij Hij.
  }
  erewrite <- rngl_product_mul_distr; [ | easy ].
  easy.
}
cbn - [ "<?" ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    move j before i.
    rewrite rngl_inv_if_then_else_distr.
    rewrite rngl_mul_if_then_else_distr.
    rewrite fold_rngl_div; [ | easy ].
    rewrite rngl_inv_1; [ | easy | easy ].
    rewrite rngl_mul_1_l.
    easy.
  }
  easy.
}
cbn - [ "<?" ].
unfold rngl_div; rewrite Hin.
easy.
Qed.

Theorem signature_comp_fun_expand_2_2 :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_is_comm = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f,
  (∏ (i = 0, n - 1),
   (∏ (j = 0, n - 1),
    if i <? j then rngl_sub_nat (f j) (f i) else 1) /
   ∏ (i = 0, n - 1),
   (∏ (j = 0, n - 1),
    if i <? j then rngl_sub_nat j i else 1))%F =
  (∏ (i = 0, n - 1),
   (∏ (j = 0, n - 1),
    (if i <? j then
      (rngl_of_nat (f j) - rngl_of_nat (f i)) / rngl_of_nat (j - i)
     else 1)))%F.
Proof.
intros Hop Hin Hic H10 Hit Hch *.
unfold rngl_div; rewrite Hin.
rewrite rngl_inv_product_comm; [ | now left | easy | easy | easy | easy | ]. 2: {
  intros i Hi Hij.
  apply rngl_product_integral in Hij; [ | now left | easy | easy ].
  destruct Hij as (j & Hj & Hij).
  rewrite if_ltb_lt_dec in Hij.
  destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 in Hij ].
  apply -> rngl_sub_move_0_r in Hij; [ | easy ].
  apply rngl_of_nat_inj in Hij; [ | now left | easy ].
  flia Hlij Hij.
}
erewrite <- rngl_product_mul_distr; [ | easy ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_inv_product_comm;
      [ | now left | easy | easy | easy | easy | ]. 2: {
    intros j Hj Hij.
    rewrite if_ltb_lt_dec in Hij.
    destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 in Hij ].
    apply -> rngl_sub_move_0_r in Hij; [ | easy ].
    apply rngl_of_nat_inj in Hij; [ | now left | easy ].
    flia Hlij Hij.
  }
  erewrite <- rngl_product_mul_distr; [ | easy ].
  easy.
}
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    move j before i.
    rewrite rngl_inv_if_then_else_distr.
    rewrite rngl_mul_if_then_else_distr.
    rewrite fold_rngl_div; [ | easy ].
    rewrite rngl_inv_1; [ | easy | easy ].
    rewrite rngl_mul_1_l.
    easy.
  }
  easy.
}
unfold rngl_div; rewrite Hin.
apply rngl_product_eq_compat.
intros i Hi.
apply rngl_product_eq_compat.
intros j Hj.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
f_equal; f_equal.
unfold rngl_sub_nat.
rewrite rngl_of_nat_sub; [ | easy ].
now apply Nat.ltb_lt in Hij; rewrite Hij.
Qed.

Theorem signature_comp_fun_changement_of_variable :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_is_comm = true →
  rngl_has_eqb = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f g,
  is_permut n f
  → is_permut n g
  → (∏ (i = 0, n - 1),
     (∏ (j = 0, n - 1),
      (if i <? j then
         (rngl_of_nat (ff_app f (ff_app g j)) -
          rngl_of_nat (ff_app f (ff_app g i))) /
         (rngl_of_nat (ff_app g j) - rngl_of_nat (ff_app g i))
       else 1)))%F =
    (∏ (i = 0, n - 1),
     (∏ (j = 0, n - 1),
      (if i <? j then
         (rngl_of_nat (ff_app f j) - rngl_of_nat (ff_app f i)) /
         rngl_of_nat (j - i)
       else 1)))%F.
Proof.
intros Hop Hin Hic Heq H10 Hit Hch * (Hp1, Hn1) (Hp2, Hn2).
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now move Hnz at top; subst n | ].
rewrite rngl_product_change_var with
    (g := ff_app (isort_rank Nat.leb g)) (h := ff_app g). 2: {
  intros i Hi.
  apply permut_isort_permut; [ easy | rewrite Hn2; flia Hi Hnz ].
}
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1, Nat.sub_0_r.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_change_var with
      (g := ff_app (isort_rank Nat.leb g)) (h := ff_app g). 2: {
    intros j Hj.
    apply permut_isort_permut; [ easy | rewrite Hn2; flia Hj Hnz ].
  }
  rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
  rewrite Nat_sub_succ_1, Nat.sub_0_r.
  erewrite rngl_product_list_eq_compat. 2: {
    intros j Hj.
    rewrite permut_permut_isort; [ | easy | ]. 2: {
      apply in_map_iff in Hj.
      destruct Hj as (k & Hk & Hkn).
      apply in_seq in Hkn.
      rewrite <- Hk.
      apply Hp2, nth_In.
      now rewrite Hn2.
    }
    rewrite permut_permut_isort; [ | easy | ]. 2: {
      apply in_map_iff in Hi.
      destruct Hi as (k & Hk & Hkn).
      apply in_seq in Hkn.
      rewrite <- Hk.
      apply Hp2, nth_In.
      now rewrite Hn2.
    }
    easy.
  }
  easy.
}
cbn - [ "<?" ].
erewrite rngl_product_list_eq_compat. 2: {
  intros j Hj.
  rewrite <- Hn2 at 1.
  rewrite <- List_map_ff_app_seq.
  erewrite (rngl_product_change_list Nat.eqb_eq); [ | easy | ]. 2: {
    now apply permut_list_permutation_iff.
  }
  easy.
}
cbn - [ "<?" ].
erewrite (rngl_product_change_list Nat.eqb_eq); [ | easy | ]. 2: {
  rewrite <- Hn2 at 1.
  rewrite <- List_map_ff_app_seq.
  now apply permut_list_permutation_iff.
}
symmetry.
unfold iter_seq.
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1, Nat.sub_0_r.
symmetry.
rewrite Hn2.
rewrite product_product_if_permut; try easy. {
  apply rngl_product_list_eq_compat.
  intros i Hi.
  apply rngl_product_list_eq_compat.
  intros j Hj.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
  f_equal.
  rewrite rngl_of_nat_sub; [ | easy ].
  now apply Nat.ltb_lt in Hij; rewrite Hij.
} {
  now left.
} {
  now apply (isort_rank_is_permut _ n).
} {
  intros i j.
  destruct (Nat.eq_dec i j) as [Hij| Hij]; [ now subst j | ].
  rewrite <- rngl_opp_sub_distr; [ | easy ].
  unfold rngl_div.
  rewrite Hin.
  rewrite rngl_mul_opp_l; [ | easy ].
  rewrite <- rngl_mul_opp_r; [ | easy ].
  f_equal.
  rewrite rngl_opp_inv; [ | easy | easy | easy | ]. 2: {
    intros H.
    apply -> rngl_sub_move_0_r in H; [ | easy ].
    apply Hij; symmetry.
    apply rngl_of_nat_inj in H; [ easy | now left | easy ].
  }
  now rewrite rngl_opp_sub_distr.
} {
  intros * Hi Hj Hij.
  unfold rngl_div.
  rewrite Hin.
  intros H.
  apply rngl_integral in H; [ | now left | now rewrite Hit ].
  destruct H as [H| H]. {
    apply -> rngl_sub_move_0_r in H; [ | easy ].
    apply rngl_of_nat_inj in H; [ | now left | easy ].
    apply Hij; symmetry.
    rewrite <- Hn1 in Hi, Hj.
    destruct Hp1 as (_, Hp1).
    now apply (NoDup_nat _ Hp1) in H.
  } {
    revert H.
    apply rngl_inv_neq_0; [ now left | easy | easy | ].
    intros H.
    apply -> rngl_sub_move_0_r in H; [ | easy ].
    apply rngl_of_nat_inj in H; [ | now left | easy ].
    now apply Hij; symmetry.
  }
}
Qed.

Theorem sign_diff_id : ∀ a, sign_diff a a = 0%F.
Proof.
intros.
unfold sign_diff.
now rewrite Nat.compare_refl.
Qed.

Theorem sign_diff_swap :
  rngl_has_opp = true →
  ∀ u v, sign_diff u v = (- sign_diff v u)%F.
Proof.
intros Hop u v.
unfold sign_diff.
remember (u ?= v) as b1 eqn:Hb1; symmetry in Hb1.
remember (v ?= u) as b2 eqn:Hb2; symmetry in Hb2.
destruct b1. {
  apply Nat.compare_eq_iff in Hb1; subst v.
  rewrite Nat.compare_refl in Hb2; subst b2.
  now symmetry; apply rngl_opp_0.
} {
  apply Nat.compare_lt_iff in Hb1.
  destruct b2; [ | | easy ]. {
    apply Nat.compare_eq_iff in Hb2; subst v.
    now apply Nat.lt_irrefl in Hb1.
  } {
    apply Nat.compare_lt_iff, Nat.lt_le_incl in Hb2.
    now apply Nat.nlt_ge in Hb2.
  }
} {
  rewrite <- (rngl_opp_involutive Hop 1%F) at 1.
  apply Nat.compare_gt_iff in Hb1.
  destruct b2; [ | easy | ]. {
    apply Nat.compare_eq_iff in Hb2; subst v.
    now apply Nat.lt_irrefl in Hb1.
  } {
    apply Nat.compare_gt_iff, Nat.lt_le_incl in Hb2.
    now apply Nat.nlt_ge in Hb2.
  }
}
Qed.

Theorem butn_is_permut : ∀ n i l,
  is_permut (S n) l
  → n = ff_app l i
  → i < length l
  → is_permut n (butn i l).
Proof.
intros * Hp Hni Hil.
split. {
  split. {
    intros j Hj.
    rewrite butn_length.
    destruct Hp as (Hp, Hl).
    apply Nat.ltb_lt in Hil; rewrite Hil.
    apply Nat.ltb_lt in Hil.
    rewrite Hl, Nat_sub_succ_1.
    destruct Hp as (Hpl, Hpi).
    specialize (Hpl j) as Hjl.
    assert (H : j ∈ l) by now apply in_butn in Hj.
    specialize (Hjl H); clear H.
    rewrite Hl in Hjl.
    destruct (Nat.eq_dec j n) as [H| H]; [ | flia H Hjl ].
    subst j; clear Hjl; exfalso.
    assert (Hnni : n ≠ i). {
      intros H; move H at top; subst i.
      apply (In_nth _ _ 0) in Hj.
      rewrite butn_length, Hl in Hj.
      replace (n <? S n) with true in Hj by now symmetry; apply Nat.ltb_lt.
      rewrite Nat_sub_succ_1 in Hj.
      destruct Hj as (j & Hjn & Hnj); symmetry in Hnj.
      rewrite nth_butn in Hnj.
      apply Nat.leb_gt in Hjn.
      rewrite Hjn, Nat.add_0_r in Hnj.
      apply Nat.leb_gt in Hjn.
      specialize (NoDup_nat _ Hpi j n) as H2.
      assert (H : j < length l) by now rewrite Hl; flia Hjn.
      specialize (H2 H Hil); clear H.
      assert (H : ff_app l j = ff_app l n) by now rewrite <- Hni.
      specialize (H2 H).
      now rewrite H2 in Hjn; apply Nat.lt_irrefl in Hjn.
    }
    unfold butn in Hj.
    apply in_app_or in Hj.
    destruct Hj as [Hini| Hini]. {
      apply (In_nth _ _ 0) in Hini.
      destruct Hini as (j & Hjl & Hjn).
      rewrite firstn_length, min_l in Hjl; [ | flia Hil ].
      specialize (NoDup_nat _ Hpi i j Hil) as H2.
      assert (H : j < length l) by flia Hjl Hil.
      specialize (H2 H); clear H.
      rewrite <- Hni in H2.
      rewrite List_nth_firstn in Hjn; [ | easy ].
      symmetry in Hjn.
      specialize (H2 Hjn).
      rewrite <- H2 in Hjl.
      now apply Nat.lt_irrefl in Hjl.
    } {
      apply (In_nth _ _ 0) in Hini.
      destruct Hini as (j & Hjl & Hjn).
      rewrite skipn_length in Hjl.
      rewrite List_nth_skipn in Hjn.
      specialize (NoDup_nat _ Hpi i (j + S i) Hil) as H2.
      assert (H : j + S i < length l) by flia Hjl.
      specialize (H2 H); clear H.
      rewrite <- Hni in H2.
      unfold ff_app in H2.
      rewrite Hjn in H2.
      specialize (H2 eq_refl).
      flia H2.
    }
  } {
    apply nat_NoDup.
    rewrite butn_length.
    apply Nat.ltb_lt in Hil; rewrite Hil.
    apply Nat.ltb_lt in Hil.
    destruct Hp as (Hpp, Hpl).
    rewrite Hpl, Nat_sub_succ_1.
    intros j k Hj Hk Hjk.
    destruct Hpp as (Hp, Hpi).
    unfold ff_app in Hjk.
    do 2 rewrite nth_butn in Hjk.
    apply (NoDup_nat _ Hpi) in Hjk; cycle 1. {
      rewrite Hpl, <- Nat.add_1_r.
      apply Nat.add_lt_le_mono; [ easy | ].
      apply Nat_b2n_upper_bound.
    } {
      rewrite Hpl, <- Nat.add_1_r.
      apply Nat.add_lt_le_mono; [ easy | ].
      apply Nat_b2n_upper_bound.
    }
    unfold Nat.b2n in Hjk.
    do 2 rewrite if_leb_le_dec in Hjk.
    destruct (le_dec i j) as [Hij| Hij].  {
      destruct (le_dec i k) as [Hik| Hik]; [ flia Hjk | ].
      exfalso; flia Hik Hij Hjk.
    } {
      destruct (le_dec i k) as [Hik| Hik]; [ | flia Hjk ].
      exfalso; flia Hik Hij Hjk.
    }
  }
} {
  rewrite butn_length.
  apply Nat.ltb_lt in Hil.
  destruct Hp as (Hpp, Hpl).
  now rewrite Hil, Hpl, Nat_sub_succ_1.
}
Qed.

Theorem permut_without_highest : ∀ n l,
  is_permut (S n) l
  → ∃ i, i < length l ∧ nth i l 0 = n ∧ is_permut n (butn i l).
Proof.
intros * Hl.
exists (ff_app (isort_rank Nat.leb l) n).
split. {
  rewrite <- (isort_rank_length Nat.leb).
  destruct Hl as (Hp, Hl).
  specialize (isort_rank_is_permut Nat.leb _ Hl) as Hil.
  apply Hil, nth_In.
  rewrite isort_rank_length.
  now rewrite Hl.
}
split. {
  rewrite fold_ff_app.
  destruct Hl as (Hp, Hl).
  apply permut_permut_isort; [ easy | now rewrite Hl ].
}
apply butn_is_permut; [ easy | | ]. {
  destruct Hl as (Hp, Hl).
  rewrite permut_permut_isort; [ easy | easy | now rewrite Hl ].
} {
  specialize (isort_rank_is_permut_list Nat.leb l) as H1.
  destruct Hl as (H2, H3).
  destruct H1 as (H4, H5).
  rewrite isort_rank_length in H4.
  apply H4, nth_In.
  now rewrite isort_rank_length, H3.
}
Qed.

Theorem sign_diff_mul :
  rngl_has_opp = true →
   ∀ a b c d,
  (sign_diff a b * sign_diff c d)%F =
  sign_diff (a * c + b * d) (a * d + b * c).
Proof.
intros Hop *.
unfold sign_diff.
remember (a ?= b) as b1 eqn:Hb1; symmetry in Hb1.
remember (c ?= d) as b2 eqn:Hb2; symmetry in Hb2.
move b2 before b1.
destruct b1. {
  rewrite rngl_mul_0_l; [ | now left ].
  apply Nat.compare_eq_iff in Hb1; subst b.
  now rewrite Nat.add_comm, Nat.compare_refl.
} {
  destruct b2. {
    rewrite rngl_mul_0_r; [ | now left ].
    apply Nat.compare_eq_iff in Hb2; subst d.
    now rewrite Nat.compare_refl.
  } {
    rewrite rngl_squ_opp_1; [ | easy ].
    apply Nat.compare_lt_iff in Hb1, Hb2.
    specialize (Nat_lt_lt_sum_mul_lt_sum_mul Hb1 Hb2) as H1.
    apply Nat.compare_gt_iff in H1.
    now rewrite H1.
  } {
    rewrite rngl_mul_1_r.
    apply Nat.compare_lt_iff in Hb1.
    apply Nat.compare_gt_iff in Hb2.
    specialize (Nat_lt_lt_sum_mul_lt_sum_mul Hb1 Hb2) as H1.
    apply Nat.compare_lt_iff in H1.
    now rewrite H1.
  }
} {
  destruct b2. {
    rewrite rngl_mul_0_r; [ | now left ].
    apply Nat.compare_eq_iff in Hb2; subst d.
    now rewrite Nat.compare_refl.
  } {
    rewrite rngl_mul_1_l.
    apply Nat.compare_gt_iff in Hb1.
    apply Nat.compare_lt_iff in Hb2.
    specialize (Nat_lt_lt_sum_mul_lt_sum_mul Hb1 Hb2) as H1.
    apply Nat.compare_lt_iff in H1.
    rewrite Nat.add_comm, (Nat.add_comm (a * d)).
    now rewrite H1.
  } {
    rewrite rngl_mul_1_l.
    apply Nat.compare_gt_iff in Hb1, Hb2.
    specialize (Nat_lt_lt_sum_mul_lt_sum_mul Hb1 Hb2) as H1.
    apply Nat.compare_gt_iff in H1.
    rewrite Nat.add_comm, (Nat.add_comm (a * d)).
    now rewrite H1.
  }
}
Qed.

Theorem sign_diff'_mul :
  rngl_has_opp = true →
   ∀ a b c d,
  a ≠ b
  → c ≠ d
  → (sign_diff' a b * sign_diff' c d)%F =
     sign_diff (a * c + b * d) (a * d + b * c).
Proof.
intros Hop * Hab Hcd.
rewrite sign_diff'_sign_diff; [ | easy ].
rewrite sign_diff'_sign_diff; [ | easy ].
now apply sign_diff_mul.
Qed.

Theorem fold_comp_lt : ∀ la lb i,
  i < length lb
  → ff_app la (ff_app lb i) = ff_app (la ° lb) i.
Proof.
intros * Hib.
unfold "°".
unfold ff_app.
now rewrite (List_map_nth' 0).
Qed.

Theorem map_ff_app_is_permut_list : ∀ n la lb,
  is_permut n la
  → is_permut n lb
  → is_permut_list (map (ff_app la) lb).
Proof.
intros * (Hap, Hal) (Hbp, Hbl).
split. {
  intros j Hj.
  apply in_map_iff in Hj.
  destruct Hj as (k & Hkj & Hk).
  rewrite <- Hkj.
  rewrite map_length, Hbl, <- Hal.
  apply Hap, nth_In.
  rewrite Hal, <- Hbl.
  now apply Hbp.
} {
  apply nat_NoDup.
  rewrite map_length.
  intros j k Hj Hk Hjk.
  assert (Hab : is_permut n (la ° lb)) by now apply comp_is_permut.
  destruct Hab as ((_, Hab), _).
  apply (NoDup_nat _ Hab) in Hjk; [ easy | | ]; now rewrite comp_length.
}
Qed.

Theorem fold_comp_list : ∀ la lb, map (ff_app la) lb = la ° lb.
Proof. easy. Qed.

Theorem permut_comp_cancel_l : ∀ n la lb lc,
  NoDup la
  → length la = n
  → is_permut n lb
  → is_permut n lc
  → la ° lb = la ° lc ↔ lb = lc.
Proof.
intros * Ha Hal Hb Hc.
split; [ | now intros; subst lc ].
intros Hbc.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  destruct Hb as (_, Hb).
  destruct Hc as (_, Hc).
  apply length_zero_iff_nil in Hb, Hc.
  congruence.
}
apply List_eq_iff in Hbc.
destruct Hbc as (_, Hbc).
apply List_eq_iff.
split; [ destruct Hb, Hc; congruence | ].
intros d i.
unfold "°" in Hbc.
assert (H : ∀ i, ff_app la (nth i lb 0) = ff_app la (nth i lc 0)). {
  intros j.
  destruct (lt_dec j n) as [Hjn| Hjn]. 2: {
    apply Nat.nlt_ge in Hjn.
    rewrite nth_overflow; [ | destruct Hb; congruence ].
    rewrite nth_overflow; [ | destruct Hc; congruence ].
    easy.
  }
  specialize (Hbc 0 j).
  rewrite (List_map_nth' 0) in Hbc; [ | destruct Hb; congruence ].
  rewrite (List_map_nth' 0) in Hbc; [ | destruct Hc; congruence ].
  easy.
}
clear Hbc; rename H into Hbc.
destruct (lt_dec i n) as [Hin| Hin]. 2: {
  apply Nat.nlt_ge in Hin.
  rewrite nth_overflow; [ | destruct Hb; congruence ].
  rewrite nth_overflow; [ | destruct Hc; congruence ].
  easy.
}
specialize (Hbc i).
apply (NoDup_nat _ Ha) in Hbc; cycle 1. {
  destruct Hb as (Hbp, Hbl).
  rewrite Hal, <- Hbl.
  apply Hbp, nth_In.
  congruence.
} {
  destruct Hc as (Hcp, Hcl).
  rewrite Hal, <- Hcl.
  apply Hcp, nth_In.
  congruence.
}
rewrite nth_indep with (d' := 0); [ | destruct Hb; congruence ].
symmetry.
rewrite nth_indep with (d' := 0); [ | destruct Hc; congruence ].
now symmetry.
Qed.

Theorem permut_comp_cancel_r : ∀ n la lb lc,
  length la = n
  → length lb = n
  → is_permut n lc
  → la ° lc = lb ° lc ↔ la = lb.
Proof.
intros * Hal Hbl Hc.
split; [ | now intros; subst la ].
intros Hab.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  apply length_zero_iff_nil in Hal, Hbl.
  congruence.
}
apply List_eq_iff in Hab.
destruct Hab as (_, Hab).
apply List_eq_iff.
split; [ congruence | ].
intros d i.
specialize (Hab d (nth i (isort_rank Nat.leb lc) 0)).
unfold "°" in Hab.
rewrite (List_map_nth' 0) in Hab. 2: {
  apply isort_rank_ub.
  intros H; subst lc.
  destruct Hc as (Hcp, Hcl).
  now symmetry in Hcl.
}
rewrite (List_map_nth' 0) in Hab. 2: {
  apply isort_rank_ub.
  intros H; subst lc.
  destruct Hc as (Hcp, Hcl).
  now symmetry in Hcl.
}
do 2 rewrite fold_ff_app in Hab.
destruct Hc as (Hcp, Hcl).
destruct (lt_dec i n) as [Hin| Hin]. 2: {
  apply Nat.nlt_ge in Hin.
  rewrite nth_overflow; [ | now rewrite Hal ].
  rewrite nth_overflow; [ | now rewrite Hbl ].
  easy.
}
rewrite <- Hcl in Hin.
rewrite permut_permut_isort in Hab; [ | easy | easy ].
rewrite Hcl, <- Hal in Hin.
rewrite nth_indep with (d' := 0); [ symmetry | easy ].
rewrite Hal, <- Hbl in Hin.
rewrite nth_indep with (d' := 0); [ symmetry | easy ].
easy.
Qed.

Theorem comp_1_l : ∀ n l, AllLt l n → seq 0 n ° l = l.
Proof.
intros * Hp.
unfold "°", ff_app.
erewrite map_ext_in. 2: {
  intros i Hi.
  rewrite seq_nth; [ | now apply Hp ].
  now apply Nat.add_0_l.
}
apply map_id.
Qed.

Theorem comp_1_r : ∀ n la,
  length la = n
  → la ° seq 0 n = la.
Proof.
intros * Hl.
subst n.
unfold "°"; cbn.
unfold ff_app.
symmetry.
apply List_map_nth_seq.
Qed.

Arguments comp_1_r n%nat [la]%list.

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

(*
Compute (let l := [19;3;7;6] in (collapse l, isort_rank Nat.leb l)).
Compute (let l := [19;3;7;6] in (collapse l, isort_rank Nat.leb l)).
Compute (let l := [19;3;7;6] in (collapse l, collapse (collapse l))).
*)

Theorem collapse_length : ∀ l, length (collapse l) = length l.
Proof.
intros.
unfold collapse.
now do 2 rewrite isort_rank_length.
Qed.

Theorem collapse_is_permut : ∀ l, is_permut (length l) (collapse l).
Proof.
intros.
apply isort_rank_is_permut.
apply isort_rank_length.
Qed.

Theorem nth_ff_app_isort_rank : ∀ A d ord (l : list A) i,
  i < length l
  → nth (ff_app (isort_rank ord l) i) l d = nth i (isort ord l) d.
Proof.
intros * Hil.
rewrite (isort_isort_rank _ d).
rewrite (List_map_nth' 0); [ easy | ].
now rewrite isort_rank_length.
Qed.

Theorem sorted_rel : ∀ A (d : A) ord l,
  sorted ord l
  → ∀ i, S i < length l
  → ord (nth i l d) (nth (S i) l d) = true.
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

Theorem sorted_strongly_sorted : ∀ A (d : A) ord l,
  transitive ord
  → sorted ord l
  → ∀ i j,
    i < length l
    → j < length l
    → i < j
    → ord (nth i l d) (nth j l d) = true.
Proof.
intros * Htr Hso * Hi Hj Hij.
remember (j - i) as n eqn:Hn.
replace j with (i + n) in * by flia Hn Hij.
assert (Hnz : n ≠ 0) by flia Hij.
clear Hi Hij Hn.
revert i Hj.
induction n; intros; [ easy | clear Hnz; cbn ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  rewrite Nat.add_1_r in Hj |-*.
  now apply sorted_rel.
}
apply Htr with (b := nth (S i) l d). 2: {
  rewrite <- Nat.add_succ_comm in Hj.
  rewrite <- Nat.add_succ_comm.
  now apply IHn.
}
apply sorted_rel; [ easy | flia Hj ].
Qed.

Theorem permut_isort_rank_involutive : ∀ la,
  is_permut_list la
  → isort_rank Nat.leb (isort_rank Nat.leb la) = la.
Proof.
intros * Hp.
remember (isort_rank Nat.leb la) as lb eqn:Hlb.
apply (@permut_comp_cancel_r (length lb)) with (lc := lb). {
  now apply isort_rank_is_permut.
} {
  now rewrite Hlb, isort_rank_length.
} {
  rewrite Hlb, isort_rank_length.
  now apply isort_rank_is_permut.
}
subst lb.
rewrite comp_isort_rank_r.
rewrite permut_comp_isort_rank_l; [ | apply isort_rank_is_permut_list ].
rewrite isort_rank_length; symmetry.
now apply permut_isort_leb.
Qed.

Theorem collapse_lt_compat : ∀ l i j,
  i < length l
  → j < length l
  → ff_app l i < ff_app l j
  → ff_app (collapse l) i < ff_app (collapse l) j.
Proof.
intros l j i Hj Hi Hc2.
specialize (collapse_is_permut l) as Hc.
specialize (isort_rank_is_permut Nat.leb (length l) eq_refl) as Hr.
apply Nat.nle_gt; intros Hc1.
destruct (Nat.eq_dec (ff_app (collapse l) i) (ff_app (collapse l) j))
  as [H| H]. {
  destruct Hc as ((Hca, Hcn), Hcl).
  apply (NoDup_nat _ Hcn) in H; cycle 1. {
    now rewrite collapse_length.
  } {
    now rewrite collapse_length.
  }
  now subst j; apply Nat.lt_irrefl in Hc2.
}
assert (H' : ff_app (collapse l) i < ff_app (collapse l) j) by flia Hc1 H.
clear Hc1 H; rename H' into Hc1.
unfold collapse in Hc1.
remember (isort_rank Nat.leb l) as lrank eqn:Hlr.
remember (ff_app (collapse l) i) as i' eqn:Hi'.
assert (Hii' : i = ff_app lrank i'). {
  subst i'; unfold collapse.
  rewrite <- Hlr; symmetry.
  destruct Hr as (Hrp, Hrl).
  apply permut_permut_isort; [ easy | now rewrite Hrl ].
}
rewrite Hii' in Hc1.
rewrite permut_isort_permut in Hc1; [ | now destruct Hr | ]. 2: {
  rewrite Hi'.
  destruct Hc as ((Hca, Hcn), Hcl).
  rewrite Hcl in Hca.
  rewrite Hlr, isort_rank_length.
  apply Hca, nth_In.
  now rewrite Hcl.
}
remember (ff_app (collapse l) j) as j' eqn:Hj'.
assert (Hjj' : j = ff_app lrank j'). {
  subst j'; unfold collapse.
  rewrite <- Hlr; symmetry.
  destruct Hr as (Hrp, Hrl).
  apply permut_permut_isort; [ easy | now rewrite Hrl ].
}
rewrite Hjj' in Hc1.
rewrite permut_isort_permut in Hc1; [ | now destruct Hr | ]. 2: {
  rewrite Hj'.
  destruct Hc as ((Hca, Hcn), Hcl).
  rewrite Hcl in Hca.
  rewrite Hlr, isort_rank_length.
  apply Hca, nth_In.
  now rewrite Hcl.
}
rewrite Hii', Hjj' in Hc2.
rewrite Hlr in Hc2.
unfold ff_app in Hc2 at 1 3.
assert (Hi'l : i' < length l). {
  rewrite Hi'.
  destruct Hc as ((Hca, Hcn), Hcl).
  rewrite Hcl in Hca.
  apply Hca, nth_In.
  now rewrite collapse_length.
}
assert (Hj'l : j' < length l). {
  rewrite Hj'.
  destruct Hc as ((Hca, Hcn), Hcl).
  rewrite Hcl in Hca.
  apply Hca, nth_In.
  now rewrite collapse_length.
}
rewrite nth_ff_app_isort_rank in Hc2; [ | easy ].
rewrite nth_ff_app_isort_rank in Hc2; [ | easy ].
specialize (sorted_isort Nat_leb_is_total_relation l) as Hsl.
rewrite (isort_isort_rank _ 0) in Hsl.
rewrite <- Hlr in Hsl.
specialize sorted_strongly_sorted as H1.
specialize (H1 _ 0 _ _ Nat_leb_trans Hsl).
rewrite map_length, Hlr, isort_rank_length in H1.
specialize (H1 i' j' Hi'l Hj'l Hc1).
apply Nat.leb_le in H1.
rewrite <- Hlr in H1.
rewrite (isort_isort_rank _ 0) in Hc2.
rewrite <- Hlr in Hc2.
now apply Nat.nle_gt in Hc2.
Qed.

Theorem collapse_keeps_order : ∀ l i j,
  NoDup l
  → i < length l
  → j < length l
  → (ff_app (collapse l) i ?= ff_app (collapse l) j) =
    (ff_app l i ?= ff_app l j).
Proof.
intros * Hnd Hi Hj.
remember (ff_app (collapse l) i ?= ff_app (collapse l) j) as c1 eqn:Hc1.
remember (ff_app l i ?= ff_app l j) as c2 eqn:Hc2.
specialize (collapse_is_permut l) as Hc.
specialize (isort_rank_is_permut Nat.leb (length l) eq_refl) as Hr.
move c2 before c1.
symmetry in Hc1, Hc2.
destruct c1. {
  apply Nat.compare_eq_iff in Hc1.
  destruct Hc as ((Hca, Hcn), Hcl).
  specialize (NoDup_nat _ Hcn i j) as H1.
  rewrite Hcl in H1.
  specialize (H1 Hi Hj Hc1).
  subst j.
  now rewrite Nat.compare_refl in Hc2.
} {
  apply Nat.compare_lt_iff in Hc1.
  destruct c2; [ | easy | ]; exfalso. {
    apply Nat.compare_eq_iff in Hc2.
    specialize (NoDup_nat _ Hnd i j Hi Hj Hc2) as H1.
    rewrite H1 in Hc1.
    now apply Nat.lt_irrefl in Hc1.
  } {
    apply Nat.compare_gt_iff in Hc2.
    apply Nat.nle_gt in Hc1; apply Hc1.
    now apply Nat.lt_le_incl, collapse_lt_compat.
  }
} {
  apply Nat.compare_gt_iff in Hc1.
  destruct c2; [ | | easy ]; exfalso. {
    apply Nat.compare_eq_iff in Hc2.
    specialize (NoDup_nat _ Hnd i j Hi Hj Hc2) as H1.
    rewrite H1 in Hc1.
    now apply Nat.lt_irrefl in Hc1.
  } {
    apply Nat.compare_lt_iff in Hc2.
    apply Nat.nle_gt in Hc1; apply Hc1.
    now apply Nat.lt_le_incl, collapse_lt_compat.
  }
}
Qed.

Theorem ε_collapse_ε : ∀ l, NoDup l → ε (collapse l) = ε l.
Proof.
intros * Hnd.
destruct (Nat.eq_dec (length l) 0) as [Hlz| Hlz]. {
  now apply length_zero_iff_nil in Hlz; subst l; cbn.
}
unfold ε.
rewrite collapse_length.
apply rngl_product_eq_compat.
intros i (_, Hi).
apply rngl_product_eq_compat.
intros j (_, Hj).
move j before i.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
unfold sign_diff.
rewrite collapse_keeps_order; [ easy | easy | flia Hj Hlz | flia Hi Hlz ].
Qed.

Theorem fold_collapse : ∀ l,
  isort_rank Nat.leb (isort_rank Nat.leb l) = collapse l.
Proof. easy. Qed.

Theorem comp_0_l : ∀ l, [] ° l = repeat 0 (length l).
Proof.
intros.
unfold "°".
induction l as [| a]; [ easy | cbn ].
now destruct a; rewrite IHl.
Qed.

Theorem permut_isort : ∀ ord,
  antisymmetric ord
  → transitive ord
  → total_relation ord
  → ∀ n l p q,
  is_permut n p
  → is_permut n q
  → isort ord (l ° p) = isort ord (l ° q).
Proof.
intros * Hant Htr Htot * Hp Hq.
apply (isort_when_permuted Nat.eqb_eq); [ easy | easy | easy | ].
unfold "°".
apply (permutation_map Nat.eqb_eq Nat.eqb_eq).
apply (permutation_trans Nat.eqb_eq) with (lb := seq 0 n). {
  destruct Hp as (Hp1, Hp2); rewrite <- Hp2.
  now apply permut_list_permutation_iff.
} {
  destruct Hq as (Hq1, Hq2); rewrite <- Hq2.
  apply (permutation_sym Nat.eqb_eq).
  now apply permut_list_permutation_iff.
}
Qed.

Theorem isort_comp_permut_r : ∀ l p,
  is_permut (length l) p
  → isort Nat.leb (l ° p) = isort Nat.leb l.
Proof.
intros * Hp.
symmetry.
rewrite <- (comp_1_r (length l) eq_refl) at 1.
specialize (permut_isort Nat_leb_antisym Nat_leb_trans) as H1.
specialize (H1 Nat_leb_is_total_relation).
apply (H1 (length l)); [ | easy ].
apply seq_is_permut.
Qed.

Theorem permut_isort_rank_comp : ∀ n la lb,
  NoDup la
  → length la = n
  → is_permut n lb
  → isort_rank Nat.leb (la ° lb) =
    isort_rank Nat.leb lb ° isort_rank Nat.leb la.
Proof.
intros * Ha Hal Hb.
apply permut_comp_cancel_l with (n := n) (la := la ° lb). {
  destruct Hb as ((Hba, Hbn), Hbl).
  unfold "°".
  apply (NoDup_map_iff 0).
  intros i j Hi Hj Hij.
  apply (NoDup_nat _ Ha) in Hij; cycle 1. {
    rewrite Hal, <- Hbl.
    now apply Hba, nth_In.
  } {
    rewrite Hal, <- Hbl.
    now apply Hba, nth_In.
  }
  now apply (NoDup_nat _ Hbn) in Hij.
} {
  now rewrite comp_length; destruct Hb.
} {
  apply isort_rank_is_permut.
  now rewrite comp_length; destruct Hb.
} {
  destruct Hb.
  now apply comp_is_permut; apply isort_rank_is_permut.
}
rewrite comp_isort_rank_r.
rewrite <- (permut_comp_assoc n); cycle 1. {
  now destruct Hb.
} {
  destruct Hb as ((Hba, Hbn), Hbl).
  now apply comp_is_permut; apply isort_rank_is_permut.
}
rewrite (permut_comp_assoc n) with (f := lb); cycle 1. {
  destruct Hb as ((Hba, Hbn), Hbl).
  now rewrite isort_rank_length.
} {
  now apply isort_rank_is_permut.
}
rewrite comp_isort_rank_r.
destruct Hb as (Hbp, Hbl).
rewrite (permut_isort_leb Hbp).
rewrite comp_1_l. 2: {
  intros i Hi.
  rewrite Hbl, <- Hal.
  now apply in_isort_rank_lt in Hi.
}
rewrite comp_isort_rank_r.
apply isort_comp_permut_r.
now rewrite Hal, <- Hbl.
Qed.

Arguments permut_isort_rank_comp n%nat [la lb]%list.

Theorem butn_is_permut_list : ∀ i la,
  is_permut_list la
  → i = ff_app (isort_rank Nat.leb la) (length la - 1)
  → is_permut_list (butn i la).
Proof.
intros * Hp Hi.
destruct (Nat.eq_dec (length la) 0) as [Hlz| Hlz]. {
  apply length_zero_iff_nil in Hlz;subst la.
  now cbn in Hi; subst i; cbn.
}
split. {
  intros j Hj.
  rewrite butn_length.
  unfold Nat.b2n; rewrite if_ltb_lt_dec.
  destruct (lt_dec i (length la)) as [Hila| Hila]. 2: {
    exfalso; apply Hila; clear Hila.
    rewrite Hi.
    rewrite <- (isort_rank_length Nat.leb).
    apply isort_rank_is_permut_list, nth_In.
    rewrite isort_rank_length; cbn.
    apply in_butn in Hj.
    flia Hlz.
  }
  specialize (in_butn _ _ _ Hj) as H1.
  apply Hp in H1.
  destruct (Nat.eq_dec j (length la - 1)) as [Hjl| H]; [ | flia H1 H ].
  clear H1; exfalso.
  rewrite <- Hjl in Hi.
  assert (Hji : j = ff_app la i). {
    rewrite Hi; symmetry.
    apply permut_permut_isort; [ easy | flia Hjl Hlz ].
  }
  apply (In_nth _ _ 0) in Hj.
  rewrite butn_length in Hj.
  apply Nat.ltb_lt in Hila.
  rewrite Hila in Hj.
  apply Nat.ltb_lt in Hila.
  destruct Hj as (k & Hki & Hkj).
  cbn in Hki.
  rewrite nth_butn in Hkj.
  rewrite <- Hkj in Hji.
  unfold ff_app in Hji.
  destruct Hp as (Hpa, Hpd).
  apply (NoDup_nat _ Hpd) in Hji; [ | | easy ]. 2: {
    unfold Nat.b2n; rewrite if_leb_le_dec.
    destruct (le_dec i k) as [Hik| Hik]; [ flia Hki | ].
    apply Nat.nle_gt in Hik.
    flia Hila Hik.
  }
  unfold Nat.b2n in Hji; rewrite if_leb_le_dec in Hji.
  destruct (le_dec i k) as [H| H]; flia H Hji.
}
apply NoDup_butn.
now destruct Hp.
Qed.

Theorem permut_collapse : ∀ la,
  is_permut_list la
  → collapse la = la.
Proof.
intros * Ha.
unfold collapse.
now apply permut_isort_rank_involutive.
Qed.

Theorem collapse_idemp : ∀ la,
  collapse (collapse la) = collapse la.
Proof.
intros.
apply permut_collapse.
apply collapse_is_permut.
Qed.

Theorem collapse_comp : ∀ la lb,
  NoDup la
  → is_permut_list lb
  → length la = length lb
  → collapse (la ° lb) = collapse la ° lb.
Proof.
intros * Ha Hb Hab.
unfold collapse.
symmetry.
rewrite <- (permut_isort_rank_involutive Hb) at 1.
rewrite (permut_isort_rank_comp (length lb)); [ | easy | easy | ]. 2: {
  now destruct Hb.
}
rewrite (permut_isort_rank_comp (length lb)); [ easy | | | ]. {
  apply NoDup_isort_rank.
} {
  apply isort_rank_length.
} {
  now apply isort_rank_is_permut.
}
Qed.

(* to be completed
Theorem NoDup_comp_if : ∀ la lb,
  NoDup (la ° lb)
  → NoDup la.
Proof.
intros * Hab.
apply nat_NoDup.
specialize (NoDup_nat _ Hab) as H1.
intros i j Hi Hj Hij.
rewrite comp_length in H1.
...
destruct Hbp as (Hbp, Hbl).
    rewrite <- Hbl in Hi, Hj.
    remember (ff_app (isort_rank Nat.leb lb) i) as i' eqn:Hi'.
    remember (ff_app (isort_rank Nat.leb lb) j) as j' eqn:Hj'.
    specialize (H1 i' j').
    assert (H : i' < length lb). {
      rewrite Hi'; unfold ff_app.
      apply isort_rank_ub.
      now intros H; rewrite H in Hi.
    }
    specialize (H1 H); clear H.
    assert (H : j' < length lb). {
      rewrite Hj'; unfold ff_app.
      apply isort_rank_ub.
      now intros H; rewrite H in Hi.
    }
    specialize (H1 H); clear H.
    assert (H : ff_app (la ° lb) i' = ff_app (la ° lb) j'). {
      rewrite Hi', Hj'.
      unfold "°", ff_app.
      rewrite (List_map_nth' 0). 2: {
        apply isort_rank_ub.
        now intros H; subst lb.
      }
      rewrite (List_map_nth' 0). 2: {
        apply isort_rank_ub.
        now intros H; subst lb.
      }
      do 6 rewrite fold_ff_app.
      rewrite permut_permut_isort; [ | now destruct Hbp | easy ].
      rewrite permut_permut_isort; [ | now destruct Hbp | easy ].
      easy.
    }
    specialize (H1 H); clear H.
    rewrite Hi', Hj' in H1.
    assert (H : is_permut_list (isort_rank Nat.leb lb)). {
      now apply isort_rank_is_permut_list.
    }
    destruct H as (Hra, Hrn).
    apply (NoDup_nat _ Hrn) in H1; [ easy | | ]. {
      now rewrite isort_rank_length.
    } {
      now rewrite isort_rank_length.
    }
  }
Qed.
*)

Theorem NoDup_comp_iff : ∀ la lb,
  is_permut (length la) lb
  → NoDup la
  ↔ NoDup (la ° lb).
Proof.
intros * Hbp.
split. {
  intros Haa.
  unfold "°".
  apply (NoDup_map_iff 0).
  intros i j Hi Hj Hij.
  destruct Hbp as (Hbp, Hbl).
  apply (NoDup_nat _ Haa) in Hij; cycle 1. {
    rewrite <- Hbl.
    now apply Hbp, nth_In.
  } {
    rewrite <- Hbl.
    now apply Hbp, nth_In.
  }
  destruct Hbp as (Hba, Hbn).
  now apply (NoDup_nat _ Hbn) in Hij.
} {
  intros Haa.
  apply nat_NoDup.
  specialize (NoDup_nat _ Haa) as H1.
    intros i j Hi Hj Hij.
    rewrite comp_length in H1.
    destruct Hbp as (Hbp, Hbl).
    rewrite <- Hbl in Hi, Hj.
    remember (ff_app (isort_rank Nat.leb lb) i) as i' eqn:Hi'.
    remember (ff_app (isort_rank Nat.leb lb) j) as j' eqn:Hj'.
    specialize (H1 i' j').
    assert (H : i' < length lb). {
      rewrite Hi'; unfold ff_app.
      apply isort_rank_ub.
      now intros H; rewrite H in Hi.
    }
    specialize (H1 H); clear H.
    assert (H : j' < length lb). {
      rewrite Hj'; unfold ff_app.
      apply isort_rank_ub.
      now intros H; rewrite H in Hi.
    }
    specialize (H1 H); clear H.
    assert (H : ff_app (la ° lb) i' = ff_app (la ° lb) j'). {
      rewrite Hi', Hj'.
      unfold "°", ff_app.
      rewrite (List_map_nth' 0). 2: {
        apply isort_rank_ub.
        now intros H; subst lb.
      }
      rewrite (List_map_nth' 0). 2: {
        apply isort_rank_ub.
        now intros H; subst lb.
      }
      do 6 rewrite fold_ff_app.
      rewrite permut_permut_isort; [ | now destruct Hbp | easy ].
      rewrite permut_permut_isort; [ | now destruct Hbp | easy ].
      easy.
    }
    specialize (H1 H); clear H.
    rewrite Hi', Hj' in H1.
    assert (H : is_permut_list (isort_rank Nat.leb lb)). {
      now apply isort_rank_is_permut_list.
    }
    destruct H as (Hra, Hrn).
    apply (NoDup_nat _ Hrn) in H1; [ easy | | ]. {
      now rewrite isort_rank_length.
    } {
      now rewrite isort_rank_length.
    }
  }
Qed.

Theorem ε_when_dup :
  rngl_has_opp = true →
  rngl_has_eqb = true →
  ∀ la,
  ¬ NoDup la
  → ε la = 0%F.
Proof.
intros Hop Heq * Haa.
symmetry.
remember (rngl_eqb (ε la) 0%F) as ez eqn:Hez; symmetry in Hez.
destruct ez; [ now apply rngl_eqb_eq in Hez | exfalso ].
apply (rngl_eqb_neq Heq) in Hez.
apply Haa; clear Haa.
apply nat_NoDup.
intros i j Hi Hj Hij.
unfold ε in Hez.
destruct (Nat.eq_dec i j) as [Heij| Heqj]; [ easy | exfalso ].
apply Hez; clear Hez.
destruct (lt_dec i j) as [Hlij| Hlij]. {
  erewrite (rngl_product_split3 i). 2: {
    split; [ easy | flia Hi ].
  }
  remember (∏ (_ = _, _), _) as x eqn:Hx.
  erewrite (rngl_product_split3 j); subst x. 2: {
    split; [ easy | flia Hj ].
  }
  apply Nat.ltb_lt in Hlij; rewrite Hlij.
  rewrite Hij.
  rewrite sign_diff_id.
  rewrite rngl_mul_0_r; [ | now left ].
  rewrite rngl_mul_0_l; [ | now left ].
  rewrite rngl_mul_0_r; [ | now left ].
  rewrite rngl_mul_0_l; [ | now left ].
  easy.
} {
  assert (H : j < i) by flia Heqj Hlij.
  clear Hlij; rename H into Hlij.
  erewrite (rngl_product_split3 j). 2: {
    split; [ easy | flia Hj ].
  }
  remember (∏ (_ = _, _), _) as x eqn:Hx.
  erewrite (rngl_product_split3 i); subst x. 2: {
    split; [ easy | flia Hi ].
  }
  apply Nat.ltb_lt in Hlij; rewrite Hlij.
  rewrite Hij.
  rewrite sign_diff_id.
  rewrite rngl_mul_0_r; [ | now left ].
  rewrite rngl_mul_0_l; [ | now left ].
  rewrite rngl_mul_0_r; [ | now left ].
  rewrite rngl_mul_0_l; [ | now left ].
  easy.
}
Qed.

(* to be completed
Theorem NoDup_sign_comp : in_charac_0_field →
  ∀ la lb,
  NoDup lb
  → ε (la ° lb) = (ε la * ε lb)%F.
Proof.
intros Hif * Hbnd.
destruct (ListDec.NoDup_dec Nat.eq_dec la) as [Haa| Haa]. 2: {
  symmetry.
  rewrite ε_when_dup; [ | now destruct Hif | now destruct Hif | easy ].
  symmetry.
  rewrite ε_when_dup; [ | now destruct Hif | now destruct Hif | ]. 2: {
    intros H; apply Haa; clear Haa.
...
    apply NoDup_comp_iff in H.
    now apply NoDup_comp_iff in H.
  }
  symmetry.
  now apply rngl_mul_0_l; destruct Hif; left.
} {
  rewrite <- ε_collapse_ε; [ | now apply NoDup_comp_iff ].
  rewrite collapse_comp; [ | easy | now destruct Hbp | now destruct Hbp ].
  symmetry.
  rewrite <- ε_collapse_ε; [ | easy ].
  symmetry.
  apply (signature_comp_fun_expand_1 Hif (length la)); [ | easy | ]. {
    apply collapse_is_permut.
  }
  destruct Hif as (Hop & Hic & Hin & H10 & Hit & Hde & Hch).
  rewrite signature_comp_fun_expand_2_1; try easy.
  rewrite signature_comp_fun_expand_2_2; try easy.
  apply signature_comp_fun_changement_of_variable; try easy.
  apply collapse_is_permut.
}
Qed.
...
*)

Theorem sign_comp : in_charac_0_field →
  ∀ la lb,
  is_permut (length la) lb
  → ε (la ° lb) = (ε la * ε lb)%F.
Proof.
intros Hif * Hbp.
destruct (ListDec.NoDup_dec Nat.eq_dec la) as [Haa| Haa]. 2: {
  symmetry.
  rewrite ε_when_dup; [ | now destruct Hif | now destruct Hif | easy ].
  symmetry.
  rewrite ε_when_dup; [ | now destruct Hif | now destruct Hif | ]. 2: {
    intros H; apply Haa; clear Haa.
    now apply NoDup_comp_iff in H.
  }
  symmetry.
  now apply rngl_mul_0_l; destruct Hif; left.
} {
  rewrite <- ε_collapse_ε; [ | now apply NoDup_comp_iff ].
  rewrite collapse_comp; [ | easy | now destruct Hbp | now destruct Hbp ].
  symmetry.
  rewrite <- ε_collapse_ε; [ | easy ].
  symmetry.
  apply (signature_comp_fun_expand_1 Hif (length la)); [ | easy | ]. {
    apply collapse_is_permut.
  }
  destruct Hif as (Hop & Hic & Hin & H10 & Hit & Hde & Hch).
  rewrite signature_comp_fun_expand_2_1; try easy.
  rewrite signature_comp_fun_expand_2_2; try easy.
  apply signature_comp_fun_changement_of_variable; try easy.
  apply collapse_is_permut.
}
Qed.

(* *)

Theorem canon_sym_gr_succ_values : ∀ n k σ σ',
  σ = canon_sym_gr_list (S n) k
  → σ' = canon_sym_gr_list n (k mod n!)
  → ∀ i,
    ff_app σ i =
    match i with
    | 0 => k / n!
    | S i' =>
        if ((k <? n!) && (n <=? i'))%bool then 0
        else succ_when_ge (k / n!) (ff_app σ' i')
    end.
Proof.
intros * Hσ Hσ' i.
destruct i; [ now subst σ | ].
subst σ; cbn - [ "<=?" ].
remember ((k <? n!) && (n <=? i))%bool as b eqn:Hb.
symmetry in Hb.
destruct b. {
  apply Bool.andb_true_iff in Hb.
  destruct Hb as (Hkn, Hni).
  apply Nat.ltb_lt in Hkn.
  apply Nat.leb_le in Hni.
  rewrite nth_overflow; [ easy | ].
  rewrite map_length.
  now rewrite canon_sym_gr_list_length.
}
apply Bool.andb_false_iff in Hb.
destruct Hb as [Hb| Hb]. {
  apply Nat.ltb_ge in Hb.
  destruct (lt_dec i n) as [Hin| Hin]. {
    rewrite (List_map_nth' 0); [ | now rewrite canon_sym_gr_list_length ].
    now rewrite Hσ'.
  } {
    apply Nat.nlt_ge in Hin.
    rewrite nth_overflow. 2: {
      now rewrite map_length, canon_sym_gr_list_length.
    }
    unfold succ_when_ge, ff_app.
    rewrite Hσ'.
    rewrite nth_overflow; [ | now rewrite canon_sym_gr_list_length ].
    unfold Nat.b2n; rewrite if_leb_le_dec.
    destruct (le_dec (k / n!) 0) as [H1| H1]; [ | easy ].
    apply Nat.le_0_r in H1.
    apply Nat.div_small_iff in H1; [ | apply fact_neq_0 ].
    now apply Nat.nle_gt in H1.
  }
} {
  apply Nat.leb_gt in Hb.
  rewrite (List_map_nth' 0); [ | now rewrite canon_sym_gr_list_length ].
  now rewrite Hσ'.
}
Qed.

(* equality of ε of sym_gr elem and ε_permut *)

Theorem ε_of_sym_gr_permut_succ :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  ∀ n k,
  k < (S n)!
  → ε (canon_sym_gr_list (S n) k) =
    (minus_one_pow (k / n!) * ε (canon_sym_gr_list n (k mod n!)))%F.
Proof.
intros Hic Hop Hin H10 * Hkn.
unfold ε at 1.
rewrite canon_sym_gr_list_length.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  unfold ε.
  subst n; cbn.
  apply Nat.lt_1_r in Hkn; subst k; cbn.
  do 4 rewrite rngl_product_only_one; cbn.
  symmetry; apply rngl_mul_1_l.
}
rewrite Nat_sub_succ_1.
rewrite rngl_product_split_first; [ | easy ].
f_equal. {
  rewrite rngl_product_split_first; [ | easy ].
  replace (0 <? 0) with false by easy.
  rewrite rngl_mul_1_l.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec 0 i) as [H| H]; [ clear H | flia Hi H ].
    easy.
  }
  cbn - [ "<?" canon_sym_gr_list ].
  remember (canon_sym_gr_list (S n) k) as σ eqn:Hσ.
  remember (canon_sym_gr_list n (k mod n!)) as σ' eqn:Hσ'.
  specialize (canon_sym_gr_succ_values Hσ Hσ') as H1.
  unfold sign_diff at 1.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite H1.
    replace i with (S (i - 1)) at 1 by flia Hi.
    easy.
  }
  cbn - [ "<?" ].
  rewrite (rngl_product_shift 1); [ | flia Hnz ].
  rewrite Nat.sub_diag.
  remember (k / fact n) as x eqn:Hx.
  erewrite rngl_product_eq_compat. 2: {
    intros i (_, Hi).
    rewrite Nat.add_comm, Nat.add_sub.
    replace (match _ with Eq => _ | Lt => _ | Gt => _ end) with
      (if x <? ff_app σ' i + 1 then 1%F else (-1)%F). 2: {
      rewrite H1.
      unfold succ_when_ge, Nat.b2n.
      rewrite if_ltb_lt_dec.
      rewrite if_leb_le_dec.
      remember ((k <? n!) && (n <=? i))%bool as b eqn:Hb.
      symmetry in Hb.
      destruct b. {
        apply Bool.andb_true_iff in Hb.
        destruct Hb as (_, Hb).
        apply Nat.leb_le in Hb.
        flia Hi Hb Hnz.
      }
      unfold ff_app.
      destruct (le_dec x (nth i σ' 0)) as [H2| H2]. {
        destruct (lt_dec x (nth i σ' 0 + 1)) as [H3| H3]; [ | flia H2 H3 ].
        apply Nat.compare_gt_iff in H3.
        now rewrite H3.
      }
      rewrite Nat.add_0_r.
      apply Nat.nle_gt in H2.
      apply Nat.compare_lt_iff in H2.
      rewrite H2.
      apply Nat.compare_lt_iff in H2.
      destruct (lt_dec x (nth i σ' 0)) as [H| H]; [ flia H H2 | clear H ].
      destruct (lt_dec x (nth i σ' 0 + 1)) as [H3| H3]; [ | easy ].
      flia H2 H3.
    }
    easy.
  }
  cbn - [ "<?" ].
  assert (Hp' : is_permut n σ'). {
    rewrite Hσ'.
    now apply canon_sym_gr_list_is_permut.
  }
  assert (Hp : is_permut (S n) σ). {
    rewrite Hσ.
    now apply canon_sym_gr_list_is_permut.
  }
  rewrite rngl_product_change_var with
    (g := ff_app (isort_rank Nat.leb σ')) (h := ff_app σ'). 2: {
    intros i (_, Hi).
    destruct Hp' as (Hp'p, Hp'l).
    apply permut_isort_permut; [ easy | rewrite Hp'l; flia Hnz Hi ].
  }
  rewrite Nat.sub_0_r.
  rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
  rewrite Nat_sub_succ_1.
  destruct Hp' as (Hp'p, Hp'l).
  erewrite rngl_product_list_eq_compat. 2: {
    intros i Hi.
    apply in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj).
    apply in_seq in Hj.
    rewrite permut_permut_isort; [ | easy | ]. 2: {
      rewrite <- Hji.
      destruct Hp'p as (Hp'a, Hp'n).
      apply Hp'a, nth_In.
      now rewrite Hp'l.
    }
    easy.
  }
  cbn - [ "<?" seq ].
  rewrite (rngl_product_change_list Nat.eqb_eq) with
      (lb := seq 0 n); [ | easy | ]. 2: {
    destruct Hp'p as (Hp'a, Hp'n).
    rewrite <- Hp'l at 1.
    rewrite <- List_map_ff_app_seq, <- Hp'l.
    now apply permut_list_permutation_iff.
  }
  rewrite rngl_product_seq_product; [ | easy ].
  rewrite Nat.add_0_l.
  destruct (Nat.eq_dec x 0) as [Hxz| Hxz]. {
    move Hxz at top; subst x.
    cbn - [ "<?" ].
    apply all_1_rngl_product_1.
    intros i (_, Hi).
    now rewrite Nat.add_comm.
  }
  rewrite (rngl_product_split (x - 1)). 2: {
    split; [ easy | ].
    apply -> Nat.succ_le_mono.
    enough (H : x < S n) by flia H Hnz.
    replace x with (ff_app σ 0) by now rewrite H1.
    destruct Hp as ((Hp1, Hp2), Hp3).
    rewrite <- Hp3.
    apply Hp1, nth_In.
    rewrite Hp3; flia.
  }
  remember (∏ (i = _, _), _)%F as y eqn:Hy.
  rewrite all_1_rngl_product_1. 2: {
    intros i Hi.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec x (i + 1)) as [H2| H2]; [ easy | ].
    flia Hi H2.
  }
  subst y; rewrite rngl_mul_1_r.
  erewrite rngl_product_eq_compat. 2: {
    intros i (_, Hi).
    replace (if x <? i + 1 then 1%F else _) with (-1)%F. 2: {
      rewrite if_ltb_lt_dec.
      destruct (lt_dec x (i + 1)) as [H| H]; [ | easy ].
      flia Hi H Hxz.
    }
    easy.
  }
  cbn.
  destruct x; [ easy | clear Hxz ].
  rewrite Nat_sub_succ_1.
  clear Hx H1.
  induction x; cbn. {
    unfold iter_seq, iter_list; cbn.
    apply rngl_mul_1_l.
  }
  rewrite rngl_product_split_last; [ | easy ].
  rewrite (rngl_product_shift 1); [ | flia ].
  rewrite Nat.sub_diag.
  rewrite Nat_sub_succ_1.
  rewrite IHx.
  symmetry.
  rewrite minus_one_pow_succ; [ | easy ].
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_opp_l; [ | easy ].
  now rewrite rngl_mul_1_l.
}
unfold ε.
rewrite canon_sym_gr_list_length.
rewrite (rngl_product_shift 1). 2: {
  split; [ easy | flia Hnz ].
}
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_split_first; [ | easy ].
  rewrite if_ltb_lt_dec.
  destruct (lt_dec (1 + i) 0) as [H| H]; [ flia H | clear H ].
  rewrite rngl_mul_1_l.
  easy.
}
cbn - [ canon_sym_gr_list "<?" ].
apply rngl_product_eq_compat.
intros i Hi.
rewrite (rngl_product_shift 1). 2: {
  split; [ easy | flia Hnz ].
}
apply rngl_product_eq_compat.
intros j Hj.
cbn - [ "<?" canon_sym_gr_list ].
replace (S i <? S j) with (i <? j) by easy.
move j before i.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
remember (canon_sym_gr_list (S n) k) as σ eqn:Hσ.
remember (canon_sym_gr_list  n (k mod n!)) as σ' eqn:Hσ'.
specialize (canon_sym_gr_succ_values Hσ Hσ') as H1.
do 2 rewrite H1.
unfold succ_when_ge, Nat.b2n.
do 2 rewrite if_leb_le_dec.
remember ((k <? n!) && (n <=? i))%bool as bi eqn:Hbi.
remember ((k <? n!) && (n <=? j))%bool as bj eqn:Hbj.
symmetry in Hbi, Hbj.
move σ' before σ; move bj before bi.
destruct bi. {
  apply Bool.andb_true_iff in Hbi.
  destruct Hbi as (Hkni, Hni).
  apply Nat.leb_le in Hni.
  flia Hi Hni Hnz.
}
destruct bj. {
  apply Bool.andb_true_iff in Hbj.
  destruct Hbj as (Hknj, Hnj).
  apply Nat.leb_le in Hnj.
  flia Hj Hnj Hnz.
}
apply Bool.andb_false_iff in Hbi, Hbj.
unfold sign_diff.
destruct (le_dec (k / n!) (ff_app σ' j)) as [Hsfj| Hsfj]. {
  destruct (le_dec (k / n!) (ff_app σ' i)) as [Hsfi| Hsfi]. {
    now do 2 rewrite Nat.add_1_r.
  }
  rewrite Nat.add_0_r.
  replace (ff_app σ' j + 1 ?= ff_app σ' i) with Gt. 2: {
    symmetry; apply Nat.compare_gt_iff.
    flia Hsfi Hsfj.
  }
  replace (ff_app σ' j ?= ff_app σ' i) with Gt. 2: {
    symmetry; apply Nat.compare_gt_iff.
    flia Hsfi Hsfj.
  }
  easy.
}
destruct (le_dec (k / n!) (ff_app σ' i)) as [Hsfi| Hsfi]. {
  rewrite Nat.add_0_r.
  replace (ff_app σ' j ?= ff_app σ' i + 1) with Lt. 2: {
    symmetry; apply Nat.compare_lt_iff.
    flia Hsfi Hsfj.
  }
  replace (ff_app σ' j ?= ff_app σ' i) with Lt. 2: {
    symmetry; apply Nat.compare_lt_iff.
    flia Hsfi Hsfj.
  }
  easy.
}
now do 2 rewrite Nat.add_0_r.
Qed.

Theorem canon_sym_gr_surjective : ∀ n k j,
  k < fact n
  → j < n
  → ∃ i : nat, i < n ∧ ff_app (canon_sym_gr_list n k) i = j.
Proof.
intros * Hkn Hjn.
exists (ff_app (canon_sym_gr_inv_list n k) j).
split; [ now apply canon_sym_gr_inv_list_ub | ].
now apply canon_sym_gr_sym_gr_inv.
Qed.

Theorem NoDup_ε_1_opp_1 :
  rngl_has_opp = true →
  ∀ σ, NoDup σ → ε σ = 1%F ∨ ε σ = (-1)%F.
Proof.
intros Hop * Hσ.
unfold ε.
destruct (le_dec (length σ) 1) as [Hn1| Hn1]. {
  replace (length σ - 1) with 0 by flia Hn1.
  now do 2 rewrite rngl_product_only_one; cbn; left.
}
apply rngl_product_1_opp_1; [ easy | ].
intros i Hi.
apply rngl_product_1_opp_1; [ easy | ].
intros j Hj.
unfold sign_diff.
rewrite if_ltb_lt_dec.
remember (ff_app σ j ?= ff_app σ i) as b eqn:Hb.
symmetry in Hb.
destruct (lt_dec i j) as [Hij| Hij]; [ | now left ].
destruct b; [ | now right | now left ].
apply Nat.compare_eq_iff in Hb.
apply (NoDup_nat _ Hσ) in Hb; [ | flia Hj Hn1 | flia Hi Hn1 ].
flia Hi Hj Hb Hij.
Qed.

Theorem ε_1_opp_1_NoDup :
  rngl_has_opp = true →
  rngl_has_1_neq_0 = true →
  rngl_has_eqb = true →
  ∀ σ, ε σ = 1%F ∨ ε σ = (-1)%F → NoDup σ.
Proof.
intros Hop H10 Heq * Hσ.
destruct (ListDec.NoDup_dec Nat.eq_dec σ) as [H1| H1]; [ easy | ].
exfalso.
apply ε_when_dup in H1; [ | easy | easy ].
rewrite H1 in Hσ.
destruct Hσ as [Hσ| Hσ]; symmetry in Hσ. {
  now apply rngl_1_neq_0 in Hσ.
} {
  rewrite <- rngl_opp_0 in Hσ; [ | easy ].
  apply rngl_opp_inj in Hσ; [ | easy ].
  now apply rngl_1_neq_0 in Hσ.
}
Qed.

Theorem NoDup_ε_square :
  rngl_has_opp = true →
  ∀ σ, NoDup σ → (ε σ * ε σ = 1)%F.
Proof.
intros Hop * Hσ.
specialize (NoDup_ε_1_opp_1) as H1.
specialize (H1 Hop σ Hσ).
destruct H1 as [H1| H1]; rewrite H1. {
  apply rngl_mul_1_l.
} {
  rewrite rngl_mul_opp_opp; [ | easy ].
  apply rngl_mul_1_l.
}
Qed.

End a.

Arguments ε {T}%type {ro}.
Arguments sign_diff {T}%type {ro} (u v)%nat.

Arguments ε_nil {T ro rp}.
Arguments ε_permut {T}%type {ro} (n k)%nat.
Arguments ε_of_sym_gr_permut_succ {T}%type {ro rp} _ (n k)%nat.
Arguments comp_is_permut_list n%nat [σ₁ σ₂]%list.
Arguments map_ff_app_is_permut_list n%nat [la lb]%list.
Arguments permut_isort_rank_comp n%nat [la lb]%list.
Arguments rngl_product_change_list {T ro rp} [A]%type _ _ _ [la lb]%list.
Arguments rngl_product_change_var {T ro} A%type [b e]%nat.
Arguments sign_comp {T}%type {ro rp} _ [la lb]%list.
Arguments transposition_signature {T}%type {ro rp} _ _ (n p q)%nat.
Arguments NoDup_ε_1_opp_1 {T}%type {ro rp} _  [σ].
Arguments NoDup_ε_square {T}%type {ro rp} _ [σ].
Arguments ε_when_dup {T ro rp} Hop Hde [la]%list.

Arguments minus_one_pow {T}%type {ro} n%nat.
Arguments minus_one_pow_add_r {T}%type {ro rp} Hop (i j)%nat.
Arguments minus_one_pow_succ {T}%type {ro rp} _ i%nat.
Arguments minus_one_pow_succ_succ {T}%type {ro rp} _ i%nat.
