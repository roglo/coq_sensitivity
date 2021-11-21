(* signatures *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Require Import Permutation.
Import List List.ListNotations.

Require Import Misc RingLike.
Require Import IterMul.
Require Import PermutSeq.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

Definition δ i j u v :=
  if i <? j then (rngl_of_nat v - rngl_of_nat u)%F else 1%F.

(*
Definition ε_fun f n :=
  ((∏ (i = 1, n), ∏ (j = 1, n), δ i j (f (i - 1)%nat) (f (j - 1)%nat)) /
   (∏ (i = 1, n), ∏ (j = 1, n), δ i j i j))%F.

Definition ε n (p : list nat) := ε_fun (λ i, nth i p 0) n.
*)

Definition ε n (p : list nat) :=
  ((∏ (i = 1, n), ∏ (j = 1, n),
    δ i j (ff_app p (i - 1)) (ff_app p (j - 1))) /
   (∏ (i = 1, n), ∏ (j = 1, n), δ i j i j))%F.

Definition minus_one_pow n :=
  match n mod 2 with
  | 0 => 1%F
  | _ => (- 1%F)%F
  end.

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

(* alternative version of signature of a permutation
   using only signs: ws = with sign *)

Definition sign_diff u v := if v <? u then 1%F else (-1)%F.
Definition abs_diff u v := if v <? u then u - v else v - u.

(*
Definition ε_fun_ws f n :=
  (∏ (i = 1, n), ∏ (j = 1, n),
   if i <? j then sign_diff (f (j - 1)%nat) (f (i - 1)%nat) else 1)%F.

Definition ε_ws n (p : list nat) := ε_fun_ws (λ i, nth i p 0) n.
*)

Definition ε_ws n (p : list nat) :=
  (∏ (i = 1, n), ∏ (j = 1, n),
   if i <? j then sign_diff (nth (j - 1) p 0)%nat (nth (i - 1) p 0)%nat
   else 1)%F.

(* equality of both definitions of ε: ε and ε_ws *)

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
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ i j,
  i < j
  → (rngl_of_nat j - rngl_of_nat i)%F = rngl_of_nat (j - i).
Proof.
intros Hom * Hij.
revert j Hij.
induction i; intros; cbn. {
  rewrite rngl_sub_0_r; f_equal; [ | easy ].
  now destruct j.
}
destruct j; [ easy | cbn ].
rewrite rngl_add_sub_simpl_l; [ | easy ].
apply IHi.
now apply Nat.succ_lt_mono in Hij.
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
  rewrite rngl_product_empty; [ | flia ].
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

Theorem rngl_sub_is_mul_sign_abs :
  rngl_has_opp = true →
  ∀ a b,
  (rngl_of_nat a - rngl_of_nat b)%F =
  (sign_diff a b * rngl_of_nat (abs_diff a b))%F.
Proof.
intros Hop *.
unfold sign_diff, abs_diff.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec b a) as [Hba| Hba]. {
  rewrite rngl_mul_1_l.
  apply rngl_of_nat_sub; [ now left | easy ].
} {
  apply Nat.nlt_ge in Hba.
  destruct (Nat.eq_dec a b) as [Hab| Hab]. {
    subst b.
    rewrite rngl_sub_diag, Nat.sub_diag; cbn; [ | now left ].
    symmetry.
    now apply rngl_mul_0_r; left.
  }
  rewrite <- rngl_opp_sub_distr; [ | easy ].
  rewrite rngl_of_nat_sub; [ | now left | flia Hba Hab ].
  rewrite rngl_mul_opp_l; [ | easy ].
  now rewrite rngl_mul_1_l.
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

Theorem rngl_product_change_list :
  rngl_is_comm = true →
  ∀ A (la lb : list A) f,
  Permutation la lb
  → (∏ (i ∈ la), f i = ∏ (i ∈ lb), f i)%F.
Proof.
intros Hic * P.
induction P; [ easy | | | ]. {
  rewrite rngl_product_list_cons; [ | easy ].
  rewrite rngl_product_list_cons; [ | easy ].
  now rewrite IHP.
} {
  do 4 (rewrite rngl_product_list_cons; [ | easy ]).
  do 2 rewrite rngl_mul_assoc.
  f_equal.
  now apply rngl_mul_comm.
} {
  etransitivity; [ apply IHP1 | apply IHP2 ].
}
Qed.

Theorem rngl_product_product_div_eq_1 :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_is_comm = true →
  rngl_has_inv = true →
  rngl_is_integral = true →
  rngl_has_1_neq_0 = true →
  rngl_has_dec_eq = true →
  ∀ n f g,
  (∀ i j, i < n → j < n → g i j ≠ 0%F)
  → (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), (f i j / g i j)))%F = 1%F
  → (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), f i j))%F =
    (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), g i j))%F.
Proof.
intros Hom Hic Hid Hin H10 Hde * Hg Hs.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
remember (∏ (i ∈ _), _)%F as a eqn:Ha in |-*.
remember (∏ (i ∈ _), _)%F as b eqn:Hb in |-*.
destruct (rngl_eq_dec Hde b 0%F) as [Hbz| Hbz]. {
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
erewrite rngl_product_list_permut with (l1 := rev _); [ | easy | ]. 2: {
  symmetry; apply Permutation_rev.
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
  erewrite rngl_product_list_permut with (l1 := rev _); [ | easy | ]. 2: {
    symmetry; apply Permutation_rev.
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
rewrite rngl_product_shift; [ | flia Hnz Hn1 ].
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
  replace (n - i) with (S (n - i - 1)) by flia Hnz Hn1 Hi.
  rewrite seq_S.
  replace (S i + (n - i - 1)) with n by flia Hnz Hn1 Hi.
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
  rewrite Nat.add_1_r.
  rewrite Nat.sub_succ.
  now rewrite Nat_sub_sub_swap.
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
rewrite rngl_product_shift; [ | flia Hnz Hn1 ].
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
rewrite rngl_product_shift; [ | flia Hnz Hn1 ].
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
  is_permut_list σ
  → length σ = n
  → (∀ i j, f i j = f j i)
  → (∀ i j, i < n → j < n → i ≠ j → f i j ≠ 0%F)
  → ∀ i j, i < n → j < n →
    ((if ff_app σ i <? ff_app σ j then f i j else 1) /
      (if i <? j then f i j else 1) *
     ((if ff_app σ j <? ff_app σ i then f j i else 1) /
      (if j <? i then f j i else 1)))%F = 1%F.
Proof.
intros * Hic Hin H10 Hp Hn Hfij Hfijnz * Hlin Hljn.
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
  apply Hp in H1; [ flia H1 H3 | now rewrite Hn | now rewrite Hn ].
}
destruct (lt_dec j i) as [H4| H4]. {
  apply Hp in H1; [ flia H1 H4 | now rewrite Hn | now rewrite Hn ].
}
rewrite rngl_div_1_r; [ | now left | easy ].
apply rngl_mul_1_l.
Qed.

Theorem product_product_if_permut_div :
  rngl_is_comm = true →
  rngl_has_1_neq_0 = true →
  rngl_has_inv = true →
  ∀ n σ f,
  is_permut_list σ
  → length σ = n
  → (∀ i j, f i j = f j i)
  → (∀ i j, i < n → j < n → i ≠ j → f i j ≠ 0%F)
  → (∏ (i ∈ seq 0 n), ∏ (j ∈ seq 0 n),
      ((if ff_app σ i <? ff_app σ j then f i j else 1) /
       (if i <? j then f i j else 1)))%F =
     1%F.
Proof.
intros Hic H10 Hin * Hp Hn Hfij Hfijnz.
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
  rngl_has_dec_eq = true →
  ∀ n σ f,
  is_permut_list σ
  → length σ = n
  → (∀ i j, f i j = f j i)
  → (∀ i j, i < n → j < n → i ≠ j → f i j ≠ 0%F)
  → (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n),
        if ff_app σ i <? ff_app σ j then f i j else 1))%F =
    (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n),
        if i <? j then f i j else 1))%F.
Proof.
intros Hom Hic Hid Hin H10 Hed * Hp Hn Hfij Hfijnz.
apply rngl_product_product_div_eq_1; try easy. {
  intros i j Hi Hj.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec i j) as [Hij| Hij]; [ | now apply rngl_1_neq_0 ].
  apply Hfijnz; [ easy | easy | flia Hij ].
}
now apply product_product_if_permut_div.
Qed.

Theorem ε_ws_ε :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n (p : list nat),
  is_permut_list p
  → length p = n
  → ε n p = ε_ws n p.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hp Hpn.
unfold ε, ε_ws, δ.
do 3 rewrite rngl_product_product_if.
rewrite <- rngl_product_div_distr; try easy; [ | now left | ]. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite rngl_of_nat_sub; [ | now left | flia Hj ].
    easy.
  }
  cbn.
  destruct (Nat.eq_dec i n) as [Hein| Hein]. {
    subst i.
    rewrite rngl_product_empty; [ now apply rngl_1_neq_0 | flia ].
  }
  rewrite rngl_product_shift; [ | flia Hi Hein ].
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    replace (i + 1 + j - i) with (S j) by flia.
    easy.
  }
  cbn - [ rngl_of_nat ].
  erewrite <- rngl_product_succ_succ.
  replace (S (n - (i + 1))) with (n - i) by flia Hi Hein.
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
  apply rngl_sub_move_0_r in H; [ | easy ].
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
      rewrite if_ltb_lt_dec.
      destruct (lt_dec i j) as [H| H]; [ easy | flia Hj H ].
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
rewrite <- rngl_mul_1_r; f_equal.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite fold_rngl_div; [ | easy ].
    easy.
  }
  cbn.
  rewrite rngl_product_div_distr; try easy; [ now left | ].
  intros j Hj.
  intros H.
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  flia Hj H.
}
cbn.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  rewrite rngl_product_empty; [ easy | ].
  now apply Nat.lt_1_r.
}
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  replace n with (S (n - 1)) at 1 2 by flia Hnz.
  rewrite Nat.add_1_r at 1 2.
  rewrite rngl_product_succ_succ.
  rewrite rngl_product_succ_succ.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    now rewrite Nat_sub_succ_1.
  }
  cbn - [ "-" ].
  easy.
}
cbn - [ "-" ].
erewrite rngl_product_shift; [ | flia Hnz ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite (Nat.add_comm 1).
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite Nat.add_sub.
    easy.
  }
  remember (iter_seq _ _ _ _) as x.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    now rewrite Nat.add_1_r, Nat.sub_succ.
  }
  subst x.
  easy.
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
(* changt de var *)
rewrite rngl_product_change_var with
  (g := ff_app (permut_list_inv p)) (h := ff_app p). 2: {
  intros i Hi.
  destruct Hp as (Hp1, Hp2).
  apply (permut_inv_permut n); [ easy | flia Hi Hnz ].
}
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1.
rewrite <- Hpn.
rewrite <- List_map_ff_app_seq.
rewrite Hpn.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_change_var with
    (g := ff_app (permut_list_inv p)) (h := ff_app p). 2: {
    intros j Hj.
    destruct Hp as (Hp1, Hp2).
    apply (permut_inv_permut n); [ easy | flia Hj Hnz ].
  }
  rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
  rewrite Nat_sub_succ_1, Nat.sub_0_r.
  rewrite <- Hpn at 1.
  rewrite <- List_map_ff_app_seq.
  apply (In_nth _ _ 0) in Hi.
  destruct Hi as (u & Hu & Hui).
  rewrite Hpn in Hu.
  replace (ff_app _ (ff_app _ i)) with i. 2: {
    symmetry.
    apply (permut_permut_inv n); [ easy | ].
    rewrite <- Hui, <- Hpn.
    apply permut_list_ub; [ easy | now rewrite Hpn ].
  }
  erewrite rngl_product_list_eq_compat. 2: {
    intros j Hj.
    apply (In_nth _ _ 0) in Hj.
    destruct Hj as (v & Hv & Hvj).
    rewrite Hpn in Hv.
    replace (ff_app _ (ff_app _ j)) with j. 2: {
      symmetry.
      apply (permut_permut_inv n); [ easy | ].
      rewrite <- Hvj, <- Hpn.
      apply permut_list_ub; [ easy | now rewrite Hpn ].
    }
    easy.
  }
  cbn - [ "<?" ].
  easy.
}
cbn - [ "<?" ].
rewrite rngl_product_list_permut with (l2 := seq 0 n); [ | easy | ]. 2: {
  now apply permut_list_Permutation.
}
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_change_list with (lb := seq 0 n); [ | easy | ]. 2: {
    now apply permut_list_Permutation.
  }
  easy.
}
cbn - [ "<?" ].
rewrite product_product_if_permut; try easy; cycle 1. {
  now left.
} {
  now apply permut_list_inv_is_permut.
} {
  now rewrite length_permut_list_inv.
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
rewrite rngl_product_seq_product; [ | easy ].
rewrite Nat.add_0_l.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_seq_product; [ | easy ].
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

Definition permut_fun_swap (p q : nat) (σ : nat → nat) :=
  λ i, σ (transposition p q i).

(*
Definition permut_swap {n} (p q : nat) (σ : vector nat) :=
  mk_vect n (permut_fun_swap p q (vect_el σ)).
*)

Definition list_swap p q l :=
  map (λ i, nth (transposition p q i) l 0) (seq 0 (length l)).

Theorem length_list_swap : ∀ p q l, length (list_swap p q l) = length l.
Proof.
intros.
unfold list_swap.
now rewrite map_length, seq_length.
Qed.

Theorem permut_swap_fun_is_permut : ∀ p q σ n,
  p < n
  → q < n
  → is_permut_list σ
  → length σ = n
  → is_permut_list (list_swap p q σ).
Proof.
intros * Hp Hq Hσ Hn.
unfold list_swap.
rewrite <- Hn in Hp, Hq.
split. {
  intros x Hx.
  apply in_map_iff in Hx.
  destruct Hx as (i & Hix & Hi).
  apply in_seq in Hi.
  rewrite map_length, seq_length.
  rewrite <- Hix.
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec i p) as [Hip| Hip]; [ now apply Hσ, nth_In | ].
  destruct (Nat.eq_dec i q) as [Hiq| Hiq]; [ now apply Hσ, nth_In | ].
  now apply Hσ, nth_In.
} {
  rewrite map_length, seq_length.
  intros i j Hi Hj Hs.
  unfold ff_app in Hs.
  rewrite (List_map_nth' 0) in Hs; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hs; [ | now rewrite seq_length ].
  rewrite seq_nth in Hs; [ | easy ].
  rewrite seq_nth in Hs; [ | easy ].
  cbn in Hs.
  unfold transposition in Hs.
  do 4 rewrite if_eqb_eq_dec in Hs.
  destruct (Nat.eq_dec i p) as [Hip| Hip]. {
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ congruence | ].
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]. {
      apply Hσ in Hs; [ congruence | easy | easy ].
    } {
      apply Hσ in Hs; [ congruence | easy | easy ].
    }
  }
  destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]. {
      apply Hσ in Hs; [ congruence | easy | easy ].
    }
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]. {
      apply Hσ in Hs; [ congruence | easy | easy ].
    }
    apply Hσ in Hs; [ congruence | easy | easy ].
  }
  destruct (Nat.eq_dec j p) as [Hjp| Hjp]. {
    apply Hσ in Hs; [ congruence | easy | easy ].
  }
  destruct (Nat.eq_dec j q) as [Hjq| Hjq]. {
    apply Hσ in Hs; [ congruence | easy | easy ].
  }
  apply Hσ in Hs; [ congruence | easy | easy ].
}
Qed.

Theorem permut_list_swap_is_permut : ∀ p q n l,
  n = length l
  → p < n
  → q < n
  → is_permut_list l
  → is_permut_list (list_swap p q l).
Proof.
intros * Hn Hp Hq Hpl.
rewrite Hn in Hp, Hq.
split. {
  intros j Hj.
  unfold list_swap in Hj |-*.
  apply in_map_iff in Hj.
  destruct Hj as (i & Hij & Hi).
  apply in_seq in Hi.
  rewrite map_length, seq_length.
  rewrite <- Hij.
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec i p) as [Hip| Hip]; [ now apply Hpl, nth_In | ].
  now destruct (Nat.eq_dec i q); apply Hpl, nth_In.
} {
  intros i j Hi Hj Hs.
  rewrite length_list_swap in Hi, Hj.
  unfold list_swap in Hs.
  unfold ff_app in Hs.
  rewrite (List_map_nth' 0) in Hs; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hs; [ | now rewrite seq_length ].
  rewrite seq_nth in Hs; [ | easy ].
  rewrite seq_nth in Hs; [ | easy ].
  cbn in Hs.
  unfold transposition in Hs.
  do 4 rewrite if_eqb_eq_dec in Hs.
  apply Hpl; [ easy | easy | ].
  destruct (Nat.eq_dec i p) as [Hip| Hip]. {
    subst i.
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ congruence | ].
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ now subst j | ].
    now symmetry in Hs; apply Hpl in Hs.
  }
  destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
    subst i.
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ now subst j | ].
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ congruence | ].
    apply Hpl in Hs; [ | easy | easy ].
    now symmetry in Hs.
  }
  destruct (Nat.eq_dec j p) as [Hjp| Hjp]. {
    now subst j; apply Hpl in Hs.
  }
  destruct (Nat.eq_dec j q) as [Hjq| Hjq]. {
    now subst j; apply Hpl in Hs.
  }
  easy.
}
Qed.

(*
Theorem transposition_is_permut_vect : ∀ n p q,
  p < n
  → q < n
  → is_permut_vect (mk_vect (transposition p q)).
Proof.
intros.
now apply transposition_is_permut.
Qed.
*)

(*
Theorem is_permut_map : ∀ f n,
  is_permut_fun f n
  → is_permut_fun (λ i, nth i (map f (seq 0 n)) 0) n.
Theorem is_permut_map : ∀ f n,
  is_permut_fun f n
  → is_permut_fun (λ i, nth i (map f (seq 0 n)) 0) n.
Proof.
intros * Hf.
destruct Hf as (Hf, Hff).
split. {
  intros i Hi.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  now apply Hf.
} {
  intros i j Hi Hj Hij.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  now apply Hff.
}
Qed.
*)

Theorem transposition_signature_lt :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n p q,
  p < q
  → q < n
  → ε n (map (transposition p q) (seq 0 n)) = (-1)%F.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hpq Hq.
rewrite ε_ws_ε; try easy; [ | | now rewrite map_length, seq_length ]. 2: {
  split; cbn. {
    intros x Hx.
    rewrite map_length, seq_length.
    apply in_map_iff in Hx.
    destruct Hx as (y & Hyx & Hy).
    apply in_seq in Hy.
    rewrite <- Hyx.
    apply transposition_lt; [ flia Hpq Hq | easy | easy ].
  }
  rewrite map_length, seq_length.
  intros i j Hi Hj Hij.
  unfold ff_app in Hij.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  cbn in Hij.
  unfold transposition in Hij.
  do 4 rewrite if_eqb_eq_dec in Hij.
  destruct (Nat.eq_dec i p) as [Hip| Hip]. {
    subst i.
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ easy | ].
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ flia Hpq Hij | ].
    now symmetry in Hij.
  }
  destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
    subst i.
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ flia Hpq Hij | ].
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ easy | ].
    now symmetry in Hij.
  }
  destruct (Nat.eq_dec j p) as [H| H]; [ easy | clear H ].
  now destruct (Nat.eq_dec j q).
}
unfold ε_ws; cbn - [ "<?" ].
unfold sign_diff.
rewrite rngl_product_shift; [ | flia Hq ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_shift; [ | flia Hq ].
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite (Nat.add_comm 1 j), Nat.add_sub.
    rewrite (Nat.add_comm 1 i), Nat.add_sub.
    rewrite Nat_ltb_mono_r.
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hi Hq ].
    rewrite seq_nth; [ | flia Hi Hq ].
    rewrite Nat.add_0_l.
    rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hj Hq ].
    rewrite seq_nth; [ | flia Hj Hq ].
    rewrite Nat.add_0_l.
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
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec (i - 1) j) as [Hij| Hij]; [ | easy ].
  destruct (lt_dec (transposition p q (i - 1)) (transposition p q j))
    as [Htij| Htij]; [ easy | ].
  exfalso; apply Htij; clear Htij.
  rewrite transposition_out; [ | flia Hi | flia Hpq Hi ].
  unfold transposition.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ flia Hpq Hi | ].
  destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ flia Hpq Hi | easy ].
}
rewrite rngl_mul_1_l.
rewrite transposition_1.
rewrite (rngl_product_split3 p); [ | flia Hpq Hq ].
rewrite if_ltb_lt_dec.
destruct (lt_dec p p) as [H| H]; [ flia H | clear H ].
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
  easy.
}
cbn - [ "<?" ].
rewrite <- rngl_product_mul_distr; [ | easy ].
rewrite (rngl_product_split3 q); [ | flia Hpq Hq ].
rewrite transposition_2.
rewrite if_ltb_lt_dec.
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
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec p i) as [H| H]; [ clear H | flia Hpq Hi H ].
  rewrite rngl_mul_1_l.
  destruct (lt_dec q i) as [H| H]; [ clear H | flia Hi H ].
  rewrite rngl_mul_1_l.
  apply all_1_rngl_product_1.
  intros j Hj.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
  rewrite transposition_out; [ | flia Hpq Hi Hij | flia Hi Hij ].
  rewrite if_ltb_lt_dec.
  now destruct (lt_dec i j).
}
rewrite rngl_mul_1_l.
rewrite all_1_rngl_product_1; [ apply rngl_mul_1_l | ].
intros i Hi.
rewrite transposition_out; [ | flia Hi | flia Hi ].
rewrite if_ltb_lt_dec.
destruct (lt_dec q (i - 1)) as [H| H]; [ flia Hi H | clear H ].
rewrite (rngl_product_split3 p); [ | flia Hp ].
rewrite transposition_1.
rewrite if_ltb_lt_dec.
destruct (lt_dec (i - 1) p) as [H| H]; [ flia Hi H | clear H ].
rewrite rngl_mul_1_r.
rewrite all_1_rngl_product_1. 2: {
  intros j Hj.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec (i - 1) (j - 1)) as [H| H]; [ flia Hi Hj H | easy ].
}
rewrite rngl_mul_1_l.
rewrite (rngl_product_split3 q); [ | flia Hpq Hq ].
rewrite if_ltb_lt_dec.
destruct (lt_dec (i - 1) q) as [H| H]; [ clear H | flia Hi H ].
rewrite transposition_2.
rewrite if_ltb_lt_dec.
destruct (lt_dec (i - 1) p) as [H| H]; [ flia Hi H | clear H ].
rewrite rngl_mul_mul_swap; [ | easy ].
rewrite rngl_mul_comm; [ | easy ].
rewrite <- rngl_mul_assoc.
rewrite rngl_sqr_opp_1; [ | easy ].
rewrite rngl_mul_1_r.
rewrite (all_1_rngl_product_1 (q + 1)). 2: {
  intros j Hj.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec (i - 1) j) as [H| H]; [ clear H | flia Hi Hj H ].
  rewrite transposition_out; [ | flia Hpq Hj | flia Hj ].
  rewrite if_ltb_lt_dec.
  destruct (lt_dec (i - 1) j) as [H| H]; [ easy | flia Hi Hj H ].
}
rewrite rngl_mul_1_r.
apply all_1_rngl_product_1.
intros j Hj.
rewrite transposition_out; [ | flia Hj | flia Hj ].
do 2 rewrite if_ltb_lt_dec.
now destruct (lt_dec (i - 1) (j - 1)).
Qed.

Theorem transposition_signature :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n p q,
  p ≠ q
  → p < n
  → q < n
  → ε n (map (transposition p q) (seq 0 n)) = (-1)%F.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hpq Hp Hq.
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

(* ε (σ₁ ° σ₂) = ε σ₁ * ε σ₂ *)

Theorem signature_comp_fun_expand_1 :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f g,
  is_permut_list g
  → length g = n
  → (∏ (i = 1, n),
        (∏ (j = 1, n),
         δ i j (ff_app f (ff_app g (i - 1)))
           (ff_app f (ff_app g (j - 1)))) /
      ∏ (i = 1, n),
        (∏ (j = 1, n),
         δ i j (ff_app g (i - 1)) (ff_app g (j - 1))))%F =
    (∏ (i = 1, n),
       (∏ (j = 1, n), δ i j (ff_app f (i - 1)) (ff_app f (j - 1))) /
      ∏ (i = 1, n), (∏ (j = 1, n), δ i j i j))%F
  → ε n (f ° g) = (ε n f * ε n g)%F.
Proof.
intros Hop Hin H10 Hit Hch * Hp2 Hn Hs.
unfold ε, comp_list; cbn.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    unfold ff_app.
    rewrite (List_map_nth' 0); [ | flia Hi Hn ].
    rewrite (List_map_nth' 0); [ | flia Hj Hn ].
    easy.
  }
  easy.
}
rewrite <- Hs; symmetry.
apply rngl_div_mul_div; [ easy | ].
intros Hij.
apply rngl_product_integral in Hij; [ | now left | easy | easy ].
destruct Hij as (i & Hi & Hij).
apply rngl_product_integral in Hij; [ | now left | easy | easy ].
destruct Hij as (j & Hj & Hij).
unfold δ in Hij.
rewrite if_ltb_lt_dec in Hij.
destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 ].
apply rngl_sub_move_0_r in Hij; [ | easy ].
apply rngl_of_nat_inj in Hij; [ | now left | easy ].
destruct Hp2 as (Hp21, Hp22).
rewrite <- Hn in Hi, Hj.
apply Hp22 in Hij; [ flia Hi Hj Hlij Hij | flia Hj | flia Hi ].
Qed.

Theorem signature_comp_fun_expand_2_1 :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_is_comm = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f g,
  is_permut_list g
  → length g = n
  → (∏ (i = 1, n),
      (∏ (j = 1, n),
       δ i j (ff_app f (ff_app g (i - 1)))
         (ff_app f (ff_app g (j - 1)))) /
     ∏ (i = 1, n),
      (∏ (j = 1, n), δ i j (ff_app g (i - 1)) (ff_app g (j - 1))))%F =
    (∏ (i = 1, n),
      (∏ (j = 1, n),
       (if i <? j then
         (rngl_of_nat (ff_app f (ff_app g (j - 1))) -
          rngl_of_nat (ff_app f (ff_app g (i - 1)))) /
         (rngl_of_nat (ff_app g (j - 1)) - rngl_of_nat (ff_app g (i - 1)))
       else 1)))%F.
Proof.
intros Hop Hin Hic H10 Hit Hch * Hp2 Hn.
unfold rngl_div; rewrite Hin.
rewrite rngl_inv_product_comm; [ | | easy | easy | easy | easy | ]; cycle 1. {
  now left.
} {
  intros i Hi Hij.
  apply rngl_product_integral in Hij; [ | now left | easy | easy ].
  destruct Hij as (j & Hj & Hij).
  rewrite <- Hn in Hi, Hj.
  unfold δ in Hij.
  rewrite if_ltb_lt_dec in Hij.
  destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 in Hij ].
  apply rngl_sub_move_0_r in Hij; [ | easy ].
  apply rngl_of_nat_inj in Hij; [ | now left | easy ].
  apply Hp2 in Hij; [ flia Hi Hj Hlij Hij | flia Hj | flia Hi ].
}
erewrite <- rngl_product_mul_distr; [ | easy ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_inv_product_comm;
      [ | now left | easy | easy | easy | easy | ]. 2: {
    intros j Hj Hij.
    rewrite <- Hn in Hi, Hj.
    unfold δ in Hij.
    rewrite if_ltb_lt_dec in Hij.
    destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 in Hij ].
    apply rngl_sub_move_0_r in Hij; [ | easy ].
    apply rngl_of_nat_inj in Hij; [ | now left | easy ].
    apply Hp2 in Hij; [ flia Hi Hj Hlij Hij | flia Hj | flia Hi ].
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
    unfold δ.
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
  (∏ (i = 1, n), (∏ (j = 1, n), δ i j (f (i - 1)%nat) (f (j - 1)%nat)) /
   ∏ (i = 1, n), (∏ (j = 1, n), δ i j i j))%F =
  (∏ (i = 1, n),
   (∏ (j = 1, n),
    (if i <? j then
      (rngl_of_nat (f (j - 1)%nat) - rngl_of_nat (f (i - 1)%nat)) /
      rngl_of_nat (j - i)
     else 1)))%F.
Proof.
intros Hop Hin Hic H10 Hit Hch *.
unfold rngl_div; rewrite Hin.
rewrite rngl_inv_product_comm; [ | now left | easy | easy | easy | easy | ]. 2: {
  intros i Hi Hij.
  apply rngl_product_integral in Hij; [ | now left | easy | easy ].
  destruct Hij as (j & Hj & Hij).
  unfold δ in Hij.
  rewrite if_ltb_lt_dec in Hij.
  destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 in Hij ].
  apply rngl_sub_move_0_r in Hij; [ | easy ].
  apply rngl_of_nat_inj in Hij; [ | now left | easy ].
  flia Hlij Hij.
}
erewrite <- rngl_product_mul_distr; [ | easy ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_inv_product_comm; [ | now left | easy | easy | easy | easy | ]. 2: {
    intros j Hj Hij.
    unfold δ in Hij.
    rewrite if_ltb_lt_dec in Hij.
    destruct (lt_dec i j) as [Hlij| Hlij]; [ | now apply rngl_1_neq_0 in Hij ].
    apply rngl_sub_move_0_r in Hij; [ | easy ].
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
    unfold δ.
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
apply rngl_of_nat_sub; [ now left | easy ].
Qed.

Theorem signature_comp_fun_changement_of_variable :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_is_comm = true →
  rngl_has_dec_eq = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f g,
  is_permut_list f
  → is_permut_list g
  → length f = n
  → length g = n
  → (∏ (i = 1, n),
     (∏ (j = 1, n),
      (if i <? j then
         (rngl_of_nat (ff_app f (ff_app g (j - 1))) -
          rngl_of_nat (ff_app f (ff_app g (i - 1)))) /
         (rngl_of_nat (ff_app g (j - 1)) - rngl_of_nat (ff_app g (i - 1)))
       else 1)))%F =
    (∏ (i = 1, n),
     (∏ (j = 1, n),
      (if i <? j then
         (rngl_of_nat (ff_app f (j - 1)) - rngl_of_nat (ff_app f (i - 1))) /
         rngl_of_nat (j - i)
       else 1)))%F.
Proof.
intros Hop Hin Hic Hde H10 Hit Hch * Hp1 Hp2 Hn1 Hn2.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now move Hnz at top; subst n | ].
rewrite rngl_product_shift; [ | flia Hnz ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    now rewrite (Nat.add_comm 1), Nat.add_sub.
  }
  easy.
}
cbn - [ "<?" ].
rewrite rngl_product_change_var with
    (g := ff_app (permut_list_inv g)) (h := ff_app g). 2: {
  intros i Hi.
  apply (permut_inv_permut n); [ easy | flia Hi Hnz ].
}
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1, Nat.sub_0_r.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_shift; [ | flia Hnz ].
  rewrite rngl_product_change_var with
      (g := ff_app (permut_list_inv g)) (h := ff_app g). 2: {
    intros j Hj.
    apply (permut_inv_permut n); [ easy | flia Hj Hnz ].
  }
  rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
  rewrite Nat_sub_succ_1, Nat.sub_0_r.
  erewrite rngl_product_list_eq_compat. 2: {
    intros j Hj.
    rewrite (Nat.add_comm _ 1).
    rewrite Nat_ltb_mono_l.
    rewrite (permut_permut_inv n); [ | easy | ]. 2: {
      apply in_map_iff in Hi.
      destruct Hi as (k & Hk & Hkn).
      apply in_seq in Hkn.
      rewrite <- Hk, <- Hn2.
      apply Hp2, nth_In.
      now rewrite Hn2.
    }
    rewrite Nat.add_comm, Nat.add_sub.
    rewrite (permut_permut_inv n); [ | easy | ]. 2: {
      apply in_map_iff in Hj.
      destruct Hj as (k & Hk & Hkn).
      apply in_seq in Hkn.
      rewrite <- Hk, <- Hn2.
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
  erewrite rngl_product_change_list; [ | easy | ]. 2: {
    now apply permut_list_Permutation.
  }
  easy.
}
cbn - [ "<?" ].
erewrite rngl_product_change_list; [ | easy | ]. 2: {
  rewrite <- Hn2 at 1.
  rewrite <- List_map_ff_app_seq.
  now apply permut_list_Permutation.
}
symmetry.
rewrite rngl_product_shift; [ | flia Hnz ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_shift; [ | flia Hnz ].
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite Nat_ltb_mono_l.
    rewrite Nat.add_comm, Nat.add_sub.
    rewrite Nat.add_comm, Nat.add_sub.
    do 2 rewrite Nat.add_1_r.
    cbn - [ "<?" ].
    easy.
  }
  easy.
}
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
  apply rngl_of_nat_sub; [ now left | easy ].
} {
  now left.
} {
  now apply permut_list_inv_is_permut.
} {
  now rewrite length_permut_list_inv.
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
    apply rngl_sub_move_0_r in H; [ | easy ].
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
    apply rngl_sub_move_0_r in H; [ | easy ].
    apply rngl_of_nat_inj in H; [ | now left | easy ].
    apply Hij; symmetry.
    rewrite <- Hn1 in Hi, Hj.
    now apply Hp1 in H.
  } {
    revert H.
    apply rngl_inv_neq_0; [ now left | easy | easy | ].
    intros H.
    apply rngl_sub_move_0_r in H; [ | easy ].
    apply rngl_of_nat_inj in H; [ | now left | easy ].
    now apply Hij; symmetry.
  }
}
Qed.

Theorem signature_comp :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_is_comm = true →
  rngl_has_dec_eq = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f g,
  is_permut n f
  → is_permut n g
  → ε n (f ° g) = (ε n f * ε n g)%F.
Proof.
intros Hop Hin Hic Hde H10 Hit Hch * Hpf Hpg.
destruct Hpf as (Hp11, Hpf2).
destruct Hpg as (Hpg1, Hpg2).
apply signature_comp_fun_expand_1; try easy.
rewrite signature_comp_fun_expand_2_1; try easy.
rewrite signature_comp_fun_expand_2_2; try easy.
now apply signature_comp_fun_changement_of_variable.
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

Theorem transposition_injective : ∀ p q i j,
  transposition p q i = transposition p q j
  → i = j.
Proof.
intros * Hpq.
apply (f_equal (transposition p q)) in Hpq.
now do 2 rewrite transposition_involutive in Hpq.
Qed.

(*
Theorem swap_elem_involutive : ∀ f p q,
  swap_elem (swap_elem f p q) p q = f.
Proof.
intros.
Print fin_fun_ext.
Theorem my_false : ∀ A (f g : nat → A), f = g.
Proof.
intros.
apply fin_fun_ext with (n := 0).
easy.
Print fin_fun_ext.
...
apply fin_fun_ext with (n := n).
intros i Hi.
unfold swap_elem.
rewrite transposition_involutive.
...
apply vector_eq.
intros i Hi; cbn.
unfold swap_elem.
now rewrite transposition_involutive.
Qed.
*)

(*
Theorem vect_swap_elem_injective : ∀ (u v : vector nat) p q,
  vect_swap_elem u p q = vect_swap_elem v p q
  → u = v.
Proof.
intros * Huv.
apply (f_equal (λ u, vect_swap_elem u p q)) in Huv.
now do 2 rewrite vect_swap_elem_involutive in Huv.
Qed.
*)

(* i such that vect_el (permut n k) i = j *)

(*
Definition sym_gr_elem_swap_with_0 p n k :=
  vect_swap_elem (vect_el (canon_sym_gr n) k) 0 p.
*)

(* k' such that permut_swap_with_0 p n k = permut n k' *)

...

Definition sym_gr_elem_swap_last (p q : nat) n k :=
  vect_swap_elem 0
    (vect_swap_elem 0 (vect_vect_nat_el (canon_sym_gr n) k) p (n - 2))
    q (n - 1).

(* *)

Theorem ε_permut_succ : ∀ n k,
  k < fact (S n)
  → ε_permut (S n) k =
     (minus_one_pow (k / fact n) * ε_permut n (k mod fact n))%F.
Proof. easy. Qed.

Theorem sym_gr_succ_values : ∀ n k σ σ',
  σ = canon_sym_gr_fun n (canon_sym_gr_elem n) k
  → σ' = canon_sym_gr_elem n (k mod n!)
  → ∀ i,
    σ i =
    match i with
    | 0 => k / fact n
    | S i' => if σ' i' <? k / fact n then σ' i' else σ' i' + 1
    end.
Proof.
intros * Hσ Hσ' i.
destruct i; [ now subst σ | ].
subst σ; cbn - [ "<?" ].
subst σ'; cbn - [ "<?" ].
rewrite Nat.leb_antisym.
unfold Nat.b2n.
rewrite if_ltb_lt_dec.
rewrite negb_if.
rewrite if_ltb_lt_dec.
destruct (lt_dec _ _) as [H1| H1]; [ | easy ].
apply Nat.add_0_r.
Qed.

Theorem sym_gr_vect_succ_values : ∀ (n k : nat) (σ σ' : nat → nat),
  k < (S n)!
  → σ = vect_el 0 (vect_vect_nat_el (canon_sym_gr (S n)) k)
  → σ' = vect_el 0 (vect_vect_nat_el (canon_sym_gr n) (k mod n!))
  → ∀ i : nat, i < S n →
    σ i =
      match i with
      | 0 => k / n!
      | S i' => if σ' i' <? k / n! then σ' i' else σ' i' + 1
      end.
Proof.
intros * Hkn Hσ Hσ' i Hin.
unfold canon_sym_gr in Hσ.
cbn - [ map fact seq ] in Hσ.
rewrite (List_map_nth' 0) in Hσ; [ | now rewrite seq_length ].
rewrite seq_nth in Hσ; [ | easy ].
rewrite Nat.add_0_l in Hσ.
rewrite Hσ.
unfold vect_el.
cbn - [ "<?" nth seq ].
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
rewrite Nat.add_0_l.
destruct i; [ easy | ].
subst σ; cbn - [ "<?" ].
subst σ'; cbn - [ "<?" ].
rewrite Nat.leb_antisym.
unfold Nat.b2n.
rewrite if_ltb_lt_dec.
rewrite negb_if.
rewrite if_ltb_lt_dec.
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  apply Nat.mod_upper_bound, fact_neq_0.
}
cbn - [ fact map seq "<?" ].
rewrite (List_map_nth' 0); [ | rewrite seq_length; flia Hin ].
rewrite seq_nth; [ | apply Nat.mod_upper_bound, fact_neq_0 ].
rewrite seq_nth; [ | flia Hin ].
do 2 rewrite Nat.add_0_l.
destruct (lt_dec _ _); [ apply Nat.add_0_r | easy ].
Qed.

(* equality of ε of sym_gr elem and ε_permut *)

Theorem ε_of_sym_gr_permut_succ :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n k,
  k < (S n)!
  → ε (S n) (vect_vect_nat_el (canon_sym_gr (S n)) k) =
    (minus_one_pow (k / n!) *
     ε n (vect_vect_nat_el (canon_sym_gr n) (k mod n!)))%F.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hkn.
rewrite ε_ws_ε; try easy; [ | now apply mk_canon_is_permut_vect ].
unfold ε_ws, ε_fun_ws.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  unfold ε, ε_fun.
  subst n.
  apply Nat.lt_1_r in Hkn.
  subst k; cbn.
  unfold iter_seq, iter_list; cbn.
  repeat rewrite rngl_mul_1_l.
  rewrite rngl_div_1_l; [ | easy ].
  now symmetry; apply rngl_inv_1.
}
rewrite rngl_product_succ_succ.
rewrite rngl_product_split_first; [ | flia ].
rewrite Nat.sub_diag.
f_equal. {
  rewrite rngl_product_shift; [ | flia ].
  rewrite Nat_sub_succ_1.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    replace (1 <? 1 + i) with (0 <? i) by easy.
    rewrite Nat.add_comm, Nat.add_sub.
    easy.
  }
  cbn - [ "<?" canon_sym_gr ].
  rewrite rngl_product_split_first; [ | flia ].
  replace (0 <? 0) with false by easy.
  rewrite rngl_mul_1_l.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec 0 i) as [H| H]; [ clear H | flia Hi H ].
    easy.
  }
  cbn - [ canon_sym_gr ].
  remember (vect_el 0 (vect_vect_nat_el (canon_sym_gr (S n)) k))
    as σ eqn:Hσ.
  remember
    (vect_el 0 (vect_vect_nat_el (canon_sym_gr n) (k mod n!)))
    as σ' eqn:Hσ'.
  specialize (sym_gr_vect_succ_values Hkn Hσ Hσ') as H1.
  unfold sign_diff.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite H1; [ | flia ].
    easy.
  }
  cbn - [ "<?" ].
  rewrite rngl_product_shift; [ | flia Hnz ].
  remember (k / fact n) as x eqn:Hx.
  erewrite rngl_product_eq_compat. 2: {
    intros i (_, Hi).
    replace (if x <? _ then _ else _) with
      (if x <? σ' i + 1 then 1%F else (-1)%F). 2: {
      rewrite (Nat.add_1_l i).
      rewrite H1; [ | flia Hi Hnz ].
      do 3 rewrite if_ltb_lt_dec.
      destruct (lt_dec (σ' i) x) as [H2| H2]; [ | easy ].
      destruct (lt_dec x (σ' i)) as [H| H]; [ flia H H2 | clear H ].
      destruct (lt_dec x (σ' i + 1)) as [H3| H3]; [ | easy ].
      flia H2 H3.
    }
    easy.
  }
  cbn - [ "<?" ].
  assert (Hp' : is_permut_fun σ' n). {
    rewrite Hσ'.
    apply mk_canon_is_permut_vect.
    apply Nat.mod_upper_bound, fact_neq_0.
  }
  assert (Hp : is_permut_fun σ (S n)). {
    rewrite Hσ.
    now apply mk_canon_is_permut_vect.
  }
  rewrite rngl_product_change_var with (g := permut_fun_inv_loop σ' n) (h := σ').
  2: {
    intros i (_, Hi).
    apply fun_find_prop; [ | flia Hnz Hi ].
    apply Hp'.
  }
  rewrite Nat.sub_0_r.
  rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
  rewrite Nat_sub_succ_1.
  erewrite rngl_product_list_eq_compat. 2: {
    intros i Hi.
    apply in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj).
    apply in_seq in Hj.
    rewrite fun_permut_fun_inv_loop; [ easy | easy | ].
    now rewrite <- Hji; apply Hp'.
  }
  cbn - [ "<?" seq ].
  rewrite rngl_product_change_list with (lb := seq 0 n); [ | easy | ]. 2: {
    now apply permut_fun_Permutation.
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
    split; [ flia | ].
    apply -> Nat.succ_le_mono.
    enough (H : x < S n) by flia H Hnz.
    replace x with (σ 0). 2: {
      rewrite H1; [ easy | flia ].
    }
    apply Hp; flia.
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
  rewrite rngl_product_split_last; [ | flia ].
  rewrite rngl_product_shift; [ | flia ].
  rewrite Nat_sub_succ_1.
  rewrite IHx.
  symmetry.
  rewrite minus_one_pow_succ; [ | easy ].
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_opp_l; [ | easy ].
  now rewrite rngl_mul_1_l.
}
rewrite ε_ws_ε; try easy. 2: {
  apply mk_canon_is_permut_vect.
  apply Nat.mod_upper_bound.
  apply fact_neq_0.
}
unfold ε_ws, ε_fun_ws.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_succ_succ.
  rewrite rngl_product_split_first; [ | flia ].
  rewrite if_ltb_lt_dec.
  destruct (lt_dec (S i) 1) as [H| H]; [ flia H | clear H ].
  rewrite rngl_mul_1_l.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    replace (S i <? S j) with (i <? j) by easy.
    now do 2 rewrite Nat_sub_succ_1.
  }
  easy.
}
cbn - [ canon_sym_gr_elem "<?" fact map vect_vect_nat_el ].
apply rngl_product_eq_compat.
intros i Hi.
apply rngl_product_eq_compat.
intros j Hj.
move j before i.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
remember (vect_el 0 (vect_vect_nat_el (canon_sym_gr (S n)) k))
  as σ eqn:Hσ.
remember (vect_el 0 (vect_vect_nat_el (canon_sym_gr n) (k mod n!)))
  as σ' eqn:Hσ'.
rewrite (sym_gr_vect_succ_values Hkn Hσ Hσ'); [ | flia Hj ].
rewrite (sym_gr_vect_succ_values Hkn Hσ Hσ'); [ | flia Hi ].
destruct j; [ flia Hj | ].
destruct i; [ flia Hi | ].
rewrite Nat_sub_succ_1.
rewrite Nat_sub_succ_1.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec (σ' j) (k / fact n)) as [Hsfj| Hsfj]. {
  destruct (lt_dec (σ' i) (k / fact n)) as [Hsfi| Hsfi]; [ easy | ].
  unfold sign_diff.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec (σ' i + 1) (σ' j)) as [Hsi1j| Hsi1j]. {
    destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ easy | ].
    flia Hsi1j Hsij.
  }
  destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ | easy ].
  flia Hsij Hsfj Hsfi.
}
destruct (lt_dec (σ' i) (k / fact n)) as [Hsfi| Hsfi]. {
  unfold sign_diff.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec (σ' i) (σ' j + 1)) as [Hsi1j| Hsi1j]. {
    destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ easy | ].
    flia Hsij Hsfj Hsfi.
  }
  destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ | easy ].
  flia Hsi1j Hsij.
}
unfold sign_diff.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec (σ' i + 1) (σ' j + 1)) as [Hsi1j| Hsi1j]. {
  destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ easy | ].
  flia Hsi1j Hsij.
}
destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ | easy ].
flia Hsi1j Hsij.
Qed.

(*
Theorem ε_of_sym_gr_permut_succ :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n k,
  k < (S n)!
  → ε (vect_el (canon_sym_gr (S n)) k) =
    (minus_one_pow (k / n!) *
     ε (vect_el (canon_sym_gr n) (k mod n!)))%F.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hkn.
rewrite ε_ws_ε; try easy; [ | now apply sym_gr_elem_is_permut ].
unfold ε_ws, ε_fun_ws.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  unfold ε, ε_fun.
  subst n.
  apply Nat.lt_1_r in Hkn.
  subst k; cbn.
  unfold iter_seq, iter_list; cbn.
  repeat rewrite rngl_mul_1_l.
  rewrite rngl_div_1_l; [ | easy ].
  now symmetry; apply rngl_inv_1.
}
rewrite rngl_product_succ_succ.
rewrite rngl_product_split_first; [ | flia ].
rewrite Nat.sub_diag.
f_equal. {
  rewrite rngl_product_shift; [ | flia ].
  rewrite Nat_sub_succ_1.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    replace (1 <? 1 + i) with (0 <? i) by easy.
    rewrite Nat.add_comm, Nat.add_sub.
    easy.
  }
  cbn - [ "<?" canon_sym_gr_elem ].
  rewrite rngl_product_split_first; [ | flia ].
  replace (0 <? 0) with false by easy.
  rewrite rngl_mul_1_l.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec 0 i) as [H| H]; [ clear H | flia Hi H ].
    easy.
  }
  cbn - [ canon_sym_gr_elem ].
  remember (canon_sym_gr_elem (S n) k) as σ eqn:Hσ.
  remember (canon_sym_gr_elem n (k mod fact n)) as σ' eqn:Hσ'.
  specialize (sym_gr_succ_values Hσ Hσ') as H1.
  unfold sign_diff.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite H1.
    replace i with (S (i - 1)) at 1 by flia Hi.
    easy.
  }
  cbn - [ "<?" ].
  remember (k / fact n) as x eqn:Hx.
  erewrite rngl_product_eq_compat. 2: {
    intros i Hi.
    rewrite <- Nat.sub_succ_l; [ | easy ].
    rewrite Nat_sub_succ_1.
    rewrite H1.
    replace i with (S (i - 1)) at 1 by flia Hi.
    easy.
  }
  cbn - [ "<?" ].
  rewrite rngl_product_shift; [ | flia Hnz ].
  erewrite rngl_product_eq_compat. 2: {
    intros i (_, Hi).
    rewrite Nat.add_comm, Nat.add_sub.
    easy.
  }
  cbn - [ "<?" ].
  erewrite rngl_product_eq_compat. 2: {
    intros i (_, Hi).
    replace (if x <? _ then _ else _) with
      (if x <? σ' i + 1 then 1%F else (-1)%F). 2: {
      do 3 rewrite if_ltb_lt_dec.
      destruct (lt_dec (σ' i) x) as [H2| H2]; [ | easy ].
      destruct (lt_dec x (σ' i)) as [H| H]; [ flia H H2 | clear H ].
      destruct (lt_dec x (σ' i + 1)) as [H3| H3]; [ | easy ].
      flia H2 H3.
    }
    easy.
  }
  cbn - [ "<?" ].
  assert (Hp' : is_permut_fun σ' n). {
    rewrite Hσ'.
    apply sym_gr_elem_is_permut.
    apply Nat.mod_upper_bound.
    apply fact_neq_0.
  }
  assert (Hp : is_permut_fun σ (S n)). {
    rewrite Hσ.
    now apply sym_gr_elem_is_permut.
  }
  rewrite rngl_product_change_var with (g := permut_fun_inv_loop σ' n) (h := σ').
  2: {
    intros i (_, Hi).
    apply fun_find_prop; [ | flia Hnz Hi ].
    apply Hp'.
  }
  rewrite Nat.sub_0_r.
  rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
  rewrite Nat_sub_succ_1.
  erewrite rngl_product_list_eq_compat. 2: {
    intros i Hi.
    apply in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj).
    apply in_seq in Hj.
    rewrite fun_permut_fun_inv_loop; [ easy | easy | ].
    now rewrite <- Hji; apply Hp'.
  }
  cbn - [ "<?" seq ].
  rewrite rngl_product_change_list with (lb := seq 0 n); [ | easy | ]. 2: {
    now apply permut_fun_Permutation.
  }
  rewrite rngl_product_seq_product; [ | easy ].
  rewrite Nat.add_0_l.
  destruct (Nat.eq_dec x 0) as [Hxz| Hxz]. {
    move Hxz at top; subst x.
    cbn - [ "<?" ].
    apply all_1_rngl_product_1; [ easy | ].
    intros i (_, Hi).
    now rewrite Nat.add_comm.
  }
  rewrite (rngl_product_split (x - 1)). 2: {
    split; [ flia | ].
    apply -> Nat.succ_le_mono.
    enough (H : x < S n) by flia H Hnz.
    replace x with (σ 0) by now rewrite H1.
    apply Hp; flia.
  }
  remember (∏ (i = _, _), _)%F as y eqn:Hy.
  rewrite all_1_rngl_product_1; [ | easy | ]. 2: {
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
  rewrite rngl_product_split_last; [ | flia ].
  rewrite rngl_product_shift; [ | flia ].
  rewrite Nat_sub_succ_1.
  rewrite IHx.
  symmetry.
  rewrite minus_one_pow_succ; [ | easy ].
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_opp_l; [ | easy ].
  now rewrite rngl_mul_1_l.
}
rewrite ε_ws_ε; try easy. 2: {
  apply sym_gr_elem_is_permut.
  apply Nat.mod_upper_bound.
  apply fact_neq_0.
}
unfold ε_ws, ε_fun_ws.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_succ_succ.
  rewrite rngl_product_split_first; [ | flia ].
  rewrite if_ltb_lt_dec.
  destruct (lt_dec (S i) 1) as [H| H]; [ flia H | clear H ].
  rewrite rngl_mul_1_l.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    replace (S i <? S j) with (i <? j) by easy.
    now do 2 rewrite Nat_sub_succ_1.
  }
  easy.
}
cbn - [ canon_sym_gr_elem "<?" ].
apply rngl_product_eq_compat.
intros i Hi.
apply rngl_product_eq_compat.
intros j Hj.
move j before i.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
remember (canon_sym_gr_elem (S n) k) as σ eqn:Hσ.
remember (canon_sym_gr_elem n (k mod n!)) as σ' eqn:Hσ'.
move σ' before σ.
do 2 rewrite (sym_gr_succ_values Hσ Hσ').
destruct j; [ flia Hj | ].
destruct i; [ flia Hi | ].
rewrite Nat_sub_succ_1.
rewrite Nat_sub_succ_1.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec (σ' j) (k / fact n)) as [Hsfj| Hsfj]. {
  destruct (lt_dec (σ' i) (k / fact n)) as [Hsfi| Hsfi]; [ easy | ].
  unfold sign_diff.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec (σ' i + 1) (σ' j)) as [Hsi1j| Hsi1j]. {
    destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ easy | ].
    flia Hsi1j Hsij.
  }
  destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ | easy ].
  flia Hsij Hsfj Hsfi.
}
destruct (lt_dec (σ' i) (k / fact n)) as [Hsfi| Hsfi]. {
  unfold sign_diff.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec (σ' i) (σ' j + 1)) as [Hsi1j| Hsi1j]. {
    destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ easy | ].
    flia Hsij Hsfj Hsfi.
  }
  destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ | easy ].
  flia Hsi1j Hsij.
}
unfold sign_diff.
do 2 rewrite if_ltb_lt_dec.
destruct (lt_dec (σ' i + 1) (σ' j + 1)) as [Hsi1j| Hsi1j]. {
  destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ easy | ].
  flia Hsi1j Hsij.
}
destruct (lt_dec (σ' i) (σ' j)) as [Hsij| Hsij]; [ | easy ].
flia Hsi1j Hsij.
Qed.
*)

Theorem ε_of_permut_ε :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n k,
  k < fact n
  → ε n (vect_vect_nat_el (canon_sym_gr n) k) = ε_permut n k.
Proof.
intros Hic Hop Hin H10 Hit Hde Hch * Hkn.
revert k Hkn.
induction n; intros. {
  cbn; unfold ε, ε_fun; cbn.
  unfold iter_seq, iter_list; cbn.
  apply rngl_div_1_r; [ now left | easy ].
}
rewrite ε_of_sym_gr_permut_succ; try easy.
cbn.
f_equal.
apply IHn.
apply Nat.mod_upper_bound.
apply fact_neq_0.
Qed.

Theorem permut_vect_inv_is_permut : ∀ n (σ : vector nat),
  is_permut_vect n σ
  → is_permut_vect n (permut_vect_inv n σ).
Proof.
intros * (Hp1, Hp2).
specialize (permut_fun_inv_loop_is_permut Hp2) as H1.
split; [ now cbn; rewrite map_length, seq_length | ].
unfold permut_vect_inv, vect_el; cbn.
eapply is_permut_eq_compat. {
  intros i Hi.
  symmetry.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite Nat.add_0_l.
  easy.
}
easy.
Qed.

Theorem canon_sym_gr_inv_ub : ∀ n k j,
  k < fact n
  → j < n
  → canon_sym_gr_inv n k j < n.
Proof.
intros * Hkn Hjn.
revert k j Hkn Hjn.
induction n; intros; [ easy | ].
cbn.
destruct (lt_dec j (k / fact n)) as [Hjkn| Hjkn]. {
  apply -> Nat.succ_lt_mono.
  destruct n. {
    cbn in Hkn.
    apply Nat.lt_1_r in Hkn; subst k.
    now cbn in Hjkn.
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
    apply IHn; [ | flia Hjn Hjsn ].
    apply Nat.mod_upper_bound, fact_neq_0.
  }
} {
  apply Nat.nlt_ge in Hjkn.
  destruct (lt_dec (k / fact n) j) as [Hknj| Hknj]; [ | flia ].
  apply -> Nat.succ_lt_mono.
  destruct n. {
    now apply Nat.lt_1_r in Hjn; subst j.
  }
  apply IHn; [ | flia Hjn Hknj ].
  apply Nat.mod_upper_bound, fact_neq_0.
}
Qed.

Theorem sym_gr_sym_gr_inv : ∀ n k j,
  j < n
  → k < fact n
  → canon_sym_gr_elem n k (canon_sym_gr_inv n k j) = j.
Proof.
intros * Hjn Hkn.
revert j k Hjn Hkn.
induction n; intros; [ easy | cbn ].
destruct (lt_dec j (k / fact n)) as [Hjkn| Hjkn]. {
  cbn.
  destruct n. {
    rewrite Nat.div_1_r in Hjkn; cbn in Hkn.
    flia Hkn Hjkn.
  }
  destruct (lt_dec k (fact (S n))) as [Hksn| Hksn]. {
    now rewrite Nat.div_small in Hjkn.
  }
  apply Nat.nlt_ge in Hksn.
  destruct (Nat.eq_dec j (S n)) as [Hjsn| Hjsn]. {
    subst j.
    clear Hjn.
    exfalso; apply Nat.nle_gt in Hjkn; apply Hjkn; clear Hjkn.
    rewrite Nat_fact_succ in Hkn.
    rewrite Nat.mul_comm in Hkn.
    apply Nat.lt_succ_r.
    apply Nat.div_lt_upper_bound; [ | easy ].
    apply fact_neq_0.
  }
  rewrite IHn; [ | flia Hjn Hjsn | ]. 2: {
    apply Nat.mod_upper_bound, fact_neq_0.
  }
  remember (k / fact (S n) <=? j) as b eqn:Hb.
  symmetry in Hb.
  destruct b; [ exfalso | apply Nat.add_0_r ].
  apply Nat.leb_le in Hb.
  flia Hjkn Hb.
} {
  apply Nat.nlt_ge in Hjkn.
  destruct (lt_dec (k / fact n) j) as [Hkj| Hkj]. 2: {
    apply Nat.nlt_ge in Hkj; cbn.
    now apply Nat.le_antisymm.
  }
  clear Hjkn.
  destruct j; [ easy | ].
  rewrite Nat_sub_succ_1; cbn.
  destruct n; [ flia Hjn | ].
  apply Nat.succ_lt_mono in Hjn.
  rewrite IHn; [ | easy | ]. 2: {
    apply Nat.mod_upper_bound, fact_neq_0.
  }
  remember (k / fact (S n) <=? j) as b eqn:Hb.
  symmetry in Hb.
  destruct b; [ apply Nat.add_1_r | exfalso ].
  apply Nat.leb_nle in Hb.
  now apply Nat.succ_le_mono in Hkj.
}
Qed.

Theorem canon_sym_gr_surjective : ∀ n k j,
  k < fact n
  → j < n
  → ∃ i : nat, i < n ∧ canon_sym_gr_elem n k i = j.
Proof.
intros * Hkn Hjn.
exists (canon_sym_gr_inv n k j).
destruct n; [ easy | ].
split. {
  cbn.
  destruct (lt_dec j (k / fact n)) as [Hjk| Hjk]. {
    apply -> Nat.succ_lt_mono.
    destruct n. {
      now apply Nat.lt_1_r in Hkn; subst k.
    }
    destruct (Nat.eq_dec j (S n)) as [Hjsn| Hjsn]. {
      subst j; clear Hjn.
      apply Nat.nle_gt in Hjk.
      exfalso; apply Hjk; clear Hjk.
      rewrite Nat_fact_succ in Hkn.
      rewrite Nat.mul_comm in Hkn.
      apply Nat.lt_succ_r.
      apply Nat.div_lt_upper_bound; [ | easy ].
      apply fact_neq_0.
    }
    apply canon_sym_gr_inv_upper_bound; [ | flia Hjn Hjsn ].
    apply Nat.mod_upper_bound, fact_neq_0.
  } {
    apply Nat.nlt_ge in Hjk.
    destruct (lt_dec (k / fact n) j) as [Hkj| Hkj]; [ | flia ].
    apply -> Nat.succ_lt_mono.
    destruct n. {
      apply Nat.lt_1_r in Hkn; subst k.
      flia Hjn Hkj.
    }
    apply canon_sym_gr_inv_ub; [ | flia Hjn Hkj ].
    apply Nat.mod_upper_bound, fact_neq_0.
  }
}
now apply sym_gr_sym_gr_inv.
Qed.

Theorem comp_is_permut : ∀ n (σ₁ σ₂ : nat → nat),
  is_permut_fun σ₁ n
  → is_permut_fun σ₂ n
  → is_permut_fun (comp σ₁ σ₂) n.
Proof.
intros * Hp1 Hp2.
split. {
  intros i Hi.
  now apply Hp1, Hp2.
} {
  intros i j Hi Hj Hc.
  apply Hp2; [ easy | easy | ].
  apply Hp1; [ now apply Hp2 | now apply Hp2 | easy ].
}
Qed.

Theorem comp_list_is_permut : ∀ n l,
  (∀ σ, σ ∈ l → is_permut_fun σ n)
  → is_permut_fun (Comp (σ ∈ l), σ) n.
Proof.
intros * Hl.
induction l as [| σ]; [ easy | ].
rewrite iter_list_cons; [ | easy | easy | easy ].
apply comp_is_permut. 2: {
  apply IHl.
  intros σ' Hσ'.
  now apply Hl; right.
}
now apply Hl; left.
Qed.

(*
Theorem is_permut_comp : ∀ n (u v : vector nat),
  is_permut_vect u → is_permut_vect v → is_permut_vect (u ° v).
Proof.
intros * Hu Hv.
split. {
  intros i Hi.
  cbn; unfold comp.
  now apply Hu, Hv.
} {
  intros i j Hi Hj Huv.
  apply Hu in Huv; [ | now apply Hv | now apply Hv ].
  now apply Hv in Huv.
}
Qed.
*)

(*
Theorem ε_1_opp_1 :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n (σ : vector n nat), is_permut_vect σ → ε σ = 1%F ∨ ε σ = (-1)%F.
Proof.
intros Hic Hop Hiv H10 Hit Hed Hch * Hσ.
rewrite ε_ws_ε; try easy.
unfold ε_ws.
unfold ε_fun_ws.
apply rngl_product_1_opp_1; [ easy | ].
intros i Hi.
apply rngl_product_1_opp_1; [ easy | ].
intros j Hj.
unfold sign_diff.
rewrite if_ltb_lt_dec.
rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [Hij| Hij]. {
  now destruct (lt_dec _ _) as [Hvv| Hvv]; [ left | right ].
}
now left.
Qed.
*)

(*
Theorem ε_square :
  rngl_is_comm = true →
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_has_1_neq_0 = true →
  rngl_is_integral = true →
  rngl_has_dec_eq = true →
  rngl_characteristic = 0 →
  ∀ n (σ : vector n nat), is_permut_vect σ → (ε σ * ε σ = 1)%F.
Proof.
intros Hic Hop Hiv H10 Hit Hed Hch * Hσ.
specialize (ε_1_opp_1) as H1.
specialize (H1 Hic Hop Hiv H10 Hit Hed Hch).
specialize (H1 n σ Hσ).
destruct H1 as [H1| H1]; rewrite H1. {
  apply rngl_mul_1_l.
} {
  rewrite rngl_mul_opp_opp; [ | easy ].
  apply rngl_mul_1_l.
}
Qed.
*)

End a.

Arguments δ {T}%type {ro} (i j u v)%nat.
Arguments ε {T}%type {ro} n%nat p%V.
Arguments ε_fun {T}%type {ro} f%function n%nat.
Arguments ε_ws {T}%type {ro} n.
Arguments ε_fun_ws {T}%type {ro} f%function n%nat.
Arguments sign_diff {T}%type {ro} (u v)%nat.

Arguments ε_permut {T}%type {ro} (n k)%nat.
Arguments ε_of_sym_gr_permut_succ {T}%type {ro rp} _ _ _ _ _ _ _ (n k)%nat.
Arguments ε_of_permut_ε {T}%type {ro rp} _ _ _ _ _ _ _ n%nat [k]%nat.
Arguments ε_ws_ε {T}%type {ro rp} _ _ _ _ _ _ _ n%nat p%V.
Arguments ε_ws_ε_fun {T}%type {ro rp} _ _ _ _ _ _ _ [σ]%function [n]%nat.
Arguments rngl_product_change_list {T}%type {ro rp} _ [A]%type [la lb]%list
  f%function.
Arguments signature_comp {T}%type {ro rp} _ _ _ _ _ _ _ [n]%nat [σ₁ σ₂].
Arguments transposition_signature {T}%type {ro rp} _ _ _ _ _ _ _ (n p q)%nat.
(*
Arguments ε_1_opp_1 {T}%type {ro rp} _ _ _ _ _ _ _ [n]%nat [σ].
Arguments ε_square {T}%type {ro rp} _ _ _ _ _ _ _ [n]%nat [σ].
*)

Arguments minus_one_pow {T}%type {ro} n%nat.
Arguments minus_one_pow_add_r {T}%type {ro rp} Hop (i j)%nat.
Arguments minus_one_pow_succ {T}%type {ro rp} _ i%nat.
