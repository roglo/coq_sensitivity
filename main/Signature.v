(* signatures *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Init.Nat.
Import List List.ListNotations.

Require Import Misc RingLike.
Require Import SortingFun SortRank PermutationFun.
Require Import IterMul PermutSeq.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).

(* version of signature (parity) of a list of nat *)

Fixpoint ε_aux i l :=
  match l with
  | [] => 1%L
  | j :: l' =>
      match i ?= j with
      | Lt => ε_aux i l'
      | Eq => 0%L
      | Gt => (- ε_aux i l')%L
      end
  end.

Fixpoint ε (l : list nat) :=
  match l with
  | [] => 1%L
  | i :: q => (ε_aux i q * ε q)%L
  end.

(*
End a.

Require Import RnglAlg.Zrl ZArith.

Definition ro := RnglAlg.Zrl.Z_ring_like_op.
Compute (ε ro []).
Compute (ε ro [3;5;3]).
Compute (canon_sym_gr_list_list 3).
Compute (map (λ l, (l, ε ro l)) (canon_sym_gr_list_list 4)).
Compute (map (λ l, (l, ε ro l)) (cart_prod (repeat (seq 1 4) 3))).
...
*)

(* old version
Definition sign_diff u v :=
  match Nat.compare u v with
  | Lt => (-1)%L
  | Eq => 0%L
  | Gt => 1%L
  end.

Definition ε (p : list nat) :=
  let n := length p in
  ∏ (i = 0, n - 1), ∏ (j = 0, n - 1),
  if i <? j then sign_diff (nth j p O) (nth i p O) else 1.
*)

(*
End a.

Require Import RnglAlg.Zrl.
Require Import ZArith.

Definition ro := RnglAlg.Zrl.Z_ring_like_op.
Compute (ε Z_ring_like_op []).
Compute (ε Z_ring_like_op [3;5;3]).
Compute (canon_sym_gr_list_list 3).
Compute (map (λ l, (l, ε Z_ring_like_op l, ε₀ Z_ring_like_op l)) (canon_sym_gr_list_list 4)).
Compute (map (λ l, (l, ε ro l, ε₀ ro l)) (cart_prod (repeat (seq 1 4) 3))).
Check no_dup.
*)

(*
Definition rngl_sub_nat i j := (rngl_of_nat i - rngl_of_nat j)%L.
*)

(* still other definition of ε

Definition ε' (p : list nat) :=
  let n := length p in
  ((∏ (i = 0, n - 1), ∏ (j = 0, n - 1),
    if i <? j then rngl_sub_nat (nth j p O) (nth i p O) else 1) /
   (∏ (i = 0, n - 1), ∏ (j = 0, n - 1),
    if i <? j then rngl_sub_nat j i else 1))%L.

Theorem fold_ε : ∀ p,
  ∏ (i = 0, length p - 1),
  (∏ (j = 0, length p - 1),
   (if i <? j then sign_diff (nth j p O) (nth i p O) else 1)) =
  ε p.
Proof. easy. Qed.
*)

Definition minus_one_pow n :=
  match n mod 2 with
  | 0 => 1%L
  | _ => (- 1%L)%L
  end.

Theorem ε_nil : ε [] = 1%L.
Proof. easy. Qed.

Theorem ε_aux_map_S : ∀ i l,  ε_aux (S i) (map S l) = ε_aux i l.
Proof.
intros.
revert i.
induction l as [| j]; intros; [ easy | cbn ].
rewrite IHl.
now destruct (i ?= j).
Qed.

Theorem ε_map_S : ∀ l, ε (map S l) = ε l.
Proof.
intros.
induction l as [| i]; [ easy | cbn ].
rewrite IHl.
f_equal.
apply ε_aux_map_S.
Qed.

Theorem minus_one_pow_mul_comm :
  rngl_has_opp = true →
  ∀ i x, (minus_one_pow i * x = x * minus_one_pow i)%L.
Proof.
intros Hop *.
unfold minus_one_pow.
remember (i mod 2) as k eqn:Hk; symmetry in Hk.
destruct k; [ now rewrite rngl_mul_1_r, rngl_mul_1_l | ].
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_opp_r Hop).
now rewrite rngl_mul_1_l, rngl_mul_1_r.
Qed.

Theorem minus_one_pow_succ :
  rngl_has_opp = true →
  ∀ i, minus_one_pow (S i) = (- minus_one_pow i)%L.
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

Theorem minus_one_pow_add :
  rngl_has_opp = true →
  ∀ i j, minus_one_pow (i + j) = (minus_one_pow i * minus_one_pow j)%L.
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
  | 0 => 1%L
  | S n' => (minus_one_pow (k / fact n') * ε_permut n' (k mod fact n'))%L
  end.

Theorem rngl_product_product_if : ∀ b e f,
  (∏ (i = b, e), ∏ (j = b, e), if i <? j then f i j else 1)%L =
  (∏ (i = b, e), ∏ (j = i + 1, e), f i j)%L.
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
  (rngl_of_nat j - rngl_of_nat i)%L =
     if i <? j then rngl_of_nat (j - i)
     else (- rngl_of_nat (i - j))%L.
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hop'.
specialize (Hop' (or_introl Hop)).
move Hop' before Hop.
rewrite if_ltb_lt_dec.
destruct (lt_dec i j) as [Hij| Hij]. {
  revert j Hij.
  induction i; intros; cbn. {
    rewrite rngl_sub_0_r; f_equal; [ | easy ].
    now destruct j.
  }
  destruct j; [ easy | cbn ].
  rewrite rngl_add_sub_simpl_l; [ | easy ].
  apply IHi.
  now apply Nat.succ_lt_mono in Hij.
} {
  apply Nat.nlt_ge in Hij.
  revert j Hij.
  induction i; intros; cbn. {
    rewrite rngl_sub_0_r; f_equal; [ | easy ].
    rewrite rngl_opp_0; [ | easy ].
    now apply Nat.le_0_r in Hij; subst j.
  }
  destruct j. {
    unfold rngl_sub; rewrite Hop; cbn.
    now rewrite rngl_add_0_l.
  }
  cbn.
  rewrite rngl_add_sub_simpl_l; [ | easy ].
  apply IHi.
  now apply Nat.succ_le_mono in Hij.
}
Qed.

Theorem rngl_of_nat_add : ∀ a b,
  (rngl_of_nat a + rngl_of_nat b)%L = rngl_of_nat (a + b).
Proof.
intros.
induction a; [ apply rngl_add_0_l | ].
now cbn; rewrite <- rngl_add_assoc; f_equal.
Qed.

Theorem rngl_of_nat_mul :
  rngl_has_opp_or_subt = true →
  ∀ a b, (rngl_of_nat a * rngl_of_nat b)%L = rngl_of_nat (a * b).
Proof.
intros Hom *.
induction a; [ now apply rngl_mul_0_l | cbn ].
rewrite rngl_mul_add_distr_r.
rewrite rngl_mul_1_l.
rewrite IHa.
apply rngl_of_nat_add.
Qed.

Theorem rngl_product_rngl_of_nat :
  rngl_has_opp_or_subt = true →
  ∀ n, (∏ (i = 1, n), rngl_of_nat i)%L = rngl_of_nat (fact n).
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

(*
Definition sign_diff' u v := if u <? v then (-1)%L else 1%L.

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
*)

(*
Theorem rngl_sub_is_mul_sign_abs :
  rngl_has_opp = true →
  ∀ a b,
  (rngl_of_nat a - rngl_of_nat b)%L =
  (sign_diff a b * rngl_of_nat (abs_diff a b))%L.
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hop'.
specialize (Hop' (or_introl Hop)).
move Hop' before Hop.
unfold sign_diff, abs_diff.
rewrite if_ltb_lt_dec.
remember (a ?= b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  apply Nat.compare_eq in Hab; subst b.
  rewrite rngl_sub_diag; [ | easy ].
  now rewrite rngl_mul_0_l.
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
*)

(*
Theorem rngl_sign_diff'_sub_div_abs :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_characteristic = 0 →
  ∀ a b,
  a ≠ b
  → sign_diff' a b =
       ((rngl_of_nat a - rngl_of_nat b) / rngl_of_nat (abs_diff a b))%L.
Proof.
intros Hop Hiv Hch * Hab.
specialize (proj2 rngl_has_inv_or_quot_iff) as Hiq.
specialize (Hiq (or_introl Hiv)).
move Hiq before Hiv.
assert (Hnz : rngl_of_nat (abs_diff a b) ≠ 0%L). {
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
  easy.
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
*)

Theorem rngl_product_product_div_eq_1 :
  rngl_has_opp_or_subt = true →
  rngl_mul_is_comm = true →
  rngl_has_inv = true →
  rngl_is_integral = true →
  rngl_characteristic ≠ 1 →
  rngl_has_eqb = true →
  ∀ n f g,
  (∀ i j, i < n → j < n → g i j ≠ 0%L)
  → (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), (f i j / g i j)))%L = 1%L
  → (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), f i j))%L =
    (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n), g i j))%L.
Proof.
intros Hom Hic Hiv Hin H10 Heq * Hg Hs.
specialize (proj2 rngl_has_inv_or_quot_iff) as Hiq.
specialize (Hiq (or_introl Hiv)).
move Hiq before Hiv.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
remember (∏ (i ∈ _), _)%L as a eqn:Ha in |-*.
remember (∏ (i ∈ _), _)%L as b eqn:Hb in |-*.
remember (rngl_eqb b 0%L) as bz eqn:Hbz; symmetry in Hbz.
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
apply rngl_mul_cancel_r with (c := (b⁻¹)%L); [ easy | | ]. {
  intros Hbiz.
  apply (f_equal (rngl_mul b)) in Hbiz.
  rewrite fold_rngl_div in Hbiz; [ | easy ].
  rewrite rngl_div_diag in Hbiz; [ | easy | easy ].
  rewrite rngl_mul_0_r in Hbiz; [ | easy ].
  now apply rngl_1_neq_0_iff in Hbiz.
}
remember (_ * _)%L as c.
rewrite fold_rngl_div; [ | easy ].
rewrite rngl_div_diag; [ | easy | easy ].
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
erewrite (rngl_product_list_permut _ Nat.eqb_eq) with
    (la := rev _); [ | easy | ]. 2: {
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
  erewrite (rngl_product_list_permut _ Nat.eqb_eq) with
      (la := rev _); [ | easy | ]. 2: {
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
  rngl_mul_is_comm = true →
  ∀ n f,
  (∏ (i ∈ seq 0 n), ∏ (j ∈ seq 0 n), f i j)%L =
  ((∏ (i ∈ seq 0 n), f i i) *
   (∏ (i ∈ seq 0 (n - 1)), ∏ (j = i + 1, n - 1), (f i j * f j i)))%L.
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
  rngl_mul_is_comm = true →
  rngl_has_inv = true →
  rngl_characteristic ≠ 1 →
  permut_seq_with_len n σ
  → (∀ i j, f i j = f j i)
  → (∀ i j, i < n → j < n → i ≠ j → f i j ≠ 0%L)
  → ∀ i j, i < n → j < n →
    ((if nth i σ O <? nth j σ O then f i j else 1) /
      (if i <? j then f i j else 1) *
     ((if nth j σ O <? nth i σ O then f j i else 1) /
      (if j <? i then f j i else 1)))%L = 1%L.
Proof.
intros * Hic Hin H10 (Hp, Hn) Hfij Hfijnz * Hlin Hljn.
specialize (proj2 rngl_has_inv_or_quot_iff) as Hiq.
specialize (Hiq (or_introl Hin)).
move Hiq before Hin.
do 4 rewrite if_ltb_lt_dec.
destruct (lt_dec (nth i σ 0) (nth j σ 0)) as [H1| H1]. {
  destruct (lt_dec (nth j σ 0) (nth i σ 0)) as [H| H]; [ flia H1 H | ].
  clear H.
  destruct (lt_dec i j) as [H3| H3]. {
    destruct (lt_dec j i) as [H| H]; [ flia H3 H | clear H ].
    rewrite Hfij.
    rewrite rngl_div_diag; [ | easy | ]. 2: {
      apply Hfijnz; [ easy | easy | flia H3 ].
    }
    rewrite rngl_mul_1_l.
    apply rngl_div_diag; [ easy | ].
    now apply rngl_1_neq_0_iff.
  }
  destruct (lt_dec j i) as [H4| H4]. {
    rewrite Hfij.
    rewrite rngl_div_1_r; [ | easy | easy ].
    rewrite rngl_div_1_l; [ | easy ].
    rewrite fold_rngl_div; [ | easy ].
    apply rngl_div_diag; [ easy | ].
    apply Hfijnz; [ easy | easy | flia H4 ].
  }
  exfalso.
  apply Nat.nlt_ge in H3.
  apply Nat.nlt_ge in H4.
  apply Nat.le_antisymm in H3; [ | easy ].
  subst j; flia H1.
}
destruct (lt_dec (nth j σ 0) (nth i σ 0)) as [H2| H2]. {
  destruct (lt_dec i j) as [H3| H3]. {
    destruct (lt_dec j i) as [H| H]; [ flia H3 H | clear H ].
    rewrite Hfij.
    rewrite rngl_div_1_r; [ | easy | easy ].
    rewrite rngl_div_1_l; [ | easy ].
    rewrite rngl_mul_comm; [ | easy ].
    rewrite fold_rngl_div; [ | easy ].
    apply rngl_div_diag; [ easy | ].
    apply Hfijnz; [ easy | easy | flia H3 ].
  }
  destruct (lt_dec j i) as [H4| H4]. {
    rewrite Hfij.
    rewrite rngl_div_1_r; [ | easy | easy ].
    rewrite rngl_mul_1_l.
    apply rngl_div_diag; [ easy | ].
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
  apply permut_seq_iff in Hp.
  destruct Hp as (_, Hp).
  apply (NoDup_nat _ Hp) in H1; [ | now rewrite Hn | now rewrite Hn ].
  flia H1 H3.
}
destruct (lt_dec j i) as [H4| H4]. {
  apply permut_seq_iff in Hp.
  destruct Hp as (_, Hp).
  apply (NoDup_nat _ Hp) in H1; [ | now rewrite Hn | now rewrite Hn ].
  flia H1 H4.
}
rewrite rngl_div_1_r; [ | easy | easy ].
apply rngl_mul_1_l.
Qed.

Theorem product_product_if_permut_div :
  rngl_mul_is_comm = true →
  rngl_characteristic ≠ 1 →
  rngl_has_inv = true →
  ∀ n σ f,
  permut_seq_with_len n σ
  → (∀ i j, f i j = f j i)
  → (∀ i j, i < n → j < n → i ≠ j → f i j ≠ 0%L)
  → (∏ (i ∈ seq 0 n), ∏ (j ∈ seq 0 n),
      ((if nth i σ O <? nth j σ O then f i j else 1) /
       (if i <? j then f i j else 1)))%L =
     1%L.
Proof.
intros Hic H10 Hin * (Hp, Hn) Hfij Hfijnz.
specialize (proj2 rngl_has_inv_or_quot_iff) as Hiq.
specialize (Hiq (or_introl Hin)).
move Hiq before Hin.
rewrite rngl_product_product_by_swap; [ | easy ].
rewrite all_1_rngl_product_list_1; [ | easy | ]. 2: {
  intros i Hi.
  do 2 rewrite if_ltb_lt_dec.
  destruct (lt_dec _ _) as [H| H]; [ flia H | clear H ].
  destruct (lt_dec _ _) as [H| H]; [ flia H | clear H ].
  now apply rngl_div_1_r.
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
  rngl_has_opp_or_subt = true →
  rngl_mul_is_comm = true →
  rngl_has_inv = true →
  rngl_is_integral = true →
  rngl_characteristic ≠ 1 →
  rngl_has_eqb = true →
  ∀ n σ f,
  permut_seq_with_len n σ
  → (∀ i j, f i j = f j i)
  → (∀ i j, i < n → j < n → i ≠ j → f i j ≠ 0%L)
  → (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n),
        if nth i σ O <? nth j σ O then f i j else 1))%L =
    (∏ (i ∈ seq 0 n), (∏ (j ∈ seq 0 n),
        if i <? j then f i j else 1))%L.
Proof.
intros Hom Hic Hid Hin H10 Heq * (Hp, Hn) Hfij Hfijnz.
apply rngl_product_product_div_eq_1; try easy. {
  intros i j Hi Hj.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec i j) as [Hij| Hij]; [ | now apply rngl_1_neq_0_iff ].
  apply Hfijnz; [ easy | easy | flia Hij ].
}
now apply product_product_if_permut_div.
Qed.

Theorem rngl_product_product_abs_diff_div_diff : in_charac_0_field →
  ∀ p,
  permut_seq p
  → ∏ (i = 0, length p - 1),
    (∏ (j = 0, length p - 1),
     (if i <? j then
        rngl_of_nat (abs_diff (nth j p O) (nth i p O)) /
        rngl_of_nat (j - i)
      else 1)) = 1%L.
Proof.
intros Hif * Hp.
destruct Hif as (Hic, Hop, Hin, Hit, Hde, Hch).
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
specialize (proj2 rngl_has_inv_or_quot_iff) as Hiq.
specialize (Hiq (or_introl Hin)).
move Hiq before Hin.
destruct (le_dec (length p) 1) as [Hn1| Hn1]. {
  replace (length p - 1) with 0 by flia Hn1.
  now do 2 rewrite rngl_product_only_one.
}
assert (H10 : rngl_characteristic ≠ 1) by now rewrite Hch.
rewrite rngl_product_product_if.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_div_distr; try easy.
  intros j Hj.
  intros H.
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  flia Hj H.
}
cbn.
rewrite rngl_product_div_distr; try easy. 2: {
  intros i Hi H.
  apply (rngl_product_integral Hos Hit H10) in H.
  destruct H as (j & Hj & Hji).
  apply eq_rngl_of_nat_0 in Hji; [ | easy ].
  flia Hj Hji.
}
apply eq_rngl_div_1; [ easy | | ]. {
  intros H.
  apply (rngl_product_integral Hos Hit H10) in H.
  destruct H as (i & Hi & H).
  apply (rngl_product_integral Hos Hit H10) in H.
  destruct H as (j & Hj & H).
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  flia Hj H.
}
rewrite <- rngl_product_product_if; symmetry.
rewrite <- rngl_product_product_if; symmetry.
apply Nat.nle_gt in Hn1.
(* changt of var *)
rewrite rngl_product_change_var with
  (g := λ i, nth i (isort_rank Nat.leb p) 0) (h := λ i, nth i p 0). 2: {
  intros i Hi.
  apply permut_isort_permut; [ easy | flia Hi Hn1 ].
}
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | flia Hn1 ].
rewrite Nat_sub_succ_1.
rewrite <- List_map_nth_seq.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_change_var with
    (g := λ i, nth i (isort_rank Nat.leb p) 0) (h := λ i, nth i p 0). 2: {
    intros j Hj.
    apply permut_isort_permut; [ easy | flia Hj Hn1 ].
  }
  rewrite <- Nat.sub_succ_l; [ | flia Hn1 ].
  rewrite Nat_sub_succ_1, Nat.sub_0_r.
  rewrite <- List_map_nth_seq.
  apply (In_nth _ _ 0) in Hi.
  destruct Hi as (u & Hu & Hui).
  replace (nth (nth i _ 0) _ 0) with i. 2: {
    symmetry.
    apply permut_permut_isort; [ easy | ].
    rewrite <- Hui.
    apply permut_list_ub; [ easy | now apply nth_In ].
  }
  erewrite rngl_product_list_eq_compat. 2: {
    intros j Hj.
    apply (In_nth _ _ 0) in Hj.
    destruct Hj as (v & Hv & Hvj).
    replace (nth (nth j _ 0) _ 0) with j. 2: {
      symmetry.
      apply permut_permut_isort; [ easy | ].
      rewrite <- Hvj.
      apply permut_list_ub; [ easy | now apply nth_In ].
    }
    easy.
  }
  cbn - [ "<?" ].
  easy.
}
cbn - [ "<?" ].
rewrite (rngl_product_list_permut _ Nat.eqb_eq) with
    (lb := seq 0 (length p)); [ | easy | easy ].
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  now rewrite (rngl_product_list_permut _ Nat.eqb_eq) with
    (lb := seq 0 (length p)).
}
cbn - [ "<?" ].
rewrite product_product_if_permut; try easy; cycle 1. {
  now apply (isort_rank_permut_seq_with_len _ (length p)).
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

(*
Theorem ε'_ε_1 : in_charac_0_field →
  ∀ p,
  (∏ (i = 0, length p - 1),
   ∏ (j = 0, length p - 1),
   if i <? j then
      rngl_of_nat (abs_diff (nth j p O) (nth i p O)) / rngl_of_nat (j - i)
   else 1) = 1%L
  → ε' p = ε p.
Proof.
intros Hif * Hij1.
destruct Hif as (Hic, Hop, Hin, Hit, _, Hch).
assert (H10 : rngl_characteristic ≠ 1) by now rewrite Hch.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
specialize (proj2 rngl_has_inv_or_quot_iff) as Hiq.
specialize (Hiq (or_introl Hin)).
move Hiq before Hin.
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
  apply rngl_div_1_r; [ easy | easy ].
}
apply Nat.nle_gt in Hn1.
rewrite <- rngl_product_div_distr; try easy. 2: {
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
    rewrite rngl_product_empty; [ | flia ].
    now apply rngl_1_neq_0_iff.
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
  rewrite rngl_product_rngl_of_nat; [ | easy ].
  intros H.
  apply eq_rngl_of_nat_0 in H; [ | easy ].
  now apply fact_neq_0 in H.
}
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite <- rngl_product_div_distr; try easy.
  intros j Hj.
  intros H.
  apply -> rngl_sub_move_0_r in H; [ | easy ].
  apply rngl_of_nat_inj in H; [ | easy | easy ].
  flia Hj H.
}
cbn.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite rngl_sub_is_mul_sign_abs; [ | easy ].
    rewrite rngl_sub_is_mul_sign_abs; [ | easy ].
    replace (sign_diff j i) with 1%L. 2: {
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
  ∀ p, permut_seq p → ε' p = ε p.
Proof.
intros Hif * Hp.
apply ε'_ε_1; [ easy | ].
now rewrite rngl_product_product_abs_diff_div_diff.
Qed.
*)

Theorem transposition_permut_seq_with_len : ∀ p q n,
  p < n → q < n → permut_seq_with_len n (map (transposition p q) (seq 0 n)).
Proof.
intros * Hp Hq.
split. {
  apply permut_seq_iff.
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

Theorem ε_app_cons :
  rngl_has_opp = true →
  ∀ n la lb,
  (∀ a, a ∈ la ++ lb → a < n)
  → ε (la ++ n :: lb) = (minus_one_pow (length lb) * ε (la ++ lb))%L.
Proof.
intros Hop * Hab.
revert n lb Hab.
induction la as [| a]; intros; cbn. {
  f_equal; cbn in Hab.
  induction lb as [| b]; [ easy | cbn ].
  specialize (Hab b (or_introl eq_refl)) as H1.
  remember (n ?= b) as c eqn:Hc; symmetry in Hc.
  destruct c. {
    now apply Nat.compare_eq_iff in Hc; subst b; apply Nat.lt_irrefl in H1.
  } {
    apply Nat.compare_lt_iff in Hc; flia H1 Hc.
  }
  rewrite (minus_one_pow_succ Hop).
  f_equal.
  apply IHlb.
  intros a Ha.
  now apply Hab; right.
}
rewrite IHla. 2: {
  intros b Hb.
  now apply Hab; right.
}
do 2 rewrite rngl_mul_assoc.
f_equal.
rewrite (minus_one_pow_mul_comm Hop); f_equal.
clear IHla.
revert a lb Hab.
induction la as [| a']; intros; cbn. {
  specialize (Hab a (or_introl eq_refl)).
  apply Nat.compare_lt_iff in Hab.
  now rewrite Hab.
}
remember (a ?= a') as c eqn:Hc; symmetry in Hc.
destruct c; [ easy | | ]. {
  apply IHla.
  intros b Hb.
  apply Hab.
  cbn in Hb |-*.
  destruct Hb; [ now left | now right; right ].
} {
  f_equal.
  apply IHla.
  intros b Hb.
  apply Hab.
  cbn in Hb |-*.
  destruct Hb; [ now left | now right; right ].
}
Qed.

Theorem ε_aux_app : ∀ i p q,
  (∀ j k, j ∈ i :: p → k ∈ q → j < k)
  → ε_aux i (p ++ q) = ε_aux i p.
Proof.
intros * Hpq.
revert i q Hpq.
induction p as [| j]; intros; cbn. {
  assert (H : ∀ k, k ∈ q → i < k). {
    intros.
    apply Hpq; [ now left | easy ].
  }
  clear Hpq; rename H into Hq.
  induction q as [| k]; [ easy | cbn ].
  specialize (Hq k (or_introl eq_refl)) as H.
  apply Nat.compare_lt_iff in H; rewrite H.
  apply IHq.
  intros j Hj.
  now apply Hq; right.
}
destruct (i ?= j); [ easy | | ]. {
  apply IHp.
  intros k l Hk Hl.
  apply Hpq; [ | easy ].
  destruct Hk; [ now left | now right; right ].
} {
  f_equal.
  apply IHp.
  intros k l Hk Hl.
  apply Hpq; [ | easy ].
  destruct Hk; [ now left | now right; right ].
}
Qed.

Theorem ε_app : ∀ p q,
  (∀ i j, i ∈ p → j ∈ q → i < j)
  → ε (p ++ q) = (ε p * ε q)%L.
Proof.
intros * Hpq.
revert q Hpq.
induction p as [| i]; intros. {
  cbn; symmetry; f_equal.
  apply rngl_mul_1_l.
}
cbn.
rewrite IHp. 2: {
  intros j k Hj Hk.
  apply Hpq; [ now right | easy ].
}
rewrite <- rngl_mul_assoc; f_equal.
now apply ε_aux_app.
Qed.

Theorem ε_aux_app2 :
  rngl_has_opp = true →
  ∀ i p q,
  (∀ j k, j ∈ i :: p → k ∈ q → k < j)
  → ε_aux i (p ++ q) = (minus_one_pow (length q) * ε_aux i p)%L.
Proof.
intros Hop * Hpq.
revert i q Hpq.
induction p as [| j]; intros; cbn. {
  rewrite rngl_mul_1_r.
  assert (H : ∀ k, k ∈ q → k < i). {
    intros.
    apply Hpq; [ now left | easy ].
  }
  clear Hpq; rename H into Hq.
  induction q as [| k]; [ easy | cbn ].
  specialize (Hq k (or_introl eq_refl)) as H.
  apply Nat.compare_lt_iff in H.
  apply (f_equal CompOpp) in H; cbn in H.
  rewrite <- Nat.compare_antisym in H; rewrite H.
  rewrite (minus_one_pow_succ Hop); f_equal.
  apply IHq.
  intros j Hj.
  now apply Hq; right.
}
destruct (i ?= j). {
  symmetry; apply rngl_mul_0_r.
  now apply rngl_has_opp_or_subt_iff; left.
} {
  apply IHp.
  intros k l Hk Hl.
  apply Hpq; [ | easy ].
  destruct Hk; [ now left | now right; right ].
} {
  rewrite (rngl_mul_opp_r Hop).
  f_equal.
  apply IHp.
  intros k l Hk Hl.
  apply Hpq; [ | easy ].
  destruct Hk; [ now left | now right; right ].
}
Qed.

Theorem ε_aux_dup :
  rngl_has_opp = true →
  ∀ i l1 l2, ε_aux i (l1 ++ i :: l2) = 0%L.
Proof.
intros Hop *.
revert i l2.
induction l1 as [| j]; intros; cbn; [ now rewrite Nat.compare_refl | ].
destruct (i ?= j); [ easy | apply IHl1 | ].
rewrite IHl1.
apply (rngl_opp_0 Hop).
Qed.

Theorem ε_app2 :
  rngl_has_opp = true →
  ∀ p q,
  (∀ i j, i ∈ p → j ∈ q → j < i)
  → ε (p ++ q) = (minus_one_pow (length p * length q) * ε p * ε q)%L.
Proof.
intros Hop * Hpq.
revert q Hpq.
induction p as [| i]; intros. {
  cbn; symmetry; f_equal.
  now do 2 rewrite rngl_mul_1_l.
}
cbn.
rewrite IHp. 2: {
  intros j k Hj Hk.
  apply Hpq; [ now right | easy ].
}
do 3 rewrite rngl_mul_assoc.
f_equal; f_equal.
rewrite (minus_one_pow_add Hop).
do 2 rewrite <- (minus_one_pow_mul_comm Hop).
rewrite <- rngl_mul_assoc; f_equal.
now apply ε_aux_app2.
Qed.

Theorem ε_seq : ∀ sta len, ε (seq sta len) = 1%L.
Proof.
intros.
revert sta.
induction len; intros; [ easy | ].
rewrite seq_S.
rewrite ε_app. 2: {
  intros * Hi Hj.
  apply in_seq in Hi.
  destruct Hj as [Hj| ]; [ now subst j | easy ].
}
cbn.
do 2 rewrite rngl_mul_1_r.
apply IHlen.
Qed.

Theorem minus_one_pow_mul_same :
  rngl_has_opp = true →
  ∀ i, (minus_one_pow i * minus_one_pow i = 1)%L.
Proof.
intros Hop *.
unfold minus_one_pow.
destruct (i mod 2); [ apply rngl_mul_1_l | ].
now apply rngl_squ_opp_1.
Qed.

Theorem transposition_signature_lt :
  rngl_has_opp = true →
  ∀ n p q,
  p < q
  → q < n
  → ε (map (transposition p q) (seq 0 n)) = (-1)%L.
Proof.
intros Hop * Hpq Hq.
unfold transposition.
rewrite (List_seq_cut p). 2: {
  apply in_seq.
  split; [ easy | cbn ].
  now transitivity q.
}
rewrite (List_seq_cut q (S p)). 2: {
  apply in_seq; cbn.
  split; [ easy | flia Hq ].
}
rewrite Nat.sub_0_r, Nat.add_0_l.
replace (S p + (n - S p) - S q) with (n - S q) by flia Hpq.
do 4 rewrite map_app.
cbn.
do 2 rewrite Nat.eqb_refl.
replace (q =? p) with false. 2: {
  symmetry; apply Nat.eqb_neq.
  intros H; subst q.
  now apply Nat.lt_irrefl in Hpq.
}
erewrite map_ext_in. 2: {
  intros i Hi.
  apply in_seq in Hi; cbn in Hi.
  destruct Hi as (_, Hi).
  replace (i =? q) with false. 2: {
    symmetry; apply Nat.eqb_neq; flia Hpq Hi.
  }
  apply Nat.lt_neq in Hi.
  apply Nat.eqb_neq in Hi; rewrite Hi.
  easy.
}
rewrite map_id.
erewrite map_ext_in. 2: {
  intros i Hi.
  apply in_seq in Hi; cbn in Hi.
  replace (S (p + (q - S p))) with q in Hi by flia Hpq.
  replace (i =? p) with false. 2: {
    symmetry; apply Nat.eqb_neq; flia Hi.
  }
  replace (i =? q) with false. 2: {
    symmetry; apply Nat.eqb_neq; flia Hi.
  }
  easy.
}
rewrite map_id.
erewrite map_ext_in. 2: {
  intros i Hi.
  apply in_seq in Hi; cbn in Hi.
  replace (S (q + _)) with n in Hi by flia Hpq Hq.
  replace (i =? p) with false. 2: {
    symmetry; apply Nat.eqb_neq; flia Hpq Hi.
  }
  replace (i =? q) with false. 2: {
    symmetry; apply Nat.eqb_neq; flia Hi.
  }
  easy.
}
rewrite map_id.
rewrite ε_app. 2: {
  intros * Hi Hj.
  apply in_seq in Hi; cbn in Hi; destruct Hi as (_, Hi).
  destruct Hj as [Hj| Hj]; [ now subst j; transitivity p | ].
  apply in_app_iff in Hj.
  destruct Hj as [Hj| Hj]; [ apply in_seq in Hj; flia Hi Hj | ].
  destruct Hj as [Hj| Hj]; [ now subst j | ].
  apply in_seq in Hj; flia Hi Hpq Hj.
}
rewrite ε_seq, rngl_mul_1_l.
rewrite List_cons_is_app.
rewrite (List_cons_is_app p).
do 2 rewrite app_assoc.
rewrite ε_app. 2: {
  intros i j Hi Hj.
  apply in_seq in Hj.
  rewrite Nat.add_comm, Nat.sub_add in Hj; [ | easy ].
  apply in_app_iff in Hi.
  destruct Hi as [Hi| Hi]. {
    apply in_app_iff in Hi.
    destruct Hi as [Hi| Hi]. {
      destruct Hi; [ now subst i | easy ].
    }
    apply in_seq in Hi.
    rewrite Nat.add_comm, Nat.sub_add in Hi; [ | easy ].
    now transitivity q.
  }
  destruct Hi; [ subst i | easy ].
  now transitivity q.
}
rewrite ε_seq, rngl_mul_1_r.
clear n Hq.
rewrite (ε_app2 Hop). 2: {
  intros i j Hi Hj.
  destruct Hj; [ subst j | easy ].
  apply in_app_iff in Hi.
  destruct Hi as [Hi| Hi]. {
    destruct Hi; [ now subst i | easy ].
  }
  now apply in_seq in Hi.
}
rewrite app_length, seq_length.
cbn - [ ε ].
rewrite Nat.mul_1_r.
replace (ε [p]) with 1%L by now cbn; rewrite rngl_mul_1_l.
rewrite rngl_mul_1_r.
rewrite (minus_one_pow_succ Hop).
rewrite (rngl_mul_opp_l Hop); f_equal.
rewrite List_cons_is_app.
rewrite (ε_app2 Hop). 2: {
  intros i j Hi Hj.
  destruct Hi; [ subst i | easy ].
  apply in_seq in Hj.
  now rewrite Nat.add_comm, Nat.sub_add in Hj.
}
rewrite ε_seq, rngl_mul_1_r.
rewrite seq_length; cbn.
rewrite Nat.add_0_r.
do 2 rewrite rngl_mul_1_r.
now apply minus_one_pow_mul_same.
Qed.

Theorem transposition_signature :
  rngl_has_opp = true →
  ∀ n p q,
  p ≠ q
  → p < n
  → q < n
  → ε (map (transposition p q) (seq 0 n)) = (-1)%L.
Proof.
intros Hop * Hpq Hp Hq.
destruct (lt_dec p q) as [Hpq'| Hpq']. {
  now apply transposition_signature_lt.
}
apply Nat.nlt_ge in Hpq'.
assert (H : q < p) by flia Hpq Hpq'.
rewrite <- (transposition_signature_lt Hop H Hp).
f_equal.
apply map_ext_in.
intros i Hi.
apply transposition_comm.
Qed.

Theorem comp_permut_seq : ∀ n σ₁ σ₂,
  permut_seq_with_len n σ₁
  → permut_seq_with_len n σ₂
  → permut_seq (σ₁ ° σ₂).
Proof.
intros * (Hp11, Hp12) (Hp21, Hp22).
apply permut_seq_iff.
split. {
  intros i Hi.
  unfold comp_list in Hi |-*.
  rewrite map_length.
  apply in_map_iff in Hi.
  destruct Hi as (j & Hji & Hj).
  subst i.
  rewrite Hp22, <- Hp12.
  apply permut_list_ub; [ easy | ].
  apply nth_In.
  apply permut_seq_iff in Hp21.
  apply Hp21 in Hj.
  congruence.
} {
  unfold comp_list.
  apply nat_NoDup.
  rewrite map_length.
  intros i j Hi Hj.
  rewrite (List_map_nth' 0); [ | easy ].
  rewrite (List_map_nth' 0); [ | easy ].
  intros Hij.
  apply permut_seq_iff in Hp11.
  apply permut_seq_iff in Hp21.
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

Arguments comp_permut_seq n%nat [σ₁ σ₂]%list_scope.

Theorem comp_permut_seq_with_len : ∀ n σ₁ σ₂,
  permut_seq_with_len n σ₁
  → permut_seq_with_len n σ₂
  → permut_seq_with_len n (σ₁ ° σ₂).
Proof.
intros * Hp1 Hp2.
split; [ now apply (comp_permut_seq n) | ].
unfold "°".
rewrite map_length.
now destruct Hp2.
Qed.

(* ε (σ₁ ° σ₂) = ε σ₁ * ε σ₂ *)

(*
Theorem signature_comp_fun_expand_1 : in_charac_0_field →
  ∀ n f g,
  permut_seq_with_len n f
  → permut_seq_with_len n g
  → (∏ (i = 0, n - 1),
        (∏ (j = 0, n - 1),
         if i <? j then
           rngl_sub_nat (nth (nth j g O) f O) (nth (nth i g O) f O)
         else 1) /
      ∏ (i = 0, n - 1),
        (∏ (j = 0, n - 1),
         if i <? j then rngl_sub_nat (nth j g O) (nth i g O)
         else 1))%L =
    (∏ (i = 0, n - 1),
       (∏ (j = 0, n - 1),
        if i <? j then rngl_sub_nat (nth j f O) (nth i f O) else 1) /
      ∏ (i = 0, n - 1),
       (∏ (j = 0, n - 1),
        if i <? j then rngl_sub_nat j i else 1))%L
  → ε (f ° g) = (ε f * ε g)%L.
Proof.
intros Hif * (Hfp, Hfn) (Hgp, Hgn) Hs.
assert (H10 : rngl_characteristic ≠ 1). {
  now rewrite (cf_characteristic Hif).
}
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
assert (H : rngl_has_opp = true) by now destruct Hif.
specialize (Hos (or_introl H)); clear H.
specialize (proj2 rngl_has_inv_or_quot_iff) as Hiq.
assert (H : rngl_has_inv = true) by now destruct Hif.
specialize (Hiq (or_introl H)); clear H.
rewrite <- ε'_ε; [ | easy | now apply (comp_permut_seq n) ].
rewrite <- ε'_ε; [ | easy | easy ].
rewrite <- ε'_ε; [ | easy | easy ].
unfold ε', comp_list; cbn - [ "<?" ].
rewrite map_length, Hfn, Hgn.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  unfold "<?".
  do 8 rewrite rngl_product_only_one; cbn.
  symmetry.
  rewrite rngl_div_1_r; [ | easy | easy ].
  apply rngl_mul_1_l.
}
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite (List_map_nth' 0); [ | flia Hj Hgn Hnz ].
    rewrite (List_map_nth' 0); [ | flia Hi Hgn Hnz ].
    easy.
  }
  easy.
}
rewrite <- Hs; symmetry.
destruct Hif as (Hop, Hic, Hin, Hit, Hde, Hch).
apply rngl_div_mul_div; [ easy | ].
intros Hij.
apply rngl_product_integral in Hij; [ | easy | easy | easy ].
destruct Hij as (i & Hi & Hij).
apply rngl_product_integral in Hij; [ | easy | easy | easy ].
destruct Hij as (j & Hj & Hij).
rewrite if_ltb_lt_dec in Hij.
destruct (lt_dec i j) as [Hlij| Hlij]. 2: {
  apply rngl_1_neq_0_iff in Hij; [ easy | ].
  now rewrite Hch.
}
apply -> rngl_sub_move_0_r in Hij; [ | easy ].
apply rngl_of_nat_inj in Hij; [ | easy | easy ].
apply permut_seq_iff in Hgp.
destruct Hgp as (_, Hgp).
apply (NoDup_nat _ Hgp) in Hij; [ | flia Hj Hgn Hnz | flia Hi Hgn Hnz ].
flia Hi Hj Hlij Hij.
Qed.

Arguments signature_comp_fun_expand_1 _ n%nat [f g]%list.

Theorem signature_comp_fun_expand_2_1 :
  rngl_has_opp = true →
  rngl_has_inv = true →
  rngl_mul_is_comm = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f g,
  permut_seq_with_len n g
  → (∏ (i = 0, n - 1),
      (∏ (j = 0, n - 1),
       if i <? j then
         rngl_sub_nat (nth (nth j g O) f O) (nth (nth i g O) f O)
       else 1) /
     ∏ (i = 0, n - 1),
      (∏ (j = 0, n - 1),
       if i <? j then rngl_sub_nat (nth j g O) (nth i g O)
       else 1))%L =
    (∏ (i = 0, n - 1),
      (∏ (j = 0, n - 1),
       (if i <? j then
         (rngl_of_nat (nth (nth j g O) f O) -
          rngl_of_nat (nth (nth i g O) f O)) /
         (rngl_of_nat (nth j g O) - rngl_of_nat (nth i g O))
       else 1)))%L.
Proof.
intros Hop Hin Hic Hit Hch * (Hp2, Hn).
assert (H10 : rngl_characteristic ≠ 1) by now rewrite Hch.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hch.
specialize (proj2 rngl_has_inv_or_quot_iff) as Hiq.
specialize (Hiq (or_introl Hin)).
move Hiq before Hch.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  move Hnz at top; subst n.
  do 6 rewrite rngl_product_only_one; cbn.
  apply rngl_div_1_r; [ easy | easy ].
}
unfold rngl_div; rewrite Hin.
rewrite rngl_inv_product_comm; [ | easy | easy | easy | easy | easy | ]. 2: {
  intros i Hi Hij.
  apply rngl_product_integral in Hij; [ | easy | easy | easy ].
  destruct Hij as (j & Hj & Hij).
  rewrite <- Hn in Hi, Hj.
  rewrite if_ltb_lt_dec in Hij.
  destruct (lt_dec i j) as [Hlij| Hlij]. 2: {
    apply rngl_1_neq_0_iff in Hij; [ easy | ].
    now rewrite Hch.
  }
  apply -> rngl_sub_move_0_r in Hij; [ | easy ].
  apply rngl_of_nat_inj in Hij; [ | easy | easy ].
  rewrite <- Hn in Hnz.
  apply permut_seq_iff in Hp2.
  destruct Hp2 as (_, Hp2).
  apply (NoDup_nat _ Hp2) in Hij; [ | flia Hj Hnz | flia Hi Hnz ].
  flia Hi Hj Hlij Hij.
}
erewrite <- rngl_product_mul_distr; [ | easy ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_inv_product_comm;
      [ | easy | easy | easy | easy | easy | ]. 2: {
    intros j Hj Hij.
    rewrite <- Hn in Hi, Hj.
    rewrite if_ltb_lt_dec in Hij.
    destruct (lt_dec i j) as [Hlij| Hlij]. 2: {
      apply rngl_1_neq_0_iff in Hij; [ easy | ].
      now rewrite Hch.
    }
    apply -> rngl_sub_move_0_r in Hij; [ | easy ].
    apply rngl_of_nat_inj in Hij; [ | easy | easy ].
    rewrite <- Hn in Hnz.
    apply permut_seq_iff in Hp2.
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
  rngl_mul_is_comm = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f,
  (∏ (i = 0, n - 1),
   (∏ (j = 0, n - 1),
    if i <? j then rngl_sub_nat (f j) (f i) else 1) /
   ∏ (i = 0, n - 1),
   (∏ (j = 0, n - 1),
    if i <? j then rngl_sub_nat j i else 1))%L =
  (∏ (i = 0, n - 1),
   (∏ (j = 0, n - 1),
    (if i <? j then
      (rngl_of_nat (f j) - rngl_of_nat (f i)) / rngl_of_nat (j - i)
     else 1)))%L.
Proof.
intros Hop Hin Hic Hit Hch *.
assert (H10 : rngl_characteristic ≠ 1) by now rewrite Hch.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hch.
unfold rngl_div; rewrite Hin.
rewrite rngl_inv_product_comm; [ | easy | easy | easy | easy | easy | ]. 2: {
  intros i Hi Hij.
  apply rngl_product_integral in Hij; [ | easy | easy | easy ].
  destruct Hij as (j & Hj & Hij).
  rewrite if_ltb_lt_dec in Hij.
  destruct (lt_dec i j) as [Hlij| Hlij]. 2: {
    apply rngl_1_neq_0_iff in Hij; [ easy | ].
    now rewrite Hch.
  }
  apply -> rngl_sub_move_0_r in Hij; [ | easy ].
  apply rngl_of_nat_inj in Hij; [ | easy | easy ].
  flia Hlij Hij.
}
erewrite <- rngl_product_mul_distr; [ | easy ].
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_inv_product_comm;
      [ | easy | easy | easy | easy | easy | ]. 2: {
    intros j Hj Hij.
    rewrite if_ltb_lt_dec in Hij.
    destruct (lt_dec i j) as [Hlij| Hlij]. 2: {
      apply rngl_1_neq_0_iff in Hij; [ easy | ].
      now rewrite Hch.
    }
    apply -> rngl_sub_move_0_r in Hij; [ | easy ].
    apply rngl_of_nat_inj in Hij; [ | easy | easy ].
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
  rngl_mul_is_comm = true →
  rngl_has_eqb = true →
  rngl_is_integral = true →
  rngl_characteristic = 0 →
  ∀ n f g,
  permut_seq_with_len n f
  → permut_seq_with_len n g
  → (∏ (i = 0, n - 1),
     (∏ (j = 0, n - 1),
      (if i <? j then
         (rngl_of_nat (nth (nth j g O) f O) -
          rngl_of_nat (nth (nth i g O) f O)) /
         (rngl_of_nat (nth j g O) - rngl_of_nat (nth i g O))
       else 1)))%L =
    (∏ (i = 0, n - 1),
     (∏ (j = 0, n - 1),
      (if i <? j then
         (rngl_of_nat (nth j f O) - rngl_of_nat (nth i f O)) /
         rngl_of_nat (j - i)
       else 1)))%L.
Proof.
intros Hop Hin Hic Heq Hit Hch * (Hp1, Hn1) (Hp2, Hn2).
assert (H10 : rngl_characteristic ≠ 1) by now rewrite Hch.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hch.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now move Hnz at top; subst n | ].
rename g into g1.
rewrite rngl_product_change_var with
    (g := λ i, nth i (isort_rank Nat.leb g1) 0) (h := λ i, nth i g1 0). 2: {
  intros i Hi.
  apply permut_isort_permut; [ easy | rewrite Hn2; flia Hi Hnz ].
}
rewrite <- Nat.sub_succ_l; [ | flia Hnz ].
rewrite Nat_sub_succ_1, Nat.sub_0_r.
erewrite rngl_product_list_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_product_change_var with
      (g := λ i, nth i (isort_rank Nat.leb g1) 0) (h := λ i, nth i g1 0). 2: {
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
      apply permut_seq_iff in Hp2.
      apply Hp2, nth_In.
      now rewrite Hn2.
    }
    rewrite permut_permut_isort; [ | easy | ]. 2: {
      apply in_map_iff in Hi.
      destruct Hi as (k & Hk & Hkn).
      apply in_seq in Hkn.
      rewrite <- Hk.
      apply permut_seq_iff in Hp2.
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
  rewrite <- List_map_nth_seq.
  erewrite (rngl_product_list_permut _ Nat.eqb_eq); [ | easy | apply Hp2 ].
  easy.
}
cbn - [ "<?" ].
erewrite (rngl_product_list_permut _ Nat.eqb_eq); [ | easy | ]. 2: {
  rewrite <- Hn2 at 1.
  rewrite <- List_map_nth_seq.
  apply Hp2.
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
  now apply (isort_rank_permut_seq_with_len _ n).
} {
  intros i j.
  destruct (Nat.eq_dec i j) as [Hij| Hij]; [ now subst j | ].
  rewrite <- rngl_opp_sub_distr; [ | easy ].
  unfold rngl_div.
  rewrite Hin.
  rewrite rngl_mul_opp_l; [ | easy ].
  rewrite <- rngl_mul_opp_r; [ | easy ].
  f_equal.
  rewrite rngl_opp_inv; [ | easy | easy | ]. 2: {
    intros H.
    apply -> rngl_sub_move_0_r in H; [ | easy ].
    apply Hij; symmetry.
    apply rngl_of_nat_inj in H; [ easy | easy | easy ].
  }
  now rewrite rngl_opp_sub_distr.
} {
  intros * Hi Hj Hij.
  unfold rngl_div.
  rewrite Hin.
  intros H.
  apply rngl_integral in H; [ | easy | now rewrite Hit ].
  destruct H as [H| H]. {
    apply -> rngl_sub_move_0_r in H; [ | easy ].
    apply rngl_of_nat_inj in H; [ | easy | easy ].
    apply Hij; symmetry.
    rewrite <- Hn1 in Hi, Hj.
    apply permut_seq_iff in Hp1.
    destruct Hp1 as (_, Hp1).
    now apply (NoDup_nat _ Hp1) in H.
  } {
    revert H.
    apply rngl_inv_neq_0; [ easy | easy | ].
    intros H.
    apply -> rngl_sub_move_0_r in H; [ | easy ].
    apply rngl_of_nat_inj in H; [ | easy | easy ].
    now apply Hij; symmetry.
  }
}
Qed.

Theorem sign_diff_id : ∀ a, sign_diff a a = 0%L.
Proof.
intros.
unfold sign_diff.
now rewrite Nat.compare_refl.
Qed.

Theorem sign_diff_swap :
  rngl_has_opp = true →
  ∀ u v, sign_diff u v = (- sign_diff v u)%L.
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
  rewrite <- (rngl_opp_involutive Hop 1%L) at 1.
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
*)

Theorem butn_permut_seq_with_len : ∀ n i l,
  permut_seq_with_len (S n) l
  → n = nth i l 0
  → i < length l
  → permut_seq_with_len n (butn i l).
Proof.
intros * Hp Hni Hil.
split. {
  apply permut_seq_iff.
  split. {
    intros j Hj.
    rewrite butn_length.
    destruct Hp as (Hp, Hl).
    apply Nat.ltb_lt in Hil; rewrite Hil.
    apply Nat.ltb_lt in Hil.
    rewrite Hl, Nat_sub_succ_1.
    apply permut_seq_iff in Hp.
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
      assert (H : nth j l 0 = nth n l 0) by now rewrite <- Hni.
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
    apply permut_seq_iff in Hpp.
    destruct Hpp as (Hp, Hpi).
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
  permut_seq_with_len (S n) l
  → ∃ i, i < length l ∧ nth i l 0 = n ∧ permut_seq_with_len n (butn i l).
Proof.
intros * Hl.
exists (nth n (isort_rank Nat.leb l) 0).
split. {
  rewrite <- (isort_rank_length Nat.leb).
  destruct Hl as (Hp, Hl).
  specialize (isort_rank_permut_seq_with_len Nat.leb _ Hl) as Hil.
  destruct Hil as (Hil, Hil').
  apply permut_seq_iff in Hil.
  apply Hil, nth_In.
  rewrite isort_rank_length.
  now rewrite Hl.
}
split. {
  destruct Hl as (Hp, Hl).
  apply permut_permut_isort; [ easy | now rewrite Hl ].
}
apply butn_permut_seq_with_len; [ easy | | ]. {
  destruct Hl as (Hp, Hl).
  rewrite permut_permut_isort; [ easy | easy | now rewrite Hl ].
} {
  specialize (isort_rank_permut_seq Nat.leb l) as H1.
  destruct Hl as (H2, H3).
  apply permut_seq_iff in H1.
  destruct H1 as (H4, H5).
  rewrite isort_rank_length in H4.
  apply H4, nth_In.
  now rewrite isort_rank_length, H3.
}
Qed.

(*
Theorem sign_diff_mul :
  rngl_has_opp = true →
   ∀ a b c d,
  (sign_diff a b * sign_diff c d)%L =
  sign_diff (a * c + b * d) (a * d + b * c).
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
unfold sign_diff.
remember (a ?= b) as b1 eqn:Hb1; symmetry in Hb1.
remember (c ?= d) as b2 eqn:Hb2; symmetry in Hb2.
move b2 before b1.
destruct b1. {
  rewrite rngl_mul_0_l; [ | easy ].
  apply Nat.compare_eq_iff in Hb1; subst b.
  now rewrite Nat.add_comm, Nat.compare_refl.
} {
  destruct b2. {
    rewrite rngl_mul_0_r; [ | easy ].
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
    rewrite rngl_mul_0_r; [ | easy ].
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
  → (sign_diff' a b * sign_diff' c d)%L =
     sign_diff (a * c + b * d) (a * d + b * c).
Proof.
intros Hop * Hab Hcd.
rewrite sign_diff'_sign_diff; [ | easy ].
rewrite sign_diff'_sign_diff; [ | easy ].
now apply sign_diff_mul.
Qed.
*)

Theorem map_nth_permut_seq : ∀ n la lb,
  permut_seq_with_len n la
  → permut_seq_with_len n lb
  → permut_seq (map (λ i, nth i la 0) lb).
Proof.
intros * (Hap, Hal) (Hbp, Hbl).
apply permut_seq_iff.
split. {
  intros j Hj.
  apply in_map_iff in Hj.
  destruct Hj as (k & Hkj & Hk).
  rewrite <- Hkj.
  rewrite map_length, Hbl, <- Hal.
  apply permut_seq_iff in Hap.
  apply Hap, nth_In.
  rewrite Hal, <- Hbl.
  apply permut_seq_iff in Hbp.
  now apply Hbp.
} {
  apply nat_NoDup.
  rewrite map_length.
  intros j k Hj Hk Hjk.
  assert (Hab : permut_seq_with_len n (la ° lb)) by now apply comp_permut_seq_with_len.
  destruct Hab as (Hab, _).
  apply permut_seq_iff in Hab.
  destruct Hab as (_, Hab).
  apply (NoDup_nat _ Hab) in Hjk; [ easy | | ]; now rewrite comp_length.
}
Qed.

Theorem fold_comp_list : ∀ la lb, map (λ i, nth i la 0) lb = la ° lb.
Proof. easy. Qed.

Theorem permut_comp_cancel_l : ∀ n la lb lc,
  NoDup la
  → length la = n
  → permut_seq_with_len n lb
  → permut_seq_with_len n lc
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
assert (H : ∀ i, nth (nth i lb 0) la 0 = nth (nth i lc 0) la 0). {
  intros j.
  destruct (lt_dec j n) as [Hjn| Hjn]. 2: {
    apply Nat.nlt_ge in Hjn.
    rewrite (nth_overflow lb); [ | destruct Hb; congruence ].
    rewrite (nth_overflow lc); [ | destruct Hc; congruence ].
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
  apply permut_seq_iff in Hbp.
  apply Hbp, nth_In.
  congruence.
} {
  destruct Hc as (Hcp, Hcl).
  rewrite Hal, <- Hcl.
  apply permut_seq_iff in Hcp.
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
  → permut_seq_with_len n lc
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
unfold "°".
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
symmetry.
apply List_map_nth_seq.
Qed.

Arguments comp_1_r n%nat [la]%list.

Theorem collapse_permut_seq_with_len : ∀ l, permut_seq_with_len (length l) (collapse l).
Proof.
intros.
apply isort_rank_permut_seq_with_len.
apply isort_rank_length.
Qed.

Theorem permut_isort_rank_involutive : ∀ la,
  permut_seq la
  → isort_rank Nat.leb (isort_rank Nat.leb la) = la.
Proof.
intros * Hp.
remember (isort_rank Nat.leb la) as lb eqn:Hlb.
apply (@permut_comp_cancel_r (length lb)) with (lc := lb). {
  now apply isort_rank_permut_seq_with_len.
} {
  now rewrite Hlb, isort_rank_length.
} {
  rewrite Hlb, isort_rank_length.
  now apply isort_rank_permut_seq_with_len.
}
subst lb.
rewrite comp_isort_rank_r.
rewrite permut_comp_isort_rank_l; [ | apply isort_rank_permut_seq ].
rewrite isort_rank_length; symmetry.
now apply permut_isort_leb.
Qed.

Theorem collapse_lt_compat : ∀ l i j,
  i < length l
  → j < length l
  → nth i l 0 < nth j l 0
  → nth i (collapse l) 0 < nth j (collapse l) 0.
Proof.
intros l j i Hj Hi Hc2.
specialize (collapse_permut_seq_with_len l) as Hc.
specialize (isort_rank_permut_seq_with_len Nat.leb (length l) eq_refl) as Hr.
apply Nat.nle_gt; intros Hc1.
destruct (Nat.eq_dec (nth i (collapse l) 0) (nth j (collapse l) 0))
  as [H| H]. {
  destruct Hc as (Hca, Hcl).
  apply permut_seq_iff in Hca.
  destruct Hca as (Hca, Hcn).
  apply (NoDup_nat _ Hcn) in H; cycle 1. {
    now rewrite collapse_length.
  } {
    now rewrite collapse_length.
  }
  now subst j; apply Nat.lt_irrefl in Hc2.
}
assert (H' : nth i (collapse l) 0 < nth j (collapse l) 0) by flia Hc1 H.
clear Hc1 H; rename H' into Hc1.
unfold collapse in Hc1.
remember (isort_rank Nat.leb l) as lrank eqn:Hlr.
remember (nth i (collapse l) 0) as i' eqn:Hi'.
assert (Hii' : i = nth i' lrank 0). {
  subst i'; unfold collapse.
  rewrite <- Hlr; symmetry.
  destruct Hr as (Hrp, Hrl).
  apply permut_permut_isort; [ easy | now rewrite Hrl ].
}
rewrite Hii' in Hc1.
rewrite permut_isort_permut in Hc1; [ | now destruct Hr | ]. 2: {
  rewrite Hi'.
  destruct Hc as (Hca, Hcl).
  apply permut_seq_iff in Hca.
  destruct Hca as (Hca, Hcn).
  rewrite Hcl in Hca.
  rewrite Hlr, isort_rank_length.
  apply Hca, nth_In.
  now rewrite Hcl.
}
remember (nth j (collapse l) 0) as j' eqn:Hj'.
assert (Hjj' : j = nth j' lrank 0). {
  subst j'; unfold collapse.
  rewrite <- Hlr; symmetry.
  destruct Hr as (Hrp, Hrl).
  apply permut_permut_isort; [ easy | now rewrite Hrl ].
}
rewrite Hjj' in Hc1.
rewrite permut_isort_permut in Hc1; [ | now destruct Hr | ]. 2: {
  rewrite Hj'.
  destruct Hc as (Hca, Hcl).
  apply permut_seq_iff in Hca.
  destruct Hca as (Hca, Hcn).
  rewrite Hcl in Hca.
  rewrite Hlr, isort_rank_length.
  apply Hca, nth_In.
  now rewrite Hcl.
}
rewrite Hii', Hjj' in Hc2.
rewrite Hlr in Hc2.
assert (Hi'l : i' < length l). {
  rewrite Hi'.
  destruct Hc as (Hca, Hcl).
  apply permut_seq_iff in Hca.
  destruct Hca as (Hca, Hcn).
  rewrite Hcl in Hca.
  apply Hca, nth_In.
  now rewrite collapse_length.
}
assert (Hj'l : j' < length l). {
  rewrite Hj'.
  destruct Hc as (Hca, Hcl).
  apply permut_seq_iff in Hca.
  destruct Hca as (Hca, Hcn).
  rewrite Hcl in Hca.
  apply Hca, nth_In.
  now rewrite collapse_length.
}
rewrite nth_nth_isort_rank in Hc2; [ | easy ].
rewrite nth_nth_isort_rank in Hc2; [ | easy ].
specialize (sorted_isort Nat_leb_total_relation l) as Hsl.
rewrite (isort_isort_rank _ 0) in Hsl.
rewrite <- Hlr in Hsl.
specialize sorted_strongly_sorted as H1.
specialize (H1 _ _ Nat_leb_trans _ Hsl).
specialize strongly_sorted_if as H2.
specialize (H2 _ _ Nat_leb_trans _ H1 0).
rewrite map_length, Hlr, isort_rank_length in H2.
specialize (H2 i' j' Hi'l Hj'l Hc1).
apply Nat.leb_le in H2.
rewrite <- Hlr in H2.
rewrite (isort_isort_rank _ 0) in Hc2.
rewrite <- Hlr in Hc2.
now apply Nat.nle_gt in Hc2.
Qed.

Theorem collapse_keeps_order : ∀ l,
  NoDup l
  → ∀ i j,  i < length l → j < length l
  → (nth i (collapse l) 0 ?= nth j (collapse l) 0) =
    (nth i l 0 ?= nth j l 0).
Proof.
intros * Hnd * Hi Hj.
remember (nth i (collapse l) 0 ?= nth j (collapse l) 0) as c1 eqn:Hc1.
remember (nth i l 0 ?= nth j l 0) as c2 eqn:Hc2.
specialize (collapse_permut_seq_with_len l) as Hc.
specialize (isort_rank_permut_seq_with_len Nat.leb (length l) eq_refl) as Hr.
move c2 before c1.
symmetry in Hc1, Hc2.
destruct c1. {
  apply Nat.compare_eq_iff in Hc1.
  destruct Hc as (Hca, Hcl).
  apply permut_seq_iff in Hca.
  destruct Hca as (Hca, Hcn).
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

Definition keep_order la lb :=
  ∀ i j,  i < length la → j < length la →
  (nth i la 0 ?= nth j la 0) = (nth i lb 0 ?= nth j lb 0).

Theorem ε_keep_order :
  ∀ la lb, keep_order la lb → length la = length lb → ε la = ε lb.
Proof.
intros * Hko Hab.
revert lb Hko Hab.
induction la as [| a]; intros. {
  symmetry in Hab.
  now apply length_zero_iff_nil in Hab; subst lb.
}
destruct lb as [| b]; [ easy | ].
cbn in Hab; apply Nat.succ_inj in Hab.
cbn; rewrite IHla with (lb := lb); [ | | easy ]. 2: {
  intros i j Hi Hj.
  apply (Hko (S i) (S j)); now cbn; apply -> Nat.succ_lt_mono.
}
f_equal.
clear IHla.
move b before a.
revert a b lb Hko Hab.
induction la as [| a']; intros. {
  symmetry in Hab.
  now apply length_zero_iff_nil in Hab; subst lb.
}
destruct lb as [| b']; [ easy | ].
cbn in Hab; apply Nat.succ_inj in Hab.
cbn.
specialize (Hko 0 1) as H1; cbn in H1.
rewrite <- H1; [ | easy | now apply -> Nat.succ_lt_mono ].
remember (a ?= a') as c eqn:Hc; symmetry in Hc.
assert (H : ε_aux a la = ε_aux b lb). {
  apply IHla; [ | easy ].
  intros i j Hi Hj.
  destruct i. {
    destruct j; [ now do 2 rewrite Nat.compare_refl | ].
    apply (Hko 0 (S (S j))); [ now cbn | ].
    now cbn; apply -> Nat.succ_lt_mono.
  }
  destruct j. {
    apply (Hko (S (S i)) 0); [ | now cbn ].
    now cbn; apply -> Nat.succ_lt_mono.
  }
  apply (Hko (S (S i)) (S (S j))); now cbn; apply -> Nat.succ_lt_mono.
}
destruct c; [ easy | easy | now f_equal ].
Qed.

Theorem ε_collapse_ε :
  rngl_has_opp_or_subt = true →
  ∀ l, NoDup l → ε (collapse l) = ε l.
Proof.
intros Hos * Hnd.
apply ε_keep_order; [ | apply collapse_length ].
intros i j Hi Hj.
rewrite collapse_length in Hi, Hj.
now apply (collapse_keeps_order Hnd).
Qed.

Theorem permut_isort : ∀ ord,
  antisymmetric ord
  → transitive ord
  → total_relation ord
  → ∀ n l p q,
  permut_seq_with_len n p
  → permut_seq_with_len n q
  → isort ord (l ° p) = isort ord (l ° q).
Proof.
intros * Hant Htr Htot * Hp Hq.
apply (isort_when_permuted Nat.eqb_eq); [ easy | easy | easy | ].
unfold "°".
apply (permutation_map Nat.eqb_eq Nat.eqb_eq).
apply (permutation_trans Nat.eqb_eq) with (lb := seq 0 n). {
  now destruct Hp as (Hp1, Hp2); rewrite <- Hp2.
} {
  destruct Hq as (Hq1, Hq2); rewrite <- Hq2.
  now apply (permutation_sym Nat.eqb_eq).
}
Qed.

Theorem isort_comp_permut_r : ∀ l p,
  permut_seq_with_len (length l) p
  → isort Nat.leb (l ° p) = isort Nat.leb l.
Proof.
intros * Hp.
symmetry.
rewrite <- (comp_1_r (length l) eq_refl) at 1.
specialize (permut_isort Nat_leb_antisym Nat_leb_trans) as H1.
specialize (H1 Nat_leb_total_relation).
apply (H1 (length l)); [ | easy ].
apply seq_permut_seq_with_len.
Qed.

Theorem permut_isort_rank_comp : ∀ n la lb,
  NoDup la
  → length la = n
  → permut_seq_with_len n lb
  → isort_rank Nat.leb (la ° lb) =
    isort_rank Nat.leb lb ° isort_rank Nat.leb la.
Proof.
intros * Ha Hal Hb.
apply permut_comp_cancel_l with (n := n) (la := la ° lb). {
  destruct Hb as (Hba, Hbl).
  apply permut_seq_iff in Hba.
  destruct Hba as (Hba, Hbn).
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
  apply isort_rank_permut_seq_with_len.
  now rewrite comp_length; destruct Hb.
} {
  destruct Hb.
  now apply comp_permut_seq_with_len; apply isort_rank_permut_seq_with_len.
}
rewrite comp_isort_rank_r.
rewrite <- (permut_comp_assoc n); cycle 1. {
  now destruct Hb.
} {
  destruct Hb as (Hba, Hbl).
  apply permut_seq_iff in Hba.
  destruct Hba as (Hba, Hbn).
  now apply comp_permut_seq_with_len; apply isort_rank_permut_seq_with_len.
} {
  apply (comp_permut_seq n). {
    apply isort_rank_permut_seq_with_len.
    now destruct Hb.
  } {
    now apply isort_rank_permut_seq_with_len.
  }
}
rewrite (permut_comp_assoc n) with (f := lb); cycle 1. {
  destruct Hb as (Hba, Hbl).
  apply permut_seq_iff in Hba.
  destruct Hba as (Hba, Hbn).
  now rewrite isort_rank_length.
} {
  now apply isort_rank_permut_seq_with_len.
} {
  apply isort_rank_permut_seq.
}
rewrite comp_isort_rank_r.
destruct Hb as (Hbp, Hbl).
rewrite (permut_isort_leb Hbp).
rewrite comp_1_l. 2: {
  intros i Hi.
  rewrite Hbl, <- Hal.
  now apply in_isort_rank in Hi.
}
rewrite comp_isort_rank_r.
apply isort_comp_permut_r.
now rewrite Hal, <- Hbl.
Qed.

Arguments permut_isort_rank_comp n%nat [la lb]%list.

Theorem permut_collapse : ∀ la,
  permut_seq la
  → collapse la = la.
Proof.
intros * Ha.
unfold collapse.
now apply permut_isort_rank_involutive.
Qed.

Theorem collapse_comp : ∀ la lb,
  NoDup la
  → permut_seq lb
  → length la = length lb
  → collapse (la ° lb) = collapse la ° lb.
Proof.
intros * Ha Hb Hab.
unfold collapse.
symmetry.
rewrite <- (permut_isort_rank_involutive Hb) at 1.
rewrite (permut_isort_rank_comp (length lb)); [ | easy | easy | easy ].
rewrite (permut_isort_rank_comp (length lb)); [ easy | | | ]. {
  apply NoDup_isort_rank.
} {
  apply isort_rank_length.
} {
  now apply isort_rank_permut_seq_with_len.
}
Qed.

Theorem isort_comp_collapse : ∀ la,
  isort Nat.leb la ° collapse la = la.
Proof.
intros.
apply List_eq_iff.
rewrite comp_length, collapse_length.
split; [ easy | ].
intros d i.
unfold comp_list.
destruct (lt_dec i (length la)) as [Hila| Hila]. 2: {
  apply Nat.nlt_ge in Hila.
  rewrite nth_overflow; [ | now rewrite map_length, collapse_length ].
  now rewrite nth_overflow.
}
rewrite nth_indep with (d' := 0). 2: {
  now rewrite map_length, collapse_length.
}
symmetry.
rewrite nth_indep with (d' := 0); [ | easy ].
symmetry.
clear d.
rewrite (isort_isort_rank _ 0).
rewrite (List_map_nth' 0); [ | now rewrite collapse_length ].
rewrite (List_map_nth' 0). 2: {
  unfold collapse.
  apply isort_rank_ub.
  now intros H; apply eq_isort_rank_nil in H; subst la.
}
unfold collapse.
rewrite permut_permut_isort with (i := i); [ easy | | ]. 2: {
  now rewrite isort_rank_length.
}
apply isort_rank_permut_seq.
Qed.

Theorem sorted_permuted_comp_collapse : ∀ la lb,
  sorted Nat.leb la
  → permutation Nat.eqb la lb
  → la ° collapse lb = lb.
Proof.
intros * Hs Hp.
assert (Hba : isort Nat.leb lb = la). {
  rewrite isort_when_permuted with (eqb := Nat.eqb) (lb := la). {
    now apply isort_when_sorted.
  } {
    unfold equality; apply Nat.eqb_eq.
  } {
    apply Nat_leb_antisym.
  } {
    apply Nat_leb_trans.
  } {
    apply Nat_leb_total_relation.
  } {
    apply permutation_sym; [ | easy ].
    unfold equality; apply Nat.eqb_eq.
  }
}
rewrite <- Hba.
clear la Hs Hp Hba.
rename lb into la.
apply isort_comp_collapse.
Qed.

Theorem NoDup_comp_iff : ∀ la lb,
  permut_seq_with_len (length la) lb
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
    apply permut_seq_iff in Hbp.
    now apply Hbp, nth_In.
  } {
    rewrite <- Hbl.
    apply permut_seq_iff in Hbp.
    now apply Hbp, nth_In.
  }
  apply permut_seq_iff in Hbp.
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
  remember (nth i (isort_rank Nat.leb lb) 0) as i' eqn:Hi'.
  remember (nth j (isort_rank Nat.leb lb) 0) as j' eqn:Hj'.
  specialize (H1 i' j').
  assert (H : i' < length lb). {
    rewrite Hi'.
    apply isort_rank_ub.
    now intros H; rewrite H in Hi.
  }
  specialize (H1 H); clear H.
  assert (H : j' < length lb). {
    rewrite Hj'.
    apply isort_rank_ub.
    now intros H; rewrite H in Hi.
  }
  specialize (H1 H); clear H.
  assert (H : nth i' (la ° lb) 0 = nth j' (la ° lb) 0). {
    rewrite Hi', Hj'.
    unfold "°".
    rewrite (List_map_nth' 0). 2: {
      apply isort_rank_ub.
      now intros H; subst lb.
    }
    rewrite (List_map_nth' 0). 2: {
      apply isort_rank_ub.
      now intros H; subst lb.
    }
    rewrite permut_permut_isort; [ | easy | easy ].
    rewrite permut_permut_isort; [ | easy | easy ].
    easy.
  }
  specialize (H1 H); clear H.
  rewrite Hi', Hj' in H1.
  assert (H : permut_seq (isort_rank Nat.leb lb)). {
    now apply isort_rank_permut_seq.
  }
  apply permut_seq_iff in H.
  destruct H as (Hra, Hrn).
  apply (NoDup_nat _ Hrn) in H1; [ easy | | ]. {
    now rewrite isort_rank_length.
  } {
    now rewrite isort_rank_length.
  }
}
Qed.

Theorem ε_dup :
  rngl_has_opp = true →
  ∀ i l1 l2 l3, ε (l1 ++ i :: l2 ++ i :: l3) = 0%L.
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos after Hop.
revert i l2 l3.
induction l1 as [| j]; intros. {
  rewrite app_nil_l; cbn.
  rewrite (ε_aux_dup Hop).
  apply (rngl_mul_0_l Hos).
}
cbn.
rewrite IHl1.
apply (rngl_mul_0_r Hos).
Qed.

Theorem ε_when_dup :
  rngl_has_opp = true →
  ∀ la,
  ¬ NoDup la
  → ε la = 0%L.
Proof.
intros Hop * Haa.
assert (H : no_dup Nat.eqb la = false). {
  apply Bool.negb_true_iff.
  apply Bool.eq_true_not_negb.
  intros H; apply Haa.
  now apply (no_dup_NoDup Nat.eqb_eq).
}
clear Haa; rename H into Haa.
apply (no_dup_false_iff Nat.eqb_eq) in Haa.
destruct Haa as (l1 & l2 & l3 & i & Haa).
subst la.
apply (ε_dup Hop).
Qed.

Theorem sign_comp :
  rngl_has_opp = true →
  ∀ la lb,
  permut_seq_with_len (length la) lb
  → ε (la ° lb) = (ε la * ε lb)%L.
Proof.
intros Hop * Hbp.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
specialize (Hos (or_introl Hop)).
move Hos before Hop.
destruct (ListDec.NoDup_dec Nat.eq_dec la) as [Haa| Haa]. 2: {
  symmetry.
  rewrite ε_when_dup; [ | easy | easy ].
  symmetry.
  rewrite ε_when_dup; [ | easy | ]. 2: {
    intros H; apply Haa; clear Haa.
    now apply NoDup_comp_iff in H.
  }
  symmetry.
  apply (rngl_mul_0_l Hos).
}
rewrite <- ε_collapse_ε; [ | easy | now apply NoDup_comp_iff ].
rewrite collapse_comp; [ | easy | now destruct Hbp | now destruct Hbp ].
rewrite <- (ε_collapse_ε Hos Haa).
rewrite <- (collapse_length la) in Hbp.
destruct Hbp as (Hb, Hab).
clear Haa.
specialize (collapse_permut_seq_with_len la) as Ha.
destruct Ha as (Ha, _).
remember (collapse la) as lc eqn:Hlc.
clear la Hlc; rename lc into la.
move Ha after Hb; move la after lb.
remember (length la) as n eqn:Hla; symmetry in Hla.
rename Hab into Hlb.
assert (H : permut_seq_with_len n la) by easy.
clear Ha Hla; rename H into Ha.
assert (H : permut_seq_with_len n lb) by easy.
clear Hb Hlb; rename H into Hb.
revert la lb Ha Hb.
induction n; intros; cbn. {
  destruct Ha as (_, Hla).
  destruct Hb as (_, Hlb).
  apply length_zero_iff_nil in Hla, Hlb; subst la lb.
  symmetry; apply rngl_mul_1_l.
}
specialize (permut_without_highest Ha) as H1.
destruct H1 as (i & Hi & Hin & H1).
unfold "°".
specialize permut_list_surj as H2.
specialize (H2 i lb).
assert (H : permut_seq lb) by now destruct Hb.
specialize (H2 H); clear H.
replace (length la) with (S n) in Hi by now destruct Ha.
replace (length lb) with (S n) in H2 by now destruct Hb.
specialize (H2 Hi).
destruct H2 as (j & Hj & Hji).
specialize nth_split as H2.
specialize (H2 _ j lb 0).
replace (length lb) with (S n) in H2 by now destruct Hb.
specialize (H2 Hj).
destruct H2 as (lb1 & lb2 & Hlb & Hjl1).
rewrite Hji in Hlb.
subst lb.
rewrite map_app.
cbn.
rewrite Hin.
rewrite (ε_app_cons Hop). 2: {
  intros k Hk.
  apply in_app_or in Hk.
  clear - Hk Ha Hb Hin Hi.
  move Ha before Hb.
  move k before i.
(**)
  destruct Ha as (Ha, Hla).
  destruct Hb as (Hb, Hlb).
  generalize Ha; intros Ha'.
  apply permut_seq_iff in Ha'.
  destruct Ha' as (Ha1, Ha2).
  unfold AllLt in Ha1.
  generalize Hb; intros Hb'.
  apply permut_seq_iff in Hb'.
  destruct Hb' as (Hb1, Hb2).
  unfold AllLt in Hb1.
  unfold permut_seq in Ha, Hb.
  rewrite Hla in Ha.
  rewrite Hlb in Hb.
  destruct Hk as [Hk| Hk]. {
    apply in_map_iff in Hk.
    destruct Hk as (u & Huk & Hu).
    subst k.
    apply (permutation_in_iff Nat.eqb_eq) with (a := u) in Hb.
    apply (permutation_in_iff Nat.eqb_eq) with (a := u) in Ha.
    assert (H : u ∈ lb1 ++ i :: lb2) by now apply in_or_app; left.
    apply Hb in H.
    apply in_seq in H; cbn in H; destruct H as (_, H).
    rewrite <- Hla in H.
    rewrite Hla in Ha1.
    specialize (Ha1 (nth u la 0)) as H2.
    assert (H5 : nth u la 0 ∈ la) by now apply nth_In.
    specialize (H2 H5).
    destruct (Nat.eq_dec (nth u la 0) n) as [Hn| Hn]; [ | flia H2 Hn ].
    exfalso.
    rewrite <- Hin in Hn.
    rewrite <- Hla in Hi.
    specialize (NoDup_nat la Ha2 u i H Hi Hn) as H3.
    subst u.
    apply NoDup_app_iff in Hb2.
    destruct Hb2 as (Hb2 & Hb3 & Hb4).
    specialize (Hb4 _ Hu).
    now apply Hb4; left.
  } {
    apply in_map_iff in Hk.
    destruct Hk as (u & Huk & Hu).
    subst k.
    apply (permutation_in_iff Nat.eqb_eq) with (a := u) in Hb.
    apply (permutation_in_iff Nat.eqb_eq) with (a := u) in Ha.
    assert (H : u ∈ lb1 ++ i :: lb2) by now apply in_or_app; right; right.
    apply Hb in H.
    apply in_seq in H; cbn in H; destruct H as (_, H).
    rewrite <- Hla in H.
    rewrite Hla in Ha1.
    specialize (Ha1 (nth u la 0)) as H2.
    assert (H5 : nth u la 0 ∈ la) by now apply nth_In.
    specialize (H2 H5).
    destruct (Nat.eq_dec (nth u la 0) n) as [Hn| Hn]; [ | flia H2 Hn ].
    exfalso.
    rewrite <- Hin in Hn.
    rewrite <- Hla in Hi.
    specialize (NoDup_nat la Ha2 u i H Hi Hn) as H3.
    subst u.
    apply NoDup_app_iff in Hb2.
    destruct Hb2 as (Hb2 & Hb3 & Hb4).
    now apply NoDup_cons_iff in Hb3.
  }
}
rewrite map_length.
rewrite <- map_app.
rewrite fold_comp_list.
specialize permut_without_highest as H2.
specialize (H2 n (lb1 ++ i :: lb2) Hb).
destruct H2 as (k & Hkl & Hn & H2).
rewrite app_length in Hkl; cbn in Hkl.
rewrite Nat.add_succ_r, <- app_length in Hkl.
specialize (IHn _ _ H1 H2) as H3.
remember (lb1 ++ i :: lb2) as lb eqn:Hlb.
rename H2 into H4.
specialize nth_split as H2.
specialize (H2 _ i la 0).
replace (length la) with (S n) in H2 by now destruct Ha.
specialize (H2 Hi).
destruct H2 as (la1 & la2 & Hla & Hil1).
rewrite Hin in Hla.
subst la.
rewrite (ε_app_cons Hop). 2: {
...
permut_without_highest:
  ∀ (n : nat) (l : list nat),
    permut_seq_with_len (S n) l
    → ∃ i : nat,
        i < length l ∧ nth i l 0 = n ∧ permut_seq_with_len n (butn i l)
...
Search (_ ++ _ :: _).
in_split:
  ∀ (A : Type) (x : A) (l : list A),
    x ∈ l → ∃ l1 l2 : list A, l = l1 ++ x :: l2
nth_split:
  ∀ (A : Type) (n : nat) (l : list A) (d : A),
    n < length l → ∃ l1 l2 : list A, l = l1 ++ nth n l d :: l2 ∧ length l1 = n
...
remember (la ° lb) as lc eqn:Hlc; symmetry in Hlc.
revert la lb Ha Hb Hab Hlc.
induction lc as [| c]; intros. {
  unfold "°" in Hlc.
  apply map_eq_nil in Hlc; subst lb.
  symmetry in Hab; apply length_zero_iff_nil in Hab; subst la.
  symmetry; apply rngl_mul_1_l.
}
cbn.
unfold "°" in Hlc.
...
destruct lb as [| b]; [ easy | cbn in Hlc |-* ].
injection Hlc; clear Hlc; intros Hlc Hc.
...
(**)
unfold permut_seq in Ha, Hb.
apply (permutation_sym Nat.eqb_eq) in Hb.
apply (permutation_trans Nat.eqb_eq) with (la := la) in Hb. 2: {
  now rewrite <- H2 in Ha.
}
(**)
clear Ha.
(**)
revert lb Hb H2.
induction la as [| a]; intros. {
  apply length_zero_iff_nil in H2; subst lb.
  cbn; symmetry; apply rngl_mul_1_l.
}
apply permutation_cons_l_iff in Hb.
remember (extract _ _) as lal eqn:Hlal; symmetry in Hlal.
destruct lal as [((bef, x), aft) | ]; [ | easy ].
apply extract_Some_iff in Hlal.
destruct Hlal as (Hbef & H & Hli).
apply Nat.eqb_eq in H; subst x.
subst lb.
rewrite app_length in H2; cbn in H2.
rewrite Nat.add_succ_r in H2.
apply Nat.succ_inj in H2.
rewrite <- app_length in H2.
specialize (IHla _ Hb H2) as H1.
cbn.
unfold "°".
rewrite map_app.
cbn - [ nth ].
Search (ε (_ ++ _)).
...
symmetry.
...
rewrite <- ε_collapse_ε; [ | easy ].
symmetry.
Search collapse.
...
Check signature_comp_fun_expand_1.
Search ε.
Print ε'.
...
  apply (signature_comp_fun_expand_1 Hif (length la)); [ | easy | ]. {
    apply collapse_permut_seq_with_len.
  }
  destruct Hif as (Hop, Hic, Hin, Hit, Hde, Hch).
  rewrite signature_comp_fun_expand_2_1; try easy.
  rewrite signature_comp_fun_expand_2_2; try easy.
  apply signature_comp_fun_changement_of_variable; try easy.
  apply collapse_permut_seq_with_len.
}
Qed.
*)


Theorem sign_comp : in_charac_0_field →
  ∀ la lb,
  permut_seq_with_len (length la) lb
  → ε (la ° lb) = (ε la * ε lb)%L.
Proof.
intros Hif * Hbp.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hos.
assert (H : rngl_has_opp = true) by now destruct Hif.
specialize (Hos (or_introl H)); clear H.
move Hos before Hif.
destruct (ListDec.NoDup_dec Nat.eq_dec la) as [Haa| Haa]. 2: {
  symmetry.
  rewrite ε_when_dup; [ | now destruct Hif | now destruct Hif | easy ].
  symmetry.
  rewrite ε_when_dup; [ | now destruct Hif | now destruct Hif | ]. 2: {
    intros H; apply Haa; clear Haa.
    now apply NoDup_comp_iff in H.
  }
  symmetry.
  now apply rngl_mul_0_l.
} {
  rewrite <- ε_collapse_ε; [ | now apply NoDup_comp_iff ].
  rewrite collapse_comp; [ | easy | now destruct Hbp | now destruct Hbp ].
  symmetry.
  rewrite <- ε_collapse_ε; [ | easy ].
  symmetry.
  apply (signature_comp_fun_expand_1 Hif (length la)); [ | easy | ]. {
    apply collapse_permut_seq_with_len.
  }
  destruct Hif as (Hop, Hic, Hin, Hit, Hde, Hch).
  rewrite signature_comp_fun_expand_2_1; try easy.
  rewrite signature_comp_fun_expand_2_2; try easy.
  apply signature_comp_fun_changement_of_variable; try easy.
  apply collapse_permut_seq_with_len.
}
Qed.

(* *)

Theorem canon_sym_gr_succ_values : ∀ n k σ σ',
  σ = canon_sym_gr_list (S n) k
  → σ' = canon_sym_gr_list n (k mod n!)
  → ∀ i,
    nth i σ 0 =
    match i with
    | 0 => k / n!
    | S i' =>
        if ((k <? n!) && (n <=? i'))%bool then 0
        else succ_when_ge (k / n!) (nth i' σ' 0)
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
    unfold succ_when_ge.
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
  rngl_mul_is_comm = true →
  rngl_has_opp = true →
  ∀ n k,
  k < (S n)!
  → ε (canon_sym_gr_list (S n) k) =
    (minus_one_pow (k / n!) * ε (canon_sym_gr_list n (k mod n!)))%L.
Proof.
intros Hic Hop * Hkn.
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
      (if x <? nth i σ' 0 + 1 then 1%L else (-1)%L). 2: {
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
  assert (Hp' : permut_seq_with_len n σ'). {
    rewrite Hσ'.
    now apply canon_sym_gr_list_permut_seq_with_len.
  }
  assert (Hp : permut_seq_with_len (S n) σ). {
    rewrite Hσ.
    now apply canon_sym_gr_list_permut_seq_with_len.
  }
  rewrite rngl_product_change_var with
    (g := λ i, nth i (isort_rank Nat.leb σ') 0) (h := λ i, nth i σ' 0). 2: {
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
      apply permut_seq_iff in Hp'p.
      destruct Hp'p as (Hp'a, Hp'n).
      apply Hp'a, nth_In.
      now rewrite Hp'l.
    }
    easy.
  }
  cbn - [ "<?" seq ].
  rewrite (rngl_product_list_permut _ Nat.eqb_eq) with
      (lb := seq 0 n); [ | easy | ]. 2: {
    apply permut_seq_iff in Hp'p.
    destruct Hp'p as (Hp'a, Hp'n).
    rewrite <- Hp'l at 1.
    rewrite <- List_map_nth_seq, <- Hp'l.
    now apply permut_seq_iff.
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
    replace x with (nth 0 σ 0) by now rewrite H1.
    destruct Hp as (Hp, Hp3).
    apply permut_seq_iff in Hp.
    destruct Hp as (Hp1, Hp2).
    rewrite <- Hp3.
    apply Hp1, nth_In.
    rewrite Hp3; flia.
  }
  remember (∏ (i = _, _), _)%L as y eqn:Hy.
  rewrite all_1_rngl_product_1. 2: {
    intros i Hi.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec x (i + 1)) as [H2| H2]; [ easy | ].
    flia Hi H2.
  }
  subst y; rewrite rngl_mul_1_r.
  erewrite rngl_product_eq_compat. 2: {
    intros i (_, Hi).
    replace (if x <? i + 1 then 1%L else _) with (-1)%L. 2: {
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
destruct (le_dec (k / n!) (nth j σ' 0)) as [Hsfj| Hsfj]. {
  destruct (le_dec (k / n!) (nth i σ' 0)) as [Hsfi| Hsfi]. {
    now do 2 rewrite Nat.add_1_r.
  }
  rewrite Nat.add_0_r.
  replace (nth j σ' 0 + 1 ?= nth i σ' 0) with Gt. 2: {
    symmetry; apply Nat.compare_gt_iff.
    flia Hsfi Hsfj.
  }
  replace (nth j σ' 0 ?= nth i σ' 0) with Gt. 2: {
    symmetry; apply Nat.compare_gt_iff.
    flia Hsfi Hsfj.
  }
  easy.
}
destruct (le_dec (k / n!) (nth i σ' 0)) as [Hsfi| Hsfi]. {
  rewrite Nat.add_0_r.
  replace (nth j σ' 0 ?= nth i σ' 0 + 1) with Lt. 2: {
    symmetry; apply Nat.compare_lt_iff.
    flia Hsfi Hsfj.
  }
  replace (nth j σ' 0 ?= nth i σ' 0) with Lt. 2: {
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
  → ∃ i : nat, i < n ∧ nth i (canon_sym_gr_list n k) 0 = j.
Proof.
intros * Hkn Hjn.
exists (nth j (canon_sym_gr_inv_list n k) 0).
split; [ now apply canon_sym_gr_inv_list_ub | ].
now apply canon_sym_gr_sym_gr_inv.
Qed.

Theorem NoDup_ε_1_opp_1 :
  rngl_has_opp = true →
  ∀ σ, NoDup σ → ε σ = 1%L ∨ ε σ = (-1)%L.
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
remember (nth j σ 0 ?= nth i σ 0) as b eqn:Hb.
symmetry in Hb.
destruct (lt_dec i j) as [Hij| Hij]; [ | now left ].
destruct b; [ | now right | now left ].
apply Nat.compare_eq_iff in Hb.
apply (NoDup_nat _ Hσ) in Hb; [ | flia Hj Hn1 | flia Hi Hn1 ].
flia Hi Hj Hb Hij.
Qed.

Theorem ε_1_opp_1_NoDup :
  rngl_has_opp = true →
  rngl_characteristic ≠ 1 →
  rngl_has_eqb = true →
  ∀ σ, ε σ = 1%L ∨ ε σ = (-1)%L → NoDup σ.
Proof.
intros Hop H10 Heq * Hσ.
destruct (ListDec.NoDup_dec Nat.eq_dec σ) as [H1| H1]; [ easy | ].
exfalso.
apply ε_when_dup in H1; [ | easy | easy ].
rewrite H1 in Hσ.
destruct Hσ as [Hσ| Hσ]; symmetry in Hσ. {
  now apply rngl_1_neq_0_iff in Hσ.
} {
  rewrite <- rngl_opp_0 in Hσ; [ | easy ].
  apply rngl_opp_inj in Hσ; [ | easy ].
  now apply rngl_1_neq_0_iff in Hσ.
}
Qed.

Theorem NoDup_ε_square :
  rngl_has_opp = true →
  ∀ σ, NoDup σ → (ε σ * ε σ = 1)%L.
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

(*
Theorem ε_seq : ∀ sta len, ε (seq sta len) = 1%L.
Proof.
intros.
destruct (Nat.eq_dec len 0) as [Hnz| Hnz]. {
  subst len; cbn.
  unfold ε; cbn.
  unfold iter_seq, iter_list; cbn.
  now do 2 rewrite rngl_mul_1_l.
}
unfold ε.
rewrite seq_length.
unfold sign_diff.
erewrite rngl_product_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_product_eq_compat. 2: {
    intros j Hj.
    rewrite seq_nth; [ | flia Hj Hnz ].
    rewrite seq_nth; [ | flia Hi Hnz ].
    replace (if _ <? _ then _ else _) with 1%L. 2: {
      symmetry.
      rewrite if_ltb_lt_dec.
      destruct (lt_dec i j) as [Hij| Hij]; [ | easy ].
      apply Nat.add_lt_mono_l with (p := sta) in Hij.
      now apply Nat.compare_gt_iff in Hij; rewrite Hij.
    }
    easy.
  }
  easy.
}
apply all_1_rngl_product_1.
intros i Hi.
now apply all_1_rngl_product_1.
Qed.
*)

End a.

Arguments ε {T}%type {ro}.
Arguments sign_diff {T}%type {ro} (u v)%nat.

Arguments ε_nil {T ro rp}.
Arguments ε_permut {T}%type {ro} (n k)%nat.
Arguments ε_of_sym_gr_permut_succ {T}%type {ro rp} Hic Hop (n k)%nat.
Arguments comp_permut_seq n%nat [σ₁ σ₂]%list.
Arguments map_nth_permut_seq n%nat [la lb]%list.
Arguments permut_isort_rank_comp n%nat [la lb]%list.
Arguments sign_comp {T}%type {ro rp} _ [la lb]%list.
Arguments transposition_signature {T}%type {ro rp} _ _ (n p q)%nat.
Arguments NoDup_ε_1_opp_1 {T}%type {ro rp} _  [σ].
Arguments NoDup_ε_square {T}%type {ro rp} _ [σ].
Arguments ε_when_dup {T ro rp} Hop Hde [la]%list.

Arguments minus_one_pow {T}%type {ro} n%nat.
Arguments minus_one_pow_add_r {T}%type {ro rp} Hop (i j)%nat.
Arguments minus_one_pow_mul_comm {T ro rp} Hop i%nat x%L.
Arguments minus_one_pow_succ {T}%type {ro rp} _ i%nat.
Arguments minus_one_pow_succ_succ {T}%type {ro rp} _ i%nat.
