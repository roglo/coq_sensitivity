(* Theorems of general usage, which could be (or not) in Coq library *)

Set Nested Proofs Allowed.

From Stdlib Require Import Utf8 Arith.
Require Import RingLike.PermutationFun.
Require Import RingLike.Utils RingLike.Misc.
Import List.

(* (a ^ b) mod c defined like that so that we can use "Compute"
   for testing; proved equal to (a ^ b) mod c just below *)

Fixpoint Nat_pow_mod_loop a b c :=
  match b with
  | 0 => 1 mod c
  | S b' => (a * Nat_pow_mod_loop a b' c) mod c
  end.

Definition Nat_pow_mod a b c := Nat_pow_mod_loop a b c.

(* *)

Theorem List_fold_left_mul_assoc : ∀ a b l,
  fold_left Nat.mul l a * b = fold_left Nat.mul l (a * b).
Proof.
intros.
revert a b.
induction l as [| c l]; intros; [ easy | ].
cbn; rewrite IHl.
now rewrite Nat.mul_shuffle0.
Qed.

Theorem Nat_div_less_small_iff : ∀ n a b,
  b ≠ 0
  → n * b ≤ a < (n + 1) * b
  ↔ a / b = n.
Proof.
intros * Hbz.
split; intros Hab. {
  replace a with (a - n * b + n * b) at 1 by now apply Nat.sub_add.
  rewrite Nat.div_add; [ | easy ].
  replace n with (0 + n) at 3 by easy; f_equal.
  apply Nat.div_small.
  apply Nat.add_lt_mono_r with (p := n * b).
  rewrite Nat.add_comm in Hab; cbn in Hab.
  now rewrite Nat.sub_add.
} {
  specialize (Nat.div_mod a b Hbz) as H1.
  rewrite Hab, Nat.mul_comm in H1.
  rewrite H1.
  split; [ apply Nat.le_add_r | ].
  rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
  apply Nat.add_lt_mono_l.
  now apply Nat.mod_upper_bound.
}
Qed.

Theorem Nat_eq_mod_sub_0 : ∀ a b c,
  a mod c = b mod c → (a - b) mod c = 0.
Proof.
intros * Hab.
destruct (Nat.eq_dec c 0) as [Hcz| Hcz]. {
  subst c; cbn in Hab |-*.
  subst; flia.
}
specialize (Nat.div_mod a c Hcz) as H1.
specialize (Nat.div_mod b c Hcz) as H2.
rewrite H1, H2, Hab.
rewrite (Nat.add_comm (c * (b / c))).
rewrite Nat.sub_add_distr, Nat.add_sub.
rewrite <- Nat.mul_sub_distr_l, Nat.mul_comm.
apply Nat.Div0.mod_mul.
Qed.

Theorem Nat_eq_div_1 : ∀ a b, a / b = 1 ↔ b ≤ a < 2 * b.
Proof.
intros.
split; intros Hab. {
  destruct (Nat.eq_dec b 0) as [Hbz| Hbz]; [ now subst b | ].
  apply Nat_div_less_small_iff in Hab; [ | easy ].
  now rewrite Nat.mul_1_l in Hab.
} {
  apply Nat_div_less_small.
  now rewrite Nat.mul_1_l.
}
Qed.

Theorem Nat_pow2_log2_up_succ :
  ∀ n, Nat.log2_up (S n) = S (Nat.log2_up n) ↔ 2 ^ Nat.log2_up n = n.
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
destruct (Nat.eq_dec n 1) as [H| H]; [ now subst n | ].
apply Nat.neq_0_lt_0 in Hnz.
assert (Hn1 : 1 < n). {
  destruct n; [ easy | ].
  destruct n; [ easy | ].
  now apply -> Nat.succ_lt_mono.
}
clear H.
split; intros Hn. {
  rewrite Nat.log2_up_eqn in Hn; [ | now apply -> Nat.succ_lt_mono ].
  apply Nat.succ_inj in Hn.
  cbn in Hn.
  apply Nat.log2_log2_up_exact in Hn; [ | easy ].
  destruct Hn as (m, Hm); subst n.
  now rewrite Nat.log2_up_pow2.
} {
  specialize (Nat.log2_up_succ_or n) as H1.
  destruct H1 as [H1| H1]; [ easy | ].
  exfalso.
  rewrite <- Hn in H1 at 1.
  rewrite Nat.log2_up_succ_pow2 in H1; [ | easy ].
  specialize (Nat.log2_up_eqn n Hn1) as H2.
  rewrite <- H1 in H2.
  apply Nat.succ_inj in H2.
  rewrite <- Hn in H2 at 2.
  rewrite Nat.log2_pred_pow2 in H2; [ | now apply Nat.log2_up_pos ].
  destruct (Nat.log2_up n); [ now cbn in Hn; subst n | ].
  cbn in H2.
  now apply Nat.neq_succ_diag_l in H2.
}
Qed.

Theorem Nat_log2_up_lt_twice : ∀ n, n ≠ 0 → 2 ^ Nat.log2_up n < 2 * n.
Proof.
intros * Hnz.
destruct n; [ easy | clear Hnz ].
specialize (Nat.log2_up_succ_or n) as H1.
destruct H1 as [H1| H1]. {
  rewrite H1.
  rewrite Nat.pow_succ_r'.
  apply Nat.mul_lt_mono_pos_l; [ easy | ].
  apply Nat_pow2_log2_up_succ in H1.
  now rewrite H1.
}
rewrite H1.
destruct n; [ now cbn | ].
specialize (Nat.log2_up_spec (S (S n))) as H2.
assert (H : 1 < S (S n)) by flia.
specialize (H2 H); clear H.
destruct H2 as (H2, H3).
rewrite <- Nat.sub_1_r in H2.
rewrite H1 in H2.
rewrite Nat.pow_sub_r in H2; [ | easy | ]. 2: {
  apply Nat.neq_0_lt_0.
  intros H.
  apply Nat.log2_up_null in H.
  apply Nat.succ_le_mono in H.
  now apply Nat.le_0_r in H; subst n.
}
rewrite Nat.pow_1_r in H2.
apply Nat.nle_gt.
intros H4.
apply Nat.nle_gt in H2.
apply H2; clear H2.
apply Nat.div_le_lower_bound; [ easy | ].
now rewrite H1 in H3.
Qed.

Theorem Nat_bezout_mul : ∀ a b c,
  Nat.Bezout a c 1
  → Nat.Bezout b c 1
  → Nat.Bezout (a * b) c 1.
Proof.
intros * (ua & uc & Hu) (vb & vc & Hv).
exists (ua * vb).
replace (ua * vb * (a * b)) with ((ua * a) * (vb * b)) by flia.
rewrite Hu, Hv.
exists (uc * vc * c + uc + vc).
ring.
Qed.

Theorem Nat_gcd_1_mul_l : ∀ a b c,
  Nat.gcd a c = 1
  → Nat.gcd b c = 1
  → Nat.gcd (a * b) c = 1.
Proof.
intros * Hac Hbc.
destruct (Nat.eq_dec c 0) as [Hcz| Hcz]. {
  now subst c; rewrite Nat.gcd_comm in Hac, Hbc; cbn in Hac, Hbc; subst a b.
}
destruct (Nat.eq_dec a 0) as [Haz| Haz]; [ now subst a | ].
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]. {
  now subst b; rewrite Nat.mul_0_r.
}
apply Nat.bezout_1_gcd.
apply Nat_bezout_mul. {
  rewrite <- Hac.
  apply Nat.gcd_bezout_pos.
  flia Haz.
} {
  rewrite <- Hbc.
  apply Nat.gcd_bezout_pos.
  flia Hbz.
}
Qed.

Theorem Nat_gcd_1_mul_r : ∀ a b c,
  Nat.gcd a b = 1
  → Nat.gcd a c = 1
  → Nat.gcd a (b * c) = 1.
Proof.
intros * Hab Hac.
rewrite Nat.gcd_comm.
now apply Nat_gcd_1_mul_l; rewrite Nat.gcd_comm.
Qed.

Theorem Nat_gcd_le_l : ∀ a b, a ≠ 0 → Nat.gcd a b ≤ a.
Proof.
intros * Haz.
specialize (Nat.gcd_divide_l a b) as H1.
destruct H1 as (c, Hc); rewrite Hc at 2.
destruct c; [ easy | flia ].
Qed.

Theorem Nat_gcd_le_r : ∀ a b, b ≠ 0 → Nat.gcd a b ≤ b.
Proof.
intros * Hbz.
specialize (Nat.gcd_divide_r a b) as H1.
destruct H1 as (c, Hc); rewrite Hc at 2.
destruct c; [ easy | flia ].
Qed.

Definition Nat_le_neq_lt : ∀ x y : nat, x ≤ y → x ≠ y → (x < y)%nat :=
  λ x y Hxy Hnxy,
  match le_lt_eq_dec x y Hxy with
  | left Hle => Hle
  | right Heq => match Hnxy Heq with end
  end.

Theorem Nat_mod_less_small : ∀ n a b,
  n * b ≤ a < (n + 1) * b
  → a mod b = a - n * b.
Proof.
intros * Hab.
assert (Hb : b ≠ 0). {
  now intros Hb; rewrite Hb, (Nat.mul_comm (n + 1)) in Hab.
}
replace a with (a - n * b + n * b) at 1 by now apply Nat.sub_add.
rewrite Nat.Div0.mod_add.
apply Nat.mod_small.
apply Nat.add_lt_mono_r with (p := n * b).
rewrite Nat.add_comm in Hab; cbn in Hab.
now rewrite Nat.sub_add.
Qed.

Theorem Nat_mod_pow_mod : ∀ a b c, (a mod b) ^ c mod b = a ^ c mod b.
Proof.
intros.
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]; [ now subst b | ].
revert a b Hbz.
induction c; intros; [ easy | cbn ].
rewrite Nat.Div0.mul_mod_idemp_l.
rewrite <- Nat.Div0.mul_mod_idemp_r.
rewrite IHc; [ | easy ].
now rewrite Nat.Div0.mul_mod_idemp_r.
Qed.

Theorem Nat_mul_mod_cancel_r : ∀ a b c n,
  Nat.gcd c n = 1
  → a * c ≡ (b * c) mod n
  → a ≡ b mod n.
Proof.
intros * Hg Hab.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  cbn in Hab.
  rewrite Nat.gcd_0_r in Hg.
  subst c.
  do 2 rewrite Nat.mul_1_r in Hab.
  now subst a.
}
destruct (le_dec b a) as [Hba| Hba]. {
  apply Nat_eq_mod_sub_0 in Hab.
  rewrite <- Nat.mul_sub_distr_r in Hab.
  apply Nat.Lcm0.mod_divide in Hab.
  rewrite Nat.gcd_comm in Hg.
  rewrite Nat.mul_comm in Hab.
  specialize (Nat.gauss n c (a - b) Hab Hg) as H1.
  destruct H1 as (k, Hk).
  replace a with (b + k * n) by flia Hba Hk.
  now rewrite Nat.Div0.mod_add.
} {
  apply Nat.nle_gt in Hba.
  symmetry in Hab.
  apply Nat_eq_mod_sub_0 in Hab.
  rewrite <- Nat.mul_sub_distr_r in Hab.
  apply Nat.Lcm0.mod_divide in Hab.
  rewrite Nat.gcd_comm in Hg.
  rewrite Nat.mul_comm in Hab.
  specialize (Nat.gauss n c (b - a) Hab Hg) as H1.
  destruct H1 as (k, Hk).
  replace b with (a + k * n) by flia Hba Hk.
  now rewrite Nat.Div0.mod_add.
}
Qed.

Theorem Nat_mul_mod_cancel_l : ∀ a b c n,
  Nat.gcd c n = 1
  → c * a ≡ (c * b) mod n
  → a ≡ b mod n.
Proof.
intros * Hg Hab.
setoid_rewrite Nat.mul_comm in Hab.
now apply Nat_mul_mod_cancel_r in Hab.
Qed.

Theorem Nat_mul_sub_div_le : ∀ a b c,
  c ≤ a * b
  → (a * b - c) / b ≤ a.
Proof.
intros * Hc.
destruct (zerop b) as [Hb| Hb]; [ now subst b | ].
apply Nat.neq_0_lt_0 in Hb.
remember (a * b - c) as d eqn:Hd.
assert (H1 : a = (c + d) / b). {
  rewrite Hd.
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  now rewrite Nat.div_mul.
}
rewrite H1.
apply Nat.Div0.div_le_mono.
apply Nat.le_add_l.
Qed.

Theorem Nat_pow_mod_is_pow_mod : ∀ a b c,
  c ≠ 0 → Nat_pow_mod a b c = (a ^ b) mod c.
Proof.
intros * Hcz.
revert a.
induction b; intros; [ easy | ].
cbn; rewrite IHb.
now rewrite Nat.Div0.mul_mod_idemp_r.
Qed.

Theorem Nat_sub_sub_assoc : ∀ a b c,
  c ≤ b ≤ a + c
  → a - (b - c) = a + c - b.
Proof.
intros * (Hcb, Hba).
revert a c Hcb Hba.
induction b; intros.
-apply Nat.le_0_r in Hcb; subst c.
 now rewrite Nat.add_0_r.
-destruct c; [ now rewrite Nat.add_0_r | ].
 apply Nat.succ_le_mono in Hcb.
 rewrite Nat.add_succ_r in Hba.
 apply Nat.succ_le_mono in Hba.
 specialize (IHb a c Hcb Hba) as H1.
 rewrite Nat.sub_succ, H1.
 rewrite Nat.add_succ_r.
 now rewrite Nat.sub_succ.
Qed.

Theorem permutation_fold_mul : ∀ la lb d,
  permutation Nat.eqb la lb → fold_left Nat.mul la d = fold_left Nat.mul lb d.
Proof.
intros * Hpab.
revert d lb Hpab.
induction la as [| a]; intros; cbn. {
  now apply permutation_nil_l in Hpab; subst lb.
}
apply permutation_cons_l_iff in Hpab.
remember (List_extract (Nat.eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Nat.eqb_eq in H; subst x.
subst lb.
rewrite IHla with (lb := bef ++ aft); [ | easy ].
symmetry.
rewrite fold_left_app; cbn.
rewrite List_fold_left_mul_assoc.
now rewrite fold_left_app.
Qed.
