(* Theorems of general usage, which could be (or not) in Coq library *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith (*Psatz Sorted Permutation Decidable*).
Require Import Main.Misc.
(*
Import List List.ListNotations.
Arguments length {A}.

Global Hint Resolve Nat.le_0_l : core.
Global Hint Resolve Nat.lt_0_succ : core.
Global Hint Resolve Nat.lt_succ_diag_r : core.

(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Notation "n !" := (fact n) (at level 1, format "n !").
Notation "x '∈' l" := (List.In x l) (at level 70).
Notation "x '∉' l" := (¬ List.In x l) (at level 70).

Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level) :
                          nat_scope.
Notation "x < y ≤ z" := (x < y ∧ y <= z)%nat (at level 70, y at next level) :
                          nat_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%nat (at level 70, y at next level) :
                          nat_scope.
Notation "x < y < z" := (x < y ∧ y < z)%nat (at level 70, y at next level).

Notation "∃! x .. y , p" :=
  (ex (unique (λ x, .. (ex (unique (λ y, p))) ..)))
    (at level 200, x binder, right associativity)
  : type_scope.

Notation "x ≠? y" := (negb (Nat.eqb x y)) (at level 70) : nat_scope.
*)

Theorem Nat_div_less_small : ∀ n a b,
  n * b ≤ a < (n + 1) * b
  → a / b = n.
Proof.
intros * Hab.
assert (Hb : b ≠ 0). {
  now intros Hb; rewrite Hb, (Nat.mul_comm (n + 1)) in Hab.
}
replace a with (a - n * b + n * b) at 1 by now apply Nat.sub_add.
rewrite Nat.div_add; [ | easy ].
replace n with (0 + n) at 3 by easy; f_equal.
apply Nat.div_small.
apply Nat.add_lt_mono_r with (p := n * b).
rewrite Nat.add_comm in Hab; cbn in Hab.
now rewrite Nat.sub_add.
Qed.

Theorem Nat_div_add_same_l : ∀ a b, a ≠ 0 → (a + b) / a = 1 + b / a.
Proof.
intros * Ha.
replace a with (1 * a) at 1 by apply Nat.mul_1_l.
rewrite Nat.add_comm.
rewrite Nat.div_add; [ apply Nat.add_comm | easy ].
Qed.

Theorem Nat_div_interv : ∀ n a b,
  n * b ≤ a < (n + 1) * b
  → a / b = n.
Proof.
intros * Hn.
revert a b Hn.
induction n; intros.
-rewrite Nat.mul_0_l, Nat.mul_1_l in Hn.
 now apply Nat.div_small.
-specialize (IHn (a - b) b) as H1.
 assert (H : n * b ≤ a - b < (n + 1) * b). {
   destruct Hn as (H2, H3).
   assert (Hba : b ≤ a). {
     eapply Nat.le_trans; [ | apply H2 ].
     apply Nat.le_add_r.
   }
   split.
   -apply (Nat.add_le_mono_r _ _ b).
    replace (n * b + b) with (S n * b) by apply Nat.add_comm.
    rewrite Nat.sub_add; [ apply H2 | easy ].
   -apply (Nat.add_lt_mono_r _ _ b).
    rewrite Nat.sub_add; [ | easy ].
    rewrite Nat.add_1_r in H3; cbn in H3.
    rewrite Nat.add_1_r; cbn.
    now rewrite Nat.add_assoc, Nat.add_shuffle0 in H3.
 }
 specialize (H1 H); clear H.
 assert (H : b ≤ a). {
   apply (Nat.mul_le_mono_pos_l _ _ (S n)); [ easy | ].
   eapply le_trans; [ apply Hn | apply Nat.le_add_r ].
 }
 destruct b.
 +now do 2 rewrite Nat.mul_0_r in Hn.
 +replace a with (S b + (a - S b)); cycle 1. {
    rewrite Nat.add_sub_assoc; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  rewrite Nat_div_add_same_l; [ | easy ].
  rewrite Nat.add_1_l.
  now f_equal.
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
rewrite Nat.mod_add; [ | easy ].
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
rewrite Nat.mul_mod_idemp_l; [ | easy ].
rewrite <- Nat.mul_mod_idemp_r; [ | easy ].
rewrite IHc; [ | easy ].
now rewrite Nat.mul_mod_idemp_r.
Qed.

Theorem Nat_mul_le_pos_r : ∀ a b, 1 ≤ b → a ≤ a * b.
Proof.
intros * Ha.
replace a with (a * 1) at 1 by apply Nat.mul_1_r.
now apply Nat.mul_le_mono_nonneg_l.
Qed.
