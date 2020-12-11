(* Fermat's little theorem *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith SetoidList Permutation.
Require Import Misc.
Import List ListNotations.

Fixpoint prime_test cnt n d :=
  match cnt with
  | 0 => true
  | S c =>
      match n mod d with
      | 0 => n <=? d
      | S _ => prime_test c n (d + 1)
      end
  end.

Definition is_prime n :=
  match n with
  | 0 | 1 => false
  | S (S c) => prime_test c n 2
  end.

Definition prime p := is_prime p = true.

Lemma prime_test_mod_ne_0 : ∀ n k,
  2 ≤ n
  → prime_test (n - k) n k = true
  → ∀ d, k ≤ d < n → n mod d ≠ 0.
Proof.
intros * Hn Hp d Hd.
remember (n - k) as cnt eqn:Hcnt; symmetry in Hcnt.
revert n k d Hn Hcnt Hp Hd.
induction cnt; intros; [ flia Hcnt Hd | ].
cbn in Hp.
remember (n mod k) as m eqn:Hm; symmetry in Hm.
destruct m; [ apply Nat.leb_le in Hp; flia Hp Hd | ].
destruct n; [ flia Hcnt | ].
destruct (Nat.eq_dec k d) as [Hkd| Hkd]. {
  now intros H; rewrite Hkd, H in Hm.
}
apply (IHcnt (S n) (k + 1)); [ easy | flia Hcnt | easy | flia Hd Hkd ].
Qed.

Theorem prime_only_divisors : ∀ p,
  prime p → ∀ a, Nat.divide a p → a = 1 ∨ a = p.
Proof.
intros * Hp a * Hap.
destruct (lt_dec p 2) as [Hp2| Hp2]. {
  destruct p; [ easy | ].
  destruct p; [ easy | flia Hp2 ].
}
apply Nat.nlt_ge in Hp2.
destruct (zerop a) as [Ha| Ha]. {
  subst a.
  apply Nat.divide_0_l in Hap; flia Hap Hp2.
}
apply Nat.neq_0_lt_0 in Ha.
apply Nat.mod_divide in Hap; [ | easy ].
apply Nat.mod_divides in Hap; [ | easy ].
destruct Hap as (k, Hk).
symmetry in Hk.
destruct p; [ easy | ].
destruct p; [ easy | ].
specialize (prime_test_mod_ne_0 (S (S p)) 2 Hp2) as H1.
replace (S (S p) - 2) with p in H1 by flia.
specialize (H1 Hp).
destruct k; [ now rewrite Nat.mul_0_r in Hk | ].
destruct k; [ now rewrite Nat.mul_1_r in Hk; right | left ].
destruct a; [ easy | ].
destruct a; [ easy | exfalso ].
specialize (H1 (S (S k))) as H2.
assert (H : 2 ≤ S (S k) < S (S p)). {
  split; [ flia Hp2 | flia Hk ].
}
specialize (H2 H); clear H.
apply H2; rewrite <- Hk.
now rewrite Nat.mod_mul.
Qed.

Theorem eq_gcd_prime_small_1 : ∀ p n,
  prime p
  → 0 < n < p
  → Nat.gcd p n = 1.
Proof.
intros * Hp Hnp.
remember (Nat.gcd p n) as g eqn:Hg; symmetry in Hg.
destruct g; [ now apply Nat.gcd_eq_0 in Hg; rewrite (proj1 Hg) in Hp | ].
destruct g; [ easy | exfalso ].
specialize (Nat.gcd_divide_l p n) as H1.
rewrite Hg in H1.
destruct H1 as (d, Hd).
specialize (prime_only_divisors p Hp (S (S g))) as H1.
assert (H : Nat.divide (S (S g)) p). {
  rewrite Hd; apply Nat.divide_factor_r.
}
specialize (H1 H); clear H.
destruct H1 as [H1| H1]; [ easy | ].
destruct d; [ now rewrite Hd in Hp | ].
rewrite Hd in H1.
destruct d. {
  rewrite Nat.mul_1_l in Hd.
  rewrite <- Hd in Hg.
  specialize (Nat.gcd_divide_r p n) as H2.
  rewrite Hg in H2.
  destruct H2 as (d2, Hd2).
  destruct d2; [ rewrite Hd2 in Hnp; flia Hnp | ].
  rewrite Hd2 in Hnp; flia Hnp.
}
replace (S (S d)) with (1 + S d) in H1 by flia.
rewrite Nat.mul_add_distr_r, Nat.mul_1_l in H1.
rewrite <- (Nat.add_0_r (S (S g))) in H1 at 1.
now apply Nat.add_cancel_l in H1.
Qed.

Theorem Nat_gcd_prime_fact_lt : ∀ p,
  prime p → ∀ k, k < p → Nat.gcd p (fact k) = 1.
Proof.
intros * Hp * Hkp.
induction k; [ apply Nat.gcd_1_r | ].
rewrite Nat_fact_succ.
apply Nat_gcd_1_mul_r; [ | apply IHk; flia Hkp ].
apply eq_gcd_prime_small_1; [ easy | flia Hkp ].
Qed.

Notation "a ^ b" := (Nat.pow a b) : nat_scope.

Theorem smaller_than_prime_all_different_multiples : ∀ p,
  prime p
  → ∀ a, 1 ≤ a < p
  → ∀ i j, i < j < p → (i * a) mod p ≠ (j * a) mod p.
Proof.
intros * Hp * Hap * Hijp.
intros Haa; symmetry in Haa.
apply Nat_mul_mod_cancel_r in Haa. 2: {
  rewrite Nat.gcd_comm.
  now apply eq_gcd_prime_small_1.
}
rewrite Nat.mod_small in Haa; [ | easy ].
rewrite Nat.mod_small in Haa; [ | flia Hijp ].
flia Hijp Haa.
Qed.

Theorem fold_left_mul_map_mod : ∀ a b l,
  fold_left Nat.mul (map (λ i, i mod a) l) b mod a =
  fold_left Nat.mul l b mod a.
Proof.
intros.
destruct (Nat.eq_dec a 0) as [Haz| Haz]; [ now subst a | ].
induction l as [| c l]; [ easy | cbn ].
rewrite <- List_fold_left_mul_assoc.
rewrite Nat.mul_mod_idemp_r; [ | easy ].
rewrite <- Nat.mul_mod_idemp_l; [ | easy ].
rewrite IHl.
rewrite Nat.mul_mod_idemp_l; [ | easy ].
now rewrite List_fold_left_mul_assoc.
Qed.

Theorem fold_left_mul_map_mul : ∀ b c l,
  fold_left Nat.mul (map (λ a, a * b) l) c =
  fold_left Nat.mul l c * b ^ length l.
Proof.
intros.
induction l as [| a l]; [ now cbn; rewrite Nat.mul_1_r | cbn ].
do 2 rewrite <- List_fold_left_mul_assoc.
rewrite IHl; flia.
Qed.

Theorem fact_eq_fold_left : ∀ n,
  fact n = fold_left Nat.mul (seq 1 n) 1.
Proof.
induction n; intros; [ easy | ].
rewrite <- (Nat.add_1_r n) at 2.
rewrite seq_app.
rewrite fold_left_app.
now rewrite <- IHn, Nat_fact_succ, Nat.mul_comm.
Qed.

Theorem fermat_little : ∀ p,
  prime p → ∀ a, 1 ≤ a < p → a ^ (p - 1) mod p = 1.
Proof.
intros * Hp * Hap.
specialize (smaller_than_prime_all_different_multiples p Hp a Hap) as H1.
assert (Hpz : p ≠ 0) by now intros H; rewrite H in Hp.
assert
  (Hperm :
     Permutation (map (λ i, (i * a) mod p) (seq 1 (p - 1)))
       (seq 1 (p - 1))). {
  apply NoDup_Permutation_bis; cycle 1. {
    now rewrite map_length, seq_length.
  } {
    intros i Hi.
    apply in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj).
    apply in_seq in Hj.
    rewrite <- Hji.
    apply in_seq.
    replace (1 + (p - 1)) with p in Hj |-* by flia Hpz.
    split; [ | now apply Nat.mod_upper_bound ].
    apply Nat.neq_0_lt_0.
    intros Hi.
    apply Nat.mod_divide in Hi; [ | easy ].
    specialize (Nat.gauss _ _ _ Hi) as H2.
    assert (H : Nat.gcd p j = 1) by now apply eq_gcd_prime_small_1.
    specialize (H2 H); clear H.
    destruct H2 as (c, Hc).
    rewrite Hc in Hap.
    destruct c; [ easy | ].
    cbn in Hap; flia Hap.
  } {
    remember (λ i, (i * a) mod p) as f eqn:Hf.
    assert (H2 : ∀ i j, i < j < p → f i ≠ f j) by now rewrite Hf.
    assert
      (H : ∀ {A} start len (f : nat → A),
         (∀ i j, i < j < start + len → f i ≠ f j)
         → NoDup (map f (seq start len))). {
      clear; intros * Hij.
      remember (seq start len) as l eqn:Hl; symmetry in Hl.
      revert start len Hij Hl; induction l as [| i l]; intros; [ constructor | ].
      rewrite map_cons; constructor. {
        intros H1.
        apply in_map_iff in H1.
        destruct H1 as (j & Hji & Hj).
        destruct len; [ easy | cbn in Hl ].
        injection Hl; clear Hl; intros Hl Hb; subst i.
        specialize (Hij start j) as H1.
        assert (H : start < j < start + S len). {
          rewrite <- Hl in Hj.
          apply in_seq in Hj; flia Hj.
        }
        specialize (H1 H); clear H.
        now symmetry in Hji.
      }
      destruct len; [ easy | ].
      injection Hl; clear Hl; intros Hl Hi.
      apply (IHl (S start) len); [ | easy ].
      intros j k Hjk.
      apply Hij; flia Hjk.
    }
    apply H.
    now replace (1 + (p - 1)) with p by flia Hpz.
  }
}
remember (λ i : nat, (i * a) mod p) as f eqn:Hf.
remember (fold_left Nat.mul (map f (seq 1 (p - 1))) 1) as x eqn:Hx.
assert (Hx1 : x mod p = fact (p - 1) mod p). {
  subst x.
  erewrite Permutation_fold_mul; [ | apply Hperm ].
  f_equal.
  clear.
  (* lemma perhaps? *)
  remember (p - 1) as n; clear p Heqn.
  symmetry.
  apply fact_eq_fold_left.
}
assert (Hx2 : x mod p = (fact (p - 1) * a ^ (p - 1)) mod p). {
  subst x; rewrite Hf.
  rewrite <- (map_map (λ i, i * a) (λ j, j mod p)).
  rewrite fold_left_mul_map_mod.
  rewrite fold_left_mul_map_mul.
  rewrite seq_length.
  f_equal; f_equal.
  symmetry.
  apply fact_eq_fold_left.
}
rewrite Hx2 in Hx1.
rewrite <- (Nat.mul_1_r (fact _)) in Hx1 at 2.
apply Nat_mul_mod_cancel_l in Hx1. 2: {
  rewrite Nat.gcd_comm.
  apply Nat_gcd_prime_fact_lt; [ easy | flia Hpz ].
}
rewrite (Nat.mod_small 1) in Hx1; [ easy | flia Hap ].
Qed.
