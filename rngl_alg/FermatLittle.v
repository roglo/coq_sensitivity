(* Fermat's little theorem *)

Set Nested Proofs Allowed.
Require Import Stdlib.Arith.Arith Stdlib.Sorting.SetoidList.
Require Import RingLike.Utf8.
Require Import RingLike.PermutationFun.
Require Import RingLike.Misc.
Import ListNotations.

Require Import Misc.

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
apply Nat.Lcm0.mod_divide in Hap.
apply Nat.Div0.mod_divides in Hap.
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
now rewrite Nat.Div0.mod_mul.
Qed.

Theorem eq_gcd_prime_small_1 : ∀ p n,
  prime p
  → 0 < n < p
  → Nat.gcd p n = 1.
Proof.
intros * Hp Hnp.
destruct Hnp as (Hzn, Hnp).
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
  subst n.
  destruct d2; [ now apply Nat.lt_irrefl in Hzn | flia Hnp ].
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
induction k; [ now rewrite Nat.gcd_comm | ].
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
destruct Hap as (H1a, Hap).
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
induction l as [| c l]; [ easy | cbn ].
rewrite <- List_fold_left_mul_assoc.
rewrite Nat.Div0.mul_mod_idemp_r.
rewrite <- Nat.Div0.mul_mod_idemp_l.
rewrite IHl.
rewrite Nat.Div0.mul_mod_idemp_l.
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
     permutation Nat.eqb (map (λ i, (i * a) mod p) (seq 1 (p - 1)))
       (seq 1 (p - 1))). {
  apply (NoDup_permutation_bis Nat.eqb_eq); cycle 1. {
    now rewrite length_map, length_seq.
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
    apply Nat.Lcm0.mod_divide in Hi.
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
      revert start len Hij Hl.
      induction l as [| i l]; intros; [ constructor | ].
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
  erewrite permutation_fold_mul; [ | apply Hperm ].
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
  rewrite length_seq.
  f_equal; f_equal.
  symmetry.
  now apply fact_eq_fold_left.
}
rewrite Hx2 in Hx1.
rewrite <- (Nat.mul_1_r (fact _)) in Hx1 at 2.
apply Nat_mul_mod_cancel_l in Hx1. 2: {
  rewrite Nat.gcd_comm.
  apply Nat_gcd_prime_fact_lt; [ easy | flia Hpz ].
}
rewrite (Nat.mod_small 1) in Hx1; [ easy | flia Hap ].
Qed.

Theorem Nat_neg_neg_mod :
  ∀ a b n, a ≤ n → b ≤ n → (n - a) * (n - b) ≡ (a * b) mod n.
Proof.
intros * Han Hbn.
rewrite Nat.mul_sub_distr_l.
do 2 rewrite Nat.mul_sub_distr_r.
rewrite Nat_sub_sub_swap.
rewrite <- (Nat.Div0.mod_add _ a).
rewrite Nat.sub_add; cycle 1. {
  rewrite Nat.sub_sub_distr; cycle 1. {
    now apply Nat.mul_le_mono_nonneg_r.
  } {
    now apply Nat.mul_le_mono_nonneg_l.
  }
  rewrite <- Nat.mul_sub_distr_l.
  apply Nat.le_sub_le_add_r.
  rewrite <- Nat.mul_sub_distr_l.
  apply Nat.mul_le_mono_nonneg_r; [ | easy ].
  apply Nat.le_add_le_sub_l.
  now rewrite Nat.add_0_r.
}
rewrite Nat.sub_sub_distr; cycle 1. {
  now apply Nat.mul_le_mono_nonneg_r.
} {
  now apply Nat.mul_le_mono_nonneg_l.
}
rewrite <- Nat.mul_sub_distr_l.
rewrite Nat.mul_comm.
rewrite Nat.add_comm.
now rewrite Nat.Div0.mod_add.
Qed.

Fixpoint sqrt_mod_loop a p i :=
  match i with
  | 0 => None
  | S i' =>
      if i * i mod p =? a mod p then Some (p - i)
      else sqrt_mod_loop a p i'
  end.

Definition sqrt_mod a p := sqrt_mod_loop a p (p - 1).

Definition legendre_symbol a p :=
  if a =? 0 then 0
  else
    match sqrt_mod a p with
    | Some _ => 1
    | None => p - 1
    end.

(*
Definition is_quadratic_residue a p := legendre_symbol a p =? 1.

Compute (let p := 17 in List.map (λ a, (sqrt_mod a p, a)) (List.seq 0 p)).
Compute (let p := 17 in List.filter (λ a, is_quadratic_residue a p) (List.seq 0 p)).
*)

Theorem eq_sqrt_mod_loop_Some :
  ∀ a b p i,
  i < p
  → sqrt_mod_loop a p i = Some b
  → 1 ≤ b < p ∧ b * b ≡ a mod p.
Proof.
intros * Hip Hsm.
induction i; [ easy | ].
cbn - [ "*" ] in Hsm.
remember ((S i * S i) mod p =? a mod p) as e eqn:He.
symmetry in He.
destruct e; cycle 1. {
  apply IHi; [ flia Hip | easy ].
}
injection Hsm; clear Hsm; intros; subst b.
apply Nat.eqb_eq in He.
split; [ | now apply Nat.lt_le_incl in Hip; rewrite Nat_neg_neg_mod ].
split; [ | now apply Nat.lt_le_incl in Hip; apply Nat.sub_lt ].
flia Hip.
Qed.

Theorem eq_sqrt_mod_Some :
  ∀ a b p,
  p ≠ 0
  → sqrt_mod a p = Some b
  → 1 ≤ b < p ∧ b * b ≡ a mod p.
Proof.
intros * Hp Hsm.
apply eq_sqrt_mod_loop_Some in Hsm; [ easy | ].
apply Nat.sub_lt; [ | easy ].
now apply Nat.neq_0_lt_0.
Qed.

(* to be completed
Theorem euler_criterion : ∀ p,
  prime p
  → ∀ a, 1 ≤ a < p
  → a ^ ((p - 1) / 2) ≡ legendre_symbol a p mod p.
Proof.
intros * Hp * Hap.
progress unfold legendre_symbol.
remember (a =? 0) as az eqn:Haz.
symmetry in Haz.
destruct az. {
  now apply Nat.eqb_eq in Haz; subst a.
}
apply Nat.eqb_neq in Haz.
remember (sqrt_mod a p) as sm eqn:Hsm.
symmetry in Hsm.
destruct sm as [b| ]. {
  apply eq_sqrt_mod_Some in Hsm; [ | flia Hap ].
  destruct Hsm as (Hbp, Hsm).
  rewrite <- Nat_mod_pow_mod.
  rewrite <- Hsm.
  rewrite Nat_mod_pow_mod.
  rewrite <- Nat.pow_2_r.
  rewrite <- Nat.pow_mul_r.
  rewrite <- (proj2 (Nat.Div0.div_exact _ _)). {
    rewrite fermat_little; [ | easy | easy ].
    symmetry.
    apply Nat.mod_1_l.
    now apply (Nat.le_lt_trans _ a).
  }
....
rewrite Nat.mul_sub_distr_l.
do 2 rewrite Nat.mul_sub_distr_r.
rewrite Nat_sub_sub_swap.
Theorem glop : ∀ a b c, b * c ≤  a → a - b * c ≡ a mod c.
Proof.
intros * Hbca.
rewrite <- (Nat.Div0.mod_add _ b).
now rewrite Nat.sub_add.
Qed.
rewrite glop.
...
rewrite Nat.mul_sub_distr_r.
do 2 rewrite Nat.mul_sub_distr_l.
....
rewrite Nat.sub_sub_distr; cycle 1. {
  apply Nat.mul_le_mono_r.
  now apply Nat.lt_le_incl.
} {
  apply Nat.mul_le_mono_l.
  now apply Nat.lt_le_incl.
}
rewrite Nat.add_sub_swap.
...
rewrite <- Nat.add_sub_swap; cycle 1. {
  apply Nat.mul_le_mono_l.
  now apply Nat.lt_le_incl.
}
rewrite (Nat.mul_comm p (S i)).
rewrite <- Nat.sub_add_distr.
rewrite <- Nat.mul_add_distr_l.
Search ((_ - _) mod _).

do 2 rewrite <- (Nat.Div0.mod_add _ (S i)).
rewrite <- Nat.add_assoc.
rewrite <- Nat.mul_add_distr_l.
rewrite Nat.sub_add.
...
now apply eq_sqrt_mod_loop_Some in Hsm.
...
*)
