(* ℕ is a ring-like without opposite, i.e. a semiring *)
(* ℤ/nℤ is a ring-like,
     if n is prime, has inverse, i.e. it is a field
     if n is not prime, it has neither inverse nor division, it is a ring *)

Set Nested Proofs Allowed.
Require Import Stdlib.Arith.Arith.
Require Import RingLike.Utf8.
Require Import RingLike.Misc.

Require Import Misc FermatLittle.

(*
have been moved to NatRingLike.v in directory ../sensitivity
*)

(* primes, for ℤn, following *)

(* (a ^ b) mod c defined like that so that we can use "Compute"
   for testing; proved equal to (a ^ b) mod c just below... *)

Fixpoint Nat_pow_mod_loop a b c :=
  match b with
  | 0 => 1 mod c
  | S b' => (a * Nat_pow_mod_loop a b' c) mod c
  end.

Definition Nat_pow_mod a b c := Nat_pow_mod_loop a b c.

(* ... and, in fact, it is a ^ b *)

Theorem Nat_pow_mod_is_pow_mod : ∀ a b c,
  Nat_pow_mod a b c = (a ^ b) mod c.
Proof.
intros.
revert a.
induction b; intros; [ easy | ].
cbn; rewrite IHb.
now rewrite Nat.Div0.mul_mod_idemp_r.
Qed.

Definition inv_mod i n := Nat_pow_mod i (n - 2) n.

Theorem prime_mul_inv_l_mod : ∀ p a,
  is_prime p = true
  → a mod p ≠ 0
  → (inv_mod a p * a) mod p = 1.
Proof.
intros * Hp Haz.
progress unfold inv_mod.
rewrite Nat_pow_mod_is_pow_mod.
rewrite Nat.Div0.mul_mod_idemp_l.
replace a with (a ^ 1); [ | apply Nat.pow_1_r ].
rewrite Nat.pow_1_r at 1.
rewrite <- Nat.pow_add_r.
replace (p - 2 + 1) with (p - 1). 2: {
  destruct p; [ easy | ].
  destruct p; [ easy | ].
  cbn; rewrite Nat.sub_0_r.
  symmetry.
  apply Nat.add_1_r.
}
(* Fermat's little theorem *)
rewrite <- Nat_mod_pow_mod.
apply fermat_little; [ easy | ].
split; [ flia Haz | ].
apply Nat.mod_upper_bound.
now destruct p.
Qed.

(* ℤn = ℤ/nℤ *)

Definition at_least_1 n := S(n - 1).

Definition Zn n := {a : nat | a <? at_least_1 n = true}.

Theorem Zn_op_prop n r : r mod at_least_1 n <? at_least_1 n = true.
Proof.
intros.
apply Nat.ltb_lt.
now apply Nat.mod_upper_bound.
Qed.

Definition Zn_of_nat n v : Zn n :=
  exist _ (v mod at_least_1 n) (Zn_op_prop n v).

Definition Zn_add n (a b : Zn n) : Zn n :=
  let r := proj1_sig a + proj1_sig b in
  exist _ (r mod at_least_1 n) (Zn_op_prop n r).
Definition Zn_mul n (a b : Zn n) : Zn n :=
  let r := proj1_sig a * proj1_sig b in
  exist _ (r mod at_least_1 n) (Zn_op_prop n r).
Definition Zn_opp n (a : Zn n) : Zn n :=
  let r := at_least_1 n - proj1_sig a in
  exist _ (r mod at_least_1 n) (Zn_op_prop n r).
Definition Zn_inv n (a : Zn n) : Zn n :=
  let r := inv_mod (proj1_sig a) n in
  exist _ (r mod at_least_1 n) (Zn_op_prop n r).

Theorem Zn_eq : ∀ n (a b : Zn n), proj1_sig a = proj1_sig b → a = b.
Proof.
intros * Hab.
destruct a as (a, Ha).
destruct b as (b, Hb).
cbn in Hab.
apply eq_exist_uncurried.
exists Hab.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Theorem Zn_neq : ∀ n (a b : Zn n), proj1_sig a ≠ proj1_sig b → a ≠ b.
Proof.
intros * Hab.
intros H; apply Hab.
now destruct H.
Qed.

Theorem Zn_add_comm : ∀ n (a b : Zn n), Zn_add n a b = Zn_add n b a.
Proof.
intros n (a, Ha) (b, Hb).
apply Zn_eq; cbn - [ "mod" ].
now rewrite Nat.add_comm.
Qed.

Theorem Zn_add_assoc :
  ∀ n a b c, Zn_add n a (Zn_add n b c) = Zn_add n (Zn_add n a b) c.
Proof.
intros.
apply Zn_eq; cbn - [ "mod" ].
rewrite Nat.Div0.add_mod_idemp_l.
rewrite Nat.Div0.add_mod_idemp_r.
now rewrite Nat.add_assoc.
Qed.

Theorem Zn_add_0_l :
  ∀ n (a : Zn n), Zn_add n (Zn_of_nat n 0) a = a.
Proof.
intros.
apply Zn_eq; cbn - [ "mod" ].
rewrite (Nat.mod_small 0); [ | apply Nat.lt_0_succ ].
rewrite Nat.add_0_l.
apply Nat.mod_small.
destruct a as (a, Ha); cbn.
now apply Nat.ltb_lt in Ha.
Qed.

Theorem Zn_mul_assoc :
  ∀ n (a b c : Zn n),
  Zn_mul n a (Zn_mul n b c) = Zn_mul n (Zn_mul n a b) c.
Proof.
intros.
apply Zn_eq; cbn - [ "mod" ].
rewrite Nat.Div0.mul_mod_idemp_l.
rewrite Nat.Div0.mul_mod_idemp_r.
now rewrite Nat.mul_assoc.
Qed.

Theorem Zn_mul_1_l :
  ∀ n (a : Zn n), Zn_mul n (Zn_of_nat n 1) a = a.
Proof.
intros.
apply Zn_eq; cbn - [ "mod" ].
rewrite Nat.Div0.mul_mod_idemp_l.
rewrite Nat.mul_1_l.
destruct a as (a, Ha); cbn - [ "mod" ].
apply Nat.ltb_lt in Ha.
now apply Nat.mod_small.
Qed.

Theorem Zn_mul_add_distr_l :
  ∀ n (a b c : Zn n),
  Zn_mul n a (Zn_add n b c) = Zn_add n (Zn_mul n a b) (Zn_mul n a c).
Proof.
intros.
apply Zn_eq; cbn - [ "mod" ].
rewrite Nat.Div0.add_mod_idemp_l.
rewrite Nat.Div0.add_mod_idemp_r.
rewrite Nat.Div0.mul_mod_idemp_r.
now rewrite Nat.mul_add_distr_l.
Qed.

Theorem Zn_mul_comm :
  ∀ n (a b : Zn n), Zn_mul n a b = Zn_mul n b a.
Proof.
intros n (a, Ha) (b, Hb).
apply Zn_eq; cbn - [ "mod" ].
now rewrite Nat.mul_comm.
Qed.

Theorem Zn_add_opp_diag_l :
  ∀ n (a : Zn n), Zn_add n (Zn_opp n a) a = Zn_of_nat n 0.
Proof.
intros n (a, Ha).
apply Zn_eq; cbn - [ "mod" "-" ].
apply Nat.ltb_lt in Ha.
rewrite Nat.Div0.add_mod_idemp_l.
rewrite (Nat.mod_small 0); [ | apply Nat.lt_0_succ ].
rewrite Nat.sub_add. 2: {
  now apply Nat.lt_le_incl.
}
apply Nat.Div0.mod_same.
Qed.

Theorem Zn_eq_dec : ∀ n (a b : Zn n), {a = b} + {a ≠ b}.
Proof.
intros n (a, Ha) (b, Hb).
destruct (Nat.eq_dec a b) as [Hab| Hab]; [ left | right ]. {
  now apply Zn_eq.
} {
  now apply Zn_neq.
}
Qed.

Definition Zn_opt_inv_or_pdiv n :=
  if is_prime n then Some (inl (Zn_inv n) : _ + (Zn n → Zn n → Zn n))
  else None.

Definition Zn_has_inv n :=
  match Zn_opt_inv_or_pdiv n with
  | Some (inl _) => true
  | _ => false
  end.

Definition Zn_has_pdiv n :=
  match Zn_opt_inv_or_pdiv n with
  | Some (inr _) => true
  | _ => false
  end.

Definition Zn_inv' n a :=
  match Zn_opt_inv_or_pdiv n with
  | Some (inl rngl_inv) => rngl_inv a
  | _ => Zn_of_nat n 0
  end.

Theorem Zn_opt_mul_inv_diag_l :
  ∀ {not_applicable : Prop} (NA : not_applicable) n,
  if Zn_has_inv n then
    ∀ a : Zn n,
    a ≠ Zn_of_nat n 0
    → Zn_mul n (Zn_inv' n a) a = Zn_of_nat n 1
  else not_applicable.
Proof.
intros.
progress unfold Zn_has_inv.
progress unfold Zn_inv'.
progress unfold Zn_opt_inv_or_pdiv.
remember (is_prime n) as p eqn:Hp.
symmetry in Hp.
destruct p; [ cbn | easy ].
intros * Haz.
destruct (lt_dec n 2) as [Hn2| Hn2]. {
  destruct n; [ easy | ].
  destruct n; [ easy | ].
  do 2 apply Nat.succ_lt_mono in Hn2.
  easy.
}
apply Nat.nlt_ge in Hn2; cbn.
apply Zn_eq; cbn - [ "mod" ].
rewrite (Nat.mod_small 1). 2: {
  apply -> Nat.succ_lt_mono.
  flia Hn2.
}
rewrite Nat.Div0.mul_mod_idemp_l.
replace (at_least_1 n) with n. 2: {
  destruct n as [| n']; [ easy | ].
  destruct n'; [ easy | ].
  progress unfold at_least_1.
  rewrite Nat.sub_succ.
  now rewrite Nat.sub_0_r.
}
unfold at_least_1.
destruct a as (a, Ha); cbn - [ "mod" ].
apply prime_mul_inv_l_mod; [ easy | ].
intros H; apply Haz; clear Haz.
apply Zn_eq; cbn; symmetry.
rewrite Nat.sub_diag; symmetry.
destruct a; [ easy | exfalso ].
apply Nat.ltb_lt in Ha.
progress unfold at_least_1 in Ha.
apply Nat.Div0.mod_divides in H.
destruct H as (c, Hc).
replace (S (S (n - 2))) with n in Ha by flia Hn2.
rewrite Hc in Ha.
apply Nat.nle_gt in Ha; apply Ha.
destruct c; [ now rewrite Nat.mul_comm in Hc | flia Hn2 ].
Qed.

Theorem Zn_opt_mul_inv_diag_r :
  ∀ {not_applicable : Prop} (NA : not_applicable) n {P},
  if (Zn_has_inv n && false)%bool then P
  else not_applicable.
Proof.
now intros; rewrite Bool.andb_false_r.
Qed.

Theorem Zn_opt_mul_div :
  ∀ {not_applicable : Prop} (NA : not_applicable) n {P},
  if Zn_has_pdiv n then P else not_applicable.
Proof.
intros.
progress unfold Zn_has_pdiv; cbn.
progress unfold Zn_opt_inv_or_pdiv.
now destruct (is_prime n).
Qed.

(* *)

Require Import RingLike.Core.

Instance Zn_ring_like_op n : ring_like_op (Zn n) :=
  {| rngl_zero := Zn_of_nat n 0;
     rngl_one := Zn_of_nat n 1;
     rngl_add := Zn_add n;
     rngl_mul := Zn_mul n;
     rngl_opt_opp_or_psub := Some (inl (Zn_opp n));
     rngl_opt_inv_or_pdiv := Zn_opt_inv_or_pdiv n;
     rngl_opt_is_zero_divisor := Some (λ _, True);
     rngl_opt_eq_dec := Some (Zn_eq_dec n);
     rngl_opt_leb := None |}.

Section a.

Context {n : nat}.

Theorem proj1_sig_Zn_of_nat :
  let roz := Zn_ring_like_op n in
  ∀ i, proj1_sig (rngl_mul_nat 1 i) = i mod at_least_1 n.
Proof.
intros.
progress unfold rngl_mul_nat.
progress unfold mul_nat; cbn - [ "mod" ].
induction i. {
  cbn - [ "mod" ].
  now rewrite Nat.Div0.mod_0_l.
}
cbn - [ "mod" ].
cbn - [ "mod" ] in IHi.
rewrite IHi.
rewrite Nat.Div0.add_mod_idemp_l.
rewrite Nat.Div0.add_mod_idemp_r.
easy.
Qed.

Theorem Zn_integral :
  ∀ a b : Zn n,
  (a * b)%L = 0%L
  → a = 0%L ∨ b = 0%L ∨ rngl_is_zero_divisor a ∨ rngl_is_zero_divisor b.
Proof.
intros * Hab.
now right; right; left.
Qed.

Theorem Zn_characteristic_prop :
  let roz := Zn_ring_like_op n in
  if at_least_1 n =? 0 then ∀ i : nat, rngl_mul_nat 1 (S i) ≠ 0%L
  else
    (∀ i : nat, 0 < i < at_least_1 n → rngl_mul_nat 1 i ≠ 0%L) ∧
    rngl_mul_nat 1 (at_least_1 n) = 0%L.
Proof.
intros.
split. {
  intros i Hi.
  cbn; intros H.
  specialize (@proj1_sig_Zn_of_nat i) as H1.
  subst roz.
  progress unfold Zn in H.
  cbn - [ "mod" ] in H1.
  cbn in H.
  rewrite H in H1.
  cbn - [ "mod" ] in H1.
  symmetry in H1.
  rewrite Nat.mod_small in H1; [ | easy ].
  cbn in H1.
  now rewrite Nat.sub_diag in H1; subst i.
}
intros.
apply Zn_eq.
rewrite proj1_sig_Zn_of_nat.
rewrite Nat.Div0.mod_same.
cbn; symmetry.
apply Nat.sub_diag.
Qed.

Definition Zn_ring_like_prop (ro := Zn_ring_like_op n) :
    ring_like_prop (Zn n) :=
  {| rngl_mul_is_comm := true;
     rngl_is_archimedean := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := at_least_1 n;
     rngl_add_comm := Zn_add_comm n;
     rngl_add_assoc := Zn_add_assoc n;
     rngl_add_0_l := Zn_add_0_l n;
     rngl_mul_assoc := Zn_mul_assoc n;
     rngl_mul_1_l := Zn_mul_1_l n;
     rngl_mul_add_distr_l := Zn_mul_add_distr_l n;
     rngl_opt_mul_comm := Zn_mul_comm n;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_diag_l := Zn_add_opp_diag_l n;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_sub_0_l := NA;
     rngl_opt_mul_inv_diag_l := Zn_opt_mul_inv_diag_l NA n;
     rngl_opt_mul_inv_diag_r := Zn_opt_mul_inv_diag_r NA n;
     rngl_opt_mul_div := Zn_opt_mul_div NA n;
     rngl_opt_integral := Zn_integral;
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := Zn_characteristic_prop;
     rngl_opt_ord := NA;
     rngl_opt_archimedean := NA |}.

End a.
