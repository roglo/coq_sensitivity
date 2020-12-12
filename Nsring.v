(* Semiring of natural *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Misc RingLike FermatLittle.

Definition phony_Nat_opp (x : nat) := 0.
Definition phony_Nat_inv (x : nat) := 0.

Canonical Structure nat_ring_like_op : ring_like_op nat :=
  {| rngl_has_opp := false;
     rngl_has_inv := false;
     rngl_zero := 0;
     rngl_one := 1;
     rngl_add := Nat.add;
     rngl_mul := Nat.mul;
     rngl_opp := phony_Nat_opp;
     rngl_inv := phony_Nat_inv;
     rngl_opt_sub := Nat.sub;
     rngl_opt_div := Nat.div |}.

Existing Instance nat_ring_like_op.

Theorem Nat_eq_mul_0 : ∀ n m, n * m = 0 → n = 0 ∨ m = 0.
Proof. now intros; apply Nat.eq_mul_0. Qed.

Theorem Nat_neq_1_0 : 1 ≠ 0.
Proof. easy. Qed.

Theorem nat_characteristic_prop : ∀ i, rngl_of_nat (S i) ≠ 0.
Proof. easy. Qed.

Canonical Structure nat_ring_like_prop : ring_like_prop nat :=
  {| rngl_is_comm := true;
     rngl_has_dec_eq := true;
     rngl_is_domain := true;
     rngl_characteristic := 0;
     rngl_add_comm := Nat.add_comm;
     rngl_add_assoc := Nat.add_assoc;
     rngl_add_0_l := Nat.add_0_l;
     rngl_mul_assoc := Nat.mul_assoc;
     rngl_mul_1_l := Nat.mul_1_l;
     rngl_mul_add_distr_l := Nat.mul_add_distr_l;
     rngl_1_neq_0 := Nat_neq_1_0;
     rngl_opt_mul_comm := Nat.mul_comm;
     rngl_opt_mul_1_r := I;
     rngl_opt_mul_add_distr_r := I;
     rngl_opt_add_opp_l := I;
     rngl_opt_add_sub := Nat.add_sub;
     rngl_opt_mul_0_l := Nat.mul_0_l;
     rngl_opt_mul_0_r := Nat.mul_0_r;
     rngl_opt_mul_inv_l := I;
     rngl_opt_mul_inv_r := I;
     rngl_opt_mul_div := Nat.div_mul;
     rngl_opt_eq_dec := Nat.eq_dec;
     rngl_opt_is_integral := Nat_eq_mul_0;
     rngl_characteristic_prop := nat_characteristic_prop |}.

(*
Print nat_ring_like_op.
Existing Instance nat_ring_like_op.
Compute (7 - 3)%F.
Compute (7 - 3)%nat.
Compute (15 / 3)%F.
Compute (15 / 3)%nat.
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
  c ≠ 0 → Nat_pow_mod a b c = (a ^ b) mod c.
Proof.
intros * Hcz.
revert a.
induction b; intros; [ easy | ].
cbn; rewrite IHb.
now rewrite Nat.mul_mod_idemp_r.
Qed.

Definition inv_mod i n := Nat_pow_mod i (n - 2) n.

Theorem prime_mul_inv_l_mod : ∀ p a,
  is_prime p = true
  → a mod p ≠ 0
  → (inv_mod a p * a) mod p = 1.
Proof.
intros * Hp Haz.
unfold inv_mod.
rewrite Nat_pow_mod_is_pow_mod; [ | now intros H; subst p ].
rewrite Nat.mul_mod_idemp_l; [ | now intros H; subst p ].
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

Definition at_least_2 n := S (S (n - 2)).

Definition Zn n := {a : nat | a <? at_least_2 n = true}.

Theorem Zn_op_prop n r : r mod at_least_2 n <? at_least_2 n = true.
Proof.
intros.
apply Nat.ltb_lt.
now apply Nat.mod_upper_bound.
Qed.

Definition Zn_v n v : Zn n :=
  exist _ (v mod at_least_2 n) (Zn_op_prop n v).

Definition Zn_add n (a b : Zn n) : Zn n :=
  let r := proj1_sig a + proj1_sig b in
  exist _ (r mod at_least_2 n) (Zn_op_prop n r).
Definition Zn_mul n (a b : Zn n) : Zn n :=
  let r := proj1_sig a * proj1_sig b in
  exist _ (r mod at_least_2 n) (Zn_op_prop n r).
Definition Zn_opp n (a : Zn n) : Zn n :=
  let r := at_least_2 n - proj1_sig a in
  exist _ (r mod at_least_2 n) (Zn_op_prop n r).
Definition Zn_inv n (a : Zn n) : Zn n :=
  let r := inv_mod (proj1_sig a) n in
  exist _ (r mod at_least_2 n) (Zn_op_prop n r).
Definition Zn_div n (a b : Zn n) : Zn n :=
  if is_prime n then Zn_mul n a (Zn_inv n b)
  else a.

Definition phony_Zn_sub n (a b : Zn n) := a.

Canonical Structure Zn_ring_like_op n : ring_like_op (Zn n) :=
  {| rngl_has_opp := true;
     rngl_has_inv := is_prime n;
     rngl_zero := Zn_v n 0;
     rngl_one := Zn_v n 1;
     rngl_add := Zn_add n;
     rngl_mul := Zn_mul n;
     rngl_opp := Zn_opp n;
     rngl_inv := Zn_inv n;
     rngl_opt_sub := phony_Zn_sub n;
     rngl_opt_div := Zn_div n |}.

Existing Instance Zn_ring_like_op.

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

Section a.

Context {n : nat}.
Context (ro := Zn_ring_like_op n).
Existing Instance ro.

Theorem Zn_add_comm : ∀ (a b : Zn n), (a + b = b + a)%F.
Proof.
intros (a, Ha) (b, Hb).
apply Zn_eq; cbn - [ "mod" ].
now rewrite Nat.add_comm.
Qed.

Theorem Zn_add_assoc : ∀ (a b c : Zn n), (a + (b + c) = (a + b) + c)%F.
Proof.
intros.
apply Zn_eq; cbn - [ "mod" ].
rewrite Nat.add_mod_idemp_l; [ | easy ].
rewrite Nat.add_mod_idemp_r; [ | easy ].
now rewrite Nat.add_assoc.
Qed.

Theorem Zn_add_0_l : ∀ (a : Zn n), (0 + a = a)%F.
Proof.
intros.
apply Zn_eq; cbn - [ "mod" ].
rewrite (Nat.mod_small 0); [ | apply Nat.lt_0_succ ].
rewrite Nat.add_0_l.
apply Nat.mod_small.
destruct a as (a, Ha); cbn.
now apply Nat.ltb_lt in Ha.
Qed.

Theorem Zn_mul_assoc : ∀ (a b c : Zn n), (a * (b * c) = (a * b) * c)%F.
Proof.
intros.
apply Zn_eq; cbn - [ "mod" ].
rewrite Nat.mul_mod_idemp_l; [ | easy ].
rewrite Nat.mul_mod_idemp_r; [ | easy ].
now rewrite Nat.mul_assoc.
Qed.

Theorem Zn_mul_1_l : ∀ (a : Zn n), (1 * a = a)%F.
Proof.
intros.
apply Zn_eq; cbn - [ "mod" ].
rewrite (Nat.mod_small 1). 2: {
  apply -> Nat.succ_lt_mono.
  apply Nat.lt_0_succ.
}
rewrite Nat.mul_1_l.
destruct a as (a, Ha); cbn - [ "mod" ].
apply Nat.ltb_lt in Ha.
now apply Nat.mod_small.
Qed.

Theorem Zn_mul_add_distr_l : ∀ (a b c : Zn n),
  (a * (b + c) = a * b + a * c)%F.
Proof.
intros.
apply Zn_eq; cbn - [ "mod" ].
rewrite Nat.add_mod_idemp_l; [ | easy ].
rewrite Nat.add_mod_idemp_r; [ | easy ].
rewrite Nat.mul_mod_idemp_r; [ | easy ].
now rewrite Nat.mul_add_distr_l.
Qed.

Theorem Zn_neq_1_0 : (1 ≠ 0)%F.
Proof.
intros.
apply Zn_neq; cbn - [ "mod" ].
rewrite Nat.mod_small. 2: {
  apply -> Nat.succ_lt_mono.
  apply Nat.lt_0_succ.
}
rewrite Nat.mod_small. 2: {
  apply Nat.lt_0_succ.
}
easy.
Qed.

Theorem Zn_mul_comm : ∀ (a b : Zn n), (a * b = b * a)%F.
Proof.
intros (a, Ha) (b, Hb).
apply Zn_eq; cbn - [ "mod" ].
now rewrite Nat.mul_comm.
Qed.

Theorem Zn_add_opp_l : ∀ (a : Zn n), (- a + a = 0)%F.
Proof.
intros (a, Ha).
apply Zn_eq; cbn - [ "mod" "-" ].
apply Nat.ltb_lt in Ha.
rewrite Nat.add_mod_idemp_l; [ | easy ].
rewrite (Nat.mod_small 0); [ | apply Nat.lt_0_succ ].
rewrite Nat.sub_add. 2: {
  now apply Nat.lt_le_incl.
}
now apply Nat.mod_same.
Qed.

Theorem Zn_eq_dec : ∀ (a b : Zn n), ({a = b} + {a ≠ b})%F.
Proof.
intros (a, Ha) (b, Hb).
destruct (Nat.eq_dec a b) as [Hab| Hab]; [ left | right ]. {
  now apply Zn_eq.
} {
  now apply Zn_neq.
}
Qed.

Theorem Zn_opt_mul_inv_l :
  if is_prime n then ∀ a : Zn n, a ≠ 0%F → (¹/ a * a)%F = 1%F else True.
Proof.
intros.
remember (is_prime n) as p eqn:Hp.
symmetry in Hp.
destruct p; [ | easy ].
intros * Haz.
destruct (lt_dec n 2) as [Hn2| Hn2]. {
  destruct n; [ easy | ].
  destruct n0; [ easy | ].
  do 2 apply Nat.succ_lt_mono in Hn2.
  easy.
}
apply Nat.nlt_ge in Hn2; cbn.
apply Zn_eq; cbn - [ "mod" ].
rewrite (Nat.mod_small 1). 2: {
  apply -> Nat.succ_lt_mono.
  apply Nat.lt_0_succ.
}
rewrite Nat.mul_mod_idemp_l; [ | easy ].
replace (at_least_2 n) with n. 2: {
  destruct n as [| n']; [ easy | ].
  destruct n'; [ easy | ].
  unfold at_least_2.
  do 2 rewrite Nat.sub_succ.
  now rewrite Nat.sub_0_r.
}
apply prime_mul_inv_l_mod; [ easy | ].
destruct a as (a, Ha); cbn.
intros H; apply Haz; clear Haz.
apply Zn_eq; cbn; symmetry.
rewrite Nat.sub_diag; symmetry.
destruct a; [ easy | exfalso ].
apply Nat.ltb_lt in Ha.
unfold at_least_2 in Ha.
apply Nat.mod_divides in H; [ | flia Hn2 ].
destruct H as (c, Hc).
replace (S (S (n - 2))) with n in Ha by flia Hn2.
rewrite Hc in Ha.
apply Nat.nle_gt in Ha; apply Ha.
destruct c; [ now rewrite Nat.mul_comm in Hc | flia ].
Qed.

Theorem Zn_opt_mul_inv_r :
  if (is_prime n && negb true)%bool then ∀ a : Zn n, a ≠ 0%F → (a / a)%F = 1%F
  else True.
Proof.
now rewrite Bool.andb_false_r.
Qed.

Theorem proj1_sig_Zn_of_nat : ∀ i,
  proj1_sig (rngl_of_nat i) = i mod at_least_2 n.
Proof.
intros.
induction i. {
  cbn - [ "mod" ].
  now rewrite Nat.mod_0_l.
}
cbn - [ "mod" ].
rewrite (Nat.mod_small 1); [ | unfold at_least_2; flia ].
unfold at_least_2 in IHi.
cbn - [ "mod" ] in IHi.
rewrite IHi.
unfold at_least_2.
remember (S (S (n - 2))) as k eqn:Hk.
assert (Hk2 : 2 ≤ k) by flia Hk.
apply Nat.add_mod_idemp_r; flia Hk2.
Qed.

Theorem Zn_characteristic_prop :
  match at_least_2 n with
  | 0 => ∀ i : nat, rngl_of_nat (S i) ≠ 0%F
  | S _ => rngl_of_nat (at_least_2 n) = 0%F
  end.
Proof.
intros.
apply Zn_eq.
rewrite proj1_sig_Zn_of_nat.
rewrite Nat.mod_same; [ | easy ].
cbn; symmetry.
apply Nat.sub_diag.
Qed.

Theorem Zn_opt_mul_div :
  if rngl_has_inv then True else ∀ a b : Zn n, b ≠ 0%F → (a * b / b)%F = a.
Proof.
cbn.
unfold ro.
unfold Zn_div.
unfold Zn_ring_like_op.
remember (is_prime n) as p eqn:Hp.
symmetry in Hp.
destruct p; [ easy | ].
intros * Hb; cbn.
apply Zn_eq; cbn.
unfold Zn_div, Zn_mul; cbn - [ "mod" ].
rewrite Hp; cbn - [ "mod" ].
...

unfold rngl_div.
destruct rngl_has_inv; [ easy | ].
intros * Hb; cbn.
apply Zn_eq.
unfold Zn_div.
...
apply Zn_eq; cbn - [ "mod" ].
...
rewrite Nat.mul_mod_idemp_l; [ | easy ].
rewrite Nat.mul_mod_idemp_r; [ | easy ].
rewrite <- Nat.mul_assoc.
rewrite (Nat.mul_comm (proj1_sig b)).
rewrite <- Nat.mul_mod_idemp_r; [ | easy ].
...
  destruct n as [| n']; [ easy | ].
  destruct n'; [ easy | ].
...
rewrite prime_mul_inv_l_mod.
...
*)

Definition Zn_ring_like_prop : ring_like_prop (Zn n) :=
  {| rngl_is_comm := true;
     rngl_has_dec_eq := true;
     rngl_is_domain := false;
     rngl_characteristic := at_least_2 n;
     rngl_add_comm := Zn_add_comm;
     rngl_add_assoc := Zn_add_assoc;
     rngl_add_0_l := Zn_add_0_l;
     rngl_mul_assoc := Zn_mul_assoc;
     rngl_mul_1_l := Zn_mul_1_l;
     rngl_mul_add_distr_l := Zn_mul_add_distr_l;
     rngl_1_neq_0 := Zn_neq_1_0;
     rngl_opt_mul_comm := Zn_mul_comm;
     rngl_opt_mul_1_r := I;
     rngl_opt_mul_add_distr_r := I;
     rngl_opt_add_opp_l := Zn_add_opp_l;
     rngl_opt_add_sub := I;
     rngl_opt_mul_0_l := I;
     rngl_opt_mul_0_r := I;
     rngl_opt_mul_inv_l := Zn_opt_mul_inv_l;
     rngl_opt_mul_inv_r := Zn_opt_mul_inv_r;
     rngl_opt_mul_div := Zn_opt_mul_div;
     rngl_opt_eq_dec := Zn_eq_dec;
     rngl_opt_is_integral := I;
     rngl_characteristic_prop := Zn_characteristic_prop |}.

End a.
