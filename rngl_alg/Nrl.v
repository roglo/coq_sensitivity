(* ℕ is a ring-like without opposite, i.e. a semiring *)
(* ℤ/nℤ is a ring-like,
     if n is prime, has inverse, i.e. it is a field
     if n is not prime, it has neither inverse nor division, it is a ring *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Main.Misc Main.RingLike Misc FermatLittle.

(*
Canonical Structure nat_ring_like_op : ring_like_op nat :=
  ...
Canonical Structure nat_ring_like_prop : ring_like_prop nat :=
  ...
have been moved to NatRingLike.v in directory ../main
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
Definition Zn_div n (a b : Zn n) : Zn n :=
  if is_prime n then Zn_mul n a (Zn_inv n b)
  else a.
Definition Zn_eqb n (a b : Zn n) : bool :=
  proj1_sig a =? proj1_sig b.

Definition Zn_ring_like_op n : ring_like_op (Zn n) :=
  {| rngl_zero := Zn_of_nat n 0;
     rngl_one := Zn_of_nat n 1;
     rngl_add := Zn_add n;
     rngl_mul := Zn_mul n;
     rngl_opt_opp_or_subt :=
       Some (inl (Zn_opp n));
     rngl_opt_inv_or_quot :=
       if is_prime n then Some (inl (Zn_inv n)) else None;
     rngl_opt_eqb := Some (Zn_eqb n);
     rngl_opt_le := None |}.

(*
Global Existing Instance Zn_ring_like_op.
*)

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
(*
Context (ro := Zn_ring_like_op n).
Existing Instance ro.
*)

Theorem Zn_add_comm :
  let roz := Zn_ring_like_op n in
  ∀ (a b : Zn n), (a + b = b + a)%L.
Proof.
intros roz (a, Ha) (b, Hb).
apply Zn_eq; cbn - [ "mod" ].
now rewrite Nat.add_comm.
Qed.

Theorem Zn_add_assoc :
  let roz := Zn_ring_like_op n in
  ∀ (a b c : Zn n), (a + (b + c) = (a + b) + c)%L.
Proof.
intros roz *.
apply Zn_eq; cbn - [ "mod" ].
rewrite Nat.add_mod_idemp_l; [ | easy ].
rewrite Nat.add_mod_idemp_r; [ | easy ].
now rewrite Nat.add_assoc.
Qed.

Theorem Zn_add_0_l :
  let roz := Zn_ring_like_op n in
  ∀ (a : Zn n), (0 + a = a)%L.
Proof.
intros roz *.
apply Zn_eq; cbn - [ "mod" ].
rewrite (Nat.mod_small 0); [ | apply Nat.lt_0_succ ].
rewrite Nat.add_0_l.
apply Nat.mod_small.
destruct a as (a, Ha); cbn.
now apply Nat.ltb_lt in Ha.
Qed.

Theorem Zn_mul_assoc :
  let roz := Zn_ring_like_op n in
  ∀ (a b c : Zn n), (a * (b * c) = (a * b) * c)%L.
Proof.
intros roz *.
apply Zn_eq; cbn - [ "mod" ].
rewrite Nat.mul_mod_idemp_l; [ | easy ].
rewrite Nat.mul_mod_idemp_r; [ | easy ].
now rewrite Nat.mul_assoc.
Qed.

Theorem Zn_mul_1_l :
  let roz := Zn_ring_like_op n in
  ∀ (a : Zn n), (1 * a = a)%L.
Proof.
intros roz *.
apply Zn_eq; cbn - [ "mod" ].
rewrite Nat.mul_mod_idemp_l; [ | easy ].
rewrite Nat.mul_1_l.
destruct a as (a, Ha); cbn - [ "mod" ].
apply Nat.ltb_lt in Ha.
now apply Nat.mod_small.
Qed.

Theorem Zn_mul_add_distr_l :
  let roz := Zn_ring_like_op n in
  ∀ (a b c : Zn n), (a * (b + c) = a * b + a * c)%L.
Proof.
intros roz *.
apply Zn_eq; cbn - [ "mod" ].
rewrite Nat.add_mod_idemp_l; [ | easy ].
rewrite Nat.add_mod_idemp_r; [ | easy ].
rewrite Nat.mul_mod_idemp_r; [ | easy ].
now rewrite Nat.mul_add_distr_l.
Qed.

Theorem Zn_mul_comm :
  let roz := Zn_ring_like_op n in
  ∀ (a b : Zn n), (a * b = b * a)%L.
Proof.
intros roz (a, Ha) (b, Hb).
apply Zn_eq; cbn - [ "mod" ].
now rewrite Nat.mul_comm.
Qed.

Theorem Zn_add_opp_l :
  let roz := Zn_ring_like_op n in
  ∀ (a : Zn n), (- a + a = 0)%L.
Proof.
intros roz (a, Ha).
apply Zn_eq; cbn - [ "mod" "-" ].
apply Nat.ltb_lt in Ha.
rewrite Nat.add_mod_idemp_l; [ | easy ].
rewrite (Nat.mod_small 0); [ | apply Nat.lt_0_succ ].
rewrite Nat.sub_add. 2: {
  now apply Nat.lt_le_incl.
}
now apply Nat.mod_same.
Qed.

Theorem Zn_eqb_eq :
  let roz := Zn_ring_like_op n in
  ∀ a b : Zn n, (a =? b)%L = true ↔ a = b.
Proof.
intros roz (a, Ha) (b, Hb); cbn.
split. {
  intros Hab.
  apply Nat.eqb_eq in Hab; subst b.
  apply eq_exist_uncurried.
  exists eq_refl.
  apply (Eqdep_dec.UIP_dec Bool.bool_dec).
} {
  intros Hab.
  apply Nat.eqb_eq.
  now injection Hab.
}
Qed.

Theorem Zn_eq_dec : ∀ (a b : Zn n), ({a = b} + {a ≠ b})%L.
Proof.
intros (a, Ha) (b, Hb).
destruct (Nat.eq_dec a b) as [Hab| Hab]; [ left | right ]. {
  now apply Zn_eq.
} {
  now apply Zn_neq.
}
Qed.

Theorem Zn_opt_mul_inv_l :
  let roz := Zn_ring_like_op n in
  if rngl_has_inv then ∀ a : Zn n, a ≠ 0%L → (a⁻¹ * a)%L = 1%L
  else not_applicable.
Proof.
intros.
unfold rngl_has_inv; cbn.
remember (is_prime n) as p eqn:Hp.
symmetry in Hp.
destruct p; [ cbn | easy ].
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
  flia Hn2.
}
unfold rngl_inv.
cbn - [ "/" "mod" ].
rewrite Hp.
cbn - [ "/" "mod" ].
unfold "<?".
cbn - [ "/" "mod" ].
rewrite Nat.mul_mod_idemp_l; [ | easy ].
replace (at_least_1 n) with n. 2: {
  destruct n as [| n']; [ easy | ].
  destruct n'; [ easy | ].
  unfold at_least_1.
  rewrite Nat.sub_succ.
  now rewrite Nat.sub_0_r.
}
apply prime_mul_inv_l_mod; [ easy | ].
destruct a as (a, Ha); cbn.
intros H; apply Haz; clear Haz.
apply Zn_eq; cbn; symmetry.
rewrite Nat.sub_diag; symmetry.
destruct a; [ easy | exfalso ].
apply Nat.ltb_lt in Ha.
unfold at_least_1 in Ha.
apply Nat.mod_divides in H; [ | flia Hn2 ].
destruct H as (c, Hc).
replace (S (S (n - 2))) with n in Ha by flia Hn2.
rewrite Hc in Ha.
apply Nat.nle_gt in Ha; apply Ha.
destruct c; [ now rewrite Nat.mul_comm in Hc | flia Hn2 ].
Qed.

Theorem Zn_opt_mul_inv_r :
  let roz := Zn_ring_like_op n in
  if (rngl_has_inv && negb true)%bool then
    ∀ a : Zn n, a ≠ 0%L → (a / a)%L = 1%L
  else not_applicable.
Proof.
now intros; rewrite Bool.andb_false_r.
Qed.

Theorem Zn_opt_mul_div :
  let roz := Zn_ring_like_op n in
  if rngl_has_quot then ∀ a b : Zn n, b ≠ 0%L → (a * b / b)%L = a
  else not_applicable.
Proof.
intros.
unfold rngl_has_quot; cbn.
remember (is_prime n) as p eqn:Hp; symmetry in Hp.
now destruct p.
Qed.

Theorem Zn_opt_mul_quot_r :
  let roz := Zn_ring_like_op n in
  if (rngl_has_quot && negb true)%bool then
    ∀ a b : Zn n, b ≠ 0%L → (b * a / b)%L = a
  else not_applicable.
Proof.
now intros; rewrite Bool.andb_false_r.
Qed.

Theorem proj1_sig_Zn_of_nat :
  let roz := Zn_ring_like_op n in
  ∀ i, proj1_sig (rngl_of_nat i) = i mod at_least_1 n.
Proof.
intros.
induction i. {
  cbn - [ "mod" ].
  now rewrite Nat.mod_0_l.
}
cbn - [ "mod" ].
cbn - [ "mod" ] in IHi.
rewrite IHi.
rewrite Nat.add_mod_idemp_l; [ | easy ].
rewrite Nat.add_mod_idemp_r; [ | easy ].
easy.
Qed.

Theorem Zn_characteristic_prop :
  let roz := Zn_ring_like_op n in
  if at_least_1 n =? 0 then ∀ i : nat, rngl_of_nat (S i) ≠ 0%L
  else
    (∀ i : nat, 0 < i < at_least_1 n → rngl_of_nat i ≠ 0%L) ∧
    rngl_of_nat (at_least_1 n) = 0%L.
Proof.
intros.
split. {
  intros i Hi.
  cbn; intros H.
  specialize (@proj1_sig_Zn_of_nat i) as H1.
  subst roz.
  unfold Zn in H.
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
rewrite Nat.mod_same; [ | easy ].
cbn; symmetry.
apply Nat.sub_diag.
Qed.

Theorem Zn_opt_quot_mul :
  let roz := Zn_ring_like_op n in
  if rngl_has_quot then
    ∀ a b c : Zn n, b ≠ 0%L → c ≠ 0%L → (a / (b * c))%L = (a / b / c)%L
  else not_applicable.
Proof.
intros; cbn.
remember rngl_has_quot as qu eqn:Hqu; symmetry in Hqu.
destruct qu; [ | easy ].
intros * Hbz Hcz.
apply Zn_eq; cbn.
unfold rngl_div; cbn.
specialize Zn_opt_mul_div as H1.
fold roz in H1.
cbn in H1.
unfold rngl_div in H1.
rewrite Hqu in H1 |-*.
remember rngl_has_inv as iv eqn:Hiv; symmetry in Hiv.
destruct iv. {
  unfold rngl_has_quot in Hqu.
  unfold rngl_has_inv in Hiv.
  destruct rngl_opt_inv_or_quot as [iq| ]; [ | easy ].
  now destruct iq.
}
unfold rngl_quot in H1 |-*.
unfold rngl_has_quot in Hqu.
destruct rngl_opt_inv_or_quot as [iq| ]; [ | easy ].
destruct iq as [| quot]; [ easy | ].
...

Definition Zn_ring_like_prop : ring_like_prop (Zn n) :=
  {| rngl_mul_is_comm := true;
     rngl_has_dec_le := false;
     rngl_is_integral := false;
     rngl_is_alg_closed := false;
     rngl_characteristic := at_least_1 n;
     rngl_add_comm := Zn_add_comm;
     rngl_add_assoc := Zn_add_assoc;
     rngl_add_0_l := Zn_add_0_l;
     rngl_mul_assoc := Zn_mul_assoc;
     rngl_mul_1_l := Zn_mul_1_l;
     rngl_mul_add_distr_l := Zn_mul_add_distr_l;
     rngl_opt_mul_comm := Zn_mul_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_l := Zn_add_opp_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_mul_sub_distr_l := NA;
     rngl_opt_mul_sub_distr_r := NA;
     rngl_opt_mul_inv_l := Zn_opt_mul_inv_l;
     rngl_opt_mul_inv_r := Zn_opt_mul_inv_r;
     rngl_opt_mul_div := Zn_opt_mul_div;
     rngl_opt_mul_quot_r := Zn_opt_mul_quot_r;
     rngl_opt_quot_mul := Zn_opt_quot_mul;
     rngl_opt_eqb_eq := Zn_eqb_eq;
     rngl_opt_le_dec := NA;
     rngl_opt_integral := NA;
     rngl_opt_alg_closed := NA;
     rngl_characteristic_prop := Zn_characteristic_prop;
     rngl_opt_le_refl := NA;
     rngl_opt_le_antisymm := NA;
     rngl_opt_le_trans := NA;
     rngl_opt_add_le_compat := NA;
     rngl_opt_mul_le_compat_nonneg := NA;
     rngl_opt_mul_le_compat_nonpos := NA;
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := NA |}.

End a.

(* Semiring by Mohammed Abu Shamia in his PhD
   "On Some Types Of Ideals In Semirings", Aug 2008,
   https://iugspace.iugaza.edu.ps/bitstream/handle/20.500.12358/21352/file_1.pdf
   Example 1.15
   This "almost" semiring is special because:
   1/ 1=0, but not a trivial set
   2/ 0 is not absorbing
   3/ it is integral
   4/ its characteristic is 1
   5/ the natural 0 (which is not the 0) is absorbing for + and x
 *)

Definition lcm_ring_like_op : ring_like_op nat :=
  {| rngl_zero := 1;
     rngl_one := 1;
     rngl_add := Nat.lcm;
     rngl_mul := Nat.mul;
     rngl_opt_opp_or_subt := None;
     rngl_opt_inv_or_quot := None;
     rngl_opt_eqb := Some Nat.eqb;
     rngl_opt_le := None |}.

Section a.

Context (ro := lcm_ring_like_op).
(*
Existing Instance ro.
*)

Theorem lcm_mul_add_distr_l : ∀ a b c,
  a * Nat.lcm b c = Nat.lcm (a * b) (a * c).
Proof.
intros.
symmetry.
apply Nat.lcm_mul_mono_l.
Qed.

Theorem lcm_opt_integral : ∀ a b, a * b = 1 → a = 1 ∨ b = 1.
Proof.
intros * Hab.
apply Nat.eq_mul_1 in Hab.
now left.
Qed.

Theorem lcm_characteristic_prop :
  let rol := lcm_ring_like_op in
  if 1 =? 0 then ∀ i : nat, rngl_of_nat (S i) ≠ 0%L
  else (∀ i : nat, 0 < i < 1 → rngl_of_nat i ≠ 0%L) ∧ rngl_of_nat 1 = 0%L.
Proof.
split; [ intros * Hi; flia Hi | easy ].
Qed.

Definition lcm_ring_like_prop :=
  let rol := lcm_ring_like_op in
  {| rngl_mul_is_comm := true;
     rngl_has_dec_le := false;
     rngl_is_integral := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := 1;
     rngl_add_comm := Nat.lcm_comm;
     rngl_add_assoc := Nat.lcm_assoc;
     rngl_add_0_l := Nat.lcm_1_l;
     rngl_mul_assoc := Nat.mul_assoc;
     rngl_mul_1_l := Nat.mul_1_l;
     rngl_mul_add_distr_l := lcm_mul_add_distr_l;
     rngl_opt_mul_comm := Nat.mul_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_l := NA;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_mul_sub_distr_l := NA;
     rngl_opt_mul_sub_distr_r := NA;
     rngl_opt_mul_inv_l := NA;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_eqb_eq := Nat.eqb_eq;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_le_dec := NA;
     rngl_opt_integral := lcm_opt_integral;
     rngl_opt_alg_closed := NA;
     rngl_characteristic_prop := lcm_characteristic_prop;
     rngl_opt_le_refl := NA;
     rngl_opt_le_antisymm := NA;
     rngl_opt_le_trans := NA;
     rngl_opt_add_le_compat := NA;
     rngl_opt_mul_le_compat_nonneg := NA;
     rngl_opt_mul_le_compat_nonpos := NA;
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := NA |}.

End a.
