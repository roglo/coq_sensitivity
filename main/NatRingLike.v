(* ℕ is a ring-like without opposite, i.e. a semiring *)
(* ℤ/nℤ is a ring-like,
     if n is prime, has inverse, i.e. it is a field
     if n is not prime, it has neither inverse nor division, it is a ring *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Misc RingLike.

Canonical Structure nat_ring_like_op : ring_like_op nat :=
  {| rngl_zero := 0;
     rngl_add := Nat.add;
     rngl_mul := Nat.mul;
     rngl_opt_one := Some 1;
     rngl_opt_opp_or_subt := Some (inr Nat.sub);
     rngl_opt_inv_or_quot := Some (inr Nat.div);
     rngl_opt_eq_dec := Some Nat.eq_dec;
     rngl_opt_leb := Some Nat.leb |}.

(*
Global Existing Instance nat_ring_like_op.
*)

Theorem Nat_eq_mul_0 : ∀ n m, n * m = 0 → n = 0 ∨ m = 0.
Proof. now intros; apply Nat.eq_mul_0. Qed.

Theorem nat_characteristic_prop :
  let ro := nat_ring_like_op in
  ∀ i, rngl_mul_nat 1 (S i) ≠ 0.
Proof. easy. Qed.

Theorem Nat_mul_div :
  let ro := nat_ring_like_op in
  ∀ a b, b ≠ 0%L → (a * b / b)%L = a.
Proof.
intros * Hbz.
now apply Nat.div_mul.
Qed.

Theorem Nat_mul_le_compat :
  ∀ a b c d : nat,
  (a <=? c) = true → (b <=? d) = true → (a * b <=? c * d) = true.
Proof.
intros * Hab Hcd.
apply Nat.leb_le in Hab, Hcd.
apply Nat.leb_le.
now apply Nat.mul_le_mono.
Qed.

Theorem Nat_not_le :
  ∀ a b : nat, (a <=? b) ≠ true → a ≠ b ∧ (b <=? a) = true.
Proof.
intros * Hab.
apply Bool.not_true_iff_false in Hab.
apply Nat.leb_gt in Hab.
split. {
  now intros H; subst b; apply Nat.lt_irrefl in Hab.
}
apply Nat.leb_le.
now apply Nat.lt_le_incl.
Qed.

Theorem Nat_mul_sub_distr_l :
  let ro := nat_ring_like_op in
  ∀ a b c, (a * (b - c))%L = (a * b - a * c)%L.
Proof.
intros.
apply Nat.mul_sub_distr_l.
Qed.

Theorem Nat_opt_quot_mul :
  let ro := nat_ring_like_op in
  if rngl_has_quot _ then
    ∀ a b c : nat, b ≠ 0%L → c ≠ 0%L → (a / (b * c))%L = (a / b / c)%L
  else not_applicable.
Proof.
intros; cbn.
intros * Hbz Hcz.
symmetry; apply (Nat.div_div _ _ _ Hbz Hcz).
Qed.

Theorem Nat_opt_le_dec :
  ∀ a b : nat, {(a <=? b) = true} + {(a <=? b) ≠ true}.
Proof.
intros.
apply Bool.bool_dec.
Qed.

Theorem Nat_le_antisymm :
  ∀ a b : nat, (a <=? b) = true → (b <=? a) = true → a = b.
Proof.
intros * Hab Hba.
apply Nat.leb_le in Hab, Hba.
now apply Nat.le_antisymm.
Qed.

Theorem Nat_le_trans :
  ∀ a b c : nat, (a <=? b) = true → (b <=? c) = true → (a <=? c) = true.
Proof.
intros * Hab Hbc.
apply Nat.leb_le in Hab, Hbc.
apply Nat.leb_le.
now apply (Nat.le_trans _ b).
Qed.

Theorem Nat_add_le_compat :
  ∀ a b c d : nat,
  (a <=? b) = true → (c <=? d) = true → (a + c <=? b + d) = true.
Proof.
intros * Hab Hcd.
apply Nat.leb_le in Hab, Hcd.
apply Nat.leb_le.
now apply Nat.add_le_mono.
Qed.

Theorem nat_archimedean :
  let ro := nat_ring_like_op in
  ∀ a b : nat, (0 < a < b)%L → ∃ n : nat, (b < rngl_mul_nat a n)%L.
Proof.
intros * (Ha, Hab) *.
exists (S b).
apply Nat.leb_gt in Ha, Hab; cbn in Ha.
apply Nat.leb_gt; cbn.
apply Nat.neq_0_lt_0 in Ha.
(**)
...
apply -> Nat.succ_lt_mono.
destruct b; [ easy | ].
apply -> Nat.lt_succ_r in Hab.
apply Nat.succ_lt_mono in Hab.
apply Nat.succ_lt_mono in Hab.
apply -> Nat.succ_lt_mono.
clear Ha.
cbn.
revert a Hab.
induction b; intros; [ easy | cbn ].
rewrite Nat.add_succ_r.
apply -> Nat.succ_lt_mono.
...
induction b; intros; [ easy | cbn ].
apply -> Nat.lt_succ_r in Hab.
destruct (Nat.eq_dec a b) as [Heab| Heab]. {
  subst b.
  rewrite <- Nat.add_1_r.
  apply Nat.add_lt_mono_l.
  clear IHb Hab.
  destruct a; [ easy | cbn ].
  clear Ha.
  apply -> Nat.succ_lt_mono.
  now rewrite Nat.add_succ_r.
}
eapply Nat.le_lt_trans. 2: {
  apply Nat.add_lt_mono_l.
  apply IHb.
  eapply Nat.le_lt_trans; [ apply Hab | ].
...
intros * (Ha, Hab) *.
exists (S (b / a)); cbn.
apply Nat.leb_gt in Ha, Hab; cbn in Ha.
apply Nat.leb_gt.
apply Nat.neq_0_lt_0 in Ha.
remember (b / a) as n eqn:Hn; symmetry in Hn.
specialize (Nat.div_mod_eq b a) as H2.
rewrite Hn in H2.
clear Hn.
revert b Hab H2.
induction n; intros. {
  rewrite Nat.mul_0_r, Nat.add_0_l in H2.
  rewrite H2 in Hab.
  apply Nat.nle_gt in Hab.
  exfalso; apply Hab.
  apply Nat.lt_le_incl.
  now apply Nat.mod_upper_bound.
}
cbn.
rewrite Nat.mul_succ_r in H2.
rewrite H2.
rewrite (Nat.add_comm _ a).
rewrite <- Nat.add_assoc.
apply Nat.add_lt_mono_l.
apply IHn. 2: {
  rewrite Nat.add_mod_idemp_r; [ | easy ].
  rewrite <- Nat.add_mod_idemp_l; [ | easy ].
  rewrite Nat.mul_comm, Nat.mod_mul; [ | easy ].
  now rewrite Nat.add_0_l.
}
...
destruct n. 2: {
  rewrite Nat.mul_succ_r.
  rewrite (Nat.add_comm _ a), <- Nat.add_assoc.
  apply Nat.lt_add_pos_r.
...
  rewrite H2.
  rewrite Nat.add_mod_idemp_r; [ | easy ].
  rewrite <- Nat.add_mod_idemp_l; [ | easy ].
  rewrite (Nat.mul_comm _ (S n)), Nat_mod_add_l_mul_r; [ | easy ].
  rewrite Nat.mod_same; [ | easy ].
  rewrite Nat.add_0_l.
  now rewrite Nat.add_0_l.

  apply Nat.add_pos_r.

...
etransitivity. 2: {
  apply IHn.
  apply Nat_div_small_iff in Hn; [ | easy ].
  apply Nat.nle_gt in Hn.
  now exfalso; apply Hn; apply Nat.lt_le_incl.
}
cbn.
clear Hn.
induction n. {
  cbn.
  rewrite Nat.add_0_r.
...
  apply Nat_div_small_iff in Hn; [ | easy ].
  apply Nat.nle_gt in Hn.
  now exfalso; apply Hn; apply Nat.lt_le_incl.
}
cbn.
...
specialize (Nat.div_mod_eq b a) as H1.
...
intros * (Ha, Hab) *.
apply Nat.leb_gt in Ha, Hab; cbn in Ha.
exists (S (b / a)).
remember (b / a) as n eqn:Hn.
symmetry in Hn.
revert a b Ha Hab Hn.
induction n; intros. {
  apply Nat.neq_0_lt_0 in Ha.
  apply Nat_div_small_iff in Hn; [ | easy ].
  apply Nat.nle_gt in Hn.
  now exfalso; apply Hn; apply Nat.lt_le_incl.
}
cbn.
cbn in IHn.
(* ah, fait chier, tiens *)
...
  apply (f_equal (λ b, a * b)) in Hn.
  rewrite Nat.mul_0_r in Hn.
  apply
Search (_ * (_ / _)).
  apply Nat.div_small in Hab.
  cbn; rewrite Nat.add_0_r.
Search (_ / _ = 0).
apply
cbn - [ "/" ].
exists (S n).
apply Nat.leb_gt; cbn.
induction n; [ now rewrite Nat.add_0_r | ].
cbn; rewrite <- Nat.add_1_l.
now apply Nat.add_le_lt_mono.
...

Theorem glop :
  let ro := nat_ring_like_op in
   ∀ ε : nat, (0 < ε)%L →
   ∀ n : nat, ∃ m : nat, (rngl_mul_nat 1 n < rngl_mul_nat ε m)%L.
Proof.
intros * Hε *.
apply Nat.leb_gt in Hε.
exists (S n).
apply Nat.leb_gt; cbn.
induction n; [ now rewrite Nat.add_0_r | ].
cbn; rewrite <- Nat.add_1_l.
now apply Nat.add_le_lt_mono.
Qed.

Canonical Structure nat_ring_like_prop : ring_like_prop nat :=
  {| rngl_mul_is_comm := true;
     rngl_is_integral_domain := true;
     rngl_is_archimedean := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := Nat.add_comm;
     rngl_add_assoc := Nat.add_assoc;
     rngl_add_0_l := Nat.add_0_l;
     rngl_mul_assoc := Nat.mul_assoc;
     rngl_opt_mul_1_l := Nat.mul_1_l;
     rngl_mul_add_distr_l := Nat.mul_add_distr_l;
     rngl_opt_mul_comm := Nat.mul_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_l := NA;
     rngl_opt_add_sub := Nat.add_sub;
     rngl_opt_sub_add_distr := Nat.sub_add_distr;
     rngl_opt_mul_inv_l := NA;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_mul_div := Nat_mul_div;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_le_dec := Nat_opt_le_dec;
     rngl_opt_integral := Nat_eq_mul_0;
     rngl_opt_alg_closed := NA;
     rngl_characteristic_prop := nat_characteristic_prop;
     rngl_opt_le_refl := Nat.leb_refl;
     rngl_opt_le_antisymm := Nat_le_antisymm;
     rngl_opt_le_trans := Nat_le_trans;
     rngl_opt_add_le_compat := Nat_add_le_compat;
     rngl_opt_mul_le_compat_nonneg := NA;
     rngl_opt_mul_le_compat_nonpos := NA;
     rngl_opt_mul_le_compat := Nat_mul_le_compat;
     rngl_opt_not_le := Nat_not_le;
     rngl_opt_archimedean := nat_archimedean |}.

(*
Global Existing Instance nat_ring_like_prop.
*)

(*
Print nat_ring_like_op.
Existing Instance nat_ring_like_op.
Compute (7 - 3)%L.
Compute (7 - 3)%nat.
Compute (15 / 3)%L.
Compute (15 / 3)%nat.
*)
