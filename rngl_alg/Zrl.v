(* ℤ is a ring-like, i.e. a ring *)

Require Import Utf8.
Require Import ZArith.

Require Import Main.RingLike.

Notation "x ≤ y" := (x <= y)%Z (at level 70, y at next level) : Z_scope.
Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%Z (at level 70, y at next level) :
  Z_scope.

Canonical Structure Z_ring_like_op : ring_like_op Z :=
  {| rngl_zero := 0%Z;
     rngl_add := Z.add;
     rngl_mul := Z.mul;
     rngl_opt_one := Some 1%Z;
     rngl_opt_opp_or_subt := Some (inl Z.opp);
     rngl_opt_inv_or_quot := Some (inr Z.quot);
     rngl_opt_eqb := Some Z.eqb;
     rngl_opt_leb := Some Z.leb |}.

(*
Global Existing Instance Z_ring_like_op.
*)

Theorem Z_eq_mul_0 :  ∀ n m, (n * m)%Z = 0%Z → n = 0%Z ∨ m = 0%Z.
Proof. now apply Z.eq_mul_0. Qed.

Theorem Z_characteristic_prop :
  let roz := Z_ring_like_op in
  ∀ i, rngl_mul_nat 1 (S i) ≠ 0%Z.
Proof.
intros.
cbn - [ Z.add ].
assert (Hz : ∀ i, (0 <= rngl_mul_nat 1 i)%Z). {
  clear i; intros.
  cbn - [ Z.add ].
  induction i; [ easy | ].
  cbn - [ Z.add ].
  now destruct (rngl_mul_nat 1%Z i).
}
intros H.
specialize (Hz i).
apply Z.nlt_ge in Hz; apply Hz.
rewrite <- H.
apply Z.lt_sub_lt_add_r.
now rewrite Z.sub_diag.
Qed.

Theorem Z_mul_le_compat_nonneg :
  ∀ a b c d : Z,
  (0 <=? a)%Z = true ∧ (a <=? c)%Z = true
  → (0 <=? b)%Z = true ∧ (b <=? d)%Z = true
  → (a * b <=? c * d)%Z = true.
Proof.
intros * (Hza, Hac) (Hzb, Hbd).
apply Z.leb_le in Hza, Hac, Hzb, Hbd.
apply Z.leb_le.
now apply Z.mul_le_mono_nonneg.
Qed.

Theorem Z_mul_le_compat_nonpos :
  ∀ a b c d : Z,
  (c <=? a)%Z = true ∧ (a <=? 0)%Z = true
  → (d <=? b)%Z = true ∧ (b <=? 0)%Z = true
  → (a * b <=? c * d)%Z = true.
Proof.
intros * (Hac, Haz) (Hbd, Hbz).
apply Z.leb_le in Hac, Haz, Hbd, Hbz.
apply Z.leb_le.
now apply Z.mul_le_mono_nonpos.
Qed.

Theorem Z_not_le :
  ∀ a b : Z, (a <=? b)%Z ≠ true → a = b ∨ (b <=? a)%Z = true.
Proof.
intros * Hab.
apply Bool.not_true_iff_false in Hab.
apply Z.leb_gt in Hab; right.
now apply Z.leb_le, Z.lt_le_incl.
Qed.

Theorem Z_opt_quot_mul :
  let roz := Z_ring_like_op in
  if rngl_has_quot then
    ∀ a b c : Z, b ≠ 0%L → c ≠ 0%L → (a / (b * c))%L = (a / b / c)%L
  else not_applicable.
Proof.
intros; cbn.
intros * Hbz Hcz.
now symmetry; apply Z.quot_quot.
Qed.

Theorem Z_opt_le_dec : ∀ a b : Z, {(a <=? b)%Z = true} + {(a <=? b)%Z ≠ true}.
Proof.
intros.
specialize (Z_le_dec a b) as H1.
destruct H1 as [H1| H1]; [ left | right ]. {
  now apply Z.leb_le.
} {
  intros H2.
  now apply Z.leb_le in H2.
}
Qed.

Theorem Z_le_refl : ∀ a : Z, (a <=? a)%Z = true.
Proof.
intros.
apply Z.leb_le, Z.le_refl.
Qed.

Theorem Z_le_antisymm :
  ∀ a b : Z, (a <=? b)%Z = true → (b <=? a)%Z = true → a = b.
Proof.
intros * Hab Hba.
apply Z.leb_le in Hab, Hba.
now apply Z.le_antisymm.
Qed.

Theorem Z_le_trans :
  ∀ a b c : Z, (a <=? b)%Z = true → (b <=? c)%Z = true → (a <=? c)%Z = true.
Proof.
intros * Hab Hbc.
apply Z.leb_le in Hab, Hbc.
apply Z.leb_le.
now apply (Z.le_trans _ b).
Qed.

Theorem Z_add_le_compat :
  ∀ a b c d : Z,
  (a <=? b)%Z = true → (c <=? d)%Z = true → (a + c <=? b + d)%Z = true.
Proof.
intros * Hab Hcd.
apply Z.leb_le in Hab, Hcd.
apply Z.leb_le.
now apply Z.add_le_mono.
Qed.

Definition Z_ring_like_prop : ring_like_prop Z :=
  {| rngl_mul_is_comm := true;
     rngl_is_integral_domain := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := Z.add_comm;
     rngl_add_assoc := Z.add_assoc;
     rngl_add_0_l := Z.add_0_l;
     rngl_mul_assoc := Z.mul_assoc;
     rngl_opt_mul_1_l := Z.mul_1_l;
     rngl_mul_add_distr_l := Z.mul_add_distr_l;
     rngl_opt_mul_comm := Z.mul_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_l := Z.add_opp_diag_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_mul_inv_l := NA;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_mul_div := Z.quot_mul;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_eqb_eq := Z.eqb_eq;
     rngl_opt_le_dec := Z_opt_le_dec;
     rngl_opt_integral := Z_eq_mul_0;
     rngl_opt_alg_closed := NA;
     rngl_characteristic_prop := Z_characteristic_prop;
     rngl_opt_le_refl := Z_le_refl;
     rngl_opt_le_antisymm := Z_le_antisymm;
     rngl_opt_le_trans := Z_le_trans;
     rngl_opt_add_le_compat := Z_add_le_compat;
     rngl_opt_mul_le_compat_nonneg := Z_mul_le_compat_nonneg;
     rngl_opt_mul_le_compat_nonpos := Z_mul_le_compat_nonpos;
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := Z_not_le |}.
