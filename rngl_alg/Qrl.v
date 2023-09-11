(* ℚ is a ring-like with inverse *)
(* i.e. it is a field *)

Set Implicit Arguments.
Require Import Utf8.

Require Import Main.RingLike Rational.
Import Q.Notations.

Definition Q_leb (x y : Q) :=
  match Q.le_dec x y with
  | left _ => true
  | right _ => false
  end.

Canonical Structure Q_ring_like_op : ring_like_op Q :=
  {| rngl_zero := 0%Q;
     rngl_add := Q.add;
     rngl_mul := Q.mul;
     rngl_opt_one := Some 1%Q;
     rngl_opt_opp_or_subt := Some (inl Q.opp);
     rngl_opt_inv_or_quot := Some (inl Q.inv);
     rngl_opt_eq_dec := Some Q.eq_dec;
     rngl_opt_leb := Some Q_leb |}.

(*
Global Existing Instance Q_ring_like_op.
*)

Theorem Q_characteristic_prop :
  let roq := Q_ring_like_op in
  ∀ i, rngl_mul_nat 1 (S i) ≠ 0%Q.
Proof.
intros.
cbn - [ Q.add ].
assert (Hz : ∀ i, (0 ≤ rngl_mul_nat 1 i)%Q). {
  clear i; intros.
  progress unfold rngl_mul_nat.
  progress unfold mul_nat.
  cbn - [ Q.add ].
  induction i; [ easy | ].
  cbn - [ Q.add ].
  now destruct (List.fold_right _ _ _).
}
intros H.
specialize (Hz i).
apply Q.nlt_ge in Hz; apply Hz.
rewrite <- H.
apply Q.lt_sub_lt_add_r.
now rewrite Q.sub_diag.
Qed.

Theorem Q_mul_le_compat_nonneg :
  ∀ a b c d : Q,
  Q_leb 0%Q a = true ∧ Q_leb a c = true
  → Q_leb 0%Q b = true ∧ Q_leb b d = true
  → Q_leb (a * b)%Q (c * d)%Q = true.
Proof.
intros * Hac Hbd.
progress unfold Q_leb in Hac.
progress unfold Q_leb in Hbd.
progress unfold Q_leb.
destruct (Q.le_dec 0 a) as [Hza| ]; [ | easy ].
destruct (Q.le_dec 0 b) as [Hzb| ]; [ | easy ].
destruct Hac as (_, Hac).
destruct Hbd as (_, Hbd).
destruct (Q.le_dec a c) as [Hac'| ]; [ | easy ].
destruct (Q.le_dec b d) as [Hbd'| ]; [ | easy ].
clear Hac Hbd.
destruct (Q.le_dec (a * b) (c * d)) as [| H3]; [ easy | ].
exfalso; apply H3.
now apply Q.mul_le_mono_nonneg.
Qed.

Theorem Q_mul_le_compat_nonpos :
  ∀ a b c d : Q,
  Q_leb c a = true ∧ Q_leb a 0%Q = true
  → Q_leb d b = true ∧ Q_leb b 0%Q = true
  → Q_leb (a * b)%Q (c * d)%Q = true.
Proof.
intros * Hca Hdb.
progress unfold Q_leb in Hca.
progress unfold Q_leb in Hdb.
progress unfold Q_leb.
destruct (Q.le_dec c a) as [Hca'| ]; [ | easy ].
destruct (Q.le_dec d b) as [Hdb'| ]; [ | easy ].
destruct Hca as (_, Hca).
destruct Hdb as (_, Hdb).
destruct (Q.le_dec a 0) as [Haz| ]; [ | easy ].
destruct (Q.le_dec b 0) as [Hbz| ]; [ | easy ].
clear Hca Hdb.
destruct (Q.le_dec (a * b) (c * d)) as [| H3]; [ easy | ].
exfalso; apply H3.
now apply Q.mul_le_mono_nonpos.
Qed.

Theorem Q_not_le :
  ∀ a b : Q, Q_leb a b ≠ true → a ≠ b ∧ Q_leb b a = true.
Proof.
intros * Hab.
progress unfold Q_leb in Hab.
progress unfold Q_leb.
destruct (Q.le_dec a b) as [| Hab']; [ easy | clear Hab ].
apply Q.nle_gt in Hab'.
destruct (Q.le_dec b a) as [Hba| Hba]. {
  split; [ | easy ].
  intros H; subst b.
  now apply Q.lt_irrefl in Hab'.
}
exfalso; apply Hba.
now apply Q.lt_le_incl.
Qed.

Theorem Q_le_dec :
  ∀ a b : Q, {Q_leb a b = true} + {Q_leb a b ≠ true}.
Proof.
intros.
unfold Q_leb.
now destruct (Q.le_dec a b); [ left | right ].
Qed.

Theorem Q_le_refl : ∀ a : Q, Q_leb a a = true.
Proof.
intros.
progress unfold Q_leb.
destruct (Q.le_dec a a) as [H| H]; [ easy | ].
exfalso; apply H.
apply Q.le_refl.
Qed.

Theorem Q_le_antisymm :
  ∀ a b : Q, Q_leb a b = true → Q_leb b a = true → a = b.
Proof.
intros * Hab Hba.
progress unfold Q_leb in Hab.
progress unfold Q_leb in Hba.
destruct (Q.le_dec a b) as [H1| ]; [ | easy ].
destruct (Q.le_dec b a) as [H2| ]; [ | easy ].
now apply Q.le_antisymm.
Qed.

Theorem Q_le_trans :
  ∀ a b c : Q, Q_leb a b = true → Q_leb b c = true → Q_leb a c = true.
Proof.
intros * Hab Hbc.
progress unfold Q_leb in Hab.
progress unfold Q_leb in Hbc.
progress unfold Q_leb.
destruct (Q.le_dec a b) as [H1| ]; [ | easy ].
destruct (Q.le_dec b c) as [H2| ]; [ | easy ].
destruct (Q.le_dec a c) as [| H3]; [ easy | ].
exfalso; apply H3.
now apply (Q.le_trans _ b).
Qed.

Theorem Q_add_le_compat :
  ∀ a b c d : Q,
  Q_leb a b = true → Q_leb c d = true → Q_leb (a + c)%Q (b + d)%Q = true.
Proof.
intros * Hab Hcd.
progress unfold Q_leb in Hab.
progress unfold Q_leb in Hcd.
progress unfold Q_leb.
destruct (Q.le_dec a b) as [H1| ]; [ | easy ].
destruct (Q.le_dec c d) as [H2| ]; [ | easy ].
destruct (Q.le_dec (a + c) (b + d)) as [| H3]; [ easy | ].
exfalso; apply H3.
now apply Q.add_le_mono.
Qed.

Definition Q_ring_like_prop :=
  {| rngl_mul_is_comm := true;
     rngl_is_integral_domain := false;
     rngl_is_archimedean := false; (* to be implemented *)
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := Q.add_comm;
     rngl_add_assoc := Q.add_assoc;
     rngl_add_0_l := Q.add_0_l;
     rngl_mul_assoc := Q.mul_assoc;
     rngl_opt_mul_1_l := Q.mul_1_l;
     rngl_mul_add_distr_l := Q.mul_add_distr_l;
     rngl_opt_mul_comm := Q.mul_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_l := Q.add_opp_diag_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_mul_inv_l := Q.mul_inv_l;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_le_dec := Q_le_dec;
     rngl_opt_integral := NA;
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := Q_characteristic_prop;
     rngl_opt_le_refl := Q_le_refl;
     rngl_opt_le_antisymm := Q_le_antisymm;
     rngl_opt_le_trans := Q_le_trans;
     rngl_opt_add_le_compat := Q_add_le_compat;
     rngl_opt_mul_le_compat_nonneg := Q_mul_le_compat_nonneg;
     rngl_opt_mul_le_compat_nonpos := Q_mul_le_compat_nonpos;
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := Q_not_le;
     rngl_opt_archimedean := NA |}.
