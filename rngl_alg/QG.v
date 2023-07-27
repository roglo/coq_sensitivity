(* implementation of rationals with the normal rationals of
   coq (library QArith) together with a field saying that the
   numerator and the denominator are coprimes. This allows to
   use normal equality instead of ==. Therefore rewrite is
   possible. *)

Set Nested Proofs Allowed.
Set Implicit Arguments.
Require Import Utf8.

Require Import QArith.
Notation "x ≤ y" := (Z.le x y) : Z_scope.
Notation "x ≤ y" := (Qle x y) : Q_scope.
Notation "x ≤ y" := (Nat.le x y) : nat_scope.
Notation "x ≤ y" := (Pos.le x y) : positive_scope.

Definition Z_pos_gcd z p :=
  match z with
  | Z0 => p
  | Zpos zp => Pos.gcd zp p
  | Zneg zp => Pos.gcd zp p
  end.

Record QG := mk_qg
  {qg_q : Q; qg_gcd : Z_pos_gcd (Qnum qg_q) (Qden qg_q) = 1%positive}.

Theorem Z_pos_gcd_Z_gcd :
  ∀ n d, Z_pos_gcd n d = Z.to_pos (Z.gcd n (Z.pos d)).
Proof.
intros.
unfold Z_pos_gcd.
now destruct n.
Qed.

Theorem Z_pos_gcd_opp_l : ∀ z p, Z_pos_gcd (- z) p = Z_pos_gcd z p.
Proof. now intros; destruct z. Qed.

Theorem Pos_gcd_comm : ∀ a b, Pos.gcd a b = Pos.gcd b a.
Proof.
intros.
apply Pos2Z.inj.
do 2 rewrite Pos2Z.inj_gcd.
apply Z.gcd_comm.
Qed.

Theorem Pos_gcd_le_l : ∀ a b, (Pos.gcd a b <= a)%positive.
Proof.
intros.
specialize (Pos.gcd_divide_l a b) as H1.
apply Z.divide_Zpos in H1.
apply Znumtheory.Zdivide_mod in H1.
apply Zdiv.Zmod_divides in H1; [ | easy ].
destruct H1 as (c & Hc).
destruct c as [| c| c]; [ easy | | easy ].
cbn in Hc.
apply Pos2Z.inj in Hc.
rewrite Hc at 2.
remember (_ * _)%positive as x.
rewrite <- (Pos.mul_1_r (Pos.gcd _ _)); subst x.
apply Pos.mul_le_mono_l.
apply Pos.le_1_l.
Qed.

Theorem Pos_gcd_le_r : ∀ a b, (Pos.gcd a b <= b)%positive.
Proof.
intros.
rewrite Pos_gcd_comm.
apply Pos_gcd_le_l.
Qed.

Theorem QG_of_Q_prop : ∀ q,
  let g := Z_pos_gcd (Qnum q) (Qden q) in
  Z_pos_gcd (Qnum (Qnum q / Z.pos g # Z.to_pos (QDen q / Z.pos g)))
    (Qden (Qnum q / Z.pos g # Z.to_pos (QDen q / Z.pos g))) = 1%positive.
Proof.
intros; cbn.
subst g; cbn.
progress unfold Z_pos_gcd.
remember (Qnum q) as qn eqn:Hqn; symmetry in Hqn.
destruct qn as [| qn| qn]. {
  now cbn; rewrite Z.div_same.
} {
  remember (Z.pos qn / _)%Z as z eqn:Hz; symmetry in Hz.
  destruct z as [| z| z]. {
    apply Z.div_small_iff in Hz; [ | easy ].
    destruct Hz as [(Hz1, Hz2)| Hz]; [ | easy ].
    exfalso.
    apply Z.nle_gt in Hz2; apply Hz2; clear Hz2.
    apply Pos2Z.pos_le_pos.
    apply Pos_gcd_le_l.
  } {
    apply Pos2Z.inj; cbn.
    rewrite Pos2Z.inj_gcd.
    rewrite <- Hz.
    rewrite Z2Pos.id. 2: {
      apply Z.div_str_pos.
      split; [ easy | ].
      apply Pos2Z.pos_le_pos.
      apply Pos_gcd_le_r.
    }
    now apply Z.gcd_div_gcd.
  } {
    specialize (Zdiv.Z_div_nonneg_nonneg) as H1.
    remember (Z.pos _) as x eqn:Hx in Hz.
    remember (Z.pos _) as y eqn:Hy in Hz.
    specialize (H1 x y).
    assert (H : (0 <= x)%Z) by now subst x.
    specialize (H1 H); clear H.
    assert (H : (0 <= y)%Z) by now subst y.
    specialize (H1 H); clear H.
    now rewrite Hz in H1.
  }
} {
  remember (Z.neg qn / _)%Z as z eqn:Hz; symmetry in Hz.
  destruct z as [| z| z]. {
    apply Z.div_small_iff in Hz; [ | easy ].
    now destruct Hz.
  } {
    apply Pos2Z.inj; cbn.
    rewrite Pos2Z.inj_gcd.
    rewrite <- Hz.
    rewrite Z2Pos.id. 2: {
      apply Z.div_str_pos.
      split; [ easy | ].
      apply Pos2Z.pos_le_pos.
      apply Pos_gcd_le_r.
    }
    now apply Z.gcd_div_gcd.
  } {
    apply (f_equal Z.opp) in Hz.
    cbn in Hz.
    rewrite <- Zdiv.Z_div_zero_opp_full in Hz. 2: {
      rewrite Pos2Z.inj_gcd.
      rewrite <- Z.gcd_opp_l.
      rewrite Pos2Z.opp_pos.
      apply Znumtheory.Zdivide_mod.
      apply Z.gcd_divide_l.
    }
    cbn in Hz.
    apply (f_equal Z.to_pos) in Hz.
    cbn in Hz.
    rewrite <- Hz.
    rewrite Pos2Z.inj_gcd.
    rewrite <- Z2Pos.inj_gcd; cycle 1. {
      apply Z.div_str_pos.
      split; [ easy | ].
      apply Znumtheory.Zdivide_le; [ easy | easy | ].
      apply Z.gcd_divide_l.
    } {
      apply Z.div_str_pos.
      split; [ easy | ].
      apply Znumtheory.Zdivide_le; [ easy | easy | ].
      apply Z.gcd_divide_r.
    }
    rewrite Z.gcd_div_factor; [ | easy | | ]; cycle 1. {
      apply Z.gcd_divide_l.
    } {
      apply Z.gcd_divide_r.
    }
    now rewrite Z.div_same.
  }
}
Qed.

Definition QG_of_Q (q : Q) :=
  let g := Z_pos_gcd (Qnum q) (Qden q) in
  mk_qg (Qmake (Qnum q / Zpos g) (Z.to_pos (Zpos (Qden q) / Zpos g)%Z))
    (QG_of_Q_prop q).

Definition QG_0 := QG_of_Q 0.
Definition QG_1 := QG_of_Q 1.
Definition QG_add (a b : QG) := QG_of_Q (qg_q a + qg_q b).
Definition QG_mul (a b : QG) := QG_of_Q (qg_q a * qg_q b).
Definition QG_opp (a : QG) := QG_of_Q (- qg_q a).
Definition QG_inv (a : QG) := QG_of_Q (/ qg_q a).
Definition QG_sub (a b : QG) := QG_add a (QG_opp b).

Definition QG_eqb (a b : QG) := Qeq_bool (qg_q a) (qg_q b).
Definition QG_leb (a b : QG) := Qle_bool (qg_q a) (qg_q b).
Definition QG_le a b := QG_leb a b = true.
Definition QG_lt a b := QG_leb b a = false.

Declare Scope QG_scope.
Delimit Scope QG_scope with QG.

Notation "0" := QG_0 : QG_scope.
Notation "1" := QG_1 : QG_scope.
Notation "- a" := (QG_opp a) : QG_scope.
Notation "a + b" := (QG_add a b) : QG_scope.
Notation "a - b" := (QG_sub a b) : QG_scope.
Notation "a * b" := (QG_mul a b) : QG_scope.
Notation "a '⁻¹'" := (QG_inv a) (at level 1, format "a ⁻¹") :
  QG_scope.

Notation "a =? b" := (QG_eqb a b) (at level 70) : QG_scope.
Notation "a ≤? b" := (QG_leb a b) (at level 70) : QG_scope.
Notation "a <? b" := (negb (QG_leb b a)) (at level 70) : QG_scope.
Notation "a ≤ b" := (QG_le a b) : QG_scope.
Notation "a < b" := (QG_lt a b) : QG_scope.
Notation "a ≤ b ≤ c" := (QG_le a b ∧ QG_le b c)
  (at level 70, b at next level) : QG_scope.
Notation "a < b < c" := (QG_lt a b ∧ QG_lt b c)
  (at level 70, b at next level) : QG_scope.

Arguments qg_q q%QG.

Theorem eq_QG_eq : ∀ q1 q2 : QG, q1 = q2 ↔ qg_q q1 = qg_q q2.
Proof.
intros.
split; intros Hq; [ now subst q2 | ].
destruct q1 as (q1, Hq1).
destruct q2 as (q2, Hq2).
cbn in Hq; subst q2.
f_equal.
apply (Eqdep_dec.UIP_dec Pos.eq_dec).
Qed.

Theorem QG_of_Q_0 : ∀ d, QG_of_Q (0 # d) = QG_of_Q 0.
Proof.
intros.
apply eq_QG_eq; cbn.
now rewrite (Z.div_same (Z.pos d)).
Qed.

Theorem Nat_gcd_iff :
  ∀ a b c, c ≠ 0%nat →
  Nat.gcd a b = c ↔
  Nat.divide c a ∧ Nat.divide c b ∧ Nat.gcd (a / c) (b / c) = 1%nat.
Proof.
intros * Hcz.
split; intros Habc. {
  subst c.
  split; [ apply Nat.gcd_divide_l | ].
  split; [ apply Nat.gcd_divide_r | ].
  now apply Nat.gcd_div_gcd.
} {
  destruct Habc as (Hca & Hcb & Habc).
  destruct Hca as (ca, Hca).
  destruct Hcb as (cb, Hcb).
  subst a b.
  rewrite Nat.gcd_mul_mono_r.
  rewrite Nat.div_mul in Habc; [ | easy ].
  rewrite Nat.div_mul in Habc; [ | easy ].
  rewrite Habc.
  apply Nat.mul_1_l.
}
Qed.

Theorem Nat_Bezout_mul :
  ∀ a b c,
  Nat.Bezout a b 1
  → Nat.Bezout a c 1
  → Nat.gcd a (b * c) = 1%nat.
Proof.
intros * H1 H2.
destruct (Nat.eq_dec a 1) as [Ha1| Ha1]; [ now subst a | ].
destruct (Nat.eq_dec c 0) as [Hcz| Hcz]. {
  subst c; rewrite Nat.mul_0_r.
  rewrite Nat.gcd_0_r.
  destruct H2 as (u & v & Huv).
  rewrite Nat.mul_0_r, Nat.add_0_r in Huv.
  now apply Nat.eq_mul_1 in Huv.
}
destruct H1 as (u1 & v1 & H1).
symmetry in H1.
apply Nat.add_sub_eq_r in H1.
destruct H2 as (u2 & v2 & H2).
symmetry in H2.
apply Nat.add_sub_eq_r in H2.
specialize (f_equal2_mult _ _ _ _ H1 H2) as H3.
rewrite Nat.mul_1_l in H3.
rewrite Nat.mul_sub_distr_l in H3.
rewrite H1, Nat.mul_1_l in H3 at 1.
rewrite Nat.mul_sub_distr_r in H3.
rewrite Nat.mul_shuffle0 in H3.
rewrite Nat.mul_assoc in H3.
apply Nat.add_sub_eq_nz in H3; [ | easy ].
rewrite <- Nat.add_sub_swap in H3. 2: {
  rewrite (Nat.mul_comm _ a).
  do 3 rewrite Nat.mul_assoc.
  rewrite <- Nat.mul_assoc.
  rewrite <- (Nat.mul_assoc (a * u1)).
  apply Nat.mul_le_mono_r.
  apply Nat.add_sub_eq_nz in H1; [ | easy ].
  rewrite (Nat.mul_comm a).
  rewrite <- H1.
  apply Nat.le_add_r.
}
apply Nat.add_sub_eq_nz in H3. 2: {
  intros H4.
  apply Nat.eq_mul_0 in H4.
  destruct H4 as [H4| H4]; [ now rewrite H4 in H2 | ].
  now rewrite H4, Nat.mul_0_r in H1.
}
apply Nat.add_sub_eq_r in H3.
rewrite Nat.add_sub_swap in H3. 2: {
  apply Nat.add_sub_eq_nz in H1; [ | easy ].
  rewrite (Nat.mul_comm (_ * _ * _)).
  do 2 rewrite Nat.mul_assoc.
  rewrite (Nat.mul_comm a).
  rewrite <- H1.
  apply Nat.add_sub_eq_nz in H2; [ | easy ].
  rewrite <- H2.
  do 2 rewrite Nat.mul_add_distr_r.
  rewrite Nat.mul_1_l.
  rewrite Nat.add_comm.
  apply Nat.add_le_mono_r.
  apply Nat.le_succ_l.
  apply Nat.neq_0_lt_0.
  intros H4.
  apply Nat.eq_mul_0 in H4.
  destruct H4 as [H4| H4]; [ | easy ].
  apply Nat.eq_mul_0 in H4.
  destruct H4 as [H4| H4]. 2: {
    subst v2.
    rewrite Nat.mul_0_l, Nat.add_0_l in H2.
    symmetry in H2.
    now apply Nat.eq_mul_1 in H2.
  }
  rewrite H4 in H1.
  symmetry in H1.
  now apply Nat.eq_mul_1 in H1.
}
rewrite <- Nat.mul_sub_distr_r in H3.
rewrite Nat.mul_assoc in H3.
rewrite (Nat.mul_shuffle0 v1) in H3.
rewrite <- (Nat.mul_assoc (v1 * v2)) in H3.
rewrite Nat.gcd_comm.
apply Nat.bezout_1_gcd.
exists (v1 * v2)%nat.
exists (u1 * v2 * c - u2)%nat.
symmetry in H3; rewrite Nat.add_comm in H3.
easy.
Qed.

Theorem Nat_gcd_mul_r_1 :
  ∀ a b c,
  Nat.gcd a b = 1%nat → Nat.gcd a c = 1%nat → Nat.gcd a (b * c) = 1%nat.
Proof.
intros * Hab Hac.
destruct (Nat.eq_dec a 0) as [Haz| Haz]. {
  now subst a; cbn in *; subst.
}
specialize (Nat.gcd_bezout a b) as H1.
specialize (Nat.gcd_bezout a c) as H2.
rewrite Hab in H1.
rewrite Hac in H2.
apply Nat_Bezout_mul. {
  destruct H1 as [H1| H1]; [ easy | ].
  now apply Nat.bezout_comm.
} {
  destruct H2 as [H2| H2]; [ easy | ].
  now apply Nat.bezout_comm.
}
Qed.

Theorem Nat_eq_gcd_mul_1 :
  ∀ a b c, Nat.gcd (a * b) c = 1%nat → Nat.gcd a c = 1%nat.
Proof.
intros * Habc.
destruct (Nat.eq_dec a 0) as [Haz| Haz]; [ now subst a | ].
apply Nat.bezout_1_gcd.
specialize (Nat.gcd_bezout (a * b) c) as H1.
rewrite Habc in H1.
destruct H1 as [H1| H1]. {
  destruct H1 as (u & v & Huv).
  exists (u * b)%nat, v.
  rewrite <- Huv.
  now rewrite Nat.mul_shuffle0, Nat.mul_assoc.
} {
  destruct H1 as (u & v & Huv).
  apply (Nat.bezout_comm _ _ _ Haz).
  exists u, (v * b)%nat.
  rewrite Huv.
  now rewrite Nat.mul_shuffle0, Nat.mul_assoc.
}
Qed.

Theorem Nat_gcd_mul_r :
  ∀ a b c, Nat.gcd a b = 1%nat → Nat.gcd a c = Nat.gcd a (b * c).
Proof.
intros * Hab.
destruct (Nat.eq_dec (Nat.gcd a b) 0) as [Habz| Habz]; [ congruence | ].
destruct (Nat.eq_dec (Nat.gcd a c) 0) as [Hacz| Hacz]. {
  rewrite Hacz; symmetry.
  apply Nat.gcd_eq_0 in Hacz.
  destruct Hacz; subst; cbn.
  apply Nat.mul_0_r.
}
destruct (Nat.eq_dec (Nat.gcd a c) 1) as [Hac1| Hac1]. {
  rewrite Hac1; symmetry.
  now apply Nat_gcd_mul_r_1.
}
specialize (Nat.gcd_div_gcd a c (Nat.gcd a c) Hacz eq_refl) as H1.
remember (a / Nat.gcd a c)%nat as a' eqn:Ha'.
remember (c / Nat.gcd a c)%nat as c' eqn:Hc'.
specialize (Nat_gcd_mul_r_1 a' b c') as H2.
assert (Ha : a = (a' * Nat.gcd a c)%nat). {
  rewrite Ha', Nat.mul_comm.
  rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
    apply Nat.gcd_divide_l.
  }
  now rewrite Nat.mul_comm, Nat.div_mul.
}
assert (Hc : c = (c' * Nat.gcd a c)%nat). {
  rewrite Hc', Nat.mul_comm.
  rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
    apply Nat.gcd_divide_r.
  }
  now rewrite Nat.mul_comm, Nat.div_mul.
}
assert (Ha'b : Nat.gcd a' b = 1%nat). {
  rewrite Ha in Hab.
  now apply Nat_eq_gcd_mul_1 in Hab.
}
specialize (H2 Ha'b H1).
symmetry.
rewrite Hc at 1.
rewrite Ha at 1.
rewrite Nat.mul_assoc.
rewrite Nat.gcd_mul_mono_r.
rewrite H2.
apply Nat.mul_1_l.
Qed.

Theorem Nat_div_gcd_1 : ∀ a b c d,
  (a * d = b * c → Nat.gcd a b = 1 → Nat.gcd c d = 1 → a = c)%nat.
Proof.
intros * Hadbc Hab Hcd.
specialize (Nat.gauss a b c) as H1.
rewrite <- Hadbc in H1.
assert (H : Nat.divide a (a * d)) by (exists d; apply Nat.mul_comm).
specialize (H1 H Hab); clear H.
specialize (Nat.gauss c d a) as H2.
rewrite Nat.mul_comm, Hadbc in H2.
assert (H : Nat.divide c (b * c)) by now exists b.
specialize (H2 H Hcd); clear H.
now apply Nat.divide_antisym.
Qed.

Theorem Nat_div_gcd : ∀ a b c d,
  (a * b * c * d ≠ 0 → a * d = b * c → a / Nat.gcd a b = c / Nat.gcd c d)%nat.
Proof.
intros * Habcdz Hadbc.
remember (Nat.gcd a b) as gab eqn:Hgab.
remember (Nat.gcd c d) as gcd eqn:Hgcd.
assert (Hgabz : gab ≠ 0%nat). {
  intros H; subst gab.
  apply Nat.gcd_eq_0 in H.
  now destruct H; subst a; rewrite Nat.mul_0_l in Habcdz.
}
assert (Hgcdz : gcd ≠ 0%nat). {
  intros H; subst gcd.
  apply Nat.gcd_eq_0 in H.
  now destruct H; subst d; rewrite Nat.mul_0_r in Habcdz.
}
apply Nat_div_gcd_1 with (b := (b / gab)%nat) (d := (d / gcd)%nat); cycle 1. {
  now apply Nat.gcd_div_gcd.
} {
  now apply Nat.gcd_div_gcd.
}
rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
  rewrite Hgcd.
  apply Nat.gcd_divide_r.
}
rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
  rewrite Hgcd.
  apply Nat.gcd_divide_l.
}
f_equal.
rewrite Nat.mul_comm.
rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
  rewrite Hgab.
  apply Nat.gcd_divide_l.
}
rewrite (Nat.mul_comm _ c).
rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
  rewrite Hgab.
  apply Nat.gcd_divide_r.
}
f_equal.
rewrite Nat.mul_comm, Hadbc.
apply Nat.mul_comm.
Qed.

(* should be added in coq library ZArith *)

Theorem fold_Z_sub : ∀ a b, (a + - b = a - b)%Z.
Proof. easy. Qed.

Theorem Z_mul_div_eq_l :
  ∀ a b c : Z, a ≠ 0%Z → (a * b)%Z = c → (c / a)%Z = b.
Proof.
intros * Haz Habc.
apply (f_equal (λ x, Z.div x a)) in Habc.
rewrite Z.mul_comm in Habc.
now rewrite Z.div_mul in Habc.
Qed.

Theorem Z_abs_of_nat : ∀ a, Z.abs (Z.of_nat a) = Z.of_nat a.
Proof.
intros.
remember (Z.of_nat a) as x eqn:Hx; symmetry in Hx.
destruct x as [| x| x]; [ easy | easy | ].
specialize (Nat2Z.is_nonneg a) as H1.
now rewrite Hx in H1.
Qed.

Theorem Nat_gcd_pos :
  ∀ x y, Nat.gcd (Pos.to_nat x) (Pos.to_nat y) = Pos.to_nat (Pos.gcd x y).
Proof.
intros.
progress unfold Pos.gcd.
remember (Pos.size_nat x + Pos.size_nat y)%nat as n eqn:Hn.
assert (H : (Pos.size_nat x + Pos.size_nat y ≤ n)%nat). {
  now rewrite Hn; apply Nat.le_refl.
}
clear Hn; rename H into Hn.
revert x y Hn.
induction n; intros; cbn; [ now destruct x | ].
assert (Hgp : ∀ x y,
  (Pos.size_nat x + S (Pos.size_nat y) ≤ n)%nat
  → (x < y)%positive
  → Nat.gcd (Pos.to_nat x~1) (Pos.to_nat y~1) =
     Pos.to_nat (Pos.gcdn n (y - x) x~1)). {
  clear x y Hn.
  intros * Hn Hxy.
  do 2 rewrite Pos2Nat.inj_xI.
  rewrite <- Nat.add_1_r.
  rewrite <- (Nat.add_1_r (_ * _)).
  rewrite <- IHn. 2: {
    eapply Nat.le_trans; [ | apply Hn ].
    rewrite Nat.add_comm.
    rewrite <- Nat.add_succ_comm.
    apply Nat.add_le_mono; [ apply Nat.le_refl | ].
    apply Pos.size_nat_monotone.
    now apply Pos.sub_decr.
  }
  rewrite Pos2Nat.inj_xI.
  rewrite <- (Nat.add_1_r (_ * _)).
  rewrite Pos2Nat.inj_sub; [ | easy ].
  rewrite (Nat.gcd_comm (_ - _)).
  symmetry.
  rewrite (Nat_gcd_mul_r _ 2%nat). 2: {
    rewrite Nat.gcd_comm, Nat.add_comm, Nat.mul_comm.
    now rewrite Nat.gcd_add_mult_diag_r.
  }
  symmetry.
  rewrite Nat.add_comm.
  rewrite <- Nat.gcd_sub_diag_r. 2: {
    rewrite Nat.add_comm.
    apply Nat.add_le_mono_r.
    apply Nat.mul_le_mono_l.
    apply Pos2Nat.inj_lt in Hxy.
    now apply Nat.lt_le_incl.
  }
  rewrite Nat.sub_add_distr.
  rewrite Nat.add_sub.
  rewrite <- Nat.mul_sub_distr_l.
  easy.
}
destruct x as [x| x| ]; [ | | easy ]. {
  cbn in Hn.
  apply Nat.succ_le_mono in Hn.
  destruct y as [y| y| ]. {
    cbn in Hn.
    remember (x ?= y)%positive as xy eqn:Hxy; symmetry in Hxy.
    destruct xy. {
      apply Pos.compare_eq in Hxy; subst y.
      now rewrite Nat.gcd_diag.
    } {
      apply -> Pos.compare_lt_iff in Hxy.
      now apply Hgp.
    } {
      rewrite <- Nat.add_succ_comm, Nat.add_comm in Hn.
      apply -> Pos.compare_gt_iff in Hxy.
      rewrite Nat.gcd_comm.
      now apply Hgp.
    }
  } {
    cbn in Hn.
    rewrite Pos2Nat.inj_xI.
    rewrite Pos2Nat.inj_xO.
    rewrite <- Nat_gcd_mul_r. 2: {
      rewrite <- Nat.add_1_l, Nat.gcd_comm, Nat.mul_comm.
      apply Nat.gcd_add_mult_diag_r.
    }
    rewrite <- Nat.add_succ_comm in Hn.
    rewrite <- Pos2Nat.inj_xI.
    now apply IHn.
  } {
    rewrite Pos2Nat.inj_1.
    apply Nat.gcd_1_r.
  }
} {
  cbn in Hn.
  apply Nat.succ_le_mono in Hn.
  destruct y as [y| y| ]. {
    rewrite Pos2Nat.inj_xI.
    rewrite Pos2Nat.inj_xO.
    rewrite Nat.gcd_comm.
    rewrite <- Nat_gcd_mul_r. 2: {
      rewrite <- Nat.add_1_l, Nat.gcd_comm, Nat.mul_comm.
      apply Nat.gcd_add_mult_diag_r.
    }
    rewrite Nat.gcd_comm.
    rewrite <- Pos2Nat.inj_xI.
    now apply IHn.
  } {
    do 3 rewrite Pos2Nat.inj_xO.
    rewrite Nat.gcd_mul_mono_l.
    f_equal.
    apply IHn.
    cbn in Hn.
    eapply Nat.le_trans; [ | apply Hn ].
    apply Nat.add_le_mono_l.
    apply Nat.le_succ_diag_r.
  } {
    rewrite Pos2Nat.inj_1.
    apply Nat.gcd_1_r.
  }
}
Qed.

Theorem Z_of_nat_gcd :
  ∀ a b, Z.of_nat (Nat.gcd a b) = Z.gcd (Z.of_nat a) (Z.of_nat b).
Proof.
intros.
progress unfold Z.gcd.
remember (Z.of_nat a) as x eqn:Hx; symmetry in Hx.
destruct x as [| x| x]. {
  rewrite Z_abs_of_nat.
  now destruct a.
} {
  remember (Z.of_nat b) as y eqn:Hy; symmetry in Hy.
  destruct y as [| y| y]. {
    destruct b; [ now rewrite Nat.gcd_0_r | easy ].
  } {
    rewrite Pos2Z.inj_gcd.
    apply (f_equal Z.to_nat) in Hx, Hy.
    rewrite Nat2Z.id in Hx, Hy.
    subst a b.
    do 2 rewrite Z2Nat.inj_pos.
    rewrite Nat_gcd_pos.
    now rewrite positive_nat_Z.
  } {
    specialize (Pos2Z.neg_is_neg y) as H1.
    rewrite <- Hy in H1.
    apply Z.nle_gt in H1.
    exfalso; apply H1.
    apply Nat2Z.is_nonneg.
  }
} {
  specialize (Pos2Z.neg_is_neg x) as H1.
  rewrite <- Hx in H1.
  apply Z.nle_gt in H1.
  exfalso; apply H1.
  apply Nat2Z.is_nonneg.
}
Qed.

Theorem Pos_gcd_diag : ∀ a, Pos.gcd a a = a.
Proof.
intros.
apply Pos2Nat.inj.
rewrite <- Nat_gcd_pos.
now rewrite Nat.gcd_diag.
Qed.

Theorem Z_div_gcd_1 : ∀ a b c d,
  (0 < a * c → a * d = b * c → Z.gcd a b = 1 → Z.gcd c d = 1 → a = c)%Z.
Proof.
intros * Hacp Hadbc Hab Hcd.
specialize (Z.gauss a b c) as H1.
rewrite <- Hadbc in H1.
assert (H : Z.divide a (a * d)) by (exists d; apply Z.mul_comm).
specialize (H1 H Hab); clear H.
specialize (Z.gauss c d a) as H2.
rewrite Z.mul_comm, Hadbc in H2.
assert (H : Z.divide c (b * c)) by now exists b.
specialize (H2 H Hcd); clear H.
apply Z.divide_antisym in H1; [ | easy ].
destruct H1 as [H1| H1]; [ easy | ].
rewrite H1 in Hacp.
rewrite Z.mul_opp_r in Hacp.
exfalso; apply Z.nle_gt in Hacp; apply Hacp.
apply Z.opp_nonpos_nonneg.
apply Z.square_nonneg.
Qed.

Theorem Z_div_gcd : ∀ a b c d : Z,
  (0 < a)%Z
  → (0 < b)%Z
  → (0 < c)%Z
  → (0 < d)%Z
  → (a * d)%Z = (b * c)%Z
  → (a / Z.gcd a b)%Z = (c / Z.gcd c d)%Z.
Proof.
intros * Hap Hbp Hcp Hdp Hadbc.
remember (Z.gcd a b) as gab eqn:Hgab.
remember (Z.gcd c d) as gcd eqn:Hgcd.
assert (Hgabz : gab ≠ 0%Z). {
  intros H; subst gab.
  apply Z.gcd_eq_0 in H.
  now destruct H; subst a; apply Z.lt_irrefl in Hap.
}
assert (Hgcdz : gcd ≠ 0%Z). {
  intros H; subst gcd.
  apply Z.gcd_eq_0 in H.
  now destruct H; subst c; apply Z.lt_irrefl in Hcp.
}
apply Z_div_gcd_1 with (b := (b / gab)%Z) (d := (d / gcd)%Z); cycle 2. {
  now apply Z.gcd_div_gcd.
} {
  now apply Z.gcd_div_gcd.
} {
  apply Z.mul_pos_pos. {
    apply Z.div_str_pos.
    split. {
      specialize (Z.lt_total 0 gab) as H1.
      destruct H1 as [H1| H1]; [ easy | ].
      destruct H1 as [H1| H1]; [ now symmetry in H1 | ].
      apply Z.nle_gt in H1; exfalso; apply H1.
      rewrite Hgab.
      apply Z.gcd_nonneg.
    } {
      rewrite Hgab.
      destruct a as [| a| a]; [ easy | | easy ].
      destruct b as [| b| b]; [ easy | | easy ].
      rewrite <- Pos2Z.inj_gcd.
      apply Pos2Z.pos_le_pos.
      apply Pos_gcd_le_l.
    }
  } {
    apply Z.div_str_pos.
    split. {
      specialize (Z.lt_total 0 gcd) as H1.
      destruct H1 as [H1| H1]; [ easy | ].
      destruct H1 as [H1| H1]; [ now symmetry in H1 | ].
      apply Z.nle_gt in H1; exfalso; apply H1.
      rewrite Hgcd.
      apply Z.gcd_nonneg.
    } {
      rewrite Hgcd.
      destruct c as [| c| c]; [ easy | | easy ].
      destruct d as [| d| d]; [ easy | | easy ].
      rewrite <- Pos2Z.inj_gcd.
      apply Pos2Z.pos_le_pos.
      apply Pos_gcd_le_l.
    }
  }
}
rewrite <- Z.divide_div_mul_exact; [ | easy | ]. 2: {
  rewrite Hgcd.
  apply Z.gcd_divide_r.
}
rewrite <- Z.divide_div_mul_exact; [ | easy | ]. 2: {
  rewrite Hgcd.
  apply Z.gcd_divide_l.
}
f_equal.
rewrite Z.mul_comm.
rewrite <- Z.divide_div_mul_exact; [ | easy | ]. 2: {
  rewrite Hgab.
  apply Z.gcd_divide_l.
}
rewrite (Z.mul_comm _ c).
rewrite <- Z.divide_div_mul_exact; [ | easy | ]. 2: {
  rewrite Hgab.
  apply Z.gcd_divide_r.
}
f_equal.
rewrite Z.mul_comm, Hadbc.
apply Z.mul_comm.
Qed.

Require Import Psatz.

(* I don't understand why the proof of that is so complicated *)
Theorem qeq_eq : ∀ q1 q2,
  Z.gcd (Qnum q1) (QDen q1) = 1%Z
  → Z.gcd (Qnum q2) (QDen q2) = 1%Z
  → q1 == q2
  → q1 = q2.
Proof.
intros * Hq1 Hq2 Hq.
progress unfold "==" in Hq.
destruct (Z.eq_dec (Qnum q1) 0) as [Hqz1| Hqz1]. {
  rewrite Hqz1 in Hq1; cbn in Hq1.
  rewrite Hqz1, Z.mul_0_l in Hq.
  symmetry in Hq.
  apply Z.mul_eq_0 in Hq.
  destruct Hq as [Hqz2| Hqz2]; [ | easy ].
  rewrite Hqz2 in Hq2; cbn in Hq2.
  destruct q1 as (qn1, qd1).
  destruct q2 as (qn2, qd2).
  cbn in *.
  subst qn1 qn2.
  apply Pos2Z.inj in Hq1, Hq2.
  now rewrite Hq1, Hq2.
}
assert (H1 : (0 < Qnum q1 * Qnum q2)%Z). {
  destruct (Z_dec' 0 (Qnum q1)) as [[H1| H1]| H1]. {
    rewrite <- (Z.mul_0_l (Qnum q2)).
    apply Z.mul_lt_mono_pos_r; [ | easy ].
    lia.
  } {
    rewrite <- (Z.mul_0_l (Qnum q2)).
    apply Z.mul_lt_mono_neg_r; [ | easy ].
    lia.
  } {
    now symmetry in H1.
  }
}
rewrite (Z.mul_comm (Qnum q2)) in Hq.
specialize (Z_div_gcd_1 (Qnum q1) (QDen q1) (Qnum q2) (QDen q2)) as H2.
specialize (H2 H1 Hq Hq1 Hq2).
destruct q1 as (qn1, qd1).
destruct q2 as (qn2, qd2).
cbn in Hq1, Hq2, Hqz1, H1, H2.
subst qn2.
f_equal.
rewrite (Z.mul_comm (QDen _)) in Hq.
cbn in Hq.
apply Z.mul_reg_l in Hq; [ | easy ].
now apply Pos2Z.inj in Hq.
Qed.

(* I don't understand why the proof of that too is so complicated *)
Theorem qeq_QG_eq : ∀ q1 q2 : QG, q1 = q2 ↔ qg_q q1 == qg_q q2.
Proof.
intros.
split; intros Hq; [ now subst q2 | ].
destruct q1 as (q1, Hq1).
destruct q2 as (q2, Hq2).
cbn in Hq.
move q2 before q1.
apply eq_QG_eq; cbn.
rewrite Z_pos_gcd_Z_gcd in Hq1, Hq2.
rewrite <- Z2Pos.inj_1 in Hq1, Hq2.
apply Z2Pos.inj in Hq1; [ | | easy ]. 2: {
  destruct (Z.eq_dec (Z.gcd (Qnum q1) (QDen q1)) 0) as [H1| H1]. {
    now apply Z.gcd_eq_0 in H1.
  }
  specialize (Z.gcd_nonneg (Qnum q1) (QDen q1)) as H2.
  apply Z.nle_gt.
  intros H3; apply H1.
  now apply Z.le_antisymm.
}
apply Z2Pos.inj in Hq2; [ | | easy ]. 2: {
  destruct (Z.eq_dec (Z.gcd (Qnum q2) (QDen q2)) 0) as [H1| H1]. {
    now apply Z.gcd_eq_0 in H1.
  }
  specialize (Z.gcd_nonneg (Qnum q2) (QDen q2)) as H2.
  apply Z.nle_gt.
  intros H3; apply H1.
  now apply Z.le_antisymm.
}
now apply qeq_eq.
Qed.

Theorem Z_le_0_div_nonneg_r :
  ∀ x y, (0 < y → 0 ≤ x / y ↔ 0 ≤ x)%Z.
Proof.
intros * Hy.
progress unfold Z.div.
specialize (Zdiv.Z_div_mod x y) as H1.
apply Z.lt_gt in Hy.
specialize (H1 Hy).
apply Z.gt_lt in Hy.
remember (Z.div_eucl x y) as qr eqn:Hqr.
symmetry in Hqr.
destruct qr as (q, r); cbn.
destruct H1 as (Hq, Hr).
clear Hqr.
subst x.
split. {
  intros Hq.
  apply Z.add_nonneg_nonneg; [ | easy ].
  apply Z.mul_nonneg_nonneg; [ | easy ].
  now apply Z.lt_le_incl.
} {
  intros Hyqr.
  apply Z.le_sub_le_add_l in Hyqr.
  rewrite Z.sub_0_l in Hyqr.
  rewrite <- Z.mul_opp_r in Hyqr.
  apply Z.nlt_ge.
  intros Hq.
  apply Z.opp_lt_mono in Hq.
  rewrite Z.opp_0 in Hq.
  remember (- q)%Z as x.
  clear q Heqx.
  move x after y.
  move r before y.
  destruct Hr as (Hrz, Hry).
  assert (H1 : (y * x < y)%Z) by now apply (Z.le_lt_trans _ r).
  rewrite <- Z.mul_1_r in H1.
  apply Z.mul_lt_mono_pos_l in H1; [ | easy ].
  destruct x as [| x| x]; [ easy | | easy ].
  now destruct x.
}
Qed.

(* end of should be added in coq library ZArith *)

Theorem Q_num_den_div_gcd :
  ∀ x y,
  x / Z.gcd x (Z.pos y) # Z.to_pos (Z.pos y / Z.gcd x (Z.pos y)) == x # y.
Proof.
intros.
progress unfold "=="; cbn.
remember (Z.pos y) as z.
assert (Hzz : (0 < z)%Z) by now subst z.
clear y Heqz; rename z into y.
rewrite Z2Pos.id. 2: {
  specialize (Z.gcd_divide_r x y) as H1.
  destruct H1 as (k, Hk).
  rewrite Hk at 1.
  rewrite Z.div_mul. 2: {
    intros H.
    apply Z.gcd_eq_0 in H.
    now destruct H; subst.
  }
  destruct k as [| k| k]; [ | easy | ]. {
    now cbn in Hk; subst y.
  } {
    exfalso; apply Z.nle_gt in Hzz; apply Hzz; clear Hzz.
    rewrite Hk; clear Hk.
    specialize (Z.gcd_nonneg x y) as H1.
    now destruct (Z.gcd x y).
  }
}
rewrite Z.mul_comm.
rewrite <- Z.divide_div_mul_exact; cycle 1. {
  intros H.
  apply Z.gcd_eq_0 in H.
  now destruct H; subst.
} {
  apply Z.gcd_divide_l.
}
rewrite <- Z.divide_div_mul_exact; cycle 1. {
  intros H.
  apply Z.gcd_eq_0 in H.
  now destruct H; subst.
} {
  apply Z.gcd_divide_r.
}
now rewrite Z.mul_comm.
Qed.

Global Instance GQ_of_eq_morph : Proper (Qeq ==> eq) QG_of_Q.
Proof.
intros (xn, xd) (yn, yd) Hxy.
apply eq_QG_eq; cbn.
f_equal. {
  progress unfold Z_pos_gcd.
  destruct xn as [| xn| xn]; [ now destruct yn | | ]. {
    destruct yn as [| yn| yn]; [ easy | | easy ].
    progress unfold Qeq in Hxy.
    cbn in Hxy.
    do 2 rewrite Pos2Z.inj_mul in Hxy.
    symmetry in Hxy; rewrite Z.mul_comm in Hxy.
    symmetry in Hxy.
    do 2 rewrite Pos2Z.inj_gcd.
    now apply Z_div_gcd.
  } {
    destruct yn as [| yn| yn]; [ easy | easy | ].
    progress unfold Qeq in Hxy.
    cbn in Hxy.
    injection Hxy; clear Hxy; intros Hxy.
    apply (f_equal Z.pos) in Hxy.
    do 2 rewrite Pos2Z.inj_mul in Hxy.
    symmetry in Hxy; rewrite Z.mul_comm in Hxy.
    symmetry in Hxy.
    do 2 rewrite Pos2Z.inj_gcd.
    do 2 rewrite <- Pos2Z.opp_pos.
    rewrite Z.div_opp_l_z; [ | easy | ]. 2: {
      apply Z.mod_divide; [ easy | ].
      apply Z.gcd_divide_l.
    }
    rewrite Z.div_opp_l_z; [ | easy | ]. 2: {
      apply Z.mod_divide; [ easy | ].
      apply Z.gcd_divide_l.
    }
    f_equal.
    now apply Z_div_gcd.
  }
} {
  progress unfold "==" in Hxy.
  cbn in Hxy.
  f_equal.
  progress unfold Z_pos_gcd.
  destruct xn as [| xn| xn]; cbn. {
    destruct yn as [| yn| yn]; cbn; [ | easy | easy ].
    rewrite Z.div_same; [ | easy ].
    rewrite Z.div_same; [ | easy ].
    easy.
  } {
    destruct yn as [| yn| yn]; cbn; [ easy | | easy ].
    do 2 rewrite Pos2Z.inj_gcd.
    rewrite Z.gcd_comm.
    rewrite (Z.gcd_comm (Z.pos yn)).
    symmetry in Hxy.
    rewrite Z.mul_comm in Hxy.
    now apply Z_div_gcd.
  } {
    destruct yn as [| yn| yn]; cbn; [ easy | easy | ].
    do 2 rewrite <- Pos2Z.opp_pos in Hxy.
    do 2 rewrite Z.mul_opp_l in Hxy.
    injection Hxy; clear Hxy; intros Hxy.
    apply (f_equal Z.pos) in Hxy.
    do 2 rewrite Pos2Z.inj_mul in Hxy.
    do 2 rewrite Pos2Z.inj_gcd.
    rewrite Z.gcd_comm.
    rewrite (Z.gcd_comm (Z.pos yn)).
    symmetry in Hxy.
    rewrite Z.mul_comm in Hxy.
    now apply Z_div_gcd.
  }
}
Qed.

Theorem QG_eq_dec : ∀ q1 q2 : QG, {q1 = q2} + {q1 ≠ q2}.
Proof.
intros (q1, Hq1) (q2, Hq2).
move q2 before q1.
specialize (Qeq_dec q1 q2) as H1.
destruct H1 as [H1| H1]; [ left | right ]. {
  apply eq_QG_eq; cbn.
  apply qeq_eq; [ | | easy ]. {
    unfold Z_pos_gcd in Hq1.
    destruct (Qnum q1) as [| n| n]. {
      now rewrite Hq1.
    } {
      now apply (f_equal Z.pos) in Hq1.
    } {
      now apply (f_equal Z.pos) in Hq1.
    }
  } {
    unfold Z_pos_gcd in Hq2.
    destruct (Qnum q2) as [| n| n]. {
      now rewrite Hq2.
    } {
      now apply (f_equal Z.pos) in Hq2.
    } {
      now apply (f_equal Z.pos) in Hq2.
    }
  }
}
intros H2.
apply H1; clear H1.
now injection H2; clear H2; intros; subst q2.
Qed.

Theorem QG_of_Q_opp : ∀ a, QG_of_Q (- a) = (- QG_of_Q a)%QG.
Proof.
intros.
unfold QG_opp.
destruct a as (an, ad); cbn.
destruct an as [| an| an]. {
  unfold Qopp; cbn.
  rewrite QG_of_Q_0; symmetry.
  now rewrite QG_of_Q_0.
} {
  cbn.
  rewrite Pos2Z.inj_gcd.
  now rewrite Q_num_den_div_gcd.
} {
  cbn.
  rewrite Pos2Z.inj_gcd.
  rewrite <- Z.gcd_opp_l.
  now rewrite Q_num_den_div_gcd.
}
Qed.

Theorem QG_of_Q_add_idemp_l :
  ∀ a b, QG_of_Q (qg_q (QG_of_Q a) + b) = QG_of_Q (a + b).
Proof.
intros; cbn.
destruct a as (an, ad).
destruct b as (bn, bd).
cbn.
progress unfold Z_pos_gcd.
destruct an as [| an| an]; cbn. {
  rewrite Z.div_same; [ cbn | easy ].
  rewrite Qplus_0_l.
  progress unfold "+"%Q; cbn.
  rewrite Z.mul_comm.
  now rewrite Qreduce_l.
} {
  rewrite Pos2Z.inj_gcd.
  now rewrite Q_num_den_div_gcd.
} {
  rewrite Pos2Z.inj_gcd.
  rewrite <- Z.gcd_opp_l.
  now rewrite Q_num_den_div_gcd.
}
Qed.

Theorem QG_of_Q_add_idemp_r :
  ∀ a b, QG_of_Q (a + qg_q (QG_of_Q b)) = QG_of_Q (a + b).
intros.
rewrite Qplus_comm.
rewrite (Qplus_comm a).
apply QG_of_Q_add_idemp_l.
Qed.

Theorem QG_of_Q_mul_idemp_l :
  ∀ a b, QG_of_Q (qg_q (QG_of_Q a) * b) = QG_of_Q (a * b).
Proof.
intros.
intros; cbn.
destruct a as (an, ad).
destruct b as (bn, bd).
cbn.
progress unfold Z_pos_gcd.
destruct an as [| an| an]; cbn. {
  rewrite Z.div_same; [ cbn | easy ].
  rewrite Qmult_0_l.
  progress unfold "*"%Q; cbn.
  symmetry.
  now rewrite Qreduce_zero.
} {
  rewrite Pos2Z.inj_gcd.
  now rewrite Q_num_den_div_gcd.
} {
  rewrite Pos2Z.inj_gcd.
  rewrite <- Z.gcd_opp_l.
  now rewrite Q_num_den_div_gcd.
}
Qed.

Theorem QG_of_Q_mul_idemp_r :
  ∀ a b, QG_of_Q (a * qg_q (QG_of_Q b)) = QG_of_Q (a * b).
intros.
rewrite Qmult_comm.
rewrite (Qmult_comm a).
apply QG_of_Q_mul_idemp_l.
Qed.

Theorem QG_of_Q_qg_q : ∀ a, QG_of_Q (qg_q a) = a.
Proof.
intros.
apply eq_QG_eq.
destruct a as (a, ap); cbn.
rewrite ap.
do 2 rewrite Z.div_1_r.
now destruct a.
Qed.

(* *)

Theorem QG_add_comm : ∀ a b : QG, (a + b)%QG = (b + a)%QG.
Proof.
intros.
progress unfold QG_add.
now rewrite Qplus_comm.
Qed.

Theorem QG_add_assoc : ∀ a b c : QG, (a + (b + c))%QG = (a + b + c)%QG.
Proof.
intros.
progress unfold QG_add.
rewrite QG_of_Q_add_idemp_r.
rewrite QG_of_Q_add_idemp_l.
now rewrite Qplus_assoc.
Qed.

Theorem QG_add_0_l : ∀ a : QG, (0 + a)%QG = a.
Proof.
intros.
progress unfold QG_add.
rewrite Qplus_0_l.
apply QG_of_Q_qg_q.
Qed.

Theorem QG_add_0_r : ∀ a : QG, (a + 0)%QG = a.
Proof.
intros.
rewrite QG_add_comm.
apply QG_add_0_l.
Qed.

Theorem QG_add_opp_l : ∀ a : QG, (- a + a)%QG = 0%QG.
Proof.
intros.
progress unfold QG_add, QG_opp.
rewrite Qplus_comm.
rewrite QG_of_Q_add_idemp_r.
now rewrite Qplus_opp_r.
Qed.

Theorem QG_add_opp_r : ∀ a : QG, (a + - a)%QG = 0%QG.
Proof.
intros.
rewrite QG_add_comm.
apply QG_add_opp_l.
Qed.

Theorem QG_mul_comm : ∀ a b : QG, (a * b)%QG = (b * a)%QG.
Proof.
intros.
progress unfold QG_mul.
now rewrite Qmult_comm.
Qed.

Theorem QG_mul_assoc : ∀ a b c : QG, (a * (b * c))%QG = (a * b * c)%QG.
Proof.
intros.
progress unfold QG_mul.
rewrite QG_of_Q_mul_idemp_r.
rewrite QG_of_Q_mul_idemp_l.
now rewrite Qmult_assoc.
Qed.

Theorem QG_mul_1_l : ∀ a : QG, (1 * a)%QG = a.
Proof.
intros.
progress unfold QG_mul.
rewrite Qmult_1_l.
apply QG_of_Q_qg_q.
Qed.

Theorem QG_mul_inv_l : ∀ a : QG, a ≠ 0%QG → (a⁻¹ * a)%QG = 1%QG.
Proof.
intros * Haz.
progress unfold QG_mul.
progress unfold QG_inv.
rewrite Qmult_comm.
rewrite QG_of_Q_mul_idemp_r.
rewrite Qmult_inv_r; [ easy | ].
intros H1.
apply Haz; clear Haz.
rewrite <- (QG_of_Q_qg_q a).
rewrite <- QG_of_Q_qg_q.
now rewrite H1.
Qed.

Theorem QG_mul_add_distr_l :  ∀ a b c, (a * (b + c))%QG = (a * b + a * c)%QG.
Proof.
intros.
progress unfold QG_mul.
progress unfold QG_add.
rewrite QG_of_Q_mul_idemp_r.
rewrite QG_of_Q_add_idemp_l.
rewrite QG_of_Q_add_idemp_r.
now rewrite Qmult_plus_distr_r.
Qed.

Theorem QG_mul_add_distr_r :  ∀ a b c, ((a + b) * c)%QG = (a * c + b * c)%QG.
Proof.
intros.
do 3 rewrite (QG_mul_comm _ c).
apply QG_mul_add_distr_l.
Qed.

Theorem QG_eqb_eq : ∀ a b : QG, (a =? b)%QG = true ↔ a = b.
Proof.
intros.
split; intros Hab. {
  apply Qeq_bool_iff in Hab.
  rewrite <- (QG_of_Q_qg_q a).
  rewrite <- (QG_of_Q_qg_q b).
  now rewrite Hab.
} {
  subst b.
  now apply Qeq_bool_iff.
}
Qed.

Theorem QG_le_dec : ∀ a b : QG, {(a ≤ b)%QG} + {¬ (a ≤ b)%QG}.
Proof.
intros.
unfold QG_le.
apply Bool.bool_dec.
Qed.

Theorem QG_le_refl : ∀ a : QG, (a ≤ a)%QG.
Proof.
intros.
apply Qle_bool_iff.
apply Qle_refl.
Qed.

Theorem QG_le_antisymm : ∀ a b : QG, (a ≤ b → b ≤ a → a = b)%QG.
Proof.
intros * Hab Hba.
apply Qle_bool_iff in Hab, Hba.
apply Qle_antisym in Hab; [ | easy ].
rewrite <- QG_of_Q_qg_q.
rewrite <- (QG_of_Q_qg_q a).
now rewrite Hab.
Qed.

Theorem QG_le_trans : ∀ x y z : QG, (x ≤ y → y ≤ z → x ≤ z)%QG.
Proof.
intros * Hxy Hyz.
apply Qle_bool_iff in Hxy, Hyz.
apply Qle_bool_iff.
now apply (Qle_trans _ (qg_q y)).
Qed.

Theorem QG_le_0_sub : ∀ x y : QG, (0 ≤ y - x)%QG ↔ (x ≤ y)%QG.
Proof.
intros.
split; intros Hxy. {
  destruct x as (x, xp).
  destruct y as (y, yp).
  cbn.
  cbn in Hxy.
  progress unfold QG_sub in Hxy.
  progress unfold QG_opp in Hxy.
  cbn in Hxy.
  progress unfold QG_add in Hxy.
  apply Qle_bool_iff; cbn.
  cbn - [ QG_of_Q ] in Hxy.
  rewrite QG_of_Q_add_idemp_r in Hxy.
  apply Qle_minus_iff.
  remember (y + - x) as yx eqn:Hyx.
  clear - Hxy.
  rename yx into x; rename Hxy into Hx.
  apply Qle_bool_iff in Hx.
  remember (qg_q 0%QG) as y.
  cbn in Heqy; subst y.
  progress unfold Qle in Hx |-*.
  cbn in Hx |-*.
  rewrite Z.mul_1_r in Hx |-*.
  destruct x as (xn, xd).
  cbn in Hx |-*.
  remember (Z_pos_gcd _ _) as y eqn:Hy.
  clear Hy xd.
  rename xn into x; rename y into p.
  now apply Z_le_0_div_nonneg_r in Hx.
} {
  destruct x as (x, xp).
  destruct y as (y, yp).
  progress unfold QG_sub.
  progress unfold QG_opp.
  cbn.
  progress unfold QG_add.
  apply Qle_bool_iff in Hxy; cbn in Hxy.
  cbn - [ QG_of_Q ].
  rewrite QG_of_Q_add_idemp_r.
  apply Qle_minus_iff in Hxy.
  remember (y + - x) as yx eqn:Hyx.
  clear - Hxy.
  rename yx into x; rename Hxy into Hx.
  apply Qle_bool_iff.
  remember (qg_q 0%QG) as y.
  cbn in Heqy; subst y.
  progress unfold Qle in Hx |-*.
  cbn in Hx |-*.
  rewrite Z.mul_1_r in Hx |-*.
  destruct x as (xn, xd).
  cbn in Hx |-*.
  remember (Z_pos_gcd _ _) as y eqn:Hy.
  clear Hy xd.
  rename xn into x; rename y into p.
  now apply Z_le_0_div_nonneg_r.
}
Qed.

Theorem qg_q_opp : ∀ a, qg_q (- a)%QG = - qg_q a.
Proof.
intros.
destruct a as (a, Hap); cbn.
rewrite Z_pos_gcd_opp_l.
rewrite Hap.
now do 2 rewrite Z.div_1_r.
Qed.

Theorem QG_opp_add_distr : ∀ a b, (- (a + b) = - a - b)%QG.
Proof.
intros.
progress unfold QG_sub.
progress unfold QG_opp.
progress unfold QG_add.
rewrite QG_of_Q_opp.
rewrite QG_of_Q_qg_q, QG_of_Q_opp.
rewrite QG_of_Q_qg_q, QG_of_Q_opp.
rewrite QG_of_Q_qg_q.
do 2 rewrite qg_q_opp.
rewrite <- Qopp_plus.
symmetry; apply QG_of_Q_opp.
Qed.

Theorem fold_QG_sub : ∀ a b, (a + - b = a - b)%QG.
Proof. easy. Qed.

Theorem QG_add_le_mono_l : ∀ a b c : QG, (b ≤ c)%QG ↔ (a + b ≤ a + c)%QG.
Proof.
intros.
split; intros Hbc. {
  apply -> QG_le_0_sub.
  rewrite QG_add_comm.
  progress unfold QG_sub.
  rewrite QG_opp_add_distr.
  progress unfold QG_sub.
  rewrite QG_add_assoc.
  rewrite QG_add_comm.
  rewrite <- QG_add_assoc.
  rewrite QG_add_opp_r.
  rewrite QG_add_0_r.
  rewrite QG_add_comm.
  now apply QG_le_0_sub.
} {
  apply QG_le_0_sub in Hbc.
  rewrite QG_add_comm in Hbc.
  progress unfold QG_sub in Hbc.
  rewrite QG_opp_add_distr in Hbc.
  progress unfold QG_sub in Hbc.
  rewrite QG_add_assoc in Hbc.
  rewrite QG_add_comm in Hbc.
  rewrite <- QG_add_assoc in Hbc.
  rewrite QG_add_opp_r in Hbc.
  rewrite QG_add_0_r in Hbc.
  rewrite QG_add_comm in Hbc.
  now apply -> QG_le_0_sub in Hbc.
}
Qed.

Theorem QG_add_le_mono_r : ∀ a b c : QG, (a ≤ b)%QG ↔ (a + c ≤ b + c)%QG.
Proof.
intros.
do 2 rewrite (QG_add_comm _ c).
apply QG_add_le_mono_l.
Qed.

Theorem QG_add_le_compat : ∀ a b c d : QG, (a ≤ b → c ≤ d → a + c ≤ b + d)%QG.
Proof.
intros * Hab Hcd.
apply QG_le_trans with (y := (b + c)%QG). {
  now apply QG_add_le_mono_r.
} {
  now apply QG_add_le_mono_l.
}
Qed.

Theorem QG_opp_involutive: ∀ a : QG, (- - a)%QG = a.
Proof.
intros.
progress unfold QG_opp.
rewrite (QG_of_Q_opp (qg_q a)).
rewrite qg_q_opp.
rewrite Qopp_opp.
now do 2 rewrite QG_of_Q_qg_q.
Qed.

Theorem Z_pos_pos_gcd : ∀ a b, Z.pos (Z_pos_gcd a b) = Z.gcd a (Z.pos b).
Proof.
intros.
unfold Z_pos_gcd.
now destruct a.
Qed.

Theorem qg_q_add : ∀ a b, qg_q (a + b) == qg_q a + qg_q b.
Proof.
intros.
destruct a as (a, Ha).
destruct b as (b, Hb).
move b before a.
progress unfold "==".
cbn.
assert (Han : ∀ an ad bn bd,
  ((Z.pos an * Z.pos bd + bn * Z.pos ad) /
   Z.pos (Z_pos_gcd (Z.pos an * Z.pos bd + bn * Z.pos ad) (ad * bd)) *
   Z.pos (ad * bd))%Z =
  ((Z.pos an * Z.pos bd + bn * Z.pos ad) *
   Z.pos
     (Z.to_pos
        (Z.pos (ad * bd) /
         Z.pos
           (Z_pos_gcd (Z.pos an * Z.pos bd + bn * Z.pos ad)
              (ad * bd)))))%Z). {
  clear.
  intros.
  rewrite Z2Pos.id. 2: {
    apply Z.div_str_pos.
    split; [ easy | ].
    apply Pos2Z.pos_le_pos.
    progress unfold Z_pos_gcd.
    remember (_ + _)%Z as x.
    destruct x as [| x| x]; [ apply Pos.le_refl | | ]. {
      apply Pos_gcd_le_r.
    } {
      apply Pos_gcd_le_r.
    }
  }
  remember (_ + _)%Z as x.
  rewrite Z_pos_pos_gcd.
  rewrite Z.lcm_equiv2; [ | now rewrite <- Z_pos_pos_gcd ].
  rewrite Z.lcm_equiv1; [ easy | ].
  now rewrite <- Z_pos_pos_gcd.
}
destruct a as (an, ad).
destruct b as (bn, bd); cbn in Ha, Hb |-*.
destruct an as [| an| an]; [ | | ]. {
  cbn in Ha; subst ad.
  rewrite Z.mul_0_l, Z.mul_1_r.
  rewrite Z.add_0_l, Pos.mul_1_l.
  rewrite Hb.
  do 2 rewrite Z.div_1_r.
  now rewrite Pos2Z.id.
} {
  apply Han.
} {
  rewrite <- Pos2Z.opp_pos.
  rewrite <- (Z.opp_involutive bn).
  remember (- bn)%Z as bn'.
  do 2 rewrite Z.mul_opp_l.
  rewrite <- Z.opp_add_distr.
  rewrite Z_pos_gcd_opp_l.
  rewrite Z.div_opp_l_z; [ | easy | ]. 2: {
    apply Z.mod_divide; [ easy | ].
    progress unfold Z_pos_gcd.
    remember (_ + _)%Z as x.
    destruct x as [| x| x]; [ apply Z.divide_0_r | | ]. {
      rewrite Pos2Z.inj_gcd.
      apply Z.gcd_divide_l.
    } {
      rewrite Pos2Z.inj_gcd.
      apply Z.divide_opp_r.
      rewrite Pos2Z.opp_neg.
      apply Z.gcd_divide_l.
    }
  }
  do 2 rewrite Z.mul_opp_l.
  f_equal.
  apply Han.
}
Qed.

Theorem qg_q_mul : ∀ a b, qg_q (a * b) == qg_q a * qg_q b.
Proof.
intros.
destruct a as (a, Ha).
destruct b as (b, Hb).
move b before a.
progress unfold "==".
cbn.
clear Ha Hb.
destruct a as (an, ad).
destruct b as (bn, bd); cbn.
assert (Han : ∀ an,
  (Z.pos an * bn / Z.pos (Z_pos_gcd (Z.pos an * bn) (ad * bd)) *
     Z.pos (ad * bd))%Z =
  (Z.pos an * bn *
     Z.pos
       (Z.to_pos
          (Z.pos (ad * bd) /
           Z.pos (Z_pos_gcd (Z.pos an * bn) (ad * bd)))))%Z). {
  clear an; intros.
  assert (Hbn : ∀ bn,
    (Z.pos (an * bn) / Z.pos (Pos.gcd (an * bn) (ad * bd)) *
       Z.pos (ad * bd))%Z =
    Z.pos
      (an * bn *
       Z.to_pos
         (Z.pos (ad * bd) / Z.pos (Pos.gcd (an * bn) (ad * bd))))). {
    clear bn; intros.
    rewrite Pos2Z.inj_gcd.
    rewrite Z.gcd_div_swap.
    rewrite Z.lcm_equiv1; [ | now rewrite <- Pos2Z.inj_gcd ].
    remember (an * bn)%positive as abn.
    remember (ad * bd)%positive as abd.
    rewrite Pos2Z.inj_mul.
    subst abn abd.
    rewrite Z2Pos.id. 2: {
      apply Z.div_str_pos.
      rewrite <- Pos2Z.inj_gcd.
      split; [ easy | ].
      apply Pos2Z.pos_le_pos.
      apply Pos_gcd_le_r.
    }
    apply Z.divide_div_mul_exact; [ | apply Z.gcd_divide_r ].
    now intros H; apply Z.gcd_eq_0_l in H.
  }
  destruct bn as [| bn| bn]; [ easy | apply Hbn | ].
  cbn.
  do 2 rewrite <- Pos2Z.opp_pos.
  rewrite Z.div_opp_l_z; [ | easy | ]. 2: {
    rewrite Pos2Z.inj_gcd.
    apply Z.mod_divide; [ now intros H; apply Z.gcd_eq_0_l in H | ].
    apply Z.gcd_divide_l.
  }
  rewrite Z.mul_opp_l.
  f_equal.
  apply Hbn.
}
destruct an as [| an| an]; [ easy | apply Han | ].
rewrite <- Pos2Z.opp_pos.
rewrite Z.mul_opp_l.
rewrite Z_pos_gcd_opp_l.
rewrite Z.div_opp_l_z; [ | easy | ]. 2: {
  remember (Z.pos an * bn)%Z as x.
  progress unfold Z_pos_gcd.
  destruct x as [| x| x]; [ easy | | ]. {
    rewrite Pos2Z.inj_gcd.
    apply Z.mod_divide; [ now intros H; apply Z.gcd_eq_0_l in H | ].
    apply Z.gcd_divide_l.
  } {
    rewrite <- Pos2Z.opp_pos.
    apply Z.mod_opp_l_z; [ easy | ].
    rewrite Pos2Z.inj_gcd.
    apply Z.mod_divide; [ now intros H; apply Z.gcd_eq_0_l in H | ].
    apply Z.gcd_divide_l.
  }
}
do 2 rewrite Z.mul_opp_l.
f_equal.
apply Han.
Qed.

Theorem QG_of_Q_qg_q_mul :
  ∀ a b : QG, QG_of_Q (qg_q a * qg_q b) = (a * b)%QG.
Proof.
intros.
rewrite <- QG_of_Q_qg_q.
rewrite qg_q_mul.
now rewrite <- QG_of_Q_mul_idemp_l.
Qed.

Theorem Q_mul_opp_l : ∀ n m : Q, (- n * m)%Q == (- (n * m))%Q.
Proof.
intros.
progress unfold "=="%Q; cbn.
f_equal.
apply Z.mul_opp_l.
Qed.

Theorem QG_mul_opp_l : ∀ a b : QG, (- a * b = - (a * b))%QG.
Proof.
intros.
rewrite <- QG_of_Q_qg_q; symmetry.
rewrite <- QG_of_Q_qg_q; symmetry.
rewrite <- QG_of_Q_qg_q_mul.
rewrite <- QG_of_Q_qg_q_mul.
rewrite <- QG_of_Q_opp.
rewrite QG_of_Q_qg_q.
rewrite QG_of_Q_qg_q.
rewrite qg_q_opp.
now rewrite Q_mul_opp_l.
Qed.

Theorem QG_mul_opp_r : ∀ a b : QG, (a * - b = - (a * b))%QG.
Proof.
intros.
do 2 rewrite (QG_mul_comm a).
apply QG_mul_opp_l.
Qed.

Theorem QG_mul_sub_distr_l :  ∀ a b c, (a * (b - c))%QG = (a * b - a * c)%QG.
Proof.
intros.
progress unfold QG_sub.
rewrite QG_mul_add_distr_l.
f_equal.
apply QG_mul_opp_r.
Qed.

Theorem QG_mul_sub_distr_r :  ∀ a b c, ((a - b) * c)%QG = (a * c - b * c)%QG.
Proof.
intros.
do 3 rewrite (QG_mul_comm _ c).
apply QG_mul_sub_distr_l.
Qed.

Theorem QG_mul_nonneg_nonneg : ∀ a b : QG, (0 ≤ a → 0 ≤ b → 0 ≤ a * b)%QG.
Proof.
intros * Ha Hb.
apply Qle_bool_iff in Ha, Hb.
apply Qle_bool_iff.
cbn in Ha, Hb.
cbn - [ QG_mul ].
rewrite qg_q_mul.
now apply Qmult_le_0_compat.
Qed.

Theorem QG_mul_le_compat_nonneg :
  ∀ a b c d : QG, (0 ≤ a ≤ c → 0 ≤ b ≤ d → a * b ≤ c * d)%QG.
Proof.
intros * Hac Hbd.
apply QG_le_trans with (y := (c * b)%QG). {
  apply QG_le_0_sub.
  rewrite <- QG_mul_sub_distr_r.
  apply QG_mul_nonneg_nonneg; [ now apply QG_le_0_sub | easy ].
} {
  apply QG_le_0_sub.
  rewrite <- QG_mul_sub_distr_l.
  apply QG_mul_nonneg_nonneg; [ | now apply QG_le_0_sub ].
  eapply QG_le_trans; [ apply Hac | easy ].
}
Qed.

Theorem QG_opp_le_mono: ∀ a b : QG, (a ≤ b ↔ - b ≤ - a)%QG.
Proof.
intros.
split; intros Hab. {
  apply QG_le_0_sub.
  progress unfold QG_sub.
  rewrite QG_opp_involutive.
  rewrite QG_add_comm.
  rewrite fold_QG_sub.
  now apply <- QG_le_0_sub.
} {
  apply QG_le_0_sub in Hab.
  progress unfold QG_sub in Hab.
  rewrite QG_opp_involutive in Hab.
  rewrite QG_add_comm in Hab.
  rewrite fold_QG_sub in Hab.
  now apply -> QG_le_0_sub in Hab.
}
Qed.

Theorem QG_mul_le_compat_nonpos :
  ∀ a b c d : QG, (c ≤ a ≤ 0 → d ≤ b ≤ 0 → a * b ≤ c * d)%QG.
Proof.
intros * Hac Hbd.
assert (Hle : ∀ a b c, (c ≤ a ≤ 0 → b ≤ 0 → a * b ≤ c * b)%QG). {
  clear.
  intros * Hac Hbz.
  rewrite <- (QG_opp_involutive a).
  rewrite QG_mul_opp_l.
  rewrite <- (QG_opp_involutive c).
  rewrite (QG_mul_opp_l (- c))%QG.
  rewrite <- (QG_opp_involutive b).
  do 2 rewrite (QG_mul_opp_r _ (- b))%QG.
  do 2 rewrite QG_opp_involutive.
  apply QG_mul_le_compat_nonneg. {
    split. {
      apply QG_opp_le_mono.
      now rewrite QG_opp_involutive.
    } {
      now apply -> QG_opp_le_mono.
    }
  }
  split; [ | apply QG_le_refl ].
  apply QG_opp_le_mono.
  now rewrite QG_opp_involutive.
}
apply QG_le_trans with (y := (c * b)%QG). {
  now apply Hle.
} {
  do 2 rewrite (QG_mul_comm c).
  assert (Hcz : (c ≤ 0)%QG) by now apply QG_le_trans with (y := a).
  destruct Hac as (Hca, Haz).
  now apply Hle.
}
Qed.

Theorem QG_not_le : ∀ a b : QG, (¬ (a ≤ b) → a ≠ b ∧ b ≤ a)%QG.
Proof.
intros * Hab.
split. {
  intros H1; apply Hab; clear Hab; subst b.
  apply QG_le_refl.
}
apply Qle_bool_iff.
apply Qnot_lt_le.
intros H1.
apply Hab; clear Hab.
apply Qle_bool_iff.
now apply Qlt_le_weak.
Qed.

Theorem nat_of_inv_Q :
  ∀ n d,
  (Pos.to_nat d / Z.to_nat n =
     Z.to_nat (Qnum (/ (n # d))) / Pos.to_nat (Qden (/ (n # d))))%nat.
Proof.
intros.
destruct n as [| n| n]; [ easy | easy | cbn ].
symmetry; apply Nat.div_0_l.
apply Nat.neq_0_lt_0.
apply Pos2Nat.is_pos.
Qed.

Theorem QG_add_sub : ∀ a b, (a + b - b)%QG = a.
Proof.
intros.
progress unfold QG_sub.
rewrite <- QG_add_assoc, QG_add_comm.
rewrite QG_add_opp_r.
apply QG_add_0_l.
Qed.

Theorem QG_characteristic_prop :
  ∀ i, List.fold_right QG_add 0%QG (List.repeat 1%QG (S i)) ≠ 0%QG.
Proof.
intros * H1.
assert (Hle : ∀ i, (0 ≤ List.fold_right QG_add 0 (List.repeat 1 i))%QG). {
  clear i H1; intros.
  induction i; cbn; [ easy | ].
  eapply QG_le_trans; [ apply IHi | ].
  apply QG_le_0_sub.
  now rewrite QG_add_sub.
}
specialize (Hle i).
apply (QG_add_le_mono_l 1%QG) in Hle.
rewrite QG_add_0_r in Hle.
cbn in H1.
now rewrite H1 in Hle.
Qed.

Theorem qg_q_mul_nat :
  ∀ a n,
  qg_q (List.fold_right QG_add 0%QG (List.repeat a n)) ==
  List.fold_right Qplus 0 (List.repeat (qg_q a) n).
Proof.
intros.
induction n; [ easy | ].
cbn - [ QG_add ].
rewrite qg_q_add.
now rewrite IHn.
Qed.

Theorem Q_mul_nat : ∀ a n,
  List.fold_right Qplus 0 (List.repeat a n) == a * (Z.of_nat n # 1).
Proof.
intros.
induction n; cbn; [ symmetry; apply Qmult_0_r | ].
rewrite IHn; clear IHn.
progress unfold "==".
cbn.
rewrite Pos.mul_1_r.
rewrite Pos2Z.inj_mul.
do 2 rewrite <- Z.mul_assoc.
rewrite <- Z.mul_add_distr_l.
rewrite <- Z.mul_assoc.
f_equal.
rewrite Z.mul_assoc.
f_equal.
rewrite <- (Z.mul_1_l (QDen a)) at 1.
rewrite <- Z.mul_add_distr_r.
f_equal.
rewrite Zpos_P_of_succ_nat.
apply Z.add_comm.
Qed.

Theorem QG_archimedean :
  ∀ a b : QG, (0 < a < b)%QG →
  ∃ n : nat,
  (b < List.fold_right QG_add 0 (List.repeat a n))%QG.
Proof.
intros * Hab *.
destruct a as ((an, ad), Hap).
destruct b as ((bn, bd), Hbp).
cbn in Hap, Hbp.
destruct Hab as (Ha, Hab).
exists
  ((Z.to_nat bn * Pos.to_nat ad) / (Z.to_nat an * Pos.to_nat bd + 1) + 1)%nat.
apply not_true_iff_false in Hab.
apply not_true_iff_false.
intros H1; apply Hab; clear Hab.
apply Qle_bool_iff in H1.
apply Qle_bool_iff.
apply Qnot_lt_le.
apply Qle_not_lt in H1.
cbn.
intros Hε; apply H1; clear H1.
rewrite qg_q_mul_nat; cbn.
rewrite Q_mul_nat.
progress unfold Qlt.
cbn.
rewrite Pos.mul_1_r.
destruct an as [| an| an]; [ easy | | easy ].
...
destruct εn as [| εn| εn]; [ easy | | easy ].
cbn - [ Z.mul ].
rewrite Nat2Z.inj_add.
cbn - [ Z.mul ].
rewrite Nat2Z.inj_mul.
rewrite Z.mul_add_distr_l.
rewrite Z.mul_1_r.
rewrite Z.mul_assoc.
rewrite (Z.mul_comm (Z.pos εn)).
rewrite <- Z.mul_assoc.
remember (Z.pos εn * _)%Z as x.
apply Z.le_lt_trans with (m := (Z.of_nat n * x)%Z). 2: {
  now apply Z.lt_add_pos_r.
}
apply Z.mul_le_mono_nonneg_l; [ apply Nat2Z.is_nonneg | ].
subst x.
rewrite Nat2Z.inj_add.
cbn - [ Z.mul ].
rewrite Z.mul_add_distr_l.
rewrite Z.mul_1_r.
rewrite Nat2Z.inj_div.
do 2 rewrite positive_nat_Z.
rewrite (Z.div_mod (Z.pos εd) (Z.pos εn)) at 1; [ | easy ].
apply Z.add_le_mono_l.
apply Z.lt_le_incl.
now apply Z.mod_pos_bound.
Qed.
*)

(* *)

Require Import Main.RingLike.

Definition QG_ring_like_op : ring_like_op QG :=
  {| rngl_zero := 0%QG;
     rngl_add := QG_add;
     rngl_mul := QG_mul;
     rngl_opt_one := Some 1%QG;
     rngl_opt_opp_or_subt := Some (inl QG_opp);
     rngl_opt_inv_or_quot := Some (inl QG_inv);
     rngl_opt_eq_dec := Some QG_eq_dec;
     rngl_opt_leb := Some QG_leb |}.

Definition QG_ring_like_prop (ro := QG_ring_like_op) : ring_like_prop QG :=
  {| rngl_mul_is_comm := true;
     rngl_is_integral_domain := false;
     rngl_is_archimedean := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := QG_add_comm;
     rngl_add_assoc := QG_add_assoc;
     rngl_add_0_l := QG_add_0_l;
     rngl_mul_assoc := QG_mul_assoc;
     rngl_opt_mul_1_l := QG_mul_1_l;
     rngl_mul_add_distr_l := QG_mul_add_distr_l;
     rngl_opt_mul_comm := QG_mul_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_l := QG_add_opp_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_mul_inv_l := QG_mul_inv_l;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_le_dec := QG_le_dec;
     rngl_opt_integral := NA;
     rngl_opt_alg_closed := NA;
     rngl_characteristic_prop := QG_characteristic_prop;
     rngl_opt_le_refl := QG_le_refl;
     rngl_opt_le_antisymm := QG_le_antisymm;
     rngl_opt_le_trans := QG_le_trans;
     rngl_opt_add_le_compat := QG_add_le_compat;
     rngl_opt_mul_le_compat_nonneg := QG_mul_le_compat_nonneg;
     rngl_opt_mul_le_compat_nonpos := QG_mul_le_compat_nonpos;
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := QG_not_le;
     rngl_opt_archimedean := QG_archimedean |}.
