(* Attempt to implement rationals with the normal rationals of
   coq (library QArith) together with a field saying that the
   numerator and the denominator are coprimes. This allows to
   use normal equality instead of ==. Therefore rewrite is
   possible. *)

Set Nested Proofs Allowed.
Set Implicit Arguments.
Require Import Utf8.

Require Import QArith.

Definition Z_pos_gcd z p :=
  match z with
  | Z0 => p
  | Zpos zp => Pos.gcd zp p
  | Zneg zp => Pos.gcd zp p
  end.

Record QG := mk_qg
  {qg_q : Q; qg_gcd : Z_pos_gcd (Qnum qg_q) (Qden qg_q) = 1%positive}.

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
destruct (Nat.eq_dec (Nat.gcd a b) 0) as [Habz| Habz]. {
  congruence.
}
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
unfold Pos.gcd.
remember (Pos.size_nat x + Pos.size_nat y)%nat as n eqn:Hn.
assert (H : (Pos.size_nat x + Pos.size_nat y ≤ n)%nat). {
  now rewrite Hn; apply Nat.le_refl.
}
clear Hn; rename H into Hn.
revert x y Hn.
induction n; intros; cbn; [ now destruct x | ].
assert (Hgp : ∀ x y,
  Pos.size_nat x + S (Pos.size_nat y) ≤ n
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
    destruct xy as [xy| xy| ]. {
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
unfold Z.gcd.
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
  unfold Z_pos_gcd.
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

Definition QG_add (a b : QG) := QG_of_Q (qg_q a + qg_q b).
Definition QG_mul (a b : QG) := QG_of_Q (qg_q a * qg_q b).

Theorem QG_add_comm : ∀ a b, QG_add a b = QG_add b a.
Proof.
intros.
apply eq_QG_eq; cbn.
f_equal. {
  f_equal; [ apply Z.add_comm | ].
  f_equal.
  f_equal; [ apply Z.add_comm | apply Pos.mul_comm ].
} {
  f_equal.
  f_equal; [ f_equal; apply Pos.mul_comm | ].
  f_equal.
  progress unfold Z_pos_gcd.
  rewrite Z.add_comm.
  remember (_ + _)%Z as x.
  destruct x; [ apply Pos.mul_comm | | ]; now rewrite Pos.mul_comm.
}
Qed.

Theorem QG_add_assoc : ∀ a b c, QG_add a (QG_add b c) = QG_add (QG_add a b) c.
Proof.
intros.
apply eq_QG_eq.
unfold QG_add.
Search (QG_of_Q (_ + QG_of_Q _)).
Theorem QG_of_Q_add_idemp_r :
  ∀ a b, QG_of_Q (a + qg_q (QG_of_Q b)) = QG_of_Q (a + b).
Proof.
intros; cbn.
destruct a as (an, ad).
destruct b as (bn, bd).
cbn.
unfold Z_pos_gcd.
destruct bn as [| bn| bn]; cbn. {
  rewrite Z.div_same; [ cbn | easy ].
  rewrite Qplus_0_r.
  progress unfold "+"%Q; cbn.
  rewrite Z.add_0_r.
  now rewrite Qreduce_r.
} {
  rewrite Pos2Z.inj_gcd.
  now rewrite Q_num_den_div_gcd.
} {
  rewrite Pos2Z.inj_gcd.
...
Check Qreduce_r.
Search (_ / _ # _ / _)%Q.
Search (_ # Z.to_pos _).
remember (Z.pos (Pos.gcd bn bd)) as g eqn:Hg.
Search (Z.to_pos (_ / _)).
...
Theorem QG_of_Q_add_idemp_l :
  ∀ a b, QG_of_Q (qg_q (QG_of_Q a) + b) = QG_of_Q (a + b).
Proof.
intros; cbn.
... ...
rewrite QG_of_Q_add_idemp_r.
rewrite QG_of_Q_add_idemp_l.
now rewrite Qplus_assoc.
Qed.

Inspect 1.
... ...
apply glop.
apply Qplus_assoc.
...
remember (Z.pos (Z_pos_gcd _ _)) as XXXXX in |-*.
remember (Z.pos (Z_pos_gcd _ _)) as YYYYY in |-*.
remember (Z.pos (Z_pos_gcd _ _)) as ZZZZZ in |-*.
remember (Z.pos (Z_pos_gcd _ _)) as TTTTT in |-*.
f_equal.
...
remember (Z.pos _) as YYYYY in |-*.
remember (Z.pos _) as ZZZZZ in |-*.
...
f_equal. {
  f_equal. {
...
  f_equal; [ apply Z.add_comm | ].
  f_equal.
  f_equal; [ apply Z.add_comm | apply Pos.mul_comm ].
} {
  f_equal.
  f_equal; [ f_equal; apply Pos.mul_comm | ].
  f_equal.
  progress unfold Z_pos_gcd.
  rewrite Z.add_comm.
  remember (_ + _)%Z as x.
  destruct x; [ apply Pos.mul_comm | | ]; now rewrite Pos.mul_comm.
}
Qed.

...
