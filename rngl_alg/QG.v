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

(* end of should be added in coq library ZArith *)

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
    do 2 rewrite Pos2Z.inj_gcd.
(*
remember (Z.pos xn) as a.
remember (Z.pos xd) as b.
remember (Z.pos yn) as c.
remember (Z.pos yd) as d.
subst a b c d.
*)
Theorem Nat_div_gcd : ∀ a b c d,
  (a * d = b * c → a / Nat.gcd a b = c / Nat.gcd c d)%nat.
Admitted.
apply (f_equal Z.to_nat) in Hxy.
cbn in Hxy.
do 2 rewrite Pos2Nat.inj_mul in Hxy.
symmetry in Hxy; rewrite Nat.mul_comm in Hxy.
symmetry in Hxy.
specialize Nat_div_gcd as H1.
specialize (H1 _ _ _ _ Hxy).
apply (f_equal Z.of_nat) in H1.
do 2 rewrite Nat2Z.inj_div in H1.
do 2 rewrite positive_nat_Z in H1.
(*
Theorem Pos_of_nat_gcd :
  ∀ a b, a ≠ 0%nat → b ≠ 0%nat →
  Pos.of_nat (Nat.gcd a b) = Pos.gcd (Pos.of_nat a) (Pos.of_nat b).
Proof.
intros * Haz Hbz.
revert b Hbz.
induction a; intros; [ easy | ].
clear Haz.
cbn.
Search Nat.divmod.
...
*)
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
Theorem glop :
  ∀ a b c, Nat.gcd a b = 1%nat → Nat.gcd a c = Nat.gcd a (b * c).
Proof.
intros * Hab.
specialize (Nat.gcd_bezout a (b * c)) as H1.
destruct H1 as [H1| H1]. {
  destruct H1 as (u & v & Huv).
  move u before c; move v before u.
(*
  apply Nat.add_sub_eq_r in Huv.
*)
  remember (Nat.gcd a (b * c)) as d eqn:Hd; symmetry in Hd.
  move d before c.
  rewrite Nat.mul_assoc in Huv.
  specialize (Nat.gcd_bezout a c) as H2.
  destruct H2 as [H2| H2]. {
    destruct H2 as (u' & v' & Huv').
    move u' before v; move v' before u'.
(*
    symmetry in Huv'.
    apply Nat.add_sub_eq_r in Huv'.
*)
    remember (Nat.gcd a c) as e eqn:He; symmetry in He.
    move e before d; move He before Hd.
    apply (f_equal (Nat.mul u')) in Huv.
    apply (f_equal (Nat.mul u)) in Huv'.
    rewrite Nat.mul_add_distr_l in Huv, Huv'.
    do 3 rewrite Nat.mul_assoc in Huv.
    do 2 rewrite Nat.mul_assoc in Huv'.
    rewrite (Nat.mul_comm u') in Huv.
...
intros * Hab.
specialize (Nat_gcd_iff a c) as H1.
specialize (H1 (Nat.gcd a c)).
assert (H : Nat.gcd a c ≠ 0%nat). {
  intros H.
  apply Nat.gcd_eq_0 in H.
  destruct H; subst a c.
  cbn in Hab; subst b.
  _admit.
}
specialize (proj1 (H1 H) eq_refl) as H2; clear H H1.
destruct H2 as (H1 & H2 & H3).
specialize (Nat_gcd_iff a (b * c)) as H4.
specialize (H4 (Nat.gcd a (b * c))).
assert (H : Nat.gcd a (b * c) ≠ 0%nat) by _admit.
specialize (proj1 (H4 H) eq_refl) as H5; clear H H4.
destruct H5 as (H4 & H5 & H6).
unfold Nat.divide in H1, H2, H4, H5.
destruct H1 as (a1, Ha1).
destruct H2 as (c1, Hc1); rewrite Hc1 at 1.
destruct H4 as (a2, Ha2).
destruct H5 as (bc1, Hbc1); rewrite Hbc1.
move a1 before c; move c1 before a1; move a2 before c1; move bc1 before a2.
rewrite Ha1 in H3 at 1.
rewrite Nat.div_mul in H3.
rewrite Hc1 in H3 at 1.
rewrite Nat.div_mul in H3.
rewrite Ha2 in H6 at 1.
rewrite Nat.div_mul in H6.
rewrite Hbc1 in H6 at 1.
rewrite Nat.div_mul in H6.
apply (f_equal (Nat.mul a2)) in Hbc1.
do 2 rewrite Nat.mul_assoc in Hbc1.
rewrite (Nat.mul_shuffle0 _ bc1) in Hbc1.
rewrite <- Ha2 in Hbc1.
move H3 before H6.
move Ha2 before Ha1.
...
rewrite Hc1 in Hbc1 at 1.
...
Nat.divide_mul_split:
  ∀ n m p : nat,
    n ≠ 0%nat
    → Nat.divide n (m * p)
      → ∃ q r : nat, n = (q * r)%nat ∧ Nat.divide q m ∧ Nat.divide r p
...
revert b c Hab.
induction a; intros. {
  now cbn in Hab; subst b; rewrite Nat.mul_1_l.
}
cbn - [ "mod" ].
...
intros * Hab.
revert a c Hab.
induction b; intros. {
  now rewrite Nat.gcd_0_r in Hab; subst a.
}
...
Nat.gcd_add_diag_r: ∀ n m : nat, Nat.gcd n (m + n) = Nat.gcd n m
...
Search Nat.gcd.
Search (Nat.gcd _ (_ + _)%nat).
...
intros * Hab.
specialize (Nat.gcd_bezout a b) as H1.
rewrite Hab in H1.
destruct H1 as [H1| H1]. {
  unfold Nat.Bezout in H1.
  destruct H1 as (d & e & H1).
... ...
symmetry.
rewrite (glop _ _ 2%nat).
Search (Nat.gcd (_ mod _)).
Search (Z.gcd (_ * _)).
Search (_~1)%positive.
gcd (2m+1) (2n+1) =? gcd (m-n) (2n+1)
2m-2n
Search (Pos.to_nat (_ - _)).
replace (y - x)%positive
      rewrite Pos2Nat.inj_sub; [ | easy ].
Search (Nat.gcd _ (_ - _)).
...
  rewrite Pos2Nat.inj_1.
  apply Nat.eq_add_0 in Hn.
  destruct Hn as (Hx, Hy).
  destruct x as [x| x| ]; [ easy | easy | easy ].
Theorem eq_pos_size_nat_0 :
  ∀ x, Pos.size_nat x = 0%nat → x = 1%positive.
Proof.
intros * Hx.
now destruct x.
destruct x as [x| x| ]; [ easy | easy | easy ].
... ...
  now apply eq_pos_size_nat_0 in Hx, Hy; subst x y.
}
...
apply eq_pos_size_nat_0 in Hx.
  revert y Hy.
  induction x as [x| x| ]; intros; [ | easy | easy ].
  destruct y as [y| y| ]; intros; [ | easy | easy ].
Print Pos.size_nat.
...
intros.
destruct x as [x| x| ]; intros; cbn; [ | | easy ]. {
  destruct y as [y| y| ]. {
    remember (x ?= y)%positive as xy eqn:Hxy; symmetry in Hxy.
    destruct xy. {
      apply Pos.compare_eq in Hxy; subst y.
      now rewrite Nat.gcd_diag.
    } {
      apply -> Pos.compare_lt_iff in Hxy.
      remember (Pos.size_nat x + Pos.size_nat y~1)%nat as n eqn:Hn.
... ...
    rewrite Nat_gcd_pos.
    now rewrite positive_nat_Z.
  }
...
induction a; [ now rewrite Z_abs_of_nat | ].
unfold Z.gcd.
cbn - [ Nat.gcd Z.gcd ].
rewrite Zpos_P_of_succ_nat.
rewrite <- Nat2Z.inj_succ.
...
intros.
remember (a + b)%nat as c eqn:Hc.
assert (H : (a + b)%nat ≤ c) by now subst; apply Nat.le_refl.
clear Hc; rename H into Hc.
revert a b Hc.
induction c; intros; cbn. {
  apply Nat.le_0_r in Hc.
  apply Nat.eq_add_0 in Hc.
  destruct Hc; now subst a b.
}
destruct a; [ now cbn; rewrite Z_abs_of_nat | ].
cbn in Hc; apply Nat.succ_le_mono in Hc.
destruct b; [ now rewrite Nat.gcd_0_r, Z.gcd_0_r | ].
cbn - [ Nat.modulo ].
rewrite IHc. 2: {
  assert (H : (S b mod S a ≤ S b)%nat). {
    now apply Nat.mod_le.
  }
(* fuck you *)
...
(*
intros.
remember (Z.of_nat a) as x eqn:Hx; symmetry in Hx.
revert a b Hx.
induction x as [| x| x]; intros; cbn. {
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
Search (Z.to_nat (Z.pos _)).
do 2 rewrite Z2Nat.inj_pos.
Search (Nat.gcd (Pos.to_nat _)).
Search (Nat.gcd (Z.to_nat _)).
...
    rewrite <- Hx, <- Hy.
Search (Z.gcd (Z.of_nat _)).
Search (Z.of_nat (Nat.gcd _ _)).
...
*)
intros.
remember (Nat.gcd a b) as g eqn:Hg; symmetry in Hg.
revert a b Hg.
induction g; intros; cbn. {
  apply Nat.gcd_eq_0 in Hg.
  now destruct Hg; subst a b.
}
rewrite Zpos_P_of_succ_nat.
rewrite <- Nat2Z.inj_succ.
cbn.
rewrite <- Hg.
rewrite <- IHg.
...
*)
(*
intros.
revert a.
induction b; intros. {
  cbn.
  rewrite Nat.gcd_0_r.
  rewrite Z.gcd_0_r.
  now rewrite Z_abs_of_nat.
}
cbn.
rewrite Zpos_P_of_succ_nat.
...
*)
intros.
revert b.
induction a; intros. {
  now rewrite Z_abs_of_nat.
}
cbn.
specialize Nat.divmod_spec as H1.
specialize (H1 b a 0%nat a (Nat.le_refl _)).
remember (Nat.divmod _ _ _ _) as d eqn:Hd; symmetry in Hd.
destruct d as (x, y); cbn.
rewrite Nat.mul_0_r, Nat.sub_diag in H1.
do 2 rewrite Nat.add_0_r in H1.
destruct H1 as (H1, H2).
Search (Z.gcd (_ - _))%Z.
...
cbn - [ Nat.modulo ].
remember (Z.of_nat b) as y eqn:Hy; symmetry in Hy.
apply (f_equal Z.to_nat) in Hy.
rewrite Nat2Z.id in Hy.
subst b.
destruct y as [| y| y]. {
  now rewrite Nat.mod_0_l.
} {
  rewrite Nat.gcd_mod; [ | easy ].
  rewrite Z2Nat.inj_pos.
  rewrite Pos2Z.inj_gcd.
  rewrite Zpos_P_of_succ_nat.
  rewrite <- Nat2Z.inj_succ.
Search (Z.of_nat (Nat.gcd _ _)).
...
  rewrite <- Pos.succ_of_nat.
Search (Pos.gcd (Pos.succ _)).
Search (Nat.gcd _ (Pos.to_nat _)).
Search (Nat.gcd _ (S _)).
...

  apply (f_equal Z.to_nat) in Hy.
...
  specialize (Nat2Z.is_nonneg b) as H1.
  now rewrite Hy in H1.
...
do 2 rewrite Z_of_nat_gcd in H1.
Search (Z.of_nat (Pos.to_nat _)).
do 4 rewrite positive_nat_Z in H1.
easy.
...
symmetry in H1.
...
remember (Z.pos xn) as a.
remember (Z.pos xd) as b.
remember (Z.pos yn) as c.
remember (Z.pos yd) as d.
    apply Z_mul_div_eq_l; [ now subst a b | ].
Search (positive → nat).

...
specialize (Z.div_mod a (Z.gcd a b)) as H1.
assert (H : Z.gcd a b ≠ 0%Z) by now subst a b d.
specialize (H1 H); clear H.
rewrite H1 at 1.
Search ((_ * _ + _) / _)%Z.
rewrite Z.mul_comm.
rewrite Z.div_add_l.

specialize (H1 (Z.pos xn)).
...
    apply Z_mul_div_eq_l; [ easy | ].
Search (_ * (_ / _))%Z.
...
    specialize (Z.gcd_divide_l (Z.pos xn) (Z.pos xd)) as H1.
    apply Znumtheory.Zdivide_Zdiv_eq in H1.
Search (_ | _)%Z.
Znumtheory.Zdivide_Zdiv_eq: ∀ a b : Z, (0 < a)%Z → (a | b)%Z → b = (a * (b / a))%Z
specia
Z.gcd_divide_r: ∀ a b : Z, (Z.gcd a b | b)%Z
Search (_ = _ / _)%Q.
Search Z.gcd.
...
Search (_ / _)%Q.
remember (Z.pos xn) as a.
remember (Z.pos xd) as b.
Search (_ / Z.gcd _ _)%Z.
Search (Z.pos (_ * _)).
...
intros (xn, xd) (yn, yd) Hxy.
progress unfold "=="%Q in Hxy.
cbn in Hxy.
apply eq_QG_eq; cbn.
...
intros a b Hab.
unfold "=="%Q in Hab.
destruct a as (an, ad).
destruct b as (bn, bd).
cbn in Hab.
progress unfold QG_of_Q.
cbn.
apply eq_QG_eq; cbn.
...

(*
Theorem glop : ∀ q1 q2, q1 == q2 ↔ qg_q (QG_of_Q q1) = qg_q (QG_of_Q q2).
Proof.
intros.
split; intros Hq. {
  setoid_rewrite Hq.
...
split; intros Hq. 2: {
  apply eq_QG_eq in Hq.
...
*)

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
Admitted.
Theorem QG_of_Q_add_idemp_l :
  ∀ a b, QG_of_Q (qg_q (QG_of_Q a) + b) = QG_of_Q (a + b).
Proof.
intros; cbn.
Admitted.
... ...
rewrite QG_of_Q_add_idemp_r.
rewrite QG_of_Q_add_idemp_l.
now rewrite Qplus_assoc.
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
