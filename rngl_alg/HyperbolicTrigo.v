(* experimental
   hyperbolic angles implemented like trigo without π
   but with "x²-y²=1" instead of "x²+y²=1" *)

Set Nested Proofs Allowed.

Require Import Stdlib.Arith.Arith.
Import List.ListNotations.
Require Import RingLike.Utf8.
Require Import RingLike.Core.
Require Import RingLike.RealLike.
Require Import RingLike.Misc.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Definition cosh2_sinh2_prop x y :=
  ((x² - y² =? 1)%L && (0 ≤? x)%L)%bool = true.

Record hangle := mk_hangle
  { rngl_cosh : T;
    rngl_sinh : T;
    rngl_cosh2_sinh2 : cosh2_sinh2_prop rngl_cosh rngl_sinh }.

Class hangle_ctx :=
  { hc_ic : rngl_mul_is_comm T = true;
    hc_op : rngl_has_opp T = true;
    hc_ed : rngl_has_eq_dec T = true;
    hc_iv : rngl_has_inv T = true;
    hc_c2 : rngl_characteristic T ≠ 2;
    hc_or : rngl_is_ordered T = true }.

End a.

Arguments hangle T {ro}.
Arguments mk_hangle {T ro} (rngl_cosh rngl_sinh)%_L.
Arguments hangle_ctx T {ro rp}.
Arguments cosh2_sinh2_prop {T ro} (x y)%_L.

Declare Scope hangle_scope.
Delimit Scope hangle_scope with H.
Bind Scope hangle_scope with hangle.

Ltac destruct_hc :=
  set (Hic := hc_ic);
  set (Hop := hc_op);
  set (Hiv := hc_iv);
  set (Hed := hc_ed);
  set (Hor := hc_or);
  specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos;
  specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq;
  specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo;
  specialize hc_c2 as Hc2.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {hc : hangle_ctx T}.

Theorem fold_rl_sqrt : rl_nth_root 2 = rl_sqrt.
Proof. easy. Qed.

Theorem eq_hangle_eq : ∀ θ1 θ2,
  (rngl_cosh θ1, rngl_sinh θ1) = (rngl_cosh θ2, rngl_sinh θ2) ↔ θ1 = θ2.
Proof.
intros.
split; intros Hab; [ | now subst θ2 ].
injection Hab; clear Hab; intros Hs Hc.
destruct θ1 as (aco, asi, Hacs).
destruct θ2 as (bco, bsi, Hbcs).
cbn in Hs, Hc.
subst bsi bco.
f_equal.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Theorem cosh2_sinh2_prop_if :
  ∀ c s, cosh2_sinh2_prop c s → (c² - s² = 1)%L ∧ (0 ≤ c)%L.
Proof.
destruct_hc.
intros * Hcs.
progress unfold cosh2_sinh2_prop in Hcs.
apply Bool.andb_true_iff in Hcs.
split; [ now apply (rngl_eqb_eq Heo) | ].
now apply rngl_leb_le.
Qed.

Theorem rngl_cosh_proj_bound :
  ∀ c s, cosh2_sinh2_prop c s → (1 ≤ c)%L.
Proof.
destruct_hc.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
intros * Hcs.
apply cosh2_sinh2_prop_if in Hcs.
destruct Hcs as (Hcs, Hzc).
assert (H : (1 ≤ c²)%L). {
  apply (rngl_sub_move_r Hop) in Hcs.
  rewrite Hcs.
  apply (rngl_le_add_r Hor).
  apply (rngl_squ_nonneg Hos Hto).
}
replace 1%L with 1²%L in H by apply rngl_mul_1_l.
rewrite <- (rngl_squ_abs Hop c) in H.
rewrite <- (rngl_squ_abs Hop 1%L) in H.
apply (rngl_square_le_simpl_nonneg Hop Hiq Hor) in H. 2: {
  apply (rngl_abs_nonneg Hop Hto).
}
rewrite (rngl_abs_1 Hos Hor) in H.
now rewrite (rngl_abs_nonneg_eq Hop Hor) in H.
Qed.

Theorem rngl_cosh_bound :
  ∀ a, (1 ≤ rngl_cosh a)%L.
Proof.
destruct_hc.
intros.
destruct a as (ca, sa, Ha); cbn.
now apply (rngl_cosh_proj_bound ca sa).
Qed.

Theorem cosh2_sinh2_1 :
  ∀ θ, ((rngl_cosh θ)² - (rngl_sinh θ)² = 1)%L.
Proof.
destruct_hc.
intros.
destruct θ as (c, s, Hcs); cbn.
progress unfold cosh2_sinh2_prop in Hcs.
apply Bool.andb_true_iff in Hcs.
now apply (rngl_eqb_eq Heo).
Qed.

Theorem eq_rngl_cosh_0 :
  rngl_characteristic T ≠ 1 →
  ∀ θ, rngl_cosh θ ≠ 0%L.
Proof.
destruct_hc.
intros Hc1.
intros * H.
specialize (cosh2_sinh2_1 θ) as H1.
rewrite H in H1.
rewrite (rngl_squ_0 Hos) in H1.
apply (rngl_sub_move_l Hop) in H1.
rewrite (rngl_sub_0_l Hop) in H1.
specialize (rngl_squ_nonneg Hos Hto (rngl_sinh θ))%L as H2.
apply rngl_nlt_ge in H2.
apply H2; clear H2.
rewrite H1.
apply (rngl_opp_1_lt_0 Hop Hto Hc1).
Qed.

Theorem rngl_cosh_nonneg :
  ∀ θ, (0 ≤ rngl_cosh θ)%L.
Proof.
destruct_hc.
intros.
apply (rngl_le_trans Hor _ 1).
apply (rngl_0_le_1 Hos Hor).
apply rngl_cosh_bound.
Qed.

Theorem rngl_cosh_pos :
  rngl_characteristic T ≠ 1 →
  ∀ θ, (0 < rngl_cosh θ)%L.
Proof.
destruct_hc.
intros Hc1 *.
apply (rngl_le_neq Hto).
split; [ apply rngl_cosh_nonneg | ].
symmetry.
apply (eq_rngl_cosh_0 Hc1).
Qed.

Theorem hangle_zero_prop : (cosh2_sinh2_prop 1 0)%L.
Proof.
destruct_hc.
progress unfold cosh2_sinh2_prop.
progress unfold rngl_squ.
rewrite rngl_mul_1_l.
rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_r Hos).
apply Bool.andb_true_iff.
split; [ apply (rngl_eqb_refl Heo) | ].
apply rngl_leb_le.
apply (rngl_0_le_1 Hos Hor).
Qed.

Definition hangle_zero :=
  {| rngl_cosh := 1; rngl_sinh := 0;
     rngl_cosh2_sinh2 := hangle_zero_prop |}%L.

Theorem hangle_add_prop :
  ∀ a b,
  cosh2_sinh2_prop
    (rngl_cosh a * rngl_cosh b + rngl_sinh a * rngl_sinh b)%L
    (rngl_sinh a * rngl_cosh b + rngl_cosh a * rngl_sinh b)%L.
Proof.
destruct_hc.
intros.
rewrite (rngl_add_comm (rngl_sinh a * _)%L).
destruct a as (x, y, Hxy).
destruct b as (x', y', Hxy'); cbn.
move x' before y; move y' before x'.
progress unfold cosh2_sinh2_prop in Hxy, Hxy' |-*.
apply Bool.andb_true_iff in Hxy, Hxy'.
apply Bool.andb_true_iff.
destruct Hxy as (Hxy, Hzx).
destruct Hxy' as (Hxy', Hzx').
move Hxy' before Hxy.
split. {
  do 2 rewrite (rngl_squ_add Hic).
  rewrite rngl_add_add_swap.
  do 2 rewrite (rngl_sub_add_distr Hos).
  rewrite (rngl_sub_sub_swap Hop (_ + _ + _))%L.
  do 4 rewrite rngl_mul_assoc.
  rewrite (rngl_mul_mul_swap Hic (2 * x * y')%L).
  rewrite (rngl_mul_mul_swap Hic (2 * x) y')%L.
  rewrite (rngl_mul_mul_swap Hic (2 * x * x') y' y)%L.
  rewrite (rngl_add_sub Hos).
  do 4 rewrite (rngl_squ_mul Hic).
  do 2 rewrite (rngl_add_sub_swap Hop).
  rewrite <- (rngl_sub_sub_distr Hop).
  do 2 rewrite <- (rngl_mul_sub_distr_l Hop).
  apply (rngl_eqb_eq Heo) in Hxy'.
  rewrite Hxy'.
  now do 2 rewrite rngl_mul_1_r.
}
apply rngl_leb_le.
apply (rngl_eqb_eq Heo) in Hxy, Hxy'.
apply rngl_leb_le in Hzx, Hzx'.
assert (Hyx : (y ≤ x)%L). {
  destruct (rngl_leb_dec 0 y) as [Hzy| Hzy]. {
    apply rngl_leb_le in Hzy.
    apply (rngl_le_squ_le Hop Hiq Hor); [ easy | easy | ].
    apply (rngl_sub_move_r Hop) in Hxy.
    rewrite Hxy.
    apply (rngl_le_add_l Hos Hor).
    apply (rngl_0_le_1 Hos Hor).
  }
  apply rngl_leb_nle in Hzy.
  apply (rngl_nle_gt_iff Hto) in Hzy.
  apply (rngl_lt_le_incl Hor) in Hzy.
  now apply (rngl_le_trans Hor _ 0).
}
assert (Hyx' : (y' ≤ x')%L). {
  destruct (rngl_leb_dec 0 y') as [Hzy'| Hzy']. {
    apply rngl_leb_le in Hzy'.
    apply (rngl_le_squ_le Hop Hiq Hor); [ easy | easy | ].
    apply (rngl_sub_move_r Hop) in Hxy'.
    rewrite Hxy'.
    apply (rngl_le_add_l Hos Hor).
    apply (rngl_0_le_1 Hos Hor).
  }
  apply rngl_leb_nle in Hzy'.
  apply (rngl_nle_gt_iff Hto) in Hzy'.
  apply (rngl_lt_le_incl Hor) in Hzy'.
  now apply (rngl_le_trans Hor _ 0).
}
destruct (rngl_leb_dec 0 y) as [Hzy| Hzy]. {
  apply rngl_leb_le in Hzy.
  destruct (rngl_leb_dec 0 y') as [Hzy'| Hzy']. {
    apply rngl_leb_le in Hzy'.
    apply (rngl_le_trans Hor _ (y * y' + y * y')). 2: {
      apply (rngl_add_le_mono_r Hos Hor).
      now apply (rngl_mul_le_compat_nonneg Hor).
    }
    rewrite <- rngl_mul_2_l.
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply (rngl_0_le_2 Hos Hor).
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
  }
  apply rngl_leb_nle in Hzy'.
  apply (rngl_nle_gt_iff Hto) in Hzy'.
  clear - Hzx' Hyx Hzy Hzy' Hxy' hc Hor Hop Hos Hiq.
  apply (rngl_le_trans Hor _ (y * x' + y * y')). 2: {
    apply (rngl_add_le_mono_r Hor).
    now apply (rngl_mul_le_mono_nonneg_r Hop Hto).
  }
  rewrite <- rngl_mul_add_distr_l.
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
  rewrite rngl_add_comm.
  apply (rngl_le_opp_l Hop Hor).
  apply (rngl_le_squ_le Hop Hiq Hor); [ | easy | ]. {
    apply (rngl_lt_le_incl Hor) in Hzy'.
    (* todo: rename rngl_opp_nonneg_nonpos into rngl_le_0_opp, perhaps? *)
    now apply (rngl_opp_nonneg_nonpos Hop Hto).
  }
  rewrite (rngl_squ_opp Hop).
  apply (rngl_sub_move_r Hop) in Hxy'.
  rewrite Hxy'.
  apply (rngl_le_add_l Hos Hor).
  apply (rngl_0_le_1 Hos Hor).
}
apply rngl_leb_nle in Hzy.
destruct (rngl_leb_dec 0 y') as [Hzy'| Hzy']. {
  apply rngl_leb_le in Hzy'.
  apply (rngl_nle_gt_iff Hto) in Hzy.
  apply (rngl_le_trans Hor _ (x * y' + y * y')). 2: {
    apply (rngl_add_le_mono_r Hor).
    now apply (rngl_mul_le_mono_nonneg_l Hop Hto).
  }
  rewrite <- rngl_mul_add_distr_r.
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
  rewrite rngl_add_comm.
  apply (rngl_le_opp_l Hop Hor).
  apply (rngl_le_squ_le Hop Hiq Hor); [ | easy | ]. {
    apply (rngl_lt_le_incl Hor) in Hzy.
    (* todo: rename rngl_opp_nonneg_nonpos into rngl_le_0_opp, perhaps? *)
    now apply (rngl_opp_nonneg_nonpos Hop Hto).
  }
  rewrite (rngl_squ_opp Hop).
  apply (rngl_sub_move_r Hop) in Hxy.
  rewrite Hxy.
  apply (rngl_le_add_l Hos Hor).
  apply (rngl_0_le_1 Hos Hor).
}
apply rngl_leb_nle in Hzy'.
apply (rngl_nle_gt_iff Hto) in Hzy, Hzy'.
apply (rngl_le_0_add Hos Hto).
now apply (rngl_mul_nonneg_nonneg Hos Hor).
apply (rngl_lt_le_incl Hor) in Hzy, Hzy'.
now apply (rngl_mul_nonpos_nonpos Hos Hor).
Qed.

Definition hangle_add a b :=
  {| rngl_cosh := (rngl_cosh a * rngl_cosh b + rngl_sinh a * rngl_sinh b)%L;
     rngl_sinh := (rngl_sinh a * rngl_cosh b + rngl_cosh a * rngl_sinh b)%L;
     rngl_cosh2_sinh2 := hangle_add_prop a b |}.

Theorem hangle_nonneg_div_2_prop :
  ∀ a (ε := (if (0 ≤? rngl_sinh a)%L then 1%L else (-1)%L)),
  cosh2_sinh2_prop
    (√((rngl_cosh a + 1) / 2))
    (ε * √((rngl_cosh a - 1) / 2)).
Proof.
destruct_hc.
intros.
progress unfold cosh2_sinh2_prop.
assert (Hε : (ε² = 1)%L). {
  progress unfold ε.
  destruct (0 ≤? rngl_sinh a)%L.
  apply rngl_mul_1_l.
  apply (rngl_squ_opp_1 Hop).
}
rewrite (rngl_squ_mul Hic).
rewrite Hε.
rewrite rngl_mul_1_l.
apply Bool.andb_true_iff.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  split. {
    apply (rngl_eqb_eq Heo).
    now rewrite (H1 (_ + _)%L), (H1 1%L).
  }
  apply rngl_leb_le.
  rewrite (H1 √_)%L.
  apply (rngl_le_refl Hor).
}
split. 2: {
  apply rngl_leb_le.
  apply rl_sqrt_nonneg.
  apply (rngl_le_div_r Hop Hiv Hor).
  apply (rngl_0_lt_2 Hos Hc1 Hor).
  rewrite (rngl_mul_0_l Hos).
  rewrite rngl_add_comm.
  apply (rngl_le_opp_l Hop Hor).
  apply (rngl_le_trans Hor _ 1); [ | apply rngl_cosh_bound ].
  apply (rngl_opp_1_le_1 Hop Hto).
}
apply (rngl_eqb_eq Heo).
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_le_div_r Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hos Hc1 Hor).
  }
  rewrite (rngl_mul_0_l Hos).
  rewrite rngl_add_comm.
  apply (rngl_le_opp_l Hop Hor).
  apply (rngl_le_trans Hor _ 1); [ | apply rngl_cosh_bound ].
  apply (rngl_opp_1_le_1 Hop Hto).
}
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_le_div_r Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hos Hc1 Hor).
  }
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_le_0_sub Hop Hor).
  apply rngl_cosh_bound.
}
rewrite <- (rngl_div_sub_distr_r Hop Hiv).
rewrite (rngl_sub_sub_distr Hop).
rewrite (rngl_add_sub_swap Hop).
rewrite (rngl_sub_diag Hos).
rewrite rngl_add_0_l.
apply (rngl_div_diag Hiq).
apply (rngl_2_neq_0 Hos Hc1 Hto).
Qed.

Definition hangle_div_2 a :=
  let ε := if (0 ≤? rngl_sinh a)%L then 1%L else (-1)%L in
  {| rngl_cosh := √((rngl_cosh a + 1) / 2);
     rngl_sinh := ε * √((rngl_cosh a - 1) / 2);
     rngl_cosh2_sinh2 := hangle_nonneg_div_2_prop a |}.

Fixpoint hangle_mul_nat a n :=
  match n with
  | 0 => hangle_zero
  | S n' => hangle_add a (hangle_mul_nat a n')
  end.

End a.

Notation "θ /₂" := (hangle_div_2 θ) (at level 40) : hangle_scope.
Notation "n * θ" := (hangle_mul_nat θ n) : hangle_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {hc : hangle_ctx T}.

Theorem hangle_div_2_mul_2 :
  ∀ a, (0 ≤ rngl_cosh a)%L → (2 * (a /₂))%H = a.
Proof.
destruct_hc.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hza.
  apply eq_hangle_eq.
  do 2 rewrite (H1 (rngl_cosh _)).
  do 2 rewrite (H1 (rngl_sinh _)).
  easy.
}
intros * Hza.
apply eq_hangle_eq.
specialize (rngl_2_neq_0 Hos Hc1 Hto) as H20.
progress unfold hangle_mul_nat.
progress unfold hangle_div_2.
progress unfold hangle_add.
cbn.
destruct (rngl_leb_dec 0 (rngl_cosh a)) as [H| H]. 2: {
  now apply rngl_leb_nle in H.
}
cbn; clear H.
do 2 rewrite (rngl_mul_0_r Hos).
do 2 rewrite rngl_mul_1_r.
do 2 rewrite rngl_add_0_r.
do 2 rewrite fold_rngl_squ.
set (ε := if (0 ≤? rngl_sinh a)%L then 1%L else (-1)%L).
assert (Hε : (ε² = 1)%L). {
  progress unfold ε.
  destruct (0 ≤? rngl_sinh a)%L.
  apply rngl_mul_1_l.
  apply (rngl_squ_opp_1 Hop).
}
rewrite (rngl_squ_mul Hic).
rewrite Hε.
rewrite rngl_mul_1_l.
assert (Hz1ac : (0 ≤ rngl_cosh a + 1)%L). {
  apply (rngl_le_sub_le_add_r Hop Hor).
  rewrite (rngl_sub_0_l Hop).
  apply (rngl_le_trans Hor _ 0); [ | easy ].
  apply (rngl_opp_1_le_0 Hop Hor).
}
assert (Hz1sc : (0 ≤ rngl_cosh a - 1)%L). {
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply (rngl_cosh_bound a).
}
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_le_div_r Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hos Hc1 Hor).
  }
  now rewrite (rngl_mul_0_l Hos).
}
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_le_div_r Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hos Hc1 Hor).
  }
  now rewrite (rngl_mul_0_l Hos).
}
progress unfold rngl_div.
rewrite Hiv.
rewrite <- rngl_mul_add_distr_r.
rewrite (rngl_add_sub_assoc Hop).
rewrite (rngl_add_sub_swap Hop).
rewrite (rngl_add_sub Hos).
rewrite <- rngl_mul_2_r.
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_inv_diag_r Hiv); [ | easy ].
rewrite rngl_mul_1_r; f_equal.
progress unfold rl_sqrt.
rewrite rngl_add_comm.
rewrite (rngl_mul_comm Hic).
rewrite <- rngl_mul_2_r.
do 2 rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_comm Hic).
rewrite rngl_mul_assoc.
rewrite <- rl_nth_root_mul; cycle 1. {
  rewrite (rngl_mul_inv_r Hiv).
  apply (rngl_le_div_r Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hos Hc1 Hor).
  }
  now rewrite (rngl_mul_0_l Hos).
} {
  rewrite (rngl_mul_inv_r Hiv).
  apply (rngl_le_div_r Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hos Hc1 Hor).
  }
  now rewrite (rngl_mul_0_l Hos).
}
rewrite (rngl_mul_mul_swap Hic (_ - 1)%L).
do 3 rewrite <- rngl_mul_assoc.
rewrite rl_nth_root_mul; cycle 1; [ easy | | ]. {
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
  apply (rngl_mul_diag_nonneg Hos Hor).
}
rewrite rl_nth_root_mul; cycle 1; [ easy | | ]. {
  apply (rngl_mul_diag_nonneg Hos Hor).
}
assert (Hz2 : (0 ≤ 2⁻¹)%L). {
  apply (rngl_lt_le_incl Hor).
  apply (rngl_inv_pos Hop Hiv Hor).
  apply (rngl_0_lt_2 Hos Hc1 Hor).
}
rewrite rl_nth_root_mul; [ | easy | easy ].
do 2 rewrite rngl_mul_assoc.
rewrite fold_rngl_squ.
rewrite fold_rl_sqrt.
rewrite rngl_squ_pow_2.
progress unfold rl_sqrt.
rewrite rl_nth_root_pow; [ | easy ].
rewrite (rngl_mul_comm Hic).
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_inv_diag_l Hiv); [ | easy ].
rewrite rngl_mul_1_r.
rewrite <- rl_nth_root_mul; [ | easy | easy ].
rewrite (rngl_mul_comm Hic (_ - _)).
rewrite (rngl_squ_sub_squ' Hop).
rewrite rngl_mul_1_r, rngl_mul_1_l.
rewrite (rngl_add_sub Hos).
rewrite rngl_squ_1.
specialize (cosh2_sinh2_1 a) as H1.
apply (rngl_sub_move_l Hop) in H1.
rewrite <- H1.
rewrite fold_rl_sqrt.
rewrite (rl_sqrt_squ Hop Hto).
progress unfold ε.
remember (0 ≤? rngl_sinh a)%L as saz eqn:Hsaz; symmetry in Hsaz.
destruct saz. {
  apply rngl_leb_le in Hsaz.
  rewrite rngl_mul_1_l.
  now apply (rngl_abs_nonneg_eq Hop Hor).
} {
  apply (rngl_leb_gt_iff Hor) in Hsaz.
  apply (rngl_lt_le_incl Hor) in Hsaz.
  rewrite (rngl_abs_nonpos_eq Hop Hto); [ | easy ].
  rewrite (rngl_mul_opp_opp Hop).
  apply rngl_mul_1_l.
}
Qed.

Theorem hangle_opp_prop :
  ∀ a, cosh2_sinh2_prop (rngl_cosh a) (- rngl_sinh a)%L.
Proof.
destruct_hc.
intros.
destruct a as (x, y, Hxy); cbn.
progress unfold cosh2_sinh2_prop in Hxy |-*.
now rewrite (rngl_squ_opp Hop).
Qed.

Definition hangle_opp a :=
  {| rngl_cosh := rngl_cosh a; rngl_sinh := - rngl_sinh a;
     rngl_cosh2_sinh2 := hangle_opp_prop a |}.

Definition hangle_sub θ1 θ2 := hangle_add θ1 (hangle_opp θ2).

(* *)

Definition hangle_eqb a b :=
  ((rngl_cosh a =? rngl_cosh b)%L && (rngl_sinh a =? rngl_sinh b)%L)%bool.

Definition hangle_leb θ1 θ2 :=
  if (0 ≤? rngl_sinh θ1)%L then
    if (0 ≤? rngl_sinh θ2)%L then (rngl_cosh θ1 ≤? rngl_cosh θ2)%L
    else false
  else
    if (0 ≤? rngl_sinh θ2)%L then true
    else (rngl_cosh θ2 ≤? rngl_cosh θ1)%L.

Definition hangle_ltb θ1 θ2 :=
  if (0 ≤? rngl_sinh θ1)%L then
    if (0 ≤? rngl_sinh θ2)%L then (rngl_cosh θ1 <? rngl_cosh θ2)%L
    else false
  else
    if (0 ≤? rngl_sinh θ2)%L then true
    else (rngl_cosh θ2 <? rngl_cosh θ1)%L.

End a.

Notation "0" := hangle_zero : hangle_scope.
Notation "θ1 + θ2" := (hangle_add θ1 θ2) : hangle_scope.
Notation "θ1 - θ2" := (hangle_sub θ1 θ2) : hangle_scope.
Notation "- θ" := (hangle_opp θ) : hangle_scope.
Notation "θ1 =? θ2" := (hangle_eqb θ1 θ2) : hangle_scope.
Notation "θ1 ≠? θ2" := (negb (hangle_eqb θ1 θ2)) : hangle_scope.
Notation "θ1 ≤? θ2" := (hangle_leb θ1 θ2) : hangle_scope.
Notation "θ1 <? θ2" := (hangle_ltb θ1 θ2) : hangle_scope.
Notation "θ1 ≤ θ2" := (hangle_leb θ1 θ2 = true) : hangle_scope.
Notation "θ1 < θ2" := (hangle_ltb θ1 θ2 = true) : hangle_scope.
Notation "θ1 ≤ θ2 < θ3" :=
  (hangle_leb θ1 θ2 = true ∧ hangle_ltb θ2 θ3 = true) : hangle_scope.
Notation "θ1 ≤ θ2 ≤ θ3" :=
  (hangle_leb θ1 θ2 = true ∧ hangle_leb θ2 θ3 = true) : hangle_scope.
Notation "θ1 < θ2 < θ3" :=
  (hangle_ltb θ1 θ2 = true ∧ hangle_ltb θ2 θ3 = true) : hangle_scope.
Notation "θ1 < θ2 ≤ θ3" :=
  (hangle_ltb θ1 θ2 = true ∧ hangle_leb θ2 θ3 = true) : hangle_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {hc : hangle_ctx T}.

Theorem rngl_characteristic_1_hangle_0 :
  rngl_characteristic T = 1 →
  ∀ θ, (θ = 0)%H.
Proof.
destruct_hc.
intros Hc1 *.
specialize (rngl_characteristic_1 Hos Hc1) as H1.
apply eq_hangle_eq.
do 2 rewrite (H1 (rngl_cosh _)).
now do 2 rewrite (H1 (rngl_sinh _)).
Qed.

Theorem hangle_nlt_ge : ∀ θ1 θ2, ¬ (θ1 < θ2)%H ↔ (θ2 ≤ θ1)%H.
Proof.
destruct_hc.
intros.
progress unfold hangle_ltb.
progress unfold hangle_leb.
destruct (0 ≤? rngl_sinh θ1)%L. {
  destruct (0 ≤? rngl_sinh θ2)%L; [ | easy ].
  split; intros H. {
    apply Bool.not_true_iff_false in H.
    apply (rngl_ltb_ge_iff Hto) in H.
    now apply rngl_leb_le.
  }
  apply Bool.not_true_iff_false.
  apply rngl_ltb_ge.
  now apply rngl_leb_le.
}
destruct (0 ≤? rngl_sinh θ2)%L; [ easy | ].
split; intros H. {
  apply Bool.not_true_iff_false in H.
  apply (rngl_ltb_ge_iff Hto) in H.
  now apply rngl_leb_le.
}
apply Bool.not_true_iff_false.
apply rngl_ltb_ge.
now apply rngl_leb_le.
Qed.

Theorem hangle_nle_gt : ∀ θ1 θ2, (θ1 ≤? θ2)%H ≠ true ↔ (θ2 < θ1)%H.
Proof.
destruct_hc.
intros.
progress unfold hangle_ltb.
progress unfold hangle_leb.
destruct (0 ≤? rngl_sinh θ1)%L. {
  destruct (0 ≤? rngl_sinh θ2)%L; [ | easy ].
  split; intros H. {
    apply Bool.not_true_iff_false in H.
    apply (rngl_leb_gt_iff Hor) in H.
    now apply rngl_ltb_lt.
  }
  apply Bool.not_true_iff_false.
  apply (rngl_leb_gt_iff Hor).
  now apply rngl_ltb_lt.
}
destruct (0 ≤? rngl_sinh θ2)%L; [ easy | ].
split; intros H. {
  apply Bool.not_true_iff_false in H.
  apply (rngl_leb_gt_iff Hor) in H.
  now apply rngl_ltb_lt.
}
apply Bool.not_true_iff_false.
apply (rngl_leb_gt_iff Hor).
now apply rngl_ltb_lt.
Qed.

Theorem rngl_cosh_add :
  ∀ θ1 θ2,
  rngl_cosh (θ1 + θ2) =
    (rngl_cosh θ1 * rngl_cosh θ2 + rngl_sinh θ1 * rngl_sinh θ2)%L.
Proof. easy. Qed.

Theorem rngl_sinh_add :
  ∀ θ1 θ2,
  rngl_sinh (θ1 + θ2) =
    (rngl_sinh θ1 * rngl_cosh θ2 + rngl_cosh θ1 * rngl_sinh θ2)%L.
Proof. easy. Qed.

Theorem rngl_cosh_sub :
  ∀ θ1 θ2,
  (rngl_cosh (θ1 - θ2) =
     rngl_cosh θ1 * rngl_cosh θ2 - rngl_sinh θ1 * rngl_sinh θ2)%L.
Proof.
destruct_hc.
intros; cbn.
rewrite (rngl_mul_opp_r Hop).
apply (rngl_add_opp_r Hop).
Qed.

Theorem rngl_sinh_sub :
  ∀ θ1 θ2,
  (rngl_sinh (θ1 - θ2) =
     rngl_sinh θ1 * rngl_cosh θ2 - rngl_cosh θ1 * rngl_sinh θ2)%L.
Proof.
destruct_hc.
intros; cbn.
rewrite (rngl_mul_opp_r Hop).
apply (rngl_add_opp_r Hop).
Qed.

Theorem eq_rngl_sinh_0 : ∀ θ, rngl_sinh θ = 0%L → θ = 0%H.
Proof.
destruct_hc.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros * Hθ.
  apply (rngl_characteristic_1_hangle_0 Hc1).
}
intros * Hθ.
destruct θ as (c, s, Hcs).
cbn in Hθ |-*.
subst s; cbn.
specialize (cosh2_sinh2_prop_if _ _ Hcs) as H1.
rewrite (rngl_squ_0 Hos) in H1.
rewrite (rngl_sub_0_r Hos) in H1.
rewrite <- rngl_squ_1 in H1.
destruct H1 as (H1, H2).
apply (rngl_squ_eq_cases Hop Hiv Heo) in H1. 2: {
  rewrite rngl_mul_1_l.
  apply rngl_mul_1_r.
}
apply eq_hangle_eq; cbn.
destruct H1; subst c; [ easy | ].
exfalso.
apply rngl_nlt_ge in H2.
apply H2; clear H2.
apply (rngl_opp_1_lt_0 Hop Hto Hc1).
Qed.

Theorem hangle_add_comm :
  ∀ θ1 θ2, (θ1 + θ2 = θ2 + θ1)%H.
Proof.
destruct_hc.
intros.
apply eq_hangle_eq; cbn.
rewrite (rngl_mul_comm Hic).
rewrite (rngl_mul_comm Hic (rngl_sinh θ1)).
f_equal.
rewrite rngl_add_comm.
rewrite (rngl_mul_comm Hic).
rewrite (rngl_mul_comm Hic (rngl_cosh θ2)).
easy.
Qed.

Theorem hangle_add_assoc :
  ∀ θ1 θ2 θ3, (θ1 + (θ2 + θ3) = (θ1 + θ2) + θ3)%H.
Proof.
destruct_hc.
intros.
apply eq_hangle_eq; cbn.
destruct θ1 as (c1, s1, Hcs1).
destruct θ2 as (c2, s2, Hcs2).
destruct θ3 as (c3, s3, Hcs3).
cbn.
do 4 rewrite rngl_mul_add_distr_l.
do 4 rewrite rngl_mul_add_distr_r.
do 8 rewrite rngl_mul_assoc.
do 4 rewrite <- rngl_add_assoc.
f_equal. {
  f_equal.
  rewrite rngl_add_comm; symmetry.
  apply rngl_add_assoc.
} {
  f_equal.
  rewrite rngl_add_comm; symmetry.
  apply rngl_add_assoc.
}
Qed.

Theorem hangle_add_opp_l : ∀ θ1 θ2, (- θ1 + θ2 = θ2 - θ1)%H.
Proof.
intros.
apply hangle_add_comm.
Qed.

Theorem hangle_add_opp_r : ∀ θ1 θ2, (θ1 + - θ2 = θ1 - θ2)%H.
Proof. easy. Qed.

Theorem hangle_sub_diag : ∀ θ, (θ - θ = 0)%H.
Proof.
destruct_hc.
intros.
apply eq_hangle_eq; cbn.
do 2 rewrite (rngl_mul_opp_r Hop).
do 2 rewrite (rngl_add_opp_r Hop).
do 2 rewrite fold_rngl_squ.
rewrite cosh2_sinh2_1.
f_equal.
rewrite (rngl_mul_comm Hic).
apply (rngl_sub_diag Hos).
Qed.

Theorem hangle_add_0_l : ∀ θ, (0 + θ = θ)%H.
Proof.
destruct_hc.
intros.
apply eq_hangle_eq; cbn.
do 2 rewrite rngl_mul_1_l.
do 2 rewrite (rngl_mul_0_l Hos).
now rewrite rngl_add_0_l, rngl_add_0_r.
Qed.

Theorem hangle_add_0_r : ∀ θ, (θ + 0 = θ)%H.
Proof.
destruct_hc.
intros.
apply eq_hangle_eq; cbn.
do 2 rewrite rngl_mul_1_r.
do 2 rewrite (rngl_mul_0_r Hos).
now do 2 rewrite rngl_add_0_r.
Qed.

Theorem hangle_sub_0_l :
  ∀ θ, (0 - θ = - θ)%H.
Proof.
destruct_hc.
intros.
apply eq_hangle_eq; cbn.
do 2 rewrite rngl_mul_1_l.
do 2 rewrite (rngl_mul_0_l Hos).
now rewrite rngl_add_0_l, rngl_add_0_r.
Qed.

Theorem hangle_sub_0_r :
  ∀ θ, (θ - 0 = θ)%H.
Proof.
destruct_hc.
intros.
apply eq_hangle_eq; cbn.
do 2 rewrite rngl_mul_1_r.
rewrite (rngl_opp_0 Hop).
do 2 rewrite (rngl_mul_0_r Hos).
now do 2 rewrite rngl_add_0_r.
Qed.

Theorem hangle_add_opp_diag_l : ∀ θ, (- θ + θ = 0)%H.
Proof.
destruct_hc; intros.
apply eq_hangle_eq; cbn.
do 2 rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_add_opp_r Hop).
rewrite rngl_add_comm.
rewrite (rngl_add_opp_r Hop).
do 2 rewrite fold_rngl_squ.
rewrite (rngl_mul_comm Hic).
rewrite (rngl_sub_diag Hos).
now rewrite cosh2_sinh2_1.
Qed.

Theorem hangle_add_sub : ∀ θ1 θ2, (θ1 + θ2 - θ2)%H = θ1.
Proof.
destruct_hc; intros.
progress unfold hangle_sub.
rewrite <- hangle_add_assoc.
rewrite hangle_add_opp_r.
rewrite hangle_sub_diag.
apply hangle_add_0_r.
Qed.

Theorem hangle_sub_add : ∀ θ1 θ2, (θ1 - θ2 + θ2)%H = θ1.
Proof.
destruct_hc; intros.
progress unfold hangle_sub.
rewrite <- hangle_add_assoc.
rewrite hangle_add_opp_diag_l.
apply hangle_add_0_r.
Qed.

Theorem hangle_opp_add_distr :
  ∀ θ1 θ2, (- (θ1 + θ2))%H = (- θ2 - θ1)%H.
Proof.
destruct_hc.
intros.
apply eq_hangle_eq; cbn.
do 2 rewrite (rngl_mul_opp_r Hop).
do 2 rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_opp_involutive Hop).
do 2 rewrite (rngl_mul_comm Hic (rngl_cosh θ1)).
do 2 rewrite (rngl_mul_comm Hic (rngl_sinh θ1)).
f_equal.
rewrite (rngl_opp_add_distr Hop).
rewrite (rngl_opp_sub_swap Hop).
now rewrite (rngl_add_opp_r Hop).
Qed.

Theorem hangle_opp_sub_distr :
  ∀ θ1 θ2, (- (θ1 - θ2))%H = (θ2 - θ1)%H.
Proof.
destruct_hc.
intros.
apply eq_hangle_eq; cbn.
do 4 rewrite (rngl_mul_opp_r Hop).
do 4 rewrite (rngl_add_opp_r Hop).
rewrite (rngl_opp_sub_distr Hop).
do 2 rewrite (rngl_mul_comm Hic (rngl_cosh θ1)).
do 2 rewrite (rngl_mul_comm Hic (rngl_sinh θ1)).
easy.
Qed.

Theorem hangle_opp_involutive : ∀ θ, (- - θ)%H = θ.
Proof.
destruct_hc.
intros.
apply eq_hangle_eq; cbn.
f_equal.
apply (rngl_opp_involutive Hop).
Qed.

Theorem hangle_sub_sub_distr :
  ∀ θ1 θ2 θ3, (θ1 - (θ2 - θ3))%H = (θ1 - θ2 + θ3)%H.
Proof.
intros.
progress unfold hangle_sub.
rewrite <- hangle_add_assoc.
f_equal.
rewrite hangle_opp_add_distr.
rewrite hangle_opp_involutive.
apply hangle_add_comm.
Qed.

Theorem hangle_add_move_l :
  ∀ θ1 θ2 θ3, (θ1 + θ2)%H = θ3 ↔ θ2 = (θ3 - θ1)%H.
Proof.
destruct_hc.
intros.
split; intros H2. {
  subst θ3; symmetry.
  rewrite hangle_add_comm.
  apply hangle_add_sub.
} {
  subst θ2.
  rewrite hangle_add_comm.
  apply hangle_sub_add.
}
Qed.

Theorem hangle_add_move_r :
  ∀ θ1 θ2 θ3, (θ1 + θ2)%H = θ3 ↔ θ1 = (θ3 - θ2)%H.
Proof.
destruct_hc; intros.
rewrite hangle_add_comm.
apply hangle_add_move_l.
Qed.

Theorem hangle_sub_move_l :
  ∀ θ1 θ2 θ3, (θ1 - θ2)%H = θ3 ↔ θ2 = (θ1 - θ3)%H.
Proof.
destruct_hc.
intros.
split; intros Ha. {
  subst θ3; symmetry.
  rewrite hangle_sub_sub_distr.
  rewrite hangle_sub_diag.
  apply hangle_add_0_l.
} {
  subst θ2.
  rewrite hangle_sub_sub_distr.
  rewrite hangle_sub_diag.
  apply hangle_add_0_l.
}
Qed.

Theorem hangle_sub_move_r :
  ∀ θ1 θ2 θ3, (θ1 - θ2)%H = θ3 ↔ θ1 = (θ3 + θ2)%H.
Proof.
destruct_hc.
intros.
split; intros Ha. {
  subst θ3; symmetry.
  apply hangle_sub_add.
} {
  subst θ1.
  apply hangle_add_sub.
}
Qed.

Theorem rngl_sinh_sinh_nonneg_sinh_le_cosh_le_iff :
  ∀ θ1 θ2,
  (0 ≤ rngl_sinh θ1)%L
  → (0 ≤ rngl_sinh θ2)%L
  → (rngl_sinh θ1 ≤ rngl_sinh θ2)%L
  ↔ (rngl_cosh θ1 ≤ rngl_cosh θ2)%L.
Proof.
destruct_hc.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
intros * Hzs1 Hzs2.
specialize (cosh2_sinh2_1 θ1) as Hcs1.
specialize (cosh2_sinh2_1 θ2) as Hcs2.
split. {
  intros Hss.
  apply (rngl_le_le_squ Hop Hor) in Hss; [ | easy ].
  apply (rngl_sub_move_l Hop) in Hcs1, Hcs2.
  rewrite Hcs1, Hcs2 in Hss.
  apply (rngl_sub_le_mono_r Hop Hor) in Hss.
  apply (rngl_le_squ_le Hop Hiq Hor) in Hss; [ easy | | ].
  apply rngl_cosh_nonneg.
  apply rngl_cosh_nonneg.
} {
  intros Hcc.
  apply (rngl_le_le_squ Hop Hor) in Hcc; [ | apply rngl_cosh_nonneg ].
  apply (rngl_sub_move_r Hop) in Hcs1, Hcs2.
  rewrite Hcs1, Hcs2 in Hcc.
  apply (rngl_add_le_mono_l Hos Hor) in Hcc.
  now apply (rngl_le_squ_le Hop Hiq Hor) in Hcc.
}
Qed.

Theorem rngl_sinh_sinh_nonneg_sinh_lt_cosh_lt_iff :
  ∀ θ1 θ2,
  (0 ≤ rngl_sinh θ1)%L
  → (0 ≤ rngl_sinh θ2)%L
  → (rngl_sinh θ1 < rngl_sinh θ2)%L
  ↔ (rngl_cosh θ1 < rngl_cosh θ2)%L.
Proof.
destruct_hc.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
intros * Hzs1 Hzs2.
specialize (cosh2_sinh2_1 θ1) as Hcs1.
specialize (cosh2_sinh2_1 θ2) as Hcs2.
split. {
  intros Hss.
  apply (rngl_lt_lt_squ Hop Hiq Hor) in Hss; [ | | easy ]. 2: {
    apply (rngl_mul_comm Hic).
  }
  apply (rngl_sub_move_l Hop) in Hcs1, Hcs2.
  rewrite Hcs1, Hcs2 in Hss.
  apply (rngl_sub_lt_mono_r Hop Hor) in Hss.
  apply (rngl_lt_squ_lt Hop Hiq Hor) in Hss; [ easy | | ].
  apply rngl_cosh_nonneg.
  apply rngl_cosh_nonneg.
} {
  intros Hcc.
  apply (rngl_lt_lt_squ Hop Hiq Hor) in Hcc; cycle 1. {
    apply (rngl_mul_comm Hic).
  } {
    apply rngl_cosh_nonneg.
  }
  apply (rngl_sub_move_r Hop) in Hcs1, Hcs2.
  rewrite Hcs1, Hcs2 in Hcc.
  apply (rngl_add_lt_mono_l Hos Hor) in Hcc.
  now apply (rngl_lt_squ_lt Hop Hiq Hor) in Hcc.
}
Qed.

Theorem eq_rngl_cosh_1 : ∀ θ, rngl_cosh θ = 1%L ↔ θ = 0%H.
Proof.
destruct_hc.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hi1.
intros.
split; intros Hθ; [ | now subst θ ].
specialize (cosh2_sinh2_1 θ) as H1.
rewrite Hθ in H1.
rewrite rngl_squ_1 in H1.
apply (rngl_sub_move_l Hop) in H1.
rewrite (rngl_sub_diag Hos) in H1.
apply (eq_rngl_squ_0 Hos) in H1. 2: {
  apply Bool.orb_true_iff; right.
  now rewrite Heo, Hi1.
}
apply eq_hangle_eq.
now rewrite Hθ, H1.
Qed.

Theorem rngl_cosh_eq :
  ∀ θ1 θ2, rngl_cosh θ1 = rngl_cosh θ2 → θ1 = θ2 ∨ θ1 = (- θ2)%H.
Proof.
destruct_hc.
intros * Hcc.
destruct (rngl_eqb_dec (rngl_sinh θ1) (rngl_sinh θ2)) as [Hss| Hss]. {
  apply (rngl_eqb_eq Heo) in Hss.
  left.
  apply eq_hangle_eq.
  now rewrite Hcc, Hss.
}
apply (rngl_eqb_neq Heo) in Hss.
right.
apply eq_hangle_eq.
rewrite Hcc; f_equal.
cbn.
specialize (cosh2_sinh2_1 θ1) as H1.
specialize (cosh2_sinh2_1 θ2) as H2.
apply (rngl_sub_move_l Hop) in H1, H2.
rewrite Hcc in H1.
rewrite <- H2 in H1; clear H2.
apply (eq_rngl_squ_rngl_abs Hop Hto) in H1; cycle 1. {
  apply Bool.orb_true_iff; right.
  apply (rngl_has_inv_has_inv_or_pdiv Hiv).
} {
  apply (rngl_mul_comm Hic).
}
progress unfold rngl_abs in H1.
remember (rngl_sinh θ1 ≤? 0)%L as s1z eqn:Hs1z.
remember (rngl_sinh θ2 ≤? 0)%L as s2z eqn:Hs2z.
symmetry in Hs1z, Hs2z.
destruct s1z; [ | now destruct s2z ].
destruct s2z; [ now apply (rngl_opp_inj Hop) in H1 | ].
rewrite <- H1; symmetry.
apply (rngl_opp_involutive Hop).
Qed.

Theorem rngl_sinh_eq :
  ∀ θ1 θ2, rngl_sinh θ1 = rngl_sinh θ2 → θ1 = θ2.
Proof.
destruct_hc.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_hangle_0 Hc1) as H1.
  intros.
  now rewrite (H1 θ1), (H1 θ2).
}
intros * Hss.
destruct (rngl_eqb_dec (rngl_cosh θ1) (rngl_cosh θ2)) as [Hcc| Hcc]. {
  apply (rngl_eqb_eq Heo) in Hcc.
  apply eq_hangle_eq.
  now rewrite Hcc, Hss.
}
apply (rngl_eqb_neq Heo) in Hcc.
apply eq_hangle_eq.
exfalso; apply Hcc; clear Hcc.
specialize (cosh2_sinh2_1 θ1) as H1.
specialize (cosh2_sinh2_1 θ2) as H2.
apply (rngl_sub_move_r Hop) in H1, H2.
rewrite Hss in H1.
rewrite <- H2 in H1; clear H2.
apply (eq_rngl_squ_rngl_abs Hop Hto Hii) in H1. 2: {
  apply (rngl_mul_comm Hic).
}
progress unfold rngl_abs in H1.
remember (rngl_cosh θ1 ≤? 0)%L as c1z eqn:Hc1z.
remember (rngl_cosh θ2 ≤? 0)%L as c2z eqn:Hc2z.
symmetry in Hc1z, Hc2z.
destruct c1z. 2: {
  destruct c2z; [ | easy ].
  exfalso.
  apply rngl_leb_le in Hc2z.
  apply rngl_nlt_ge in Hc2z.
  apply Hc2z; clear Hc2z.
  apply (rngl_cosh_pos Hc1).
}
destruct c2z; [ now apply (rngl_opp_inj Hop) in H1 | ].
exfalso.
apply rngl_leb_le in Hc1z.
apply rngl_nlt_ge in Hc1z.
apply Hc1z; clear Hc1z.
apply (rngl_cosh_pos Hc1).
Qed.

Theorem rngl_add_cosh_nonneg :
  ∀ θ1 θ2, (0 ≤ rngl_cosh θ1 + rngl_cosh θ2)%L.
Proof.
destruct_hc.
intros.
apply (rngl_le_0_add Hos Hto); apply rngl_cosh_nonneg.
Qed.

Theorem rngl_sinh_sub_anticomm :
  ∀ θ1 θ2, rngl_sinh (θ1 - θ2) = (- rngl_sinh (θ2 - θ1))%L.
Proof.
destruct_hc.
intros; cbn.
do 2 rewrite (rngl_mul_opp_r Hop).
do 2 rewrite (rngl_add_opp_r Hop).
rewrite (rngl_opp_sub_distr Hop).
rewrite (rngl_mul_comm Hic).
f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem hangle_sub_move_0_r : ∀ θ1 θ2, (θ1 - θ2)%H = 0%H ↔ θ1 = θ2.
Proof.
intros.
split; intros H12. {
  apply hangle_sub_move_r in H12.
  now rewrite hangle_add_0_l in H12.
} {
  apply hangle_sub_move_r.
  now rewrite hangle_add_0_l.
}
Qed.

Theorem hangle_leb_gt : ∀ θ1 θ2, (θ1 ≤? θ2)%H = false ↔ (θ2 < θ1)%H.
Proof.
destruct_hc.
intros.
progress unfold hangle_leb.
progress unfold hangle_ltb.
remember (0 ≤? rngl_sinh θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sinh θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs1. {
  apply rngl_leb_le in Hzs1.
  destruct zs2; [ | easy ].
  apply rngl_leb_le in Hzs2.
  split; intros H12. {
    apply (rngl_leb_gt_iff Hor) in H12.
    now apply rngl_ltb_lt.
  } {
    apply (rngl_leb_gt_iff Hor).
    now apply rngl_ltb_lt in H12.
  }
} {
  apply (rngl_leb_gt_iff Hor) in Hzs1.
  destruct zs2; [ easy | ].
  split; intros H12. {
    apply (rngl_leb_gt_iff Hor) in H12.
    now apply rngl_ltb_lt.
  } {
    apply (rngl_leb_gt_iff Hor).
    now apply rngl_ltb_lt in H12.
  }
}
Qed.

Theorem hangle_opp_inj :
  ∀ θ1 θ2, (- θ1)%H = (- θ2)%H → θ1 = θ2.
Proof.
destruct_hc.
intros * H12.
progress unfold hangle_opp in H12.
injection H12; clear H12; intros H1 H2.
apply (rngl_opp_inj Hop) in H1.
apply eq_hangle_eq.
now rewrite H1, H2.
Qed.

Theorem hangle_lt_irrefl : ∀ θ, ¬ (θ < θ)%H.
Proof.
destruct_hc.
intros * H.
progress unfold hangle_ltb in H.
remember (0 ≤? rngl_sinh θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  apply rngl_ltb_lt in H.
  now apply (rngl_lt_irrefl Hor) in H.
} {
  apply rngl_ltb_lt in H.
  now apply (rngl_lt_irrefl Hor) in H.
}
Qed.

Theorem hangle_le_refl :
  ∀ θ, (θ ≤? θ)%H = true.
Proof.
intros.
destruct_hc.
progress unfold hangle_leb.
remember (0 ≤? rngl_sinh θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs; apply (rngl_leb_refl Hor).
Qed.

Theorem hangle_le_rngl_sinh_nonneg_sinh_nonneg :
  ∀ θ1 θ2,
  (θ1 ≤ θ2)%H
  → (0 ≤ rngl_sinh θ1)%L
  → (0 ≤ rngl_sinh θ2)%L.
Proof.
destruct_hc.
intros * H21 Hzs1.
apply Bool.not_false_iff_true in H21.
apply (rngl_nlt_ge_iff Hto).
intros Hs2z.
apply H21; clear H21.
apply hangle_leb_gt.
progress unfold hangle_ltb.
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply (rngl_leb_gt_iff Hor) in Hs2z.
now rewrite Hs2z.
Qed.

Theorem rngl_cosh_opp : ∀ θ, rngl_cosh (- θ) = rngl_cosh θ.
Proof. easy. Qed.

Theorem rngl_sinh_opp : ∀ θ, rngl_sinh (- θ) = (- rngl_sinh θ)%L.
Proof. easy. Qed.

Theorem hangle_add_add_swap :
  ∀ θ1 θ2 θ3, (θ1 + θ2 + θ3)%H = (θ1 + θ3 + θ2)%H.
Proof.
intros.
do 2 rewrite <- hangle_add_assoc.
f_equal.
apply hangle_add_comm.
Qed.

Theorem hangle_sub_sub_swap :
  ∀ θ1 θ2 θ3, (θ1 - θ2 - θ3 = θ1 - θ3 - θ2)%H.
Proof.
intros.
progress unfold hangle_sub.
apply hangle_add_add_swap.
Qed.

Theorem rngl_cosh_sub_comm :
  ∀ θ1 θ2, rngl_cosh (θ1 - θ2) = rngl_cosh (θ2 - θ1).
Proof.
destruct_hc.
intros; cbn.
rewrite (rngl_mul_comm Hic).
f_equal.
do 2 rewrite (rngl_mul_opp_r Hop).
f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem hangle_sub_opp_r :
  ∀ θ1 θ2, (θ1 - - θ2)%H = (θ1 + θ2)%H.
Proof.
destruct_hc.
intros.
apply eq_hangle_eq; cbn.
now rewrite (rngl_opp_involutive Hop).
Qed.

Theorem hangle_add_sub_swap :
  ∀ θ1 θ2 θ3, (θ1 + θ2 - θ3 = θ1 - θ3 + θ2)%H.
Proof.
intros.
apply hangle_add_add_swap.
Qed.

Theorem hangle_add_sub_assoc :
  ∀ θ1 θ2 θ3, (θ1 + (θ2 - θ3))%H = (θ1 + θ2 - θ3)%H.
Proof.
intros.
progress unfold hangle_sub.
apply hangle_add_assoc.
Qed.

Theorem hangle_eqb_eq :
  ∀ θ1 θ2 : hangle T, (θ1 =? θ2)%H = true ↔ θ1 = θ2.
Proof.
destruct_hc.
intros.
split; intros H12. {
  progress unfold hangle_eqb in H12.
  apply Bool.andb_true_iff in H12.
  destruct H12 as (Hc12, Hs12).
  apply (rngl_eqb_eq Heo) in Hc12, Hs12.
  apply eq_hangle_eq.
  now rewrite Hc12, Hs12.
} {
  subst θ2.
  progress unfold hangle_eqb.
  now do 2 rewrite (rngl_eqb_refl Heo).
}
Qed.

Theorem hangle_eqb_neq :
  ∀ θ1 θ2, (θ1 =? θ2)%H = false ↔ θ1 ≠ θ2.
Proof.
destruct_hc.
intros.
progress unfold hangle_eqb.
split; intros H12. {
  intros H; subst θ2.
  now do 2 rewrite (rngl_eqb_refl Heo) in H12.
} {
  apply Bool.not_true_iff_false.
  intros H; apply H12; clear H12.
  apply eq_hangle_eq; cbn.
  apply Bool.andb_true_iff in H.
  destruct H as (Hc, Hs).
  apply (rngl_eqb_eq Heo) in Hc, Hs.
  now rewrite Hc, Hs.
}
Qed.

Theorem hangle_eq_dec : ∀ θ1 θ2 : hangle T, {θ1 = θ2} + {θ1 ≠ θ2}.
Proof.
intros.
remember (θ1 =? θ2)%H as tt eqn:Htt.
symmetry in Htt.
destruct tt. {
  now left; apply hangle_eqb_eq in Htt.
} {
  now right; apply hangle_eqb_neq in Htt.
}
Qed.

Theorem hangle_mul_add_distr_r :
  ∀ a b θ, ((a + b) * θ = a * θ + b * θ)%H.
Proof.
intros.
induction a; cbn; [ symmetry; apply hangle_add_0_l | ].
rewrite IHa.
apply hangle_add_assoc.
Qed.

Theorem hangle_sub_add_distr :
  ∀ θ1 θ2 θ3, (θ1 - (θ2 + θ3))%H = (θ1 - θ2 - θ3)%H.
Proof.
intros.
progress unfold hangle_sub.
rewrite hangle_opp_add_distr.
progress unfold hangle_sub.
rewrite hangle_add_assoc.
apply hangle_add_add_swap.
Qed.

Theorem hangle_mul_sub_distr_r :
  ∀ a b θ, b ≤ a → ((a - b) * θ = a * θ - b * θ)%H.
Proof.
intros * Hba.
revert b Hba.
induction a; intros. {
  apply Nat.le_0_r in Hba; subst b; cbn.
  symmetry.
  apply hangle_sub_diag.
}
destruct b; [ now rewrite hangle_sub_0_r | ].
apply Nat.succ_le_mono in Hba.
rewrite Nat.sub_succ.
rewrite IHa; [ cbn | easy ].
rewrite hangle_sub_add_distr.
rewrite hangle_add_comm.
now rewrite hangle_add_sub.
Qed.

Theorem hangle_add_move_0_r : ∀ θ1 θ2, (θ1 + θ2 = 0 ↔ θ1 = (- θ2))%H.
Proof.
destruct_hc.
intros.
split; intros H12. {
  rewrite <- hangle_sub_0_l.
  rewrite <- H12; symmetry.
  apply hangle_add_sub.
} {
  subst θ1.
  rewrite hangle_add_opp_l.
  apply hangle_sub_diag.
}
Qed.

Theorem hangle_0_div_2 : (0 /₂ = 0)%H.
Proof.
destruct_hc.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_hangle_0 Hc1) as H1.
  apply H1.
}
apply eq_hangle_eq; cbn.
rewrite (rngl_leb_refl Hor).
rewrite rngl_mul_1_l.
rewrite (rngl_div_diag Hiq). 2: {
  apply (rngl_2_neq_0 Hos Hc1 Hto).
}
rewrite (rl_sqrt_1 Hop Hiq Hor).
f_equal.
rewrite (rngl_sub_diag Hos).
rewrite (rngl_div_0_l Hos Hi1). 2: {
  apply (rngl_2_neq_0 Hos Hc1 Hto).
}
apply (rl_sqrt_0 Hop Hto).
rewrite Bool.orb_true_iff; right.
apply (rngl_has_inv_has_inv_or_pdiv Hiv).
Qed.

Theorem hangle_opp_0 : (- 0)%H = 0%H.
Proof.
destruct_hc.
apply eq_hangle_eq.
cbn; f_equal.
apply (rngl_opp_0 Hop).
Qed.

(* euclidean distance *)

Definition hangle_eucl_dist θ1 θ2 :=
  rl_modl (rngl_cosh θ2 - rngl_cosh θ1) (rngl_sinh θ2 - rngl_sinh θ1).

Theorem hangle_eucl_dist_symmetry :
  ∀ θ1 θ2, hangle_eucl_dist θ1 θ2 = hangle_eucl_dist θ2 θ1.
Proof.
destruct_hc.
intros.
progress unfold hangle_eucl_dist.
progress unfold rl_modl.
f_equal; rewrite (rngl_squ_sub_comm Hop).
f_equal; rewrite (rngl_squ_sub_comm Hop).
easy.
Qed.

Theorem hangle_eucl_dist_separation :
  ∀ θ1 θ2, hangle_eucl_dist θ1 θ2 = 0%L ↔ θ1 = θ2.
Proof.
destruct_hc.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hi1.
intros *.
progress unfold hangle_eucl_dist.
progress unfold rl_modl.
split; intros H12. 2: {
  subst θ2.
  do 2 rewrite (rngl_sub_diag Hos).
  rewrite (rngl_squ_0 Hos).
  rewrite rngl_add_0_r.
  apply (rl_sqrt_0 Hop Hto Hii).
}
apply eq_hangle_eq.
apply (eq_rl_sqrt_0 Hos) in H12. 2: {
  apply (rngl_add_squ_nonneg Hos Hto).
}
apply (rngl_eq_add_0 Hor) in H12; cycle 1. {
  apply (rngl_squ_nonneg Hos Hto).
} {
  apply (rngl_squ_nonneg Hos Hto).
}
destruct H12 as (Hc, Hs).
apply (eq_rngl_squ_0 Hos) in Hc, Hs; cycle 1. {
  rewrite Bool.orb_true_iff; right.
  rewrite Hi1; cbn.
  apply (rngl_has_eq_dec_or_is_ordered_r Hor).
} {
  rewrite Bool.orb_true_iff; right.
  rewrite Hi1; cbn.
  apply (rngl_has_eq_dec_or_is_ordered_r Hor).
}
apply -> (rngl_sub_move_0_r Hop) in Hc.
apply -> (rngl_sub_move_0_r Hop) in Hs.
now rewrite Hc, Hs.
Qed.

Theorem hangle_eucl_dist_triangular :
  ∀ θ1 θ2 θ3,
  (hangle_eucl_dist θ1 θ3 ≤ hangle_eucl_dist θ1 θ2 + hangle_eucl_dist θ2 θ3)%L.
Proof.
intros *.
destruct_hc.
destruct θ1 as (c1, s1, Hcs1).
destruct θ2 as (c2, s2, Hcs2).
destruct θ3 as (c3, s3, Hcs3).
progress unfold hangle_eucl_dist.
cbn.
apply (euclidean_distance_triangular Hic Hop Hiv Hto).
Qed.

Theorem hangle_eucl_dist_is_dist : is_dist hangle_eucl_dist.
Proof.
intros.
split. {
  apply hangle_eucl_dist_symmetry.
} {
  apply hangle_eucl_dist_separation.
} {
  apply hangle_eucl_dist_triangular.
}
Qed.

(* taxicab distance *)

Definition hangle_taxi_dist θ1 θ2 :=
  (rngl_abs (rngl_cosh θ2 - rngl_cosh θ1) +
   rngl_abs (rngl_sinh θ2 - rngl_sinh θ1))%L.

Theorem hangle_taxi_dist_symmetry :
  ∀ θ1 θ2, hangle_taxi_dist θ1 θ2 = hangle_taxi_dist θ2 θ1.
Proof.
destruct_hc; intros.
progress unfold hangle_taxi_dist.
rewrite (rngl_abs_sub_comm Hop Hto).
f_equal.
apply (rngl_abs_sub_comm Hop Hto).
Qed.

Theorem hangle_taxi_dist_separation :
  ∀ θ1 θ2, hangle_taxi_dist θ1 θ2 = 0%L ↔ θ1 = θ2.
Proof.
destruct_hc; intros.
progress unfold hangle_taxi_dist.
split; intros H12. {
  apply (rngl_eq_add_0 Hor) in H12; cycle 1.
  apply (rngl_abs_nonneg Hop Hto).
  apply (rngl_abs_nonneg Hop Hto).
  destruct H12 as (Hcc, Hss).
  apply (eq_rngl_abs_0 Hop) in Hcc, Hss.
  apply -> (rngl_sub_move_0_r Hop) in Hcc.
  apply -> (rngl_sub_move_0_r Hop) in Hss.
  apply eq_hangle_eq.
  now rewrite Hcc, Hss.
} {
  subst θ2.
  do 2 rewrite (rngl_sub_diag Hos).
  rewrite (rngl_abs_0 Hop).
  apply rngl_add_0_l.
}
Qed.

Theorem hangle_taxi_dist_triangular :
  ∀ θ1 θ2 θ3,
  (hangle_taxi_dist θ1 θ3 ≤ hangle_taxi_dist θ1 θ2 + hangle_taxi_dist θ2 θ3)%L.
Proof.
destruct_hc; intros.
destruct θ1 as (c1, s1, Hcs1).
destruct θ2 as (c2, s2, Hcs2).
destruct θ3 as (c3, s3, Hcs3).
progress unfold hangle_taxi_dist.
cbn.
specialize (rngl_abs_triangle Hop Hto) as H1.
rewrite rngl_add_assoc.
rewrite (rngl_add_add_swap (rngl_abs (c2 - c1))).
rewrite <- rngl_add_assoc.
apply (rngl_add_le_mono Hos Hor). {
  eapply (rngl_le_trans Hor); [ | apply H1 ].
  rewrite rngl_add_comm.
  rewrite (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_add Hop).
  apply (rngl_le_refl Hor).
} {
  eapply (rngl_le_trans Hor); [ | apply H1 ].
  rewrite rngl_add_comm.
  rewrite (rngl_add_sub_assoc Hop).
  rewrite (rngl_sub_add Hop).
  apply (rngl_le_refl Hor).
}
Qed.

Theorem hangle_taxi_dist_is_dist : is_dist hangle_taxi_dist.
Proof.
split. {
  apply hangle_taxi_dist_symmetry.
} {
  apply hangle_taxi_dist_separation.
} {
  apply hangle_taxi_dist_triangular.
}
Qed.

End a.

Require Import TrigoWithoutPi.AngleDef.
Require Import TrigoWithoutPi.Angle.
Require Import TrigoWithoutPi.AngleDiv2.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.
Context {hc : hangle_ctx T}.

(* trying to define an exponential *)

Definition rngl_exph (a : hangle T) : T := (rngl_cosh a + rngl_sinh a)%L.

Theorem rngl_exph_add :
  ∀ a b, rngl_exph (a + b) = (rngl_exph a * rngl_exph b)%L.
Proof.
intros.
progress unfold rngl_exph.
cbn.
rewrite rngl_mul_add_distr_l.
do 2 rewrite rngl_mul_add_distr_r.
do 2 rewrite <- rngl_add_assoc.
f_equal.
rewrite rngl_add_comm.
rewrite <- rngl_add_assoc.
easy.
Qed.

Theorem rngl_exph_0 : rngl_exph 0 = 1%L.
Proof. apply rngl_add_0_r. Qed.

(* tracing a line from O to the right, less than 45°, we intersect
   the unit circle and the hyperbole once. This is how I convert an
   angle to a hyperbolic angle. *)
Theorem hangle_of_angle_prop :
  ∀ θ,
  let θ2 :=
    if (0 ≤? rngl_sin θ)%L then (θ /₂)%A
    else (- (- θ /₂))%A
  in
  (0 <? rngl_cos θ)%L = true
  → let d := √(rngl_cos θ) in
     cosh2_sinh2_prop (rngl_cos θ2 / d) (rngl_sin θ2 / d).
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hzc *.
  apply rngl_ltb_lt in Hzc.
  rewrite H1 in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
intros * Hzc.
apply rngl_ltb_lt in Hzc.
progress unfold cosh2_sinh2_prop.
apply Bool.andb_true_iff.
set (d := √(rngl_cos θ)).
assert (Hzcr : (0 ≤ rngl_cos θ2 / d)%L). {
  subst θ2.
  remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
  symmetry in Hzs.
  destruct zs. {
    cbn; rewrite Hzs, rngl_mul_1_l.
    apply (rngl_div_nonneg Hop Hiv Hto). {
      apply rl_sqrt_nonneg.
      apply rngl_1_add_cos_div_2_nonneg.
    }
    subst d.
    now apply (rl_sqrt_pos Hos Hor).
  } {
    cbn.
    rewrite (rngl_leb_0_opp Hop Hto).
    apply (rngl_leb_gt_iff Hor) in Hzs.
    apply (rngl_lt_le_incl Hor) in Hzs.
    apply rngl_leb_le in Hzs.
    rewrite Hzs, rngl_mul_1_l.
    apply (rngl_div_nonneg Hop Hiv Hto). {
      apply rl_sqrt_nonneg.
      apply rngl_1_add_cos_div_2_nonneg.
    }
    subst d.
    now apply (rl_sqrt_pos Hos Hor).
  }
}
split; [ | now apply rngl_leb_le ].
apply (rngl_eqb_eq Heo).
subst d; cbn.
rewrite (rngl_squ_div Hic Hos Hiv). 2: {
  intros H.
  apply (eq_rl_sqrt_0 Hos) in H; [ | now apply (rngl_lt_le_incl Hto) ].
  rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
rewrite (rngl_squ_div Hic Hos Hiv). 2: {
  intros H.
  apply (eq_rl_sqrt_0 Hos) in H; [ | now apply (rngl_lt_le_incl Hto) ].
  rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
rewrite <- (rngl_div_sub_distr_r Hop Hiv).
rewrite rngl_squ_sqrt; [ | now apply (rngl_lt_le_incl Hor)].
specialize (cos2_sin2_1 θ2) as H1.
apply (rngl_add_sub_eq_l Hos) in H1.
rewrite <- H1.
rewrite (rngl_sub_sub_distr Hop).
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- rngl_mul_2_r.
unfold θ2.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  cbn; rewrite Hzs, rngl_mul_1_l.
  rewrite rngl_squ_sqrt. 2: {
    apply (rngl_le_div_r Hop Hiv Hor). {
      apply (rngl_0_lt_2 Hos Hc1 Hor).
    }
    rewrite (rngl_mul_0_l Hos).
    apply (rngl_le_opp_l Hop Hor).
    apply rngl_cos_bound.
  }
  rewrite (rngl_div_mul Hiv). 2: {
    apply (rngl_2_neq_0 Hos Hc1 Hto).
  }
  rewrite rngl_add_comm.
  rewrite (rngl_add_sub Hos).
  apply (rngl_div_diag Hiq).
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
} {
  cbn.
  rewrite (rngl_leb_0_opp Hop Hto).
  apply (rngl_leb_gt_iff Hor) in Hzs.
  apply (rngl_lt_le_incl Hor) in Hzs.
  apply rngl_leb_le in Hzs.
  rewrite Hzs, rngl_mul_1_l.
  rewrite rngl_squ_sqrt. 2: {
    apply (rngl_le_div_r Hop Hiv Hor). {
      apply (rngl_0_lt_2 Hos Hc1 Hor).
    }
    rewrite (rngl_mul_0_l Hos).
    apply (rngl_le_opp_l Hop Hor).
    apply rngl_cos_bound.
  }
  rewrite (rngl_div_mul Hiv). 2: {
    apply (rngl_2_neq_0 Hos Hc1 Hto).
  }
  rewrite rngl_add_comm.
  rewrite (rngl_add_sub Hos).
  apply (rngl_div_diag Hiq).
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
Qed.

Definition hangle_of_angle θ :=
  let θ2 :=
    if (0 ≤? rngl_sin θ)%L then (θ /₂)%A
    else (- (- θ /₂))%A
  in
  match rngl_ltb_dec 0 (rngl_cos θ) with
  | left Hzc =>
      let d := √(rngl_cos θ) in
      mk_hangle (rngl_cos θ2 / d) (rngl_sin θ2 / d)
        (hangle_of_angle_prop θ Hzc)
  | right _ =>
      0%H
  end.

Theorem angle_of_hangle_prop :
  ∀ θ,
  let d := √((rngl_cosh θ)² + (rngl_sinh θ)²) in
  let ε := if (0 ≤? rngl_sinh θ)%L then 1%L else (-1)%L in
  cos2_sin2_prop (rngl_cosh θ / d)%L (ε * rngl_sinh θ / d)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  progress unfold cos2_sin2_prop.
  apply (rngl_eqb_eq Heo).
  now rewrite (H1 (_ + _)%L), (H1 1%L).
}
intros.
progress unfold cos2_sin2_prop.
apply (rngl_eqb_eq Heo).
rewrite (rngl_squ_div Hic Hos Hiv). 2: {
  intros H; subst d.
  apply (eq_rl_sqrt_0 Hos) in H. 2: {
    apply (rngl_add_squ_nonneg Hos Hto).
  }
  apply (eq_rngl_add_square_0 Hop Hiq Hor) in H.
  destruct H as (Hc, Hs).
  now apply (eq_rngl_cosh_0 Hc1) in Hc.
}
rewrite (rngl_squ_div Hic Hos Hiv). 2: {
  intros H; subst d.
  apply (eq_rl_sqrt_0 Hos) in H. 2: {
    apply (rngl_add_squ_nonneg Hos Hto).
  }
  apply (eq_rngl_add_square_0 Hop Hiq Hor) in H.
  destruct H as (Hc, Hs).
  now apply (eq_rngl_cosh_0 Hc1) in Hc.
}
rewrite <- (rngl_div_add_distr_r Hiv).
rewrite (rngl_squ_mul Hic).
replace ε² with 1%L. 2: {
  subst ε; symmetry.
  destruct (0 ≤? rngl_sinh θ)%L; [ apply rngl_squ_1 | ].
  apply (rngl_squ_opp_1 Hop).
}
rewrite rngl_mul_1_l.
specialize (cosh2_sinh2_1 θ) as H1.
apply (rngl_sub_move_r Hop) in H1.
progress unfold d.
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_add_squ_nonneg Hos Hto).
}
apply (rngl_div_diag Hiq).
intros H.
apply (eq_rngl_add_square_0 Hop Hiq Hor) in H.
destruct H as (Hc, Hs).
now apply (eq_rngl_cosh_0 Hc1) in Hc.
Qed.

(* cos / sin = cosh / sinh *)
(* c / εsinh √(1-c²) = cosh / sinh *)
(* c² / (1 - c²) = (cosh² / sinh² *)
(* c² = (sinh² - 1) / sinh² * (1 - c²) *)
(* c² = (ch/sh)² - c² (ch/sh)² *)
(* c² (1 + (ch/sh)²) = (ch/sh)² *)
(* c = (ch/sh) / √(1+(ch/sh)²) *)
(* c = ch / √(ch² + sh²)) *)
Definition angle_of_hangle (θ : hangle T) :=
  let d := √((rngl_cosh θ)² + (rngl_sinh θ)²) in
  let ε := if (0 ≤? rngl_sinh θ)%L then 1%L else (-1)%L in
  mk_angle (rngl_cosh θ / d) (ε * rngl_sinh θ / d)
    (angle_of_hangle_prop θ).

Definition rngl_expc (θ : angle T) := rngl_exph (hangle_of_angle θ).

(* to be completed
Theorem rngl_expc_add :
  ∀ a b, rngl_expc (a + b) = (rngl_expc a * rngl_expc b)%L.
Proof.
destruct_ac.
intros.
progress unfold rngl_expc.
progress unfold rngl_exph.
cbn.
rewrite rngl_mul_add_distr_l.
do 2 rewrite rngl_mul_add_distr_r.
progress unfold hangle_of_angle.
destruct (rngl_lt_dec ac_or 0 (rngl_cos a)) as [Hzca| Hzca]. {
  cbn - [ angle_add ].
  destruct (rngl_lt_dec ac_or 0 (rngl_cos b)) as [Hzcb| Hzcb]. {
    cbn - [ angle_add ].
    destruct (rngl_lt_dec ac_or 0 (rngl_cos (a + b))) as [Hzcab| Hzcab]. {
      cbn - [ angle_add ].
      remember (0 ≤? rngl_sin (a + b))%L as zsab eqn:Hzsab.
      symmetry in Hzsab.
      destruct zsab. {
        remember (0 ≤? rngl_sin a)%L as zsa eqn:Hzsa.
        symmetry in Hzsa.
        destruct zsa. {
          remember (0 ≤? rngl_sin b)%L as zsb eqn:Hzsb.
          symmetry in Hzsb.
          destruct zsb. {
            cbn - [ angle_add ].
            rewrite Hzsab, Hzsa, Hzsb.
            do 3 rewrite rngl_mul_1_l.
(*
remember (rngl_cos (a + b)) as cab.
remember (rngl_cos a) as ca.
remember (rngl_cos b) as cb.
*)
            f_equal. {
              cbn.
(* mouais, pas sûr que ça marche *)
(* d'ailleurs, ça m'étonnerait *)
...
        do 2 rewrite <- rngl_add_assoc.
f_equal.
rewrite rngl_add_comm.
rewrite <- rngl_add_assoc.
easy.
Qed.

...

Theorem glop :
  ∀ θ, rngl_cos (angle_of_hangle θ) = rngl_cosh θ.
Proof.
intros.
progress unfold angle_of_hangle.
cbn.
(*
  ============================
  (rngl_cosh θ / √((rngl_cosh θ)² + (rngl_sinh θ)²))%L = rngl_cosh θ

donc, c'est pas la bonne solution.
angle_of_hangle n'est pas bon.
*)
...

Theorem glop :
  ∀ θ, rngl_cosh (hangle_of_angle θ) = rngl_cos θ.
Proof.
destruct_ac.
intros.
progress unfold hangle_of_angle.
destruct (rngl_lt_dec ac_or 0 (rngl_cos θ)) as [Hzc| Hzc]. {
  cbn.
  remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
  symmetry in Hzs.
  destruct zs. {
    cbn.
    rewrite Hzs.
    rewrite rngl_mul_1_l.
...

(* should have the property cos (hangle_mul_i θ) = cosh θ *)

(* en fait, on ne peut pas avoir cos(iθ)=cosh(θ), puisque cosh va
   entre 1 et ∞, tandis que cos(iθ), bin si c'est un cosinus, il
   doit varier entre -1 et 1 *)
(* donc le cos de iθ, c'est pas un cosinus *)
(* donc comment faire le lien entre le cos et le cosh ? *)
(* que veut dire la formule cos(iθ)=cosh(θ) si on veut la typer
   correctement ? *)

...

Definition rngl_ln (a : T) := a.

Theorem rngl_acosh_prop :
  ∀ a, cosh2_sinh2_prop a (rngl_ln (a + √(a² - 1))%L).
...

Definition rngl_acosh (a : T) : hangle T :=
  mk_hangle a (rngl_ln (a + √(a² - 1)))%L (rngl_acosh_prop a).

Definition rngl_exp_1 (a : T) : T :=
  (rngl_cosh (rngl_acosh a) + rngl_sinh (rngl_acosh a))%L.

Definition rngl_exp_2 (a : T) : T :=
  let b := rngl_acosh a in
  (rngl_cosh b + rngl_sinh b)%L.

(e^b+e^(-b))/2 + (e^b-e^(-b)/2) = e^b

Definition rngl_exp (a : T) : T :=
  (a + √(a²-1))%L.

(* bizarre... *)
...
*)

End a.
