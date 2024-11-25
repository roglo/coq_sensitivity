(* experimental
   hyperbolic angles implemented like trigo without π
   but with "x²-y²=1" instead of "x²+y²=1" *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Import List.ListNotations.
Require Import Main.Misc1 Main.RingLike.
Require Import Trigo.RealLike.

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
    hc_on : rngl_has_1 T = true;
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
  set (Hed := hc_ed);
  set (Hor := hc_or);
  specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos;
  specialize hc_on as Hon;
  specialize hc_iv as Hiv;
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
split; [ now apply (rngl_eqb_eq Hed) | ].
now apply rngl_leb_le.
Qed.

Theorem rngl_cosh_proj_bound :
  ∀ c s, cosh2_sinh2_prop c s → (1 ≤ c)%L.
Proof.
destruct_hc.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hcs.
apply cosh2_sinh2_prop_if in Hcs.
destruct Hcs as (Hcs, Hzc).
assert (H : (1 ≤ c²)%L). {
  apply (rngl_sub_move_r Hop) in Hcs.
  rewrite Hcs.
  apply (rngl_le_add_r Hor).
  apply (rngl_squ_nonneg Hos Hor).
}
replace 1%L with 1²%L in H by apply (rngl_mul_1_l Hon).
rewrite <- (rngl_squ_abs Hop c) in H.
rewrite <- (rngl_squ_abs Hop 1%L) in H.
apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in H. 2: {
  apply (rngl_abs_nonneg Hop Hor).
}
rewrite (rngl_abs_1 Hon Hos Hor) in H.
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
now apply (rngl_eqb_eq Hed).
Qed.

Theorem eq_rngl_cosh_0 :
  rngl_characteristic T ≠ 1 →
  ∀ θ, rngl_cosh θ ≠ 0%L.
Proof.
destruct_hc.
intros Hc1.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * H.
specialize (cosh2_sinh2_1 θ) as H1.
rewrite H in H1.
rewrite (rngl_squ_0 Hos) in H1.
apply (rngl_sub_move_l Hop) in H1.
rewrite (rngl_sub_0_l Hop) in H1.
specialize (rngl_squ_nonneg Hos Hor (rngl_sinh θ))%L as H2.
apply rngl_nlt_ge in H2.
apply H2; clear H2.
rewrite H1.
apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
Qed.

Theorem rngl_cosh_nonneg :
  ∀ θ, (0 ≤ rngl_cosh θ)%L.
Proof.
destruct_hc.
intros.
apply (rngl_le_trans Hor _ 1).
apply (rngl_0_le_1 Hon Hos Hor).
apply rngl_cosh_bound.
Qed.

Theorem rngl_cosh_pos :
  rngl_characteristic T ≠ 1 →
  ∀ θ, (0 < rngl_cosh θ)%L.
Proof.
destruct_hc.
intros Hc1 *.
apply (rngl_lt_iff Hor).
split; [ apply rngl_cosh_nonneg | ].
symmetry.
apply (eq_rngl_cosh_0 Hc1).
Qed.

Theorem hangle_zero_prop : (cosh2_sinh2_prop 1 0)%L.
Proof.
destruct_hc.
progress unfold cosh2_sinh2_prop.
progress unfold rngl_squ.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_r Hos).
apply Bool.andb_true_iff.
split; [ apply (rngl_eqb_refl Hed) | ].
apply rngl_leb_le.
apply (rngl_0_le_1 Hon Hos Hor).
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
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
  do 2 rewrite (rngl_squ_add Hic Hon).
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
  apply (rngl_eqb_eq Hed) in Hxy'.
  rewrite Hxy'.
  now do 2 rewrite (rngl_mul_1_r Hon).
}
apply rngl_leb_le.
apply (rngl_eqb_eq Hed) in Hxy, Hxy'.
apply rngl_leb_le in Hzx, Hzx'.
assert (Hyx : (y ≤ x)%L). {
  destruct (rngl_le_dec Hor 0 y) as [Hzy| Hzy]. {
    apply (rngl_le_squ_le Hop Hor Hii); [ easy | easy | ].
    apply (rngl_sub_move_r Hop) in Hxy.
    rewrite Hxy.
    apply (rngl_le_add_l Hor).
    apply (rngl_0_le_1 Hon Hos Hor).
  }
  apply (rngl_nle_gt_iff Hor) in Hzy.
  apply (rngl_lt_le_incl Hor) in Hzy.
  now apply (rngl_le_trans Hor _ 0).
}
assert (Hyx' : (y' ≤ x')%L). {
  destruct (rngl_le_dec Hor 0 y') as [Hzy'| Hzy']. {
    apply (rngl_le_squ_le Hop Hor Hii); [ easy | easy | ].
    apply (rngl_sub_move_r Hop) in Hxy'.
    rewrite Hxy'.
    apply (rngl_le_add_l Hor).
    apply (rngl_0_le_1 Hon Hos Hor).
  }
  apply (rngl_nle_gt_iff Hor) in Hzy'.
  apply (rngl_lt_le_incl Hor) in Hzy'.
  now apply (rngl_le_trans Hor _ 0).
}
destruct (rngl_le_dec Hor 0 y) as [Hzy| Hzy]. {
  destruct (rngl_le_dec Hor 0 y') as [Hzy'| Hzy']. {
    apply (rngl_le_trans Hor _ (y * y' + y * y')). 2: {
      apply (rngl_add_le_mono_r Hop Hor).
      now apply (rngl_mul_le_compat_nonneg Hor).
    }
    rewrite <- (rngl_mul_2_l Hon).
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply (rngl_0_le_2 Hon Hos Hor).
    now apply (rngl_mul_nonneg_nonneg Hos Hor).
  }
  apply (rngl_nle_gt_iff Hor) in Hzy'.
  clear - Hzx' Hyx Hzy Hii Hzy' Hxy' hc Hor Hop Hon Hos.
  apply (rngl_le_trans Hor _ (y * x' + y * y')). 2: {
    apply (rngl_add_le_mono_r Hop Hor).
    now apply (rngl_mul_le_mono_nonneg_r Hop Hor).
  }
  rewrite <- rngl_mul_add_distr_l.
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
  rewrite rngl_add_comm.
  apply (rngl_le_opp_l Hop Hor).
  apply (rngl_le_squ_le Hop Hor Hii); [ | easy | ]. {
    apply (rngl_lt_le_incl Hor) in Hzy'.
    (* todo: rename rngl_opp_nonneg_nonpos into rngl_le_0_opp, perhaps? *)
    now apply (rngl_opp_nonneg_nonpos Hop Hor).
  }
  rewrite (rngl_squ_opp Hop).
  apply (rngl_sub_move_r Hop) in Hxy'.
  rewrite Hxy'.
  apply (rngl_le_add_l Hor).
  apply (rngl_0_le_1 Hon Hos Hor).
}
destruct (rngl_le_dec Hor 0 y') as [Hzy'| Hzy']. {
  apply (rngl_nle_gt_iff Hor) in Hzy.
  apply (rngl_le_trans Hor _ (x * y' + y * y')). 2: {
    apply (rngl_add_le_mono_r Hop Hor).
    now apply (rngl_mul_le_mono_nonneg_l Hop Hor).
  }
  rewrite <- rngl_mul_add_distr_r.
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
  rewrite rngl_add_comm.
  apply (rngl_le_opp_l Hop Hor).
  apply (rngl_le_squ_le Hop Hor Hii); [ | easy | ]. {
    apply (rngl_lt_le_incl Hor) in Hzy.
    (* todo: rename rngl_opp_nonneg_nonpos into rngl_le_0_opp, perhaps? *)
    now apply (rngl_opp_nonneg_nonpos Hop Hor).
  }
  rewrite (rngl_squ_opp Hop).
  apply (rngl_sub_move_r Hop) in Hxy.
  rewrite Hxy.
  apply (rngl_le_add_l Hor).
  apply (rngl_0_le_1 Hon Hos Hor).
}
apply (rngl_nle_gt_iff Hor) in Hzy, Hzy'.
apply (rngl_add_nonneg_nonneg Hor).
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
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
intros.
progress unfold cosh2_sinh2_prop.
assert (Hε : (ε² = 1)%L). {
  progress unfold ε.
  destruct (0 ≤? rngl_sinh a)%L.
  apply (rngl_mul_1_l Hon).
  apply (rngl_squ_opp_1 Hon Hop).
}
rewrite (rngl_squ_mul Hic).
rewrite Hε.
rewrite (rngl_mul_1_l Hon).
apply Bool.andb_true_iff.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  split. {
    apply (rngl_eqb_eq Hed).
    now rewrite (H1 (_ + _)%L), (H1 1%L).
  }
  apply rngl_leb_le.
  rewrite (H1 √_)%L.
  apply (rngl_le_refl Hor).
}
split. 2: {
  apply rngl_leb_le.
  apply rl_sqrt_nonneg.
  apply (rngl_le_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  rewrite (rngl_mul_0_l Hos).
  rewrite rngl_add_comm.
  apply (rngl_le_opp_l Hop Hor).
  apply (rngl_le_trans Hor _ 1); [ | apply rngl_cosh_bound ].
  apply (rngl_opp_1_le_1 Hon Hop Hor).
}
apply (rngl_eqb_eq Hed).
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  rewrite (rngl_mul_0_l Hos).
  rewrite rngl_add_comm.
  apply (rngl_le_opp_l Hop Hor).
  apply (rngl_le_trans Hor _ 1); [ | apply rngl_cosh_bound ].
  apply (rngl_opp_1_le_1 Hon Hop Hor).
}
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
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
apply (rngl_div_diag Hon Hiq).
apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
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
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hza.
  apply eq_hangle_eq.
  do 2 rewrite (H1 (rngl_cosh _)).
  do 2 rewrite (H1 (rngl_sinh _)).
  easy.
}
intros * Hza.
apply eq_hangle_eq.
specialize (rngl_2_neq_0 Hon Hos Hc1 Hor) as H20.
progress unfold hangle_mul_nat.
progress unfold hangle_div_2.
progress unfold hangle_add.
cbn.
destruct (rngl_le_dec hc_or 0 (rngl_cosh a)) as [H| H]; [ | easy ].
cbn; clear H.
do 2 rewrite (rngl_mul_0_r Hos).
do 2 rewrite (rngl_mul_1_r Hon).
do 2 rewrite rngl_add_0_r.
do 2 rewrite fold_rngl_squ.
set (ε := if (0 ≤? rngl_sinh a)%L then 1%L else (-1)%L).
assert (Hε : (ε² = 1)%L). {
  progress unfold ε.
  destruct (0 ≤? rngl_sinh a)%L.
  apply (rngl_mul_1_l Hon).
  apply (rngl_squ_opp_1 Hon Hop).
}
rewrite (rngl_squ_mul Hic).
rewrite Hε.
rewrite (rngl_mul_1_l Hon).
assert (Hz1ac : (0 ≤ rngl_cosh a + 1)%L). {
  apply (rngl_le_sub_le_add_r Hop Hor).
  rewrite (rngl_sub_0_l Hop).
  apply (rngl_le_trans Hor _ 0); [ | easy ].
  apply (rngl_opp_1_le_0 Hon Hop Hor).
}
assert (Hz1sc : (0 ≤ rngl_cosh a - 1)%L). {
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply (rngl_cosh_bound a).
}
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  now rewrite (rngl_mul_0_l Hos).
}
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  now rewrite (rngl_mul_0_l Hos).
}
progress unfold rngl_div.
rewrite Hiv.
rewrite <- rngl_mul_add_distr_r.
rewrite (rngl_add_sub_assoc Hop).
rewrite (rngl_add_sub_swap Hop).
rewrite (rngl_add_sub Hos).
rewrite <- (rngl_mul_2_r Hon).
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_inv_diag_r Hon Hiv); [ | easy ].
rewrite (rngl_mul_1_r Hon); f_equal.
progress unfold rl_sqrt.
rewrite rngl_add_comm.
rewrite (rngl_mul_comm Hic).
rewrite <- (rngl_mul_2_r Hon).
do 2 rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_comm Hic).
rewrite rngl_mul_assoc.
rewrite <- rl_nth_root_mul; cycle 1. {
  rewrite (rngl_mul_inv_r Hiv).
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  now rewrite (rngl_mul_0_l Hos).
} {
  rewrite (rngl_mul_inv_r Hiv).
  apply (rngl_le_div_r Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
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
  apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
}
rewrite rl_nth_root_mul; [ | easy | easy ].
do 2 rewrite rngl_mul_assoc.
rewrite fold_rngl_squ.
rewrite fold_rl_sqrt.
rewrite (rngl_squ_pow_2 Hon).
progress unfold rl_sqrt.
rewrite rl_nth_root_pow; [ | easy ].
rewrite (rngl_mul_comm Hic).
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_inv_diag_l Hon Hiv); [ | easy ].
rewrite (rngl_mul_1_r Hon).
rewrite <- rl_nth_root_mul; [ | easy | easy ].
rewrite (rngl_mul_comm Hic (_ - _)).
rewrite (rngl_squ_sub_squ' Hop).
rewrite (rngl_mul_1_r Hon), (rngl_mul_1_l Hon).
rewrite (rngl_add_sub Hos).
rewrite (rngl_squ_1 Hon).
specialize (cosh2_sinh2_1 a) as H1.
apply (rngl_sub_move_l Hop) in H1.
rewrite <- H1.
rewrite fold_rl_sqrt.
rewrite (rl_sqrt_squ Hon Hop Hor).
progress unfold ε.
remember (0 ≤? rngl_sinh a)%L as saz eqn:Hsaz; symmetry in Hsaz.
destruct saz. {
  apply rngl_leb_le in Hsaz.
  rewrite (rngl_mul_1_l Hon).
  now apply (rngl_abs_nonneg_eq Hop Hor).
} {
  apply (rngl_leb_gt Hor) in Hsaz.
  apply (rngl_lt_le_incl Hor) in Hsaz.
  rewrite (rngl_abs_nonpos_eq Hop Hor); [ | easy ].
  rewrite (rngl_mul_opp_opp Hop).
  apply (rngl_mul_1_l Hon).
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
specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
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
    apply (rngl_ltb_ge_iff Hor) in H.
    now apply rngl_leb_le.
  }
  apply Bool.not_true_iff_false.
  apply rngl_ltb_ge.
  now apply rngl_leb_le.
}
destruct (0 ≤? rngl_sinh θ2)%L; [ easy | ].
split; intros H. {
  apply Bool.not_true_iff_false in H.
  apply (rngl_ltb_ge_iff Hor) in H.
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
    apply (rngl_leb_gt Hor) in H.
    now apply rngl_ltb_lt.
  }
  apply Bool.not_true_iff_false.
  apply (rngl_leb_gt Hor).
  now apply rngl_ltb_lt.
}
destruct (0 ≤? rngl_sinh θ2)%L; [ easy | ].
split; intros H. {
  apply Bool.not_true_iff_false in H.
  apply (rngl_leb_gt Hor) in H.
  now apply rngl_ltb_lt.
}
apply Bool.not_true_iff_false.
apply (rngl_leb_gt Hor).
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
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
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
rewrite <- (rngl_squ_1 Hon) in H1.
destruct H1 as (H1, H2).
apply (rngl_squ_eq_cases Hon Hop Hiv Heo) in H1. 2: {
  rewrite (rngl_mul_1_l Hon).
  apply (rngl_mul_1_r Hon).
}
apply eq_hangle_eq; cbn.
destruct H1; subst c; [ easy | ].
exfalso.
apply rngl_nlt_ge in H2.
apply H2; clear H2.
apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
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
do 2 rewrite (rngl_mul_1_l Hon).
do 2 rewrite (rngl_mul_0_l Hos).
now rewrite rngl_add_0_l, rngl_add_0_r.
Qed.

Theorem hangle_add_0_r : ∀ θ, (θ + 0 = θ)%H.
Proof.
destruct_hc.
intros.
apply eq_hangle_eq; cbn.
do 2 rewrite (rngl_mul_1_r Hon).
do 2 rewrite (rngl_mul_0_r Hos).
now do 2 rewrite rngl_add_0_r.
Qed.

Theorem hangle_sub_0_l :
  ∀ θ, (0 - θ = - θ)%H.
Proof.
destruct_hc.
intros.
apply eq_hangle_eq; cbn.
do 2 rewrite (rngl_mul_1_l Hon).
do 2 rewrite (rngl_mul_0_l Hos).
now rewrite rngl_add_0_l, rngl_add_0_r.
Qed.

Theorem hangle_sub_0_r :
  ∀ θ, (θ - 0 = θ)%H.
Proof.
destruct_hc.
intros.
apply eq_hangle_eq; cbn.
do 2 rewrite (rngl_mul_1_r Hon).
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
apply (hangle_add_0_r).
Qed.

Theorem hangle_sub_add : ∀ θ1 θ2, (θ1 - θ2 + θ2)%H = θ1.
Proof.
destruct_hc; intros.
progress unfold hangle_sub.
rewrite <- hangle_add_assoc.
rewrite hangle_add_opp_diag_l.
apply (hangle_add_0_r).
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hzs1 Hzs2.
specialize (cosh2_sinh2_1 θ1) as Hcs1.
specialize (cosh2_sinh2_1 θ2) as Hcs2.
split. {
  intros Hss.
  apply (rngl_le_le_squ Hop Hor Hii) in Hss; [ | easy ].
  apply (rngl_sub_move_l Hop) in Hcs1, Hcs2.
  rewrite Hcs1, Hcs2 in Hss.
  apply (rngl_sub_le_mono_r Hop Hor) in Hss.
  apply (rngl_le_squ_le Hop Hor Hii) in Hss; [ easy | | ].
  apply rngl_cosh_nonneg.
  apply rngl_cosh_nonneg.
} {
  intros Hcc.
  apply (rngl_le_le_squ Hop Hor Hii) in Hcc; [ | apply rngl_cosh_nonneg ].
  apply (rngl_sub_move_r Hop) in Hcs1, Hcs2.
  rewrite Hcs1, Hcs2 in Hcc.
  apply (rngl_add_le_mono_l Hop Hor) in Hcc.
  now apply (rngl_le_squ_le Hop Hor Hii) in Hcc.
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hzs1 Hzs2.
specialize (cosh2_sinh2_1 θ1) as Hcs1.
specialize (cosh2_sinh2_1 θ2) as Hcs2.
split. {
  intros Hss.
  apply (rngl_lt_lt_squ Hop Hor Hii) in Hss; [ | | easy ]. 2: {
    apply (rngl_mul_comm Hic).
  }
  apply (rngl_sub_move_l Hop) in Hcs1, Hcs2.
  rewrite Hcs1, Hcs2 in Hss.
  apply (rngl_sub_lt_mono_r Hop Hor) in Hss.
  apply (rngl_lt_squ_lt Hop Hor Hii) in Hss; [ easy | | ].
  apply rngl_cosh_nonneg.
  apply rngl_cosh_nonneg.
} {
  intros Hcc.
  apply (rngl_lt_lt_squ Hop Hor Hii) in Hcc; cycle 1. {
    apply (rngl_mul_comm Hic).
  } {
    apply rngl_cosh_nonneg.
  }
  apply (rngl_sub_move_r Hop) in Hcs1, Hcs2.
  rewrite Hcs1, Hcs2 in Hcc.
  apply (rngl_add_lt_mono_l Hop Hor) in Hcc.
  now apply (rngl_lt_squ_lt Hop Hor Hii) in Hcc.
}
Qed.

Theorem eq_rngl_cosh_1 : ∀ θ, rngl_cosh θ = 1%L ↔ θ = 0%H.
Proof.
destruct_hc.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
intros.
split; intros Hθ; [ | now subst θ ].
specialize (cosh2_sinh2_1 θ) as H1.
rewrite Hθ in H1.
rewrite (rngl_squ_1 Hon) in H1.
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
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Hcc.
destruct (rngl_eq_dec Heo (rngl_sinh θ1) (rngl_sinh θ2)) as [Hss| Hss]. {
  left.
  apply eq_hangle_eq.
  now rewrite Hcc, Hss.
}
right.
apply eq_hangle_eq.
rewrite Hcc; f_equal.
cbn.
specialize (cosh2_sinh2_1 θ1) as H1.
specialize (cosh2_sinh2_1 θ2) as H2.
apply (rngl_sub_move_l Hop) in H1, H2.
rewrite Hcc in H1.
rewrite <- H2 in H1; clear H2.
apply (eq_rngl_squ_rngl_abs Hop Hor) in H1; cycle 1. {
  apply Bool.orb_true_iff; right.
  apply (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv).
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
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_hangle_0 Hc1) as H1.
  intros.
  now rewrite (H1 θ1), (H1 θ2).
}
intros * Hss.
destruct (rngl_eq_dec Heo (rngl_cosh θ1) (rngl_cosh θ2)) as [Hcc| Hcc]. {
  apply eq_hangle_eq.
  now rewrite Hcc, Hss.
}
apply eq_hangle_eq.
exfalso; apply Hcc; clear Hcc.
specialize (cosh2_sinh2_1 θ1) as H1.
specialize (cosh2_sinh2_1 θ2) as H2.
apply (rngl_sub_move_r Hop) in H1, H2.
rewrite Hss in H1.
rewrite <- H2 in H1; clear H2.
apply (eq_rngl_squ_rngl_abs Hop Hor Hii) in H1. 2: {
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
apply (rngl_add_nonneg_nonneg Hor); apply rngl_cosh_nonneg.
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
    apply (rngl_leb_gt Hor) in H12.
    now apply rngl_ltb_lt.
  } {
    apply (rngl_leb_gt Hor).
    now apply rngl_ltb_lt in H12.
  }
} {
  apply (rngl_leb_gt Hor) in Hzs1.
  destruct zs2; [ easy | ].
  split; intros H12. {
    apply (rngl_leb_gt Hor) in H12.
    now apply rngl_ltb_lt.
  } {
    apply (rngl_leb_gt Hor).
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
apply (rngl_nlt_ge_iff Hor).
intros Hs2z.
apply H21; clear H21.
apply hangle_leb_gt.
progress unfold hangle_ltb.
apply rngl_leb_le in Hzs1.
rewrite Hzs1.
apply (rngl_leb_gt Hor) in Hs2z.
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
  apply (rngl_eqb_eq Hed) in Hc12, Hs12.
  apply eq_hangle_eq.
  now rewrite Hc12, Hs12.
} {
  subst θ2.
  progress unfold hangle_eqb.
  now do 2 rewrite (rngl_eqb_refl Hed).
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
  now do 2 rewrite (rngl_eqb_refl Hed) in H12.
} {
  apply Bool.not_true_iff_false.
  intros H; apply H12; clear H12.
  apply eq_hangle_eq; cbn.
  apply Bool.andb_true_iff in H.
  destruct H as (Hc, Hs).
  apply (rngl_eqb_eq Hed) in Hc, Hs.
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
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_hangle_0 Hc1) as H1.
  apply H1.
}
apply eq_hangle_eq; cbn.
rewrite (rngl_leb_refl Hor).
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_div_diag Hon Hiq). 2: {
  apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
}
rewrite (rl_sqrt_1 Hon Hop Hor). 2: {
  rewrite Bool.orb_true_iff; right.
  apply (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv).
}
f_equal.
rewrite (rngl_sub_diag Hos).
rewrite (rngl_div_0_l Hos Hi1). 2: {
  apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
}
apply (rl_sqrt_0 Hon Hop Hor).
rewrite Bool.orb_true_iff; right.
apply (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv).
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
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_1_or_quot_r Hon Hiq) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
intros *.
progress unfold hangle_eucl_dist.
progress unfold rl_modl.
split; intros H12. 2: {
  subst θ2.
  do 2 rewrite (rngl_sub_diag Hos).
  rewrite (rngl_squ_0 Hos).
  rewrite rngl_add_0_r.
  apply (rl_sqrt_0 Hon Hop Hor Hii).
}
apply eq_hangle_eq.
apply (eq_rl_sqrt_0 Hon Hos) in H12. 2: {
  apply (rngl_add_squ_nonneg Hos Hor).
}
apply (rngl_eq_add_0 Hor) in H12; cycle 1. {
  apply (rngl_squ_nonneg Hos Hor).
} {
  apply (rngl_squ_nonneg Hos Hor).
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
apply (euclidean_distance_triangular Hic Hon Hop Hiv Hor).
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
rewrite (rngl_abs_sub_comm Hop Hor).
f_equal.
apply (rngl_abs_sub_comm Hop Hor).
Qed.

Theorem hangle_taxi_dist_separation :
  ∀ θ1 θ2, hangle_taxi_dist θ1 θ2 = 0%L ↔ θ1 = θ2.
Proof.
destruct_hc; intros.
progress unfold hangle_taxi_dist.
split; intros H12. {
  apply (rngl_eq_add_0 Hor) in H12; cycle 1.
  apply (rngl_abs_nonneg Hop Hor).
  apply (rngl_abs_nonneg Hop Hor).
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
specialize (rngl_abs_triangle Hop Hor) as H1.
Search (rngl_abs _ - rngl_abs _)%L.
rewrite rngl_add_assoc.
rewrite (rngl_add_add_swap (rngl_abs (c2 - c1))).
rewrite <- rngl_add_assoc.
apply (rngl_add_le_compat Hor). {
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

Require Import Trigo.Angle.
Require Import Trigo.AngleDiv2.

(* voir si vraiment utiles *)
Require Import Trigo.TacChangeAngle.
Require Import Trigo.AngleDiv2Add.
Require Import Trigo.AngleDivNat.
Require Import Trigo.SeqAngleIsCauchy.
Require Import Trigo.TrigoWithoutPiExt.
Require Import Trigo.Angle_order.
Require Import Trigo.AngleAddLeMonoL.

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
  (0 < rngl_cos θ)%L
  → let d := √(rngl_cos θ) in
     cosh2_sinh2_prop (rngl_cos θ2 / d) (rngl_sin θ2 / d).
Proof.
destruct_ac.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hzc *.
  rewrite H1 in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
intros * Hzc.
progress unfold cosh2_sinh2_prop.
apply Bool.andb_true_iff.
set (d := √(rngl_cos θ)).
assert (Hzcr : (0 ≤ rngl_cos θ2 / d)%L). {
  subst θ2.
  remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
  symmetry in Hzs.
  destruct zs. {
    cbn; rewrite Hzs, (rngl_mul_1_l Hon).
    apply (rngl_div_nonneg Hon Hop Hiv Hor). {
      apply rl_sqrt_nonneg.
      apply rngl_1_add_cos_div_2_nonneg.
    }
    subst d.
    now apply (rl_sqrt_pos Hon Hos Hor).
  } {
    cbn.
    rewrite (rngl_leb_0_opp Hop Hor).
    apply (rngl_leb_gt Hor) in Hzs.
    apply (rngl_lt_le_incl Hor) in Hzs.
    apply rngl_leb_le in Hzs.
    rewrite Hzs, (rngl_mul_1_l Hon).
    apply (rngl_div_nonneg Hon Hop Hiv Hor). {
      apply rl_sqrt_nonneg.
      apply rngl_1_add_cos_div_2_nonneg.
    }
    subst d.
    now apply (rl_sqrt_pos Hon Hos Hor).
  }
}
split; [ | now apply rngl_leb_le ].
apply (rngl_eqb_eq Hed).
subst d; cbn.
rewrite (rngl_squ_div Hic Hon Hos Hiv). 2: {
  intros H.
  apply (eq_rl_sqrt_0 Hon Hos) in H; [ | now apply (rngl_lt_le_incl Hor) ].
  rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
rewrite (rngl_squ_div Hic Hon Hos Hiv). 2: {
  intros H.
  apply (eq_rl_sqrt_0 Hon Hos) in H; [ | now apply (rngl_lt_le_incl Hor) ].
  rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
rewrite <- (rngl_div_sub_distr_r Hop Hiv).
rewrite (rngl_squ_sqrt Hon); [ | now apply (rngl_lt_le_incl Hor)].
specialize (cos2_sin2_1 θ2) as H1.
apply (rngl_add_sub_eq_l Hos) in H1.
rewrite <- H1.
rewrite (rngl_sub_sub_distr Hop).
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- (rngl_mul_2_r Hon).
unfold θ2.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  cbn; rewrite Hzs, (rngl_mul_1_l Hon).
  rewrite (rngl_squ_sqrt Hon). 2: {
    apply (rngl_le_div_r Hon Hop Hiv Hor). {
      apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
    }
    rewrite (rngl_mul_0_l Hos).
    apply (rngl_le_opp_l Hop Hor).
    apply rngl_cos_bound.
  }
  rewrite (rngl_div_mul Hon Hiv). 2: {
    apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
  }
  rewrite rngl_add_comm.
  rewrite (rngl_add_sub Hos).
  apply (rngl_div_diag Hon Hiq).
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
} {
  cbn.
  rewrite (rngl_leb_0_opp Hop Hor).
  apply (rngl_leb_gt Hor) in Hzs.
  apply (rngl_lt_le_incl Hor) in Hzs.
  apply rngl_leb_le in Hzs.
  rewrite Hzs, (rngl_mul_1_l Hon).
  rewrite (rngl_squ_sqrt Hon). 2: {
    apply (rngl_le_div_r Hon Hop Hiv Hor). {
      apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
    }
    rewrite (rngl_mul_0_l Hos).
    apply (rngl_le_opp_l Hop Hor).
    apply rngl_cos_bound.
  }
  rewrite (rngl_div_mul Hon Hiv). 2: {
    apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
  }
  rewrite rngl_add_comm.
  rewrite (rngl_add_sub Hos).
  apply (rngl_div_diag Hon Hiq).
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
Qed.

Definition hangle_of_angle θ :=
  let θ2 :=
    if (0 ≤? rngl_sin θ)%L then (θ /₂)%A
    else (- (- θ /₂))%A
  in
  match rngl_lt_dec ac_or 0 (rngl_cos θ) with
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
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  progress unfold cos2_sin2_prop.
  apply (rngl_eqb_eq Hed).
  now rewrite (H1 (_ + _)%L), (H1 1%L).
}
intros.
progress unfold cos2_sin2_prop.
apply (rngl_eqb_eq Hed).
rewrite (rngl_squ_div Hic Hon Hos Hiv). 2: {
  intros H; subst d.
  apply (eq_rl_sqrt_0 Hon Hos) in H. 2: {
    apply (rngl_add_squ_nonneg Hos Hor).
  }
  apply (eq_rngl_add_square_0 Hos Hor Hii) in H.
  destruct H as (Hc, Hs).
  now apply (eq_rngl_cosh_0 Hc1) in Hc.
}
rewrite (rngl_squ_div Hic Hon Hos Hiv). 2: {
  intros H; subst d.
  apply (eq_rl_sqrt_0 Hon Hos) in H. 2: {
    apply (rngl_add_squ_nonneg Hos Hor).
  }
  apply (eq_rngl_add_square_0 Hos Hor Hii) in H.
  destruct H as (Hc, Hs).
  now apply (eq_rngl_cosh_0 Hc1) in Hc.
}
rewrite <- (rngl_div_add_distr_r Hiv).
rewrite (rngl_squ_mul Hic).
replace ε² with 1%L. 2: {
  subst ε; symmetry.
  destruct (0 ≤? rngl_sinh θ)%L; [ apply (rngl_squ_1 Hon) | ].
  apply (rngl_squ_opp_1 Hon Hop).
}
rewrite (rngl_mul_1_l Hon).
specialize (cosh2_sinh2_1 θ) as H1.
apply (rngl_sub_move_r Hop) in H1.
progress unfold d.
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_add_squ_nonneg Hos Hor).
}
apply (rngl_div_diag Hon Hiq).
intros H.
apply (eq_rngl_add_square_0 Hos Hor Hii) in H.
destruct H as (Hc, Hs).
now apply (eq_rngl_cosh_0 Hc1) in Hc.
Qed.

(* cos / sin = cosh / sinh *)
(* c / ε(sinh) √(1-c²) = cosh / sinh *)
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

(* *)

Theorem rngl_cos_straight : rngl_cos angle_straight = (-1)%L.
Proof. easy. Qed.

Theorem angle_add_overflow_opp_r_eq :
  ∀ p q, angle_add_overflow p (- q) = ((q ≠? 0)%A && (q ≤? p)%A)%bool.
Proof.
destruct_ac.
intros.
rewrite angle_add_overflow_comm.
progress unfold angle_add_overflow.
rewrite angle_opp_involutive.
f_equal.
(* lemma *)
f_equal.
progress unfold angle_eqb.
cbn.
f_equal.
remember (rngl_sin q =? 0)%L as qz eqn:Hqz.
symmetry in Hqz.
destruct qz. {
  apply (rngl_eqb_eq Hed) in Hqz.
  rewrite Hqz.
  rewrite (rngl_opp_0 Hop).
  apply (rngl_eqb_refl Hed).
}
apply (rngl_eqb_neq Hed) in Hqz.
apply (rngl_eqb_neq Hed).
intros H; apply Hqz; clear Hqz.
apply (f_equal rngl_opp) in H.
now rewrite (rngl_opp_involutive Hop), (rngl_opp_0 Hop) in H.
Qed.

(* to be completed
Theorem rngl_cos_add_cos :
  ∀ p q,
  let c₁ := if angle_add_overflow p q then angle_straight else 0%A in
  let c₂ := if (p <? q)%A then angle_straight else 0%A in
  (rngl_cos p + rngl_cos q =
     2 * rngl_cos ((p + q) /₂ + c₁) * rngl_cos ((p - q) /₂ + c₂))%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ * _))%L.
  apply H1.
}
intros.
remember (angle_add_overflow p q) as opq eqn:Hopq.
remember (angle_add_overflow p (- q)) as opo eqn:Hopo.
symmetry in Hopq, Hopo.
rewrite angle_add_overflow_opp_r_eq in Hopo.
destruct opq. {
  subst c₁.
  rewrite rngl_cos_add_straight_r.
  rewrite (rngl_mul_opp_r Hop).
  destruct opo. {
    subst c₂.
    apply Bool.andb_true_iff in Hopo.
    destruct Hopo as (Hqz, Hqp).
Search ((_ ≤? _)%A = false).
Search ((_ <? _)%A = false).
...
    rewrite angle_ltb_ge in Hqp.
...
    progress unfold angle_add_overflow in Hopq, Hopo.
    apply Bool.andb_true_iff in Hopq, Hopo.
    destruct Hopq as (Hpz, Hopq).
    destruct Hopo as (_, Hopo).
    apply angle_neqb_neq in Hpz.
    progress unfold angle_leb in Hopq, Hopo.
    cbn in Hopq, Hopo.
    rewrite (rngl_leb_0_opp Hop Hor) in Hopq, Hopo.
    rewrite (rngl_leb_0_opp Hop Hor) in Hopo.
    remember (0 ≤? rngl_sin q)%L as zsq eqn:Hzsq.
    remember (rngl_sin q ≤? 0)%L as zqs eqn:Hzqs.
    remember (rngl_sin p ≤? 0)%L as zps eqn:Hzps.
    symmetry in Hzsq, Hzps, Hzqs.
    destruct zsq. {
      destruct zps; [ | easy ].
      apply rngl_leb_le in Hopq.
      clear Hopo.
      destruct zqs. {
        apply rngl_leb_le in Hzsq, Hzqs, Hzps.
        apply (rngl_le_antisymm Hor) in Hzsq; [ clear Hzqs | easy ].
        apply eq_rngl_sin_0 in Hzsq.
        destruct Hzsq; subst q. {
          cbn in Hopq.
          apply rngl_nlt_ge in Hopq.
          exfalso.
          apply Hopq; clear Hopq.
          apply (rngl_lt_iff Hor).
          split; [ apply rngl_cos_bound | ].
          intros H.
          now apply eq_rngl_cos_1 in H.
        }
        clear Hopq.
        rewrite <- angle_add_opp_r.
        rewrite angle_opp_straight.
        rewrite rngl_cos_straight.
        rewrite (rngl_add_opp_r Hop).
        rewrite rngl_cos_add_straight_r.
        rewrite (rngl_mul_opp_r Hop).
        rewrite (rngl_mul_opp_l Hop).
        rewrite (rngl_opp_involutive Hop).
        rewrite <- rngl_mul_assoc.
        rewrite fold_rngl_squ.
        rewrite angle_div_2_add_overflow. 2: {
          (* lemma *)
          progress unfold angle_add_overflow.
          apply Bool.andb_true_iff.
          split; [ now apply angle_neqb_neq | ].
          apply rngl_sin_nonneg_angle_le_straight; cbn.
          now apply (rngl_opp_nonneg_nonpos Hop Hor).
        }
        rewrite rngl_cos_add_straight_r.
        rewrite angle_straight_div_2.
        rewrite rngl_cos_add_right_r.
        rewrite (rngl_opp_involutive Hop).
        cbn.
        rewrite (rngl_squ_sqrt Hon). 2: {
          apply rngl_1_sub_cos_div_2_nonneg.
        }
        rewrite (rngl_mul_comm Hic).
        rewrite (rngl_div_mul Hon Hiv). 2: {
          apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
        }
(* bon, c'est pas bon *)
...
Search (rngl_sin (_ /₂))%L.
Search (_ /₂ + _/₂)%A.
rewrite <- rngl
        do 2 rewrite (rngl_mul_opp_r Hop).
        rewrite (rngl_opp_involutive Hop).
...
        rewrite angle_straight_div_2.
...
            rewrite angle_add_0_r, angle_sub_0_r.
            cbn.
            remember (0 ≤? rngl_sin p)%L as zsp eqn:Hzsp.
            symmetry in Hzsp.
            destruct zsp. {
              apply rngl_leb_le in Hzsp, Hzps.
              apply (rngl_le_antisymm Hor) in Hzsp; [ clear Hzps | easy ].
              apply eq_rngl_sin_0 in Hzsp.
              destruct Hzsp; subst p. {
                now apply angle_neqb_neq in Hpz.
              }
              cbn.
              rewrite (rngl_add_opp_l Hop).
              rewrite (rngl_add_opp_r Hop).
...
    rewrite rngl_cos_add_straight_r.
    rewrite (rngl_mul_opp_r Hop).
    rewrite (rngl_mul_opp_l Hop).
    rewrite (rngl_opp_involutive Hop).
    replace p with ((p + q) /₂ + (p - q) /₂)%A at 1. 2: {
      rewrite angle_div_2_add.
      rewrite Hopq.
      replace q with ((p + q) /₂ - (p - q) /₂)%A at 2. 2: {
        (* lemma ? angle_div_2_sub *)
        progress unfold angle_sub at 1.
        rewrite angle_opp_div_2.
        remember (p - q =? 0)%A as pqz eqn:Hpqz.
        symmetry in Hpqz.
        destruct pqz. {
          apply angle_eqb_eq in Hpqz.
          apply -> angle_sub_move_0_r in Hpqz.
          subst q.
          rewrite angle_sub_diag.
          rewrite angle_opp_0.
          rewrite angle_0_div_2.
          do 2 rewrite angle_add_0_r.
          rewrite angle_add_diag.
          rewrite <- angle_mul_nat_div_2. 2: {
            cbn; rewrite angle_add_0_r.
...
            now cbn; rewrite angle_add_0_r, Hopq.
          }
          apply angle_div_2_mul_2.
        }
        apply angle_eqb_neq in Hpqz.
...

Theorem rngl_cos_add_cos :
  ∀ p q,
  (rngl_cos p + rngl_cos q =
     2 * rngl_cos ((p + q) /₂) * rngl_cos ((p - q) /₂))%L.
Proof.
destruct_ac.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ * _))%L.
  apply H1.
}
intros.
assert (Hp : ∀ a, (0 ≤ a)%L → (√(a / 2) * 2 * √(a / 2))%L = a). {
  intros * Ha.
  replace 2%L with (√2 * √2)%L at 2. 2: {
    rewrite fold_rngl_squ.
    apply (rngl_squ_sqrt Hon).
    apply (rngl_0_le_2 Hon Hos Hor).
  }
  rewrite rngl_mul_assoc.
  rewrite <- rl_sqrt_mul; cycle 1. {
    apply (rngl_div_nonneg Hon Hop Hiv Hor); [ easy | ].
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  } {
    apply (rngl_0_le_2 Hon Hos Hor).
  }
  rewrite (rngl_div_mul Hon Hiv). 2: {
    apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
  }
  rewrite (rngl_mul_mul_swap Hic).
  rewrite <- rngl_mul_assoc.
  rewrite <- rl_sqrt_mul; cycle 1. {
    apply (rngl_div_nonneg Hon Hop Hiv Hor); [ easy | ].
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  } {
    apply (rngl_0_le_2 Hon Hos Hor).
  }
  rewrite (rngl_div_mul Hon Hiv). 2: {
    apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
  }
  rewrite <- rl_sqrt_mul; [ | easy | easy ].
  rewrite fold_rngl_squ.
  rewrite (rl_sqrt_squ Hon Hop Hor).
  now apply (rngl_abs_nonneg_eq Hop Hor).
}
remember (angle_add_overflow p q) as opq eqn:Hopq.
remember (angle_add_overflow p (-q)) as opo eqn:Hopo.
symmetry in Hopq, Hopo.
(**)
destruct opq. 2: {
  destruct opo. 2: {
destruct (angle_eq_dec q angle_straight) as [Hqs| Hqs]. {
  subst q.
  clear Hopo.
  cbn.
  rewrite (rngl_opp_0 Hop).
  rewrite (rngl_add_opp_r Hop).
  do 2 rewrite (rngl_mul_0_r Hos).
  rewrite rngl_add_0_r, (rngl_sub_0_r Hos).
  do 2 rewrite (rngl_mul_opp_r Hop).
  do 2 rewrite (rngl_mul_1_r Hon).
  rewrite (rngl_add_opp_r Hop).
  rewrite (rngl_leb_0_opp Hop Hor).
  remember (rngl_sin p ≤? 0)%L as sz eqn:Hsz.
  symmetry in Hsz.
  destruct sz. {
    apply rngl_leb_le in Hsz.
    (* contradictoire avec Hopq *)
    admit.
  }
  apply (rngl_leb_gt Hor) in Hsz.
replace p with (angle_right)%A.
cbn.
(* ah ouais, faut que p≥q, sinon p-q devient "négatif", et
   la moitié, ça déconne *)
(* je pourrais prendre cos (abs(p-q)/2) au lieu de cos ((p-q)/2)
   mais ça la fout mal, non ? C'est quoi, le mieux ? *)
(* d'ailleurs abs dans les angles, ça n'a pas de sens : les angles
   sont tous positifs *)
...
p=π/2 q=π
p-q=π/2-π=π/2+π=3π/2
cos p + cos q = 0 - 1 = -1
cos ((p + q) / 2) = cos (3π/4) = -√2/2
cos ((p - q) / 2) = cos (3π/4) = -√2/2
...
    progress unfold angle_add_overflow in Hopq, Hopo.
    apply Bool.andb_false_iff in Hopq, Hopo.
    remember ((p ≠? 0)%A)%L as pz eqn:Hpz.
    symmetry in Hpz.
    destruct pz. {
      destruct Hopq as [| Hopq]; [ easy | ].
      destruct Hopo as [| Hopo]; [ easy | ].
      apply angle_leb_gt in Hopq, Hopo.
      (* lemma *)
      progress unfold angle_ltb in Hopq, Hopo.
      cbn in Hopq, Hopo.
      rewrite (rngl_leb_0_opp Hop Hor) in Hopq.
      do 2 rewrite (rngl_leb_0_opp Hop Hor) in Hopo.
      remember (0 ≤? rngl_sin q)%L as zsq eqn:Hzsq.
      remember (rngl_sin q ≤? 0)%L as zqs eqn:Hzqs.
      remember (rngl_sin p ≤? 0)%L as zps eqn:Hzps.
      symmetry in Hzsq, Hzps, Hzqs.
      destruct zsq. {
        destruct zps. {
          destruct zqs; [ | easy ].
          apply rngl_leb_le in Hzsq, Hzqs.
          apply (rngl_le_antisymm Hor) in Hzsq; [ clear Hzqs | easy ].
          clear Hopo.
          apply eq_rngl_sin_0 in Hzsq.
          destruct Hzsq; subst q. {
            rewrite angle_add_0_r, angle_sub_0_r.
            cbn.
            remember (0 ≤? rngl_sin p)%L as zsp eqn:Hzsp.
            symmetry in Hzsp.
            destruct zsp. {
              apply rngl_leb_le in Hzsp, Hzps.
              apply (rngl_le_antisymm Hor) in Hzsp; [ clear Hzps | easy ].
              apply eq_rngl_sin_0 in Hzsp.
              destruct Hzsp; subst p. {
                now apply angle_neqb_neq in Hpz.
              }
              cbn.
              rewrite (rngl_add_opp_l Hop).
              rewrite (rngl_add_opp_r Hop).
              rewrite (rngl_sub_diag Hos).
              rewrite (rngl_div_0_l Hos Hi1). 2: {
                apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
              }
              rewrite (rl_sqrt_0 Hon Hop Hor). 2: {
                rewrite Bool.orb_comm.
                now rewrite Hi1.
              }
              rewrite (rngl_mul_0_r Hos).
              symmetry; apply (rngl_mul_0_r Hos).
            }
            rewrite (rngl_mul_comm Hic).
            do 2 rewrite rngl_mul_assoc.
            rewrite (rngl_mul_mul_swap Hic (-1 * _)).
            rewrite (rngl_mul_mul_swap Hic (-1)).
            rewrite (rngl_squ_opp_1 Hon Hop).
            rewrite (rngl_mul_1_l Hon).
            rewrite rngl_add_comm.
            rewrite Hp; [ easy | ].
            apply (rngl_le_opp_l Hop Hor).
            apply rngl_cos_bound.
          }
          cbn in Hopq.
          exfalso.
          apply rngl_ltb_lt in Hopq.
          apply rngl_nle_gt in Hopq.
          apply Hopq; clear Hopq.
          apply rngl_cos_bound.
        }
        clear Hopq.
        destruct zqs. {
          clear Hopo.
          apply rngl_leb_le in Hzsq, Hzqs.
          apply (rngl_le_antisymm Hor) in Hzsq; [ clear Hzqs | easy ].
          apply eq_rngl_sin_0 in Hzsq.
          destruct Hzsq; subst q. {
            rewrite angle_add_0_r, angle_sub_0_r.
            cbn.
            remember (0 ≤? rngl_sin p)%L as zsp eqn:Hzsp.
            symmetry in Hzsp.
            rewrite rngl_add_comm.
            destruct zsp. {
              rewrite (rngl_mul_1_l Hon).
              rewrite (rngl_mul_comm Hic 2).
              rewrite Hp; [ easy | ].
              apply (rngl_le_opp_l Hop Hor).
              apply rngl_cos_bound.
            }
            rewrite (rngl_mul_comm Hic).
            do 2 rewrite rngl_mul_assoc.
            rewrite (rngl_mul_mul_swap Hic (-1 * _)).
            rewrite (rngl_mul_mul_swap Hic (-1)).
            rewrite (rngl_squ_opp_1 Hon Hop).
            rewrite (rngl_mul_1_l Hon).
            rewrite Hp; [ easy | ].
            apply (rngl_le_opp_l Hop Hor).
            apply rngl_cos_bound.
          }
          cbn.
          apply (rngl_leb_gt Hor) in Hzps.
          rewrite (rngl_add_opp_r Hop).
          rewrite (rngl_opp_0 Hop).
          do 2 rewrite (rngl_mul_0_r Hos).
          rewrite rngl_add_0_r, (rngl_sub_0_r Hos).
          do 2 rewrite (rngl_mul_opp_r Hop).
          do 2 rewrite (rngl_mul_1_r Hon).
          rewrite (rngl_leb_0_opp Hop Hor).
          apply (rngl_leb_gt Hor) in Hzps.
          rewrite Hzps.
          apply (rngl_leb_gt Hor) in Hzps.
          rewrite (rngl_add_opp_r Hop).
          rewrite (rngl_mul_comm Hic).
          do 2 rewrite rngl_mul_assoc.
          rewrite (rngl_mul_mul_swap Hic (-1 * _)).
          rewrite (rngl_mul_mul_swap Hic (-1)).
          rewrite (rngl_squ_opp_1 Hon Hop).
          rewrite (rngl_mul_1_l Hon).
...
          rewrite Hp.
(* ah putain, ça marche pas *)
...
...
    replace p with ((p + q) /₂ + (p - q) /₂)%A at 1. 2: {
      rewrite angle_div_2_add.
      rewrite Hopq.
      replace q with ((p + q) /₂ - (p - q) /₂)%A at 2. 2: {
        (* lemma ? angle_div_2_sub *)
        progress unfold angle_sub at 1.
        rewrite angle_opp_div_2.
        remember (p - q =? 0)%A as pqz eqn:Hpqz.
        symmetry in Hpqz.
        destruct pqz. {
          apply angle_eqb_eq in Hpqz.
          apply -> angle_sub_move_0_r in Hpqz.
          subst q.
          rewrite angle_sub_diag.
          rewrite angle_opp_0.
          rewrite angle_0_div_2.
          do 2 rewrite angle_add_0_r.
          rewrite angle_add_diag.
          rewrite <- angle_mul_nat_div_2. 2: {
            now cbn; rewrite angle_add_0_r, Hopq.
          }
          apply angle_div_2_mul_2.
        }
        apply angle_eqb_neq in Hpqz.
...
destruct opq. {
  destruct opo. {
(* chuis dans un cas raté, là *)
    replace p with ((p + q) /₂ + (p - q) /₂)%A at 1. 2: {
      rewrite angle_div_2_add.
      rewrite Hopq.
      replace q with ((p + q) /₂ - (p - q) /₂)%A at 2. 2: {
        progress unfold angle_sub at 1.
        rewrite angle_opp_div_2.
        remember (p - q =? 0)%A as pqz eqn:Hpqz.
        symmetry in Hpqz.
        destruct pqz. {
          apply angle_eqb_eq in Hpqz.
          apply -> angle_sub_move_0_r in Hpqz.
          subst q.
          rewrite angle_sub_diag.
          rewrite angle_opp_0.
          rewrite angle_0_div_2.
          do 2 rewrite angle_add_0_r.
          rewrite angle_add_diag.
          rewrite <- angle_mul_nat_div_2.
apply angle_div_2_mul_2.
(* donc ça déconne *)
...
Search (_ * (_ /₂))%A.
          rewrite angle_div_2_add_overflow; [ | easy ].
angle_div_2_add_overflow:
Search (_ /₂ + _ /₂)%A.
Search (_ + _ + angle_straight = _)%A.
...
          change_angle_add_r p angle_straight.
          apply eq_angle_eq.
          rewrite rngl_cos_add_straight_r.
          rewrite rngl_cos_sub_straight_r.
          rewrite rngl_sin_add_straight_r.
          rewrite rngl_sin_sub_straight_r.
          f_equal. {
            cbn.
...
Search (rngl_cos (_ /₂ + _ /₂)).
rewrite <- rngl_cos_angle_div_2_add_not_overflow.
...
Search (angle_add_overflow (- _) _ = false)%A.
Search (angle_add_overflow _ (- _) = false)%A.
          rewrite Hopq.
Search ((_ + _) /₂ = _)%A.
...
          rewrite angle_add_0_r.
          rewrite angle_opp_sub_distr.
          rewrite angle_div_2_add_overflow; [ | easy ].
...
rewrite angle_div_2_add_not_overflow.
rewrite
          rewrite angle_div_2_add.
...
  remember (angle_add_overflow p q) as opq eqn:Hopq.
  symmetry in Hopq.
  destruct opq. {
    replace q with ((p + q) /₂ - (p - q) /₂)%A at 1. 2: {
      (* lemma *)
      remember ((p + q) /₂)%A as x.
      progress unfold angle_sub.
      rewrite angle_div_2_add.
      remember (angle_add_overflow p (- q)) as opoq eqn:Hopoq.
      symmetry in Hopoq.
      destruct opoq. {
        move Hopq at bottom.
        progress unfold angle_add_overflow in Hopoq.
        progress unfold angle_add_overflow in Hopq.
        apply Bool.andb_true_iff in Hopoq, Hopq.
        destruct Hopoq as (Hpz, H1).
        destruct Hopq as (_, H2).
...
        progress unfold angle_leb in H1.
        progress unfold angle_leb in H2.
Search (- _ ≤ - _)%A.
Search (angle_add_overflow _ (- _)).
...
destruct_ac.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ * _)%L).
  apply H1.
}
...
Search (rngl_cos _ * rngl_cos _)%L.
Search (rngl_cos (_ /₂)).
...
intros.
cbn - [ angle_add angle_sub ].
set (ε₁ := if (0 ≤? _)%L then _ else _).
set (ε₂ := if (0 ≤? _)%L then _ else _).
rewrite (rl_sqrt_div Hon Hop Hiv Hor); cycle 1. {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
}
rewrite (rl_sqrt_div Hon Hop Hiv Hor); cycle 1. {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
}
do 2 rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (2 * ε₁)).
rewrite (rngl_mul_comm Hic 2).
rewrite (rngl_mul_mul_swap Hic _ 2).
set (ε := (ε₁ * ε₂)%L).
do 2 rewrite <- rngl_mul_assoc.
replace 2%L with (√2 * √2)%L at 1. 2: {
  rewrite fold_rngl_squ.
  apply (rngl_squ_sqrt Hon).
  apply (rngl_0_le_2 Hon Hos Hor).
}
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_comm Hic √2).
do 3 rewrite rngl_mul_assoc.
rewrite <- rngl_mul_assoc.
rewrite (rngl_div_mul Hon Hiv). 2: {
  (* lemma *)
  intros H.
  apply (eq_rl_sqrt_0 Hon Hos) in H. 2: {
    apply (rngl_0_le_2 Hon Hos Hor).
  }
  now apply (rngl_2_neq_0 Hon Hos Hc1 Hor) in H.
}
do 2 rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_comm Hic ε).
rewrite rngl_mul_assoc.
rewrite (rngl_mul_comm Hic √2).
rewrite (rngl_div_mul Hon Hiv). 2: {
  (* lemma *)
  intros H.
  apply (eq_rl_sqrt_0 Hon Hos) in H. 2: {
    apply (rngl_0_le_2 Hon Hos Hor).
  }
  now apply (rngl_2_neq_0 Hon Hos Hc1 Hor) in H.
}
rewrite <- rl_sqrt_mul; cycle 1. {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
} {
  apply (rngl_le_opp_l Hop Hor).
  apply rngl_cos_bound.
}
(**)
destruct (rngl_eq_dec Heo ε₁ ε₂) as [Hee| Hee]. {
  assert (He1 : (ε = 1)%L). {
    subst ε; rewrite <- Hee.
    rewrite fold_rngl_squ.
    progress unfold ε₁.
    destruct (0 ≤? rngl_sin (p + q))%L. {
      apply (rngl_squ_1 Hon).
    } {
      rewrite (rngl_squ_opp Hop).
      apply (rngl_squ_1 Hon).
    }
  }
  rewrite He1.
  rewrite (rngl_mul_1_r Hon).
  subst ε.
  clear He1.
  rewrite <- (rngl_abs_nonneg_eq Hop Hor (_ + _)). 2: {
    subst ε₁ ε₂.
    remember (0 ≤? rngl_sin (p + q))%L as zsa eqn:Hzsa.
    remember (0 ≤? rngl_sin (p - q))%L as zsb eqn:Hzsb.
    symmetry in Hzsa, Hzsb.
    destruct zsa. {
      destruct zsb. {
        apply rngl_leb_le in Hzsa, Hzsb.
        destruct (rngl_le_dec Hor 0 (rngl_cos p)) as [Hzcp| Hzcp]. {
          apply rngl_add_cos_nonneg_when_sin_nonneg; [ | | easy | easy ]. {
Search (_ ≤ rngl_sin _)%L.
          apply (rngl_sin_add_nonneg_angle_add_not_overflow_sin_nonneg)
            with (θ1 := q); [ | now rewrite angle_add_comm | ].
          apply (rngl_sin_add_nonneg_angle_add_not_overflow_sin_nonneg)
            with (θ1 := p); [ | easy | ].
Search (0 ≤ rngl_cos _ + rngl_cos _)%L.
...
rewrite rngl_cos_add.
rewrite rngl_cos_sub.
remember (rngl_cos p) as cp.
remember (rngl_cos q) as cq.
remember (rngl_sin p) as sp.
remember (rngl_sin q) as sq.
do 2 rewrite rngl_mul_add_distr_l.
do 3 rewrite rngl_mul_add_distr_r.
do 3 rewrite (rngl_mul_sub_distr_r Hop).
do 3 rewrite (rngl_mul_1_l Hon).
do 2 rewrite (rngl_mul_1_r Hon).
do 2 rewrite rngl_add_assoc.
do 4 rewrite (rngl_add_sub_assoc Hop).
rewrite rngl_add_assoc.
do 4 rewrite rngl_mul_assoc.
rewrite <- (rngl_add_sub_swap Hop (1 + cp * cq)).
rewrite <- (rngl_add_assoc 1).
rewrite <- (rngl_mul_2_l Hon).
rewrite <- (rngl_add_sub_swap Hop).
rewrite rngl_add_add_swap.
rewrite (rngl_sub_add Hop).
rewrite rngl_mul_assoc.
rewrite (rngl_mul_comm Hic (sp * sq)).
rewrite (rngl_mul_mul_swap Hic _ (sp * sq)).
rewrite rngl_mul_assoc.
rewrite (rngl_sub_add Hop).
rewrite <- (rngl_mul_assoc (cp * cq)).
rewrite <- (rngl_mul_assoc (sp * sq)).
do 2 rewrite fold_rngl_squ.
rewrite <- rngl_mul_assoc.
rewrite <- (rngl_squ_1 Hon) at 1.
rewrite <- (rngl_mul_1_r Hon 2).
remember (1 + cp * cq)%L as a.
remember (sp * sq)%L as b.
rewrite <- (rngl_squ_add Hic Hon).
rewrite (rngl_squ_sub_squ Hop).
rewrite (rngl_mul_comm Hic b).
rewrite (rngl_add_sub Hos).
clear a Heqa.
remember (cp * cq)%L as a eqn:Ha.
rewrite (rngl_squ_sub_squ' Hop).
rewrite (rngl_mul_comm Hic b).
rewrite (rngl_add_sub Hos).
...
rewrite (rngl_squ_add Hic Hon).
...
rewrite (rngl_mul_mul_swap Hic cp cq).
rewrite (rngl_mul_mul_swap Hic sp sq).
rewrite <- (rngl_mul_assoc _ cq).
rewrite <- (rngl_mul_assoc _ sq).
do 4 rewrite fold_rngl_squ.
...

Theorem rngl_cos_derivative :
  is_derivative angle_eucl_dist rngl_dist rngl_cos (λ θ, (- rngl_sin θ))%L.
Proof.
destruct_ac.
intros θ ε Hε.
enough (H :
  ∃ η : T,
  (0 < η)%L ∧
  ∀ dθ : angle T,
    (angle_eucl_dist (θ + dθ) θ < η)%L
    → (rngl_dist
         (rngl_dist
            (rngl_cos (θ + dθ)) (rngl_cos θ) / angle_eucl_dist (θ + dθ) θ)
            (- rngl_sin θ) <
       ε)%L). {
  destruct H as (η & Hzη & H).
  exists η.
  split; [ easy | ].
  intros θ' Hθ'.
  specialize (H (θ' - θ))%A.
  rewrite angle_add_sub_assoc in H.
  rewrite angle_add_sub_swap in H.
  rewrite angle_sub_diag, angle_add_0_l in H.
  now specialize (H Hθ').
}
enough (H :
  ∃ η : T,
  (0 < η)%L ∧
  ∀ dθ : angle T,
    (angle_eucl_dist (θ + dθ) θ < η)%L
    → (rngl_dist
         (rngl_abs (rngl_cos (θ + dθ) - rngl_cos θ) /
            rl_modl
              (rngl_cos (θ + dθ) - rngl_cos θ)
              (rngl_sin (θ + dθ) - rngl_sin θ))
         (- rngl_sin θ) <
       ε)%L). {
  destruct H as (η & Hzη & H).
  exists η.
  split; [ easy | ].
  intros dθ Hdθ.
  specialize (H dθ Hdθ)%A.
  progress unfold rngl_dist at 2.
  (* lemma *)
  progress unfold angle_eucl_dist.
  progress unfold rl_modl.
  rewrite (rngl_squ_sub_comm Hop).
  rewrite (rngl_squ_sub_comm Hop (rngl_sin θ)).
  rewrite fold_rl_modl.
  easy.
}
...

Theorem rngl_cos_sub_cos :
  ∀ p q,
  (rngl_cos p - rngl_cos q =
     - (2 * rngl_sin ((p + q) /₂) * rngl_sin ((p - q) /₂)))%L.
Proof.
destruct_ac.
intros.
specialize (rngl_cos_add_cos p (q + angle_straight)) as H1.
rewrite angle_add_assoc in H1.
rewrite angle_sub_add_distr in H1.
rewrite rngl_cos_add_straight_r in H1.
rewrite (rngl_add_opp_r Hop) in H1.
(* I need a lemma angle_lt_dec *)
remember ((p + q) <? angle_straight)%A as pqs eqn:Hpqs.
symmetry in Hpqs.
destruct pqs. {
  rewrite rngl_sin_angle_div_2_add_not_overflow in H1. 2: {
    (* lemma *)
    progress unfold angle_add_overflow.
    apply Bool.andb_false_iff.
    remember (p + q ≠? 0)%A as pqz eqn:Hpqz.
    symmetry in Hpqz.
    destruct pqz; [ right | now left ].
    apply angle_leb_gt.
    apply angle_lt_opp_r; [ | now rewrite angle_opp_straight ].
    intros H.
    now apply angle_neqb_neq in Hpqz.
  }
...
    (* lemma *)
    rewrite <- angle_add_overflow_equiv3.
    progress unfold old_angle_add_overflow.
    (* lemma *)
    apply Bool.not_true_iff_false.
    intros H.
    apply angle_nle_gt in H.
    apply H; clear H.
    (* end lemma *)
Search (_ ≤ _ + _)%A.
    (* lemma *)
    rewrite <- (angle_add_0_r (p + q)) at 1.
    apply angle_add_le_mono_l.
...
    apply angle_le_add_l.
    apply angle_ltb_ge.
...
    rewrite angle_add_overflow_equiv2.
    progress unfold angle_add_overflow.
    apply Bool.andb_false_iff.

Search (_ → angle_add_overflow _ _ = false).
Search (rngl_sin ((_ + _) /₂)).
...
rewrite H1; clear H1.
...
rewrite rngl_mul_assoc.
...
Print rngl_dist.
progress unfold rngl_dist.
enough (H : ...
...
Check rngl_cos_add_cos.
Search (rngl_cos _ - rngl_cos _)%L.
progress unfold angle_eucl_dist at 1.
...

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
            do 3 rewrite (rngl_mul_1_l Hon).
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
    rewrite (rngl_mul_1_l Hon).
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
