(* File created because Work2.v became too big, but
   without any topic found for the moment *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Import List.ListNotations.

Require Import Main.Misc Main.RingLike.
Require Import Main.IterMax.
Require Import Trigo.RealLike.
Require Import Trigo.TrigoWithoutPi Trigo.TrigoWithoutPiExt.
Require Import Trigo.AngleAddLeMonoL.
Require Import Trigo.AngleAddOverflowLe.
Require Import Trigo.AngleTypeIsComplete.
Require Import Trigo.SeqAngleIsCauchy.
Require Import Trigo.AngleDivNat.
Require Import Misc.
Require Import Complex.
Require Import Work.
Require Import Work2.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Theorem gc_mul_0_l :
  rngl_has_opp_or_subt T = true →
  ∀ z : GComplex T, (0 * z = 0)%C.
Proof.
intros Hos *.
apply eq_gc_eq; cbn.
do 2 rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_r Hos).
rewrite rngl_add_0_l.
easy.
Qed.

Theorem gc_pow_mul_l :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  ∀ z1 z2 n, ((z1 * z2) ^ n = (z1 ^ n) * (z2 ^ n))%C.
Proof.
intros Hic Hop.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
progress unfold gc_pow_nat.
induction n. {
  symmetry.
  specialize (gc_opt_mul_1_l Hos) as H1.
  progress unfold rngl_has_1 in H1.
  cbn in H1 |-*.
  progress unfold rngl_one in H1.
  progress unfold rngl_one.
  cbn in H1 |-*.
  destruct (gc_opt_one T); [ apply H1 | ].
  apply (gc_mul_0_l Hos).
}
cbn.
rewrite IHn.
do 2 rewrite (gc_mul_assoc Hop).
f_equal.
do 2 rewrite <- (gc_mul_assoc Hop).
f_equal.
apply (gc_mul_comm Hic).
Qed.

Theorem gc_has_nth_root :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  rngl_characteristic T = 0 →
  rngl_is_archimedean T = true →
  rngl_is_complete T →
  ∀ z : GComplex T, ∀ n, n ≠ 0 → ∃ z', (z' ^ n)%C = z.
Proof.
intros Hic Hop Hor Hcz Har Hco.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hnz.
specialize (polar z _ _ (eq_refl _) (eq_refl)) as H1.
set (ρ := √((gre z)² + (gim z)²)%L) in H1.
set
  (θ :=
     (if (0 ≤? gim z)%L then rngl_acos (gre z / ρ)
      else (- rngl_acos (gre z / ρ))%A)) in H1.
rewrite H1.
specialize (exists_angle_div_nat Hcz Har Hco) as H2.
specialize (H2 θ n Hnz).
destruct H2 as (θ', Ht).
rewrite <- Ht.
specialize (gc_cos_sin_pow θ' n) as H3.
exists ((rl_nth_root n ρ +ℹ 0) * (rngl_cos θ' +ℹ rngl_sin θ'))%C.
rewrite (gc_pow_mul_l Hic Hop).
rewrite (gc_pow_im_0 Hos).
rewrite gc_cos_sin_pow.
rewrite rl_nth_root_pow. 2: {
  progress unfold ρ.
  apply rl_sqrt_nonneg.
  apply (rngl_add_squ_nonneg Hop Hor).
}
progress unfold gc_mul.
cbn.
do 2 rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_r Hos).
rewrite rngl_add_0_l.
easy.
Qed.

Notation "‖ x ‖" := (gc_modl x) (at level 60) : ring_like_scope.

Theorem gc_modl_div_nonneg :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ n d, d ≠ 0%C → (0 ≤ (‖ n ‖) / (‖ d ‖))%L.
Proof.
intros Hon Hop Hiv Hor * Hz.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert (Hio :
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T &&
     rngl_has_eq_dec_or_order T)%bool = true). {
  apply Bool.orb_true_iff; right.
  rewrite Hi1; cbn.
  now apply rngl_has_eq_dec_or_is_ordered_r.
}
apply (rngl_div_nonneg Hon Hop Hiv Hor). {
  apply rl_sqrt_nonneg.
  apply (rngl_add_squ_nonneg Hop Hor).
} {
  apply (rl_sqrt_pos Hon Hos Hor).
  apply (rngl_lt_iff Hor).
  split; [ apply (rngl_add_squ_nonneg Hop Hor) | ].
  intros H1; symmetry in H1.
  cbn in Hz.
  apply (rngl_eq_add_0 Hor) in H1; cycle 1. {
    apply (rngl_squ_nonneg Hop Hor).
  } {
    apply (rngl_squ_nonneg Hop Hor).
  }
  destruct H1 as (H1, H2).
  apply (eq_rngl_squ_0 Hos Hio) in H1, H2.
  apply Hz; clear Hz.
  now apply eq_gc_eq.
}
Qed.

(* to be completed
Theorem gc_opt_alg_closed :
  let ro := gc_ring_like_op T in
  if (rngl_has_opp T && rngl_has_inv (GComplex T) &&
      rngl_has_1 (GComplex T))%bool
  then
     ∀ l : list (GComplex T), 1 < length l → List.last l 0%L ≠ 0%L →
     ∃ x : GComplex T, rngl_eval_polyn l x = 0%L
  else not_applicable.
Proof.
intros; cbn.
remember (rngl_has_opp T) as op eqn:Hop; symmetry in Hop.
destruct op; [ | easy ].
remember (rngl_has_inv (GComplex T)) as ivc eqn:Hivc; symmetry in Hivc.
destruct ivc; [ | easy ].
remember (rngl_has_1 (GComplex T)) as onc eqn:Honc; symmetry in Honc.
destruct onc; [ cbn | easy ].
intros la Hla Hl1.
Theorem gc_polyn_modl_tends_to_inf_when_modl_var_tends_to_inf :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  let gro := gc_ring_like_op T in
  ∀ P : list (GComplex T),
  ∀ M, (0 < M)%L →
  List.nth (length P - 1) P 0%L ≠ 0%C
  → ∃ R₀, (0 < R₀)%L ∧
    ∀ z : GComplex T, (R₀ < ‖z‖)%L → (M < ‖rngl_eval_polyn P z‖)%L.
Proof.
intros Hon Hop Hiv Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert (Hio :
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T &&
     rngl_has_eq_dec_or_order T)%bool = true). {
  apply Bool.orb_true_iff; right.
  rewrite Hi1; cbn.
  now apply rngl_has_eq_dec_or_is_ordered_r.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite H1 in H.
  now apply (rngl_lt_irrefl Hor) in H.
}
intros * HM Hz.
(* must take
   R₀ ​= max(‖a_{n-1}/a_n‖, ‖a_{n-2}/a_n‖^(1/2), .. ‖a₀/a_n‖^(1/n)
 *)
remember (List.length P) as n eqn:Hn.
exists (1 + Max (i = 0, n - 2), (‖ P.[i] ‖ / ‖ P.[n - 1] ‖))%L.
split. {
  apply (rngl_lt_le_trans Hor _ 1). {
    apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
  }
  apply (rngl_le_add_r Hor).
  clear Hn.
  remember (P.[n - 1]) as d eqn:Hd.
  clear Hd.
  induction n; cbn. {
    rewrite iter_seq_only_one'. {
      now apply (gc_modl_div_nonneg Hon Hop Hiv Hor).
    }
    intros x.
    apply (rngl_max_r_iff Hor).
    now apply (gc_modl_div_nonneg Hon Hop Hiv Hor).
  }
  replace 0%C with 0%L by easy.
  destruct n; [ easy | ].
  progress unfold iter_seq in IHn.
  progress unfold iter_seq.
  rewrite Nat.sub_0_r in IHn |-*.
  cbn - [ List.seq ] in IHn.
  rewrite <- Nat_succ_sub_succ_r; [ | easy ].
  rewrite Nat.sub_0_r.
  destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
    progress unfold iter_list.
    subst n; cbn.
    apply (rngl_le_max_l Hor).
  }
  apply Nat.neq_0_lt_0 in Hnz.
  rewrite <- Nat_succ_sub_succ_r in IHn; [ | easy ].
  rewrite Nat.sub_0_r in IHn.
  rewrite List.seq_S.
  cbn.
Check fold_left_op_fun_from_d'.
...
  rewrite (max_list_app Hor).
(* chiasse de pute *)
Check max_list_app.
...
progress unfold iter_list.
remember (List.seq 0 n) as l eqn:Hl.
destruct l as [| a]. {
  symmetry in Hl.
  apply List_seq_eq_nil in Hl; subst n.
  cbn.
  apply (rngl_le_max_l Hor).
}
rewrite List.seq_S.
cbn.
rewrite List.fold_left_app.
rewrite Hl in IHn.
progress unfold iter_list in IHn.
remember (List.fold_left _ _ _) as x eqn:Hx in IHn.
rewrite <- Hx.
...
progress unfold iter_list in IHn.
cbn in IHn.
rewrite (proj2 (rngl_max_r_iff Hor _ _)). 2: {
  now apply (gc_modl_div_nonneg Hon Hop Hiv Hor).
}
rewrite (proj2 (rngl_max_r_iff Hor _ _)) in IHn. 2: {
  now apply (gc_modl_div_nonneg Hon Hop Hiv Hor).
}
rewrite <- List.seq_shift.
rewrite <- Hl.
rewrite List_fold_left_map.
cbn.
...
rewrite op_d_l.
now rewrite fold_left_op_fun_from_d with (d := d).
...
rewrite iter_list_split_first with (z := n).
...
  rewrite iter_seq_split_first.
...
  rewrite iter_seq_split_first'.
...
*)

End a.

(* to be completed
Definition gc_ring_like_prop T
  {ro : ring_like_op T} {rp : ring_like_prop T} {rl : real_like_prop T}
  {roc : ring_like_op (GComplex T)}
  (Hop : rngl_has_opp T = true) :
    @ring_like_prop (GComplex T) (gc_ring_like_op T) :=
  let Hos := rngl_has_opp_has_opp_or_subt Hop in
  let Hsu := rngl_has_opp_has_no_subt Hop in
  {| rngl_mul_is_comm := rngl_mul_is_comm T;
     rngl_is_integral_domain := false;
     rngl_is_archimedean := false;
     rngl_is_alg_closed :=
       (rngl_has_opp T && rngl_has_inv (GComplex T) &&
        rngl_has_1 (GComplex T))%bool;
     rngl_characteristic := rngl_characteristic T;
     rngl_add_comm := gc_add_comm;
     rngl_add_assoc := gc_add_assoc;
     rngl_add_0_l := gc_add_0_l;
     rngl_mul_assoc := gc_mul_assoc Hop;
     rngl_opt_mul_1_l := gc_opt_mul_1_l Hos;
     rngl_mul_add_distr_l := gc_mul_add_distr_l Hop;
     rngl_opt_mul_comm := gc_opt_mul_comm;
     rngl_opt_mul_1_r := gc_opt_mul_1_r Hos;
     rngl_opt_mul_add_distr_r := gc_opt_mul_add_distr_r Hop;
     rngl_opt_add_opp_diag_l := gc_opt_add_opp_diag_l Hop;
     rngl_opt_add_sub := gc_opt_add_sub Hsu;
     rngl_opt_sub_add_distr := gc_opt_sub_add_distr Hsu;
     rngl_opt_mul_inv_diag_l := gc_opt_mul_inv_diag_l Hop;
     rngl_opt_mul_inv_diag_r := gc_opt_mul_inv_diag_r;
     rngl_opt_mul_div := gc_opt_mul_div;
     rngl_opt_mul_quot_r := gc_opt_mul_quot_r;
     rngl_opt_integral := NA;
     rngl_opt_alg_closed := (*gc_opt_alg_closed;*)NA;
(*
     rngl_characteristic_prop := gc_characteristic_prop;
     rngl_opt_le_dec := NA;
     rngl_opt_le_refl := NA;
     rngl_opt_le_antisymm := NA;
     rngl_opt_le_trans := NA;
     rngl_opt_add_le_compat := NA;
     rngl_opt_mul_le_compat_nonneg := NA;
     rngl_opt_mul_le_compat_nonpos := NA;
     rngl_opt_mul_le_compat_non_opp := NA;
     rngl_opt_not_le := NA;
*)
     rngl_opt_archimedean := NA |}.
*)
