Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import RingLike_structures.
Require Import RingLike_order.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

(* theorems *)

Theorem fold_rngl_squ : ∀ a : T, (a * a)%L = rngl_squ a.
Proof. easy. Qed.

Theorem rngl_neqb_neq :
  rngl_has_eq_dec T = true →
  ∀ a b : T, (a ≠? b)%L = true ↔ a ≠ b.
Proof.
intros Hed *.
progress unfold rngl_has_eq_dec in Hed.
progress unfold rngl_eqb.
destruct rngl_opt_eq_dec as [rngl_eq_dec| ]; [ | easy ].
clear Hed.
now destruct (rngl_eq_dec a b).
Qed.

Theorem rngl_eqb_refl :
  rngl_has_eq_dec T = true →
  ∀ a, (a =? a)%L = true.
Proof.
intros Heqb *.
now apply (rngl_eqb_eq Heqb).
Qed.

Theorem rngl_eq_dec : rngl_has_eq_dec T = true → ∀ a b : T, {a = b} + {a ≠ b}.
Proof.
intros Hed *.
progress unfold rngl_has_eq_dec in Hed.
destruct rngl_opt_eq_dec as [rngl_eq_dec| ]; [ | easy ].
apply rngl_eq_dec.
Qed.

Theorem rngl_eqb_sym :
  rngl_has_eq_dec T = true →
  ∀ a b, ((a =? b) = (b =? a))%L.
Proof.
intros Hed *.
progress unfold rngl_has_eq_dec in Hed.
progress unfold rngl_eqb.
destruct rngl_opt_eq_dec as [rngl_eq_dec| ]; [ | easy ].
destruct (rngl_eq_dec a b). {
  subst b.
  now destruct (rngl_eq_dec a a).
} {
  destruct (rngl_eq_dec b a); [ now subst b | easy ].
}
Qed.

(* *)

Arguments rngl_mul_nat {T ro} a%_L n%_nat.

Theorem rngl_of_nat_0 : rngl_of_nat 0 = 0%L.
Proof. easy. Qed.

Theorem fold_rngl_mul_nat :
  ∀ a n, List.fold_right rngl_add 0%L (List.repeat a n)%L = rngl_mul_nat a n.
Proof. easy. Qed.

...

Theorem rngl_abs_div :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_has_eq_dec T = true →
  rngl_is_ordered T = true →
  ∀ x y, y ≠ 0%L → rngl_abs (x / y)%L = (rngl_abs x / rngl_abs y)%L.
Proof.
intros * Hon Hop Hiv Heb Hor * Hyz.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
progress unfold rngl_abs.
remember (x ≤? _)%L as xz eqn:Hx; symmetry in Hx.
remember (y ≤? _)%L as yz eqn:Hy; symmetry in Hy.
remember (x / y ≤? _)%L as xyz eqn:Hxy; symmetry in Hxy.
destruct xz. {
  apply rngl_leb_le in Hx.
  destruct yz. {
    apply rngl_leb_le in Hy.
    destruct xyz. {
      apply rngl_leb_le in Hxy.
      progress unfold rngl_div in Hxy.
      rewrite Hiv in Hxy.
      specialize (rngl_mul_le_compat_nonpos Hop Hor) as H1.
      specialize (H1 0 0 x y⁻¹)%L.
      assert (H : (x ≤ 0 ≤ 0)%L). {
        split; [ easy | apply (rngl_le_refl Hor) ].
      }
      specialize (H1 H); clear H.
      assert (H : (y⁻¹ ≤ 0 ≤ 0)%L). {
        split; [ | apply (rngl_le_refl Hor) ].
        apply (rngl_opp_le_compat Hop Hor).
        rewrite (rngl_opp_0 Hop).
        rewrite (rngl_opp_inv Hon Hop Hiv _ Hyz).
        apply (rngl_opp_le_compat Hop Hor) in Hy.
        rewrite (rngl_opp_0 Hop) in Hy.
        apply (rngl_lt_le_incl Hor).
        apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
        apply (rngl_lt_iff Hor).
        split; [ easy | ].
        intros H.
        apply (f_equal rngl_opp) in H.
        rewrite (rngl_opp_0 Hop) in H.
        rewrite (rngl_opp_involutive Hop) in H.
        now symmetry in H.
      }
      specialize (H1 H); clear H.
      rewrite (rngl_mul_0_l Hos) in H1.
      specialize (rngl_le_antisymm Hor _ _ Hxy H1) as H2.
      apply (rngl_integral Hos) in H2. 2: {
        rewrite Hi1, Heb; cbn.
        now destruct rngl_is_integral_domain.
      }
      destruct H2 as [H2| H2]. {
        subst x.
        rewrite (rngl_div_0_l Hos Hi1 _ Hyz).
        rewrite (rngl_opp_0 Hop).
        symmetry.
        apply (rngl_div_0_l Hos Hi1).
        intros H.
        apply (f_equal rngl_opp) in H.
        rewrite (rngl_opp_0 Hop) in H.
        now rewrite (rngl_opp_involutive Hop) in H.
      } {
        exfalso; revert H2.
        now apply (rngl_inv_neq_0 Hon Hos Hiv).
      }
    } {
      unfold rngl_div.
      rewrite Hiv.
      rewrite (rngl_mul_opp_l Hop).
      rewrite <- (rngl_mul_opp_r Hop).
      f_equal.
      rewrite (rngl_opp_inv Hon Hop Hiv). 2: {
        intros H.
        apply (f_equal rngl_opp) in H.
        rewrite (rngl_opp_0 Hop) in H.
        now rewrite (rngl_opp_involutive Hop) in H.
      }
      now rewrite (rngl_opp_involutive Hop).
    }
  } {
    apply (rngl_leb_gt Hor) in Hy.
    destruct xyz. {
      apply rngl_leb_le in Hxy.
      progress unfold rngl_div.
      rewrite Hiv.
      now rewrite (rngl_mul_opp_l Hop).
    } {
      apply rngl_leb_nle in Hxy.
      exfalso; apply Hxy; clear Hxy.
      progress unfold rngl_div.
      rewrite Hiv.
      apply (rngl_mul_nonpos_nonneg Hop Hor _ _ Hx).
      apply (rngl_lt_le_incl Hor).
      now apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
    }
  }
}
apply (rngl_leb_gt Hor) in Hx.
destruct yz. {
  apply rngl_leb_le in Hy.
  destruct xyz. {
    apply rngl_leb_le in Hxy.
    progress unfold rngl_div.
    rewrite Hiv.
    rewrite <- (rngl_mul_opp_r Hop).
    f_equal.
    now apply (rngl_opp_inv Hon Hop Hiv).
  } {
    apply rngl_leb_nle in Hxy.
    exfalso; apply Hxy; clear Hxy.
    progress unfold rngl_div.
    rewrite Hiv.
    apply (rngl_lt_le_incl Hor) in Hx.
    apply (rngl_mul_nonneg_nonpos Hop Hor _ _ Hx).
    apply (rngl_lt_le_incl Hor).
    apply (rngl_inv_lt_0_compat Hon Hop Hiv Hor).
    apply (rngl_lt_iff Hor).
    split; [ easy | congruence ].
  }
}
(* ... *)
apply rngl_leb_nle in Hy.
apply (rngl_not_le Hor) in Hy.
destruct Hy as (_, Hy).
destruct xyz; [ | easy ].
apply rngl_leb_le in Hxy.
unfold rngl_div in Hxy.
rewrite Hiv in Hxy.
assert (Hzy : (0 < y)%L). {
  apply (rngl_lt_iff Hor).
  split; [ easy | congruence ].
}
specialize (rngl_0_lt_inv_compat Hon Hop Hiv Hor _ Hzy) as Hy'.
apply (rngl_lt_le_incl Hor) in Hy'.
generalize Hx; intros Hx'.
apply (rngl_lt_le_incl Hor) in Hx'.
specialize (rngl_mul_nonneg_nonneg Hop Hor _ _ Hx' Hy') as H1.
specialize (rngl_le_antisymm Hor _ _ Hxy H1) as H2.
apply (rngl_integral Hos) in H2. 2: {
  rewrite Hi1, Heb.
  now destruct rngl_is_integral_domain.
}
destruct H2 as [H2| H2]. {
  now subst x; apply (rngl_lt_irrefl Hor) in Hx.
} {
  exfalso; revert H2.
  now apply (rngl_inv_neq_0 Hon Hos Hiv).
}
Qed.

Theorem rngl_abs_triangle :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (rngl_abs (a + b) ≤ rngl_abs a + rngl_abs b)%L.
Proof.
intros Hop Hor *.
progress unfold rngl_abs.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
remember (b ≤? 0)%L as bz eqn:Hbz; symmetry in Hbz.
remember (a + b ≤? 0)%L as abz eqn:Habz; symmetry in Habz.
destruct abz. {
  apply rngl_leb_le in Habz.
  destruct az. {
    apply rngl_leb_le in Haz.
    rewrite (rngl_opp_add_distr Hop).
    progress unfold rngl_sub.
    rewrite Hop.
    rewrite rngl_add_comm.
    apply (rngl_add_le_compat Hor); [ apply (rngl_le_refl Hor) | ].
    destruct bz; [ apply (rngl_le_refl Hor) | ].
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_lt_le_incl Hor).
    apply (rngl_lt_trans Hor _ 0)%L; [ | easy ].
    rewrite <- (rngl_opp_0 Hop).
    now apply -> (rngl_opp_lt_compat Hop Hor).
  }
  apply (rngl_leb_gt Hor) in Haz.
  destruct bz. {
    rewrite rngl_add_comm.
    rewrite (rngl_opp_add_distr Hop).
    progress unfold rngl_sub.
    rewrite Hop.
    apply (rngl_add_le_compat Hor); [ | apply (rngl_le_refl Hor) ].
    apply (rngl_lt_le_incl Hor).
    apply (rngl_lt_trans Hor _ 0)%L; [ | easy ].
    rewrite <- (rngl_opp_0 Hop).
    now apply -> (rngl_opp_lt_compat Hop Hor).
  }
  apply (rngl_leb_gt Hor) in Hbz.
  apply (rngl_nlt_ge Hor) in Habz.
  exfalso; apply Habz; clear Habz.
  apply (rngl_lt_le_trans Hor _ a); [ easy | ].
  apply (rngl_le_add_r Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_leb_gt Hor) in Habz.
destruct az. {
  apply rngl_leb_le in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    apply (rngl_nle_gt Hor) in Habz.
    exfalso; apply Habz; clear Habz.
    rewrite <- rngl_add_0_r.
    now apply (rngl_add_le_compat Hor).
  }
  apply (rngl_add_le_compat Hor); [ | apply (rngl_le_refl Hor) ].
  apply (rngl_le_trans Hor _ 0)%L; [ easy | ].
  apply (rngl_opp_le_compat Hop Hor).
  rewrite (rngl_opp_involutive Hop).
  now rewrite (rngl_opp_0 Hop).
}
apply (rngl_leb_gt Hor) in Haz.
apply (rngl_add_le_compat Hor); [ apply (rngl_le_refl Hor) | ].
destruct bz; [ | apply (rngl_le_refl Hor) ].
apply rngl_leb_le in Hbz.
apply (rngl_le_trans Hor _ 0)%L; [ easy | ].
apply (rngl_opp_le_compat Hop Hor).
rewrite (rngl_opp_involutive Hop).
now rewrite (rngl_opp_0 Hop).
Qed.

Theorem rngl_abs_mul :
  rngl_has_opp T = true →
  rngl_has_inv_and_1_or_quot T = true →
  rngl_is_ordered T = true →
  ∀ a b, (rngl_abs (a * b) = rngl_abs a * rngl_abs b)%L.
Proof.
intros Hop Hi1 Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
unfold rngl_abs.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
remember (b ≤? 0)%L as bz eqn:Hbz; symmetry in Hbz.
remember (a * b ≤? 0)%L as abz eqn:Habz; symmetry in Habz.
destruct abz. {
  apply rngl_leb_le in Habz.
  destruct az. {
    rewrite (rngl_mul_opp_l Hop).
    apply rngl_leb_le in Haz.
    destruct bz; [ | easy ].
    rewrite (rngl_mul_opp_r Hop).
    apply rngl_leb_le in Hbz.
    specialize (rngl_mul_nonpos_nonpos Hop Hor _ _ Haz Hbz) as H1.
    apply (rngl_le_antisymm Hor _ _ Habz) in H1.
    rewrite H1.
    now do 2 rewrite (rngl_opp_0 Hop).
  }
  apply (rngl_leb_gt Hor) in Haz.
  destruct bz; [ now rewrite (rngl_mul_opp_r Hop) | ].
  apply (rngl_leb_gt Hor) in Hbz.
  apply (rngl_nlt_ge Hor) in Habz.
  exfalso; apply Habz; clear Habz.
  apply (rngl_lt_iff Hor).
  split. {
    now apply (rngl_mul_nonneg_nonneg Hop Hor); apply (rngl_lt_le_incl Hor).
  }
  apply not_eq_sym.
  intros H1.
  apply (rngl_eq_mul_0_l Hos) in H1. {
    now subst a; apply (rngl_lt_irrefl Hor) in Haz.
  } {
    rewrite Hi1.
    now destruct (rngl_is_integral_domain T).
  } {
    intros H; subst b.
    now apply (rngl_lt_irrefl Hor) in Hbz.
  }
}
apply (rngl_leb_gt Hor) in Habz.
destruct az. {
  rewrite (rngl_mul_opp_l Hop).
  apply rngl_leb_le in Haz.
  destruct bz. {
    rewrite (rngl_mul_opp_r Hop).
    symmetry.
    apply (rngl_opp_involutive Hop).
  }
  apply (rngl_leb_gt Hor) in Hbz.
  apply (rngl_lt_iff Hor) in Hbz.
  destruct Hbz as (Hbz, Hzb).
  specialize (rngl_mul_nonpos_nonneg Hop Hor _ _ Haz Hbz) as H1.
  now apply (rngl_nlt_ge Hor) in H1.
}
apply (rngl_leb_gt Hor) in Haz.
destruct bz; [ | easy ].
apply rngl_leb_le in Hbz.
apply (rngl_lt_iff Hor) in Haz.
destruct Haz as (Haz, Hza).
specialize (rngl_mul_nonneg_nonpos Hop Hor _ _ Haz Hbz) as H1.
now apply (rngl_nlt_ge Hor) in H1.
Qed.

Theorem rngl_min_id :
  rngl_is_ordered T = true →
  ∀ a, rngl_min a a = a.
Proof.
intros Hor *.
progress unfold rngl_min.
now rewrite (rngl_leb_refl Hor).
Qed.

Theorem rngl_min_comm :
  rngl_is_ordered T = true →
  ∀ a b, rngl_min a b = rngl_min b a.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
remember (b ≤? a)%L as ba eqn:Hba.
symmetry in Hab, Hba.
destruct ab. {
  destruct ba; [ | easy ].
  apply rngl_leb_le in Hab, Hba.
  now apply (rngl_le_antisymm Hor).
} {
  destruct ba; [ easy | ].
  apply (rngl_leb_gt Hor) in Hab, Hba.
  now apply (rngl_lt_asymm Hor) in Hba.
}
Qed.

Theorem rngl_min_assoc :
  rngl_is_ordered T = true →
  ∀ a b c,
  rngl_min a (rngl_min b c) = rngl_min (rngl_min a b) c.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
remember (b ≤? c)%L as bc eqn:Hbc.
symmetry in Hab, Hbc.
destruct ab. {
  destruct bc; [ | easy ].
  rewrite Hab.
  apply rngl_leb_le in Hab, Hbc.
  apply (rngl_le_trans Hor a) in Hbc; [ | easy ].
  apply rngl_leb_le in Hbc.
  now rewrite Hbc.
}
rewrite Hbc.
destruct bc; [ now rewrite Hab | ].
apply (rngl_leb_gt Hor) in Hab, Hbc.
apply (rngl_lt_le_incl Hor) in Hbc.
apply (rngl_le_lt_trans Hor c) in Hab; [ | easy ].
apply (rngl_leb_gt Hor) in Hab.
now rewrite Hab.
Qed.

Theorem rngl_min_l_iff :
  rngl_is_ordered T = true →
  ∀ a b, rngl_min a b = a ↔ (a ≤ b)%L.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
remember (b ≤? a)%L as ba eqn:Hba.
symmetry in Hab, Hba.
split; intros H1. {
  destruct ab; [ now apply rngl_leb_le in Hab | ].
  destruct ba; [ subst b; apply (rngl_le_refl Hor) | ].
  apply (rngl_leb_gt Hor) in Hab, Hba.
  apply (rngl_lt_le_incl Hor) in Hba.
  now apply (rngl_nlt_ge Hor) in Hba.
} {
  destruct ab; [ easy | ].
  apply rngl_leb_le in H1.
  now rewrite Hab in H1.
}
Qed.

Theorem rngl_min_r_iff :
  rngl_is_ordered T = true →
  ∀ a b, rngl_min a b = b ↔ (b ≤ a)%L.
Proof.
intros Hor *.
rewrite (rngl_min_comm Hor).
apply (rngl_min_l_iff Hor).
Qed.

Theorem rngl_min_glb_lt_iff :
  rngl_is_ordered T = true →
  ∀ a b c, (c < rngl_min a b ↔ c < a ∧ c < b)%L.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
symmetry in Hab.
split; intros Hcab; [ | now destruct ab ].
destruct ab. {
  apply rngl_leb_le in Hab.
  split; [ easy | ].
  now apply (rngl_lt_le_trans Hor _ a).
}
apply (rngl_leb_gt Hor) in Hab.
split; [ | easy ].
now apply (rngl_lt_trans Hor _ b).
Qed.

Theorem rngl_min_le_iff :
  rngl_is_ordered T = true →
  ∀ a b c, (rngl_min a b ≤ c ↔ a ≤ c ∨ b ≤ c)%L.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
symmetry in Hab.
split; intros Hcab. {
  now destruct ab; [ left | right ].
}
destruct ab. {
  destruct Hcab as [Hac| Hbc]; [ easy | ].
  apply rngl_leb_le in Hab.
  now apply (rngl_le_trans Hor _ b).
}
destruct Hcab as [Hac| Hbc]; [ | easy ].
apply (rngl_leb_gt Hor) in Hab.
apply (rngl_le_trans Hor _ a); [ | easy ].
now apply (rngl_lt_le_incl Hor) in Hab.
Qed.

Theorem rngl_min_lt_iff :
  rngl_is_ordered T = true →
  ∀ a b c, (rngl_min a b < c ↔ a < c ∨ b < c)%L.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
symmetry in Hab.
split; intros Hcab. {
  now destruct ab; [ left | right ].
}
destruct ab. {
  destruct Hcab as [Hac| Hbc]; [ easy | ].
  apply rngl_leb_le in Hab.
  now apply (rngl_le_lt_trans Hor _ b).
}
destruct Hcab as [Hac| Hbc]; [ | easy ].
apply (rngl_leb_gt Hor) in Hab.
now apply (rngl_lt_trans Hor _ a).
Qed.

Theorem rngl_le_min_l :
  rngl_is_ordered T = true →
  ∀ a b, (rngl_min a b ≤ a)%L.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ apply (rngl_le_refl Hor) | ].
apply (rngl_leb_gt Hor) in Hc.
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_le_min_r :
  rngl_is_ordered T = true →
  ∀ a b, (rngl_min a b ≤ b)%L.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ | apply (rngl_le_refl Hor) ].
now apply rngl_leb_le in Hc.
Qed.

Theorem rngl_min_le_compat_l :
  rngl_is_ordered T = true →
  ∀ a b c, (b ≤ c → rngl_min a b ≤ rngl_min a c)%L.
Proof.
intros Hor * Hbc.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
remember (a ≤? c)%L as ac eqn:Hac.
symmetry in Hab, Hac.
destruct ab. {
  destruct ac; [ apply (rngl_le_refl Hor) | ].
  apply rngl_leb_le in Hab.
  now apply (rngl_le_trans Hor _ b).
} {
  destruct ac; [ | easy ].
  apply (rngl_leb_gt Hor) in Hab.
  now apply (rngl_lt_le_incl Hor) in Hab.
}
Qed.

Theorem rngl_le_max_l :
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ rngl_max a b)%L.
Proof.
intros Hor *.
progress unfold rngl_max.
remember (a ≤? b)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ | apply (rngl_le_refl Hor) ].
now apply rngl_leb_le in Hc.
Qed.

Theorem rngl_le_max_r :
  rngl_is_ordered T = true →
  ∀ a b, (b ≤ rngl_max a b)%L.
Proof.
intros Hor *.
progress unfold rngl_max.
remember (a ≤? b)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ apply (rngl_le_refl Hor) | ].
apply (rngl_leb_gt Hor) in Hc.
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_le_abs :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (a ≤ rngl_abs a)%L.
Proof.
intros Hop Hor *.
progress unfold rngl_abs.
remember (a ≤? 0)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ | apply (rngl_le_refl Hor) ].
apply rngl_leb_le in Hc.
apply (rngl_le_sub_0 Hop Hor).
rewrite (rngl_sub_opp_r Hop).
rewrite <- (rngl_add_0_l 0%L).
now apply (rngl_add_le_compat Hor).
Qed.

Theorem rngl_squ_sub_squ :
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  ∀ a b, (rngl_squ a - rngl_squ b = (a + b) * (a - b))%L.
Proof.
intros Hop Hic *.
progress unfold rngl_squ.
rewrite rngl_mul_add_distr_r.
do 2 rewrite (rngl_mul_sub_distr_l Hop).
rewrite (rngl_add_sub_assoc Hop).
rewrite (rngl_mul_comm Hic b a).
f_equal; symmetry.
apply (rngl_sub_add Hop).
Qed.

Theorem rngl_add_squ_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a² + b²)%L.
Proof.
intros Hop Hor *.
apply (rngl_add_nonneg_nonneg Hor);
apply (rngl_squ_nonneg Hop Hor).
Qed.

Theorem rngl_squ_inv :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  ∀ a, (a ≠ 0 → (a⁻¹)² = (a²)⁻¹)%L.
Proof.
intros Hon Hos Hiv * Haz.
progress unfold rngl_squ.
now rewrite (rngl_inv_mul_distr Hon Hos Hiv).
Qed.

Theorem rngl_squ_div :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  ∀ a b, (b ≠ 0)%L → (a / b)²%L = (a² / b²)%L.
Proof.
intros Hic Hon Hos Hiv * Hbz.
progress unfold rngl_div.
rewrite Hiv.
rewrite <- (rngl_squ_inv Hon Hos Hiv); [ | easy ].
apply (rngl_squ_mul Hic).
Qed.

Theorem eq_rngl_squ_0 :
  rngl_has_opp_or_subt T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
  ∀ a, (a² = 0 → a = 0)%L.
Proof.
intros Hos Hii * Ha.
apply (rngl_integral Hos Hii) in Ha.
now destruct Ha.
Qed.

Theorem eq_rngl_squ_rngl_abs :
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
  ∀ a b, rngl_squ a = rngl_squ b → rngl_abs a = rngl_abs b.
Proof.
intros Hop Hic Hor Hii * Hab.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_sub_move_0_r Hop) in Hab.
rewrite (rngl_squ_sub_squ Hop Hic) in Hab.
apply (rngl_integral Hos Hii) in Hab.
destruct Hab as [Hab| Hab]. {
  apply (rngl_add_move_0_r Hop) in Hab.
  subst a.
  apply (rngl_abs_opp Hop Hor).
} {
  apply -> (rngl_sub_move_0_r Hop) in Hab.
  now subst a.
}
Qed.

Theorem rngl_squ_pow_2 :
  rngl_has_1 T = true →
  ∀ a, (a² = a ^ 2)%L.
Proof.
intros Hon *; cbn.
now rewrite rngl_mul_1_r.
Qed.

Theorem rngl_squ_eq_cases :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_has_eq_dec T = true →
  ∀ a b, (a² = b² → a = b ∨ a = -b)%L.
Proof.
intros Hic Hon Hop Hiv Hed * Hab.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo_and_eq_dec Hi1 Hed) as Hid.
apply (rngl_sub_move_0_r Hop) in Hab.
rewrite (rngl_squ_sub_squ Hop Hic) in Hab.
apply (rngl_integral Hos Hid) in Hab.
destruct Hab as [Hab| Hab]; [ right | left ]. {
  now apply (rngl_add_move_0_r Hop) in Hab.
} {
  now apply -> (rngl_sub_move_0_r Hop) in Hab.
}
Qed.

Theorem rngl_min_glb :
  ∀ a b c, (a ≤ b → a ≤ c → a ≤ rngl_min b c)%L.
Proof.
intros * Hab Hac.
progress unfold rngl_min.
now destruct (b ≤? c)%L.
Qed.

Theorem rngl_min_glb_lt :
  ∀ a b c, (a < b → a < c → a < rngl_min b c)%L.
Proof.
intros * Hab Hac.
progress unfold rngl_min.
now destruct (b ≤? c)%L.
Qed.

Theorem rngl_max_lub :
  ∀ a b c, (a ≤ c → b ≤ c → rngl_max a b ≤ c)%L.
Proof.
intros * Hac Hbc.
progress unfold rngl_max.
now destruct (a ≤? b)%L.
Qed.

Theorem rngl_max_lub_lt :
  ∀ a b c, (a < c → b < c → rngl_max a b < c)%L.
Proof.
intros * Hac Hbc.
progress unfold rngl_max.
now destruct (a ≤? b)%L.
Qed.

Theorem rngl_mul_pos_pos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (0 < a)%L → (0 < b)%L → (0 < a * b)%L.
Proof.
intros Hop Hor Hii * Haz Hbz.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_lt_iff Hor) in Haz.
apply (rngl_lt_iff Hor) in Hbz.
apply (rngl_lt_iff Hor).
destruct Haz as (Haz, Hza).
destruct Hbz as (Hbz, Hzb).
split. {
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
}
apply not_eq_sym in Hza, Hzb.
apply not_eq_sym.
intros Hab.
now apply (rngl_eq_mul_0_l Hos Hii) in Hab.
Qed.

Theorem rngl_mul_neg_neg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (a < 0)%L → (b < 0)%L → (0 < a * b)%L.
Proof.
intros Hop Hor Hii * Haz Hbz.
rewrite <- (rngl_mul_opp_opp Hop).
apply (rngl_mul_pos_pos Hop Hor Hii).
now apply (rngl_opp_pos_neg Hop Hor).
now apply (rngl_opp_pos_neg Hop Hor).
Qed.

Theorem rngl_mul_pos_cancel_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (0 < a → 0 < a * b ↔ 0 < b)%L.
Proof.
intros Hop Hor Hii * Ha.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hb. {
  apply (rngl_lt_iff Hor) in Ha.
  apply (rngl_lt_iff Hor) in Hb.
  apply (rngl_lt_iff Hor).
  destruct Ha as (Haz, Hza).
  destruct Hb as (Habz, Hzab).
  apply not_eq_sym in Hza, Hzab.
  split. {
    apply (rngl_lt_eq_cases Hor) in Habz.
    destruct Habz as [Habz| Habz]. {
      apply (rngl_nle_gt Hor) in Habz.
      apply (rngl_nlt_ge Hor).
      intros Hb; apply Habz; clear Habz.
      apply (rngl_mul_nonneg_nonpos Hop Hor); [ easy | ].
      now apply (rngl_lt_le_incl Hor).
    }
    now rewrite Habz in Hzab.
  }
  intros H; subst b.
  now rewrite (rngl_mul_0_r Hos) in Hzab.
} {
  now apply (rngl_mul_pos_pos Hop Hor).
}
Qed.

Theorem rngl_mul_pos_cancel_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (0 < b → 0 < a * b ↔ 0 < a)%L.
Proof.
intros Hop Hor Hii * Ha.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hb. {
  apply (rngl_lt_iff Hor) in Ha.
  apply (rngl_lt_iff Hor) in Hb.
  apply (rngl_lt_iff Hor).
  destruct Ha as (Haz, Hza).
  destruct Hb as (Habz, Hzab).
  apply not_eq_sym in Hza, Hzab.
  split. {
    apply (rngl_lt_eq_cases Hor) in Habz.
    destruct Habz as [Habz| Habz]. {
      apply (rngl_nle_gt Hor) in Habz.
      apply (rngl_nlt_ge Hor).
      intros Hb; apply Habz; clear Habz.
      apply (rngl_mul_nonpos_nonneg Hop Hor); [ | easy ].
      now apply (rngl_lt_le_incl Hor).
    }
    now rewrite Habz in Hzab.
  }
  intros H; subst a.
  now rewrite (rngl_mul_0_l Hos) in Hzab.
} {
  now apply (rngl_mul_pos_pos Hop Hor).
}
Qed.

Theorem rngl_mul_lt_mono_pos_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c : T, (0 < a)%L → (b < c)%L ↔ (a * b < a * c)%L.
Proof.
intros Hop Hor Hii * Ha.
split; intros Hbc. {
  apply (rngl_lt_0_sub Hop Hor).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  apply (rngl_mul_pos_pos Hop Hor Hii); [ easy | ].
  now apply (rngl_lt_0_sub Hop Hor).
} {
  apply (rngl_lt_0_sub Hop Hor) in Hbc.
  rewrite <- (rngl_mul_sub_distr_l Hop) in Hbc.
  apply (rngl_mul_pos_cancel_l Hop Hor Hii) in Hbc; [ | easy ].
  now apply (rngl_lt_0_sub Hop Hor).
}
Qed.

Theorem rngl_mul_lt_mono_pos_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c : T, (0 < a)%L → (b < c)%L ↔ (b * a < c * a)%L.
Proof.
intros Hop Hor Hii * Ha.
split; intros Hbc. {
  apply (rngl_lt_0_sub Hop Hor).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  apply (rngl_mul_pos_pos Hop Hor Hii); [ | easy ].
  now apply (rngl_lt_0_sub Hop Hor).
} {
  apply (rngl_lt_0_sub Hop Hor) in Hbc.
  rewrite <- (rngl_mul_sub_distr_r Hop) in Hbc.
  apply (rngl_mul_pos_cancel_r Hop Hor Hii) in Hbc; [ | easy ].
  now apply (rngl_lt_0_sub Hop Hor).
}
Qed.

Theorem rngl_div_lt_mono_pos_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c : T, (0 < a)%L → (b < c)%L ↔ (b / a < c / a)%L.
Proof.
intros Hon Hop Hiv Hor Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hza.
  rewrite (H1 a) in Hza.
  now apply (rngl_lt_irrefl Hor) in Hza.
}
intros * Hza.
split; intros Hbc. {
  progress unfold rngl_div at 1 2.
  rewrite Hiv.
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii); [ | easy ].
  now apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
} {
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii a) in Hbc; [ | easy ].
  rewrite (rngl_div_mul Hon Hiv) in Hbc. 2: {
    intros H; subst a.
    now apply (rngl_lt_irrefl Hor) in Hza.
  }
  rewrite (rngl_div_mul Hon Hiv) in Hbc. 2: {
    intros H; subst a.
    now apply (rngl_lt_irrefl Hor) in Hza.
  }
  easy.
}
Qed.

Theorem rngl_mul_le_mono_pos_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c : T, (0 < c)%L → (a ≤ b)%L ↔ (c * a ≤ c * b)%L.
Proof.
intros Hop Hor Hii * Hc.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hab. {
  apply (rngl_lt_eq_cases Hor) in Hab.
  destruct Hab as [Hab| Hab]; [ | subst b; apply (rngl_le_refl Hor) ].
  apply (rngl_le_0_sub Hop Hor).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  apply (rngl_mul_nonneg_nonneg Hop Hor). {
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_le_0_sub Hop Hor).
  now apply (rngl_lt_le_incl Hor).
} {
  apply (rngl_le_0_sub Hop Hor) in Hab.
  rewrite <- (rngl_mul_sub_distr_l Hop) in Hab.
  apply (rngl_nlt_ge Hor) in Hab.
  apply (rngl_nlt_ge Hor).
  intros H1; apply Hab; clear Hab.
  replace 0%L with (c * 0)%L by apply (rngl_mul_0_r Hos).
  apply (rngl_mul_lt_mono_pos_l Hop Hor Hii); [ easy | ].
  apply (rngl_nle_gt Hor).
  intros H2.
  apply -> (rngl_le_0_sub Hop Hor) in H2.
  now apply (rngl_nlt_ge Hor) in H2.
}
Qed.

Theorem rngl_mul_le_mono_nonneg_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 ≤ a)%L → (b ≤ c)%L → (a * b ≤ a * c)%L.
Proof.
intros Hop Hor * Ha Hbc.
apply (rngl_lt_eq_cases Hor) in Hbc.
destruct Hbc as [Hbc| Hbc]; [ | subst b; apply (rngl_le_refl Hor) ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_l Hop).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
apply (rngl_le_0_sub Hop Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_mul_le_mono_nonneg_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 ≤ c → a ≤ b → a * c ≤ b * c)%L.
Proof.
intros Hop Hor * Hc Hab.
apply (rngl_lt_eq_cases Hor) in Hab.
destruct Hab as [Hab| Hab]; [ | subst b; apply (rngl_le_refl Hor) ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_r Hop).
apply (rngl_mul_nonneg_nonneg Hop Hor); [ | easy ].
apply (rngl_le_0_sub Hop Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_mul_le_mono_pos_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c : T, (0 < c)%L → (a ≤ b)%L ↔ (a * c ≤ b * c)%L.
Proof.
intros Hop Hor Hii * Hc.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hab. {
  apply (rngl_mul_le_mono_nonneg_r Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
} {
  apply (rngl_le_0_sub Hop Hor) in Hab.
  rewrite <- (rngl_mul_sub_distr_r Hop) in Hab.
  apply (rngl_nlt_ge Hor) in Hab.
  apply (rngl_nlt_ge Hor).
  intros H1; apply Hab; clear Hab.
  replace 0%L with (0 * c)%L by apply (rngl_mul_0_l Hos).
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii); [ easy | ].
  apply (rngl_nle_gt Hor).
  intros H2.
  apply -> (rngl_le_0_sub Hop Hor) in H2.
  now apply (rngl_nlt_ge Hor) in H2.
}
Qed.

Theorem rngl_mul_le_mono_nonpos_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a ≤ 0)%L → (b ≤ c)%L → (a * c ≤ a * b)%L.
Proof.
intros Hop Hor * Ha Hbc.
apply (rngl_lt_eq_cases Hor) in Hbc.
destruct Hbc as [Hbc| Hbc]; [ | subst b; apply (rngl_le_refl Hor) ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_l Hop).
apply (rngl_mul_nonpos_nonpos Hop Hor); [ easy | ].
apply (rngl_le_sub_0 Hop Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_mul_le_mono_nonpos_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (c ≤ 0 → a ≤ b → b * c ≤ a * c)%L.
Proof.
intros Hop Hor * Hc Hab.
apply (rngl_lt_eq_cases Hor) in Hab.
destruct Hab as [Hab| Hab]; [ | subst b; apply (rngl_le_refl Hor) ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_r Hop).
apply (rngl_mul_nonpos_nonpos Hop Hor); [ | easy ].
apply (rngl_le_sub_0 Hop Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_mul_lt_mono_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
   rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c d, (0 ≤ a < b → 0 ≤ c < d → a * c < b * d)%L.
Proof.
intros Hop Hor Hii * (Haz, Hab) (Hcz, Hcd).
apply (rngl_le_lt_trans Hor _ (b * c)%L). {
  apply (rngl_mul_le_mono_nonneg_r Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_mul_lt_mono_pos_l Hop Hor Hii); [ | easy ].
now apply (rngl_le_lt_trans Hor _ a).
Qed.

Theorem rngl_mul_min_distr_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  rngl_has_eq_dec T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c, (0 ≤ a)%L → rngl_min (a * b)%L (a * c)%L = (a * rngl_min b c)%L.
Proof.
intros Hop Hor Hed Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hza.
destruct (rngl_eq_dec Hed a 0%L) as [Haz| Haz]. {
  subst a.
  do 3 rewrite (rngl_mul_0_l Hos).
  apply (rngl_min_id Hor).
}
assert (H : (0 < a)%L). {
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  now apply not_eq_sym.
}
clear Hza Haz; rename H into Hza.
progress unfold rngl_min.
remember (_ * _ ≤? _ * _)%L as abc eqn:Habc.
remember (b ≤? c)%L as bc eqn:Hbc.
symmetry in Habc, Hbc.
destruct abc. {
  f_equal.
  destruct bc; [ easy | ].
  apply rngl_leb_le in Habc.
  apply (rngl_leb_gt Hor) in Hbc.
  apply (rngl_mul_le_mono_pos_l Hop Hor Hii) in Habc; [ | easy ].
  now apply (rngl_nle_gt Hor) in Hbc.
}
destruct bc; [ | easy ].
f_equal.
apply rngl_leb_le in Hbc.
apply (rngl_leb_gt Hor) in Habc.
apply (rngl_mul_lt_mono_pos_l Hop Hor Hii) in Habc; [ | easy ].
now apply (rngl_nle_gt Hor) in Habc.
Qed.

Theorem rngl_lt_mul_0_if :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a * b < 0)%L → (a < 0 < b)%L ∨ (0 < a)%L ∧ (b < 0)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hab.
remember (a <? 0)%L as az eqn:Haz.
symmetry in Haz.
destruct az. {
  apply rngl_ltb_lt in Haz.
  left.
  split; [ easy | ].
  remember (0 <? b)%L as zb eqn:Hzb.
  symmetry in Hzb.
  destruct zb; [ now apply rngl_ltb_lt in Hzb | exfalso ].
  apply (rngl_ltb_ge Hor) in Hzb.
  apply (rngl_nle_gt Hor) in Hab.
  apply Hab; clear Hab.
  apply (rngl_mul_nonpos_nonpos Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor) in Haz.
}
apply (rngl_ltb_ge Hor) in Haz.
right.
split. {
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  intros H; subst a.
  rewrite (rngl_mul_0_l Hos) in Hab.
  now apply (rngl_lt_irrefl Hor) in Hab.
}
apply (rngl_nle_gt Hor).
intros Hzb.
apply (rngl_nle_gt Hor) in Hab.
apply Hab; clear Hab.
now apply (rngl_mul_nonneg_nonneg Hop Hor).
Qed.

Theorem rngl_square_le_simpl_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b, (0 ≤ b → a * a ≤ b * b → a ≤ b)%L.
Proof.
intros Hop Hor Hii * Hzb Hab.
destruct (rngl_le_dec Hor a 0%L) as [Haz| Haz]. {
  now apply (rngl_le_trans Hor a 0%L b).
}
apply (rngl_nle_gt Hor) in Haz.
apply (rngl_nlt_ge Hor) in Hab.
apply (rngl_nlt_ge Hor).
intros Hba; apply Hab; clear Hab.
now apply (rngl_mul_lt_mono_nonneg Hop Hor Hii).
Qed.

Theorem rngl_div_le_mono_pos_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c, (0 < c)%L → (a ≤ b ↔ a / c ≤ b / c)%L.
Proof.
intros Hon Hop Hiv Hor Hi1.
intros * Hcz.
progress unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_le_mono_pos_r Hop Hor Hi1).
now apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
Qed.

Theorem rngl_div_nonneg :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → 0 < b → 0 ≤ a / b)%L.
Proof.
intros Hon Hop Hiv Hor * Ha Hb.
progress unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_nonneg_nonneg Hop Hor); [ easy | ].
apply (rngl_mul_le_mono_pos_l Hop Hor) with (c := b); [ | easy | ]. {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
rewrite rngl_mul_0_r; [ | now apply rngl_has_opp_or_subt_iff; left ].
rewrite (rngl_mul_inv_diag_r Hon Hiv); [ apply (rngl_0_le_1 Hon Hop Hor) | ].
apply (rngl_lt_iff Hor) in Hb.
now apply not_eq_sym.
Qed.

Theorem rngl_div_lt_pos:
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < a)%L → (0 < b)%L → (0 < a / b)%L.
Proof.
intros Hon Hop Hiv Hor * Ha Hb.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
progress unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_pos_pos Hop Hor Hii); [ easy | ].
now apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
Qed.

Theorem rngl_le_div_l :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 < c → a ≤ b * c ↔ a / c ≤ b)%L.
Proof.
intros Hon Hop Hiv Hor * Hzc.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
split; intros Habq. {
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii) with (c := c); [ easy | ].
  rewrite (rngl_div_mul Hon Hiv); [ easy | ].
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
} {
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii _ _ c) in Habq; [ | easy ].
  rewrite (rngl_div_mul Hon Hiv) in Habq; [ easy | ].
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
Qed.

Theorem rngl_le_div_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 < c → a * c ≤ b ↔ a ≤ b / c)%L.
Proof.
intros Hon Hop Hiv Hor * Hzc.
assert (Hcz : c ≠ 0%L). {
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
split; intros Habq. {
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii) with (c := c); [ easy | ].
  now rewrite (rngl_div_mul Hon Hiv).
} {
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii _ _ c) in Habq; [ | easy ].
  now rewrite (rngl_div_mul Hon Hiv) in Habq.
}
Qed.

Theorem rngl_lt_div_l :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 < c → a < b * c ↔ a / c < b)%L.
Proof.
intros Hon Hop Hiv Hor * Hzc.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
assert (Hcz : c ≠ 0%L). {
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
split; intros Habq. {
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii) with (a := c); [ easy | ].
  now rewrite (rngl_div_mul Hon Hiv).
} {
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii c) in Habq; [ | easy ].
  now rewrite (rngl_div_mul Hon Hiv) in Habq.
}
Qed.

Theorem rngl_lt_div_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 < c → a * c < b ↔ a < b / c)%L.
Proof.
intros Hon Hop Hiv Hor * Hzc.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
assert (Hcz : c ≠ 0%L). {
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
split; intros Habq. {
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii) with (a := c); [ easy | ].
  now rewrite (rngl_div_mul Hon Hiv).
} {
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii c) in Habq; [ | easy ].
  now rewrite (rngl_div_mul Hon Hiv) in Habq.
}
Qed.

Theorem rngl_pow_1_l : rngl_has_1 T = true → ∀ n, (1 ^ n = 1)%L.
Proof.
intros Hon *.
induction n; [ easy | cbn ].
rewrite IHn.
apply (rngl_mul_1_l Hon).
Qed.

Theorem rngl_pow_mul_l :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  ∀ a b n, ((a * b) ^ n = a ^ n * b ^ n)%L.
Proof.
intros Hic Hon *.
induction n; cbn. {
  symmetry; apply (rngl_mul_1_l Hon).
}
do 2 rewrite <- rngl_mul_assoc.
f_equal.
rewrite IHn.
rewrite (rngl_mul_comm Hic).
rewrite <- rngl_mul_assoc.
f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem rngl_pow_mul_r :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  ∀ a m n, (a ^ (m * n) = (a ^ m) ^ n)%L.
Proof.
intros Hic Hon *.
revert n.
induction m; intros. {
  symmetry; apply (rngl_pow_1_l Hon).
}
rewrite rngl_pow_succ_r.
cbn.
rewrite (rngl_pow_add_r Hon).
rewrite IHm.
symmetry.
apply (rngl_pow_mul_l Hic Hon).
Qed.

Theorem rngl_pow_squ :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  ∀ a n, ((a ^ n)² = a ^ (2 * n))%L.
Proof.
intros Hic Hon *.
rewrite (rngl_squ_pow_2 Hon).
rewrite Nat.mul_comm.
now rewrite (rngl_pow_mul_r Hic Hon).
Qed.

Theorem rngl_pow_pos_nonneg :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  ∀ a n, (0 < a → 0 < a ^ n)%L.
Proof.
intros Hon Hop Hiv Hc1 Hor * Hza.
induction n; cbn. {
  apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
}
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
now apply (rngl_mul_pos_pos Hop Hor Hii).
Qed.

Theorem rngl_pow_ge_1 :
  rngl_has_opp T = true →
  rngl_has_1 T = true →
  rngl_is_ordered T = true →
  ∀ a n, (1 ≤ a → 1 ≤ a ^ n)%L.
Proof.
intros Hop Hon Hor * Hza.
induction n; [ apply (rngl_le_refl Hor) | cbn ].
rewrite <- (rngl_mul_1_l Hon 1%L).
apply (rngl_mul_le_compat_nonneg Hop Hor). {
  split; [ | easy ].
  apply (rngl_0_le_1 Hon Hop Hor).
} {
  split; [ | easy ].
  apply (rngl_0_le_1 Hon Hop Hor).
}
Qed.

Theorem rngl_pow_1_r :
  rngl_has_1 T = true →
  ∀ a, (a ^ 1)%L = a.
Proof.
intros Hon *; cbn.
apply (rngl_mul_1_r Hon).
Qed.

Theorem rngl_pow_le_mono_r :
  rngl_has_opp T = true →
  rngl_has_1 T = true →
  rngl_is_ordered T = true →
  ∀ a m n, (1 ≤ a)%L → m ≤ n → (a ^ m ≤ a ^ n)%L.
Proof.
intros Hop Hon Hor * H1a Hmn.
revert n Hmn.
induction m; intros; cbn. {
  now apply (rngl_pow_ge_1 Hop Hon Hor).
}
destruct n; [ easy | cbn ].
apply Nat.succ_le_mono in Hmn.
apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
  apply (rngl_le_trans Hor _ 1%L); [ | easy ].
  apply (rngl_0_le_1 Hon Hop Hor).
}
now apply IHm.
Qed.

Theorem rngl_le_0_mul :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a * b → 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0)%L.
Proof.
intros Hon Hop Hiv Hor * Hab.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (rngl_le_dec Hor 0 a)%L as [Hza| Hza]. {
  destruct (rngl_lt_dec Hor 0 a)%L as [Hlza| Hlza]. 2: {
    apply (rngl_nlt_ge Hor) in Hlza.
    apply (rngl_le_antisymm Hor) in Hza; [ | easy ].
    subst a.
    destruct (rngl_le_dec Hor 0 b)%L as [Hzb| Hzb]; [ now left | ].
    apply (rngl_nle_gt Hor), (rngl_lt_le_incl Hor) in Hzb.
    now right.
  }
  rewrite <- (rngl_mul_0_r Hos a) in Hab.
  now left; apply (rngl_mul_le_mono_pos_l Hop Hor Hii) in Hab.
} {
  apply (rngl_nle_gt Hor) in Hza.
  right.
  rewrite <- (rngl_mul_0_l Hos b) in Hab.
  split; [ now apply (rngl_lt_le_incl Hor) | ].
  apply (rngl_nle_gt Hor) in Hza.
  apply (rngl_nlt_ge Hor).
  intros Hzb; apply Hza.
  now apply (rngl_mul_le_mono_pos_r Hop Hor Hii) in Hab.
}
Qed.

Theorem rngl_middle_sub_l :
   rngl_has_1 T = true →
   rngl_has_opp T = true →
   rngl_has_inv T = true →
   rngl_is_ordered T = true →
   ∀ a b, (((a + b) / 2 - a) = (b - a) / 2)%L.
Proof.
intros Hon Hop Hiv Hor *.
progress unfold rngl_div.
rewrite Hiv.
rewrite rngl_mul_add_distr_r.
rewrite (rngl_mul_sub_distr_r Hop).
rewrite rngl_add_comm.
progress unfold rngl_sub.
rewrite Hop.
rewrite <- rngl_add_assoc; f_equal.
rewrite (rngl_add_opp_r Hop).
rewrite <- (rngl_mul_1_r Hon a) at 2.
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite <- (rngl_mul_opp_r Hop).
f_equal.
rewrite <- (rngl_opp_involutive Hop (_ - _))%L.
f_equal.
rewrite (rngl_opp_sub_distr Hop).
apply (rngl_one_sub_half Hon Hop Hiv Hor).
Qed.

Theorem rngl_middle_sub_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (b - (a + b) / 2 = (b - a) / 2)%L.
Proof.
intros Hon Hop Hiv Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
progress unfold rngl_div.
rewrite Hiv.
rewrite rngl_mul_add_distr_r.
rewrite (rngl_mul_sub_distr_r Hop).
rewrite rngl_add_comm.
rewrite (rngl_sub_add_distr Hos).
f_equal.
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
f_equal.
apply (rngl_one_sub_half Hon Hop Hiv Hor).
Qed.

Theorem rngl_abs_le_squ_le :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (rngl_abs a ≤ rngl_abs b → a² ≤ b²)%L.
Proof.
intros Hop Hor * Hab.
progress unfold rngl_squ.
progress unfold rngl_abs in Hab.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
remember (b ≤? 0)%L as bz eqn:Hbz; symmetry in Hbz.
destruct az. {
  apply rngl_leb_le in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Hab.
    now apply (rngl_mul_le_compat_nonpos Hop Hor).
  } {
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Haz.
    rewrite (rngl_opp_0 Hop) in Haz.
    rewrite <- (rngl_mul_opp_opp Hop).
    apply (rngl_lt_le_incl Hor) in Hbz.
    now apply (rngl_mul_le_compat_nonneg Hop Hor).
  }
} {
  apply (rngl_leb_gt Hor) in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Hbz.
    rewrite (rngl_opp_0 Hop) in Hbz.
    rewrite <- (rngl_mul_opp_opp Hop b).
    apply (rngl_lt_le_incl Hor) in Haz.
    now apply (rngl_mul_le_compat_nonneg Hop Hor).
  } {
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_lt_le_incl Hor) in Haz, Hbz.
    now apply (rngl_mul_le_compat_nonneg Hop Hor).
  }
}
Qed.

Theorem rngl_abs_lt_squ_lt :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
  ∀ a b : T, (rngl_abs a < rngl_abs b)%L → (a² < b²)%L.
Proof.
intros Hic Hop Hor Hii * Hab.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_abs_le_squ_le Hop Hor).
  now apply (rngl_lt_le_incl Hor).
}
intros H.
apply (eq_rngl_squ_rngl_abs Hop Hic Hor Hii) in H.
rewrite H in Hab.
now apply (rngl_lt_irrefl Hor) in Hab.
Qed.

Theorem rngl_squ_le_abs_le :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b, (a² ≤ b² → rngl_abs a ≤ rngl_abs b)%L.
Proof.
intros Hop Hor Hii * Hab.
progress unfold rngl_squ in Hab.
progress unfold rngl_abs.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
remember (b ≤? 0)%L as bz eqn:Hbz; symmetry in Hbz.
destruct az. {
  apply rngl_leb_le in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    rewrite <- (rngl_mul_opp_opp Hop) in Hab.
    rewrite <- (rngl_mul_opp_opp Hop b) in Hab.
    apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in Hab; [ easy | ].
    rewrite <- (rngl_opp_0 Hop).
    now apply -> (rngl_opp_le_compat Hop Hor).
  } {
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Haz.
    rewrite (rngl_opp_0 Hop) in Haz.
    rewrite <- (rngl_mul_opp_opp Hop) in Hab.
    apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in Hab; [ easy | ].
    now apply (rngl_lt_le_incl Hor).
  }
} {
  apply (rngl_leb_gt Hor) in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Hbz.
    rewrite (rngl_opp_0 Hop) in Hbz.
    rewrite <- (rngl_mul_opp_opp Hop b) in Hab.
    now apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in Hab.
  } {
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_lt_le_incl Hor) in Haz, Hbz.
    now apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in Hab.
  }
}
Qed.

Theorem rngl_squ_lt_abs_lt :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (a² < b²)%L → (rngl_abs a < rngl_abs b)%L.
Proof.
intros Hop Hor Hii * Hab.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_squ_le_abs_le Hop Hor Hii).
  now apply (rngl_lt_le_incl Hor).
}
intros H.
apply (f_equal rngl_squ) in H.
do 2 rewrite (rngl_squ_abs Hop) in H.
rewrite H in Hab.
now apply (rngl_lt_irrefl Hor) in Hab.
Qed.

Theorem rngl_abs_le_ε :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a,
  (∀ ε, (0 < ε)%L → (rngl_abs a ≤ ε)%L)
  → a = 0%L.
Proof.
intros Hon Hop Hiv Hor * H1.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  apply (rngl_characteristic_1 Hon Hos Hc1).
}
destruct (rngl_lt_dec Hor a 0%L) as [H12| H12]. {
  specialize (H1 (- a / 2))%L.
  assert (H : (0 < - a / 2)%L). {
    progress unfold rngl_div.
    rewrite Hiv.
    apply (rngl_mul_pos_pos Hop Hor Hii). {
      rewrite <- (rngl_opp_0 Hop).
      now apply -> (rngl_opp_lt_compat Hop Hor).
    }
    apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  specialize (H1 H); clear H.
  exfalso.
  apply (rngl_nlt_ge Hor) in H1; apply H1; clear H1.
  rewrite (rngl_abs_nonpos_eq Hop Hor). 2: {
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_lt_div_l Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  remember (_ * _)%L as x.
  rewrite <- (rngl_mul_1_r Hon (- a))%L.
  subst x.
  apply (rngl_mul_lt_mono_pos_l Hop Hor Hii). 2: {
    apply (rngl_lt_add_r Hos Hor).
    apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
  }
  rewrite <- (rngl_opp_0 Hop).
  now apply -> (rngl_opp_lt_compat Hop Hor).
}
destruct (rngl_lt_dec Hor 0%L a) as [H21| H21]. {
  specialize (H1 (a / 2))%L.
  assert (H : (0 < a / 2)%L). {
    progress unfold rngl_div.
    rewrite Hiv.
    apply (rngl_mul_pos_pos Hop Hor Hii); [ easy | ].
    apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  specialize (H1 H); clear H.
  exfalso.
  apply (rngl_nlt_ge Hor) in H1; apply H1.
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_lt_div_l Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
  }
  rewrite rngl_mul_add_distr_l.
  rewrite (rngl_mul_1_r Hon).
  now apply (rngl_lt_add_r Hos Hor).
}
apply (rngl_nlt_ge Hor) in H12, H21.
now apply (rngl_le_antisymm Hor).
Qed.

Theorem rngl_add_neg_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a < 0)%L → (b ≤ 0)%L → (a + b < 0)%L.
Proof.
intros Hop Hor * Haz Hbz.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
eapply (rngl_lt_le_trans Hor); [ | apply Hbz ].
apply (rngl_lt_add_lt_sub_r Hop Hor).
now rewrite (rngl_sub_diag Hos).
Qed.

Theorem rngl_add_nonpos_neg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ 0)%L → (b < 0)%L → (a + b < 0)%L.
Proof.
intros Hop Hor * Haz Hbz.
rewrite rngl_add_comm.
now apply (rngl_add_neg_nonpos Hop Hor).
Qed.

Theorem rngl_leb_opp_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (-a ≤? b)%L = (-b ≤? a)%L.
Proof.
intros Hop Hor *.
remember (-a ≤? b)%L as ab eqn:Hab.
symmetry in Hab.
symmetry.
destruct ab. {
  apply rngl_leb_le in Hab.
  apply rngl_leb_le.
  apply (rngl_le_opp_l Hop Hor) in Hab.
  rewrite rngl_add_comm in Hab.
  now apply (rngl_le_opp_l Hop Hor) in Hab.
} {
  apply (rngl_leb_gt Hor) in Hab.
  apply (rngl_leb_gt Hor).
  apply (rngl_lt_opp_r Hop Hor).
  rewrite rngl_add_comm.
  now apply (rngl_lt_opp_r Hop Hor).
}
Qed.

Theorem rngl_leb_opp_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤? -b)%L = (b ≤? -a)%L.
Proof.
intros Hop Hor *.
remember (a ≤? -b)%L as ab eqn:Hab.
symmetry in Hab.
symmetry.
destruct ab. {
  apply rngl_leb_le in Hab.
  apply rngl_leb_le.
  apply (rngl_le_opp_r Hop Hor) in Hab.
  rewrite rngl_add_comm in Hab.
  now apply (rngl_le_opp_r Hop Hor) in Hab.
} {
  apply (rngl_leb_gt Hor) in Hab.
  apply (rngl_leb_gt Hor).
  apply (rngl_lt_opp_l Hop Hor).
  rewrite rngl_add_comm.
  now apply (rngl_lt_opp_l Hop Hor).
}
Qed.

Theorem rngl_leb_0_opp :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤? - a)%L = (a ≤? 0)%L.
Proof.
intros Hop Hor *.
rewrite (rngl_leb_opp_r Hop Hor).
now rewrite (rngl_opp_0 Hop).
Qed.

Theorem rngl_ltb_opp_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (-a <? b)%L = (-b <? a)%L.
Proof.
intros Hop Hor *.
remember (-a <? b)%L as ab eqn:Hab.
symmetry in Hab.
symmetry.
destruct ab. {
  apply rngl_ltb_lt in Hab.
  apply rngl_ltb_lt.
  apply (rngl_lt_opp_l Hop Hor) in Hab.
  rewrite rngl_add_comm in Hab.
  now apply (rngl_lt_opp_l Hop Hor) in Hab.
} {
  apply (rngl_ltb_ge Hor) in Hab.
  apply (rngl_ltb_ge Hor).
  apply (rngl_le_opp_r Hop Hor).
  rewrite rngl_add_comm.
  now apply (rngl_le_opp_r Hop Hor).
}
Qed.

Theorem rngl_ltb_opp_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a <? -b)%L = (b <? -a)%L.
Proof.
intros Hop Hor *.
remember (a <? -b)%L as ab eqn:Hab.
symmetry in Hab.
symmetry.
destruct ab. {
  apply rngl_ltb_lt in Hab.
  apply rngl_ltb_lt.
  apply (rngl_lt_opp_r Hop Hor) in Hab.
  rewrite rngl_add_comm in Hab.
  now apply (rngl_lt_opp_r Hop Hor) in Hab.
} {
  apply (rngl_ltb_ge Hor) in Hab.
  apply (rngl_ltb_ge Hor).
  apply (rngl_le_opp_l Hop Hor).
  rewrite rngl_add_comm.
  now apply (rngl_le_opp_l Hop Hor).
}
Qed.

(* characteristic *)

Theorem rngl_characteristic_non_0 :
  rngl_has_1 T = true →
  rngl_characteristic T ≠ 0 →
  (∀ i : nat, 0 < i < rngl_characteristic T → rngl_of_nat i ≠ 0%L) ∧
  rngl_of_nat (rngl_characteristic T) = 0%L.
Proof.
intros Hon Hcz.
specialize (rngl_opt_characteristic_prop) as H1.
apply Nat.eqb_neq in Hcz.
now rewrite Hon, Hcz in H1.
Qed.

(* archimedianity *)

Theorem rngl_archimedean :
  rngl_is_archimedean T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 < a)%L → ∃ n, (b < rngl_mul_nat a n)%L.
Proof.
intros Har Hor.
specialize rngl_opt_archimedean as H1.
now rewrite Har, Hor in H1.
Qed.

Theorem rngl_archimedean_ub :
  rngl_is_archimedean T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < a < b)%L →
  ∃ n : nat, (rngl_mul_nat a n ≤ b < rngl_mul_nat a (n + 1))%L.
Proof.
intros Har Hor * (Ha, Hab).
specialize rngl_opt_archimedean as H1.
rewrite Har, Hor in H1; cbn in H1.
specialize (H1 a b Ha).
destruct H1 as (m, Hm).
induction m. {
  exfalso; cbn in Hm.
  apply (rngl_nle_gt Hor) in Hm.
  apply Hm; clear Hm.
  now apply (rngl_le_trans Hor _ a); apply (rngl_lt_le_incl Hor).
}
destruct (rngl_le_dec Hor (rngl_mul_nat a m) b) as [Hba| Hba]. {
  now exists m; rewrite Nat.add_1_r.
}
apply (rngl_nle_gt Hor) in Hba.
now apply IHm.
Qed.

Theorem int_part :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  rngl_is_archimedean T = true →
  ∀ a, ∃ n, (rngl_of_nat n ≤ rngl_abs a < rngl_of_nat (n + 1))%L.
Proof.
intros Hon Hop Hc1 Hor Har *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_archimedean_ub Har Hor) as H1.
destruct (rngl_lt_dec Hor (rngl_abs a) 1)%L as [H1x| H1x]. {
  exists 0; cbn.
  rewrite rngl_add_0_r.
  split; [ | easy ].
  apply (rngl_abs_nonneg Hop Hor).
}
destruct (rngl_lt_dec Hor 1 (rngl_abs a))%L as [Hx1| Hx1]. 2: {
  apply (rngl_nlt_ge Hor) in H1x, Hx1.
  apply (rngl_le_antisymm Hor) in H1x; [ | easy ].
  rewrite H1x.
  exists 1; cbn.
  rewrite rngl_add_0_r.
  split; [ apply (rngl_le_refl Hor) | ].
  apply (rngl_lt_iff Hor).
  split. 2: {
    intros H12.
    apply (f_equal (λ b, rngl_sub b 1))%L in H12.
    rewrite (rngl_sub_diag Hos) in H12.
    rewrite (rngl_add_sub Hos) in H12.
    symmetry in H12; revert H12.
    apply (rngl_1_neq_0_iff Hon), Hc1.
  }
  apply (rngl_le_add_r Hor).
  apply (rngl_0_le_1 Hon Hop Hor).
}
clear H1x.
apply (H1 1 (rngl_abs a))%L.
split; [ apply (rngl_0_lt_1 Hon Hop Hc1 Hor) | easy ].
Qed.

(* (-1) ^ n *)

Definition minus_one_pow n :=
  match n mod 2 with
  | 0 => 1%L
  | _ => (- 1%L)%L
  end.

Theorem minus_one_pow_succ :
  rngl_has_opp T = true →
  ∀ i, minus_one_pow (S i) = (- minus_one_pow i)%L.
Proof.
intros Hop *.
unfold minus_one_pow.
remember (i mod 2) as k eqn:Hk; symmetry in Hk.
destruct k. {
  apply Nat.Div0.mod_divides in Hk.
  destruct Hk as (k, Hk); subst i.
  rewrite <- Nat.add_1_l, Nat.mul_comm.
  now rewrite Nat.Div0.mod_add.
}
destruct k. {
  rewrite <- Nat.add_1_l.
  rewrite <- Nat.Div0.add_mod_idemp_r.
  rewrite Hk; cbn.
  symmetry.
  now apply rngl_opp_involutive.
}
specialize (Nat.mod_upper_bound i 2) as H1.
assert (H : 2 ≠ 0) by easy.
specialize (H1 H); clear H.
rewrite Hk in H1.
do 2 apply Nat.succ_lt_mono in H1.
easy.
Qed.

Theorem minus_one_pow_add :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a b, minus_one_pow (a + b) = (minus_one_pow a * minus_one_pow b)%L.
Proof.
intros Hon Hop *.
induction a; cbn; [ now rewrite rngl_mul_1_l | ].
rewrite (minus_one_pow_succ Hop).
rewrite (minus_one_pow_succ Hop).
rewrite IHa.
now rewrite rngl_mul_opp_l.
Qed.

(* end (-1) ^ n *)

(* comparison *)

Definition rngl_compare a b :=
  if (a =? b)%L then Eq
  else if (a ≤? b)%L then Lt else Gt.

Theorem rngl_compare_eq_iff :
  rngl_has_eq_dec T = true →
  ∀ a b, rngl_compare a b = Eq ↔ a = b.
Proof.
intros Hed *.
progress unfold rngl_compare.
remember (a =? b)%L as ab eqn:Hab.
symmetry in Hab.
destruct ab. {
  split; [ | easy ].
  now apply (rngl_eqb_eq Hed) in Hab.
} {
  destruct (a ≤? b)%L. {
    split; [ easy | ].
    now apply (rngl_eqb_neq Hed) in Hab.
  } {
    split; [ easy | ].
    now apply (rngl_eqb_neq Hed) in Hab.
  }
}
Qed.

Theorem rngl_compare_lt_iff :
  rngl_is_ordered T = true →
  rngl_has_eq_dec T = true →
  ∀ a b, rngl_compare a b = Lt ↔ (a < b)%L.
Proof.
intros Hor Hed *.
progress unfold rngl_compare.
remember (a =? b)%L as ab eqn:Hab.
remember (a ≤? b)%L as alb eqn:Halb.
symmetry in Hab, Halb.
destruct ab. {
  split; [ easy | intros H ].
  apply (rngl_eqb_eq Hed) in Hab.
  subst b.
  now apply (rngl_lt_irrefl Hor) in H.
} {
  apply (rngl_eqb_neq Hed) in Hab.
  destruct alb. {
    apply rngl_leb_le in Halb.
    split; [ | easy ].
    intros _.
    now apply (rngl_lt_iff Hor).
  } {
    split; [ easy | ].
    apply (rngl_leb_gt Hor) in Halb.
    intros H.
    now apply (rngl_lt_asymm Hor) in H.
  }
}
Qed.

Theorem rngl_compare_gt_iff :
  rngl_is_ordered T = true →
  rngl_has_eq_dec T = true →
  ∀ a b, rngl_compare a b = Gt ↔ (b < a)%L.
Proof.
intros Hor Hed *.
progress unfold rngl_compare.
remember (a =? b)%L as ab eqn:Hab.
remember (a ≤? b)%L as alb eqn:Halb.
symmetry in Hab, Halb.
destruct ab. {
  split; [ easy | intros H ].
  apply (rngl_eqb_eq Hed) in Hab.
  subst b.
  now apply (rngl_lt_irrefl Hor) in H.
} {
  apply (rngl_eqb_neq Hed) in Hab.
  destruct alb. {
    apply rngl_leb_le in Halb.
    split; [ easy | ].
    intros H.
    now apply (rngl_nle_gt Hor) in H.
  } {
    now apply (rngl_leb_gt Hor) in Halb.
  }
}
Qed.

Theorem rngl_compare_refl :
  rngl_has_eq_dec T = true →
  ∀ a, rngl_compare a a = Eq.
Proof.
intros Hed *.
now apply (rngl_compare_eq_iff Hed).
Qed.

Notation "x ?= y" := (rngl_compare x y) : ring_like_scope.

(* *)

Record charac_0_field :=
  { cf_has_1 : rngl_has_1 T = true;
    cf_mul_is_comm : rngl_mul_is_comm T = true;
    cf_has_opp : rngl_has_opp T = true;
    cf_has_inv : rngl_has_inv T = true;
    cf_has_eq_dec : rngl_has_eq_dec T = true;
    cf_characteristic : rngl_characteristic T = 0 }.

End a.

(* to be able to use tactic "ring" *)

Require Import Ring_theory.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context (Hic : @rngl_mul_is_comm T ro rp = true).
Context (Hop : @rngl_has_opp T ro = true).
Context (Hon : @rngl_has_1 T ro = true).

Theorem rngl_Ropp_def : ∀ x : T, (x + - x)%L = 0%L.
Proof.
intros.
rewrite (rngl_add_opp_r Hop).
apply rngl_sub_diag.
now apply rngl_has_opp_or_subt_iff; left.
Qed.

Definition rngl_ring_theory
    : ring_theory 0%L 1%L rngl_add rngl_mul rngl_sub rngl_opp eq :=
  {| Radd_0_l := rngl_add_0_l;
     Radd_comm := rngl_add_comm;
     Radd_assoc := rngl_add_assoc;
     Rmul_1_l := rngl_mul_1_l Hon;
     Rmul_comm := rngl_mul_comm Hic;
     Rmul_assoc := rngl_mul_assoc;
     Rdistr_l := rngl_mul_add_distr_r;
     Rsub_def x y := eq_sym (rngl_add_opp_r Hop x y);
     Ropp_def := rngl_Ropp_def |}.

End a.

(* code to be added to be able to use the Coq tactic "ring"

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {Hic : @rngl_mul_is_comm T ro rp = true}.
Context {Hop : @rngl_has_opp T T ro = true}.

Require Import Ring.
Add Ring rngl_ring : (@rngl_ring_theory T ro rp Hic Hop).

(* example *)

Example a2_b2 : ∀ a b, ((a + b) * (a - b) = a * a - b * b)%L.
Proof.
intros.
ring_simplify. (* just to see what happens *)
easy.
Qed.
*)

Arguments rngl_abs {T ro} a%_L.
Arguments rngl_abs_nonneg_eq {T ro rp} Hop Hor a%_L.
Arguments rngl_add {T ring_like_op} (a b)%_L.
Arguments rngl_add_comm {T ro ring_like_prop} (a b)%_L.
Arguments rngl_add_sub {T ro rp} Hom (a b)%_L.
Arguments rngl_characteristic_1 {T ro rp} Hon Hos Hch x%_L.
Arguments rngl_div_add_distr_r {T ro rp} Hiv (a b c)%_L.
Arguments rngl_div_le_mono_pos_r {T ro rp} Hon Hop Hiv Hor Hii (a b c)%_L.
Arguments rngl_eq_dec {T ro} Hed (a b)%_L.
Arguments rngl_le_add_r {T ro rp} Hor (a b)%_L Hb.
Arguments rngl_le_dec {T ro rp} Hor (a b)%_L.
Arguments rngl_le_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_le_lt_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_lt_le_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_lt_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_lt_dec {T ro rp} Hor (a b)%_L.
Arguments rngl_min {T ro} (a b)%_L.
Arguments rngl_mul {T ring_like_op} (a b)%_L.
Arguments rngl_mul_comm {T ro rp} Hic (a b)%_L.
Arguments rngl_mul_le_mono_pos_l {T ro rp} Hop Hor Hii (a b c)%_L.
Arguments rngl_mul_le_mono_pos_r {T ro rp} Hop Hor Hii (a b c)%_L.
Arguments rngl_mul_nat {T ro} a%_L n%_nat.
Arguments rngl_mul_0_r {T ro rp} Hom a%_L.
Arguments rngl_mul_1_r {T ro rp} Hon a%_L.
Arguments rngl_pow_squ {T ro rp} Hic Hon a%_L n%_nat.
Arguments rngl_squ {T ro} x%_L.
Arguments rngl_sub {T ro} (a b)%_L.
Arguments rngl_subt {T ro} (a b)%_L.

Arguments charac_0_field T%_type {ro rp}.
