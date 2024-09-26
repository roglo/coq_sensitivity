Require Import Utf8 Arith.
Require Import RingLike_structures.
Require Import RingLike_order.
Require Import RingLike_add.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

(* not needing order *)

Theorem rngl_mul_comm :
  rngl_mul_is_comm T = true →
  ∀ a b, (a * b = b * a)%L.
Proof.
intros H1 *.
specialize rngl_opt_mul_comm as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_mul_add_distr_r : ∀ x y z,
  ((x + y) * z = x * z + y * z)%L.
Proof.
intros x y z; simpl.
specialize rngl_opt_mul_add_distr_r as rngl_mul_add_distr_r.
remember (rngl_mul_is_comm T) as ic eqn:Hic.
symmetry in Hic.
destruct ic. {
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_comm; [ | easy ].
  now rewrite (rngl_mul_comm Hic z).
} {
  apply rngl_mul_add_distr_r.
}
Qed.

Theorem rngl_mul_0_r :
  rngl_has_opp_or_subt T = true →
  ∀ a, (a * 0 = 0)%L.
Proof.
intros Hos *.
apply (rngl_add_cancel_r Hos _ _ (a * 1)%L).
rewrite <- rngl_mul_add_distr_l.
now do 2 rewrite rngl_add_0_l.
Qed.

Theorem rngl_mul_0_l :
  rngl_has_opp_or_subt T = true →
  ∀ a, (0 * a = 0)%L.
Proof.
intros Hom a.
apply (rngl_add_cancel_r Hom _ _ (1 * a)%L).
rewrite <- rngl_mul_add_distr_r.
now do 2 rewrite rngl_add_0_l.
Qed.

Theorem rngl_mul_1_l :
  rngl_has_1 T = true →
  ∀ a, (1 * a = a)%L.
Proof.
intros Hon *.
specialize rngl_opt_mul_1_l as H1.
rewrite Hon in H1.
apply H1.
Qed.

Theorem rngl_mul_1_r :
  rngl_has_1 T = true →
  ∀ a, (a * 1 = a)%L.
Proof.
intros Hon *.
specialize rngl_opt_mul_1_l as H1.
specialize rngl_opt_mul_1_r as H2.
rewrite Hon in H1, H2.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
now rewrite rngl_mul_comm, rngl_mul_1_l.
Qed.

Theorem rngl_mul_inv_diag_l :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ a : T, a ≠ 0%L → (a⁻¹ * a = 1)%L.
Proof.
intros Hon Hiv *.
specialize rngl_opt_mul_inv_diag_l as H.
rewrite Hiv, Hon in H.
apply H.
Qed.

Theorem rngl_mul_inv_diag_r :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ a : T, a ≠ 0%L → (a * a⁻¹ = 1)%L.
Proof.
intros Hon Hiv * Haz.
specialize rngl_opt_mul_inv_diag_r as rngl_mul_inv_diag_r.
unfold rngl_div in rngl_mul_inv_diag_r.
rewrite Hiv in rngl_mul_inv_diag_r; cbn in rngl_mul_inv_diag_r.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic. {
  rewrite (rngl_mul_comm Hic).
  now apply (rngl_mul_inv_diag_l Hon Hiv).
}
cbn in rngl_mul_inv_diag_r.
rewrite Hon in rngl_mul_inv_diag_r.
now apply rngl_mul_inv_diag_r.
Qed.

Theorem rngl_add_diag :
  rngl_has_1 T = true →
  ∀ a, (a + a = 2 * a)%L.
Proof.
intros Hon *.
rewrite rngl_mul_add_distr_r.
now rewrite (rngl_mul_1_l Hon).
Qed.

Theorem rngl_add_diag2 :
  rngl_has_1 T = true →
  ∀ a, (a + a = a * 2)%L.
Proof.
intros Hon *.
rewrite rngl_mul_add_distr_l.
now rewrite (rngl_mul_1_r Hon).
Qed.

Theorem rngl_mul_mul_swap :
  rngl_mul_is_comm T = true →
  ∀ a b c, (a * b * c = a * c * b)%L.
Proof.
intros Hic *.
do 2 rewrite <- rngl_mul_assoc.
f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem rngl_div_div_swap :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ a b c,
  (a / b / c = a / c / b)%L.
Proof.
intros Hic Hin *.
progress unfold rngl_div.
now rewrite Hin, rngl_mul_mul_swap.
Qed.

Theorem rngl_div_diag :
  rngl_has_1 T = true →
  rngl_has_inv_or_quot T = true →
  ∀ a : T, a ≠ 0%L → (a / a = 1)%L.
Proof.
intros Hon Hiq * Haz.
remember (rngl_has_inv T) as ai eqn:Hai; symmetry in Hai.
destruct ai. {
  remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
  destruct ic. {
    unfold rngl_div; rewrite Hai.
    rewrite rngl_mul_comm; [ | easy ].
    now apply rngl_mul_inv_diag_l.
  }
  specialize rngl_opt_mul_inv_diag_r as rngl_mul_inv_diag_r.
  rewrite Hai, Hon, Hic in rngl_mul_inv_diag_r; cbn in rngl_mul_inv_diag_r.
  now apply rngl_mul_inv_diag_r.
}
remember (rngl_has_quot T) as qu eqn:Hqu; symmetry in Hqu.
destruct qu. {
  specialize rngl_opt_mul_div as rngl_mul_div.
  rewrite Hqu in rngl_mul_div.
  specialize (rngl_mul_div 1%L a Haz).
  now rewrite rngl_mul_1_l in rngl_mul_div.
}
apply rngl_has_inv_or_quot_iff in Hiq.
destruct Hiq; congruence.
Qed.

Theorem rngl_mul_inv_r :
  rngl_has_inv T = true →
  ∀ a b, (a * b⁻¹)%L = (a / b)%L.
Proof.
intros Hin *.
now unfold rngl_div; rewrite Hin.
Qed.

Theorem rngl_mul_div :
  rngl_has_inv_and_1_or_quot T = true →
  ∀ a b : T, b ≠ 0%L → (a * b / b)%L = a.
Proof.
intros Hii a b Hbz.
remember (rngl_has_inv T) as iv eqn:Hiv; symmetry in Hiv.
destruct iv. {
  specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
  assert (Hon : rngl_has_1 T = true). {
    apply rngl_has_inv_and_1_or_quot_iff in Hii.
    destruct Hii as [Hii| Hii]; [ easy | ].
    apply rngl_has_quot_has_no_inv in Hii.
    congruence.
  }
  progress unfold rngl_div.
  rewrite Hiv.
  rewrite <- rngl_mul_assoc.
  rewrite rngl_mul_inv_r; [ | easy ].
  rewrite rngl_div_diag; [ | easy | easy | easy ].
  now apply rngl_mul_1_r.
}
remember (rngl_has_quot T) as qu eqn:Hqu; symmetry in Hqu.
destruct qu. {
  specialize rngl_opt_mul_div as mul_div.
  rewrite Hqu in mul_div.
  now apply mul_div.
}
apply rngl_has_inv_and_1_or_quot_iff in Hii.
destruct Hii as [(H1, H2)|]; congruence.
Qed.

Theorem rngl_div_mul :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ a b, b ≠ 0%L → (a / b * b)%L = a.
Proof.
intros Hon Hiv * Hbz.
unfold rngl_div.
rewrite Hiv.
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_inv_diag_l Hon Hiv _ Hbz).
apply (rngl_mul_1_r Hon).
Qed.

Theorem rngl_mul_cancel_l :
  rngl_has_inv_and_1_or_quot T = true →
  ∀ a b c, a ≠ 0%L
  → (a * b = a * c)%L
  → b = c.
Proof.
intros Hii * Haz Habc.
remember (rngl_has_inv T) as iv eqn:Hiv.
symmetry in Hiv.
destruct iv. {
  assert (Hon : rngl_has_1 T = true). {
    apply rngl_has_inv_and_1_or_quot_iff in Hii.
    destruct Hii as [| Hii]; [ easy | ].
    apply rngl_has_quot_has_no_inv in Hii.
    congruence.
  }
  apply (f_equal (λ x, rngl_mul (a⁻¹)%L x)) in Habc.
  do 2 rewrite rngl_mul_assoc in Habc.
  rewrite rngl_mul_inv_diag_l in Habc; [ | easy | easy | easy ].
  now do 2 rewrite (rngl_mul_1_l Hon) in Habc.
}
remember (rngl_has_quot T) as qu eqn:Hqu.
symmetry in Hqu.
destruct qu. {
  apply (f_equal (λ x, rngl_div x a)) in Habc.
  remember (rngl_mul_is_comm T) as ic eqn:Hic.
  symmetry in Hic.
  destruct ic. {
    do 2 rewrite (rngl_mul_comm Hic a) in Habc.
    specialize rngl_opt_mul_div as mul_div.
    rewrite Hqu in mul_div.
    rewrite mul_div in Habc; [ | easy ].
    rewrite mul_div in Habc; [ | easy ].
    easy.
  } {
    specialize rngl_opt_mul_quot_r as mul_quot_r.
    rewrite Hqu, Hic in mul_quot_r.
    cbn in mul_quot_r.
    rewrite mul_quot_r in Habc; [ | easy ].
    rewrite mul_quot_r in Habc; [ | easy ].
    easy.
  }
}
apply rngl_has_inv_and_1_or_quot_iff in Hii.
destruct Hii as [(H1, H2)| ]; congruence.
Qed.

Theorem rngl_mul_opp_r :
  rngl_has_opp T = true →
  ∀ a b, (a * - b = - (a * b))%L.
Proof.
intros Hro *.
specialize (rngl_mul_add_distr_l a b (- b)%L) as H.
rewrite rngl_add_opp_r in H; [ | easy ].
rewrite rngl_sub_diag in H; [ | now apply rngl_has_opp_or_subt_iff; left ].
rewrite rngl_mul_0_r in H; [ | now apply rngl_has_opp_or_subt_iff; left ].
symmetry in H.
rewrite rngl_add_comm in H.
now apply rngl_add_move_0_r in H.
Qed.

Theorem rngl_mul_sub_distr_l :
  rngl_has_opp T = true →
  ∀ a b c, (a * (b - c) = a * b - a * c)%L.
Proof.
intros Hop *.
unfold rngl_sub; rewrite Hop.
rewrite rngl_mul_add_distr_l.
now rewrite rngl_mul_opp_r.
Qed.

Theorem rngl_add_mul_r_diag_l :
  rngl_has_1 T = true →
  ∀ a b, (a + a * b = a * (1 + b))%L.
Proof.
intros Hon *.
rewrite rngl_mul_add_distr_l.
now rewrite (rngl_mul_1_r Hon).
Qed.

Theorem rngl_add_mul_r_diag_r :
  rngl_has_1 T = true →
  ∀ a b, (a + b * a = (1 + b) * a)%L.
Proof.
intros Hon *.
rewrite rngl_mul_add_distr_r.
now rewrite (rngl_mul_1_l Hon).
Qed.

Theorem rngl_add_mul_l_diag_l :
  rngl_has_1 T = true →
  ∀ a b, (a * b + a = a * (b + 1))%L.
Proof.
intros Hon *.
rewrite rngl_mul_add_distr_l.
now rewrite (rngl_mul_1_r Hon).
Qed.

Theorem rngl_sub_mul_r_diag_l :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a b, (a - a * b = a * (1 - b))%L.
Proof.
intros Hon Hop *.
rewrite (rngl_mul_sub_distr_l Hop).
now rewrite (rngl_mul_1_r Hon).
Qed.

Theorem rngl_sub_mul_l_diag_l :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a b : T, (a * b - a)%L = (a * (b - 1))%L.
Proof.
intros Hon Hop *.
rewrite (rngl_mul_sub_distr_l Hop).
now rewrite (rngl_mul_1_r Hon).
Qed.

Theorem rngl_div_mul_mul_div :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ a b c, (a / b * c = a * c / b)%L.
Proof.
intros Hic Hiv *.
progress unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_mul_swap Hic).
Qed.

Theorem rngl_div_0_l :
  rngl_has_opp_or_subt T = true →
  rngl_has_inv_and_1_or_quot T = true →
  ∀ a, a ≠ 0%L → (0 / a)%L = 0%L.
Proof.
intros Hos Hiv * Haz.
remember (0 / a)%L as x eqn:Hx.
replace 0%L with (0 * a)%L in Hx. 2: {
  now apply rngl_mul_0_l.
}
subst x.
apply (rngl_mul_div Hiv _ _ Haz).
Qed.

Theorem rngl_div_div_mul_mul :
  rngl_has_1 T = true →
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ a b c d,
  b ≠ 0%L
  → d ≠ 0%L
  → (a / b = c / d)%L ↔ (a * d = b * c)%L.
Proof.
intros Hon Hic Hiv * Hbz Hdz.
split. {
  intros Habcd.
  apply (f_equal (λ x, rngl_mul x b)) in Habcd.
  rewrite rngl_div_mul in Habcd; [ | easy | easy | easy ].
  apply (f_equal (λ x, rngl_mul x d)) in Habcd.
  rewrite (rngl_mul_comm Hic _ b) in Habcd.
  rewrite <- rngl_mul_assoc in Habcd.
  now rewrite rngl_div_mul in Habcd.
} {
  intros Habcd.
  apply (f_equal (λ x, rngl_div x d)) in Habcd.
  specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
  rewrite rngl_mul_div in Habcd; [ | easy | easy ].
  apply (f_equal (λ x, rngl_div x b)) in Habcd.
  rewrite rngl_div_div_swap in Habcd; [ | easy | easy ].
  rewrite rngl_mul_comm in Habcd; [ | easy ].
  rewrite rngl_mul_div in Habcd; [ easy | easy | easy ].
}
Qed.

Theorem rngl_eq_mul_0_l :
  rngl_has_opp_or_subt T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b, (a * b = 0)%L → b ≠ 0%L → a = 0%L.
Proof.
intros Hos Hii * Hab Hbz.
specialize rngl_opt_integral as rngl_integral.
destruct rngl_is_integral_domain. {
  now apply rngl_integral in Hab; destruct Hab.
}
cbn in Hii; clear rngl_integral.
remember (rngl_has_inv T) as iv eqn:Hiv; symmetry in Hiv.
destruct iv. {
  assert (Hon : rngl_has_1 T = true). {
    apply rngl_has_inv_and_1_or_quot_iff in Hii.
    destruct Hii as [Hii| Hii]; [ easy | ].
    apply rngl_has_quot_has_no_inv in Hii.
    congruence.
  }
  apply (f_equal (λ x, (x * b⁻¹)%L)) in Hab.
  rewrite <- rngl_mul_assoc in Hab.
  rewrite rngl_mul_inv_diag_r in Hab; [ | easy | easy | easy ].
  rewrite (rngl_mul_1_r Hon) in Hab; rewrite Hab.
  apply (rngl_mul_0_l Hos).
}
remember (rngl_has_quot T) as qu eqn:Hqu; symmetry in Hqu.
destruct qu. {
  specialize (rngl_mul_div Hii a b Hbz) as H1.
  rewrite Hab in H1.
  now rewrite rngl_div_0_l in H1.
}
apply rngl_has_inv_and_1_or_quot_iff in Hii.
rewrite Hiv, Hqu in Hii.
now destruct Hii.
Qed.

Theorem rngl_eq_mul_0_r :
  rngl_has_opp_or_subt T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b, (a * b = 0)%L → a ≠ 0%L → b = 0%L.
Proof.
intros Hos Hii * Hab Haz.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic. {
  rewrite (rngl_mul_comm Hic) in Hab.
  now apply (rngl_eq_mul_0_l Hos Hii) in Hab.
}
specialize rngl_opt_integral as rngl_integral.
destruct rngl_is_integral_domain. {
  now apply rngl_integral in Hab; destruct Hab.
}
cbn in Hii; clear rngl_integral.
remember (rngl_has_inv T) as iv eqn:Hiv; symmetry in Hiv.
destruct iv. {
  assert (Hon : rngl_has_1 T = true). {
    apply rngl_has_inv_and_1_or_quot_iff in Hii.
    destruct Hii as [Hii| Hii]; [ easy | ].
    apply rngl_has_quot_has_no_inv in Hii.
    congruence.
  }
  apply (f_equal (rngl_mul a⁻¹%L)) in Hab.
  rewrite rngl_mul_assoc, (rngl_mul_0_r Hos) in Hab.
  rewrite (rngl_mul_inv_diag_l Hon Hiv) in Hab; [ | easy ].
  now rewrite rngl_mul_1_l in Hab.
}
remember (rngl_has_quot T) as qu eqn:Hqu; symmetry in Hqu.
destruct qu. {
  specialize rngl_opt_mul_quot_r as rngl_mul_quot_r.
  rewrite Hqu, Hic in rngl_mul_quot_r; cbn in rngl_mul_quot_r.
  specialize (rngl_mul_quot_r b a Haz) as H1.
  rewrite Hab in H1.
  now rewrite (rngl_div_0_l Hos Hii) in H1.
}
apply rngl_has_inv_and_1_or_quot_iff in Hii.
rewrite Hiv, Hqu in Hii.
now destruct Hii.
Qed.

Theorem rngl_integral :
  rngl_has_opp_or_subt T = true →
  (rngl_is_integral_domain T ||
   rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
  ∀ a b, (a * b = 0)%L → a = 0%L ∨ b = 0%L.
Proof.
intros Hmo Hdo * Hab.
specialize rngl_opt_integral as rngl_integral.
destruct rngl_is_integral_domain; [ now apply rngl_integral | cbn in Hdo ].
remember (rngl_has_inv T) as iv eqn:Hiv; symmetry in Hiv.
destruct iv. {
  assert (Hon : rngl_has_1 T = true). {
    remember (rngl_has_inv_and_1_or_quot T) as iq eqn:Hiq.
    symmetry in Hiq.
    destruct iq; [ cbn in Hdo | easy ].
    apply rngl_has_inv_and_1_or_quot_iff in Hiq.
    destruct Hiq as [| Hiq]; [ easy | ].
    apply rngl_has_quot_has_no_inv in Hiq.
    congruence.
  }
  remember (rngl_has_eq_dec T) as de eqn:Hde; symmetry in Hde.
  destruct de; [ | now destruct rngl_has_inv_and_1_or_quot ].
  cbn; clear rngl_integral.
  assert (H : (a⁻¹ * a * b = a⁻¹ * 0)%L). {
    now rewrite <- rngl_mul_assoc, Hab.
  }
  remember (rngl_eqb a 0%L) as az eqn:Haz; symmetry in Haz.
  destruct az; [ now left; apply (rngl_eqb_eq Hde) | ].
  apply (rngl_eqb_neq Hde) in Haz; right.
  rewrite rngl_mul_inv_diag_l in H; [ | easy | easy | easy ].
  rewrite (rngl_mul_1_l Hon) in H; rewrite H.
  apply (rngl_mul_0_r Hmo).
} {
  apply andb_prop in Hdo.
  destruct Hdo as (Hdi, Hde).
  specialize rngl_mul_div as H1.
  rewrite Hdi in H1.
  specialize (H1 eq_refl).
  remember (rngl_eqb b 0%L) as bz eqn:Hbz; symmetry in Hbz.
  destruct bz; [ now right; apply (rngl_eqb_eq Hde) | left ].
  apply (rngl_eqb_neq Hde) in Hbz.
  specialize (H1 a b Hbz) as H4.
  rewrite Hab in H4.
  rewrite <- H4.
  now apply rngl_div_0_l.
}
Qed.

Theorem rngl_mul_cancel_r :
  rngl_has_inv_and_1_or_quot T = true →
  ∀ a b c, c ≠ 0%L
  → (a * c = b * c)%L
  → a = b.
Proof.
intros Hii * Hcz Hab.
assert (H : (a * c / c = b * c / c)%L) by now rewrite Hab.
rewrite rngl_mul_div in H; [ | easy | easy ].
rewrite rngl_mul_div in H; [ | easy | easy ].
easy.
Qed.

Theorem rngl_mul_opp_l :
  rngl_has_opp T = true →
  ∀ a b, (- a * b = - (a * b))%L.
Proof.
intros Hro *.
specialize (rngl_mul_add_distr_r (- a)%L a b) as H.
rewrite rngl_add_opp_diag_l in H; [ | easy ].
rewrite rngl_mul_0_l in H. 2: {
  now apply rngl_has_opp_or_subt_iff; left.
}
symmetry in H.
now apply rngl_add_move_0_r in H.
Qed.

Theorem rngl_mul_sub_distr_r :
  rngl_has_opp T = true →
  ∀ a b c, ((a - b) * c = a * c - b * c)%L.
Proof.
intros Hop *.
unfold rngl_sub; rewrite Hop.
rewrite rngl_mul_add_distr_r.
now rewrite rngl_mul_opp_l.
Qed.

Theorem rngl_sub_mul_l_diag_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a b : T, (a * b - b)%L = ((a - 1) * b)%L.
Proof.
intros Hon Hop *.
rewrite (rngl_mul_sub_distr_r Hop).
now rewrite (rngl_mul_1_l Hon).
Qed.

Theorem rngl_sub_mul_r_diag_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a b, (a - b * a = (1 - b) * a)%L.
Proof.
intros Hon Hop *.
rewrite (rngl_mul_sub_distr_r Hop).
now rewrite (rngl_mul_1_l Hon).
Qed.

Theorem rngl_div_add_distr_r:
  rngl_has_inv T = true →
  ∀ a b c, ((a + b) / c)%L = (a / c + b / c)%L.
Proof.
intros Hiv *.
progress unfold rngl_div.
rewrite Hiv.
apply rngl_mul_add_distr_r.
Qed.

Theorem rngl_div_sub_distr_r:
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ a b c, ((a - b) / c)%L = (a / c - b / c)%L.
Proof.
intros Hop Hiv *.
progress unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_sub_distr_r Hop).
Qed.

Theorem rngl_mul_0_sub_1_comm :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a, ((0 - 1) * a = a * (0 - 1))%L.
Proof.
intros Hon Hop *.
rewrite (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_sub_distr_r Hop).
rewrite rngl_mul_0_l; [ | now apply rngl_has_opp_or_subt_iff; left ].
rewrite rngl_mul_0_r; [ | now apply rngl_has_opp_or_subt_iff; left ].
now rewrite rngl_mul_1_l, rngl_mul_1_r.
Qed.

Theorem rngl_inv_1 :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 1 →
  (1⁻¹ = 1)%L.
Proof.
intros Hon Hiv H10.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_div_diag Hon) as H.
unfold rngl_div in H.
rewrite Hiv in H.
transitivity (1 * 1⁻¹)%L. {
  symmetry.
  apply (rngl_mul_1_l Hon).
}
apply H; [ easy | ].
now apply rngl_1_neq_0_iff.
Qed.

Theorem rngl_div_1_l :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ a, (1 / a = a⁻¹)%L.
Proof.
intros Hon Hiv *.
unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_1_l Hon).
Qed.

Theorem rngl_div_1_r :
  rngl_has_1 T = true →
  rngl_has_inv_or_quot T = true →
  rngl_characteristic T ≠ 1 →
  ∀ a, (a / 1 = a)%L.
Proof.
intros Hon Hiq H10 *.
assert (Hi1 : rngl_has_inv_and_1_or_quot T = true). {
  apply rngl_has_inv_or_quot_iff in Hiq.
  apply rngl_has_inv_and_1_or_quot_iff.
  now destruct Hiq; [ left | right ].
}
specialize (rngl_mul_div Hi1 a 1%L) as H1.
rewrite (rngl_mul_1_r Hon) in H1.
now apply H1, rngl_1_neq_0_iff.
Qed.

Theorem rngl_mul_div_assoc :
  rngl_has_inv T = true →
  ∀ a b c, (a * (b / c) = a * b / c)%L.
Proof.
intros Hiv *.
progress unfold rngl_div.
rewrite Hiv.
apply rngl_mul_assoc.
Qed.

Theorem rngl_div_compat_l :
  rngl_has_inv T = true →
  ∀ a b c, c ≠ 0%L → (a = b)%L → (a / c = b / c)%L.
Proof.
intros Hin a b c Hcz Hab.
now rewrite Hab.
Qed.

Theorem rngl_inv_if_then_else_distr : ∀ (c : bool) a b,
  ((if c then a else b)⁻¹ = if c then a⁻¹ else b⁻¹)%L.
Proof. now destruct c. Qed.

Theorem rngl_mul_if_then_else_distr : ∀ (x : bool) a b c d,
  ((if x then a else b) * (if x then c else d) = if x then a * c else b * d)%L.
Proof. now destruct x. Qed.

Theorem rngl_mul_move_1_r :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ a b : T, b ≠ 0%L → (a * b)%L = 1%L ↔ a = (b⁻¹)%L.
Proof.
intros Hon Hiv * Hbz.
split; intros H. {
  apply rngl_div_compat_l with (c := b) in H; [ | easy | easy ].
  unfold rngl_div in H.
  rewrite Hiv in H.
  rewrite <- rngl_mul_assoc in H.
  rewrite (rngl_mul_inv_r Hiv) in H.
  rewrite (rngl_div_diag Hon) in H; [ | | easy ]. 2: {
    now apply rngl_has_inv_or_quot_iff; left.
  }
  now rewrite rngl_mul_1_r, rngl_mul_1_l in H.
} {
  rewrite H.
  specialize (rngl_mul_inv_diag_l Hon Hiv) as H1.
  now apply H1.
}
Qed.

Theorem rngl_mul_move_l :
  rngl_mul_is_comm T = true →
  rngl_has_inv_and_1_or_quot T = true →
  ∀ a b c, a ≠ 0%L → (a * b)%L = c → b = (c / a)%L.
Proof.
intros Hic Hi1 * Haz Hab.
subst c; symmetry.
rewrite (rngl_mul_comm Hic).
now apply (rngl_mul_div Hi1).
Qed.

Theorem rngl_mul_move_r :
  rngl_has_inv_and_1_or_quot T = true →
  ∀ a b c, b ≠ 0%L → (a * b)%L = c → a = (c / b)%L.
Proof.
intros Hi1 * Hcz Ha.
subst c; symmetry.
now apply (rngl_mul_div Hi1).
Qed.

Theorem rngl_characteristic_1 :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_characteristic T = 1 →
  ∀ x, x = 0%L.
Proof.
intros Hon Hos Hch *.
specialize (rngl_opt_characteristic_prop) as H1.
rewrite Hon, Hch in H1; cbn in H1.
destruct H1 as (_, H1).
rewrite rngl_add_0_r in H1.
assert (H : (x * 0)%L = x). {
  rewrite <- H1.
  apply (rngl_mul_1_r Hon).
}
rewrite <- H.
apply (rngl_mul_0_r Hos).
Qed.

Theorem rngl_1_eq_0_iff :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_characteristic T = 1 ↔ (1 = 0)%L.
Proof.
intros Hon Hos.
split. {
  intros Hc.
  specialize (rngl_characteristic_1 Hon Hos Hc) as H1.
  apply H1.
} {
  intros H10.
  destruct (Nat.eq_dec (rngl_characteristic T) 1) as [H1| H1]; [ easy | ].
  now apply (rngl_1_neq_0_iff Hon) in H1.
}
Qed.

Theorem rngl_inv_neq_0 :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  ∀ a, a ≠ 0%L → (a⁻¹ ≠ 0)%L.
Proof.
intros Hon Hom Hiv * Haz H1.
remember (Nat.eqb (rngl_characteristic T) 1) as ch eqn:Hch; symmetry in Hch.
destruct ch. {
  apply Nat.eqb_eq in Hch.
  now specialize (rngl_characteristic_1 Hon Hom Hch a).
}
apply Nat.eqb_neq in Hch.
symmetry in H1.
apply (rngl_mul_move_1_r Hon Hiv _ _ Haz) in H1.
rewrite (rngl_mul_0_l Hom) in H1.
symmetry in H1.
now apply rngl_1_neq_0_iff in H1.
Qed.

Theorem rngl_inv_involutive :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  ∀ x, x ≠ 0%L → (x⁻¹⁻¹)%L = x.
Proof.
intros Hon Hos Hiv * Hxz.
remember (Nat.eqb (rngl_characteristic T) 1) as ch eqn:Hch; symmetry in Hch.
destruct ch. {
  apply Nat.eqb_eq in Hch.
  exfalso; apply Hxz.
  apply (rngl_characteristic_1 Hon Hos Hch).
}
apply Nat.eqb_neq in Hch.
symmetry.
specialize (rngl_div_diag Hon) as div_diag.
unfold rngl_div in div_diag.
rewrite Hiv in div_diag.
specialize (rngl_mul_move_1_r Hon Hiv) as H1.
apply H1. 2: {
  rewrite rngl_mul_inv_r; [ | easy ].
  unfold rngl_div; rewrite Hiv.
  apply div_diag; [ | easy ].
  now apply rngl_has_inv_or_quot_iff; left.
}
now apply rngl_inv_neq_0.
Qed.

Theorem rngl_mul_opp_opp :
  rngl_has_opp T = true →
  ∀ a b, (- a * - b = a * b)%L.
Proof.
intros Hro *.
rewrite rngl_mul_opp_l; [ | easy ].
rewrite rngl_mul_opp_r; [ | easy ].
now apply rngl_opp_involutive.
Qed.

Theorem rngl_squ_opp_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  (-1 * -1)%L = 1%L.
Proof.
intros Hon Hop.
rewrite (rngl_mul_opp_opp Hop).
apply (rngl_mul_1_l Hon).
Qed.

Theorem rngl_inv_inj :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  ∀ a b, a ≠ 0%L → b ≠ 0%L →(a⁻¹ = b⁻¹)%L → a = b.
Proof.
intros Hon Hom Hiv * Haz Hbz H.
rewrite <- (rngl_inv_involutive Hon Hom Hiv a); [ | easy ].
rewrite H.
now apply rngl_inv_involutive.
Qed.

Theorem rngl_inv_mul_distr :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  ∀ a b, a ≠ 0%L → b ≠ 0%L →((a * b)⁻¹ = b⁻¹ * a⁻¹)%L.
Proof.
intros Hon Hom Hiv * Haz Hbz.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_div_diag Hon Hiq) as div_diag.
specialize (rngl_eq_mul_0_l Hom) as integral.
assert
  (H :
    (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T)%bool = true). {
  now rewrite Hi1; destruct rngl_is_integral_domain.
}
specialize (integral H); clear H.
unfold rngl_div in div_diag.
rewrite Hiv in div_diag.
assert (Habz : (a * b)%L ≠ 0%L). {
  intros H.
  now specialize (integral a b H Hbz).
}
apply (rngl_mul_cancel_l Hi1 (a * b)%L _ _ Habz).
rewrite (div_diag _ Habz).
rewrite rngl_mul_assoc.
rewrite <- (rngl_mul_assoc a).
rewrite (div_diag _ Hbz).
rewrite (rngl_mul_1_r Hon).
now symmetry; apply div_diag.
Qed.

Theorem rngl_div_div :
  rngl_has_opp_or_subt T = true →
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ a b c, (b ≠ 0 → c ≠ 0 → a / b / c = a / (c * b))%L.
Proof.
intros Hos Hon Hiv * Hbz Hzc.
progress unfold rngl_div.
rewrite Hiv.
rewrite <- rngl_mul_assoc; f_equal; symmetry.
now apply (rngl_inv_mul_distr Hon Hos Hiv).
Qed.

Theorem rngl_mul_nat_mul_nat_1 :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ a n, rngl_mul_nat a n = (a * rngl_of_nat n)%L.
Proof.
intros Hon Hos *.
induction n; cbn. {
  symmetry; apply (rngl_mul_0_r Hos).
}
rewrite rngl_mul_add_distr_l, (rngl_mul_1_r Hon).
f_equal.
apply IHn.
Qed.

Theorem rngl_mul_nat_comm :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ n a, (rngl_of_nat n * a = a * rngl_of_nat n)%L.
Proof.
intros Hon Hos *.
induction n; cbn. {
  rewrite (rngl_mul_0_r Hos).
  apply (rngl_mul_0_l Hos).
}
rewrite rngl_mul_add_distr_l.
rewrite rngl_mul_add_distr_r.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_1_r Hon).
f_equal.
apply IHn.
Qed.

Theorem fold_rngl_of_nat :
  ∀ n, List.fold_right rngl_add 0%L (List.repeat 1 n)%L = rngl_of_nat n.
Proof. easy. Qed.

Theorem rngl_of_nat_mul :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ m n : nat, rngl_of_nat (m * n) = (rngl_of_nat m * rngl_of_nat n)%L.
Proof.
intros Hon Hos *.
induction m; cbn; [ symmetry; apply (rngl_mul_0_l Hos) | ].
do 2 rewrite fold_rngl_of_nat.
rewrite rngl_of_nat_add, rngl_mul_add_distr_r.
now rewrite (rngl_mul_1_l Hon); f_equal.
Qed.

Theorem rngl_of_nat_pow :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ a n, rngl_of_nat (a ^ n) = (rngl_of_nat a ^ n)%L.
Proof.
intros Hon Hos *.
induction n; cbn; [ apply rngl_add_0_r | ].
rewrite fold_rngl_of_nat.
rewrite (rngl_of_nat_mul Hon Hos).
now f_equal.
Qed.

Theorem rngl_mul_nat_pow_comm :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  ∀ a b n, (rngl_of_nat a ^ n * b = b * rngl_of_nat a ^ n)%L.
Proof.
intros Hon Hos *.
rewrite <- (rngl_of_nat_pow Hon Hos).
apply (rngl_mul_nat_comm Hon Hos).
Qed.

Theorem rngl_opp_inv :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ a, a ≠ 0%L → (- a⁻¹ = (- a)⁻¹)%L.
Proof.
intros Hon Hop Hiv * Haz.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
remember (Nat.eqb (rngl_characteristic T) 1) as ch eqn:Hch; symmetry in Hch.
destruct ch. {
  apply Nat.eqb_eq in Hch.
  exfalso; apply Haz.
  apply (rngl_characteristic_1 Hon Hos Hch).
}
apply Nat.eqb_neq in Hch.
assert (Hoaz : (- a)%L ≠ 0%L). {
  intros H.
  apply (f_equal rngl_opp) in H.
  rewrite rngl_opp_involutive in H; [ | easy ].
  now rewrite rngl_opp_0 in H.
}
apply (rngl_mul_cancel_l Hi1 (- a)%L); [ easy | ].
specialize (rngl_opt_mul_inv_diag_r) as H2.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
rewrite Hon, Hiv in H2; cbn in H2.
rewrite rngl_mul_opp_opp; [ | easy ].
destruct ic. {
  symmetry.
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_inv_diag_l; [ | easy | easy | easy ].
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_inv_diag_l; [ | easy | easy | easy ].
  easy.
} {
  cbn in H2.
  rewrite rngl_mul_inv_r; [ | easy ].
  rewrite rngl_mul_inv_r; [ | easy ].
  rewrite H2; [ | easy ].
  now rewrite H2.
}
Qed.

Theorem rngl_div_mul_div :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ x y z, y ≠ 0%L → ((x / y) * (y / z))%L = (x / z)%L.
Proof.
intros Hon Hiv * Hs.
unfold rngl_div; rewrite Hiv.
rewrite rngl_mul_assoc; f_equal.
rewrite <- rngl_mul_assoc.
rewrite rngl_mul_inv_diag_l; [ | easy| easy | easy ].
apply (rngl_mul_1_r Hon).
Qed.

Theorem eq_rngl_div_1 :
  rngl_has_1 T = true →
  rngl_has_inv_or_quot T = true →
   ∀ a b, b ≠ 0%L → a = b → (a / b = 1)%L.
Proof.
intros Hon Hiv * Hbz Hab.
subst a.
apply (rngl_div_diag Hon Hiv _ Hbz).
Qed.

Theorem eq_rngl_add_same_0 :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  (rngl_is_integral_domain T || rngl_has_inv_or_quot T)%bool = true →
  rngl_characteristic T = 0 →
  ∀ a,
  (a + a = 0)%L
  → a = 0%L.
Proof.
intros Hon Hos Hii Hch * Haa.
rewrite (rngl_add_diag Hon) in Haa.
specialize (rngl_characteristic_0 Hon Hch 1) as H1.
cbn in H1.
rewrite rngl_add_0_r in H1.
apply (rngl_eq_mul_0_r Hos) in Haa; [ easy | | easy ].
destruct rngl_is_integral_domain; [ easy | ].
cbn in Hii |-*.
apply rngl_has_inv_or_quot_iff in Hii.
apply rngl_has_inv_and_1_or_quot_iff.
now destruct Hii; [ left | right ].
Qed.

Theorem rngl_pow_0_l :
  rngl_has_opp_or_subt T = true →
  ∀ n, (0 ^ n)%L = match n with 0 => 1%L | _ => 0%L end.
Proof.
intros Hos *.
destruct n; [ easy | ].
apply (rngl_mul_0_l Hos).
Qed.

Theorem rngl_pow_0_r : ∀ a, (a ^ 0 = 1)%L.
Proof. easy. Qed.

Theorem rngl_pow_add_r :
  rngl_has_1 T = true →
  ∀ a i j, (a ^ (i + j) = a ^ i * a ^ j)%L.
Proof.
intros Hon *.
induction i; [ symmetry; apply (rngl_mul_1_l Hon) | ].
destruct i. {
  cbn in IHi |-*.
  rewrite IHi.
  now rewrite (rngl_mul_1_r Hon).
}
cbn in IHi |-*.
rewrite IHi.
now do 3 rewrite <- rngl_mul_assoc.
Qed.

Theorem rngl_pow_nonzero :
  rngl_has_1 T = true →
  rngl_characteristic T ≠ 1 →
  rngl_has_opp_or_subt T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a n, (a ≠ 0 → a ^ n ≠ 0)%L.
Proof.
intros Hon Hc1 Hos Hii * Haz.
induction n; [ now apply (rngl_1_neq_0_iff Hon) | cbn ].
intros H1; apply IHn.
now apply (rngl_eq_mul_0_l Hos Hii) in H1.
Qed.

Theorem rngl_squ_opp :
  rngl_has_opp T = true →
  ∀ a, rngl_squ (- a)%L = rngl_squ a.
Proof.
intros Hop *.
progress unfold rngl_squ.
apply (rngl_mul_opp_opp Hop).
Qed.

Theorem rngl_squ_abs :
  rngl_has_opp T = true →
  ∀ a, rngl_squ (rngl_abs a) = rngl_squ a.
Proof.
intros Hop *.
progress unfold rngl_abs.
destruct (a ≤? 0)%L; [ | easy ].
apply (rngl_squ_opp Hop).
Qed.

Theorem rngl_squ_add :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  ∀ a b, (rngl_squ (a + b) = rngl_squ a + 2 * a * b + rngl_squ b)%L.
Proof.
intros Hic Hon *.
progress unfold rngl_squ.
rewrite rngl_mul_add_distr_l.
do 2 rewrite rngl_mul_add_distr_r.
rewrite rngl_add_assoc; f_equal.
rewrite <- rngl_add_assoc; f_equal.
rewrite <- rngl_mul_assoc.
rewrite <- (rngl_add_diag Hon); f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem rngl_squ_sub :
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  ∀ a b, (rngl_squ (a - b) = rngl_squ a - 2 * a * b + rngl_squ b)%L.
Proof.
intros Hop Hic Hon *.
progress unfold rngl_sub.
rewrite Hop.
rewrite (rngl_squ_add Hic Hon).
rewrite (rngl_squ_opp Hop).
f_equal; f_equal.
apply (rngl_mul_opp_r Hop).
Qed.

Theorem rngl_squ_sub_comm :
  rngl_has_opp T = true →
  ∀ a b, ((a - b)² = (b - a)²)%L.
Proof.
intros Hop.
intros.
rewrite <- (rngl_squ_opp Hop).
now rewrite (rngl_opp_sub_distr Hop).
Qed.

Theorem rngl_squ_mul :
  rngl_mul_is_comm T = true →
  ∀ a b, rngl_squ (a * b)%L = (rngl_squ a * rngl_squ b)%L.
Proof.
intros Hic *.
progress unfold rngl_squ.
do 2 rewrite rngl_mul_assoc.
f_equal.
apply (rngl_mul_mul_swap Hic).
Qed.

Theorem rngl_pow_succ_r :
  ∀ n a, (a ^ S n = a * a ^ n)%L.
Proof. easy. Qed.

Theorem rngl_squ_0 :
  rngl_has_opp_or_subt T = true →
  (0² = 0)%L.
Proof.
intros Hos.
apply (rngl_mul_0_l Hos).
Qed.

Theorem rngl_squ_1 :
  rngl_has_1 T = true →
  (1² = 1)%L.
Proof.
intros Hon.
apply (rngl_mul_1_l Hon).
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

Theorem rngl_pow_1_r :
  rngl_has_1 T = true →
  ∀ a, (a ^ 1)%L = a.
Proof.
intros Hon *; cbn.
apply (rngl_mul_1_r Hon).
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

(* with order *)

Theorem rngl_mul_le_compat_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L.
Proof.
intros Hop Hor *.
specialize rngl_opt_ord as rr.
rewrite Hor in rr.
move rr after rp.
specialize rngl_ord_mul_le_compat_nonneg as H.
rewrite Hop in H.
apply H.
Qed.

Theorem rngl_mul_le_compat_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L.
Proof.
intros Hop Hor *.
specialize rngl_opt_ord as rr.
rewrite Hor in rr.
move rr after rp.
specialize rngl_ord_mul_le_compat_nonpos as H.
rewrite Hop in H.
apply H.
Qed.

Theorem rngl_mul_le_compat_non_opp :
  rngl_has_opp T = false →
  rngl_is_ordered T = true →
  ∀ a b c d, (a ≤ c)%L → (b ≤ d)%L → (a * b ≤ c * d)%L.
Proof.
intros Hop Hor * Hac Hbd.
specialize rngl_opt_ord as rr.
rewrite Hor in rr.
move rr after rp.
specialize rngl_ord_mul_le_compat_non_opp as H.
rewrite Hop in H.
cbn in H.
now apply H.
Qed.

Theorem rngl_mul_le_compat_nonpos_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d,
  (0 ≤ c ≤ a)%L
  → (b ≤ d ≤ 0)%L
  → (a * b ≤ c * d)%L.
Proof.
intros Hop Hor * Had Hcd.
apply (rngl_opp_le_compat Hop Hor).
do 2 rewrite <- (rngl_mul_opp_r Hop).
apply (rngl_mul_le_compat_nonneg Hop Hor); [ easy | ].
split.
now apply (rngl_opp_nonneg_nonpos Hop Hor).
now apply -> (rngl_opp_le_compat Hop Hor).
Qed.

Theorem rngl_mul_nonneg_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → 0 ≤ b → 0 ≤ a * b)%L.
Proof.
intros * Hop Hor * Ha Hb.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_mul_le_compat_nonneg Hop Hor) as H1.
specialize (H1 0 0 a b)%L.
assert (H : (0 ≤ 0 ≤ a)%L) by now split; [ apply (rngl_le_refl Hor) | ].
specialize (H1 H); clear H.
assert (H : (0 ≤ 0 ≤ b)%L) by now split; [ apply (rngl_le_refl Hor) | ].
specialize (H1 H); clear H.
now rewrite (rngl_mul_0_l Hos) in H1.
Qed.

Theorem rngl_mul_nonpos_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ 0 → b ≤ 0 → 0 ≤ a * b)%L.
Proof.
intros * Hop Hor * Ha Hb.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_mul_le_compat_nonpos Hop Hor) as H1.
specialize (H1 0 0 a b)%L.
assert (H : (a ≤ 0 ≤ 0)%L) by now split; [ | apply (rngl_le_refl Hor) ].
specialize (H1 H); clear H.
assert (H : (b ≤ 0 ≤ 0)%L) by now split; [ | apply (rngl_le_refl Hor) ].
specialize (H1 H); clear H.
now rewrite (rngl_mul_0_l Hos) in H1.
Qed.

Theorem rngl_mul_nonneg_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → b ≤ 0 → a * b ≤ 0)%L.
Proof.
intros * Hop Hor * Ha Hb.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_mul_le_compat_nonneg Hop Hor) as H1.
specialize (H1 0 0 a (- b))%L.
assert (H : (0 ≤ 0 ≤ a)%L) by now split; [ apply (rngl_le_refl Hor) | ].
specialize (H1 H); clear H.
assert (H : (0 ≤ 0 ≤ - b)%L). {
  split; [ apply (rngl_le_refl Hor) | ].
  apply (rngl_opp_le_compat Hop Hor) in Hb.
  now rewrite (rngl_opp_0 Hop) in Hb.
}
specialize (H1 H); clear H.
rewrite (rngl_mul_0_l Hos) in H1.
rewrite (rngl_mul_opp_r Hop) in H1.
apply (rngl_opp_le_compat Hop Hor) in H1.
rewrite (rngl_opp_involutive Hop) in H1.
now rewrite (rngl_opp_0 Hop) in H1.
Qed.

Theorem rngl_mul_nonpos_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ 0 → 0 ≤ b → a * b ≤ 0)%L.
Proof.
intros * Hop Hor * Ha Hb.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_mul_le_compat_nonneg Hop Hor) as H1.
specialize (H1 0 0 (- a) b)%L.
assert (H : (0 ≤ 0 ≤ - a)%L). {
  split; [ apply (rngl_le_refl Hor) | ].
  apply (rngl_opp_le_compat Hop Hor) in Ha.
  now rewrite (rngl_opp_0 Hop) in Ha.
}
specialize (H1 H); clear H.
assert (H : (0 ≤ 0 ≤ b)%L) by now split; [ apply (rngl_le_refl Hor) | ].
specialize (H1 H); clear H.
rewrite (rngl_mul_0_l Hos) in H1.
rewrite (rngl_mul_opp_l Hop) in H1.
apply (rngl_opp_le_compat Hop Hor) in H1.
rewrite (rngl_opp_involutive Hop) in H1.
now rewrite (rngl_opp_0 Hop) in H1.
Qed.

Theorem rngl_0_le_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (0 ≤ 1)%L.
Proof.
intros Hon Hop Hor.
destruct (rngl_le_dec Hor 0%L 1%L) as [| H1]; [ easy | ].
apply (rngl_not_le Hor) in H1.
destruct H1 as (H1, H2).
specialize (rngl_mul_nonpos_nonpos Hop Hor) as H3.
specialize (H3 1 1 H2 H2)%L.
now rewrite (rngl_mul_1_l Hon) in H3.
Qed.

Theorem rngl_0_leb_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (0 ≤? 1)%L = true.
Proof.
intros * Hon Hop Hor.
apply rngl_leb_le.
apply (rngl_0_le_1 Hon Hop Hor).
Qed.

Theorem rngl_0_lt_inv_compat :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 < a → 0 < a⁻¹)%L.
Proof.
intros * Hon Hop Hiv Hor.
intros * Hza.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
assert (Haz : a ≠ 0%L). {
  intros H; subst a.
  now apply (rngl_lt_irrefl Hor) in Hza.
}
specialize (rngl_inv_neq_0 Hon Hos Hiv) as H1.
destruct (rngl_le_dec Hor 0 a⁻¹)%L as [H2| H2]. {
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  intros H; symmetry in H; revert H.
  now apply H1.
}
apply (rngl_not_le Hor) in H2.
destruct H2 as (H2, H3).
specialize (rngl_mul_nonneg_nonpos Hop Hor) as H4.
assert (H : (0 ≤ a)%L) by now apply (rngl_lt_iff Hor) in Hza.
specialize (H4 _ _ H H3); clear H.
rewrite (rngl_mul_inv_diag_r Hon Hiv a Haz) in H4.
specialize (rngl_0_le_1 Hon Hop Hor) as H5.
specialize (rngl_le_antisymm Hor _ _ H4 H5) as H6.
clear H4 H5.
apply (rngl_1_eq_0_iff Hon Hos) in H6.
specialize (rngl_characteristic_1 Hon Hos H6) as H4.
exfalso; apply Haz, H4.
Qed.

Theorem rngl_inv_lt_0_compat :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a, (a < 0 → a⁻¹ < 0)%L.
Proof.
intros * Hon Hop Hiv Hor.
intros * Hza.
specialize (rngl_0_lt_inv_compat Hon Hop Hiv Hor) as H2.
specialize (H2 (- a))%L.
apply (rngl_opp_lt_compat Hop Hor).
rewrite (rngl_opp_0 Hop).
rewrite (rngl_opp_inv Hon Hop Hiv); [ | now apply rngl_lt_iff ].
apply H2.
apply (rngl_opp_lt_compat Hop Hor) in Hza.
now rewrite (rngl_opp_0 Hop) in Hza.
Qed.

Theorem rngl_mul_pos_neg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true →
  ∀ a b, (0 < a → b < 0 → a * b < 0)%L.
Proof.
intros Hop Hor Hid * Hza Hbz.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_mul_nonneg_nonpos Hop Hor). {
    now apply (rngl_lt_le_incl Hor).
  } {
    now apply (rngl_lt_le_incl Hor).
  }
}
intros H.
apply (rngl_integral Hos Hid) in H.
destruct H as [H| H]. {
  subst a.
  now apply (rngl_lt_irrefl Hor) in Hza.
} {
  subst b.
  now apply (rngl_lt_irrefl Hor) in Hbz.
}
Qed.

Theorem rngl_div_le_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (b ≠ 0 → 0 ≤ a ≤ b → a / b ≤ 1)%L.
Proof.
intros * Hon Hop Hiv Hor * Hbz (Hza, Hab).
unfold rngl_div.
rewrite Hiv.
specialize (rngl_mul_le_compat_nonneg Hop Hor) as H1.
specialize (H1 a b⁻¹ b b⁻¹)%L.
assert (H : (0 ≤ a ≤ b)%L) by easy.
specialize (H1 H); clear H.
assert (H : (0 ≤ b⁻¹ ≤ b⁻¹)%L). {
  split; [ | apply (rngl_le_refl Hor) ].
  apply (rngl_lt_le_incl Hor).
  apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
  apply (rngl_lt_iff Hor).
  split; [ | congruence ].
  now apply (rngl_le_trans Hor _ a).
}
specialize (H1 H); clear H.
now rewrite (rngl_mul_inv_diag_r Hon Hiv) in H1.
Qed.

Theorem rngl_mul_diag_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ a * a)%L.
Proof.
intros Hop Hor *.
destruct (rngl_le_dec Hor 0%L a) as [Hap| Han]. {
  now apply (rngl_mul_nonneg_nonneg Hop Hor).
} {
  apply (rngl_not_le Hor) in Han.
  now apply (rngl_mul_nonpos_nonpos Hop Hor).
}
Qed.

Theorem rngl_squ_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ a²)%L.
Proof.
intros Hop Hor *.
now apply rngl_mul_diag_nonneg.
Qed.

Theorem eq_rngl_add_square_0 :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool =
    true →
  ∀ a b : T, (a * a + b * b = 0)%L → a = 0%L ∧ b = 0%L.
Proof.
intros * Hop Hor Hii * Hab.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_eq_add_0 Hor) in Hab; cycle 1. {
  apply (rngl_mul_diag_nonneg Hop Hor).
} {
  apply (rngl_mul_diag_nonneg Hop Hor).
}
destruct Hab as (Ha, Hb).
split. {
  now apply (rngl_integral Hos Hii) in Ha; destruct Ha.
} {
  now apply (rngl_integral Hos Hii) in Hb; destruct Hb.
}
Qed.

Theorem rngl_0_lt_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  (0 < 1)%L.
Proof.
intros Hon Hop Hc1 Hor.
apply (rngl_lt_iff Hor).
split. 2: {
  apply not_eq_sym.
  now apply (rngl_1_neq_0_iff Hon).
}
apply (rngl_0_le_1 Hon Hop Hor).
Qed.

Theorem rngl_0_lt_2 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  (0 < 2)%L.
Proof.
intros Hon Hop Hc1 Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_le_lt_trans Hor _ 1)%L. {
  apply (rngl_0_le_1 Hon Hop Hor).
}
apply (rngl_lt_add_r Hos Hor).
apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_0_le_2 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (0 ≤ 2)%L.
Proof.
intros Hon Hop Hor.
apply (rngl_le_trans Hor _ 1)%L. {
  apply (rngl_0_le_1 Hon Hop Hor).
}
apply (rngl_le_add_r Hor).
apply (rngl_0_le_1 Hon Hop Hor).
Qed.

Theorem rngl_2_neq_0 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  (2 ≠ 0)%L.
Proof.
intros Hon Hop Hc1 Hor.
specialize (rngl_0_lt_2 Hon Hop Hc1 Hor) as H5.
intros H; rewrite H in H5.
now apply (rngl_lt_irrefl Hor) in H5.
Qed.

Theorem rngl_opp_1_le_0 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (-1 ≤ 0)%L.
Proof.
intros Hon Hop Hor.
apply (rngl_opp_nonpos_nonneg Hop Hor).
apply (rngl_0_le_1 Hon Hop Hor).
Qed.

Theorem rngl_opp_1_lt_0 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  rngl_characteristic T ≠ 1 →
  (-1 < 0)%L.
Proof.
intros Hon Hop Hor Hc1.
apply (rngl_opp_neg_pos Hop Hor).
apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_opp_1_lt_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  rngl_characteristic T ≠ 1 →
  (-1 < 1)%L.
Proof.
intros Hon Hop Hor Hc1.
apply (rngl_lt_le_trans Hor _ 0)%L.
apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
apply (rngl_0_le_1 Hon Hop Hor).
Qed.

Theorem rngl_opp_1_le_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  rngl_characteristic T ≠ 1 →
  (-1 ≤ 1)%L.
Proof.
intros Hon Hop Hor Hc1.
apply (rngl_lt_le_incl Hor).
apply (rngl_opp_1_lt_1 Hon Hop Hor Hc1).
Qed.

Theorem rngl_of_nat_nonneg :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ n, (0 ≤ rngl_of_nat n)%L.
Proof.
intros Hon Hop Hor *.
induction n; [ apply (rngl_le_refl Hor) | ].
rewrite rngl_of_nat_succ.
eapply (rngl_le_trans Hor); [ apply IHn | ].
apply (rngl_le_add_l Hor).
apply (rngl_0_le_1 Hon Hop Hor).
Qed.

Theorem rngl_of_nat_inj_le :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  ∀ i j, i ≤ j ↔ (rngl_of_nat i ≤ rngl_of_nat j)%L.
Proof.
intros Hon Hop Hc1 Hor *.
apply (rngl_mul_nat_inj_le Hop Hor).
apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_of_nat_inj_lt :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  ∀ i j, i < j ↔ (rngl_of_nat i < rngl_of_nat j)%L.
Proof.
intros Hon Hop Hc1 Hor *.
apply (rngl_mul_nat_inj_lt Hop Hor).
apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_one_sub_half :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  (1 - 2⁻¹ = 2⁻¹)%L.
Proof.
intros Hon Hop Hiv Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  now rewrite (H1 (_ - _))%L, H1.
}
assert (Hc2 : (2 ≠ 0)%L). {
  specialize (rngl_0_lt_2 Hon Hop Hc1 Hor) as H2.
  intros H; rewrite H in H2.
  now apply (rngl_lt_irrefl Hor) in H2.
}
apply (rngl_mul_cancel_r Hi1) with (c := 2%L); [ easy | ].
rewrite (rngl_mul_sub_distr_r Hop).
rewrite (rngl_mul_inv_diag_l Hon Hiv); [ | easy ].
rewrite (rngl_mul_1_l Hon).
apply (rngl_add_sub Hos).
Qed.

Theorem rngl_abs_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_abs 1 = 1)%L.
Proof.
intros Hon Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  now rewrite (H1 (rngl_abs 1)%L), (H1 1%L).
}
progress unfold rngl_abs.
remember (1 ≤? 0)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ | easy ].
apply rngl_leb_le in Hc.
apply (rngl_nlt_ge Hor) in Hc.
exfalso; apply Hc.
apply (rngl_0_lt_1 Hon Hop Hc1 Hor).
Qed.

Theorem rngl_abs_2 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_abs 2 = 2)%L.
Proof.
intros Hon Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1; apply H1.
}
progress unfold rngl_abs.
remember (2 ≤? 0)%L as tz eqn:Htz.
symmetry in Htz.
destruct tz; [ | easy ].
apply rngl_leb_le in Htz.
apply (rngl_nlt_ge Hor) in Htz.
exfalso; apply Htz.
apply (rngl_0_lt_2 Hon Hop Hc1 Hor).
Qed.

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

Theorem rngl_add_squ_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a² + b²)%L.
Proof.
intros Hop Hor *.
apply (rngl_add_nonneg_nonneg Hor);
apply (rngl_squ_nonneg Hop Hor).
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
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c, (0 ≤ a)%L → rngl_min (a * b)%L (a * c)%L = (a * rngl_min b c)%L.
Proof.
intros Hop Hor Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Hza.
destruct (rngl_eq_dec Heo a 0%L) as [Haz| Haz]. {
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
     Ropp_def := rngl_add_opp_diag_r Hop |}.

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

Record charac_0_field :=
  { cf_has_1 : rngl_has_1 T = true;
    cf_mul_is_comm : rngl_mul_is_comm T = true;
    cf_has_opp : rngl_has_opp T = true;
    cf_has_inv : rngl_has_inv T = true;
    cf_has_eq_dec : rngl_has_eq_dec T = true;
    cf_characteristic : rngl_characteristic T = 0 }.

End a.

Arguments rngl_characteristic_1 {T ro rp} Hon Hos Hch x%_L.
Arguments rngl_div_add_distr_r {T ro rp} Hiv (a b c)%_L.
Arguments rngl_div_le_mono_pos_r {T ro rp} Hon Hop Hiv Hor Hii (a b c)%_L.
Arguments rngl_mul_comm {T ro rp} Hic (a b)%_L.
Arguments rngl_mul_le_mono_pos_l {T ro rp} Hop Hor Hii (a b c)%_L.
Arguments rngl_mul_le_mono_pos_r {T ro rp} Hop Hor Hii (a b c)%_L.
Arguments rngl_mul_0_r {T ro rp} Hom a%_L.
Arguments rngl_mul_1_r {T ro rp} Hon a%_L.
Arguments rngl_pow_squ {T ro rp} Hic Hon a%_L n%_nat.

Arguments charac_0_field T%_type {ro rp}.
