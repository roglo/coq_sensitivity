Require Import Utf8 Arith.
Require Import RingLike_structures.
Require Import RingLike_order.
Require Import RingLike_add.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

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

End a.
