Set Nested Proofs Allowed.

Require Import Utf8.
Require Import Main.RingLike.
Require Import Trigo.Angle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Definition rngl_tan θ := (rngl_sin θ / rngl_cos θ)%L.

Context {Hop : rngl_has_opp T = true}.
Context {Hor : rngl_is_ordered T = true}.

Theorem rngl_dist_mul_distr_r :
 (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c,
  (0 ≤ c)%L → (rngl_dist a b * c = rngl_dist (a * c) (b * c))%L.
Proof.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros Hii.
intros * Hzc.
progress unfold rngl_dist.
rewrite <- (rngl_mul_sub_distr_r Hop).
progress unfold rngl_abs.
rewrite (rngl_mul_sub_distr_r Hop).
do 2 rewrite (rngl_leb_sub_0 Hop Hor).
rewrite <- (rngl_mul_sub_distr_r Hop).
remember (a ≤? b)%L as ab eqn:Hab.
remember (a * c ≤? b * c)%L as acbc eqn:Hacbc.
symmetry in Hab, Hacbc.
destruct ab. {
  destruct acbc; [ apply (rngl_mul_opp_l Hop) | ].
  apply rngl_leb_le in Hab.
  apply (rngl_leb_gt Hor) in Hacbc.
  exfalso.
  apply rngl_nle_gt in Hacbc.
  apply Hacbc; clear Hacbc.
  now apply (rngl_mul_le_mono_nonneg_r Hop Hor).
}
apply (rngl_leb_gt Hor) in Hab.
destruct acbc; [ | easy ].
apply rngl_leb_le in Hacbc.
apply (rngl_lt_eq_cases Hor) in Hzc.
destruct Hzc as [Hzc| Hzc]. {
  exfalso.
  apply rngl_nlt_ge in Hacbc.
  apply Hacbc; clear Hacbc.
  now apply (rngl_mul_lt_mono_pos_r Hop Hor Hii).
}
subst c.
rewrite (rngl_mul_0_r Hos).
symmetry.
apply (rngl_opp_0 Hop).
Qed.

Definition rngl_distance :=
  {| d_dist := rngl_dist; d_prop := rngl_dist_is_dist Hop Hor |}.

(* to be completed
Theorem left_derivative_mul :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ A lt, (∀ x, ¬ (lt x x)) →
  ∀ da (f g f' g' : A → T) x₀,
  left_derivative_at lt da rngl_distance f f' x₀
  → left_derivative_at lt da rngl_distance g g' x₀
  → left_derivative_at lt da rngl_distance (λ x : A, (f x * g x)%L)
      (λ x : A, (f x * g' x + f' x * g x)%L) x₀.
Proof.
intros Hon Hiv.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Hlti * Hf Hg.
intros ε Hε.
specialize (Hf ε Hε).
specialize (Hg ε Hε).
move Hε before ε.
destruct Hf as (ηf & Hηf & Hf).
destruct Hg as (ηg & Hηg & Hg).
move ηf before ε.
move ηg before ηf.
move Hηg before Hηf.
exists (rngl_min ηf ηg).
split; [ now apply rngl_min_glb_lt | ].
intros x Hlt Hd.
specialize (Hf x Hlt).
specialize (Hg x Hlt).
assert (H : (d_dist x x₀ < ηf)%L). {
  eapply (rngl_lt_le_trans Hor); [ apply Hd | ].
  apply (rngl_le_min_l Hor).
}
specialize (Hf H); clear H.
assert (H : (d_dist x x₀ < ηg)%L). {
  eapply (rngl_lt_le_trans Hor); [ apply Hd | ].
  apply (rngl_le_min_r Hor).
}
specialize (Hg H); clear H.
cbn.
apply (rngl_mul_lt_mono_pos_r Hop Hor Hii (d_dist x x₀)) in Hf. 2: {
  clear H.
  apply (rngl_lt_iff Hor).
  destruct da as (da, dap).
  split; [ now apply (dist_nonneg Hon Hop Hiv Hor) | ].
  cbn; intros H; symmetry in H.
  apply dist_separation in H; [ | easy ].
  subst x.
  now apply Hlti in Hlt.
}
apply (rngl_mul_lt_mono_pos_r Hop Hor Hii (d_dist x x₀)) in Hg. 2: {
  clear H.
  apply (rngl_lt_iff Hor).
  destruct da as (da, dap).
  split; [ now apply (dist_nonneg Hon Hop Hiv Hor) | ].
  cbn; intros H; symmetry in H.
  apply dist_separation in H; [ | easy ].
  subst x.
  now apply Hlti in Hlt.
}
apply (rngl_mul_lt_mono_pos_r Hop Hor Hii (d_dist x x₀)). {
  apply (rngl_lt_iff Hor).
  destruct da as (da, dap).
  split; [ now apply (dist_nonneg Hon Hop Hiv Hor) | ].
  cbn; intros H; symmetry in H.
  apply dist_separation in H; [ | easy ].
  subst x.
  now apply Hlti in Hlt.
}
cbn in Hf, Hg.
rewrite (rngl_dist_mul_distr_r Hii) in Hf. 2: {
  now apply (dist_nonneg Hon Hop Hiv Hor).
}
rewrite (rngl_dist_mul_distr_r Hii) in Hg. 2: {
  now apply (dist_nonneg Hon Hop Hiv Hor).
}
rewrite (rngl_dist_mul_distr_r Hii). 2: {
  now apply (dist_nonneg Hon Hop Hiv Hor).
}
rewrite (rngl_div_mul Hon Hiv) in Hf. 2: {
  intros H.
  apply dist_separation in H; [ | now destruct da ].
  subst x.
  now apply Hlti in Hlt.
}
rewrite (rngl_div_mul Hon Hiv) in Hg. 2: {
  intros H.
  apply dist_separation in H; [ | now destruct da ].
  subst x.
  now apply Hlti in Hlt.
}
rewrite (rngl_div_mul Hon Hiv). 2: {
  intros H.
  apply dist_separation in H; [ | now destruct da ].
  subst x.
  now apply Hlti in Hlt.
}
rewrite rngl_mul_add_distr_r.
...
Search (0 ≤ angle_eucl_dist _ _)%L.
Require Import Trigo.TrigoWithoutPiExt.
About dist_nonneg.
Check angle_eucl_dist_nonneg.
...
Search rngl_dist.
Search (0 ≤ rngl_dist _ _)%L.
Search (0 ≤ d_dist _ _)%L.
....

Theorem derivative_mul :
  ∀ A lt da db (f g f' g' : A → T),
  is_derivative lt da db f f'
  → is_derivative lt da db g g'
  → is_derivative lt da db
      (λ x, (f x * g x)%L)
      (λ x, (f x * g' x + f' x * g x)%L).
Proof.
intros * Hf Hg.
split. {
*)

End a.
