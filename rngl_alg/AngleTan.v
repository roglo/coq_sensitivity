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

(* to be completed
Definition rngl_distance :=
  {| d_dist := rngl_dist; d_prop := rngl_dist_is_dist Hop Hor |}.

Theorem left_derivative_mul :
  ∀ A lt da (f g f' g' : A → T) x₀,
  left_derivative_at lt da rngl_distance f f' x₀
  → left_derivative_at lt da rngl_distance g g' x₀
  → left_derivative_at lt da rngl_distance (λ x : A, (f x * g x)%L)
      (λ x : A, (f x * g' x + f' x * g x)%L) x₀.
Proof.
intros * Hf Hg.
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
Theorem rngl_dist_mul_distr_r :
  ∀ a b c, (rngl_dist a b * c = rngl_dist (a * c) (b * c))%L.
Proof.
intros.
progress unfold rngl_dist.
rewrite <- (rngl_mul_sub_distr_r Hop).
progress unfold rngl_abs.
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
