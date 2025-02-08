Set Nested Proofs Allowed.

Require Import Utf8.
Require Import Main.RingLike.
Require Import Trigo.Angle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Definition rngl_tan θ := (rngl_sin θ / rngl_cos θ)%L.

(* to be completed
Definition rngl_distance :=
  {| d_dist := rngl_dist; d_prop := rngl_dist_is_dist ac_op ac_or |}.

Theorem left_derivative_mul :
  rngl_is_ordered T = true →
  ∀ A lt da (f g f' g' : A → T) x₀,
  left_derivative_at lt da rngl_distance f f' x₀
  → left_derivative_at lt da db g g' x₀
  → left_derivative_at lt da db (λ x : A, (f x * g x)%L)
      (λ x : A, (f x * g' x + f' x * g x)%L) x₀.
Proof.
intros Hor.
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
Theorem dist_mul_distr_r :
  ∀ (dist : distance T) a b c,
  (d_dist a b * c = d_dist (a * c) (b * c))%L.
Proof.
intros.
destruct dist.
cbn.
destruct d_prop.
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
