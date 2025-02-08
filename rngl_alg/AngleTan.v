Require Import Utf8.
Require Import Main.RingLike.
Require Import Trigo.Angle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.

Definition rngl_tan θ := (rngl_sin θ / rngl_cos θ)%L.

(* to be completed
Theorem left_derivative_mul :
  ∀ A lt da db (f g f' g' : A → T) x₀,
  left_derivative_at lt da db f f' x₀
  → left_derivative_at lt da db g g' x₀
  → left_derivative_at lt da db (λ x : A, (f x * g x)%L)
      (λ x : A, (f x * g' x + f' x * g x)%L) x₀.
Proof.
intros * Hf Hg.
intros ε Hε.
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
