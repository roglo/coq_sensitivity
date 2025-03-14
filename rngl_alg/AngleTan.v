(* trigonometry; tangent *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Require Import Main.RingLike.
Require Import Trigo.RealLike.
Require Import Trigo.Angle.
Require Import Trigo.AngleTypeIsComplete.
Require Import DerivMul.
Require Import AngleDeriv.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Definition rngl_tan θ := (rngl_sin θ / rngl_cos θ)%L.

(* conflict in the definition of rngl_distance of
   DerivMul.v and AngleTypeIsComplete

About rngl_distance.
...
rngl_distance :
∀ {T : Type} {ro : ring_like_op T},
  ring_like_prop T
  → rngl_has_opp T = true → rngl_is_ordered T = true → distance T

rngl_distance is not universe polymorphic
Arguments rngl_distance {T}%type_scope {ro rp Hop Hor}
rngl_distance is transparent
Expands to: Constant RnglAlg.DerivMul.rngl_distance
...
rngl_distance :
∀ {T : Type} {ro : ring_like_op T} {rp : ring_like_prop T},
  angle_ctx T → distance T

rngl_distance is not universe polymorphic
Arguments rngl_distance {T}%type_scope {ro rp ac}
rngl_distance is transparent
Expands to: Constant Trigo.AngleTypeIsComplete.rngl_distance
Check @rngl_distance.
...

Theorem rngl_tan_derivative :
  is_derivative angle_le angle_lt_for_deriv angle_eucl_distance rngl_distance
    rngl_tan (λ θ, (1 - (rngl_cos θ)²)%L).
...
*)

End a.
