(* RingLike on angles *)

From Stdlib Require Import Utf8.
Require Import RingLike.Core.
Require Import TrigoWithoutPi.Angle.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.

(* RingLike on angles by defining a phony multiplication always
   returning 0; no order because not compatible with addition *)

Definition angle_phony_mul (θ1 θ2 : angle T) := 0%A.

Instance angle_ring_like_op : ring_like_op (angle T) :=
  {| rngl_zero := 0%A;
     rngl_add := angle_add;
     rngl_mul := angle_phony_mul;
     rngl_opt_one := None;
     rngl_opt_opp_or_subt := Some (inl angle_opp);
     rngl_opt_inv_or_quot := None;
     rngl_opt_is_zero_divisor := Some (λ _, True);
     rngl_opt_eq_dec := Some (angle_eq_dec);
     rngl_opt_leb := None (* no order: fails on add_le_compat *) |}.

(*
Canonical Structure angle_ring_like_op.
*)

Theorem rngl_angle_add_comm : ∀ (a b : angle T), (a + b)%L = (b + a)%L.
Proof. apply angle_add_comm. Qed.

Theorem rngl_angle_add_assoc :
  ∀ a b c : angle T, (a + (b + c))%L = (a + b + c)%L.
Proof. apply angle_add_assoc. Qed.

Theorem rngl_angle_add_0_l : ∀ a : angle T, (0 + a)%L = a.
Proof. apply angle_add_0_l. Qed.

Theorem rngl_angle_mul_assoc :
  ∀ a b c : angle T, (a * (b * c))%L = (a * b * c)%L.
Proof. easy. Qed.

Theorem rngl_angle_mul_add_distr_l :
  ∀ a b c : angle T, (a * (b + c))%L = (a * b + a * c)%L.
Proof.
intros; cbn; progress unfold angle_phony_mul.
symmetry; apply angle_add_0_l.
Qed.

Theorem rngl_angle_opt_mul_comm :
  ∀ a b : angle T, (a * b)%L = (b * a)%L.
Proof. easy. Qed.

Theorem rngl_angle_opt_add_opp_diag_l :
  if rngl_has_opp (angle T) then ∀ a : angle T, (- a + a)%L = 0%L
  else not_applicable.
Proof. cbn; apply angle_add_opp_diag_l. Qed.

Theorem rngl_angle_integral :
  ∀ a b : angle T,
  (a * b)%L = 0%L
  → a = 0%L ∨ b = 0%L ∨ rngl_is_zero_divisor a ∨ rngl_is_zero_divisor b.
Proof.
intros * Hab.
now right; right; left.
Qed.

Instance angle_ring_like_prop :
  ring_like_prop (angle T) :=
  {| rngl_mul_is_comm := true;
     rngl_is_archimedean := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := rngl_angle_add_comm;
     rngl_add_assoc := rngl_angle_add_assoc;
     rngl_add_0_l := rngl_angle_add_0_l;
     rngl_mul_assoc := rngl_angle_mul_assoc;
     rngl_opt_mul_1_l := NA;
     rngl_mul_add_distr_l := rngl_angle_mul_add_distr_l;
     rngl_opt_mul_comm := rngl_angle_opt_mul_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_diag_l := rngl_angle_opt_add_opp_diag_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_sub_0_l := NA;
     rngl_opt_mul_inv_diag_l := NA;
     rngl_opt_mul_inv_diag_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_integral := rngl_angle_integral;
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := NA;
     rngl_opt_ord := NA;
     rngl_opt_archimedean := NA |}.

End a.
