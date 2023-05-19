(* Ideal.v *)

(* ideals on a RingLike *)

Set Nested Proofs Allowed.

Require Import Utf8.
Require Import Main.RingLike.

Record ideal {T} (P : T → bool) := mk_I
  { i_val : T;
    i_mem : P i_val = true }.

Arguments mk_I {T P} i_val%L i_mem.
Arguments i_val {T P} i%L.
Arguments i_mem {T P} i%L.

Class ideal_prop {T} {ro : ring_like_op T} (P : T → bool) := mk_ip
  { ip_zero : P rngl_zero = true;
    ip_one : P rngl_one = true;
    ip_add : ∀ a b, P a = true → P b = true → P (a + b)%L = true;
    ip_opp :
      if rngl_has_opp then ∀ a, P a = true → P (- a)%L = true
      else not_applicable;
    ip_mul_l : ∀ a b, P b = true → P (a * b)%L = true;
    ip_mul_r : ∀ a b, P a = true → P (a * b)%L = true }.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {P : T → bool}.
Context {ip : ideal_prop P}.

(* 0 and 1 *)

Definition I_zero : ideal P := mk_I 0 ip_zero.
Definition I_one : ideal P := mk_I 1 ip_one.

(* addition *)

Definition I_add (a b : ideal P): ideal P :=
  mk_I (i_val a + i_val b) (ip_add (i_val a) (i_val b) (i_mem a) (i_mem b)).

(* multiplication *)

Definition I_mul (a b : ideal P) : ideal P :=
  mk_I (i_val a * i_val b) (ip_mul_l (i_val a) (i_val b) (i_mem b)).

(* opposite *)

Theorem I_opp_prop : ∀ a : ideal P, P (- i_val a)%L = true.
Proof.
intros.
specialize ip_opp as H1.
unfold rngl_opp in H1 |-*.
unfold rngl_has_opp in H1.
destruct rngl_opt_opp_or_subt as [os| ]; [ | apply ip_zero ].
destruct os as [opp| subt]; [ | apply ip_zero ].
apply H1, a.
Show Proof.
Definition I_opp_prop' (a : ideal P) : P (- i_val a)%L = true :=
   let H1 :
     if rngl_has_opp
     then ∀ a0 : T, P a0 = true → P (- a0)%L = true
     else not_applicable := ip_opp
   in
   match rngl_opt_opp_or_subt
      as o0
      return
        ((if match o0 with
             | Some (inl _) => true
             | _ => false
             end
          then
           ∀ a0 : T,
             P a0 = true
             → P
                 match o0 with
                 | Some (inl rngl_opp) => rngl_opp a0
                 | _ => 0%L
                 end = true
          else not_applicable)
         → P
             match o0 with
             | Some (inl rngl_opp) => rngl_opp (i_val a)
             | _ => 0%L
             end = true)
    with
    | Some os =>
        λ (H2 : if
                  match os with
                  | inl _ => true
                  | inr _ => false
                  end
                then
                  ∀ a1 : T,
                    P a1 = true
                    → P
                        match os with
                        | inl rngl_opp =>
                            rngl_opp a1
                        | inr _ => 0%L
                        end = true
                else not_applicable),
        match os as s
          return
          ((if match s with
               | inl _ => true
               | inr _ => false
               end
            then
              ∀ a1 : T,
                P a1 = true
                → P
                    match s with
                    | inl rngl_opp => rngl_opp a1
                    | inr _ => 0%L
                    end = true
            else not_applicable)
           → P
               match s with
               | inl rngl_opp => rngl_opp (i_val a)
               | inr _ => 0%L
               end = true)
        with
        | inl opp => λ H3, H3 (i_val a) (i_mem a)
        | inr b => λ _, ip_zero
        end H2
    | None => λ _, ip_zero
    end H1.
...
Theorem I_opp_prop'' : ∀ a : ideal P, P (- i_val a)%L = true.
Proof.
intros a.
remember (I_opp_prop' a) as x eqn:Hx.
unfold I_opp_prop' in Hx.
cbn in Hx.
...
Theorem I_opp_prop' : ∀ a : ideal P, P (- i_val a)%L = true.
Proof.
intros.
specialize ip_opp as H1.
unfold rngl_opp in H1 |-*.
unfold rngl_has_opp in H1.
unfold rngl_opp.
refine (
  match rngl_opt_opp_or_subt with
  | Some (inl opp) => _ opp
  | Some (inr subt) => _ subt
  | None => _
  end). 3: {
...
Qed.

Definition I_opp (a : ideal P) : ideal P :=
  mk_I (- i_val a) (I_opp_prop a).

(*
Definition I_opp (a : ideal P) : ideal P :=
  mk_I (- i_val a) (ip_opp (i_val a) (i_mem a)).
*)

(* subtraction

Theorem glop : ∀ (a b : ideal P), P (rngl_subt (i_val a) (i_val b)) = true.
Proof.
intros.
...

Definition I_sub (a b : ideal P) : ideal P :=
  mk_I (rngl_subt (i_val a) (i_val b)) (glop a b).
...
*)

(* ideal ring like op *)

Definition I_ring_like_op : ring_like_op (ideal P) :=
  {| rngl_zero := I_zero;
     rngl_one := I_one;
     rngl_add := I_add;
     rngl_mul := I_mul;
     rngl_opt_opp_or_subt :=
       match rngl_opt_opp_or_subt with
       | Some (inl _) => Some (inl I_opp)
       | Some (inr _) => None (*Some (inr 42)*)
       | None => None
       end;
     rngl_opt_inv_or_quot := None;
     rngl_opt_eqb := None;
     rngl_opt_le := None |}.

(* equality in ideals is equivalent to equality in their values,
   because the proof of their properties (i_mem), being an equality
   between booleans, is unique *)

Theorem eq_ideal_eq : ∀ (a b : ideal P), i_val a = i_val b ↔ a = b.
Proof.
intros.
split; intros Hab; [ | now subst ].
destruct a as (a, pa).
destruct b as (b, pb).
cbn in Hab.
subst b.
f_equal.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

(* ideal ring like prop *)

Theorem I_add_comm : let roi := I_ring_like_op in
  ∀ a b : ideal P, (a + b)%L = (b + a)%L.
Proof. intros; apply eq_ideal_eq, rngl_add_comm. Qed.

Theorem I_add_assoc : let roi := I_ring_like_op in
  ∀ a b c : ideal P, (a + (b + c))%L = (a + b + c)%L.
Proof. intros; apply eq_ideal_eq, rngl_add_assoc. Qed.

Theorem I_add_0_l : let roi := I_ring_like_op in
  ∀ a : ideal P, (0 + a)%L = a.
Proof. intros; apply eq_ideal_eq, rngl_add_0_l. Qed.

Theorem I_mul_assoc : let roi := I_ring_like_op in
  ∀ a b c : ideal P, (a * (b * c))%L = (a * b * c)%L.
Proof. intros; apply eq_ideal_eq, rngl_mul_assoc. Qed.

Theorem I_mul_1_l : let roi := I_ring_like_op in
  ∀ a : ideal P, (1 * a)%L = a.
Proof. intros; apply eq_ideal_eq, rngl_mul_1_l. Qed.

Theorem I_mul_add_distr_l : let roi := I_ring_like_op in
  ∀ a b c : ideal P, (a * (b + c))%L = (a * b + a * c)%L.
Proof. intros; apply eq_ideal_eq, rngl_mul_add_distr_l. Qed.

Theorem I_opt_mul_1_r : let roi := I_ring_like_op in
  ∀ a : ideal P, (a * 1)%L = a.
Proof. intros; apply eq_ideal_eq, rngl_mul_1_r. Qed.

Theorem I_opt_mul_add_distr_r : let roi := I_ring_like_op in
  ∀ a b c : ideal P, ((a + b) * c)%L = (a * c + b * c)%L.
Proof. intros; apply eq_ideal_eq, rngl_mul_add_distr_r. Qed.

Theorem I_opt_add_opp_l : let roi := I_ring_like_op in
  if rngl_has_opp then ∀ a : ideal P, (- a + a)%L = 0%L else not_applicable.
Proof.
intros.
specialize (eq_refl (@rngl_has_opp T ro)) as Hop.
unfold rngl_has_opp in Hop at 2.
unfold rngl_has_opp, rngl_opp; cbn.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
destruct os as [opp| subt]; [ | easy ].
intros; apply eq_ideal_eq, (rngl_add_opp_l Hop).
Qed.

Theorem I_opt_add_sub : let roi := I_ring_like_op in
  if rngl_has_subt then ∀ a b : ideal P, (a + b - b)%L = a
  else not_applicable.
Proof.
intros.
unfold rngl_has_subt; cbn.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem I_opt_sub_add_distr : let roi := I_ring_like_op in
  if rngl_has_subt then ∀ a b c : ideal P, (a - (b + c))%L = (a - b - c)%L
  else not_applicable.
Proof.
intros.
unfold rngl_has_subt; cbn.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem rngl_of_nat_ideal : let roi := I_ring_like_op in
  ∀ i, i_val (rngl_of_nat i) = rngl_of_nat i.
Proof.
intros.
induction i; [ easy | now cbn; rewrite IHi ].
Qed.

Theorem I_characteristic_prop : let roi := I_ring_like_op in
  if Nat.eqb rngl_characteristic 0 then ∀ i : nat, rngl_of_nat (S i) ≠ 0%L
  else
    (∀ i : nat, 0 < i < rngl_characteristic → rngl_of_nat i ≠ 0%L) ∧
    rngl_of_nat rngl_characteristic = 0%L.
Proof.
intros; cbn.
specialize rngl_characteristic_prop as characteristic_prop.
remember (Nat.eqb rngl_characteristic 0) as ch eqn:Hch; symmetry in Hch.
destruct ch. {
  apply Nat_eqb_eq in Hch.
  intros i Hi.
  apply eq_ideal_eq in Hi; cbn in Hi.
  rewrite rngl_of_nat_ideal in Hi.
  cbn in characteristic_prop.
  now apply (characteristic_prop i).
}
destruct characteristic_prop as (H1, H2).
split. {
  intros i Hi H.
  apply eq_ideal_eq in H; cbn in H.
  apply (H1 i Hi).
  now rewrite rngl_of_nat_ideal in H.
} {
  apply eq_ideal_eq; cbn.
  now rewrite rngl_of_nat_ideal.
}
Qed.

Definition I_ring_like_prop : ring_like_prop (ideal P) :=
  {| rngl_mul_is_comm := false;
     rngl_has_dec_le := false;
     rngl_is_integral := false;
     rngl_is_alg_closed := false;
     rngl_characteristic := rngl_characteristic;
     rngl_add_comm := I_add_comm;
     rngl_add_assoc := I_add_assoc;
     rngl_add_0_l := I_add_0_l;
     rngl_mul_assoc := I_mul_assoc;
     rngl_mul_1_l := I_mul_1_l;
     rngl_mul_add_distr_l := I_mul_add_distr_l;
     rngl_opt_mul_comm := NA;
     rngl_opt_mul_1_r := I_opt_mul_1_r;
     rngl_opt_mul_add_distr_r := I_opt_mul_add_distr_r;
     rngl_opt_add_opp_l := I_opt_add_opp_l;
     rngl_opt_add_sub := I_opt_add_sub;
     rngl_opt_sub_add_distr := I_opt_sub_add_distr;
     rngl_opt_mul_inv_l := NA;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_eqb_eq := NA;
     rngl_opt_le_dec := NA;
     rngl_opt_integral := NA;
     rngl_opt_alg_closed := NA;
     rngl_characteristic_prop := I_characteristic_prop;
     rngl_opt_le_refl := NA;
     rngl_opt_le_antisymm := NA;
     rngl_opt_le_trans := NA;
     rngl_opt_add_le_compat := NA;
     rngl_opt_mul_le_compat_nonneg := NA;
     rngl_opt_mul_le_compat_nonpos := NA;
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := NA |}.

End a.
