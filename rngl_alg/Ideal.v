(* Ideal.v *)

(* ideals on a RingLike *)

From Stdlib Require Import Utf8 Arith.
Require Import RingLike.Core.
Require Import RingLike.Misc.

(* ideal : non empty set (type) with some properties *)

Record ideal T {ro : ring_like_op T} := mk_ip
  { ip_subtype : T → Prop;
    ip_zero : ip_subtype rngl_zero;
    ip_add :
      ∀ a b,
        ip_subtype a
        → ip_subtype b
        → ip_subtype (a + b)%L;
    ip_opp_or_psub :
      match rngl_opt_opp_or_psub T with
      | Some (inl opp) =>
          ∀ a, ip_subtype a → ip_subtype (opp a)%L
      | Some (inr psub) =>
          ∀ a b,
          ip_subtype a
          → ip_subtype b
          → ip_subtype (psub a b)
      | None =>
          not_applicable
      end;
    ip_mul_l : ∀ a b, ip_subtype b → ip_subtype (a * b)%L;
    ip_mul_r : ∀ a b, ip_subtype a → ip_subtype (a * b)%L }.

Arguments ip_subtype {T ro} i x%_L.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rr : ring_like_ord T}.
Context {rp : ring_like_prop T}.
Context {Hos : rngl_has_opp_or_psub T = true}.
Context {Heo : rngl_has_eq_dec_or_order T = true}.

(* 0 and 1 *)

Theorem I_zero_add : ∀ a b : T, a = 0%L → b = 0%L → (a + b = 0)%L.
Proof.
intros; subst.
apply rngl_add_0_l.
Qed.

Theorem I_zero_opp_or_psub :
  match rngl_opt_opp_or_psub T with
  | Some (inl opp) => ∀ a : T, a = 0%L → opp a = 0%L
  | Some (inr psub) => ∀ a b : T, a = 0%L → b = 0%L → psub a b = 0%L
  | None => not_applicable
  end.
Proof.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  specialize (rngl_opp_0 Hop) as H.
  progress unfold rngl_opp in H.
  progress unfold rngl_has_opp in Hop.
  destruct (rngl_opt_opp_or_psub T) as [op| ]; [ | easy ].
  destruct op as [opp| ]; [ | easy ].
  now intros; subst.
}
remember (rngl_has_psub T) as su eqn:Hsu.
symmetry in Hsu.
destruct su. {
  specialize rngl_opt_sub_0_l as H.
  rewrite Hsu in H.
  specialize (H 0)%L.
  progress unfold rngl_sub in H.
  rewrite Hop, Hsu in H.
  progress unfold rngl_psub in H.
  progress unfold rngl_has_opp in Hop.
  destruct (rngl_opt_opp_or_psub T) as [op| ]; [ | easy ].
  destruct op as [| psub ]; [ easy | ].
  now intros; subst.
}
progress unfold rngl_has_opp in Hop.
progress unfold rngl_has_psub in Hsu.
destruct (rngl_opt_opp_or_psub T) as [op| ]; [ | easy ].
now destruct op.
Qed.

Theorem I_zero_mul_l : ∀ a b : T, b = 0%L → (a * b = 0)%L.
Proof.
intros; subst.
apply (rngl_mul_0_r Hos).
Qed.

Theorem I_zero_mul_r : ∀ a b : T, a = 0%L → (a * b = 0)%L.
Proof.
intros; subst.
apply (rngl_mul_0_l Hos).
Qed.

Definition I_zero : ideal T :=
  {| ip_subtype a := a = 0%L;
     ip_zero := eq_refl;
     ip_add := I_zero_add;
     ip_opp_or_psub := I_zero_opp_or_psub;
     ip_mul_l := I_zero_mul_l;
     ip_mul_r := I_zero_mul_r |}.

Theorem I_one_opp_or_psub :
  match rngl_opt_opp_or_psub T with
  | Some (inl _) => T → True → True
  | Some (inr _) => T → T → True → True → True
  | None => not_applicable
  end.
Proof.
progress unfold rngl_has_opp_or_psub in Hos.
destruct (rngl_opt_opp_or_psub T) as [os| ]; [ | easy ].
now destruct os.
Qed.

Definition I_one : ideal T :=
  {| ip_subtype a := True;
     ip_zero := I;
     ip_add _ _ _ _ := I;
     ip_opp_or_psub := I_one_opp_or_psub;
     ip_mul_l _ _ _ := I;
     ip_mul_r _ _ _ := I |}.

(* addition *)

Definition I_add_subtype a b :=
  λ x, ∃ y z, x = (y + z)%L ∧ ip_subtype a y ∧ ip_subtype b z.

Theorem I_add_zero a b : I_add_subtype a b 0%L.
Proof.
exists 0%L, 0%L.
split; [ symmetry; apply rngl_add_0_l | ].
split; apply ip_zero.
Qed.

Theorem I_add_add a b :
  ∀ x y,
  I_add_subtype a b x → I_add_subtype a b y → I_add_subtype a b (x + y)%L.
Proof.
intros * Hx Hy.
destruct Hx as (x1 & x2 & Hx & Hx1 & Hx2).
destruct Hy as (y1 & y2 & Hy & Hy1 & Hy2).
subst x y.
exists (x1 + y1)%L, (x2 + y2)%L.
split; [ | now split; apply ip_add ].
do 2 rewrite rngl_add_assoc.
progress f_equal.
apply rngl_add_add_swap.
Qed.

(* to be completed
Theorem I_add_opp_or_psub a b :
  match rngl_opt_opp_or_psub T with
  | Some (inl opp) =>
      ∀ x : T, I_add_subtype a b x → I_add_subtype a b (opp x)
  | Some (inr psub) =>
      ∀ x y : T,
      I_add_subtype a b x
      → I_add_subtype a b y
      → I_add_subtype a b (psub x y)
  | None => not_applicable
  end.
Proof.
specialize (rngl_opp_add_distr) as H1.
progress unfold rngl_has_opp in H1.
progress unfold rngl_has_opp_or_psub in Hos.
progress unfold rngl_sub in H1.
progress unfold rngl_opp in H1.
progress unfold rngl_has_opp in H1.
destruct (rngl_opt_opp_or_psub T) as [os| ]; [ | easy ].
destruct os as [opp| psub]. {
  specialize (H1 eq_refl).
  intros * Hx.
  destruct Hx as (x1 & x2 & Hx & Hx1 & Hx2).
  subst.
  rewrite H1.
  exists (opp x1), (opp x2).
  split; [ easy | ].
  split.
...

Definition I_add (a b : ideal T): ideal T :=
  {| ip_subtype := I_add_subtype a b;
     ip_zero := I_add_zero a b;
     ip_add := I_add_add a b;
     ip_opp_or_psub := I_add_opp_or_psub a b;
     ip_mul_l := true;
     ip_mul_r := true |}.

...

(* multiplication *)

Theorem I_mul_zero :
  ∀ a b, (ip_subtype a 0 && ip_subtype b 0)%bool = true.
Proof.
...

Definition I_mul (a b : ideal T): ideal T :=
  {| ip_subtype x := (ip_subtype a x && ip_subtype b x)%bool;
     ip_zero := I_mul_zero a b;
     ip_add _ _ _ _ := eq_refl;
     ip_opp_or_psub := I_one_opp_or_psub;
     ip_mul_l := I_one_mul;
     ip_mul_r := I_one_mul |}.

...

(* ideal ring like op *)

Definition I_ring_like_op : ring_like_op (ideal T) :=
  {| rngl_zero := I_zero;
     rngl_add := I_add;
     rngl_mul := I_mul;
     rngl_opt_one := Some I_one;
     rngl_opt_opp_or_psub :=
       match rngl_opt_opp_or_psub T with
       | Some (inl _) => Some (inl I_opp)
       | Some (inr _) => Some (inr I_psub)
       | None => None
       end;
     rngl_opt_inv_or_pdiv := None;
     rngl_opt_is_zero_divisor :=
       match rngl_opt_is_zero_divisor T with
       | Some f => Some (λ i, f (i_val i))
       | None => None
       end;
     rngl_opt_eq_dec := I_opt_eq_dec;
     rngl_opt_leb := I_opt_leb |}.

...

(* multiplication *)

(*
Definition I_mul (a b : ideal P) : ideal P :=
  mk_I (i_val a * i_val b) (ip_mul_l (i_val a) (i_val b) (i_mem b)).
*)

(* opposite *)

(*
Theorem I_opp_prop : ∀ a : ideal P, P (- i_val a)%L = true.
Proof.
intros.
specialize ip_opp_or_psub as H1.
unfold rngl_opp.
destruct rngl_opt_opp_or_psub as [os| ]; [ | apply ip_zero ].
destruct os as [opp| psub]; [ | apply ip_zero ].
apply H1, a.
Qed.

Definition I_opp (a : ideal P) : ideal P :=
  mk_I (- i_val a) (I_opp_prop a).
*)

(* primitive subtraction *)

(*
Theorem I_psub_prop :
  ∀ (a b : ideal P), P (rngl_psub (i_val a) (i_val b)) = true.
Proof.
intros.
specialize ip_opp_or_psub as H1.
unfold rngl_psub.
destruct rngl_opt_opp_or_psub as [os| ]; [ | apply ip_zero ].
destruct os as [opp| psub]; [ apply ip_zero | ].
apply H1; [ apply a | apply b ].
Qed.

Definition I_psub (a b : ideal P) : ideal P :=
  mk_I (rngl_psub (i_val a) (i_val b)) (I_psub_prop a b).
*)

(* less equal *)

(* present definition of rngl_ord_mul_le_compat_nonneg doesn't
   allow ideals to have order *)
...
Definition I_opt_leb : option (ideal P → ideal P → bool) := None.
(*
Definition I_opt_leb : option (ideal P → ideal P → bool) :=
  match rngl_opt_leb with
  | Some leb => Some (λ a b : ideal P, leb (i_val a) (i_val b))
  | None => None
  end.
*)

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

Theorem neq_ideal_neq : ∀ (a b : ideal P), i_val a ≠ i_val b ↔ a ≠ b.
Proof.
intros.
now split; intros Hab H; apply Hab, eq_ideal_eq.
Qed.

(* eq_dec *)

Definition I_eq_dec (eq_dec : ∀ a b : T, {a = b} + {a ≠ b}) (a b : ideal P) :=
  eq_dec (i_val a) (i_val b).

Theorem I_opt_eq_dec : option (∀ a b : ideal P, {a = b} + {a ≠ b}).
Proof.
destruct (rngl_opt_eq_dec T) as [rngl_eq_dec| ]; [ | apply None ].
specialize (I_eq_dec rngl_eq_dec) as H1.
eapply Some.
intros.
specialize (H1 a b).
destruct H1 as [H1| H1]; [ left | right ]. {
  now apply eq_ideal_eq.
} {
  now apply neq_ideal_neq.
}
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

Arguments rngl_opt_one T {ring_like_op}.

Theorem I_opt_mul_1_l : let roi := I_ring_like_op in
  if rngl_has_1 (ideal P) then ∀ a : ideal P, (1 * a)%L = a
  else not_applicable.
Proof.
intros; cbn.
remember (rngl_has_1 _) as oni eqn:Honi; symmetry in Honi.
destruct oni; [ | easy ].
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honi |-*.
  progress unfold roi in Honi; cbn in Honi.
  progress unfold I_opt_one in Honi; cbn in Honi.
  now destruct rngl_opt_one.
}
intros.
apply eq_ideal_eq; cbn.
specialize (rngl_mul_1_l Hon (i_val a)) as H1.
progress unfold rngl_one in H1.
progress unfold roi.
progress unfold I_ring_like_op.
progress unfold rngl_one; cbn.
progress unfold rngl_has_1 in Honi.
progress unfold roi in Honi; cbn in Honi.
progress unfold rngl_has_1 in Hon.
remember I_opt_one as ion eqn:Hion; symmetry in Hion.
progress unfold I_opt_one in Hion.
destruct ion as [ione| ]; [ | easy ].
clear Honi.
destruct (rngl_opt_one T) as [one| ]; [ | easy ].
clear Hon.
destruct (Bool.bool_dec _ _) as [Hone| ]; [ | easy ].
injection Hion; clear Hion; intros; subst ione; cbn.
easy.
Qed.

Theorem I_mul_add_distr_l : let roi := I_ring_like_op in
  ∀ a b c : ideal P, (a * (b + c))%L = (a * b + a * c)%L.
Proof. intros; apply eq_ideal_eq, rngl_mul_add_distr_l. Qed.

Theorem I_opt_mul_comm : let roi := I_ring_like_op in
  if rngl_mul_is_comm T then ∀ a b : ideal P, (a * b)%L = (b * a)%L
  else not_applicable.
Proof.
intros.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
intros; apply eq_ideal_eq; cbn.
now apply rngl_mul_comm.
Qed.

Theorem I_opt_mul_1_r : let roi := I_ring_like_op in
  if rngl_mul_is_comm T then not_applicable
  else if rngl_has_1 (ideal P) then ∀ a : ideal P, (a * 1)%L = a
  else not_applicable.
Proof.
intros; cbn.
destruct rngl_mul_is_comm; [ easy | ].
remember (rngl_has_1 _) as oni eqn:Honi; symmetry in Honi.
destruct oni; [ | easy ].
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honi |-*.
  progress unfold roi in Honi; cbn in Honi.
  progress unfold I_opt_one in Honi; cbn in Honi.
  now destruct rngl_opt_one.
}
intros.
apply eq_ideal_eq; cbn.
specialize (rngl_mul_1_r Hon (i_val a)) as H1.
progress unfold rngl_one in H1.
progress unfold roi.
progress unfold I_ring_like_op.
progress unfold rngl_one; cbn.
progress unfold rngl_has_1 in Honi.
progress unfold roi in Honi; cbn in Honi.
progress unfold rngl_has_1 in Hon.
remember I_opt_one as ion eqn:Hion; symmetry in Hion.
progress unfold I_opt_one in Hion.
destruct ion as [ione| ]; [ | easy ].
clear Honi.
destruct (rngl_opt_one T) as [one| ]; [ | easy ].
clear Hon.
destruct (Bool.bool_dec _ _) as [Hone| ]; [ | easy ].
injection Hion; clear Hion; intros; subst ione; cbn.
easy.
Qed.

Theorem I_opt_mul_add_distr_r : let roi := I_ring_like_op in
  if rngl_mul_is_comm T then not_applicable
  else ∀ a b c : ideal P, ((a + b) * c)%L = (a * c + b * c)%L.
Proof.
intros.
remember rngl_mul_is_comm as ic eqn:Hic; symmetry in Hic.
destruct ic; [ easy | ].
intros; apply eq_ideal_eq; cbn.
apply rngl_mul_add_distr_r.
Qed.

Theorem I_opt_add_opp_diag_l : let roi := I_ring_like_op in
  if rngl_has_opp (ideal P) then ∀ a : ideal P, (- a + a)%L = 0%L
  else not_applicable.
Proof.
intros.
specialize (eq_refl (@rngl_has_opp T ro)) as Hop.
unfold rngl_has_opp in Hop at 2.
unfold rngl_has_opp, rngl_opp; cbn.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
destruct os as [opp| psub]; [ | easy ].
intros; apply eq_ideal_eq, (rngl_add_opp_diag_l Hop).
Qed.

Theorem rngl_has_psub_I_has_psub :
  let roi := I_ring_like_op in
  rngl_has_psub T = rngl_has_psub (ideal P).
Proof.
progress unfold rngl_has_psub; cbn.
remember (rngl_opt_opp_or_psub T) as os eqn:Hos.
symmetry in Hos.
destruct os as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem I_opt_add_sub : let roi := I_ring_like_op in
  if rngl_has_psub (ideal P) then ∀ a b : ideal P, (a + b - b)%L = a
  else not_applicable.
Proof.
intros.
remember (rngl_has_psub (ideal P)) as sui eqn:Hsui; symmetry in Hsui.
destruct sui; [ | easy ].
specialize (rngl_has_psub_has_no_opp Hsui) as Hopi.
assert (Hsu : @rngl_has_psub T ro = true). {
  unfold rngl_has_psub in Hsui |-*.
  cbn in Hsui.
  destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
  now destruct os.
}
specialize (rngl_has_psub_has_no_opp Hsu) as Hop.
intros.
apply eq_ideal_eq; cbn.
specialize rngl_opt_add_sub as H1.
unfold rngl_has_psub in H1.
unfold rngl_sub, rngl_psub.
rewrite Hopi, Hsui.
unfold rngl_sub in H1.
rewrite Hsu, Hop in H1.
progress unfold rngl_has_psub in Hsui, Hsu.
progress unfold rngl_has_opp in Hopi, Hop.
progress unfold roi.
progress unfold roi in Hopi.
progress unfold roi in Hsui.
cbn in Hsui, Hopi, Hsu, Hop |-*.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
destruct os as [opp| psub]; [ easy | ].
unfold I_psub, I_add; cbn.
apply H1.
Qed.

Theorem I_opt_sub_add_distr :
  let roi := I_ring_like_op in
  if rngl_has_psub (ideal P) then
    ∀ a b c : ideal P, (a - (b + c))%L = (a - b - c)%L
  else not_applicable.
Proof.
intros.
remember (rngl_has_psub (ideal P)) as sui eqn:Hsui; symmetry in Hsui.
destruct sui; [ | easy ].
specialize (rngl_has_psub_has_no_opp Hsui) as Hopi.
assert (Hsu : @rngl_has_psub T ro = true). {
  unfold rngl_has_psub in Hsui |-*.
  cbn in Hsui.
  destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
  now destruct os.
}
specialize (rngl_has_psub_has_no_opp Hsu) as Hop.
intros.
apply eq_ideal_eq; cbn.
specialize rngl_opt_sub_add_distr as H1.
unfold rngl_has_psub in H1.
unfold rngl_sub, rngl_psub.
rewrite Hopi, Hsui.
unfold rngl_sub in H1.
rewrite Hsu, Hop in H1.
progress unfold rngl_has_psub in Hsui, Hsu.
progress unfold rngl_has_opp in Hopi, Hop.
progress unfold roi.
progress unfold roi in Hopi.
progress unfold roi in Hsui.
cbn in Hsui, Hopi, Hsu, Hop |-*.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
destruct os as [opp| psub]; [ easy | ].
unfold I_psub, I_add; cbn.
apply H1.
Qed.

Theorem I_opt_sub_0_l :
  let roi := I_ring_like_op in
  if rngl_has_psub (ideal P) then ∀ a : ideal P, (0 - a)%L = 0%L
  else not_applicable.
Proof.
intros.
remember (rngl_has_psub (ideal P)) as sui eqn:Hsui; symmetry in Hsui.
destruct sui; [ | easy ].
specialize (rngl_has_psub_has_no_opp Hsui) as Hopi.
assert (Hsu : @rngl_has_psub T ro = true). {
  unfold rngl_has_psub in Hsui |-*.
  cbn in Hsui.
  destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
  now destruct os.
}
specialize (rngl_has_psub_has_no_opp Hsu) as Hop.
intros.
apply eq_ideal_eq; cbn.
specialize rngl_opt_sub_0_l as H1.
unfold rngl_has_psub in H1.
unfold rngl_sub, rngl_psub.
rewrite Hopi, Hsui.
unfold rngl_sub in H1.
rewrite Hsu, Hop in H1.
progress unfold rngl_has_psub in Hsui, Hsu.
progress unfold rngl_has_opp in Hopi, Hop.
progress unfold roi.
progress unfold roi in Hopi.
progress unfold roi in Hsui.
cbn in Hsui, Hopi, Hsu, Hop |-*.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
destruct os as [opp| psub]; [ easy | ].
unfold I_psub, I_add; cbn.
apply H1.
Qed.

(*
Theorem I_ord_le_dec :
  let roi := I_ring_like_op : ring_like_op (ideal P) in
  rngl_is_ordered (ideal P) = true →
  ∀ a b : ideal P, {(a ≤ b)%L} + {¬ (a ≤ b)%L}.
Proof.
intros roi Hor *.
specialize rngl_opt_ord as H1.
progress unfold rngl_is_ordered in Hor; cbn in Hor.
progress unfold I_opt_leb in Hor.
progress unfold rngl_is_ordered in H1.
destruct rngl_opt_leb; [ cbn in H1 | easy ].
specialize (rngl_ord_le_dec (i_val a) (i_val b)) as H2.
destruct H2 as [H2| H2]; [ left | right ]. {
  progress unfold rngl_le; cbn.
  progress unfold I_opt_leb.
  progress unfold rngl_le in H2.
  now destruct rngl_opt_leb.
} {
  intros H; apply H2; clear H2; rename H into H2.
  progress unfold rngl_le in H2; cbn in H2.
  progress unfold I_opt_leb in H2.
  progress unfold rngl_le.
  now destruct rngl_opt_leb.
}
Qed.

Theorem I_ord_le_refl :
  let roi := I_ring_like_op : ring_like_op (ideal P) in
  rngl_is_ordered (ideal P) = true →
  ∀ a : ideal P, (a ≤ a)%L.
Proof.
intros roi Hor *.
specialize rngl_opt_ord as H1.
progress unfold rngl_is_ordered in Hor; cbn in Hor.
progress unfold I_opt_leb in Hor.
progress unfold rngl_is_ordered in H1.
destruct rngl_opt_leb; [ cbn in H1 | easy ].
specialize (rngl_ord_le_refl (i_val a)) as H2.
progress unfold rngl_le; cbn.
progress unfold I_opt_leb.
progress unfold rngl_le in H2.
now destruct rngl_opt_leb.
Qed.

Theorem I_ord_le_antisymm :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  ∀ a b : ideal P, (a ≤ b)%L → (b ≤ a)%L → a = b.
Proof.
intros roi Hor a b Hab Hba.
specialize rngl_opt_ord as H1.
progress unfold rngl_is_ordered in Hor; cbn in Hor.
progress unfold I_opt_leb in Hor.
progress unfold rngl_is_ordered in H1.
destruct rngl_opt_leb; [ cbn in H1 | easy ].
specialize (rngl_ord_le_antisymm (i_val a) (i_val b)) as H2.
progress unfold rngl_le in Hab, Hba.
progress unfold rngl_le in H2.
progress unfold roi in Hab, Hba.
progress unfold I_ring_like_op in Hab, Hba.
cbn in Hab, Hba.
progress unfold I_opt_leb in Hab, Hba.
destruct rngl_opt_leb as [le| ]; [ | easy ].
apply eq_ideal_eq.
apply (H2 Hab Hba).
Qed.

Theorem I_ord_le_trans :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  ∀ a b c : ideal P, (a ≤ b)%L → (b ≤ c)%L → (a ≤ c)%L.
Proof.
intros roi Hor * Hab Hba.
specialize rngl_opt_ord as H1.
progress unfold rngl_is_ordered in Hor; cbn in Hor.
progress unfold I_opt_leb in Hor.
progress unfold rngl_is_ordered in H1.
destruct rngl_opt_leb; [ cbn in H1 | easy ].
specialize (rngl_ord_le_trans (i_val a) (i_val b) (i_val c)) as H2.
progress unfold rngl_le in Hab, Hba.
progress unfold rngl_le in H2.
progress unfold roi in Hab, Hba.
progress unfold I_ring_like_op in Hab, Hba.
progress unfold rngl_le.
progress unfold roi.
progress unfold I_ring_like_op.
cbn in Hab, Hba |-*.
progress unfold I_opt_leb in Hab, Hba.
progress unfold I_opt_leb.
destruct rngl_opt_leb as [le| ]; [ | easy ].
apply (H2 Hab Hba).
Qed.

Theorem rngl_is_ordered_ideal :
  let roi := I_ring_like_op : ring_like_op (ideal P) in
  rngl_is_ordered (ideal P) = rngl_is_ordered T.
Proof.
intros.
progress unfold rngl_is_ordered; cbn.
progress unfold I_opt_leb.
now destruct rngl_opt_leb.
Qed.
*)

Theorem rngl_has_opp_or_psub_ideal :
  let roi := I_ring_like_op : ring_like_op (ideal P) in
  rngl_has_opp_or_psub (ideal P) = rngl_has_opp_or_psub T.
Proof.
intros.
progress unfold rngl_has_opp_or_psub; cbn.
destruct (rngl_opt_opp_or_psub T) as [os| ]; [ | easy ].
now destruct os.
Qed.

(*
Theorem I_ord_add_le_mono_l :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  ∀ a b c : ideal P, (b ≤ c)%L ↔ (a + b ≤ a + c)%L.
Proof.
intros roi Hor; cbn.
progress unfold roi in Hor.
rewrite rngl_is_ordered_ideal in Hor.
remember (rngl_has_opp_or_psub (ideal P)) as os eqn:Hos.
symmetry in Hos.
progress unfold roi in Hos.
rewrite rngl_has_opp_or_psub_ideal in Hos.
intros.
specialize (rngl_add_le_mono_l Hor) as H2.
specialize (H2 (i_val a) (i_val b) (i_val c)).
progress unfold rngl_le in H2.
progress unfold rngl_le; cbn.
progress unfold I_opt_leb.
now destruct (rngl_opt_leb).
Qed.
*)

Theorem I_ord_mul_le_compat_nonneg :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  if (rngl_has_1 (ideal P) && rngl_has_inv_or_pdiv (ideal P))%bool then
    ∀ a b c d : ideal P, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L
  else not_applicable.
Proof.
intros roi Hor; cbn.
now rewrite Bool.andb_false_r.
Qed.

Theorem I_ord_mul_le_compat_nonpos :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  if (rngl_has_1 (ideal P) && rngl_has_inv_or_pdiv (ideal P))%bool then
    ∀ a b c d : ideal P, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L
  else not_applicable.
Proof.
intros roi Hor; cbn.
now rewrite Bool.andb_false_r.
Qed.

(*
Theorem I_ord_not_le :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  ∀ a b : ideal P, ¬ (a ≤ b)%L → a ≠ b ∧ (b ≤ a)%L.
Proof.
intros roi Hor.
intros * Hab.
specialize rngl_opt_ord as H1.
progress unfold rngl_is_ordered in Hor; cbn in Hor.
progress unfold I_opt_leb in Hor.
progress unfold rngl_is_ordered in H1.
destruct rngl_opt_leb; [ cbn in H1 | easy ].
specialize rngl_ord_not_le as H2.
specialize (H2 (i_val a) (i_val b)).
progress unfold rngl_le in Hab.
progress unfold rngl_le in H2.
progress unfold roi in Hab.
progress unfold I_ring_like_op in Hab.
progress unfold rngl_le.
progress unfold roi.
progress unfold I_ring_like_op.
cbn in Hab |-*.
progress unfold I_opt_leb in Hab.
progress unfold I_opt_leb.
destruct rngl_opt_leb as [le| ]. {
  specialize (H2 Hab).
  split; [ | easy ].
  intros H; subst b.
  now apply Hab; clear Hab.
}
now specialize (H2 Hab).
Qed.
*)

Theorem I_opt_integral :
  let roi := I_ring_like_op in
  ∀ a b : ideal P,
  (a * b)%L = 0%L
   → a = 0%L ∨ b = 0%L ∨ rngl_is_zero_divisor a ∨ rngl_is_zero_divisor b.
Proof.
intros * Hab.
progress unfold rngl_is_zero_divisor.
progress unfold rngl_opt_is_zero_divisor.
cbn.
remember (rngl_opt_is_zero_divisor T) as ozd eqn:Hozd.
symmetry in Hozd.
apply eq_ideal_eq in Hab.
cbn in Hab.
apply rngl_opt_integral in Hab.
destruct Hab as [Hab| [Hab| Hab]]. {
  now left; apply eq_ideal_eq.
} {
  now right; left; apply eq_ideal_eq.
}
destruct ozd as [f| ]. {
  destruct Hab as [Hab| Hab]. {
    right; right; left.
    progress unfold rngl_is_zero_divisor in Hab.
    cbn in Hozd.
    destruct (rngl_opt_is_zero_divisor T); [ | easy ].
    now injection Hozd; clear Hozd; intros; subst f.
  } {
    right; right; right.
    progress unfold rngl_is_zero_divisor in Hab.
    cbn in Hozd.
    destruct (rngl_opt_is_zero_divisor T); [ | easy ].
    now injection Hozd; clear Hozd; intros; subst f.
  }
}
progress unfold rngl_is_zero_divisor in Hab.
rewrite Hozd in Hab.
now destruct Hab.
Qed.

Theorem i_val_rngl_mul_nat : let roi := I_ring_like_op in
  ∀ a i, i_val (rngl_mul_nat a i) = rngl_mul_nat (i_val a) i.
Proof.
intros.
induction i; [ easy | cbn ].
f_equal; apply IHi.
Qed.

Theorem I_characteristic_prop : let roi := I_ring_like_op in
  if rngl_has_1 (ideal P) then
    if rngl_characteristic T =? 0 then ∀ i : nat, rngl_of_nat (S i) ≠ 0%L
    else
      (∀ i : nat, 0 < i < rngl_characteristic T → rngl_of_nat i ≠ 0%L) ∧
      rngl_of_nat (rngl_characteristic T) = 0%L
  else not_applicable.
Proof.
intros; cbn.
remember (rngl_has_1 (ideal P)) as oni eqn:Honi; symmetry in Honi.
destruct oni; [ | easy ].
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honi |-*.
  progress unfold roi in Honi; cbn in Honi.
  progress unfold I_opt_one in Honi.
  now destruct (rngl_opt_one T).
}
specialize rngl_opt_characteristic_prop as H1.
rewrite Hon in H1.
rewrite if_bool_if_dec in H1 |-*.
progress unfold roi.
progress unfold I_ring_like_op.
progress unfold rngl_one; cbn.
progress unfold I_opt_one.
progress unfold rngl_has_1 in Hon.
progress unfold rngl_has_1 in Honi; cbn in Honi.
progress unfold I_opt_one in Honi.
destruct (Sumbool.sumbool_of_bool _) as [Hcz| Hcz]. {
  apply Nat.eqb_eq in Hcz.
  intros.
  apply neq_ideal_neq; cbn.
  specialize (H1 i) as H2.
  cbn in H2.
  specialize i_val_rngl_mul_nat as H3.
  progress unfold rngl_mul_nat in H3.
  progress unfold mul_nat in H3; cbn in H3.
  rewrite H3; cbn.
  progress unfold rngl_one in H2.
  destruct (rngl_opt_one T) as [one| ]; [ | easy ].
  now destruct (Bool.bool_dec (P one) true).
}
destruct H1 as (Hbef, Hch).
progress unfold rngl_of_nat.
progress unfold rngl_of_nat in Hch.
split. {
  intros i Hi.
  specialize (Hbef i Hi) as H1.
  apply neq_ideal_neq.
  rewrite i_val_rngl_mul_nat; cbn.
  progress unfold rngl_of_nat in H1.
  progress unfold rngl_one in H1.
  destruct (rngl_opt_one T) as [one| ]; [ | easy ].
  now destruct (Bool.bool_dec (P one) true).
}
apply eq_ideal_eq.
rewrite i_val_rngl_mul_nat; cbn.
progress unfold rngl_one in Hch.
destruct (rngl_opt_one T) as [one| ]; [ | easy ].
now destruct (Bool.bool_dec (P one) true).
Qed.

Fixpoint List_map {A B} (f : A → B) l :=
  match l with
  | nil => nil
  | (a :: t)%list => (f a :: List_map f t)%list
  end.

(*
Definition I_ring_like_when_ord (Hor : rngl_is_ordered (ideal P) = true) :=
  {| rngl_ord_le_dec := I_ord_le_dec Hor;
     rngl_ord_le_refl := I_ord_le_refl Hor;
     rngl_ord_le_antisymm := I_ord_le_antisymm Hor;
     rngl_ord_le_trans := I_ord_le_trans Hor;
     rngl_ord_add_le_mono_l := I_ord_add_le_mono_l Hor;
     rngl_ord_mul_le_compat_nonneg := I_ord_mul_le_compat_nonneg Hor; (* fails *)
     rngl_ord_mul_le_compat_nonpos := I_ord_mul_le_compat_nonpos Hor;
     rngl_ord_not_le := I_ord_not_le Hor |}.

Theorem I_ring_like_ord :
  let roi := I_ring_like_op in
  if rngl_is_ordered (ideal P) then ring_like_ord (ideal P)
  else not_applicable.
Proof.
intros.
remember (rngl_is_ordered (ideal P)) as or eqn:Hor.
symmetry in Hor.
destruct or; [ | easy ].
apply (I_ring_like_when_ord Hor).
Qed.
*)

Definition I_ring_like_prop : ring_like_prop (ideal P) :=
  {| rngl_mul_is_comm := rngl_mul_is_comm T;
     rngl_is_archimedean := false;
     rngl_is_alg_closed := false;
     rngl_characteristic := rngl_characteristic T;
     rngl_add_comm := I_add_comm;
     rngl_add_assoc := I_add_assoc;
     rngl_add_0_l := I_add_0_l;
     rngl_mul_assoc := I_mul_assoc;
     rngl_opt_mul_1_l := I_opt_mul_1_l;
     rngl_mul_add_distr_l := I_mul_add_distr_l;
     rngl_opt_mul_comm := I_opt_mul_comm;
     rngl_opt_mul_1_r := I_opt_mul_1_r;
     rngl_opt_mul_add_distr_r := I_opt_mul_add_distr_r;
     rngl_opt_add_opp_diag_l := I_opt_add_opp_diag_l;
     rngl_opt_add_sub := I_opt_add_sub;
     rngl_opt_sub_add_distr := I_opt_sub_add_distr;
     rngl_opt_sub_0_l := I_opt_sub_0_l;
     rngl_opt_mul_inv_diag_l := NA;
     rngl_opt_mul_inv_diag_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_integral := I_opt_integral;
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := I_characteristic_prop;
     rngl_opt_ord := NA; (*I_ring_like_ord;*)
     rngl_opt_archimedean := NA |}.
*)

End a.
