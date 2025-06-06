(* Ideal.v *)

(* ideals on a RingLike *)

From Stdlib Require Import Utf8 Arith.
Require Import RingLike.Core.
Require Import RingLike.Misc.

Record ideal {T} (P : T → bool) := mk_I
  { i_val : T;
    i_mem : P i_val = true }.

Arguments mk_I {T P} i_val%_L i_mem.
Arguments i_val {T P} i%_L.
Arguments i_mem {T P} i%_L.

Class ideal_prop {T} {ro : ring_like_op T} (P : T → bool) := mk_ip
  { ip_zero : P rngl_zero = true;
    ip_add : ∀ a b, P a = true → P b = true → P (a + b)%L = true;
    ip_opp_or_subt :
      match rngl_opt_opp_or_subt T with
      | Some (inl opp) =>
          ∀ a, P a = true → P (opp a)%L = true
      | Some (inr subt) =>
          ∀ a b, P a = true → P b = true → P (subt a b) = true
      | None =>
          not_applicable
      end;
    ip_mul_l : ∀ a b, P b = true → P (a * b)%L = true;
    ip_mul_r : ∀ a b, P a = true → P (a * b)%L = true }.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rr : ring_like_ord T}.
Context {rp : ring_like_prop T}.
Context {P : T → bool}.
Context {ip : ideal_prop P}.

(* 0 and 1 *)

Definition I_zero : ideal P := mk_I 0 ip_zero.
Definition I_opt_one : option (ideal P) :=
  match rngl_opt_one T with
  | Some one =>
      match Bool.bool_dec (P one) true with
      | left ip_one => Some (mk_I one ip_one)
      | right _ => None
      end
  | None => None
  end.

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
specialize ip_opp_or_subt as H1.
unfold rngl_opp.
destruct rngl_opt_opp_or_subt as [os| ]; [ | apply ip_zero ].
destruct os as [opp| subt]; [ | apply ip_zero ].
apply H1, a.
Qed.

Definition I_opp (a : ideal P) : ideal P :=
  mk_I (- i_val a) (I_opp_prop a).

(* subtraction *)

Theorem I_subt_prop :
  ∀ (a b : ideal P), P (rngl_subt (i_val a) (i_val b)) = true.
Proof.
intros.
specialize ip_opp_or_subt as H1.
unfold rngl_subt.
destruct rngl_opt_opp_or_subt as [os| ]; [ | apply ip_zero ].
destruct os as [opp| subt]; [ apply ip_zero | ].
apply H1; [ apply a | apply b ].
Qed.

Definition I_subt (a b : ideal P) : ideal P :=
  mk_I (rngl_subt (i_val a) (i_val b)) (I_subt_prop a b).

(* less equal *)

Definition I_opt_leb : option (ideal P → ideal P → bool) :=
  match rngl_opt_leb with
  | Some leb => Some (λ a b : ideal P, leb (i_val a) (i_val b))
  | None => None
  end.

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
destruct rngl_opt_eq_dec as [rngl_eq_dec| ]; [ | apply None ].
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

(* ideal ring like op *)

Definition I_ring_like_op : ring_like_op (ideal P) :=
  {| rngl_zero := I_zero;
     rngl_add := I_add;
     rngl_mul := I_mul;
     rngl_opt_one := I_opt_one;
     rngl_opt_opp_or_subt :=
       match rngl_opt_opp_or_subt T with
       | Some (inl _) => Some (inl I_opp)
       | Some (inr _) => Some (inr I_subt)
       | None => None
       end;
     rngl_opt_inv_or_quot := None;
     rngl_opt_is_zero_divisor :=
       match rngl_opt_is_zero_divisor T with
       | Some f => Some (λ i, f (i_val i))
       | None => None
       end;
     rngl_opt_eq_dec := I_opt_eq_dec;
     rngl_opt_leb := I_opt_leb |}.

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
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
destruct os as [opp| subt]; [ | easy ].
intros; apply eq_ideal_eq, (rngl_add_opp_diag_l Hop).
Qed.

Theorem I_opt_add_sub : let roi := I_ring_like_op in
  if rngl_has_subt (ideal P) then ∀ a b : ideal P, (a + b - b)%L = a
  else not_applicable.
Proof.
intros.
remember (rngl_has_subt (ideal P)) as sui eqn:Hsui; symmetry in Hsui.
destruct sui; [ | easy ].
specialize (rngl_has_subt_has_no_opp Hsui) as Hopi.
assert (Hsu : @rngl_has_subt T ro = true). {
  unfold rngl_has_subt in Hsui |-*.
  cbn in Hsui.
  destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
  now destruct os.
}
specialize (rngl_has_subt_has_no_opp Hsu) as Hop.
intros.
apply eq_ideal_eq; cbn.
specialize rngl_opt_add_sub as H1.
unfold rngl_has_subt in H1.
unfold rngl_sub, rngl_subt.
rewrite Hopi, Hsui.
unfold rngl_sub in H1.
rewrite Hsu, Hop in H1.
progress unfold rngl_has_subt in Hsui, Hsu.
progress unfold rngl_has_opp in Hopi, Hop.
progress unfold roi.
progress unfold roi in Hopi.
progress unfold roi in Hsui.
cbn in Hsui, Hopi, Hsu, Hop |-*.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
destruct os as [opp| subt]; [ easy | ].
unfold I_subt, I_add; cbn.
apply H1.
Qed.

Theorem I_opt_sub_add_distr :
  let roi := I_ring_like_op in
  if rngl_has_subt (ideal P) then
    ∀ a b c : ideal P, (a - (b + c))%L = (a - b - c)%L
  else not_applicable.
Proof.
intros.
remember (rngl_has_subt (ideal P)) as sui eqn:Hsui; symmetry in Hsui.
destruct sui; [ | easy ].
specialize (rngl_has_subt_has_no_opp Hsui) as Hopi.
assert (Hsu : @rngl_has_subt T ro = true). {
  unfold rngl_has_subt in Hsui |-*.
  cbn in Hsui.
  destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
  now destruct os.
}
specialize (rngl_has_subt_has_no_opp Hsu) as Hop.
intros.
apply eq_ideal_eq; cbn.
specialize rngl_opt_sub_add_distr as H1.
unfold rngl_has_subt in H1.
unfold rngl_sub, rngl_subt.
rewrite Hopi, Hsui.
unfold rngl_sub in H1.
rewrite Hsu, Hop in H1.
progress unfold rngl_has_subt in Hsui, Hsu.
progress unfold rngl_has_opp in Hopi, Hop.
progress unfold roi.
progress unfold roi in Hopi.
progress unfold roi in Hsui.
cbn in Hsui, Hopi, Hsu, Hop |-*.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
destruct os as [opp| subt]; [ easy | ].
unfold I_subt, I_add; cbn.
apply H1.
Qed.

Theorem I_opt_sub_0_l :
  let roi := I_ring_like_op in
  if rngl_has_subt (ideal P) then ∀ a : ideal P, (0 - a)%L = 0%L
  else not_applicable.
Proof.
intros.
remember (rngl_has_subt (ideal P)) as sui eqn:Hsui; symmetry in Hsui.
destruct sui; [ | easy ].
specialize (rngl_has_subt_has_no_opp Hsui) as Hopi.
assert (Hsu : @rngl_has_subt T ro = true). {
  unfold rngl_has_subt in Hsui |-*.
  cbn in Hsui.
  destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
  now destruct os.
}
specialize (rngl_has_subt_has_no_opp Hsu) as Hop.
intros.
apply eq_ideal_eq; cbn.
specialize rngl_opt_sub_0_l as H1.
unfold rngl_has_subt in H1.
unfold rngl_sub, rngl_subt.
rewrite Hopi, Hsui.
unfold rngl_sub in H1.
rewrite Hsu, Hop in H1.
progress unfold rngl_has_subt in Hsui, Hsu.
progress unfold rngl_has_opp in Hopi, Hop.
progress unfold roi.
progress unfold roi in Hopi.
progress unfold roi in Hsui.
cbn in Hsui, Hopi, Hsu, Hop |-*.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
destruct os as [opp| subt]; [ easy | ].
unfold I_subt, I_add; cbn.
apply H1.
Qed.

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

Theorem I_ord_add_le_compat :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  ∀ a b c d : ideal P, (a ≤ b)%L → (c ≤ d)%L → (a + c ≤ b + d)%L.
Proof.
intros roi Hor.
intros * Hab Hcd.
specialize rngl_opt_ord as H1.
progress unfold rngl_is_ordered in Hor; cbn in Hor.
progress unfold I_opt_leb in Hor.
progress unfold rngl_is_ordered in H1.
destruct rngl_opt_leb; [ cbn in H1 | easy ].
specialize rngl_ord_add_le_compat as H2.
specialize (H2 (i_val a) (i_val b) (i_val c) (i_val d)).
progress unfold rngl_le in Hab, Hcd.
progress unfold rngl_le in H2.
progress unfold roi in Hab, Hcd.
progress unfold I_ring_like_op in Hab, Hcd.
progress unfold rngl_le.
progress unfold roi.
progress unfold I_ring_like_op.
cbn in Hab, Hcd |-*.
progress unfold I_opt_leb in Hab, Hcd.
progress unfold I_opt_leb.
destruct rngl_opt_leb as [le| ]; [ | easy ].
apply (H2 Hab Hcd).
Qed.

Theorem I_ord_mul_le_compat_nonneg :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  ∀ a b c d : ideal P, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L.
Proof.
intros roi Hor.
specialize rngl_ord_mul_le_compat_nonneg as H1.
intros * Hac Hbd.
progress unfold rngl_is_ordered in Hor; cbn in Hor.
progress unfold I_opt_leb in Hor.
progress unfold rngl_le.
progress unfold rngl_le in Hac.
progress unfold rngl_le in Hbd.
progress unfold rngl_le in H1.
progress unfold rngl_opt_leb in Hac.
progress unfold rngl_opt_leb in Hbd.
cbn in Hac, Hbd.
progress unfold rngl_opt_leb.
cbn.
progress unfold I_opt_leb in Hac.
progress unfold I_opt_leb in Hbd.
progress unfold I_opt_leb.
destruct rngl_opt_leb as [le| ]; [ | easy ].
now apply H1.
Qed.

Theorem I_ord_mul_le_compat_nonpos :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  ∀ a b c d : ideal P, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L.
Proof.
intros roi Hor.
intros * Hca Hdb.
specialize rngl_ord_mul_le_compat_nonpos as H2.
progress unfold rngl_le in Hca.
progress unfold rngl_le in Hdb.
progress unfold rngl_le.
cbn in Hca, Hdb |-*.
progress unfold I_opt_leb in Hca.
progress unfold I_opt_leb in Hdb.
progress unfold I_opt_leb.
specialize rngl_opt_ord as H1.
progress unfold rngl_is_ordered in Hor; cbn in Hor.
progress unfold I_opt_leb in Hor.
progress unfold rngl_is_ordered in H1.
progress unfold rngl_le in H2.
destruct rngl_opt_leb; [ cbn in H1 | easy ].
now apply H2.
Qed.

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

Definition I_ring_like_when_ord (Hor : rngl_is_ordered (ideal P) = true) :=
  {| rngl_ord_le_dec := I_ord_le_dec Hor;
     rngl_ord_le_refl := I_ord_le_refl Hor;
     rngl_ord_le_antisymm := I_ord_le_antisymm Hor;
     rngl_ord_le_trans := I_ord_le_trans Hor;
     rngl_ord_add_le_compat := I_ord_add_le_compat Hor;
     rngl_ord_mul_le_compat_nonneg := I_ord_mul_le_compat_nonneg Hor;
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
     rngl_opt_mul_quot_r := NA;
     rngl_opt_integral := I_opt_integral;
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := I_characteristic_prop;
     rngl_opt_ord := I_ring_like_ord;
     rngl_opt_archimedean := NA |}.

End a.
