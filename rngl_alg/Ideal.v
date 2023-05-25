(* Ideal.v *)

(* ideals on a RingLike *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Require Import Main.Misc Main.RingLike.

Record ideal {T} (P : T → bool) := mk_I
  { i_val : T;
    i_mem : P i_val = true }.

Arguments mk_I {T P} i_val%L i_mem.
Arguments i_val {T P} i%L.
Arguments i_mem {T P} i%L.

Class ideal_prop {T} {ro : ring_like_op T} (P : T → bool) := mk_ip
  { ip_zero : P rngl_zero = true;
    ip_add : ∀ a b, P a = true → P b = true → P (a + b)%L = true;
    ip_opp_or_subt :
      match rngl_opt_opp_or_subt with
      | Some (inl opp) => ∀ a, P a = true → P (opp a)%L = true
      | Some (inr subt) => ∀ a b, P a = true → P b = true → P (subt a b) = true
      | None => not_applicable
      end;
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

(* computable equality eqb *)

Definition I_eqb (eqb : T → T → bool) (a b : ideal P) : bool :=
  eqb (i_val a) (i_val b).

(* less equal *)

Definition I_opt_le : option (ideal P → ideal P → Prop) :=
  match rngl_opt_le with
  | Some le => Some (λ a b : ideal P, le (i_val a) (i_val b))
  | None => None
  end.

(* ideal ring like op *)

Definition I_ring_like_op : ring_like_op (ideal P) :=
  {| rngl_zero := I_zero;
     rngl_add := I_add;
     rngl_mul := I_mul;
     rngl_opt_one :=
       match rngl_opt_one  with
       | Some one =>
           match Bool.bool_dec (P one) true with
           | left ip_one => Some (mk_I one ip_one)
           | right _ => None
           end
       | None => None
       end;
     rngl_opt_opp_or_subt :=
       match rngl_opt_opp_or_subt with
       | Some (inl _) => Some (inl I_opp)
       | Some (inr _) => Some (inr I_subt)
       | None => None
       end;
     rngl_opt_inv_or_quot := None;
     rngl_opt_eqb :=
       match rngl_opt_eqb with
       | Some eqb => Some (I_eqb eqb)
       | None => None
       end;
     rngl_opt_le := I_opt_le |}.

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

Theorem I_opt_mul_1_l : let roi := I_ring_like_op in
  if rngl_has_1 then ∀ a : ideal P, (1 * a)%L = a
  else not_applicable.
Proof.
intros; cbn.
remember rngl_has_1 as oni eqn:Honi; symmetry in Honi.
destruct oni; [ | easy ].
intros.
apply eq_ideal_eq; cbn.
progress unfold roi.
progress unfold I_ring_like_op.
progress unfold rngl_one.
cbn.
progress unfold rngl_has_1 in Honi.
progress unfold roi in Honi.
cbn in Honi.
specialize (rngl_mul_1_l) as H2.
progress unfold rngl_has_1 in H2.
progress unfold rngl_one in H2.
remember rngl_opt_one as on eqn:Hon; symmetry in Hon.
destruct on as [one| ]; [ | easy ].
cbn in Honi.
destruct (Bool.bool_dec (P one) true) as [H1| H1]; [ cbn | easy ].
clear Honi.
now apply H2.
Qed.

Theorem I_mul_add_distr_l : let roi := I_ring_like_op in
  ∀ a b c : ideal P, (a * (b + c))%L = (a * b + a * c)%L.
Proof. intros; apply eq_ideal_eq, rngl_mul_add_distr_l. Qed.

Theorem I_opt_mul_comm : let roi := I_ring_like_op in
  if rngl_mul_is_comm then ∀ a b : ideal P, (a * b)%L = (b * a)%L
  else not_applicable.
Proof.
intros.
remember rngl_mul_is_comm as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
intros; apply eq_ideal_eq; cbn.
now apply rngl_mul_comm.
Qed.

Theorem I_opt_mul_1_r : let roi := I_ring_like_op in
  if rngl_mul_is_comm then not_applicable
  else if rngl_has_1 then ∀ a : ideal P, (a * 1)%L = a
  else not_applicable.
Proof.
intros; cbn.
destruct rngl_mul_is_comm; [ easy | ].
progress unfold rngl_one.
progress unfold rngl_has_1.
specialize rngl_mul_1_r as H1.
progress unfold rngl_has_1 in H1.
progress unfold rngl_one in H1.
progress unfold roi.
cbn.
remember rngl_opt_one as oni eqn:Honi; symmetry in Honi.
destruct oni as [one| ]; [ cbn | easy ].
destruct (Bool.bool_dec (P one) true) as [H2| H2]; [ cbn | easy ].
intros.
apply eq_ideal_eq; cbn.
now apply H1.
Qed.

Theorem I_opt_mul_add_distr_r : let roi := I_ring_like_op in
  if rngl_mul_is_comm then not_applicable
  else ∀ a b c : ideal P, ((a + b) * c)%L = (a * c + b * c)%L.
Proof.
intros.
remember rngl_mul_is_comm as ic eqn:Hic; symmetry in Hic.
destruct ic; [ easy | ].
intros; apply eq_ideal_eq; cbn.
apply rngl_mul_add_distr_r.
Qed.

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
remember rngl_has_subt as sui eqn:Hsui; symmetry in Hsui.
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

Theorem I_opt_sub_add_distr : let roi := I_ring_like_op in
  if rngl_has_subt then ∀ a b c : ideal P, (a - (b + c))%L = (a - b - c)%L
  else not_applicable.
Proof.
intros.
remember rngl_has_subt as sui eqn:Hsui; symmetry in Hsui.
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

Theorem I_opt_le_dec : let roi := I_ring_like_op in
  if rngl_has_dec_le then ∀ a b : ideal P, {(a ≤ b)%L} + {¬ (a ≤ b)%L}
   else not_applicable.
Proof.
intros.
remember rngl_has_dec_le as de eqn:Hde; symmetry in Hde.
destruct de; [ | easy ].
intros.
specialize rngl_opt_le_dec as H1.
rewrite Hde in H1.
specialize (H1 (i_val a) (i_val b)).
destruct H1 as [H1| H1]; [ left | right ]. {
  progress unfold rngl_le; cbn.
  progress unfold I_opt_le.
  progress unfold rngl_le in H1.
  now destruct rngl_opt_le.
} {
  intros H; apply H1; clear H1; rename H into H1.
  progress unfold rngl_le in H1;   cbn in H1.
  progress unfold I_opt_le in H1.
  progress unfold rngl_le.
  now destruct rngl_opt_le.
}
Qed.

Theorem I_opt_eqb_eq : let roi := I_ring_like_op in
  if rngl_has_eqb then ∀ a b : ideal P, (a =? b)%L = true ↔ a = b
  else not_applicable.
Proof.
intros.
remember rngl_has_eqb as ebi eqn:Hebi; symmetry in Hebi.
destruct ebi; [ | easy ].
assert (Heb : @rngl_has_eqb T ro = true). {
  progress unfold roi in Hebi.
  progress unfold I_ring_like_op in Hebi.
  progress unfold rngl_has_eqb in Hebi |-*.
  cbn in Hebi.
  now destruct rngl_opt_eqb.
}
specialize (rngl_eqb_eq Heb) as H1.
intros.
split; intros Hab. {
  apply eq_ideal_eq.
  progress unfold rngl_eqb in Hab.
  progress unfold rngl_eqb in H1.
  cbn in Hab.
  progress unfold rngl_has_eqb in Heb.
  destruct rngl_opt_eqb as [eqb| ]; [ | easy ].
  now apply H1.
} {
  apply eq_ideal_eq in Hab.
  apply H1 in Hab.
  progress unfold rngl_eqb.
  progress unfold rngl_has_eqb in Hebi; cbn in Hebi.
  progress unfold rngl_eqb in Hab.
  progress unfold roi; cbn.
  now destruct rngl_opt_eqb.
}
Qed.

Theorem I_opt_integral : let roi := I_ring_like_op in
  if rngl_is_integral then
    ∀ a b : ideal P, (a * b)%L = 0%L → a = 0%L ∨ b = 0%L
  else
    not_applicable.
Proof.
intros.
remember rngl_is_integral as it eqn:Hit; symmetry in Hit.
destruct it; [ | easy ].
intros * Hab.
cbn in Hab.
apply eq_ideal_eq in Hab; cbn in Hab.
specialize rngl_opt_integral as H1.
rewrite Hit in H1.
specialize (H1 _ _ Hab).
now destruct H1; [ left | right ]; apply eq_ideal_eq.
Qed.

Theorem i_val_rngl_mul_nat : let roi := I_ring_like_op in
  ∀ a i, i_val (rngl_mul_nat a i) = rngl_mul_nat (i_val a) i.
Proof.
intros.
induction i; [ easy | cbn ].
f_equal; apply IHi.
Qed.

Theorem I_characteristic_prop : let roi := I_ring_like_op in
  if rngl_has_1 then
   if rngl_characteristic =? 0 then ∀ i : nat, rngl_mul_nat 1 (S i) ≠ 0%L
   else
     (∀ i : nat, 0 < i < rngl_characteristic → rngl_mul_nat 1 i ≠ 0%L) ∧
     rngl_mul_nat 1 rngl_characteristic = 0%L
  else
   if rngl_characteristic =? 0 then
     ∀ a : ideal P, a ≠ 0%L → ∀ i : nat, rngl_mul_nat a (S i) ≠ 0%L
   else
     ∀ a : ideal P, a ≠ 0%L →
     (∀ i : nat, 0 < i < rngl_characteristic → rngl_mul_nat a i ≠ 0%L) ∧
     rngl_mul_nat a rngl_characteristic = 0%L.
Proof.
intros; cbn.
specialize rngl_characteristic_prop as H1.
progress unfold rngl_has_1; cbn.
progress unfold rngl_has_1 in H1; cbn in H1.
progress unfold rngl_one in H1; cbn in H1.
progress unfold rngl_one; cbn.
remember rngl_opt_one as on eqn:Hon; symmetry in Hon.
destruct on as [one| ]. {
  cbn in H1.
  destruct (Bool.bool_dec _ _) as [H2| H2]; cbn. {
    rewrite if_bool_if_dec in H1 |-*.
    destruct (Sumbool.sumbool_of_bool _) as [Hcz| Hcz]. {
      intros i.
      apply neq_ideal_neq; cbn.
      rewrite i_val_rngl_mul_nat; cbn.
      apply H1.
    }
    destruct H1 as (H1, H3).
    split. {
      intros i Hi.
      apply neq_ideal_neq; cbn.
      rewrite i_val_rngl_mul_nat; cbn.
      now apply H1.
    }
    apply eq_ideal_eq; cbn.
    now rewrite i_val_rngl_mul_nat; cbn.
  }
  rewrite if_bool_if_dec in H1 |-*.
    destruct (Sumbool.sumbool_of_bool _) as [Hcz| Hcz]. {
      intros a Ha *.
      apply neq_ideal_neq; cbn.
      rewrite i_val_rngl_mul_nat; cbn.
...
      apply H1.
    }
    destruct H1 as (H1, H3).
    split. {
      intros i Hi.
      apply neq_ideal_neq; cbn.
      rewrite i_val_rngl_mul_nat; cbn.
      now apply H1.
    }
    apply eq_ideal_eq; cbn.
    now rewrite i_val_rngl_mul_nat; cbn.
...
remember rngl_has_1 as on eqn:Hon.
cbn in H1.
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Hcz| Hcz]. {
...
  intros a Haz i.
  apply Nat.eqb_eq in Hcz.
  rewrite Hcz in H1; cbn in H1.
  apply neq_ideal_neq; cbn.
  apply neq_ideal_neq in Haz; cbn in Haz.
  rewrite i_val_rngl_mul_nat.
  remember rngl_has_1 as on eqn:Hon; symmetry in Hon.
  destruct on; [ | now apply H1 ].
...
*)

Fixpoint List_map {A B} (f : A → B) l :=
  match l with
  | nil => nil
  | (a :: t)%list => (f a :: List_map f t)%list
  end.

Theorem List_map_length : ∀ {A B} (f : A → B) l,
  length (List_map f l) = length l.
Proof.
intros.
induction l as [| a la]; [ easy | cbn ].
now f_equal.
Qed.

Theorem I_opt_le_refl : let roi := I_ring_like_op in
  if rngl_is_ordered then ∀ a : ideal P, (a ≤ a)%L else not_applicable.
Proof.
intros.
specialize rngl_opt_le_refl as H1.
progress unfold rngl_is_ordered in H1.
progress unfold rngl_is_ordered.
progress unfold roi; cbn.
progress unfold rngl_le; cbn.
progress unfold I_opt_le.
progress unfold rngl_le in H1.
destruct rngl_opt_le as [le| ]; [ cbn | easy ].
cbn in H1.
intros.
apply H1.
Qed.

Theorem I_opt_le_antisymm : let roi := I_ring_like_op in
  if rngl_is_ordered then ∀ a b : ideal P, (a ≤ b)%L → (b ≤ a)%L → a = b
  else not_applicable.
Proof.
intros.
specialize rngl_opt_le_antisymm as H1.
progress unfold rngl_is_ordered in H1.
progress unfold rngl_is_ordered.
progress unfold roi; cbn.
progress unfold rngl_le; cbn.
progress unfold I_opt_le.
progress unfold rngl_le in H1.
destruct rngl_opt_le as [le| ]; [ cbn | easy ].
cbn in H1.
intros.
apply eq_ideal_eq.
now apply H1.
Qed.

Theorem I_opt_le_trans : let roi := I_ring_like_op in
  if rngl_is_ordered then ∀ a b c : ideal P, (a ≤ b)%L → (b ≤ c)%L → (a ≤ c)%L
  else not_applicable.
Proof.
intros.
specialize rngl_opt_le_trans as H1.
progress unfold rngl_is_ordered in H1.
progress unfold rngl_is_ordered.
progress unfold roi; cbn.
progress unfold rngl_le; cbn.
progress unfold I_opt_le.
progress unfold rngl_le in H1.
destruct rngl_opt_le as [le| ]; [ cbn | easy ].
cbn in H1.
intros * Hab Hbc.
now apply (H1 _ (i_val b)).
Qed.

Theorem I_opt_add_le_compat : let roi := I_ring_like_op in
  if rngl_is_ordered then
    ∀ a b c d : ideal P, (a ≤ b)%L → (c ≤ d)%L → (a + c ≤ b + d)%L
  else not_applicable.
Proof.
intros.
specialize rngl_opt_add_le_compat as H1.
progress unfold rngl_is_ordered in H1.
progress unfold rngl_is_ordered.
progress unfold roi; cbn.
progress unfold rngl_le; cbn.
progress unfold I_opt_le.
progress unfold rngl_le in H1.
destruct rngl_opt_le as [le| ]; [ cbn | easy ].
cbn in H1.
intros * Hab Hbc.
now apply (H1 _ (i_val b)).
Qed.

Theorem I_opt_mul_le_compat_nonneg : let roi := I_ring_like_op in
  if (rngl_is_ordered && rngl_has_opp)%bool then
    ∀ a b c d : ideal P, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L
  else not_applicable.
Proof.
intros.
specialize rngl_opt_mul_le_compat_nonneg as H1.
progress unfold rngl_is_ordered, rngl_has_opp in H1.
progress unfold rngl_is_ordered, rngl_has_opp.
progress unfold roi; cbn.
progress unfold rngl_le; cbn.
progress unfold I_opt_le.
progress unfold rngl_le in H1.
destruct rngl_opt_le as [le| ]; [ cbn | easy ].
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
destruct os as [opp| subt]; [ | easy ].
cbn in H1 |-*.
intros * Hab Hbc.
now apply H1.
Qed.

Theorem I_opt_mul_le_compat_nonpos : let roi := I_ring_like_op in
  if (rngl_is_ordered && rngl_has_opp)%bool then
    ∀ a b c d : ideal P, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L
  else not_applicable.
Proof.
intros.
specialize rngl_opt_mul_le_compat_nonpos as H1.
progress unfold rngl_is_ordered, rngl_has_opp in H1.
progress unfold rngl_is_ordered, rngl_has_opp.
progress unfold roi; cbn.
progress unfold rngl_le; cbn.
progress unfold I_opt_le.
progress unfold rngl_le in H1.
destruct rngl_opt_le as [le| ]; [ cbn | easy ].
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
destruct os as [opp| subt]; [ | easy ].
cbn in H1 |-*.
intros * Hab Hbc.
now apply H1.
Qed.

Theorem I_opt_mul_le_compat : let roi := I_ring_like_op in
  if (rngl_is_ordered && negb rngl_has_opp)%bool then
    ∀ a b c d : ideal P, (a ≤ c)%L → (b ≤ d)%L → (a * b ≤ c * d)%L
  else not_applicable.
Proof.
intros.
specialize rngl_opt_mul_le_compat as H1.
progress unfold rngl_is_ordered, rngl_has_opp in H1.
progress unfold rngl_is_ordered, rngl_has_opp.
progress unfold roi; cbn.
progress unfold rngl_le; cbn.
progress unfold I_opt_le.
progress unfold rngl_le in H1.
destruct rngl_opt_le as [le| ]; [ cbn | easy ].
destruct rngl_opt_opp_or_subt as [os| ]. {
  destruct os as [opp| subt]; [ easy | ].
  cbn in H1 |-*.
  intros * Hab Hbc.
  now apply H1.
} {
  cbn in H1 |-*.
  intros * Hab Hbc.
  now apply H1.
}
Qed.

Theorem I_opt_not_le : let roi := I_ring_like_op in
  if rngl_is_ordered then ∀ a b : ideal P, ¬ (a ≤ b)%L → a = b ∨ (b ≤ a)%L
  else not_applicable.
Proof.
intros.
specialize rngl_opt_not_le as H1.
progress unfold rngl_is_ordered, rngl_has_opp in H1.
progress unfold rngl_is_ordered, rngl_has_opp.
progress unfold roi; cbn.
progress unfold rngl_le; cbn.
progress unfold I_opt_le.
progress unfold rngl_le in H1.
destruct rngl_opt_le as [le| ]; [ cbn | easy ].
cbn in H1 |-*.
intros * Hab.
specialize (H1 (i_val a) (i_val b) Hab).
destruct H1 as [H1| H1]; [ | now right ].
now apply eq_ideal_eq in H1; left.
Qed.

Definition I_ring_like_prop : ring_like_prop (ideal P) :=
  {| rngl_mul_is_comm := rngl_mul_is_comm;
     rngl_has_dec_le := rngl_has_dec_le;
     rngl_is_integral := rngl_is_integral;
     rngl_is_alg_closed := false;
     rngl_characteristic := rngl_characteristic;
     rngl_add_comm := I_add_comm;
     rngl_add_assoc := I_add_assoc;
     rngl_add_0_l := I_add_0_l;
     rngl_mul_assoc := I_mul_assoc;
     rngl_opt_mul_1_l := I_opt_mul_1_l;
     rngl_mul_add_distr_l := I_mul_add_distr_l;
     rngl_opt_mul_comm := I_opt_mul_comm;
     rngl_opt_mul_1_r := I_opt_mul_1_r;
     rngl_opt_mul_add_distr_r := I_opt_mul_add_distr_r;
     rngl_opt_add_opp_l := I_opt_add_opp_l;
     rngl_opt_add_sub := I_opt_add_sub;
     rngl_opt_sub_add_distr := I_opt_sub_add_distr;
     rngl_opt_mul_inv_l := NA;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_eqb_eq := I_opt_eqb_eq;
     rngl_opt_le_dec := I_opt_le_dec;
     rngl_opt_integral := I_opt_integral;
     rngl_opt_alg_closed := NA;
     rngl_characteristic_prop := I_characteristic_prop;
     rngl_opt_le_refl := I_opt_le_refl;
     rngl_opt_le_antisymm := I_opt_le_antisymm;
     rngl_opt_le_trans := I_opt_le_trans;
     rngl_opt_add_le_compat := I_opt_add_le_compat;
     rngl_opt_mul_le_compat_nonneg := I_opt_mul_le_compat_nonneg;
     rngl_opt_mul_le_compat_nonpos := I_opt_mul_le_compat_nonpos;
     rngl_opt_mul_le_compat := I_opt_mul_le_compat;
     rngl_opt_not_le := I_opt_not_le |}.

End a.
