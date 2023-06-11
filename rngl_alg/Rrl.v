(* complex numbers *)
(* see also Quaternions.v *)

Set Nested Proofs Allowed.
Require Import Utf8 Reals.
Require Import Main.RingLike.

Class complex T := mk_c {re : T; im : T}.
Arguments mk_c {T} re%L im%L.
Arguments re {T} complex%L.
Arguments im {T} complex%L.

Arguments rngl_has_eqb T {R}.
Arguments rngl_has_inv T {R}.
Arguments rngl_has_inv_or_quot T {R}.
Arguments rngl_has_opp T {R}.
Arguments rngl_has_opp_or_subt T {R}.
Arguments rngl_has_subt T {R}.
Arguments rngl_has_1 T {ro}.
Arguments rngl_mul_is_comm T {ro ring_like_prop}.
Arguments rngl_opt_inv_or_quot T {ring_like_op}.
Arguments rngl_opt_one T {ring_like_op}.

Theorem eq_complex_eq {T} :
  ∀ a b : complex T, re a = re b ∧ im a = im b ↔ a = b.
Proof.
intros.
split; intros Hab; [ | now subst ].
destruct a, b; cbn in Hab.
now f_equal.
Qed.

Theorem neq_complex_neq {T} {ro : ring_like_op T} {rp : ring_like_prop T} :
  rngl_has_eqb T = true →
  ∀ a b : complex T, re a ≠ re b ∨ im a ≠ im b ↔ a ≠ b.
Proof.
intros * Heb *.
split; intros Hab. {
  intros H; subst b.
  now destruct Hab.
}
destruct a as (ra, ia).
destruct b as (rb, ib); cbn.
destruct (rngl_eq_dec Heb ra rb) as [Hrab| Hrab]. {
  subst rb; right.
  now intros Hiab; apply Hab; clear Hab; subst ib.
} {
  now left.
}
Qed.

Definition complex_zero {T} {ro : ring_like_op T} : complex T :=
  {| re := rngl_zero; im := rngl_zero |}.

Definition complex_opt_one {T} {ro : ring_like_op T} : option (complex T) :=
  match rngl_opt_one T with
  | Some one => Some {| re := one; im := rngl_zero |}
  | None => None
  end.

Definition complex_add {T} {ro : ring_like_op T} (ca cb : complex T) :=
  {| re := re ca + re cb; im := im ca + im cb |}.

Definition complex_mul {T} {ro : ring_like_op T} (ca cb : complex T) :=
  {| re := (re ca * re cb - im ca * im cb)%L;
     im := (re ca * im cb + im ca * re cb)%L |}.

Definition complex_opt_opp_or_subt {T} {ro : ring_like_op T} :
  option ((complex T → complex T) + (complex T → complex T → complex T)) :=
  match rngl_opt_opp_or_subt with
  | Some (inl opp) =>
      Some (inl (λ c, mk_c (opp (re c)) (opp (im c))))
  | Some (inr subt) =>
      Some (inr (λ c d, mk_c (subt (re c) (re d)) (subt (im c) (im d))))
  | None =>
      None
  end.

Definition complex_inv {T} {ro : ring_like_op T} a :=
  let d := (re a * re a + im a * im a)%L in
  mk_c (re a / d) (- im a / d)%L.

Definition rngl_module_zero T {ro : ring_like_op T} :=
  ∀ a b : T, (a * a + b * b = 0 → a = 0 ∧ b = 0)%L.

Definition rngl_module_zero_dec T {ro : ring_like_op T} :=
  {rngl_module_zero T} + {True}.

Definition complex_opt_inv_or_quot {T}
  {ro : ring_like_op T} {rp : ring_like_prop T}
(*
  (rmz : rngl_module_zero_dec T)
*) :
  option ((complex T → complex T) + (complex T → complex T → complex T)) :=
  match rngl_opt_inv_or_quot T with
  | Some (inl inv) =>
      if rngl_mul_is_comm T then
        (*if rmz then*) Some (inl complex_inv) (*else None*)
      else None
  | Some (inr quot) =>
      None (* à voir *)
  | None =>
      None
  end.

Definition complex_opt_eqb {T} {ro : ring_like_op T} :
    option (complex T → complex T → bool) :=
  match rngl_opt_eqb with
  | Some eqb => Some (λ c d, (eqb (re c) (re d) && eqb (im c) (im d))%bool)
  | None => None
  end.

Definition complex_ring_like_op T
  {ro : ring_like_op T} {rp : ring_like_prop T}
(*
  (rmz : rngl_module_zero_dec T)
*)
  :
  ring_like_op (complex T) :=
  {| rngl_zero := complex_zero;
     rngl_add := complex_add;
     rngl_mul := complex_mul;
     rngl_opt_one := complex_opt_one;
     rngl_opt_opp_or_subt := complex_opt_opp_or_subt;
     rngl_opt_inv_or_quot := complex_opt_inv_or_quot (*rmz*);
     rngl_opt_eqb := complex_opt_eqb;
     rngl_opt_le := None |}.

Theorem complex_add_comm {T} {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op T in
  ∀ a b, (a + b)%L = (b + a)%L.
Proof.
intros; cbn.
progress unfold complex_add.
f_equal; apply rngl_add_comm.
Qed.

Theorem complex_add_assoc {T} {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op T in
  ∀ a b c : complex T, (a + (b + c))%L = (a + b + c)%L.
Proof.
intros; cbn.
progress unfold complex_add; cbn.
f_equal; apply rngl_add_assoc.
Qed.

Theorem complex_add_0_l {T} {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op T in
  ∀ a : complex T, (0 + a)%L = a.
Proof.
intros; cbn.
progress unfold complex_add; cbn.
do 2 rewrite rngl_add_0_l.
now apply eq_complex_eq.
Qed.

Theorem complex_mul_assoc {T} {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op T in
  rngl_has_opp T = true →
  ∀ a b c : complex T, (a * (b * c))%L = (a * b * c)%L.
Proof.
intros * Hop *; cbn.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
progress unfold complex_mul; cbn.
do 2 rewrite (rngl_mul_sub_distr_l Hop).
do 2 rewrite (rngl_mul_sub_distr_r Hop).
do 2 rewrite rngl_mul_add_distr_l.
do 2 rewrite rngl_mul_add_distr_r.
do 8 rewrite rngl_mul_assoc.
do 2 rewrite <- (rngl_sub_add_distr Hos).
f_equal. {
  f_equal.
  do 2 rewrite rngl_add_assoc.
  now rewrite rngl_add_comm, rngl_add_assoc.
} {
  unfold rngl_sub; rewrite Hop.
  do 2 rewrite <- rngl_add_assoc.
  f_equal.
  do 2 rewrite rngl_add_assoc.
  rewrite rngl_add_comm.
  now rewrite rngl_add_assoc.
}
Qed.

Theorem complex_opt_mul_1_l {T} {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op T in
  rngl_has_opp_or_subt T = true →
  if rngl_has_1 (complex T) then ∀ a : complex T, (1 * a)%L = a
  else not_applicable.
Proof.
intros * Hos.
remember (rngl_has_1 (complex T)) as onc eqn:Honc; symmetry in Honc.
destruct onc; [ | easy ].
intros; cbn.
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honc; cbn in Honc.
  progress unfold complex_opt_one in Honc.
  progress unfold rngl_has_1.
  now destruct rngl_opt_one.
}
progress unfold complex_mul.
apply eq_complex_eq; cbn.
specialize (rngl_mul_1_l Hon) as H1.
unfold rngl_has_1 in Hon.
progress unfold "1"%L in H1; cbn in H1.
progress unfold "1"%L; cbn.
progress unfold complex_opt_one; cbn.
destruct rngl_opt_one as [one| ]; [ cbn | easy ].
do 2 rewrite H1.
do 2 rewrite (rngl_mul_0_l Hos).
now rewrite (rngl_sub_0_r Hos), rngl_add_0_r.
Qed.

Theorem complex_mul_add_distr_l {T}
  {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op T in
  rngl_has_opp T = true →
  ∀ a b c : complex T, (a * (b + c))%L = (a * b + a * c)%L.
Proof.
intros * Hop *; cbn.
apply eq_complex_eq; cbn.
progress unfold rngl_sub; rewrite Hop.
do 4 rewrite rngl_mul_add_distr_l.
rewrite (rngl_opp_add_distr Hop).
progress unfold rngl_sub; rewrite Hop.
do 4 rewrite <- rngl_add_assoc.
split; f_equal. {
  now rewrite rngl_add_assoc, rngl_add_comm.
} {
  rewrite rngl_add_comm.
  rewrite <- rngl_add_assoc; f_equal.
  apply rngl_add_comm.
}
Qed.

Theorem complex_opt_mul_comm {T}
  {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op T in
  if rngl_mul_is_comm T then ∀ a b : complex T, (a * b)%L = (b * a)%L
  else not_applicable.
Proof.
intros; cbn.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
intros.
apply eq_complex_eq; cbn.
do 2 rewrite (rngl_mul_comm Hic (re b)).
do 2 rewrite (rngl_mul_comm Hic (im b)).
split; [ easy | ].
apply rngl_add_comm.
Qed.

Theorem complex_opt_mul_1_r {T}
  {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op T in
  rngl_has_opp_or_subt T = true →
  if rngl_mul_is_comm T then not_applicable
  else if rngl_has_1 (complex T) then ∀ a : complex T, (a * 1)%L = a
  else not_applicable.
Proof.
intros * Hos.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ easy | ].
remember (rngl_has_1 (complex T)) as onc eqn:Honc; symmetry in Honc.
destruct onc; [ | easy ].
intros.
apply eq_complex_eq; cbn.
progress unfold "1"%L; cbn.
progress unfold complex_opt_one.
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honc; cbn in Honc.
  progress unfold complex_opt_one in Honc.
  progress unfold rngl_has_1.
  now destruct rngl_opt_one.
}
specialize (rngl_mul_1_r Hon) as H1.
unfold rngl_has_1 in Honc.
cbn in Honc.
progress unfold complex_opt_one in Honc.
progress unfold "1"%L in H1.
destruct (rngl_opt_one T) as [one| ]; [ cbn | easy ].
do 2 rewrite H1.
do 2 rewrite (rngl_mul_0_r Hos).
now rewrite (rngl_sub_0_r Hos), rngl_add_0_l.
Qed.

Theorem complex_opt_mul_add_distr_r {T}
  {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op T in
  rngl_has_opp T = true →
  if rngl_mul_is_comm T then not_applicable
  else ∀ a b c : complex T, ((a + b) * c)%L = (a * c + b * c)%L.
Proof.
intros * Hop.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ easy | ].
intros.
apply eq_complex_eq; cbn.
do 4 rewrite rngl_mul_add_distr_r.
progress unfold rngl_sub.
rewrite Hop.
rewrite (rngl_opp_add_distr Hop).
do 4 rewrite <- rngl_add_assoc.
split; f_equal. {
  progress unfold rngl_sub.
  rewrite Hop.
  do 2 rewrite rngl_add_assoc.
  rewrite rngl_add_add_swap; f_equal.
  apply rngl_add_comm.
} {
  rewrite rngl_add_comm.
  rewrite <- rngl_add_assoc; f_equal.
  apply rngl_add_comm.
}
Qed.

Theorem complex_opt_add_opp_l {T}
  {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op T in
  rngl_has_opp T = true →
  if rngl_has_opp (complex T) then ∀ a : complex T, (- a + a)%L = 0%L
  else not_applicable.
Proof.
intros * Hop.
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
remember (rngl_has_opp (complex T)) as opc eqn:Hopc; symmetry in Hopc.
destruct opc; [ | easy ].
intros.
apply eq_complex_eq; cbn.
specialize (rngl_add_opp_l Hop) as H1.
progress unfold rngl_opp; cbn.
progress unfold complex_opt_opp_or_subt; cbn.
progress unfold rngl_has_opp in Hop.
progress unfold rngl_opp in H1.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
destruct os as [opp| subt]; [ cbn | easy ].
now do 2 rewrite H1.
Qed.

Theorem complex_opt_add_sub {T}
  {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op T in
  rngl_has_subt T = false →
  if rngl_has_subt (complex T) then ∀ a b : complex T, (a + b - b)%L = a
  else not_applicable.
Proof.
intros * Hsu.
progress unfold rngl_has_subt; cbn.
progress unfold complex_opt_opp_or_subt.
progress unfold rngl_has_subt in Hsu.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem complex_opt_sub_add_distr {T}
  {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op T in
  rngl_has_subt T = false →
  if rngl_has_subt (complex T) then
    ∀ a b c : complex T, (a - (b + c))%L = (a - b - c)%L
  else not_applicable.
Proof.
intros * Hsu.
progress unfold rngl_has_subt; cbn.
progress unfold complex_opt_opp_or_subt.
progress unfold rngl_has_subt in Hsu.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem complex_inv_re {T} {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op T in
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ a : complex T, a ≠ 0%L →
  re a⁻¹ = (re a / (re a * re a + im a * im a))%L.
Proof.
intros * Hic Hiv * Haz.
assert (Hiq : rngl_has_inv_or_quot T = true). {
  now apply rngl_has_inv_or_quot_iff; left.
}
progress unfold rngl_inv; cbn.
progress unfold complex_opt_inv_or_quot.
progress unfold rngl_has_inv_or_quot in Hiq.
progress unfold rngl_has_inv in Hiv.
rewrite Hic.
destruct (rngl_opt_inv_or_quot T) as [iq| ]; [ now destruct iq | easy ].
Qed.

Theorem complex_inv_im {T} {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op T in
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ a : complex T, a ≠ 0%L →
  im a⁻¹ = (- im a / (re a * re a + im a * im a))%L.
Proof.
intros * Hic Hiv * Haz.
assert (Hiq : rngl_has_inv_or_quot T = true). {
  now apply rngl_has_inv_or_quot_iff; left.
}
progress unfold rngl_inv; cbn.
progress unfold complex_opt_inv_or_quot.
progress unfold rngl_has_inv_or_quot in Hiq.
progress unfold rngl_has_inv in Hiv.
rewrite Hic.
destruct (rngl_opt_inv_or_quot T) as [iq| ]; [ now destruct iq | easy ].
Qed.

(* to be completed
Theorem complex_opt_mul_inv_l {T}
  {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op T in
  rngl_has_opp T = true →
  if (rngl_has_inv (complex T) && rngl_has_1 (complex T))%bool then
    ∀ a : complex T, a ≠ 0%L → (a⁻¹ * a)%L = 1%L
  else not_applicable.
Proof.
intros * Hop.
remember (rngl_has_inv (complex T)) as ivc eqn:Hivc; symmetry in Hivc.
destruct ivc; [ | easy ].
remember (rngl_has_1 (complex T)) as onc eqn:Honc; symmetry in Honc.
destruct onc; [ cbn | easy ].
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honc; cbn in Honc.
  progress unfold complex_opt_one in Honc.
  progress unfold rngl_has_1.
  now destruct rngl_opt_one.
}
assert (Hiv : rngl_has_inv T = true). {
  progress unfold rngl_has_inv in Hivc; cbn in Hivc.
  progress unfold complex_opt_inv_or_quot in Hivc.
  progress unfold rngl_has_inv.
  destruct rngl_opt_inv_or_quot as [iq| ]; [ | easy ].
  now destruct iq.
}
assert (Hic : rngl_mul_is_comm T = true). {
  progress unfold rngl_has_inv in Hivc; cbn in Hivc.
  progress unfold complex_opt_inv_or_quot in Hivc.
  remember (rngl_opt_inv_or_quot T) as iq eqn:Hiq; symmetry in Hiq.
  destruct iq as [inv| quot]; [ | easy ].
  destruct inv; [ | easy ].
  now destruct (rngl_mul_is_comm T).
}
intros * Haz.
apply eq_complex_eq; cbn.
specialize (rngl_mul_inv_l Hon Hiv) as H1.
rewrite (complex_inv_re Hic Hiv); [ | now intros H; subst a ].
rewrite (complex_inv_im Hic Hiv); [ | now intros H; subst a ].
progress unfold rngl_sub.
progress unfold rngl_div.
rewrite Hop, Hiv.
rewrite (rngl_mul_mul_swap Hic (re a)).
do 2 rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_mul_swap Hic (im a)).
rewrite (rngl_opp_involutive Hop).
rewrite <- rngl_mul_add_distr_r.
rewrite (rngl_mul_comm Hic).
split. {
  progress unfold "1"%L; cbn.
  progress unfold complex_opt_one.
  progress unfold rngl_has_1 in Hon.
  unfold "1"%L in H1.
  remember (rngl_opt_one T) as x eqn:Hx; symmetry in Hx.
  destruct x as [one| ]; [ | easy ].
  rewrite H1; [ easy | ].
  intros H2.
Print rngl_module_zero.
...
*)

(* to be completed
Definition complex_ring_like_prop T
  {ro : ring_like_op T} {rp : ring_like_prop T}
  (Hop : rngl_has_opp T = true) :
  ring_like_prop (complex T) :=
  let Hos := rngl_has_opp_has_opp_or_subt Hop in
  let Hsu := rngl_has_opp_has_no_subt Hop in
  {| rngl_mul_is_comm := rngl_mul_is_comm T;
     rngl_has_dec_le := false;
     rngl_is_integral_domain := rngl_is_integral_domain;
     rngl_is_alg_closed := true;
     rngl_characteristic := rngl_characteristic;
     rngl_add_comm := complex_add_comm;
     rngl_add_assoc := complex_add_assoc;
     rngl_add_0_l := complex_add_0_l;
     rngl_mul_assoc := complex_mul_assoc Hop;
     rngl_opt_mul_1_l := complex_opt_mul_1_l Hos;
     rngl_mul_add_distr_l := complex_mul_add_distr_l Hop;
     rngl_opt_mul_comm := complex_opt_mul_comm;
     rngl_opt_mul_1_r := complex_opt_mul_1_r Hos;
     rngl_opt_mul_add_distr_r := complex_opt_mul_add_distr_r Hop;
     rngl_opt_add_opp_l := complex_opt_add_opp_l Hop;
     rngl_opt_add_sub := complex_opt_add_sub Hsu;
     rngl_opt_sub_add_distr := complex_opt_sub_add_distr Hsu;
     rngl_opt_mul_inv_l := complex_opt_mul_inv_l Hop;
     rngl_opt_mul_inv_r := 42;
     rngl_opt_mul_div := ?rngl_opt_mul_div;
     rngl_opt_mul_quot_r := ?rngl_opt_mul_quot_r;
     rngl_opt_eqb_eq := ?rngl_opt_eqb_eq;
     rngl_opt_le_dec := ?rngl_opt_le_dec;
     rngl_opt_integral := ?rngl_opt_integral;
     rngl_opt_alg_closed := ?rngl_opt_alg_closed;
     rngl_characteristic_prop := ?rngl_characteristic_prop;
     rngl_opt_le_refl := ?rngl_opt_le_refl;
     rngl_opt_le_antisymm := ?rngl_opt_le_antisymm;
     rngl_opt_le_trans := ?rngl_opt_le_trans;
     rngl_opt_add_le_compat := ?rngl_opt_add_le_compat;
     rngl_opt_mul_le_compat_nonneg := ?rngl_opt_mul_le_compat_nonneg;
     rngl_opt_mul_le_compat_nonpos := ?rngl_opt_mul_le_compat_nonpos;
     rngl_opt_mul_le_compat := ?rngl_opt_mul_le_compat;
     rngl_opt_not_le := ?rngl_opt_not_le |}.
*)


(* Coq reals as Cauchy sequences *)

Set Nested Proofs Allowed.
Require Import Utf8.
Require Import Reals.Cauchy.ConstructiveCauchyReals.
Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
(*
Require Import Reals.Cauchy.ConstructiveCauchyAbs.
Require Import Reals.Cauchy.ConstructiveRcomplete.
*)
Require Import QArith.
Require Import Main.RingLike.

Axiom CReal_appart_or_eq : ∀ x y, (x # y)%CReal + (x = y).

Definition CReal_eqb x y :=
  match CReal_appart_or_eq x y with
  | inl _ => false
  | inr _ => true
  end.

Theorem CReal_eqb_refl : ∀ x, CReal_eqb x x = true.
Proof.
intros.
unfold CReal_eqb.
destruct (CReal_appart_or_eq x x) as [Hxx| Hxx]; [ exfalso | easy ].
now destruct Hxx; apply (CRealLt_irrefl x).
Qed.

Theorem CReal_appart_irrefl : ∀ x, (x # x)%CReal → False.
Proof.
intros * H1.
now destruct H1 as [H1| H1]; apply CRealLt_irrefl in H1.
Qed.

Theorem CReal_appart_sym : ∀ x y, (x # y)%CReal → (y # x)%CReal.
Proof.
intros * Hxy.
now destruct Hxy; [ right | left ].
Qed.

Theorem eq_CReal_eq : ∀ x y, ((x # y)%CReal → False) ↔ x = y.
Proof.
intros.
split. {
  intros Hxy.
  now destruct (CReal_appart_or_eq x y).
} {
  intros H1; subst y.
  apply CReal_appart_irrefl.
}
Qed.

Definition CReal_inv' (x : CReal) : CReal :=
  match CReal_appart_or_eq x 0%CReal with
  | inl H => CReal_inv x H
  | inr _ => inject_Q 0
  end.

Definition CReal_div (x y : CReal) := (x * CReal_inv' y)%CReal.

Notation "x / y" := (CReal_div x y) : CReal_scope.

Definition CReal_ring_like_op : ring_like_op CReal :=
  {| rngl_zero := 0%CReal;
     rngl_add := CReal_plus;
     rngl_mul := CReal_mult;
     rngl_opt_one := Some 1%CReal;
     rngl_opt_opp_or_subt := Some (inl CReal_opp);
     rngl_opt_inv_or_quot := Some (inl CReal_inv');
     rngl_opt_eqb := Some CReal_eqb;
     rngl_opt_le := Some CRealLe |}.

(*
Print Assumptions CReal_ring_like_op.
*)

Theorem CReal_add_comm : let ro := CReal_ring_like_op in
  ∀ a b : CReal, (a + b)%L = (b + a)%L.
Proof.
intros; cbn.
apply eq_CReal_eq.
intros H1.
rewrite CReal_plus_comm in H1.
now apply CReal_appart_irrefl in H1.
Qed.

Theorem CReal_add_assoc : let ro := CReal_ring_like_op in
  ∀ a b c : CReal, (a + (b + c))%L = (a + b + c)%L.
Proof.
intros; cbn.
apply eq_CReal_eq.
intros H1.
rewrite CReal_plus_assoc in H1.
now apply CReal_appart_irrefl in H1.
Qed.

Theorem CReal_add_0_l : let ro := CReal_ring_like_op in
  ∀ a : CReal, (0 + a)%L = a.
Proof.
intros; cbn.
apply eq_CReal_eq.
intros H1.
rewrite CReal_plus_0_l in H1.
now apply CReal_appart_irrefl in H1.
Qed.

Theorem CReal_mul_assoc : let ro := CReal_ring_like_op in
  ∀ a b c : CReal, (a * (b * c))%L = (a * b * c)%L.
Proof.
intros; cbn.
apply eq_CReal_eq.
intros H1.
rewrite CReal_mult_assoc in H1.
now apply CReal_appart_irrefl in H1.
Qed.

Theorem CReal_mul_1_l : let ro := CReal_ring_like_op in
  ∀ a : CReal, (1 * a)%L = a.
Proof.
cbn; intros.
apply eq_CReal_eq.
intros H1.
rewrite CReal_mult_1_l in H1.
now apply CReal_appart_irrefl in H1.
Qed.

Theorem CReal_mul_add_distr_l : let ro := CReal_ring_like_op in
  ∀ a b c : CReal, (a * (b + c))%L = (a * b + a * c)%L.
Proof.
cbn; intros.
apply eq_CReal_eq.
intros H1.
rewrite CReal_mult_plus_distr_l in H1.
now apply CReal_appart_irrefl in H1.
Qed.

Theorem CReal_mul_comm : let ro := CReal_ring_like_op in
  ∀ a b : CReal, (a * b)%L = (b * a)%L.
Proof.
cbn; intros.
apply eq_CReal_eq.
intros H1.
rewrite CReal_mult_comm in H1.
now apply CReal_appart_irrefl in H1.
Qed.

Theorem CReal_add_opp_l : let ro := CReal_ring_like_op in
  ∀ a : CReal, (- a + a)%L = 0%L.
Proof.
cbn; intros.
apply eq_CReal_eq.
intros H1.
rewrite CReal_plus_opp_l in H1.
now apply CReal_appart_irrefl in H1.
Qed.

Theorem CReal_mul_inv_l : let ro := CReal_ring_like_op in
  ∀ a : CReal, a ≠ 0%L → (a⁻¹ * a)%L = 1%L.
Proof.
cbn; intros * Haz.
apply eq_CReal_eq.
intros H1.
unfold CReal_inv' in H1.
destruct (CReal_appart_or_eq _ _) as [H2| H2]; [ | easy ].
rewrite CReal_inv_l in H1.
now apply CReal_appart_irrefl in H1.
Qed.

Theorem CReal_eqb_eq : ∀ x y, CReal_eqb x y = true ↔ x = y.
Proof.
intros.
split; intros Hxy; [ | subst y; apply CReal_eqb_refl ].
unfold CReal_eqb in Hxy.
now destruct (CReal_appart_or_eq x y).
Qed.

Theorem CReal_le_dec : let ro := CReal_ring_like_op in
  ∀ a b : CReal, {(a ≤ b)%L} + {¬ (a ≤ b)%L}.
Proof.
cbn; intros.
destruct (CReal_appart_or_eq a b) as [Hab| Hab]. {
  destruct Hab as [Hab| Hba]. {
    now left; apply CRealLt_asym.
  } {
    now right.
  }
}
subst b; left.
apply CRealLe_refl.
Qed.

Theorem CReal_characteristic_prop : let ro := CReal_ring_like_op in
  ∀ i : nat, rngl_mul_nat 1 (S i) ≠ 0%L.
Proof.
intros * H1.
apply eq_CReal_eq in H1; [ easy | clear H1 H ].
right.
cbn - [ rngl_mul_nat ].
induction i. {
  rewrite <- CReal_plus_0_l at 1.
  apply CReal_plus_lt_compat_r.
  now apply inject_Q_lt.
}
remember (S i) as si; cbn; subst si.
apply CReal_lt_trans with (y := 1%CReal). {
  now apply inject_Q_lt.
}
apply CReal_plus_lt_compat_l with (x := 1%CReal) in IHi.
now rewrite CReal_plus_0_r in IHi.
Qed.

Theorem CReal_le_antisymm : let ro := CReal_ring_like_op in
  ∀ a b : CReal, (a ≤ b)%L → (b ≤ a)%L → a = b.
Proof.
cbn; intros * Hab Hba.
apply eq_CReal_eq.
intros H1.
now destruct H1.
Qed.

Theorem CReal_mul_le_compat_nonneg : let ro := CReal_ring_like_op in
  ∀ a b c d : CReal, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L.
Proof.
cbn; intros * Hac Hbd.
apply CReal_le_trans with (y := (a * d)%CReal). {
  now apply CReal_mult_le_compat_l.
} {
  apply CReal_mult_le_compat_r; [ | easy ].
  now apply CReal_le_trans with (y := b).
}
Qed.

Theorem CReal_mul_le_compat_nonpos : let ro := CReal_ring_like_op in
  ∀ a b c d : CReal, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L.
Proof.
cbn; intros * Hac Hbd.
rewrite <- CReal_opp_involutive.
rewrite <- (CReal_opp_involutive (c * d)).
rewrite CReal_opp_mult_distr_l.
rewrite CReal_opp_mult_distr_r.
rewrite CReal_opp_mult_distr_l.
rewrite CReal_opp_mult_distr_r.
destruct Hac as (Hca, Haz).
destruct Hbd as (Hdb, Hbz).
apply CReal_opp_ge_le_contravar in Hca, Haz, Hdb, Hbz.
rewrite <- opp_inject_Q in Haz, Hbz.
apply CReal_le_trans with (y := (- a * - d)%CReal). {
  now apply CReal_mult_le_compat_l.
} {
  apply CReal_mult_le_compat_r; [ | easy ].
  now apply CReal_le_trans with (y := (- b)%CReal).
}
Qed.

Theorem CReal_not_le : let ro := CReal_ring_like_op in
  ∀ a b : CReal, ¬ (a ≤ b)%L → a = b ∨ (b ≤ a)%L.
Proof.
cbn; intros * Hab.
destruct (CReal_appart_or_eq a b) as [Haeb| Haeb]; [ | now left ].
right.
now destruct Haeb as [H1| H1]; apply CRealLt_asym in H1.
Qed.

Definition CReal_ring_like_prop : ring_like_prop CReal :=
  {| rngl_mul_is_comm := true;
     rngl_has_dec_le := true;
     rngl_is_integral_domain := false;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := CReal_add_comm;
     rngl_add_assoc := CReal_add_assoc;
     rngl_add_0_l := CReal_add_0_l;
     rngl_mul_assoc := CReal_mul_assoc;
     rngl_opt_mul_1_l := CReal_mul_1_l;
     rngl_mul_add_distr_l := CReal_mul_add_distr_l;
     rngl_opt_mul_comm := CReal_mul_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_l := CReal_add_opp_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_mul_inv_l := CReal_mul_inv_l;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_eqb_eq := CReal_eqb_eq;
     rngl_opt_le_dec := CReal_le_dec;
     rngl_opt_integral := NA;
     rngl_opt_alg_closed := NA;
     rngl_characteristic_prop := CReal_characteristic_prop;
     rngl_opt_le_refl := CRealLe_refl;
     rngl_opt_le_antisymm := CReal_le_antisymm;
     rngl_opt_le_trans := CReal_le_trans;
     rngl_opt_add_le_compat := CReal_plus_le_compat;
     rngl_opt_mul_le_compat_nonneg := CReal_mul_le_compat_nonneg;
     rngl_opt_mul_le_compat_nonpos := CReal_mul_le_compat_nonpos;
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := CReal_not_le |}.

(*
Print Assumptions CReal_ring_like_prop.
*)

(* complex *)

Record CComplex := mk_cc {cre : CReal; cim : CReal}.

Definition CComplex_zero : CComplex := {| cre := 0%CReal; cim := 0%CReal |}.

Definition CComplex_one : CComplex := {| cre := 1%CReal; cim := 0%CReal |}.

Definition CComplex_add (ca cb : CComplex) : CComplex :=
  {| cre := cre ca + cre cb; cim := cim ca + cim cb |}.

Definition CComplex_mul (ca cb : CComplex) : CComplex :=
  {| cre := cre ca * cre cb - cim ca * cim cb;
     cim := cre ca * cim cb + cim ca * cre cb |}.

Definition CComplex_opp c := mk_cc (- cre c) (- cim c).

Definition CComplex_inv c :=
  let d := (cre c * cre c + cim c * cim c)%CReal in
  mk_cc (cre c / d) (- cim c / d).

Definition CComplex_ring_like_op : ring_like_op CComplex :=
  {| rngl_zero := CComplex_zero;
     rngl_add := CComplex_add;
     rngl_mul := CComplex_mul;
     rngl_opt_one := Some CComplex_one;
     rngl_opt_opp_or_subt := Some (inl CComplex_opp);
     rngl_opt_inv_or_quot := Some (inl CComplex_inv);
     rngl_opt_eqb := None;
     rngl_opt_le := None |}.

(* to be completed

Mais, maintenant que je me suis rendu compte que je n'avais pas besoin
de racine carrée, qu'est-ce qui m'empêche de faire des complexes sur
un type T quelconque ? bon, il lui faut un opposé et un inverse, mais
sinon ?

Definition CComplex_ring_like_prop : ring_like_op CComplex :=
  {| rngl_mul_is_comm := true |}.
...
*)

(* Classical Reals defined by axioms *)

Set Nested Proofs Allowed.
Require Import Utf8 Reals.
Require Import Main.RingLike.

Definition reals_ring_like_op : ring_like_op R :=
  {| rngl_zero := R0;
     rngl_add := Rplus;
     rngl_mul := Rmult;
     rngl_opt_one := Some R1;
     rngl_opt_opp_or_subt := Some (inl Ropp);
     rngl_opt_inv_or_quot := Some (inl Rinv);
     rngl_opt_eqb := None;
     rngl_opt_le := Some Rle |}.

(*
Print Assumptions reals_ring_like_op.
*)

Theorem Rminus_plus_distr : ∀ x y z, (x - (y + z) = x - y - z)%R.
Proof.
intros.
unfold Rminus.
rewrite Ropp_plus_distr.
symmetry; apply Rplus_assoc.
Qed.

Theorem Rplus_minus_distr : ∀ x y z, (x + (y - z) = x + y - z)%R.
Proof.
intros.
unfold Rminus.
symmetry; apply Rplus_assoc.
Qed.

Theorem Rmult_mult_swap : ∀ x y z, (x * y * z = x * z * y)%R.
Proof.
intros.
do 2 rewrite Rmult_assoc.
f_equal.
apply Rmult_comm.
Qed.

Theorem Rplus_assoc' : ∀ a b c : R, (a + (b + c))%R = (a + b + c)%R.
Proof. intros; now rewrite Rplus_assoc. Qed.

Theorem Rmult_assoc' : ∀ a b c : R, (a * (b * c))%R = (a * b * c)%R.
Proof. intros; now rewrite Rmult_assoc. Qed.

Theorem Rcharacteristic_prop :
  let ror := reals_ring_like_op in
  ∀ i : nat, rngl_mul_nat 1 (S i) ≠ 0%L.
Proof.
intros.
cbn - [ rngl_mul_nat ].
assert (H : ∀ n, rngl_mul_nat R1 n = INR n). {
  intros.
  induction n; [ easy | cbn ].
  destruct n; [ apply Rplus_0_r | ].
  rewrite IHn.
  apply Rplus_comm.
}
rewrite H.
now apply not_0_INR.
Qed.

Theorem Ropt_mul_le_compat_nonneg :
  let ror := reals_ring_like_op in
  ∀ a b c d : R, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L.
Proof.
intros * Hac Hbd.
now apply Rmult_le_compat.
Qed.

Theorem Ropt_mul_le_compat_nonpos :
  let ror := reals_ring_like_op in
  ∀ a b c d : R, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L.
Proof.
intros * Hca Hdb; cbn.
apply Rle_trans with (r2 := (a * d)%R). {
  now apply Rmult_le_compat_neg_l.
}
rewrite (Rmult_comm a), (Rmult_comm c).
apply Rmult_le_compat_neg_l; [ | easy ].
now apply Rle_trans with (r2 := b).
Qed.

Theorem Ropt_not_le :
  let ror := reals_ring_like_op in
  ∀ a b : R, ¬ (a ≤ b)%L → a = b ∨ (b ≤ a)%L.
Proof.
intros * Hab.
cbn in Hab |-*.
apply Rnot_le_lt in Hab.
specialize (Rle_or_lt b a) as H1.
destruct H1 as [| Hba]; [ now right | left ].
now apply Rlt_asym in Hba.
Qed.

Canonical Structure reals_ring_like_prop : ring_like_prop R :=
  let ro := reals_ring_like_op in
  {| rngl_mul_is_comm := true;
     rngl_has_dec_le := false;
     rngl_is_integral_domain := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := Rplus_comm;
     rngl_add_assoc := Rplus_assoc';
     rngl_add_0_l := Rplus_0_l;
     rngl_mul_assoc := Rmult_assoc';
     rngl_opt_mul_1_l := Rmult_1_l;
     rngl_mul_add_distr_l := Rmult_plus_distr_l;
     rngl_opt_mul_comm := Rmult_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_l := Rplus_opp_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_mul_inv_l := Rinv_l;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_eqb_eq := NA;
     rngl_opt_le_dec := NA;
     rngl_opt_integral := Rmult_integral;
     rngl_opt_alg_closed := NA;
     rngl_characteristic_prop := Rcharacteristic_prop;
     rngl_opt_le_refl := Rle_refl;
     rngl_opt_le_antisymm := Rle_antisym;
     rngl_opt_le_trans := Rle_trans;
     rngl_opt_add_le_compat := Rplus_le_compat;
     rngl_opt_mul_le_compat_nonneg := Ropt_mul_le_compat_nonneg;
     rngl_opt_mul_le_compat_nonpos := Ropt_mul_le_compat_nonpos;
     rngl_opt_mul_le_compat := NA;
     rngl_opt_not_le := Ropt_not_le |}.

(* complex numbers *)
(* see also Quaternions.v *)

(*
Record complex := mk_c {re : R; im : R}.

(*
Arguments rngl_has_dec_le T {ro ring_like_prop}.
Arguments rngl_has_eqb T {R}.
Arguments rngl_has_opp T {R}.
Arguments rngl_has_opp_or_subt T {R}.
Arguments rngl_has_inv T {R}.
Arguments rngl_has_inv_and_1_or_quot T {R}.
Arguments rngl_has_inv_or_quot T {R}.
Arguments rngl_has_subt T {R}.
Arguments rngl_has_1 T {ro}.
Arguments rngl_is_integral T {ro ring_like_prop}.
Arguments rngl_is_ordered T {R}.
Arguments rngl_mul_is_comm T {ro ring_like_prop}.
Arguments rngl_opt_inv_or_quot T {ring_like_op}.
Arguments rngl_opt_one T {ring_like_op}.
*)

Theorem eq_complex_eq :
  ∀ a b : complex, re a = re b ∧ im a = im b ↔ a = b.
Proof.
intros.
split; intros Hab; [ | now subst ].
destruct a, b; cbn in Hab.
now f_equal.
Qed.

Theorem neq_complex_neq :
  ∀ a b : complex, re a ≠ re b ∨ im a ≠ im b ↔ a ≠ b.
Proof.
intros *.
split; intros Hab. {
  intros H; subst b.
  now destruct Hab.
}
destruct a as (ra, ia).
destruct b as (rb, ib); cbn.
destruct (Req_dec ra rb) as [Hr| Hr]; [ | now left ].
right.
intros Hi; apply Hab.
now subst.
Qed.

Definition complex_zero : complex := {| re := R0; im := R0 |}.

Definition complex_one : complex := {| re := R1; im := R0 |}.

Definition complex_add (ca cb : complex) : complex :=
  {| re := re ca + re cb; im := im ca + im cb |}.

Definition complex_mul (ca cb : complex) : complex :=
  {| re := (re ca * re cb - im ca * im cb);
     im := (re ca * im cb + im ca * re cb) |}.

Definition complex_opp c := mk_c (- re c) (- im c).

Definition Rsqrt' (a : R) :=
  match Rle_dec R0 a with
  | left Hle => Rsqrt (mknonnegreal a Hle)
  | right _ => R0
  end.

Definition complex_inv (a : complex) :=
  let d := Rsqrt' (re a * re a + im a * im a) in
  mk_c (re a / d) (- im a / d).

Definition complex_ring_like_op : ring_like_op complex :=
  {| rngl_zero := complex_zero;
     rngl_add := complex_add;
     rngl_mul := complex_mul;
     rngl_opt_one := Some complex_one;
     rngl_opt_opp_or_subt := Some (inl complex_opp);
     rngl_opt_inv_or_quot := Some (inl complex_inv);
     rngl_opt_eqb := None;
     rngl_opt_le := None |}.

(*
Print Assumptions complex_ring_like_op.
*)

Theorem complex_add_comm : let roc := complex_ring_like_op in
  ∀ a b, (a + b)%L = (b + a)%L.
Proof.
intros; cbn.
progress unfold complex_add.
f_equal; apply Rplus_comm.
Qed.

Theorem complex_add_assoc : let roc := complex_ring_like_op in
  ∀ a b c : complex, (a + (b + c))%L = (a + b + c)%L.
Proof.
intros; cbn.
apply eq_complex_eq; cbn.
split; symmetry; apply Rplus_assoc.
Qed.

Theorem complex_add_0_l : let roc := complex_ring_like_op in
  ∀ a : complex, (0 + a)%L = a.
Proof.
intros; cbn.
apply eq_complex_eq; cbn.
split; apply Rplus_0_l.
Qed.

Theorem complex_mul_assoc : let roc := complex_ring_like_op in
  ∀ a b c : complex, (a * (b * c))%L = (a * b * c)%L.
Proof.
intros; cbn.
apply eq_complex_eq; cbn.
do 2 rewrite Rmult_minus_distr_l.
do 2 rewrite Rmult_minus_distr_r.
do 2 rewrite Rmult_plus_distr_l.
do 2 rewrite Rmult_plus_distr_r.
do 8 rewrite <- Rmult_assoc.
rewrite Rplus_comm.
do 2 rewrite Rminus_plus_distr.
split. {
  f_equal.
  rewrite <- Rminus_plus_distr.
  rewrite Rplus_comm.
  apply Rminus_plus_distr.
} {
  progress unfold Rminus.
  do 2 rewrite Rplus_assoc.
  f_equal.
  now rewrite <- Rplus_assoc, Rplus_comm.
}
Qed.

Theorem complex_mul_1_l : let roc := complex_ring_like_op in
  ∀ a : complex, (1 * a)%L = a.
Proof.
intros; cbn.
apply eq_complex_eq; cbn.
do 2 rewrite Rmult_1_l.
do 2 rewrite Rmult_0_l.
now rewrite Rminus_0_r, Rplus_0_r.
Qed.

Theorem complex_mul_add_distr_l : let roc := complex_ring_like_op in
  ∀ a b c : complex, (a * (b + c))%L = (a * b + a * c)%L.
Proof.
intros; cbn.
apply eq_complex_eq; cbn.
do 4 rewrite Rmult_plus_distr_l.
rewrite Rminus_plus_distr.
rewrite Rplus_minus_distr.
split. {
  f_equal.
  progress unfold Rminus.
  do 2 rewrite Rplus_assoc.
  f_equal; apply Rplus_comm.
} {
  do 2 rewrite Rplus_assoc.
  f_equal.
  rewrite Rplus_comm, Rplus_assoc.
  f_equal; apply Rplus_comm.
}
Qed.

Theorem complex_mul_comm : let roc := complex_ring_like_op in
  ∀ a b : complex, (a * b)%L = (b * a)%L.
Proof.
intros; cbn.
apply eq_complex_eq; cbn.
do 2 rewrite (Rmult_comm (re b)).
do 2 rewrite (Rmult_comm (im b)).
now rewrite Rplus_comm.
Qed.

Theorem complex_add_opp_l : let roc := complex_ring_like_op in
  ∀ a : complex, (- a + a)%L = 0%L.
Proof.
intros; cbn.
apply eq_complex_eq; cbn.
now do 2 rewrite Rplus_opp_l.
Qed.

(* to be completed
Theorem complex_mul_inv_l : let roc := complex_ring_like_op in
  ∀ a : complex, a ≠ 0%L → (a⁻¹ * a)%L = 1%L.
Proof.
cbn; intros * Haz.
apply eq_complex_eq; cbn.
unfold Rsqrt'.
remember (_ + _)%R as m eqn:Hm.
destruct (Rle_dec R0 m) as [Hmz| Hmz]. 2: {
  exfalso; apply Hmz; clear Hmz; subst m.
  rewrite <- (Rplus_0_l R0); cbn.
  unfold IZR.
  apply Rplus_le_compat. {
    replace (_ * _)%R with (Rsqr (re a)) by easy.
    apply Rle_0_sqr.
  } {
    replace (_ * _)%R with (Rsqr (im a)) by easy.
    apply Rle_0_sqr.
  }
}
unfold Rdiv.
do 2 rewrite <- Ropp_mult_distr_l.
unfold Rminus.
rewrite Ropp_involutive.
rewrite (Rmult_mult_swap (re a)).
rewrite (Rmult_mult_swap (im a)).
rewrite <- Rmult_plus_distr_r, <- Hm.
(* mais putain, chuis nul, y a pas de racine carrée ! *)
...
do 2 rewrite (Rmult_mult_swap (im a)).

rewrite (Rmult_mult_swap (im a)).
...
Search (Rsqr _ = _ * _)%R.
Search (_ * _ = Rsqr _)%R.
Search (_ ^ _ = _ * _)%R.
Search (_ * _ = _ ^ _)%R.
Search Rsqr.
Print Rsqr.
fold Rsqr.
...
Rle_0_sqr: ∀ r : R, (0 <= r²)%R
Search (_ <= _ * _)%R.
Search (0 <= _ * _)%R.
Search (R0 <= _ * _)%R.
Search (_ * _ <= _ * _)%R.
...
intros * Hop Heb Hor Hdl.
clear Heb.
remember (rngl_has_inv complex) as ivc eqn:Hivc; symmetry in Hivc.
destruct ivc; [ | easy ].
remember (rngl_has_1 complex) as onc eqn:Honc; symmetry in Honc.
destruct onc; [ cbn | easy ].
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honc; cbn in Honc.
  progress unfold complex_opt_one in Honc.
  now destruct (rngl_has_1 T).
}
assert (Hiv : rngl_has_inv T = true). {
  progress unfold rngl_has_inv in Hivc; cbn in Hivc.
  progress unfold complex_opt_inv_or_quot in Hivc.
  progress unfold rngl_has_inv.
  destruct rngl_opt_inv_or_quot as [iq| ]; [ | easy ].
  now destruct iq.
}
assert (Hos : rngl_has_opp_or_subt T = true). {
  now apply rngl_has_opp_or_subt_iff; left.
}
assert (His : rngl_has_inv_and_1_or_quot T = true). {
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
intros * Haz.
apply eq_complex_eq; cbn.
specialize (rngl_mul_inv_l Hon Hiv) as H1.
assert (Hic : rngl_mul_is_comm T = true). {
  progress unfold rngl_has_inv in Hivc; cbn in Hivc.
  progress unfold complex_opt_inv_or_quot in Hivc.
  progress unfold rngl_has_inv_and_1_or_quot in His.
  rewrite Hon in His.
  destruct (rngl_opt_inv_or_quot T) as [iq| ]; [ | easy ].
  destruct iq as [inv| quot]; [ | easy ].
  now destruct (rngl_mul_is_comm T).
}
rewrite (complex_inv_re Hiv Hic); [ | easy ].
rewrite (complex_inv_im Hiv Hic); [ | easy ].
unfold rngl_div.
rewrite Hiv.
do 2 rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_mul_swap Hic (re a)).
rewrite (rngl_mul_mul_swap Hic (im a)).
progress unfold rngl_sub.
rewrite Hop.
rewrite (rngl_opp_involutive Hop).
rewrite <- rngl_mul_add_distr_r.
rewrite (rngl_mul_comm Hic).
split. {
  progress unfold "1"%L; cbn.
  progress unfold complex_opt_one.
  rewrite Hon; cbn.
  apply H1.
  intros Hri.
  apply (eq_rngl_add_square_0 Hop Hor Hdl) in Hri. 2: {
(**)
(* Si un anneau a un inverse, c'est un corps, il est forcément
   intègre, non ? *)
Theorem glop : ∀ T {ro : ring_like_op T} {rp : ring_like_prop T},
  rngl_has_inv T = true → rngl_is_integral T = true.
Proof.
intros * Hiv.
Search rngl_is_integral.
...
rewrite His; cbn.
...
    apply Bool.orb_true_iff; right.
    now rewrite His, Heb.
  }
  destruct Hri as (Hra, Hia); apply Haz.
  apply eq_complex_eq.
  now rewrite Hra, Hia.
}
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_comm Hic).
rewrite (rngl_mul_mul_swap Hic).
rewrite rngl_mul_assoc.
rewrite (fold_rngl_sub Hop).
rewrite (rngl_sub_diag Hos).
progress unfold "1"%L.
progress unfold "0"%L.
progress unfold rngl_has_1 in Hon.
remember (rngl_opt_one T) as on eqn:H2; symmetry in H2.
destruct on as [one| ]; [ cbn | easy ].
progress unfold complex_opt_one.
progress unfold rngl_has_1.
rewrite H2; cbn.
progress unfold "1"%L.
now rewrite H2.
Qed.
*)

(* to be completed
Theorem complex_opt_add_sub {T}
  {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op in
  rngl_has_subt T = false →
  if rngl_has_subt complex then ∀ a b : complex, (a + b - b)%L = a
  else not_applicable.
Proof.
intros * Hsu.
progress unfold rngl_has_subt; cbn.
progress unfold complex_opt_opp_or_subt.
progress unfold rngl_has_subt in Hsu.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem complex_opt_sub_add_distr {T}
  {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op in
  rngl_has_subt T = false →
  if rngl_has_subt complex then
    ∀ a b c : complex, (a - (b + c))%L = (a - b - c)%L
  else not_applicable.
Proof.
intros * Hsu.
progress unfold rngl_has_subt; cbn.
progress unfold complex_opt_opp_or_subt.
progress unfold rngl_has_subt in Hsu.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem complex_inv_re {T} {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op in
  rngl_has_inv T = true →
  rngl_mul_is_comm T = true →
  ∀ a : complex, a ≠ 0%L →
  re a⁻¹ = (re a / (re a * re a + im a * im a))%L.
Proof.
intros * Hiv Hic * Haz.
assert (Hiq : rngl_has_inv_or_quot T = true). {
  now apply rngl_has_inv_or_quot_iff; left.
}
progress unfold rngl_inv; cbn.
progress unfold complex_opt_inv_or_quot.
progress unfold rngl_has_inv_or_quot in Hiq.
progress unfold rngl_div.
rewrite Hiv, Hic.
generalize Hiv; intros H.
progress unfold rngl_has_inv in H.
destruct (rngl_opt_inv_or_quot T) as [iq| ]; [ | easy ].
destruct iq as [inv| quot]; [ | easy ].
symmetry; apply (fold_rngl_div Hiv).
Qed.

Theorem complex_inv_im {T} {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op in
  rngl_has_inv T = true →
  rngl_mul_is_comm T = true →
  ∀ a : complex, a ≠ 0%L →
  im a⁻¹ = ((- im a)/(re a * re a + im a * im a))%L.
Proof.
intros * Hiv Hic * Haz.
progress unfold rngl_inv; cbn.
progress unfold complex_opt_inv_or_quot.
progress unfold rngl_div.
rewrite Hiv, Hic.
generalize Hiv; intros H.
progress unfold rngl_has_inv in H.
destruct (rngl_opt_inv_or_quot T) as [iq| ]; [ | easy ].
destruct iq as [inv| quot]; [ | easy ].
symmetry; apply (fold_rngl_div Hiv).
Qed.
*)

(* to be completed
Definition complex_ring_like_prop : ring_like_prop complex :=
  {| rngl_mul_is_comm := true;
     rngl_has_dec_le := false;
     rngl_is_integral_domain := false;
     rngl_is_alg_closed := true;
     rngl_characteristic := rngl_characteristic;
     rngl_add_comm := complex_add_comm;
     rngl_add_assoc := complex_add_assoc;
     rngl_add_0_l := complex_add_0_l;
     rngl_mul_assoc := complex_mul_assoc;
     rngl_opt_mul_1_l := complex_mul_1_l;
     rngl_mul_add_distr_l := complex_mul_add_distr_l;
     rngl_opt_mul_comm := complex_mul_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_l := complex_add_opp_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_mul_inv_l := complex_opt_mul_inv_l Hop;
     rngl_opt_mul_inv_r := 42;
     rngl_opt_mul_div := ?rngl_opt_mul_div;
     rngl_opt_mul_quot_r := ?rngl_opt_mul_quot_r;
     rngl_opt_eqb_eq := ?rngl_opt_eqb_eq;
     rngl_opt_le_dec := ?rngl_opt_le_dec;
     rngl_opt_integral := ?rngl_opt_integral;
     rngl_opt_alg_closed := ?rngl_opt_alg_closed;
     rngl_characteristic_prop := ?rngl_characteristic_prop;
     rngl_opt_le_refl := ?rngl_opt_le_refl;
     rngl_opt_le_antisymm := ?rngl_opt_le_antisymm;
     rngl_opt_le_trans := ?rngl_opt_le_trans;
     rngl_opt_add_le_compat := ?rngl_opt_add_le_compat;
     rngl_opt_mul_le_compat_nonneg := ?rngl_opt_mul_le_compat_nonneg;
     rngl_opt_mul_le_compat_nonpos := ?rngl_opt_mul_le_compat_nonpos;
     rngl_opt_mul_le_compat := ?rngl_opt_mul_le_compat;
     rngl_opt_not_le := ?rngl_opt_not_le |}.
*)
*)
