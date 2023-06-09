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

Definition complex_opt_one : option complex := Some {| re := R1; im := R0 |}.

Definition complex_add (ca cb : complex) : complex :=
  {| re := re ca + re cb; im := im ca + im cb |}.

Definition complex_mul (ca cb : complex) : complex :=
  {| re := (re ca * re cb - im ca * im cb);
     im := (re ca * im cb + im ca * re cb) |}.

Definition complex_opt_opp_or_subt :
  option ((complex → complex) + (complex → complex → complex)) :=
  Some (inl (λ c, mk_c (- re c) (- im c))).

Definition Rsqrt' (a : R) :=
  match Rle_dec R0 a with
  | left Hle => Rsqrt (mknonnegreal a Hle)
  | right _ => R0
  end.

Definition complex_inv (a : complex) :=
  let d := Rsqrt' (re a * re a + im a * im a) in
  mk_c (re a / d) (- im a / d).

Definition complex_opt_inv_or_quot :
  option ((complex → complex) + (complex → complex → complex)) :=
  Some (inl complex_inv).

Definition complex_ring_like_op : ring_like_op (complex) :=
  {| rngl_zero := complex_zero;
     rngl_add := complex_add;
     rngl_mul := complex_mul;
     rngl_opt_one := complex_opt_one;
     rngl_opt_opp_or_subt := complex_opt_opp_or_subt;
     rngl_opt_inv_or_quot := complex_opt_inv_or_quot;
     rngl_opt_eqb := None;
     rngl_opt_le := None |}.

(*
Print Assumptions complex_ring_like_op.
*)

(* to be completed
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
  now destruct (rngl_has_1 T).
}
progress unfold complex_mul.
apply eq_complex_eq; cbn.
specialize (rngl_mul_1_l Hon) as H1.
progress unfold "1"%L in H1; cbn in H1.
progress unfold "1"%L; cbn.
progress unfold complex_opt_one; cbn.
rewrite Hon; cbn.
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
unfold rngl_has_1; cbn.
unfold complex_opt_one; cbn.
(**)
remember (rngl_has_1 T) as on eqn:Hon; symmetry in Hon.
destruct on; [ cbn | easy ].
intros.
apply eq_complex_eq; cbn.
progress unfold "1"%L; cbn.
progress unfold complex_opt_one.
rewrite Hon; cbn.
do 2 rewrite (rngl_mul_1_r Hon).
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
  rngl_has_inv T = true →
  rngl_mul_is_comm T = true →
  ∀ a : complex T, a ≠ 0%L →
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
  let roc := complex_ring_like_op T in
  rngl_has_inv T = true →
  rngl_mul_is_comm T = true →
  ∀ a : complex T, a ≠ 0%L →
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

(* to be completed
Theorem complex_opt_mul_inv_l {T}
  {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op T in
  rngl_has_opp T = true →
  rngl_has_eqb T = true →
  rngl_is_ordered T = true →
  rngl_has_dec_le T = true →
  if (rngl_has_inv (complex T) && rngl_has_1 (complex T))%bool then
    ∀ a : complex T, a ≠ 0%L → (a⁻¹ * a)%L = 1%L
  else not_applicable.
Proof.
intros * Hop Heb Hor Hdl.
clear Heb.
remember (rngl_has_inv (complex T)) as ivc eqn:Hivc; symmetry in Hivc.
destruct ivc; [ | easy ].
remember (rngl_has_1 (complex T)) as onc eqn:Honc; symmetry in Honc.
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
Definition complex_ring_like_prop T
  {ro : ring_like_op T} {rp : ring_like_prop T}
  (Hop : rngl_has_opp T = true) :
  ring_like_prop (complex T) :=
  let Hos := rngl_has_opp_has_opp_or_subt Hop in
  let Hsu := rngl_has_opp_has_no_subt Hop in
  {| rngl_mul_is_comm := rngl_mul_is_comm T;
     rngl_has_dec_le := false;
     rngl_is_integral := rngl_is_integral T;
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
*)
