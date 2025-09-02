(* Coq reals as Cauchy sequences *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
From Stdlib Require Import QArith.
Require Import RingLike.Core.

Axiom CReal_appart_or_eq : ∀ x y, (x # y)%CReal + (x = y).

Theorem CReal_appart_irrefl : ∀ x, (x # x)%CReal → False.
Proof.
intros * H1.
now destruct H1 as [H1| H1]; apply CRealLt_irrefl in H1.
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

Theorem CReal_eq_dec : ∀ a b : CReal, {a = b} + {a ≠ b}.
Proof.
intros.
specialize (CReal_appart_or_eq a b) as H1.
destruct H1 as [H1| H1]; [ right | now left ].
intros H; subst b.
now destruct H1 as [H1| H1]; apply CRealLt_irrefl in H1.
Qed.

Definition CReal_inv' (x : CReal) : CReal :=
  match CReal_appart_or_eq x 0%CReal with
  | inl H => CReal_inv x H
  | inr _ => inject_Q 0
  end.

Definition CReal_div (x y : CReal) := (x * CReal_inv' y)%CReal.

Notation "x / y" := (CReal_div x y) : CReal_scope.

Instance CReal_ring_like_op : ring_like_op CReal :=
  {| rngl_zero := 0%CReal;
     rngl_add := CReal_plus;
     rngl_mul := CReal_mult;
     rngl_opt_one := Some 1%CReal;
     rngl_opt_opp_or_psub := Some (inl CReal_opp);
     rngl_opt_inv_or_pdiv := Some (inl CReal_inv');
     rngl_opt_is_zero_divisor := Some (λ _, True); (* to be improved *)
     rngl_opt_eq_dec := Some CReal_eq_dec;
     rngl_opt_leb := None (*Some CRealLe*) |}.

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

Theorem CReal_add_opp_diag_l : let ro := CReal_ring_like_op in
  ∀ a : CReal, (- a + a)%L = 0%L.
Proof.
cbn; intros.
apply eq_CReal_eq.
intros H1.
rewrite CReal_plus_opp_l in H1.
now apply CReal_appart_irrefl in H1.
Qed.

Theorem CReal_mul_inv_diag_l : let ro := CReal_ring_like_op in
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

Theorem CReal_integral :
  ∀ a b : CReal,
  (a * b)%L = 0%L
  → a = 0%L ∨ b = 0%L ∨ rngl_is_zero_divisor a ∨ rngl_is_zero_divisor b.
Proof.
intros * Hab.
now right; right; left.
Qed.

Theorem CReal_characteristic_prop :
  let ro := CReal_ring_like_op in
  ∀ i : nat, rngl_of_nat (S i) ≠ 0%L.
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

Definition CReal_ring_like_prop : ring_like_prop CReal :=
  {| rngl_mul_is_comm := true;
     rngl_is_archimedean := true;
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
     rngl_opt_add_opp_diag_l := CReal_add_opp_diag_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_sub_0_l := NA;
     rngl_opt_mul_inv_diag_l := CReal_mul_inv_diag_l;
     rngl_opt_mul_inv_diag_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_integral := CReal_integral;
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := CReal_characteristic_prop;
     rngl_opt_ord := NA;
     rngl_opt_archimedean := NA |}.

(*
Print Assumptions CReal_ring_like_prop.
*)

(* complex on CReals *)

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
     rngl_opt_opp_or_psub := Some (inl CComplex_opp);
     rngl_opt_inv_or_pdiv := Some (inl CComplex_inv);
     rngl_opt_is_zero_divisor := Some (λ _, True); (* to be improved *)
     rngl_opt_eq_dec := None;
     rngl_opt_leb := None |}.

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
From Stdlib Require Import Utf8 Reals.
Require Import RingLike.Core.

Instance reals_ring_like_op : ring_like_op R :=
  {| rngl_zero := R0;
     rngl_add := Rplus;
     rngl_mul := Rmult;
     rngl_opt_one := Some R1;
     rngl_opt_opp_or_psub := Some (inl Ropp);
     rngl_opt_inv_or_pdiv := Some (inl Rinv);
     rngl_opt_is_zero_divisor := None;
     rngl_opt_eq_dec := None;
     rngl_opt_leb := None (*Some Rle*) |}.

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

Theorem Rintegral :
  ∀ a b : R,
  (a * b)%L = 0%L
  → a = 0%L ∨ b = 0%L ∨ rngl_is_zero_divisor a ∨ rngl_is_zero_divisor b.
Proof.
intros * Hab.
apply Rmult_integral in Hab.
now destruct Hab; [ left | right; left ].
Qed.

Theorem Rcharacteristic_prop :
  let ror := reals_ring_like_op in
  ∀ i : nat, rngl_of_nat (S i) ≠ 0%L.
Proof.
intros.
cbn - [ rngl_mul_nat ].
assert (H : ∀ n, rngl_mul_nat R1 n = INR n). {
  intros.
  progress unfold rngl_mul_nat.
  progress unfold mul_nat; cbn.
  induction n; [ easy | cbn ].
  destruct n; [ apply Rplus_0_r | ].
  rewrite IHn.
  apply Rplus_comm.
}
progress unfold rngl_of_nat.
rewrite H.
now apply not_0_INR.
Qed.

Canonical Structure reals_ring_like_prop : ring_like_prop R :=
  let ro := reals_ring_like_op in
  {| rngl_mul_is_comm := true;
     rngl_is_archimedean := true;
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
     rngl_opt_add_opp_diag_l := Rplus_opp_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_sub_0_l := NA;
     rngl_opt_mul_inv_diag_l := Rinv_l;
     rngl_opt_mul_inv_diag_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_integral := Rintegral;
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := Rcharacteristic_prop;
     rngl_opt_ord := NA;
     rngl_opt_archimedean := NA |}.

(* complex numbers *)
(* see also Quaternions.v *)

(*
Record complex := mk_c {re : R; im : R}.

(*
Arguments rngl_has_dec_le T {ro ring_like_prop}.
Arguments rngl_opt_inv_or_pdiv T {ring_like_op}.
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
     rngl_opt_opp_or_psub := Some (inl complex_opp);
     rngl_opt_inv_or_pdiv := Some (inl complex_inv);
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

Theorem complex_add_opp_diag_l : let roc := complex_ring_like_op in
  ∀ a : complex, (- a + a)%L = 0%L.
Proof.
intros; cbn.
apply eq_complex_eq; cbn.
now do 2 rewrite Rplus_opp_l.
Qed.

(* to be completed
Theorem complex_inv_re {T} {ro : ring_like_op T} {rp : ring_like_prop T} :
  let roc := complex_ring_like_op in
  rngl_has_inv T = true →
  rngl_mul_is_comm T = true →
  ∀ a : complex, a ≠ 0%L →
  re a⁻¹ = (re a / (re a * re a + im a * im a))%L.
Proof.
intros * Hiv Hic * Haz.
assert (Hiq : rngl_has_inv_or_pdiv T = true). {
  now apply rngl_has_inv_or_pdiv_iff; left.
}
progress unfold rngl_inv; cbn.
progress unfold complex_opt_inv_or_pdiv.
progress unfold rngl_has_inv_or_pdiv in Hiq.
progress unfold rngl_div.
rewrite Hiv, Hic.
generalize Hiv; intros H.
progress unfold rngl_has_inv in H.
destruct (rngl_opt_inv_or_pdiv T) as [iq| ]; [ | easy ].
destruct iq as [inv| pdiv]; [ | easy ].
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
progress unfold complex_opt_inv_or_pdiv.
progress unfold rngl_div.
rewrite Hiv, Hic.
generalize Hiv; intros H.
progress unfold rngl_has_inv in H.
destruct (rngl_opt_inv_or_pdiv T) as [iq| ]; [ | easy ].
destruct iq as [inv| pdiv]; [ | easy ].
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
     rngl_opt_add_opp_diag_l := complex_add_opp_diag_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_mul_inv_l := complex_opt_mul_inv_l Hop;
     rngl_opt_mul_inv_r := 42;
     rngl_opt_mul_div := ?rngl_opt_mul_div;
     rngl_opt_mul_pdiv_r := ?rngl_opt_mul_pdiv_r;
     rngl_opt_eqb_eq := ?rngl_opt_eqb_eq;
     rngl_opt_integral := ?rngl_opt_integral;
     rngl_opt_alg_closed := ?rngl_opt_alg_closed;
     rngl_characteristic_prop := ?rngl_characteristic_prop;
     rngl_opt_le_dec := ?rngl_opt_le_dec;
     rngl_opt_le_refl := ?rngl_opt_le_refl;
     rngl_opt_le_antisymm := ?rngl_opt_le_antisymm;
     rngl_opt_le_trans := ?rngl_opt_le_trans;
     rngl_opt_add_le_compat := ?rngl_opt_add_le_compat;
     rngl_opt_mul_le_compat_nonneg := ?rngl_opt_mul_le_compat_nonneg;
     rngl_opt_mul_le_compat_nonpos := ?rngl_opt_mul_le_compat_nonpos;
     rngl_opt_mul_le_compat_non_opp := ?rngl_opt_mul_le_compat;
     rngl_opt_not_le := ?rngl_opt_not_le |}.
*)
*)
