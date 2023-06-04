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
     rngl_is_integral := true;
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

(* experiment, to make, perhaps, an implementation of algebraic numbers
   where a first step is to generate all monic polynomials with values
   in ℕ; since monic, it is not required to append the coefficient 1 to
   the list representing the polynomial, so we have to generate all
   lists of nat *)

Require Import Arith.
Import List List.ListNotations.
Require Import Main.Misc Main.IterAdd Main.NatRingLike.

(* I don't know how to call that; I temporarily call it "step". It is
   a number associated with a list; the next list must have a "step"
   whose value is nat successor (next of a step 42 must have a step 43 *)
Definition step l :=
  let ron := nat_ring_like_op in
  length l + ∑ (i = 1, length l), l.(i).

(* I implemented that some years ago (hott.v in my reals) *)

Fixpoint nat_of_list_nat l :=
  match l with
  | [] => 0
  | a :: l => 2 ^ a * (2 * nat_of_list_nat l + 1)
  end.

Fixpoint how_many_times_div_by_2_aux iter n :=
  match iter with
  | 0 => 0
  | S i =>
      match n with
      | 0 => 0
      | S m =>
          if Nat.even n then
            1 + how_many_times_div_by_2_aux i (Nat.div2 n)
          else 0
      end
  end.

Definition how_many_times_div_by_2 n := how_many_times_div_by_2_aux n n.

Fixpoint odd_part_of_nat_aux it n :=
  match it with
  | 0 => 42
  | S it' =>
      match n with
      | 0 => 0
      | S m =>
          if Nat.even n then odd_part_of_nat_aux it' (Nat.div2 n)
          else n
      end
  end.

Definition odd_part_of_nat n := odd_part_of_nat_aux n n.

Fixpoint list_nat_of_nat_aux it n :=
  match it with
  | 0 => [42]
  | S it' =>
      if n =? 0 then []
      else
        how_many_times_div_by_2 n ::
        list_nat_of_nat_aux it' (Nat.div2 (odd_part_of_nat n))
  end.

Definition list_nat_of_nat n := list_nat_of_nat_aux (n + 1) n.

Require Import ZArith.

Definition Z_of_nat n :=
  if Nat.odd n then (- Z.of_nat (Nat.div2 (n + 1)))%Z
  else Z.of_nat (Nat.div2 (n + 1)).
Definition list_Z_of_nat n := map Z_of_nat (list_nat_of_nat n).

(*
Compute (list_nat_of_nat 2023).
Compute (nat_of_list_nat [0; 0; 0; 2; 0; 0; 0; 0; 0]%nat).
Compute (map list_nat_of_nat (seq 0 100)).
Open Scope Z_scope.
Compute (map Z_of_nat (seq 0 10)).
Compute (map list_Z_of_nat (seq 0 100)).
Close Scope Z_scope.
Compute (map (λ l, (l, step l, nat_of_list_nat l)) (map list_nat_of_nat (seq 0 100))).
Compute (nat_of_list_nat [6]).
...
Compute (nat_of_list_Z [6]).
*)

(* complex numbers *)
(* see also Quaternions.v *)
(* since it does not depend on real numbers, this code
   could reside elsewhere *)

Class complex T := mk_c {re : T; im : T}.
Arguments mk_c {T} re%L im%L.
Arguments re {T} complex%L.
Arguments im {T} complex%L.

Arguments rngl_has_opp T {R}.
Arguments rngl_has_opp_or_subt T {R}.
Arguments rngl_has_subt T {R}.
Arguments rngl_has_1 T {ro}.
Arguments rngl_mul_is_comm T {ro ring_like_prop}.
Arguments rngl_opt_one T {ring_like_op}.

Theorem eq_complex_eq {T} :
  ∀ a b : complex T, re a = re b ∧ im a = im b ↔ a = b.
Proof.
intros.
split; intros Hab; [ | now subst ].
destruct a, b; cbn in Hab.
now f_equal.
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

Definition complex_opt_inv_or_quot {T} {ro : ring_like_op T} :
    option ((complex T → complex T) + (complex T → complex T → complex T)) :=
  match rngl_opt_inv_or_quot with
  | Some (inl inv) => None (* à voir *)
  | Some (inr quot) => None (* à voir *)
  | None => None
  end.

Definition complex_opt_eqb {T} {ro : ring_like_op T} :
    option (complex T → complex T → bool) :=
  match rngl_opt_eqb with
  | Some eqb => Some (λ c d, (eqb (re c) (re d) && eqb (im c) (im d))%bool)
  | None => None
  end.

Definition complex_ring_like_op T {ro : ring_like_op T} :
    ring_like_op (complex T) :=
  {| rngl_zero := complex_zero;
     rngl_add := complex_add;
     rngl_mul := complex_mul;
     rngl_opt_one := complex_opt_one;
     rngl_opt_opp_or_subt := complex_opt_opp_or_subt;
     rngl_opt_inv_or_quot := complex_opt_inv_or_quot;
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

(* to be completed *)
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

(* to be completed
Definition complex_ring_like_prop T
  {ro : ring_like_op T} {rp : ring_like_prop T}
  (Hop : rngl_has_opp T = true) :
  ring_like_prop (complex T) :=
  let Hos := rngl_has_opp_has_opp_or_subt Hop in
  let Hsu := rngl_has_opp_has_no_subt Hop in
  {| rngl_mul_is_comm := rngl_mul_is_comm T;
     rngl_has_dec_le := false;
     rngl_is_integral := rngl_is_integral;
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
     rngl_opt_sub_add_distr := 42;
     rngl_opt_mul_inv_l := ?rngl_opt_mul_inv_l;
     rngl_opt_mul_inv_r := ?rngl_opt_mul_inv_r;
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
