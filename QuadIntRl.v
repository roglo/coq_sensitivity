(* quadratic integers *)
(* actually, this implementation is not correct: quadratic integers
   are supposed to be of the form a+ωb where
      ω = √d         if d ≡ 2,3 (mod 4)
      ω = (1+√d)/2   if d ≡ 1 (mod 4)
   but here I just implemented the case 1 mod 4 as the other cases,
   all numbers being of the form a+b√d, because I don't understand
   well why there is this difference, between 1 mod 4 and mod others.
     Ok, because they are supposed to be solutions of the equation
   x²+bx+c=0, but 1/ in what this equation is so important 2/ this
   difference between 1 mod 4 and 2,3 mod 4 is ugly (personal
   opinion, but it may change)
*)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 ZArith.
Require Import RingLike.
Open Scope Z_scope.

Record quad_int (d : Z) := mk_qi { qi_re : Z; qi_im : Z }.

Definition qi_zero {d} := mk_qi d 0 0.
Definition qi_one {d} := mk_qi d 1 0.

Definition qi_add {d} (α β : quad_int d) :=
  mk_qi d (qi_re α + qi_re β) (qi_im α + qi_im β).

Definition qi_mul {d} (α β : quad_int d) :=
  mk_qi d (qi_re α * qi_re β + d * qi_im α * qi_im β)
    (qi_re α * qi_im β + qi_im α * qi_re β).

Definition qi_opp d (α : quad_int d) := mk_qi d (- qi_re α) (- qi_im α).

Definition qi_sub d (α β : quad_int d) := qi_add α (qi_opp β).
Definition qi_conj d (α : quad_int d) := mk_qi d (qi_re α) (- qi_im α).

Declare Scope QI_scope.
Delimit Scope QI_scope with QI.

Arguments qi_re [d]%Z q%QI.
Arguments qi_im [d]%Z q%QI.

Notation "0" := qi_zero : QI_scope.
Notation "1" := qi_one : QI_scope.
Notation "- α" := (qi_opp α) : QI_scope.
Notation "α + β" := (qi_add α β) : QI_scope.
Notation "α * β" := (qi_mul α β) : QI_scope.
Notation "α - β" := (qi_sub α β) : QI_scope.
Notation "'〈' a + b √ d 〉" := (mk_qi d a b)
  (at level 1, a at level 35, b at level 35 ,
   format "〈  a  +  b  √ d  〉") : QI_scope.

Definition qi_gauge {d} (α : quad_int d) :=
  Z.abs_nat (qi_re (α * qi_conj α)%QI).

Definition qi_eucl_div {d} (α β : quad_int d) :=
  let den := qi_re (β * qi_conj β)%QI in
  let γ := qi_re (α * qi_conj β)%QI / den in
  let γ' := qi_im (α * qi_conj β)%QI / den in
  let q :=
    if lt_dec (qi_gauge (α - β * mk_qi d γ γ')%QI) (qi_gauge β) then
      mk_qi d γ γ'
    else if lt_dec (qi_gauge (α - β * mk_qi d (γ + 1) γ')%QI) (qi_gauge β) then
      mk_qi d (γ + 1) γ'
    else if lt_dec (qi_gauge (α - β * mk_qi d  γ (γ' + 1))%QI) (qi_gauge β) then
      mk_qi d γ (γ' + 1)
    else if
      lt_dec (qi_gauge (α - β * mk_qi d (γ + 1) (γ' + 1))%QI) (qi_gauge β)
    then
      mk_qi d (γ + 1) (γ' + 1)
    else
      0%QI
  in
  let r := (α - β * q)%QI in
  (q, r).

Definition qi_div d (α β : quad_int d) := fst (qi_eucl_div α β).

Notation "α / β" := (qi_div α β) : QI_scope.

Definition phony_qi_le {d} (a b : quad_int d) := False.

Canonical Structure quad_int_ring_like_op {d} : ring_like_op (quad_int d) :=
  {| rngl_zero := @qi_zero d;
     rngl_one := @qi_one d;
     rngl_add := @qi_add d;
     rngl_mul := @qi_mul d;
     rngl_opt_opp := Some (@qi_opp d);
     rngl_opt_inv := None;
     rngl_opt_monus := None;
     rngl_opt_eucl_div := Some (qi_eucl_div, qi_gauge);
     rngl_le := phony_qi_le |}.

Compute (mk_qi (-1) (- 36) 242 / mk_qi (-1) 50 50)%QI.
Compute (mk_qi (-1) 0 1 * mk_qi (-1) 0 1)%QI.
Compute (1 / mk_qi (-1) 0 1)%QI.
Compute (1 / mk_qi (-1) 0 (- 1))%QI.
Compute (@qi_zero 42 / @qi_zero 42)%QI.

Notation "〈 b √ d 〉" := (mk_qi d 0 b)
  (at level 1, b at level 35, format "〈  b  √ d  〉") : QI_scope.
Notation "〈 √ d 〉" := (mk_qi d 0 1)
  (at level 1, format "〈  √ d  〉") : QI_scope.
Notation "'〈' a + b '𝑖' 〉" := (mk_qi (-1) a b)
  (at level 1, a at level 35, b at level 35 ,
   format "〈  a  +  b  𝑖  〉") : QI_scope.
Notation "'〈' b '𝑖' 〉" := (mk_qi (-1) 0 b)
  (at level 1, b at level 35 ,
   format "〈  b  𝑖  〉") : QI_scope.
Notation "〈 '𝑖' 〉" := (mk_qi (-1) 0 1)
  (at level 1) : QI_scope.

Compute (〈 -36 + 242 √-1 〉 / 〈 50 + 50 √-1 〉)%QI.
Compute (〈 𝑖 〉 * 〈 𝑖 〉)%QI.
Compute (1 / 〈 𝑖 〉)%QI.
Compute (1 / 〈 -1 𝑖 〉)%QI.
Compute (〈 0 √42 〉 / 〈 0 √42 〉 )%QI.
Check (mk_qi (-1) 3 2).
Check (mk_qi (-1) 0 2).
Compute (mk_qi (-1) 1 2 * mk_qi (-1) 1 (-2))%QI.
Compute (mk_qi (-1) 2 3 * mk_qi (-1) 2 (-3))%QI.
Compute (mk_qi (-1) 1 2 * mk_qi (-1) 2 3)%QI.
Compute (mk_qi (-1) 1 2 * mk_qi (-1) 2 (-3))%QI.

Section a.

Context {d : Z}.
Context (ro := @quad_int_ring_like_op d).
Existing Instance ro.

Theorem quad_int_add_comm : ∀ a b, (a + b)%F = (b + a)%F.
Proof.
intros; cbn.
unfold "+"%QI.
now rewrite Z.add_comm, (Z.add_comm (qi_im b)).
Qed.

Theorem quad_int_add_assoc : ∀ a b c : quad_int d,
  (a + (b + c))%F = (a + b + c)%F.
Proof.
intros; cbn.
unfold "+"%QI; cbn.
now do 2 rewrite Z.add_assoc.
Qed.

Theorem quad_int_add_0_l : ∀ a : quad_int d, (0 + a)%F = a.
Proof.
intros; cbn.
unfold "+"%QI; cbn.
now destruct a.
Qed.

Theorem quad_int_mul_assoc : ∀ a b c : quad_int d,
  (a * (b * c))%F = (a * b * c)%F.
Proof.
intros; cbn.
unfold "*"%QI; cbn.
f_equal; ring.
Qed.

Theorem quad_int_mul_1_l : ∀ a : quad_int d, (1 * a)%F = a.
Proof.
intros; cbn.
unfold "*"%QI.
destruct a as (a, a'); cbn.
rewrite Z.mul_0_r, Z.mul_0_l, Z.add_0_r.
now destruct a, a'.
Qed.

Theorem quad_int_mul_add_distr_l : ∀ a b c : quad_int d,
  (a * (b + c))%F = (a * b + a * c)%F.
Proof.
intros; cbn.
unfold "*"%QI, "+"%QI; cbn.
f_equal; ring.
Qed.

Theorem quad_int_neq_1_0 : 1%F ≠ 0%F.
Proof. easy. Qed.

Theorem quad_int_mul_comm : ∀ a b : quad_int d, (a * b)%F = (b * a)%F.
Proof.
intros; cbn.
unfold "*"%QI; cbn.
f_equal; ring.
Qed.

Theorem quad_int_add_opp_l : ∀ a : quad_int d, (- a + a)%F = 0%F.
Proof.
intros; cbn.
unfold qi_opp, "+"%QI, "0"%QI; cbn.
f_equal; ring.
Qed.

Theorem quad_int_eucl_div : ∀ a b q r : quad_int d,
  b ≠ 0%F
  → rngl_eucl_div a b = (q, r)
  → a = (b * q + r)%F ∧ (rngl_gauge r < rngl_gauge b)%nat.
Proof.
intros * Hbz Hab.
cbn in Hab |-*.
unfold qi_eucl_div in Hab.
set (den := qi_re (b * qi_conj b)) in Hab.
set (γ := qi_re (a * qi_conj b) / den) in Hab.
set (γ' := qi_im (a * qi_conj b) / den) in Hab.
destruct (lt_dec (qi_gauge (a - b * 〈 γ + γ' √d 〉)%QI) (qi_gauge b))
  as [H1| H1]. {
  injection Hab; clear Hab; intros Hr Hq.
  subst r.
  rewrite Hq.
...

Canonical Structure quad_int_ring_like_prop : ring_like_prop (quad_int d) :=
  {| rngl_is_comm := true;
     rngl_has_dec_eq := true;
     rngl_has_dec_le := true;
     rngl_has_1_neq_0 := true;
     rngl_is_ordered := true;
     rngl_is_integral := true;
     rngl_characteristic := 0;
     rngl_add_comm := quad_int_add_comm;
     rngl_add_assoc := quad_int_add_assoc;
     rngl_add_0_l := quad_int_add_0_l;
     rngl_mul_assoc := quad_int_mul_assoc;
     rngl_mul_1_l := quad_int_mul_1_l;
     rngl_mul_add_distr_l := quad_int_mul_add_distr_l;
     rngl_opt_1_neq_0 := quad_int_neq_1_0;
     rngl_opt_mul_comm := quad_int_mul_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_l := quad_int_add_opp_l;
     rngl_opt_add_sub_add_sub := NA;
     rngl_opt_sub_sub_sub_add := NA;
     rngl_opt_sub_diag := NA;
     rngl_opt_add_cancel_l := NA;
     rngl_opt_sub_0_l := NA;
     rngl_opt_mul_sub_distr_l := NA;
     rngl_opt_mul_sub_distr_r := NA;
     rngl_opt_mul_inv_l := NA;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_eucl_div_prop := quad_int_eucl_div |}.
     rngl_opt_gauge_prop := ?rngl_opt_gauge_prop;
     rngl_opt_eq_dec := Nat.eq_dec;
     rngl_opt_le_dec := le_dec;
     rngl_opt_integral := Nat_eq_mul_0;
     rngl_characteristic_prop := nat_characteristic_prop;
     rngl_opt_le_refl := Nat.le_refl;
     rngl_opt_le_antisymm := Nat.le_antisymm;
     rngl_opt_le_trans := Nat.le_trans;
     rngl_opt_add_le_compat := Nat.add_le_mono;
     rngl_opt_mul_le_compat_nonneg := NA;
     rngl_opt_mul_le_compat_nonpos := NA;
     rngl_opt_mul_le_compat := Nat_mul_le_compat;
     rngl_opt_not_le := Nat_not_le;
     rngl_consistent := Nat_consistent |}.
