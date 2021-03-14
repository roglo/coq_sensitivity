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
Import List List.ListNotations.

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
Notation "'〈' a + b '√' d 〉" := (mk_qi d a b)
  (at level 1, a at level 35, b at level 35,
   format "〈  a  +  b  √ d  〉") : QI_scope.

Notation "〈 b √ d 〉" := (mk_qi d 0 b)
  (at level 1, b at level 35, format "〈  b  √ d  〉") : QI_scope.
Notation "〈 √ d 〉" := (mk_qi d 0 1)
  (at level 1, format "〈  √ d  〉") : QI_scope.
Notation "'〈' a + b '𝑖' 〉" := (mk_qi (-1) a b)
  (at level 1, a at level 35, b at level 35,
   format "〈  a  +  b  𝑖  〉") : QI_scope.
Notation "'〈' a - b '𝑖' 〉" := (mk_qi (-1) a (Zneg b))
  (at level 1, a at level 35, b at level 35,
   format "〈  a  -  b  𝑖  〉") : QI_scope.
Notation "'〈' b '𝑖' 〉" := (mk_qi (-1) 0 b)
  (at level 1, b at level 35, format "〈  b  𝑖  〉") : QI_scope.
Notation "'〈' a 〉" := (mk_qi (-1) a 0)
  (at level 1, format "〈  a  〉", a at level 35) : QI_scope.
Notation "'〈' 0 〉" := (mk_qi (-1) 0 0)
  (at level 1, format "〈  0  〉") : QI_scope.
Notation "〈 - '𝑖' 〉" := (mk_qi (-1) 0 (-1))
  (at level 1) : QI_scope.
Notation "〈 '𝑖' 〉" := (mk_qi (-1) 0 1)
  (at level 1) : QI_scope.

Definition qi_gauge {d} (α : quad_int d) :=
  Z.abs_nat (qi_re (α * qi_conj α)%QI).

Definition old_qi_eucl_quo_list {d} (α β : quad_int d) :=
  let den := qi_re (β * qi_conj β)%QI in
  let γ := qi_re (α * qi_conj β)%QI / den in
  let γ' := qi_im (α * qi_conj β)%QI / den in
  let ql := [] in
  let ql1 :=
    if lt_dec (qi_gauge (α - β * mk_qi d γ γ')%QI) (qi_gauge β) then
      mk_qi d γ γ' :: ql
    else ql
  in
  let ql2 :=
    if lt_dec (qi_gauge (α - β * mk_qi d (γ + 1) γ')%QI) (qi_gauge β) then
      mk_qi d (γ + 1) γ' :: ql1
    else ql1
  in
  let ql3 :=
      if lt_dec (qi_gauge (α - β * mk_qi d  γ (γ' + 1))%QI) (qi_gauge β) then
        mk_qi d γ (γ' + 1) :: ql2
      else ql2
  in
  let ql4 :=
      if lt_dec (qi_gauge (α - β * mk_qi d (γ + 1) (γ' + 1))%QI) (qi_gauge β)
      then
        mk_qi d (γ + 1) (γ' + 1) :: ql3
      else ql3
  in
  ql4.

Definition old_qi_eucl_div {d} (α β : quad_int d) :=
  map (λ q, (q, (α - β * q)%QI)) (old_qi_eucl_quo_list α β).

Compute (Z.div_eucl 23 4).
Compute (Z.div_eucl (-23) 4).
Compute (Z.div_eucl 23 (-4)).
Compute (Z.div_eucl (-23) (-4)).

(*
Definition Z_div_eucl' a b :=
  if Z_lt_dec b 0 then
    let '(q, r) := Z.div_eucl a b in
    (q + 1, r - b)
  else Z.div_eucl a b.

Compute (Z_div_eucl' 23 4).
Compute (Z_div_eucl' (-23) 4).
Compute (Z_div_eucl' 23 (-4)).
Compute (Z_div_eucl' (-23) (-4)).
*)

Definition qi_eucl_div {d} (a b : quad_int d) :=
  let bb := qi_re (b * qi_conj b)%QI in
  let '(γ₁, r₁) := Z.div_eucl (qi_re (a * qi_conj b)) bb in
  let '(γ'₁, r'₁) := Z.div_eucl (qi_im (a * qi_conj b)) bb in
  let γ := if Z_le_dec (2 * r₁) bb then γ₁ else γ₁ + 1 in
  let γ' := if Z_le_dec (2 * r'₁) bb then γ'₁ else γ'₁ + 1 in
  let q := mk_qi d γ γ' in
  let r := (a - b * q)%QI in
  (q, r).

Definition qi_div d (α β : quad_int d) := fst (qi_eucl_div α β).

Notation "α / β" := (qi_div α β) : QI_scope.

Compute (qi_eucl_div (mk_qi (-1) (- 36) 242) (mk_qi (-1) 50 50)).
Compute (old_qi_eucl_div (mk_qi (-1) (- 36) 242) (mk_qi (-1) 50 50)).
Compute (qi_eucl_div (mk_qi (-1) 36 242) (mk_qi (-1) 50 50)).
Compute (old_qi_eucl_div (mk_qi (-1) 36 242) (mk_qi (-1) 50 50)).
Compute (mk_qi (-1) 0 1 * mk_qi (-1) 0 1)%QI.
Check qi_eucl_div 1%QI (mk_qi (-1) 0 1).
Compute (qi_eucl_div 1%QI (mk_qi (-1) 0 1)).
Compute (old_qi_eucl_div 1%QI (mk_qi (-1) 0 1)).
Compute (1 / mk_qi (-1) 0 1)%QI.
Compute (1 / mk_qi (-1) 0 (- 1))%QI.
Compute (@qi_zero 42 / @qi_zero 42)%QI.
Check (mk_qi (-1) 0 3).
Check (mk_qi (-1) 0 0).
Check (mk_qi (-1) 2 (-3)).

Definition phony_qi_le {d} (a b : quad_int d) := False.

Definition having_eucl_div :=
  [-11; -7; -3; -2; -1; 2; 3; 5; 6; 7; 11; 13; 17; 19; 21;
   29; 33; 37; 41; 57; 73].

Definition quad_int_ring_like_op {d} : ring_like_op (quad_int d) :=
  {| rngl_zero := @qi_zero d;
     rngl_one := @qi_one d;
     rngl_add := @qi_add d;
     rngl_mul := @qi_mul d;
     rngl_opt_opp := Some (@qi_opp d);
     rngl_opt_inv := None;
     rngl_opt_sous := None;
     rngl_opt_eucl_div :=
       if In_dec Z.eq_dec d having_eucl_div then Some (qi_eucl_div, qi_gauge)
       else None;
     rngl_le := phony_qi_le |}.

Compute (mk_qi (-1) (- 36) 242 / mk_qi (-1) 50 50)%QI.
Compute (mk_qi (-1) 0 1 * mk_qi (-1) 0 1)%QI.
Compute (1 / mk_qi (-1) 0 1)%QI.
Compute (1 / mk_qi (-1) 0 (- 1))%QI.
Compute (@qi_zero 42 / @qi_zero 42)%QI.

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

Theorem quad_int_add_comm : ∀ a b : quad_int d, (a + b)%QI = (b + a)%QI.
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

Theorem quad_int_add_sub_assoc: ∀ a b c : quad_int d,
  (a + (b - c))%QI = (a + b - c)%QI.
Proof.
intros.
unfold qi_sub, qi_opp, qi_add; cbn.
f_equal; ring.
Qed.

Theorem quad_int_add_sub : ∀ a b : quad_int d, (a + b - b = a)%QI.
Proof.
intros.
unfold qi_sub, qi_opp, qi_add; cbn.
destruct a as (a, a'); cbn.
f_equal; ring.
Qed.

Theorem quad_int_mul_0_r : ∀ a : quad_int d, (a * 0 = 0)%QI.
Proof.
intros.
unfold "*"%QI, "0"%QI; cbn.
f_equal; ring.
Qed.

Theorem quad_int_sub_0_r : ∀ a : quad_int d, (a - 0 = a)%QI.
Proof.
intros.
unfold qi_sub, "+"%QI, qi_opp; cbn.
do 2 rewrite Z.add_0_r.
now destruct a.
Qed.

Theorem quad_int_eucl_div :
  if rngl_has_eucl_div then
    ∀ a b q r : quad_int d,
    b ≠ 0%F
    → rngl_eucl_div a b = (q, r)
    → a = (b * q + r)%F ∧ (rngl_gauge r < rngl_gauge b)%nat
  else not_applicable.
Proof.
intros.
unfold rngl_has_eucl_div, rngl_eucl_div, rngl_gauge.
cbn - [ In_dec ].
destruct (in_dec Z.eq_dec d having_eucl_div) as [Hhed| Hhed]; [ cbn | easy ].
intros * Hbz Hab.
unfold qi_eucl_div in Hab.
...
set (den := qi_re (b * qi_conj b)) in Hab.
set (γ := qi_re (a * qi_conj b) / den) in Hab.
set (γ' := qi_im (a * qi_conj b) / den) in Hab.
destruct (lt_dec (qi_gauge (a - b * 〈 γ + γ' √d 〉)%QI) (qi_gauge b))
  as [H1| H1]. {
  injection Hab; clear Hab; intros Hr Hq.
  subst r q.
  split; [ | easy ].
  rewrite quad_int_add_sub_assoc.
  rewrite quad_int_add_comm.
  symmetry; apply quad_int_add_sub.
}
destruct (lt_dec (qi_gauge (a - b * 〈 (γ + 1) + γ' √d 〉)%QI) (qi_gauge b))
  as [H2| H2]. {
  injection Hab; clear Hab; intros Hr Hq.
  subst r q.
  split; [ | easy ].
  rewrite quad_int_add_sub_assoc.
  rewrite quad_int_add_comm.
  symmetry; apply quad_int_add_sub.
}
destruct (lt_dec (qi_gauge (a - b * 〈 γ + (γ' + 1) √d 〉)%QI) (qi_gauge b))
  as [H3| H3]. {
  injection Hab; clear Hab; intros Hr Hq.
  subst r q.
  split; [ | easy ].
  rewrite quad_int_add_sub_assoc.
  rewrite quad_int_add_comm.
  symmetry; apply quad_int_add_sub.
}
destruct (lt_dec (qi_gauge (a - b * 〈 (γ + 1) + (γ' + 1) √d 〉)%QI) (qi_gauge b))
  as [H4| H4]. {
  injection Hab; clear Hab; intros Hr Hq.
  subst r q.
  split; [ | easy ].
  rewrite quad_int_add_sub_assoc.
  rewrite quad_int_add_comm.
  symmetry; apply quad_int_add_sub.
}
(**)
injection Hab; clear Hab; intros Hr Hq.
subst r q.
split. {
  rewrite quad_int_add_sub_assoc.
  rewrite quad_int_add_comm.
  symmetry; apply quad_int_add_sub.
}
rewrite quad_int_mul_0_r.
rewrite quad_int_sub_0_r.
(*
exfalso; clear q r Hab.
*)
apply Nat.nlt_ge in H1.
apply Nat.nlt_ge in H2.
apply Nat.nlt_ge in H3.
apply Nat.nlt_ge in H4.
unfold having_eucl_div in Hhed.
destruct (Z.eq_dec d (-1)) as [Hd1| Hd1]. {
  subst d; clear Hhed.
  move ro at top; move a after b; move γ after γ'.
  move H1 after H4; move H2 after H4; move H3 after H4.
  move Hbz before b.
Print qi_gauge.
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
