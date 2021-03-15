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

(*
Fixpoint squ_fr_loop it n d (same : bool) :=
  match it with
  | O => false
  | S it' =>
      if lt_dec n d then true
      else if Nat.eq_dec (n mod d) 0 then
        if same then false
        else squ_fr_loop it' (n / d)%nat d true
      else squ_fr_loop it' n (S d) false
  end.

Definition nat_square_free n := squ_fr_loop n n 2 false.

Definition square_free z := nat_square_free (Z.abs_nat z).

Compute filter square_free (map (λ n, Z.of_nat n -  60) (seq 1 120)).
Close Scope Z_scope.
Compute filter nat_square_free (seq 1 120).
*)

Fixpoint nat_is_square_loop it n d :=
  match it with
  | O => false
  | S it' =>
      match Nat.compare (d * d) n with
      | Eq => true
      | Gt => false
      | Lt => nat_is_square_loop it' n (S d)
      end
  end.

Definition nat_is_square n := nat_is_square_loop (S n) n 0.

(*
Close Scope Z_scope.
Compute filter nat_is_square (seq 0 120).
*)

Definition is_square z := nat_is_square (Z.abs_nat z).

Open Scope nat_scope.
Theorem nat_not_square_not_mul_square_gen : ∀ it a b c d,
  (S b = it + d)%nat
  → nat_is_square_loop it b d = false
  → (a * a)%nat = (b * c * c)%nat
  → a = 0%nat ∧ c = 0%nat.
Proof.
clear d ro.
intros * Hit Hsq Habc.
destruct (Nat.eq_dec (Nat.gcd a c) 0) as [Hgz| Hgz]. {
  now apply Nat.gcd_eq_0 in Hgz.
}
apply (f_equal (λ x, Nat.div x (Nat.gcd a c))) in Habc.
rewrite Nat.divide_div_mul_exact in Habc; [ | easy | ]. 2: {
  apply Nat.gcd_divide_l.
}
rewrite Nat.divide_div_mul_exact in Habc; [ | easy | ]. 2: {
  apply Nat.gcd_divide_r.
}
remember (a / Nat.gcd a c) as a' eqn:Ha'.
remember (c / Nat.gcd a c) as c' eqn:Hc'.
move c' before a'.
rewrite (Nat.mul_comm a) in Habc.
rewrite Nat.mul_shuffle0 in Habc.
apply (f_equal (λ x, Nat.div x (Nat.gcd a c))) in Habc.
rewrite Nat.divide_div_mul_exact in Habc; [ | easy | ]. 2: {
  apply Nat.gcd_divide_l.
}
rewrite Nat.divide_div_mul_exact in Habc; [ | easy | ]. 2: {
  apply Nat.gcd_divide_r.
}
rewrite <- Ha', <- Hc' in Habc.
assert (Hg : Nat.gcd a' c' = 1). {
  rewrite Ha', Hc'.
  now apply Nat.gcd_div_gcd.
}
specialize (Nat.gauss (a' * a') (c' * c') b) as H2.
Search (_ * _ = 2).
...
specialize (Nat.gauss b a' a') as H2.
destruct (Nat.eq_dec (Nat.gcd b a') 1) as [Hba1| Hba1]. {
  assert (H : Nat.divide b (a' * a')). {
    rewrite Habc, <- Nat.mul_assoc.
    apply Nat.divide_factor_l.
  }
  specialize (H2 H Hba1).
  destruct H as (k, H).
...
specialize (Nat.gcd_div_gcd (a * a) (c * c)) as H2.
specialize (Nat.gcd_div_gcd a c (Nat.gcd a c) Hgz eq_refl) as H2.
...
assert (H1 : Nat.divide b (a' * a')). {
  rewrite Habc.
  rewrite <- Nat.mul_assoc.
  apply Nat.divide_factor_l.
}
unfold Nat.divide in H1.
destruct H1 as (k, H1).
Search (Nat.divide).
...
assert (H : Nat.gcd (a' * a') (c' * c') = 1). {
  rewrite Ha', Hc' at 2.
  rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
    apply Nat.gcd_divide_l.
  }
Search (Nat.gcd (_ / _)).
Search (_ * (_ / Nat.gcd _ _)).
rewrite
...
specialize (Nat.gcd_div_gcd) as H2.

Search (_ * (_ / Nat.gcd _ _)).
rewrite Nat.gcd_div_swap.
rewrite <- Nat.lcm_equiv1.
...
(*
clear d ro.
intros * Hit Hsq Hbac.
specialize (Nat.div_mod (b * b) a) as H1.
enough (Haz : a ≠ O).
specialize (H1 Haz).
rewrite Hbac in H1.
symmetry in H1.
apply Nat.add_sub_eq_l in H1.
rewrite <- Nat.mul_assoc in H1.
rewrite <- Nat.mul_sub_distr_l in H1.
do 2 rewrite (Nat.mul_comm a) in H1.
rewrite Nat.mod_mul in H1.
apply Nat.eq_mul_0_l in H1.
apply Nat.sub_0_le in H1.
...
*)
clear d ro.
intros * Hit Hsq Hbac.
revert a b c d Hit Hsq Hbac.
induction it; intros. {
  cbn in Hsq.
  clear Hsq.
...
induction it; intros; [ easy | ].
destruct a. {
  cbn in Hsq.
  destruct d as [| d']; [ easy | ].
  cbn in Hsq.
...
Print nat_is_square_loop.
cbn in Hsq.
...

Theorem nat_not_square_not_mul_square : ∀ a b c,
  nat_is_square a = false
  → (b * b)%nat = (a * c * c)%nat
  → b = 0%nat ∧ c = 0%nat.
Proof.
intros * Hsqa Hbac.
unfold nat_is_square in Hsqa.
...

Theorem not_square_not_mul_square : ∀ a b c,
  is_square a = false → b * b = a * c * c → b = 0 ∧ c = 0.
Proof.
intros * Hnsq Hbac.
destruct a as [| a| a]; [ easy | | ]. {
  unfold is_square in Hnsq.
  rewrite Zabs2Nat.inj_pos in Hnsq.
  destruct c as [| c| c]. {
    rewrite Z.mul_0_r in Hbac.
    apply Z.eq_mul_0 in Hbac.
    now destruct Hbac.
  } {
    exfalso.
    cbn in Hbac.
    destruct b as [| b| b]; [ easy | | ]. {
      cbn in Hbac.
      injection Hbac; clear Hbac; intros Hbac.
      apply Pos2Nat.inj_iff in Hbac.
      do 3 rewrite Pos2Nat.inj_mul in Hbac.
...
      apply nat_not_square_not_mul_square in Hbac; [ | easy ].
      destruct Hbac as (H1, _).
      specialize (Pos2Nat.is_pos b) as H2.
      now rewrite H1 in H2.
    } {
      cbn in Hbac.
      injection Hbac; clear Hbac; intros Hbac.
      apply Pos2Nat.inj_iff in Hbac.
      do 3 rewrite Pos2Nat.inj_mul in Hbac.
      apply nat_not_square_not_mul_square in Hbac; [ | easy ].
      destruct Hbac as (H1, _).
      specialize (Pos2Nat.is_pos b) as H2.
      now rewrite H1 in H2.
...
} {
...

Theorem quad_int_eucl_div :
  is_square d = false →
  if rngl_has_eucl_div then
    ∀ a b q r : quad_int d,
    b ≠ 0%F
    → rngl_eucl_div a b = (q, r)
    → a = (b * q + r)%F ∧ (rngl_gauge r < rngl_gauge b)%nat
  else not_applicable.
Proof.
intros Hdsqu.
unfold rngl_has_eucl_div, rngl_eucl_div, rngl_gauge.
cbn - [ In_dec ].
destruct (in_dec Z.eq_dec d having_eucl_div) as [Hhed| Hhed]; [ cbn | easy ].
intros * Hbz Hab.
unfold qi_eucl_div in Hab.
set (bb := qi_re (b * qi_conj b)) in Hab.
remember (Z.div_eucl (qi_re (a * qi_conj b)) bb) as γr eqn:Hγr.
symmetry in Hγr.
destruct γr as (γ₁, r₁).
remember (Z.div_eucl (qi_im (a * qi_conj b)) bb) as γr' eqn:Hγr'.
symmetry in Hγr'.
destruct γr' as (γ'₁, r'₁).
move γ'₁ before γ₁.
move r'₁ before r₁.
remember (if Z_le_dec _ _ then _ else _) as q₁ eqn:Hq₁ in Hab.
remember (if Z_le_dec _ _ then _ else _) as q'₁ eqn:Hq'₁ in Hab.
move q'₁ before q₁.
injection Hab; clear Hab; intros Hr Hq.
symmetry in Hr, Hq.
rewrite <- Hq in Hr.
split. {
  rewrite Hr.
  rewrite quad_int_add_sub_assoc.
  rewrite quad_int_add_comm.
  symmetry.
  apply quad_int_add_sub.
}
specialize (Z.div_eucl_eq (qi_re (a * qi_conj b)) bb) as H1.
rewrite Hγr in H1.
assert (Hbbz : bb ≠ 0). {
  intros H2; apply Hbz.
  unfold bb in H2.
  destruct b as (b₁, b'₁).
  cbn in H2.
  rewrite Z.mul_opp_r in H2.
  apply Z.add_move_0_r in H2.
  rewrite Z.opp_involutive in H2.
  unfold qi_zero.
...
  apply not_square_not_mul_square in H2; [ | easy ].
  now destruct H2; subst b₁ b'₁.
...
  destruct d; [ easy | | ]. {
    destruct b'₁ as [| b'₁| b'₁]. {
      rewrite Z.mul_0_r in H2.
      apply -> Z.eq_square_0 in H2; subst b₁.
      easy.
    } {
...
rewrite Hγr in H1.
destruct (Z_le_dec (2 * r₁) bb) as [Hrbb| Hrbb]. {
  subst q₁.
  destruct (Z_le_dec (2 * r'₁) bb) as [Hr'bb| Hr'bb]. {
    subst q'₁.
    destruct (Z.eq_dec d (-1)) as [Hd1| Hd1]. {
      subst d.
Search Z.div_eucl.
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
