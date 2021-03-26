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

Require Import Misc RingLike.
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

Compute (Z.div_eucl 23 4).
Compute (Z.div_eucl (-23) 4).
Compute (Z.div_eucl 23 (-4)).
Compute (Z.div_eucl (-23) (-4)).

Definition qi_eucl_div {d} (a b : quad_int d) :=
  let bb := qi_re (b * qi_conj b)%QI in
  let '(γ₁, r₁) := Z.div_eucl (qi_re (a * qi_conj b)) bb in
  let '(γ'₁, r'₁) := Z.div_eucl (qi_im (a * qi_conj b)) bb in
  let γ := γ₁ + if Z_le_dec (2 * r₁) bb then 0 else 1 in
  let γ' := γ'₁ + if Z_le_dec (2 * r'₁) bb then 0 else 1 in
  let q := mk_qi d γ γ' in
  let r := (a - b * q)%QI in
  (q, r).

Definition qi_div d (α β : quad_int d) := fst (qi_eucl_div α β).

Notation "α / β" := (qi_div α β) : QI_scope.

Compute (qi_eucl_div (mk_qi (-1) (- 36) 242) (mk_qi (-1) 50 50)).
Compute (qi_eucl_div (mk_qi (-1) 36 242) (mk_qi (-1) 50 50)).
Compute (mk_qi (-1) 0 1 * mk_qi (-1) 0 1)%QI.
Check qi_eucl_div 1%QI (mk_qi (-1) 0 1).
Compute (qi_eucl_div 1%QI (mk_qi (-1) 0 1)).
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
Compute (1 / 〈 - 𝑖 〉)%QI.
Compute (〈 0 √42 〉 / 〈 0 √42 〉 )%QI.
Check (mk_qi (-1) 3 2).
Check (mk_qi (-1) 0 2).
Compute (mk_qi (-1) 1 2 * mk_qi (-1) 1 (-2))%QI.
Compute (mk_qi (-1) 2 3 * mk_qi (-1) 2 (-3))%QI.
Compute (mk_qi (-1) 1 2 * mk_qi (-1) 2 3)%QI.
Compute (mk_qi (-1) 1 2 * mk_qi (-1) 2 (-3))%QI.

Section a.

Context [d : Z].
Context (ro := @quad_int_ring_like_op d).
Existing Instance ro.

Theorem qi_re_im : ∀ (a : quad_int d), 〈 qi_re a + (qi_im a) √ d 〉%QI = a.
Proof.
intros.
now destruct a.
Qed.

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
  (a * (b * c))%QI = (a * b * c)%QI.
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

Theorem quad_int_mul_comm : ∀ a b : quad_int d, (a * b)%QI = (b * a)%QI.
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

Theorem quad_int_mul_opp_l : ∀ (a b : quad_int d), (- a * b = - (a * b))%QI.
Proof.
intros.
unfold qi_opp, qi_mul; cbn.
f_equal; ring.
Qed.

Theorem quad_int_mul_add_distr_r : ∀ (a b c : quad_int d),
  ((a + b) * c = a * c + b * c)%QI.
Proof.
intros.
unfold qi_add, qi_mul; cbn.
f_equal; ring.
Qed.

Theorem quad_int_mul_sub_distr_r : ∀ (a b c : quad_int d),
  ((a - b) * c = a * c - b * c)%QI.
Proof.
intros.
unfold qi_sub.
rewrite quad_int_mul_add_distr_r.
f_equal.
apply quad_int_mul_opp_l.
Qed.

Theorem quad_int_sub_move_r : ∀ a b c : quad_int d,
  (a - b = c ↔ a = b + c)%QI.
Proof.
intros.
split; intros H1. {
  subst c.
  rewrite quad_int_add_sub_assoc.
  rewrite quad_int_add_comm.
  symmetry.
  apply quad_int_add_sub.
} {
  subst a.
  rewrite quad_int_add_comm.
  apply quad_int_add_sub.
}
Qed.

Theorem quad_int_add_re_im : ∀ a b c e : Z,
  (〈 (a + b) + (c + e) √ d 〉 = 〈 a + c √ d 〉 + 〈 b + e √ d 〉)%QI.
Proof. intros. easy. Qed.

Theorem quad_int_mul_re_im : ∀ a b c,
 (〈 (a * b) + (a * c) √ d 〉 = 〈 a + 0 √ d 〉 * 〈 b + c √ d 〉)%QI.
Proof.
intros.
unfold qi_mul; cbn.
rewrite Z.mul_0_r.
rewrite Z.mul_0_l.
now do 2 rewrite Z.add_0_r.
Qed.

Theorem quad_int_add_sub_swap : ∀ a b c : quad_int d,
  (a + b - c = a - c + b)%QI.
Proof.
intros.
unfold qi_sub, qi_add; cbn.
f_equal; ring.
Qed.

Theorem quad_int_add_add_swap : ∀ a b c : quad_int d,
  (a + b + c = a + c + b)%QI.
Proof.
intros.
unfold qi_add; cbn.
f_equal; ring.
Qed.

Theorem quad_int_mul_mul_swap : ∀ a b c : quad_int d,
  (a * b * c = a * c * b)%QI.
Proof.
intros.
unfold qi_mul; cbn.
f_equal; ring.
Qed.

Theorem quad_int_sub_diag : ∀ a : quad_int d, (a - a = 0)%QI.
Proof.
intros.
unfold qi_sub, qi_add, qi_zero; cbn.
f_equal; ring.
Qed.

Theorem qi_re_mul_conj : ∀ a : quad_int d,
  qi_re (a * qi_conj a) = qi_re a ^ 2 - d * qi_im a ^ 2.
Proof.
intros.
cbn; ring.
Qed.

Theorem qi_im_mul_conj : ∀ a : quad_int d, qi_im (a * qi_conj a) = 0.
Proof.
intros.
cbn; ring.
Qed.

Theorem quad_int_mul_0_l : ∀ a : quad_int d, (0 * a = 0)%QI.
Proof.
intros.
unfold qi_mul, qi_zero; cbn.
f_equal; ring.
Qed.

Theorem quad_int_add_0_r : ∀ a : quad_int d, (a + 0 = a)%QI.
Proof.
intros.
unfold qi_add; cbn.
do 2 rewrite Z.add_0_r.
apply qi_re_im.
Qed.

Theorem qi_conj_mul : ∀ a b : quad_int d,
  (qi_conj (a * b) = qi_conj a * qi_conj b)%QI.
Proof.
intros.
unfold qi_conj, qi_mul; cbn.
f_equal; ring.
Qed.

Theorem qi_conj_involutive : ∀ a : quad_int d, qi_conj (qi_conj a) = a.
Proof.
intros.
unfold qi_conj; cbn.
rewrite Z.opp_involutive.
apply qi_re_im.
Qed.

Theorem quad_int_mul_re_re : ∀ a b, (〈 a 〉 * 〈 b 〉 = 〈 (a * b) 〉)%QI.
Proof.
intros.
unfold qi_mul; cbn.
f_equal; ring.
Qed.

End a.

(* square free integers *)

Close Scope Z_scope.

Definition bnat_square_free n :=
  (negb (n =? 0) &&
   forallb (λ d, negb (n mod (d * d) =? 0)) (seq 2 (n - 2)))%bool.

Definition nat_square_free n :=
  n ≠ 0 ∧ ∀ d, 2 ≤ d < n → n mod (d * d) ≠ 0.

Definition bsquare_free z := bnat_square_free (Z.abs_nat z).
Definition square_free z := nat_square_free (Z.abs_nat z).

Open Scope Z_scope.
Compute filter bsquare_free (map (λ n, Z.of_nat n -  60) (seq 1 120)).
Close Scope Z_scope.
Compute filter bnat_square_free (seq 1 120).

Theorem nat_square_free_bnat_square_free : ∀ n,
  nat_square_free n ↔ bnat_square_free n = true.
Proof.
clear.
intros.
unfold nat_square_free, bnat_square_free.
split; intros Hn. {
  destruct Hn as (Hnz, Hn).
  apply Bool.andb_true_iff.
  split. {
    apply Bool.negb_true_iff.
    now apply Nat.eqb_neq.
  }
  apply forallb_forall.
  intros d Hd.
  apply Bool.negb_true_iff.
  apply Nat.eqb_neq.
  apply Hn.
  apply in_seq in Hd.
  flia Hd.
} {
  apply Bool.andb_true_iff in Hn.
  destruct Hn as (Hnz, Hn).
  apply Bool.negb_true_iff in Hnz.
  apply Nat.eqb_neq in Hnz.
  split; [ easy | ].
  intros d Hd.
  specialize (proj1 (forallb_forall _ _) Hn d) as H1.
  assert (H : d ∈ seq 2 (n - 2)) by (apply in_seq; flia Hd).
  specialize (H1 H); clear H; cbn in H1.
  apply Bool.negb_true_iff in H1.
  now apply Nat.eqb_neq in H1.
}
Qed.

Definition is_square n := ∃ d, d * d = n.
Definition Z_is_square z := ∃ d, (d * d)%Z = z.

Theorem sqr_of_not_squ_is_not_rat : ∀ n,
  ¬ is_square n
  → ∀ a b, Nat.gcd a b = 1
  → n * b ^ 2 ≠ a ^ 2.
Proof.
clear.
intros * Hn * Hab Hnab.
apply Hn; clear Hn.
cbn in Hnab; do 2 rewrite Nat.mul_1_r in Hnab.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  now exists 0.
}
assert (H1 : Nat.divide (a * a) n). {
  apply Nat.gauss with (m := b * b). 2: {
    now apply Nat_gcd_1_mul_l; apply Nat_gcd_1_mul_r.
  }
  rewrite (Nat.mul_comm _ n).
  now rewrite Hnab.
}
destruct H1 as (ka, H1).
replace n with (n * 1) in H1 by apply Nat.mul_1_r.
rewrite <- Hnab in H1.
rewrite (Nat.mul_comm ka) in H1.
do 2 rewrite <- Nat.mul_assoc in H1.
apply Nat.mul_cancel_l in H1; [ | easy ].
symmetry in H1.
apply Nat.eq_mul_1 in H1.
destruct H1 as (H1, H2); subst b.
rewrite Nat.mul_1_r in Hnab.
now exists a.
Qed.

Theorem nat_square_free_not_mul_square : ∀ a b c,
  b ≠ 1
  → ¬ is_square b
  → (a * a)%nat = (b * c * c)%nat
  → a = 0%nat ∧ c = 0%nat.
Proof.
clear.
intros * Hb1 Hsqfb Habc.
destruct (Nat.eq_dec a 0) as [Haz| Haz]. {
  split; [ easy | ].
  rewrite Haz in Habc.
  symmetry in Habc; cbn in Habc.
  apply Nat.eq_mul_0 in Habc.
  destruct Habc as [Habc| Habc]; [ | easy].
  apply Nat.eq_mul_0 in Habc.
  unfold nat_square_free in Hsqfb.
  unfold is_square in Hsqfb.
  destruct Habc as [H| H]; [ | easy ].
  now exfalso; apply Hsqfb; exists 0.
}
exfalso.
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
destruct (Nat.eq_dec a' 0) as [Ha'z| Ha'z]. {
  move Ha'z at top; subst a'.
  symmetry in Ha'.
  apply Nat.div_small_iff in Ha'; [ | easy ].
  apply Nat.nle_gt in Ha'; apply Ha'.
  specialize (Nat.gcd_divide_l a c) as H1.
  destruct H1 as (ka, H1).
  rewrite H1 at 2.
  destruct ka; [ easy | ].
  apply Nat.le_add_r.
}
move Ha'z before Haz.
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
symmetry in Habc; revert Habc.
rewrite <- Nat.mul_assoc.
do 2 rewrite <- Nat.pow_2_r.
apply sqr_of_not_squ_is_not_rat; [ | easy ].
intros Hb.
destruct Hb as (k, Hk); subst b.
now apply Hsqfb; exists k.
Qed.

Open Scope Z_scope.

Theorem square_free_not_mul_square : ∀ a b c,
  a ≠ 1 → ¬ Z_is_square a → b * b = a * c * c → b = 0 ∧ c = 0.
Proof.
clear.
intros * Ha1 Hasf Hbac.
destruct a as [| a| a]. {
  now exfalso; apply Hasf; exists 0.
}  {
  assert (H1 : ∀ c, b * b = Z.pos (a * c * c) → False). {
    clear c Hbac; intros c Hbac.
    destruct b as [| b| b]; [ easy | | ]. {
      cbn in Hbac.
      injection Hbac; clear Hbac; intros Hbac.
      apply Pos2Nat.inj_iff in Hbac.
      do 3 rewrite Pos2Nat.inj_mul in Hbac.
      apply nat_square_free_not_mul_square in Hbac; cycle 1. {
        intros H; apply Ha1.
        replace 1%nat with (Pos.to_nat 1) in H by easy.
        now apply Pos2Nat.inj_iff in H; subst a.
      } {
        intros (k, Hk).
        apply Hasf.
        exists (Z.of_nat k).
        rewrite <- Nat2Z.inj_mul, Hk.
        apply positive_nat_Z.
      }
      destruct Hbac as (H1, _).
      specialize (Pos2Nat.is_succ b) as H2.
      destruct H2 as (n, H2).
      now rewrite H1 in H2.
    } {
      cbn in Hbac.
      injection Hbac; clear Hbac; intros Hbac.
      apply Pos2Nat.inj_iff in Hbac.
      do 3 rewrite Pos2Nat.inj_mul in Hbac.
      apply nat_square_free_not_mul_square in Hbac; cycle 1. {
        intros H; apply Ha1.
        rewrite <- positive_nat_Z.
        now rewrite H.
      } {
        intros (k, Hk).
        apply Hasf.
        exists (Z.of_nat k).
        rewrite <- Nat2Z.inj_mul, Hk.
        apply positive_nat_Z.
      }
      destruct Hbac as (H1, _).
      specialize (Pos2Nat.is_succ b) as H2.
      destruct H2 as (n, H2).
      now rewrite H1 in H2.
    }
  }
  destruct c as [| c| c]. {
    rewrite Z.mul_0_r in Hbac.
    apply Z.eq_mul_0 in Hbac.
    now destruct Hbac.
  } {
    now specialize (H1 c Hbac).
  } {
    now specialize (H1 c Hbac).
  }
} {
  destruct c as [| c| c]. {
    rewrite Z.mul_0_r in Hbac.
    apply Z.eq_mul_0 in Hbac.
    now destruct Hbac.
  } {
    cbn in Hbac.
    exfalso.
    specialize (Pos2Z.neg_is_neg (a * c * c)) as H1.
    rewrite <- Hbac in H1.
    apply Z.nle_gt in H1; apply H1; clear H1.
    apply Z.square_nonneg.
  } {
    cbn in Hbac.
    exfalso.
    specialize (Pos2Z.neg_is_neg (a * c * c)) as H1.
    rewrite <- Hbac in H1.
    apply Z.nle_gt in H1; apply H1; clear H1.
    apply Z.square_nonneg.
  }
}
Qed.

Theorem Z_sqr_abs_1 : ∀ z, Z.abs_nat z = 1%nat → z * z = 1.
Proof.
clear.
intros * Hz1.
destruct z as [| z| z]; [ easy | | ]. {
  cbn in Hz1 |-*.
  replace 1%nat with (Pos.to_nat 1) in Hz1 by easy.
  now apply Pos2Nat.inj in Hz1; subst z.
} {
  cbn in Hz1 |-*.
  replace 1%nat with (Pos.to_nat 1) in Hz1 by easy.
  now apply Pos2Nat.inj in Hz1; subst z.
}
Qed.

Theorem Z_eq_abs_nat_0 : ∀ z, Z.abs_nat z = 0%nat → z = 0.
Proof.
clear.
intros * Hz.
destruct z as [| z| z]; [ easy | | ]. {
  cbn in Hz.
  specialize (Pos2Nat.is_pos z) as H1.
  rewrite <- Hz in H1.
  flia H1.
} {
  cbn in Hz.
  specialize (Pos2Nat.is_pos z) as H1.
  rewrite <- Hz in H1.
  flia H1.
}
Qed.

Section a.

Context [d : Z].
Context (ro := @quad_int_ring_like_op d).
Existing Instance ro.

Context {Hd1 : d ≠ 1}.
Context {Hdsqu : square_free d}.

Theorem square_free_not_square : ∀ z, z ≠ 1 → square_free z → ¬ Z_is_square z.
Proof.
clear.
intros z Hz1 (Hnz, Hsf) (k, Hk).
specialize (Hsf (Z.abs_nat k)) as H1.
assert (H : 2 ≤ Z.abs_nat k < Z.abs_nat z). {
  split. {
    destruct k as [| k| k]; [ now subst z | | ]. {
      cbn in Hk; cbn.
      remember (Pos.to_nat k) as n eqn:Hn; symmetry in Hn.
      destruct n. {
        specialize (Pos2Nat.is_pos k) as H2.
        now rewrite Hn in H2.
      }
      destruct n; [ | flia ].
      replace 1%nat with (Pos.to_nat 1) in Hn by easy.
      now apply Pos2Nat.inj in Hn; subst k; subst z.
    } {
      cbn in Hk; cbn.
      remember (Pos.to_nat k) as n eqn:Hn; symmetry in Hn.
      destruct n. {
        specialize (Pos2Nat.is_pos k) as H2.
        now rewrite Hn in H2.
      }
      destruct n; [ | flia ].
      replace 1%nat with (Pos.to_nat 1) in Hn by easy.
      now apply Pos2Nat.inj in Hn; subst k; subst z.
    }
  }
  rewrite <- Hk.
  rewrite Zabs2Nat.inj_mul.
  remember (Z.abs_nat k) as n eqn:Hn; symmetry in Hn.
  destruct n. 2: {
    destruct n; [ | cbn; flia ].
    apply Z_sqr_abs_1 in Hn.
    now rewrite Hk in Hn.
  }
  apply Z_eq_abs_nat_0 in Hn.
  now subst k; subst z.
}
specialize (H1 H); clear H.
apply H1; clear H1.
rewrite <- Hk.
rewrite Zabs2Nat.inj_mul.
apply Nat.mod_same.
rewrite <- Hk in Hnz.
now rewrite Zabs2Nat.inj_mul in Hnz.
Qed.

Theorem quad_int_eucl_div :
  if rngl_has_eucl_div then
    ∀ a b q r : quad_int d,
    b ≠ 0%F
    → rngl_eucl_div a b = (q, r)
    → a = (b * q + r)%F ∧ (rngl_gauge r < rngl_gauge b)%nat
  else not_applicable.
Proof.
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
remember (if Z_le_dec _ _ then _ else _) as d₁ eqn:Hd₁ in Hab.
remember (if Z_le_dec _ _ then _ else _) as d'₁ eqn:Hd'₁ in Hab.
move d'₁ before d₁.
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
unfold qi_gauge.
fold bb.
assert (Hbbz : bb ≠ 0). {
  intros H2; apply Hbz.
  unfold bb in H2.
  destruct b as (b₁, b'₁).
  cbn in H2.
  rewrite Z.mul_opp_r in H2.
  apply Z.add_move_0_r in H2.
  rewrite Z.opp_involutive in H2.
  unfold qi_zero.
  apply square_free_not_mul_square in H2; [ | easy | ]. 2: {
    now apply square_free_not_square.
  }
  now destruct H2; subst b₁ b'₁.
}
specialize (Z_div_mod_full (qi_re (a * qi_conj b)) bb Hbbz) as H1.
rewrite Hγr in H1.
specialize (Z_div_mod_full (qi_im (a * qi_conj b)) bb Hbbz) as H2.
rewrite Hγr' in H2.
destruct H1 as (Hre, Hrer).
destruct H2 as (Him, Himr).
move Him before Hre.
unfold Remainder in Hrer, Himr.
assert (Hbbp : 0 < bb). {
  unfold bb; cbn.
(* ah oui, non, uniquement si d < 0 *)
...
destruct Hrer as [Hrer| Hrer]. 2: {
flia Hrer Hbbp.
...
set (rr := qi_re (r * qi_conj r)).
move rr before bb.
assert
  (Hrb : (〈 r₁ + r'₁ √ d 〉 = r * qi_conj b + 〈 (bb * d₁) + (bb * d'₁) √ d 〉)%QI). {
  rewrite Hr.
  rewrite quad_int_mul_sub_distr_r.
  rewrite <- (qi_re_im (a * qi_conj b)%QI).
  rewrite Hre, Him.
  rewrite <- quad_int_add_sub_swap.
  rewrite quad_int_add_re_im.
  rewrite quad_int_add_add_swap.
  rewrite <- quad_int_add_re_im.
  do 2 rewrite <- Z.mul_add_distr_l.
  rewrite quad_int_mul_re_im.
  rewrite <- Hq.
  rewrite (quad_int_mul_comm b).
  rewrite <- quad_int_mul_assoc.
  rewrite quad_int_add_sub_swap.
  rewrite (quad_int_mul_comm q).
  rewrite <- quad_int_mul_sub_distr_r.
  rewrite quad_int_add_comm.
  apply quad_int_sub_move_r.
  rewrite quad_int_sub_diag; symmetry.
  rewrite <- (qi_re_im (b * qi_conj b)%QI).
  fold bb.
  rewrite qi_im_mul_conj.
  rewrite quad_int_sub_diag.
  apply quad_int_mul_0_l.
}
(* mmm... c'est compliqué... mais en tous cas, pour l'instant, il
   n'y a pas de contraintes sur la valeur de d, à part de n'avoir
   pas de facteur carré (square free) ; mais normalement, la
   condition sur la jauge n'est censée marcher que sur
   la liste having_eucl_div, bien que... bon, ma définition est
   incorrecte sur les d=4n+1 (je fais des ℤ(√d) au lieu de ℚ(√d)) *)
destruct (Z.eq_dec d (-1)) as [Hdm1| Hdm1]. {
  move Hdm1 at top; subst d.
  clear Hd1 Hhed Hdsqu.
  move q at top; move b at top; move a at top.
  destruct (Z_le_dec (2 * r₁) bb) as [Hrbb| Hrbb]. {
    subst d₁.
    destruct (Z_le_dec (2 * r'₁) bb) as [Hr'bb| Hr'bb]. {
      subst d'₁.
      do 2 rewrite Z.add_0_r in Hq.
      rewrite Z.mul_0_r in Hrb.
      rewrite quad_int_add_0_r in Hrb.
      symmetry in Hrb.
      set (rq := (r * qi_conj b)%QI) in Hrb.
      assert (H1 : (rq * qi_conj rq = 〈 (r₁ ^ 2 + r'₁ ^ 2) 〉)%QI). {
        rewrite <- (qi_re_im (rq * qi_conj rq)%QI).
        rewrite qi_im_mul_conj.
        rewrite qi_re_mul_conj.
        f_equal.
        unfold Z.sub.
        rewrite <- Z.mul_opp_l.
        rewrite Z.mul_1_l.
        now rewrite Hrb.
      }
      apply (f_equal (qi_mul (mk_qi _ 4 0))) in H1.
      unfold qi_mul in H1 at 3.
      unfold qi_im in H1.
      do 2 rewrite Z.mul_0_r in H1.
      rewrite Z.mul_0_l in H1.
      do 2 rewrite Z.add_0_r in H1.
      cbn - [ qi_mul Z.pow Z.mul ] in H1.
      rewrite Z.mul_add_distr_l in H1.
      replace 4 with (2 ^ 2) in H1 by easy.
      do 2 rewrite <- Z.pow_mul_l in H1.
      unfold rq in H1.
      rewrite qi_conj_mul in H1.
      rewrite qi_conj_involutive in H1.
      rewrite (quad_int_mul_mul_swap) in H1.
      rewrite (quad_int_mul_assoc r) in H1.
      rewrite <- (qi_re_im (r * qi_conj r)%QI) in H1.
      fold rr in H1.
      rewrite qi_im_mul_conj in H1.
      rewrite <- quad_int_mul_assoc in H1.
      rewrite <- (qi_re_im (b * qi_conj b)%QI) in H1.
      fold bb in H1.
      rewrite qi_im_mul_conj in H1.
      do 2 rewrite quad_int_mul_re_re in H1.
      rewrite Z.mul_assoc in H1.
      remember (_ * _ * _) as x eqn:Hx in H1.
      remember (_ + _) as y eqn:Hy in H1.
      injection H1; clear H1; intros H1; subst x y.
      assert (H2 : 2 ^ 2 * rr * bb <= bb ^ 2 + bb ^ 2). {
        rewrite H1.
        apply Z.add_le_mono. {
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
     rngl_opt_add_sub := NA;
     rngl_opt_sub_sub_sub_add := NA;
     rngl_opt_mul_sub_distr_l := NA;
     rngl_opt_mul_sub_distr_r := NA;
     rngl_opt_mul_inv_l := NA;
     rngl_opt_mul_inv_r := NA;
     rngl_opt_eucl_div_prop := quad_int_eucl_div |}.
     rngl_opt_gauge_prop := ?rngl_opt_gauge_prop;
     rngl_opt_eq_dec := ?rngl_opt_eq_dec;
     rngl_opt_le_dec := ?rngl_opt_le_dec;
     rngl_opt_integral := ?rngl_opt_integral;
     rngl_characteristic_prop := ?rngl_characteristic_prop;
     rngl_opt_le_refl := ?rngl_opt_le_refl;
     rngl_opt_le_antisymm := ?rngl_opt_le_antisymm;
     rngl_opt_le_trans := ?rngl_opt_le_trans;
     rngl_opt_add_le_compat := ?rngl_opt_add_le_compat;
     rngl_opt_mul_le_compat_nonneg := ?rngl_opt_mul_le_compat_nonneg;
     rngl_opt_mul_le_compat_nonpos := ?rngl_opt_mul_le_compat_nonpos;
     rngl_opt_mul_le_compat := ?rngl_opt_mul_le_compat;
     rngl_opt_not_le := ?rngl_opt_not_le;
     rngl_consistent := ?rngl_consistent |}.
...
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
