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

(* square free integers *)

Fixpoint div_by_squ_loop it n d (same : bool) :=
  match it with
  | O => None
  | S it' =>
      if lt_dec n d then None
      else if Nat.eq_dec (n mod d) 0 then
        if same then Some d
        else div_by_squ_loop it' (n / d)%nat d true
      else div_by_squ_loop it' n (S d) false
  end.

Definition nat_div_by_square n := div_by_squ_loop n n 2 false.

Definition nat_square_free n := negb (bool_of_option (nat_div_by_square n)).

Definition square_free z := nat_square_free (Z.abs_nat z).

Compute filter square_free (map (λ n, Z.of_nat n -  60) (seq 1 120)).
Close Scope Z_scope.
Compute filter nat_square_free (seq 1 120).

(* should be removed and its theorems, because the real property I have to
   deal with is square_free, not is_square

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

Theorem nat_is_square_loop_false_if : ∀ it n d,
  it + d = S n
  → nat_is_square_loop it n d = false
  → ∀ a, d ≤ a → n ≠ a * a.
Proof.
clear.
intros * Hit Hsq a Had.
revert a n d Hit Hsq Had.
induction it; intros. {
  cbn in Hit; subst d.
  intros H; subst n.
  clear Hsq.
  apply Nat.nlt_ge in Had; apply Had; clear Had.
  induction a; [ cbn; flia | cbn ].
  apply -> Nat.succ_lt_mono.
  apply (lt_le_trans _ (S (a * a))); [ easy | ].
  apply -> Nat.succ_le_mono.
  rewrite (Nat.mul_comm _ (S a)); cbn.
  flia.
}
cbn in Hsq.
remember (d * d ?= n) as b eqn:Hb; symmetry in Hb.
destruct b; [ easy | | ]. {
  apply Nat.compare_lt_iff in Hb.
  destruct n; [ easy | ].
  destruct (Nat.eq_dec d a) as [Hda| Hda]. {
    subst a; flia Hb.
  }
  apply IHit with (d := S d); [ flia Hit | easy | flia Had Hda ].
} {
  apply Nat.compare_gt_iff in Hb.
  intros H; subst n.
  apply Nat.nle_gt in Hb; apply Hb; clear Hb.
  now apply Nat.mul_le_mono.
}
Qed.

Theorem nat_is_square_false_if : ∀ a,
  nat_is_square a = false
  → ∀ b, a ≠ b * b.
Proof.
clear.
intros * Hsq *.
apply nat_is_square_loop_false_if with (a := b) in Hsq; [ easy | easy | ].
apply Nat.le_0_l.
Qed.
*)

(*
Print squ_free_loop.

Theorem nat_squ_free_loop_true_if : ∀ it n d same,
  n ≤ it
  → n ≠ 0
  → squ_free_loop it n d same = true
  → ∀ b c, 2 ≤ d ≤ c → n ≠ b * c * c.
Proof.
clear.
intros * Hit Haz Hsq b c Hdc.
Print squ_free_loop.
...
n < d ∨
(n mod d = 0 ∧ same = false ∧ squ_free_loop (it - 1) (n /d) d true) ∨
squ_free_loop (it - 1) n (d + 1) false
...
nat_square_free = λ n : nat, squ_free_loop n n 2 false
...
revert a b c d same Hit Haz Hsq Hdc.
induction it; intros; [ easy | ].
cbn in Hsq.
destruct (lt_dec a d) as [Had| Had]. {
  clear Hsq.
  intros H; subst a.
  apply Nat.nle_gt in Had; apply Had; clear Had.
  destruct b; [ easy | ].
  rewrite <- Nat.mul_assoc; cbn.
  destruct c; [ now rewrite Nat.mul_comm in Haz | ].
  cbn; flia Hdc.
}
apply Nat.nlt_ge in Had.
destruct (Nat.eq_dec (a mod d) 0) as [Hadz| Hadz]. {
  destruct same; [ easy | ].
...
  specialize (IHit (a / d) b c d true) as H1.
  assert (H : a / d ≤ it). {
    apply Nat.mul_le_mono_pos_r with (p := d); [ flia Hdc | ].
    apply Nat.mod_divides in Hadz; [ | flia Hdc ].
    destruct Hadz as (k, Hk).
    rewrite Hk.
    rewrite (Nat.mul_comm d).
    rewrite Nat.div_mul; [ | flia Hdc ].
    rewrite Nat.mul_comm, <- Hk.
    transitivity (S it); [ easy | ].
    rewrite Nat.mul_comm.
    destruct d as [| d']; [ flia Hdc | cbn ].
    destruct d'; [ flia Hdc | cbn ].
    destruct it; [ | flia ].
    flia Haz Hit Had.
  }
  specialize (H1 H); clear H.
  assert (H : a / d ≠ 0). {
    apply Nat.mod_divides in Hadz; [ | flia Hdc ].
    destruct Hadz as (k, Hk).
    rewrite Hk.
    rewrite (Nat.mul_comm d).
    rewrite Nat.div_mul; [ | flia Hdc ].
    intros H; subst k.
    now rewrite Nat.mul_0_r in Hk.
  }
  specialize (H1 H Hsq Hdc); clear H.
...
  apply IHit with (d := d) (same := true); [ | easy | easy | ].
...
*)

Theorem div_by_squ_loop_more_iter : ∀ it k d a same,
  div_by_squ_loop it k d same = Some a
  → div_by_squ_loop (S it) k d same = Some a.
Proof.
clear.
intros * Hdbs.
revert k d a same Hdbs.
induction it; intros; [ easy | ].
remember (S it) as it'; cbn; subst it'.
cbn in Hdbs.
destruct (lt_dec k d) as [Hkd| Hkd]; [ easy | ].
apply Nat.nlt_ge in Hkd.
destruct (Nat.eq_dec (k mod d) 0) as [Hkdz| Hkdz]. {
  destruct same; [ easy | ].
  now apply IHit.
}
now apply IHit.
Qed.

Theorem div_by_squ_loop_some_if : ∀ it n d a,
  d ≠ 0
  → div_by_squ_loop it n d false = Some a
  → ∃ b : nat, n = b * a * a.
Proof.
clear.
intros * Hdz.
intros Hdbs.
revert n d Hdz Hdbs.
induction it; intros; [ easy | cbn in Hdbs ].
destruct (lt_dec n d) as [Hnd| Hnd]; [ easy | ].
apply Nat.nlt_ge in Hnd.
destruct (Nat.eq_dec (n mod d) 0) as [Hndz| Hndz]. {
  apply Nat.mod_divides in Hndz; [ | easy ].
  destruct Hndz as (k, Hk).
  rewrite Nat.mul_comm in Hk; subst n.
  rewrite Nat.div_mul in Hdbs; [ | easy ].
  apply div_by_squ_loop_more_iter in Hdbs.
  cbn in Hdbs.
  destruct (lt_dec k d) as [Hkd| Hkd]; [ easy | ].
  apply Nat.nlt_ge in Hkd.
  destruct (Nat.eq_dec (k mod d) 0) as [Hkdz| Hkdz]. {
    injection Hdbs; clear Hdbs; intros; subst a.
    apply Nat.mod_divides in Hkdz; [ | easy ].
    destruct Hkdz as (k', Hk').
    rewrite Nat.mul_comm in Hk'; subst k.
    now exists k'.
  }
  specialize (IHit k (S d) (Nat.neq_succ_0 _) Hdbs) as H1.
  destruct H1 as (k', Hk').
  subst k.
  exists (k' * d); flia.
}
now apply IHit with (d := S d).
Qed.

(*
Theorem div_by_squ_loop_some_only_if : ∀ it n d a b,
  0 < d ≤ a
  → 2 * (S a - d) < it
  → n ≠ 0
  → n = b * a * a
  → div_by_squ_loop it n d false = Some a.
Proof.
clear.
intros * Hda Hit Hnz Hn.
subst n.
 ...
48 = 3 * 4 * 4 = 12 * 2 * 2
...
revert d a b Hda Hit Hnz.
induction it; intros; [ easy | ].
cbn.
destruct (lt_dec (b * a * a) d) as [Hnd| Hnd]. {
  destruct b; [ easy | ].
  destruct a; [ flia Hda | ].
  flia Hda Hnd.
}
apply Nat.nlt_ge in Hnd.
(**)
destruct (Nat.eq_dec a d) as [Had| Had]. {
  subst d.
  rewrite Nat.mod_mul; [ | flia Hda ].
  rewrite Nat.div_mul; [ | flia Hda ].
  cbn.
  destruct it. {
    rewrite Nat.sub_succ_l in Hit; [ | easy ].
    rewrite Nat.sub_diag in Hit; flia Hit.
  }
  cbn.
  rewrite Nat.mod_mul; [ cbn | flia Hda ].
  destruct (lt_dec (b * a) a) as [Hbaa| Hbaa]; [ | easy ].
  destruct b; [ easy | ].
  flia Hbaa.
}
destruct (Nat.eq_dec ((b * a * a) mod d) 0) as [Hnmz| Hnmz]. {
  apply Nat.mod_divides in Hnmz; [ | flia Hda ].
  destruct Hnmz as (k, Hk).
  rewrite (Nat.mul_comm d) in Hk; rewrite Hk.
  rewrite Nat.div_mul; [ | flia Hda ].
  destruct it. {
    destruct d; [ easy | ].
    rewrite Nat.sub_succ in Hit.
    remember (a - n) as c eqn:Hc; symmetry in Hc.
    destruct c; [ flia Hda Hc | flia Hit ].
  }
  cbn.
  destruct (lt_dec k d) as [Hkd| Hkd]. {
...
*)

Theorem nat_div_by_square_some_if : ∀ n a,
  nat_div_by_square n = Some a
  → ∃ b : nat, n = b * a * a.
Proof.
clear.
intros *.
intros Hdbs.
unfold nat_div_by_square in Hdbs.
now apply div_by_squ_loop_some_if in Hdbs.
Qed.

Print div_by_squ_loop.

Theorem div_by_squ_loop_none_if : ∀ it n d same,
  n ≠ 0
  → n ≤ it
  → div_by_squ_loop it n d same = None
  → 2 ≤ d
  → ∀ b c, d ≤ c → n ≠ b * c * c.
Proof.
clear.
intros * Hnz Hit Hdbs Hd * Hdc.
revert n d same Hnz Hit Hdbs Hd b c Hdc.
induction it; intros. {
  now apply Nat.le_0_r in Hit.
}
cbn in Hdbs.
destruct (lt_dec n d) as [Hnd| Hnd]. {
  clear Hdbs.
  intros Hn.
  subst n.
  apply Nat.nle_gt in Hnd; apply Hnd; clear Hnd.
  transitivity c; [ easy | ].
  destruct b; [ easy | ].
  cbn; rewrite Nat.mul_comm.
  destruct c; [ easy | cbn; flia ].
}
apply Nat.nlt_ge in Hnd.
destruct (Nat.eq_dec (n mod d) 0) as [Hndz| Hndz]. {
  apply Nat.mod_divides in Hndz; [ | flia Hd ].
  destruct Hndz as (k, Hk).
  rewrite Nat.mul_comm in Hk; subst n.
  rewrite Nat.div_mul in Hdbs; [ | flia Hd ].
  destruct (Nat.eq_dec (k mod d) 0) as [Hkdz| Hkdz]. {
    apply Nat.mod_divides in Hkdz; [ | flia Hd ].
    destruct Hkdz as (k', Hk').
    rewrite Nat.mul_comm in Hk'; subst k.
    destruct it. {
      clear Hdbs.
      assert (H : k' * d * d = 1) by flia Hnz Hit.
      apply Nat.eq_mul_1 in H.
      flia Hd H.
    }
    cbn in Hdbs.
    rewrite Nat.mod_mul in Hdbs; [ | flia Hd ].
    cbn in Hdbs.
    destruct (lt_dec (k' * d) d) as [Hkdd| Hkdd]; [ | now destruct same ].
    clear Hdbs.
    exfalso; apply Nat.nle_gt in Hkdd.
    apply Hkdd; clear Hkdd.
    destruct k'; [ easy | cbn; flia ].
  }
  destruct same; [ easy | ].
  destruct (Nat.eq_dec (k * d) it) as [Hkdi| Hkdi]. {
    clear Hit.
(*
    specialize (IHit k d true) as H1.
    assert (H : k ≠ 0) by now apply Nat.neq_mul_0 in Hnz.
    specialize (H1 H); clear H.
    assert (H : k ≤ it). {
      rewrite <- Hkdi.
      destruct d; [ flia Hd | flia ].
    }
    specialize (H1 H Hdbs Hd); clear H.
    intros H.
*)
    destruct it; [ easy | ].
    cbn in Hdbs.
    destruct (lt_dec k d) as [Hkd| Hkd]. {
      destruct (Nat.eq_dec b 0) as [Hbz| Hbz]; [ now subst b | ].
      enough (H : k * d < b * c * c) by flia H.
      destruct (Nat.eq_dec d c) as [Hdc'| Hdc']. {
        subst d.
        apply Nat_le_neq_lt. {
          apply Nat.mul_le_mono_r.
          destruct b; [ easy | ].
          cbn; flia Hkd.
        }
        intros H.
        apply Nat.mul_cancel_r in H; [ | flia Hd ].
        apply Nat.nle_gt in Hkd; apply Hkd.
        rewrite H.
        destruct b; [ easy | cbn; flia ].
      }
      apply Nat.mul_lt_mono_nonneg; [ flia | | flia | flia Hdc Hdc' ].
      apply (Nat.lt_le_trans _ d); [ easy | ].
      destruct b; [ easy | ].
      cbn; flia Hdc.
    }
    apply Nat.nlt_ge in Hkd.
    destruct (Nat.eq_dec (k mod d) 0) as [Hkdz'| Hkdz']; [ easy | ].
    clear Hkdz'.
    destruct it. {
      apply Nat.eq_mul_1 in Hkdi.
      destruct Hkdi as (H1, H2).
      now rewrite H1, H2 in Hkdz.
    }
    cbn - [ Nat.eq_dec "/" "mod" ] in Hdbs.
    destruct (lt_dec k (S d)) as [Hksd| Hksd]. {
      replace k with d in Hkdz by flia Hkd Hksd.
      rewrite Nat.mod_same in Hkdz; [ easy | flia Hd ].
    }
    apply Nat.nlt_ge in Hksd; clear Hkd.
    destruct (Nat.eq_dec (k mod S d) 0) as [Hksdz| Hksdz]. {
      apply Nat.mod_divides in Hksdz; [ | easy ].
      destruct Hksdz as (k', Hk').
      rewrite Nat.mul_comm in Hk'; subst k.
      rewrite Nat.div_mul in Hdbs; [ | easy ].
      destruct it. {
        clear Hdbs.
        replace d with 1 in *; [ easy | ].
        destruct d as [| d']; [ easy | ].
        destruct d'; [ easy | ].
        destruct k'; [ easy | ].
        flia Hkdi.
      }
      cbn - [ Nat.eq_dec "/" "mod" ] in Hdbs.
....
  apply IHit with (d := d) (same := true); try easy. {
    destruct it. {
      (* devrait le faire *)
      admit.
    }
    cbn in Hdbs.
    destruct (lt_dec k d) as [Hkd| Hkd]. {
...
*)

Theorem nat_square_free_true_if : ∀ a,
  a ≠ 0
  → nat_square_free a = true
  → ∀ b c, 2 ≤ c → a ≠ b * c * c.
Proof.
clear.
intros a Haz Ha b c Hc.
unfold nat_square_free in Ha.
remember (nat_div_by_square a) as dbs eqn:Hdbs.
symmetry in Hdbs.
destruct dbs as [| d]; [ easy | clear Ha ].
unfold nat_div_by_square in Hdbs.
...
now apply div_by_squ_loop_none_if with (it := a) (d := 2) (same := false).
...

Theorem nat_square_free_not_mul_square : ∀ a b c,
  nat_square_free b = true
  → (a * a)%nat = (b * c * c)%nat
  → a = 0%nat ∧ c = 0%nat.
Proof.
clear.
intros * Hsqb Habc.
...
specialize (nat_square_free_true_if Hsqb) as Hsq'.
...
intros * Hsqb Habc.
specialize (nat_is_square_false_if Hsqb) as Hsq'.
destruct (Nat.eq_dec a 0) as [Haz| Haz]. {
  split; [ easy | ].
  rewrite Haz in Habc.
  symmetry in Habc; cbn in Habc.
  apply Nat.eq_mul_0 in Habc.
  destruct Habc as [Habc| Habc]; [ | easy].
  apply Nat.eq_mul_0 in Habc.
  destruct Habc; [ | easy ].
  subst b.
  now specialize (Hsq' 0).
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
assert (Hgg : Nat.gcd (a' * a') (c' * c') = 1). {
  now apply Nat_gcd_1_mul_l; apply Nat_gcd_1_mul_r.
}
specialize (Nat.gauss (a' * a') (c' * c') b) as H1.
rewrite (Nat.mul_comm _ b) in H1.
rewrite Nat.mul_assoc, <- Habc in H1.
specialize (H1 (Nat.divide_refl _) Hgg).
destruct H1 as (ka, H1).
(* would be ok if b held no squares, but provided that
   a'≠1; in that case → contradiction *)
...
Check Nat.gauss.
specialize (Nat.gauss (c' * c') a' a') as H1.
...
specialize (Nat.gauss (a' * a') (c' * c') b) as H1.
rewrite (Nat.mul_comm _ b) in H1.
rewrite Nat.mul_assoc, <- Habc in H1.
specialize (H1 (Nat.divide_refl _) Hgg).

rewrite Habc in H1.
...
specialize (Nat.gauss a' c' b) as H1.
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
