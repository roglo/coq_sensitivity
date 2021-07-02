(* vectors *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List List.ListNotations.

Require Import Misc.
Require Import RingLike RLsummation.

Record vector (n : nat) T := mk_vect
  { vect_el : Fin.t n → T }.

(* function extensionality for vectors *)
Theorem vector_eq : ∀ n T (VA VB : vector n T),
  (∀ i, vect_el VA i = vect_el VB i)
  → VA = VB.
Proof.
intros * Hab.
destruct VA as (f).
destruct VB as (g).
cbn in Hab; f_equal.
now apply fin_fun_ext.
Qed.

(*
(* function extensionality required for vectors *)
Axiom vector_eq : ∀ n T (VA VB : vector n T),
  (∀ i, i < n → vect_el VA i = vect_el VB i)
  → VA = VB.

(* ... but this version of that axiom is bad: it proves False! *)
Theorem oops : False.
Proof.
assert (H1 : ∀ f g : nat → nat, f = g). {
  intros.
  enough (mk_vect 0 f = mk_vect 0 g) by now injection H.
  now apply vector_eq.
}
assert (H2 : ∀ (f g : nat → nat), f = g → ∀ x, f x = g x). {
  intros * Hfg x.
  now subst f.
}
now specialize (H2 (λ _, 0) (λ _, 1) (H1 _ _) 0).
Qed.
*)

Theorem add_succ_comm : ∀ a b, S a + b = a + S b.
Proof.
intros; cbn.
induction a; [ reflexivity | ].
now cbn; rewrite IHa.
Defined.

Theorem add_lt_succ : ∀ a b, a < a + S b.
Proof.
intros.
apply Nat.lt_sub_lt_add_l.
rewrite Nat.sub_diag.
apply Nat.lt_0_succ.
Qed.

(*
Definition fin_t_glop a b (p : a = b) : Fin.t a → Fin.t b :=
  λ i, match p with eq_refl => i end.

Print fin_t_glop.
Print eq_rect.
Print Fin.eqb.
Check f_equal.
Print f_equal.

Print eq_rect.

Definition fin_t_add_succ_l a b : Fin.t (S a + b) → Fin.t (a + S b) :=
  λ i, eq_rect _ _ i _ (add_succ_comm a b).
*)

Definition fin_t_add_succ_l a b : Fin.t (S a + b) → Fin.t (a + S b) :=
  λ i, match add_succ_comm a b with eq_refl => i end.

Fixpoint fin_seq start len : list (Fin.t (start + len)) :=
  match len with
  | 0 => []
  | S len' =>
      Fin.of_nat_lt (add_lt_succ start len') ::
      map (fin_t_add_succ_l (b := len')) (fin_seq (S start) len')
  end.

(*
Compute (map (λ i, proj1_sig (Fin.to_nat i)) (fin_seq 2 1)).
Compute (map (λ i, proj1_sig (Fin.to_nat i)) (fin_seq 2 2)).
Compute (map (λ i, proj1_sig (Fin.to_nat i)) (fin_seq 7 4)).
Compute fin_seq 7 4.
*)

Definition vect_of_list {T} d (l : list T) : vector (length l) T :=
  mk_vect (λ i, nth (proj1_sig (Fin.to_nat i)) l d).

Definition list_of_vect {n T} (v : vector n T) :=
  map (vect_el v) (fin_seq 0 n).

(*
Compute (list_of_vect (vect_of_list 42 [3;7;2])).
Compute (vect_of_list 42 [3;7;2]).
*)

(* (-1) ^ n *)

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context {rp : ring_like_prop T}.

Definition vect_zero n : vector n T := mk_vect (λ _, 0%F).

(* addition, subtraction of vector *)

Definition vect_add {n} (U V : vector n T) :=
  mk_vect (λ i, (vect_el U i + vect_el V i)%F).
Definition vect_opp {n} (V : vector n T) :=
  mk_vect (λ i, (- vect_el V i)%F).

Definition vect_sub {n} (U V : vector n T) := vect_add U (vect_opp V).

(* multiplication of a vector by a scalar *)

Definition vect_mul_scal_l s {n} (V : vector n T) :=
  mk_vect (λ i, s * vect_el V i)%F.

(* dot product *)

Definition vect_dot_product {n} (U V : vector n T) :=
  Σ (i ∈ fin_seq 0 n), vect_el U i * vect_el V i.

(*
Definition iter_fin_seq T b e (f : T → Fin.t (b + (S e - b)) → T) d :=
  iter_list (fin_seq b (S e - b)) f d.

Theorem pouet : ∀ b e, b + (e - b) = max b e.
Proof. intros. flia. Qed.

Definition glop b e : Fin.t (b + (e - b)) → Fin.t (max b e) :=
  λ i, match pouet b e with eq_refl => i end.

Definition iter_fin_seq' T b e (f : T → Fin.t (max b (S e)) → T) d :=
  iter_list (fin_seq b (S e - b))
    (λ a i, f a (glop b (S e) i)) d.

Notation "'Σf' ( i = b , e ) , g" :=
  (iter_fin_seq' b e (λ c i, (c + g)%F) 0%F)
  (at level 45, i at level 0, b at level 60, e at level 60).

Theorem agaga : ∀ n, 0 + (S (n - 1) - 0) = n.
Proof.
intros.
destruct n; [ | flia ].
cbn.
...

Definition vect_dot_product' {n} (U V : vector n T) :=
  Σf (i = 0, n - 1), vect_el U i * vect_el V i.

Print iter_list.

Print vect_dot_product.
Locate "Σ".
Search (Fin.t _ → Fin.t _).
*)

Definition vect_squ_norm n (V : vector n T) := vect_dot_product V V.

Definition minus_one_pow n :=
  match n mod 2 with
  | 0 => 1%F
  | _ => (- 1%F)%F
  end.

Theorem minus_one_pow_succ :
  rngl_has_opp = true →
  ∀ i, minus_one_pow (S i) = (- minus_one_pow i)%F.
Proof.
intros Hop *.
unfold minus_one_pow.
remember (i mod 2) as k eqn:Hk; symmetry in Hk.
destruct k. {
  apply Nat.mod_divides in Hk; [ | easy ].
  destruct Hk as (k, Hk); subst i.
  rewrite <- Nat.add_1_l, Nat.mul_comm.
  now rewrite Nat.mod_add.
}
destruct k. {
  rewrite <- Nat.add_1_l.
  rewrite <- Nat.add_mod_idemp_r; [ | easy ].
  rewrite Hk; cbn.
  symmetry.
  now apply rngl_opp_involutive.
}
specialize (Nat.mod_upper_bound i 2) as H1.
assert (H : 2 ≠ 0) by easy.
specialize (H1 H); clear H.
rewrite Hk in H1.
flia H1.
Qed.

Theorem minus_one_pow_add_r :
  rngl_has_opp = true →
  ∀ i j, minus_one_pow (i + j) = (minus_one_pow i * minus_one_pow j)%F.
Proof.
intros Hop *.
revert j.
induction i; intros; [ now cbn; rewrite rngl_mul_1_l | ].
rewrite Nat.add_succ_comm.
rewrite IHi.
rewrite minus_one_pow_succ; [ | easy ].
rewrite minus_one_pow_succ; [ | easy ].
rewrite rngl_mul_opp_l; [ | easy ].
rewrite rngl_mul_opp_r; [ | easy ].
easy.
Qed.

Declare Scope V_scope.
Delimit Scope V_scope with V.

Arguments vect_dot_product {n}%nat (U V)%V.

Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.
Notation "≺ U , V ≻" := (vect_dot_product U V) (at level 35).
Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.

Theorem vect_mul_scal_l_mul_assoc {n} : ∀ (a b : T) (V : vector n T),
  (a × (b × V))%V = ((a * b)%F × V)%V.
Proof.
intros.
apply vector_eq.
intros; cbn.
apply rngl_mul_assoc.
Qed.

Theorem vect_mul_scal_reg_r :
  rngl_has_inv = true ∨ rngl_has_quot = true →
  rngl_has_dec_eq = true →
  ∀ {n} (V : vector n T) a b,
  V ≠ vect_zero n
  → (a × V = b × V)%V
  → a = b.
Proof.
intros Hii Hde * Hvz Hab.
assert (Hiv : ∀ i, vect_el (a × V)%V i = vect_el (b × V)%V i). {
  intros i.
  now rewrite Hab.
}
unfold vect_mul_scal_l in Hiv.
cbn in Hiv.
assert (Hn : ¬ ∀ i, vect_el V i = 0%F). {
  intros H; apply Hvz.
  apply vector_eq.
  cbn; intros.
  now apply H.
}
destruct (rngl_eq_dec Hde a b) as [Haeb| Haeb]; [ easy | ].
exfalso; apply Hvz; clear Hvz.
apply vector_eq.
intros i; cbn.
specialize (Hiv i).
destruct (rngl_eq_dec Hde (vect_el V i) 0%F) as [Hvi| Hvi]; [ easy | ].
now apply rngl_mul_cancel_r in Hiv.
Qed.

Theorem vect_dot_mul_scal_mul_comm :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  rngl_is_comm = true →
  ∀ {n} (a : T) (U V : vector n T),
  ≺ U, a × V ≻ = (a * ≺ U, V ≻)%F.
Proof.
intros Hom Hic *.
unfold vect_dot_product.
rewrite rngl_mul_summation_list_distr_l; [ | easy ].
apply rngl_summation_list_eq_compat.
intros j Hj; cbn.
do 2 rewrite rngl_mul_assoc.
f_equal.
now apply rngl_mul_comm.
Qed.

Theorem vect_scal_mul_dot_mul_comm :
  rngl_has_opp = true ∨ rngl_has_sous = true →
  ∀ {n} (a : T) (U V : vector n T),
  ≺ a × U, V ≻ = (a * ≺ U, V ≻)%F.
Proof.
intros Hom *.
unfold vect_dot_product.
rewrite rngl_mul_summation_list_distr_l; [ | easy ].
apply rngl_summation_list_eq_compat.
intros j Hj; cbn.
symmetry; apply rngl_mul_assoc.
Qed.

Theorem vect_eq_dec :
  rngl_has_dec_eq = true →
  ∀ n (U V : vector n T), {U = V} + {U ≠ V}.
Proof.
intros Hde *.
destruct U as (fu).
destruct V as (fv).
(*
assert (H : ∀ i, {fu i = fv i} + {fu i ≠ fv i}). {
  intros.
  apply (rngl_eq_dec Hde).
}
*)
induction n; intros; [ now left; apply vector_eq | ].
set (gu := λ i, fu (Fin.R 1 i)).
set (gv := λ i, fv (Fin.R 1 i)).
specialize (IHn gu gv).
destruct IHn as [IHn| IHn]. {
  set (nn := Fin.of_nat_lt (Nat.lt_succ_diag_r n)).
  destruct (rngl_eq_dec Hde (fu nn) (fv nn)) as [H1| H1]. {
    left.
    apply vector_eq.
    intros i; cbn.
    injection IHn; clear IHn; intros H2.
    destruct (Fin.eq_dec i nn) as [H3| H3]; [ now subst i | ].
    assert (H4 : proj1_sig (Fin.to_nat i) < n). {
      specialize (proj2_sig (Fin.to_nat i)) as H4.
      cbn in H4.
      destruct (Nat.eq_dec (proj1_sig (Fin.to_nat i)) n) as [H5| H5]. {
        exfalso; apply H3; clear H3.
        unfold nn.
        apply Fin.to_nat_inj.
        rewrite H5.
        now rewrite Fin.to_nat_of_nat.
      }
      flia H4 H5.
    }
    set (m := Fin.of_nat_lt H4).
    assert (H5 : gu m =  gv m) by now rewrite H2.
    unfold m, gu, gv in H5.
    cbn in H5.
    enough (Fin.FS (Fin.of_nat_lt H4) = i) by congruence.
    clear - H4.
    induction n; [ easy | ].
Definition glop n (i : Fin.t (S n)) (p : proj1_sig (Fin.to_nat i) < n) :=
  Fin.of_nat_lt p.
  remember (@glop (S n) i H4) as j eqn:Hj.
  unfold glop in Hj.
,,,
Search Fin.of_nat_lt.
assert (Fin.R 1 (Fin.of_nat_lt H4
...
    cbn in H5.
...
    enough (Fin.FS (Fin.of_nat_lt H4) = i) by congruence.
Fin.of_nat_lt: ∀ p n : nat, p < n → Fin.t n
assert (∀ i, fu i = gu (
...
Search (Fin.t _ → Fin.t _).
...
    set (m := Fin.of_nat_lt H4).
    assert (H5 : gu m =  gv m) by now rewrite H2.
    unfold m, gu, gv in H5.
    cbn in H5.
    enough (Fin.FS (Fin.of_nat_lt H4) = i) by congruence.
...
    rewrite <- H2 in Hb.
    unfold gu, m in Ha, Hb.
Search Fin.L.
    unfold gu, m in Ha; cbn in Ha.
    unfold gv, m in Hb; cbn in Hb.
Print Fin.
 Definition of_nat_lt : ∀ p n : nat, p < n → t n.
Search (Fin.t _ → Fin.t _).
Print Term Fin.t.
...
Search Fin.to_nat.
Search (proj1_sig (Fin.to_nat _)).
Check (proj1_sig (Fin.to_nat i)).
Check (proj2_sig (Fin.to_nat i)).
...

Check @Fin.eq_dec.
Check (Fin.of_nat_lt (Nat.lt_succ_diag_r n)).
destruct (Fin.eq_dec i (Fin.of_nat_lt (Nat.lt_succ_diag_r _))) as [H1| H1]. {
  subst i.

...

assert (H : ∀ i, {gu i = gv i} + {gu i ≠ gv i}). {
  intros i.
  destruct IH
...

Check @Fin.eq_dec.

Check (λ n, @Fin.of_nat_lt n (S n) (Nat.lt_succ_diag_r _)).

Print Term Fin.L.

Definition toto n (f : Fin.t (S n) → T) : Fin.t n → T :=
  λ i : Fin.t n, f (Fin.R 1 i).
...
destruct IHn as [IHn| IHn]. {
  injection IHn; clear IHn; intros IHn.
  now left; subst fv.
} {
  right.
  intros H1; apply IHn; clear IHn.
  injection H1; clear H1; intros H1.
  now subst fv.
}
Qed.

Definition vect_size {T n} (v : vector n T) := n.

End a.

Declare Scope V_scope.
Delimit Scope V_scope with V.

Arguments vect_add {T}%type {ro} {n}%nat (U V)%V.
Arguments vect_sub {T ro} {n}%nat U%V V%V.
Arguments vect_opp {T ro} {n}%nat V%V.
Arguments vect_mul_scal_l {T ro} s%F {n}%nat V%V.
Arguments vect_mul_scal_reg_r {T}%type {ro rp} Hde Hii {n}%nat V%V (a b)%F.
Arguments vect_zero {T ro} n%nat.
Arguments vect_dot_product {T}%type {ro} {n}%nat (U V)%V.
Arguments vect_dot_mul_scal_mul_comm {T}%type {ro rp} Hom Hic
  {n}%nat a%F (U V)%V.
Arguments vect_scal_mul_dot_mul_comm {T}%type {ro rp} Hom {n}%nat a%F (U V)%V.
Arguments vect_eq_dec {T}%type {ro rp} _ n%nat U%V V%V.
Arguments vect_el {n}%nat {T}%type v%V UUU%nat.
Arguments vect_squ_norm {T}%type {ro} {n}%nat V%V.

Arguments minus_one_pow {T}%type {ro} n%nat.
Arguments minus_one_pow_succ {T}%type {ro rp} _ i%nat.

Notation "U + V" := (vect_add U V) : V_scope.
Notation "U - V" := (vect_sub U V) : V_scope.
Notation "μ × V" := (vect_mul_scal_l μ V) (at level 40) : V_scope.
Notation "≺ U , V ≻" := (vect_dot_product U V) (at level 35).
Notation "- V" := (vect_opp V) : V_scope.
