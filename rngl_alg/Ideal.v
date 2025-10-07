(* Ideal.v *)

(* ideals on a RingLike *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.
Import List.ListNotations.
Import Init.Nat.

Require Import RingLike.Core.
Require Import RingLike.Misc.
Require Import RingLike.Utils.
From RingLike Require Import IterAdd IterAnd.

(* ideal: non empty set (type) with some properties *)
(* drawback: elementary properties, like commutativity of addition of ideals
   cannot be proven *)
(* another version of ideals using bool instead of Prop follows *)

Record ideal {T} {ro : ring_like_op T} := mk_ip
  { ip_subtype : T → Prop;
    ip_zero : ip_subtype rngl_zero;
    ip_add : ∀ a b, ip_subtype a → ip_subtype b → ip_subtype (a + b)%L;
    ip_opp : ∀ a, ip_subtype a → ip_subtype (- a)%L;
    ip_mul_l : ∀ a b, ip_subtype b → ip_subtype (a * b)%L;
    ip_mul_r : ∀ a b, ip_subtype a → ip_subtype (a * b)%L }.

Arguments ideal T {ro}.
Arguments ip_subtype {T ro} i a%_L.
Arguments ip_opp {T ro} i a%_L.

Class ideal_ctx T {ro : ring_like_op T} :=
  { ic_op : rngl_has_opp T = true }.

Ltac destruct_ic :=
  set (Hop := ic_op);
  set (Hos := rngl_has_opp_has_opp_or_psub Hop).

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ic : ideal_ctx T}.

(* 0 and 1 *)

Theorem I_zero_add a b : a = 0%L → b = 0%L → (a + b = 0)%L.
Proof. intros; subst; apply rngl_add_0_l. Qed.

Theorem I_zero_opp a : a = 0%L → (- a = 0)%L.
Proof. destruct_ic; intros; subst; apply (rngl_opp_0 Hop). Qed.

Theorem I_zero_mul_l a b : b = 0%L → (a * b = 0)%L.
Proof.
destruct_ic.
intros; subst; apply (rngl_mul_0_r Hos).
Qed.

Theorem I_zero_mul_r a b : a = 0%L → (a * b = 0)%L.
Proof.
destruct_ic.
intros; subst; apply (rngl_mul_0_l Hos).
Qed.

Definition I_zero : ideal T :=
  {| ip_subtype a := a = 0%L;
     ip_zero := eq_refl;
     ip_add := I_zero_add;
     ip_opp := I_zero_opp;
     ip_mul_l := I_zero_mul_l;
     ip_mul_r := I_zero_mul_r |}.

Definition I_one : ideal T :=
  {| ip_subtype a := True;
     ip_zero := I;
     ip_add _ _ _ _ := I;
     ip_opp _ _ := I;
     ip_mul_l _ _ _ := I;
     ip_mul_r _ _ _ := I |}.

(* addition *)

Definition I_add_subtype a b z :=
  ∃ x y, z = (x + y)%L ∧ ip_subtype a x ∧ ip_subtype b y.

Arguments I_add_subtype a b z%_L.

Theorem I_add_zero a b : I_add_subtype a b 0%L.
Proof.
exists 0%L, 0%L.
split; [ symmetry; apply rngl_add_0_l | ].
split; apply ip_zero.
Qed.

Theorem I_add_add a b :
  ∀ x y,
  I_add_subtype a b x → I_add_subtype a b y → I_add_subtype a b (x + y)%L.
Proof.
intros * Hx Hy.
destruct Hx as (x1 & x2 & Hx & Hx1 & Hx2).
destruct Hy as (y1 & y2 & Hy & Hy1 & Hy2).
subst x y.
exists (x1 + y1)%L, (x2 + y2)%L.
split; [ | now split; apply ip_add ].
do 2 rewrite rngl_add_assoc.
progress f_equal.
apply rngl_add_add_swap.
Qed.

Theorem I_add_opp a b : ∀ x, I_add_subtype a b x → I_add_subtype a b (- x).
Proof.
destruct_ic.
intros * Hx.
destruct Hx as (x1 & x2 & Hx & Hx1 & Hx2); subst.
exists (- x1)%L, (- x2)%L.
split; [ | now split; apply ip_opp ].
rewrite rngl_add_comm.
rewrite (rngl_add_opp_r Hop).
rewrite <- (rngl_opp_sub_distr Hop).
rewrite (rngl_sub_opp_r Hop).
now f_equal.
Qed.

Theorem I_add_mul_l a b :
  ∀ x y, I_add_subtype a b y → I_add_subtype a b (x * y).
Proof.
intros * H.
destruct H as (x1 & x2 & Hx & Hx1 & Hx2); subst.
exists (x * x1)%L, (x * x2)%L.
split; [ | now split; apply ip_mul_l ].
apply rngl_mul_add_distr_l.
Qed.

Theorem I_add_mul_r a b :
  ∀ x y, I_add_subtype a b x → I_add_subtype a b (x * y).
Proof.
intros * H.
destruct H as (x1 & x2 & Hx & Hx1 & Hx2); subst.
exists (x1 * y)%L, (x2 * y)%L.
split; [ | now split; apply ip_mul_r ].
apply rngl_mul_add_distr_r.
Qed.

Definition I_add (a b : ideal T) : ideal T :=
  {| ip_subtype := I_add_subtype a b;
     ip_zero := I_add_zero a b;
     ip_add := I_add_add a b;
     ip_opp := I_add_opp a b;
     ip_mul_l := I_add_mul_l a b;
     ip_mul_r := I_add_mul_r a b |}.

(* multiplication *)

Definition I_mul_subtype a b z :=
  ∃ n lx ly,
  length lx = n ∧ length ly = n ∧
  (∀ x, x ∈ lx → ip_subtype a x) ∧
  (∀ y, y ∈ ly → ip_subtype b y) ∧
  z = ∑ (i = 1, n), lx.[i-1] * ly.[i-1].

Arguments I_mul_subtype a b z%_L.

Theorem I_mul_zero a b : I_mul_subtype a b 0%L.
Proof.
destruct_ic.
exists 0, [], [].
split; [ easy | ].
split; [ easy | ].
split; [ easy | ].
split; [ easy | ].
symmetry.
now apply rngl_summation_empty.
Qed.

Theorem I_mul_add a b :
  ∀ x y,
  I_mul_subtype a b x → I_mul_subtype a b y → I_mul_subtype a b (x + y)%L.
Proof.
intros * Hx Hy.
destruct Hx as (nx & la1 & lb1 & Hla1 & Hlb1 & Ha1 & Hb1 & Hx).
destruct Hy as (ny & la2 & lb2 & Hla2 & Hlb2 & Ha2 & Hb2 & Hy).
subst x y.
progress unfold I_mul_subtype.
exists (nx + ny).
exists (la1 ++ la2), (lb1 ++ lb2).
do 2 rewrite List.length_app.
rewrite Hla1, Hlb1, Hla2, Hlb2.
split; [ easy | ].
split; [ easy | ].
split. {
  intros x Hx.
  apply List.in_app_or in Hx.
  now destruct Hx; [ apply Ha1 | apply Ha2 ].
}
split. {
  intros y Hy.
  apply List.in_app_or in Hy.
  now destruct Hy; [ apply Hb1 | apply Hb2 ].
}
symmetry.
rewrite (rngl_summation_split nx); [ | flia ].
f_equal. {
  apply rngl_summation_eq_compat.
  intros i Hi.
  rewrite List.app_nth1; [ | flia Hla1 Hi ].
  rewrite List.app_nth1; [ | flia Hlb1 Hi ].
  easy.
}
destruct (Nat.eq_dec ny 0) as [Hnyz| Hnyz]. {
  move Hnyz at top; subst ny.
  rewrite rngl_summation_empty; [ | flia ].
  rewrite rngl_summation_empty; [ | flia ].
  easy.
} {
  rewrite (rngl_summation_shift nx); [ | flia Hnyz ].
  do 2 rewrite Nat.add_comm, Nat.add_sub.
  apply rngl_summation_eq_compat.
  intros i Hi.
  rewrite List.app_nth2; [ | flia Hla1 Hi ].
  rewrite List.app_nth2; [ | flia Hlb1 Hi ].
  rewrite Hla1, Hlb1.
  f_equal; f_equal; flia.
}
Qed.

Theorem I_mul_opp a b : ∀ x, I_mul_subtype a b x → I_mul_subtype a b (- x).
Proof.
destruct_ic.
intros * Hx.
destruct Hx as (n & la & lb & Hla & Hlb & Ha & Hb & Hx).
subst x.
progress unfold I_mul_subtype.
exists n, (List.map rngl_opp la), lb.
rewrite List.length_map.
split; [ easy | ].
split; [ easy | ].
split. {
  intros x Hx.
  apply List.in_map_iff in Hx.
  destruct Hx as (y & Hyx & Hy).
  subst x.
  now apply ip_opp, Ha.
}
split; [ easy | ].
rewrite (rngl_opp_summation Hop).
apply rngl_summation_eq_compat.
intros i Hi.
rewrite <- (rngl_mul_opp_l Hop).
progress f_equal.
rewrite (List_map_nth' 0%L); [ easy | flia Hi Hla ].
Qed.

Theorem I_mul_mul_l a b :
  ∀ x y, I_mul_subtype a b y → I_mul_subtype a b (x * y).
Proof.
destruct_ic.
intros * H.
destruct H as (n & la & lb & Hla & Hlb & Ha & Hb & H).
subst y.
progress unfold I_mul_subtype.
exists n, (List.map (rngl_mul x) la), lb.
rewrite List.length_map.
split; [ easy | ].
split; [ easy | ].
split. {
  intros z Hz.
  apply List.in_map_iff in Hz.
  destruct Hz as (y & Hxy & Hz).
  subst z.
  now apply ip_mul_l, Ha.
}
split; [ easy | ].
rewrite (rngl_mul_summation_distr_l Hos).
apply rngl_summation_eq_compat.
intros i Hi.
rewrite rngl_mul_assoc.
progress f_equal.
rewrite (List_map_nth' 0%L); [ easy | flia Hi Hla ].
Qed.

Theorem I_mul_mul_r a b :
  ∀ x y, I_mul_subtype a b x → I_mul_subtype a b (x * y).
Proof.
destruct_ic.
intros * H.
destruct H as (n & la & lb & Hla & Hlb & Ha & Hb & H).
subst x.
progress unfold I_mul_subtype.
exists n, la, (List.map (λ z, rngl_mul z y) lb).
rewrite List.length_map.
split; [ easy | ].
split; [ easy | ].
split; [ easy | ].
split. {
  intros z Hz.
  apply List.in_map_iff in Hz.
  destruct Hz as (x & Hxy & Hx).
  subst z.
  now apply ip_mul_r, Hb.
}
rewrite (rngl_mul_summation_distr_r Hos).
apply rngl_summation_eq_compat.
intros i Hi.
rewrite <- rngl_mul_assoc.
progress f_equal.
rewrite (List_map_nth' 0%L); [ easy | flia Hi Hlb ].
Qed.

Definition I_mul (a b : ideal T) : ideal T :=
  {| ip_subtype := I_mul_subtype a b;
     ip_zero := I_mul_zero a b;
     ip_add := I_mul_add a b;
     ip_opp := I_mul_opp a b;
     ip_mul_l := I_mul_mul_l a b;
     ip_mul_r := I_mul_mul_r a b |}.

(* opposite *)

Theorem I_opp_add a :
  ∀ x y, ip_subtype a (- x) → ip_subtype a (- y) → ip_subtype a (- (x + y)%L).
Proof.
destruct_ic.
intros * Hx Hy.
apply ip_opp in Hx, Hy.
rewrite (rngl_opp_involutive Hop) in Hx, Hy.
apply ip_opp.
now apply ip_add.
Qed.

Theorem I_opp_mul_l a :
  ∀ x y, ip_subtype a (- y) → ip_subtype a (- (x * y)%L).
Proof.
destruct_ic.
intros * H.
apply ip_opp, ip_mul_l.
rewrite <- (rngl_opp_involutive Hop).
now apply ip_opp.
Qed.

Theorem I_opp_mul_r a :
  ∀ x y, ip_subtype a (- x) → ip_subtype a (- (x * y)%L).
Proof.
destruct_ic.
intros * H.
apply ip_opp, ip_mul_r.
rewrite <- (rngl_opp_involutive Hop).
now apply ip_opp.
Qed.

Definition I_opp (a : ideal T) : ideal T :=
  {| ip_subtype x := ip_subtype a (-x);
     ip_zero := ip_opp a 0 (ip_zero a);
     ip_add := I_opp_add a;
     ip_opp x := ip_opp a (-x);
     ip_mul_l := I_opp_mul_l a;
     ip_mul_r := I_opp_mul_r a |}.

(* ideal ring like op *)

Definition I_ring_like_op : ring_like_op (ideal T) :=
  {| rngl_zero := I_zero;
     rngl_add := I_add;
     rngl_mul := I_mul;
     rngl_opt_one := Some I_one;
     rngl_opt_opp_or_psub :=
       match rngl_opt_opp_or_psub T with
       | Some (inl _) => Some (inl I_opp)
       | _ => None
       end;
     rngl_opt_inv_or_pdiv := None;
     rngl_opt_is_zero_divisor := Some (λ _, True);
     rngl_opt_eq_dec := None;
     rngl_opt_leb := None |}.

End a.

(*
Declare Scope ideal_scope.
Delimit Scope ideal_scope with I.
Bind Scope ideal_scope with ideal.

Notation "0" := I_zero : ideal_scope.
Notation "1" := I_one : ideal_scope.
Notation "a + b" := (I_add a b) : ideal_scope.
Notation "a - b" := (rngl_sub a b) : ideal_scope.
Notation "a * b" := (rngl_mul a b) : ideal_scope.
Notation "- a" := (rngl_opp a) : ideal_scope.

Axiom IPO : ∀ {I} (u : I → bool), (∀ i, u i = false) + (∃ i, u i = true).

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ic : ideal_ctx T}.

Theorem I_add_comm : ∀ a b, (a + b)%I = (b + a)%I.
Proof.
intros.
progress unfold I_add.
Print ideal.
...
*)

(* attempt to implement ideals using bool instead of Prop *)

(* ideal : non empty set (type) with some properties *)

Record ideal' {T} {ro : ring_like_op T} := mk_ip'
  { ip_subtype' : T → bool;
    ip_zero' : ip_subtype' rngl_zero = true;
    ip_add' :
      ∀ a b,
      ip_subtype' a = true
      → ip_subtype' b = true
      → ip_subtype' (a + b)%L = true;
    ip_opp' : ∀ a, ip_subtype' a = true → ip_subtype' (- a)%L = true;
    ip_mul_l' : ∀ a b, ip_subtype' b = true → ip_subtype' (a * b)%L = true;
    ip_mul_r' : ∀ a b, ip_subtype' a = true → ip_subtype' (a * b)%L = true }.

Arguments ideal' T {ro}.
Arguments ip_subtype' {T ro} i a%_L.
Arguments ip_opp' {T ro} i a%_L.

Class ideal_ctx' T {ro : ring_like_op T} :=
  { ic_op' : rngl_has_opp T = true;
    ic_eo' : rngl_has_eq_dec_or_order T = true }.

Ltac destruct_ic' :=
  set (Hop := ic_op');
  set (Heo := ic_eo');
  set (Hos := rngl_has_opp_has_opp_or_psub Hop).

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ic : ideal_ctx' T}.

(* 0 and 1 *)

Theorem I_zero_add' a b :
  (a =? 0)%L = true
  → (b =? 0)%L = true
  → (a + b =? 0)%L = true.
Proof.
destruct_ic'.
intros Ha Hb.
apply (rngl_eqb_eq Heo) in Ha, Hb.
apply (rngl_eqb_eq Heo).
subst; apply rngl_add_0_l.
Qed.

Theorem I_zero_opp' a : (a =? 0)%L = true → (- a =? 0)%L = true.
Proof.
destruct_ic'.
intros Ha.
apply (rngl_eqb_eq Heo) in Ha.
apply (rngl_eqb_eq Heo).
subst; apply (rngl_opp_0 Hop).
Qed.

Theorem I_zero_mul_l' a b : (b =? 0)%L = true → (a * b =? 0)%L = true.
Proof.
destruct_ic'.
intros H.
apply (rngl_eqb_eq Heo) in H.
apply (rngl_eqb_eq Heo).
subst; apply (rngl_mul_0_r Hos).
Qed.

Theorem I_zero_mul_r' a b : (a =? 0)%L = true → (a * b =? 0)%L = true.
Proof.
destruct_ic'.
intros H.
apply (rngl_eqb_eq Heo) in H.
apply (rngl_eqb_eq Heo).
subst; apply (rngl_mul_0_l Hos).
Qed.

Definition I_zero' : ideal' T :=
  {| ip_subtype' a := (a =? 0)%L;
     ip_zero' := rngl_eqb_refl ic_eo' 0%L;
     ip_add' := I_zero_add';
     ip_opp' := I_zero_opp';
     ip_mul_l' := I_zero_mul_l';
     ip_mul_r' := I_zero_mul_r' |}.

Definition I_one' : ideal' T :=
  {| ip_subtype' a := true;
     ip_zero' := eq_refl;
     ip_add' _ _ _ _ := eq_refl;
     ip_opp' _ _ := eq_refl;
     ip_mul_l' _ _ _ := eq_refl;
     ip_mul_r' _ _ _ := eq_refl |}.

(* Illimited Principe of Omniscience *)
(*
Axiom IPO :
  ∀ {I} (u : I → bool), (∀ i, u i = false) + { i : I | u i = true }.
Axiom IPO : ∀ {I} (u : I → bool), (∀ i, u i = false) + (∃ i, u i = true).
*)
Axiom IPO : ∀ {I} (u : I → bool), { ∀ i, u i = false } + { ∃ i, u i = true }.
(**)

Definition bool_of_sum {A B} (s : A + B) :=
  match s with
  | inl _ => false
  | inr _ => true
  end.

(* addition *)

Definition I_add_subtype' a b z :=
  let u (xy : T * T) :=
    let (x, y) := xy in
    ((z =? (x + y))%L && ip_subtype' a x && ip_subtype' b y)%bool
  in
  negb (bool_of_sumbool (IPO u)).

Arguments I_add_subtype' a b z%_L.

Theorem I_add_zero' a b : I_add_subtype' a b 0 = true.
Proof.
destruct_ic'.
progress unfold I_add_subtype'.
destruct (IPO _) as [H1| H1]; [ exfalso | easy ].
specialize (H1 (0, 0))%L.
cbn in H1.
rewrite rngl_add_0_r in H1.
rewrite (rngl_eqb_refl Heo) in H1.
do 2 rewrite ip_zero' in H1.
easy.
Qed.

Theorem I_add_add' a b :
  ∀ x y,
  I_add_subtype' a b x = true
  → I_add_subtype' a b y = true
  → I_add_subtype' a b (x + y)%L = true.
Proof.
destruct_ic'.
intros * Hx Hy.
progress unfold I_add_subtype' in Hx, Hy.
progress unfold I_add_subtype'.
destruct (IPO _) as [H1| H1] in Hx; [ easy | clear Hx ].
destruct (IPO _) as [H2| H2] in Hy; [ easy | clear Hy ].
destruct (IPO _) as [H3| H3] in |-*; [ exfalso | easy ].
destruct H1 as ((x1, y1) & H1).
destruct H2 as ((x2, y2) & H2).
move x2 before y1; move y2 before x2.
apply Bool.andb_true_iff in H1, H2.
destruct H1 as (H1, H13).
destruct H2 as (H2, H23).
apply Bool.andb_true_iff in H1, H2.
destruct H1 as (H11, H12).
destruct H2 as (H21, H22).
apply (rngl_eqb_eq Heo) in H11, H21.
subst x y.
specialize (H3 (x1 + x2, y1 + y2))%L.
cbn in H3.
rewrite rngl_add_add_add_swap in H3.
rewrite (rngl_eqb_refl Heo) in H3.
rewrite ip_add' in H3; [ | easy | easy ].
rewrite ip_add' in H3; [ | easy | easy ].
easy.
Qed.

Theorem I_add_opp' a b :
  ∀ x, I_add_subtype' a b x = true → I_add_subtype' a b (- x) = true.
Proof.
destruct_ic'.
intros * Hx.
progress unfold I_add_subtype' in Hx.
progress unfold I_add_subtype'.
destruct (IPO _) as [H1| H1] in Hx; [ easy | clear Hx ].
destruct (IPO _) as [H2| H2] in |-*; [ exfalso | easy ].
destruct H1 as ((x1, y1) & H1).
apply Bool.andb_true_iff in H1.
destruct H1 as (H1, H13).
apply Bool.andb_true_iff in H1.
destruct H1 as (H11, H12).
apply (rngl_eqb_eq Heo) in H11.
subst x.
specialize (H2 (- x1, - y1))%L.
cbn in H2.
rewrite (rngl_add_opp_r Hop) in H2.
rewrite (rngl_opp_add_distr Hop) in H2.
rewrite (rngl_eqb_refl Heo) in H2.
rewrite ip_opp' in H2; [ | easy ].
rewrite ip_opp' in H2; [ | easy ].
easy.
Qed.

Theorem I_add_mul_l' a b :
  ∀ x y, I_add_subtype' a b y = true → I_add_subtype' a b (x * y) = true.
Proof.
destruct_ic'.
intros * H.
progress unfold I_add_subtype' in H.
progress unfold I_add_subtype'.
destruct (IPO _) as [H1| H1] in H; [ easy | clear H ].
destruct (IPO _) as [H2| H2] in |-*; [ exfalso | easy ].
destruct H1 as ((x1, y1) & H1).
apply Bool.andb_true_iff in H1.
destruct H1 as (H1, H13).
apply Bool.andb_true_iff in H1.
destruct H1 as (H11, H12).
apply (rngl_eqb_eq Heo) in H11.
subst.
specialize (H2 (x * x1, x * y1))%L.
cbn in H2.
rewrite rngl_mul_add_distr_l in H2.
rewrite (rngl_eqb_refl Heo) in H2.
rewrite ip_mul_l' in H2; [ | easy ].
rewrite ip_mul_l' in H2; [ | easy ].
easy.
Qed.

Theorem I_add_mul_r' a b :
  ∀ x y, I_add_subtype' a b x = true → I_add_subtype' a b (x * y) = true.
Proof.
destruct_ic'.
intros * H.
progress unfold I_add_subtype' in H.
progress unfold I_add_subtype'.
destruct (IPO _) as [H1| H1] in H; [ easy | clear H ].
destruct (IPO _) as [H2| H2] in |-*; [ exfalso | easy ].
destruct H1 as ((x1, y1) & H1).
apply Bool.andb_true_iff in H1.
destruct H1 as (H1, H13).
apply Bool.andb_true_iff in H1.
destruct H1 as (H11, H12).
apply (rngl_eqb_eq Heo) in H11.
subst.
specialize (H2 (x1 * y, y1 * y))%L.
cbn in H2.
rewrite rngl_mul_add_distr_r in H2.
rewrite (rngl_eqb_refl Heo) in H2.
rewrite ip_mul_r' in H2; [ | easy ].
rewrite ip_mul_r' in H2; [ | easy ].
easy.
Qed.

Definition I_add' (a b : ideal' T) : ideal' T :=
  {| ip_subtype' := I_add_subtype' a b;
     ip_zero' := I_add_zero' a b;
     ip_add' := I_add_add' a b;
     ip_opp' := I_add_opp' a b;
     ip_mul_l' := I_add_mul_l' a b;
     ip_mul_r' := I_add_mul_r' a b |}.

(* multiplication *)

Definition I_mul_subtype' a b z :=
  let u (nll : nat * list T * list T) :=
    let '(n, lx, ly) := nll in
    ((length lx =? n) && (length ly =? n) &&
     ⋀ (x ∈ lx), ip_subtype' a x &&
     ⋀ (y ∈ ly), ip_subtype' b y &&
     (z =? ∑ (i = 1, n), lx.[i-1] * ly.[i-1])%L)%bool
  in
  negb (bool_of_sumbool (IPO u)).

Arguments I_mul_subtype' a b z%_L.

Theorem I_mul_zero' a b : I_mul_subtype' a b 0%L = true.
Proof.
destruct_ic'.
progress unfold I_mul_subtype'.
destruct (IPO _) as [H| H]; [ exfalso | easy ].
specialize (H (0, [], [])); cbn in H.
rewrite rngl_and_list_empty in H; [ | easy ].
rewrite rngl_and_list_empty in H; [ | easy ].
rewrite rngl_summation_empty in H; [ | easy ].
now rewrite (rngl_eqb_refl Heo) in H.
Qed.

Theorem I_mul_add' a b :
  ∀ x y,
  I_mul_subtype' a b x = true
  → I_mul_subtype' a b y = true
  → I_mul_subtype' a b (x + y)%L = true.
Proof.
destruct_ic'.
intros * Hx Hy.
progress unfold I_mul_subtype' in Hx, Hy.
progress unfold I_mul_subtype'.
destruct (IPO _) as [H1| H1] in Hx; [ easy | clear Hx ].
destruct (IPO _) as [H2| H2] in Hy; [ easy | clear Hy ].
destruct (IPO _) as [H3| H3] in |-*; [ exfalso | easy ].
destruct H1 as (((n1, lx1), ly1) & H1).
destruct H2 as (((n2, lx2), ly2) & H2).
move n2 before n1.
move lx2 before ly1; move ly2 before lx2.
apply Bool.andb_true_iff in H1, H2.
destruct H1 as (H1, H15).
destruct H2 as (H2, H25).
apply Bool.andb_true_iff in H1, H2.
destruct H1 as (H1, H14).
destruct H2 as (H2, H24).
apply Bool.andb_true_iff in H1, H2.
destruct H1 as (H1, H13).
destruct H2 as (H2, H23).
apply Bool.andb_true_iff in H1, H2.
destruct H1 as (H11, H12).
destruct H2 as (H21, H22).
apply Nat.eqb_eq in H11, H12, H21, H22.
apply (rngl_eqb_eq Heo) in H15, H25.
subst x y.
specialize (H3 (n1 + n2, lx1 ++ lx2, ly1 ++ ly2)).
cbn in H3.
do 2 rewrite List.length_app in H3.
rewrite H11, H12, H21, H22 in H3.
rewrite Nat.eqb_refl in H3.
do 2 rewrite rngl_and_list_app in H3.
rewrite H13, H14, H23, H24 in H3.
destruct (Nat.eq_dec n1 0) as [H1z| H1z]. {
  move H1z at top; subst n1.
  rewrite (rngl_summation_empty _ 1 0) in H3; [ | easy ].
  rewrite rngl_add_0_l in H3.
  rewrite Nat.add_0_l in H3.
  apply List.length_zero_iff_nil in H12, H11.
  subst lx1 ly1.
  do 2 rewrite List.app_nil_l in H3.
  now rewrite (rngl_eqb_refl Heo) in H3.
}
destruct (Nat.eq_dec n2 0) as [H2z| H2z]. {
  move H2z at top; subst n2.
  rewrite (rngl_summation_empty _ 1 0) in H3; [ | easy ].
  rewrite rngl_add_0_r in H3.
  rewrite Nat.add_0_r in H3.
  apply List.length_zero_iff_nil in H22, H21.
  subst lx2 ly2.
  cbn in H3.
  do 2 rewrite List.app_nil_r in H3.
  now rewrite (rngl_eqb_refl Heo) in H3.
}
rewrite (rngl_summation_shift 1 1) in H3; [ | flia H1z ].
rewrite (rngl_summation_shift 1 1) in H3; [ | flia H2z ].
rewrite (rngl_summation_shift 1 1) in H3; [ | flia H1z ].
rewrite Nat.sub_diag in H3.
rewrite Nat.add_sub_swap in H3; [ | flia H1z ].
rewrite rngl_summation_ub_add_distr in H3.
rewrite <- Nat.sub_succ_l in H3; [ | flia H1z ].
rewrite Nat_sub_succ_1 in H3.
rewrite (rngl_summation_shift n1 n1) in H3; [ | flia H2z ].
rewrite Nat.sub_diag in H3.
replace (n1 - 1 + n2 - n1) with (n2 - 1) in H3 by flia H1z H2z.
remember (∑ (i = 0, n1 - 1), _) as x in H3.
erewrite (rngl_summation_eq_compat _ _ 0 (n1 - 1)) in H3. 2: {
  intros i Hi.
  rewrite List.app_nth1; [ | rewrite H11; flia H1z Hi ].
  rewrite List.app_nth1; [ | rewrite H12; flia H1z Hi ].
  easy.
}
subst x.
remember (∑ (i = 0, n2 - 1), _) as x in H3.
erewrite (rngl_summation_eq_compat _ _ 0 (n2 - 1)) in H3. 2: {
  intros i Hi.
  rewrite List.app_nth2; [ | rewrite H11; flia H1z Hi ].
  rewrite List.app_nth2; [ | rewrite H12; flia H1z Hi ].
  rewrite H11, H12.
  replace (1 + (n1 + i) - 1 - n1) with (1 + i - 1) by flia.
  easy.
}
subst x.
rewrite (rngl_eqb_refl Heo) in H3.
easy.
Qed.

(* to be completed
Theorem I_mul_opp' a b :
  ∀ x, I_mul_subtype' a b x = true → I_mul_subtype' a b (- x) = true.
Proof.
...
destruct_ic.
intros * Hx.
destruct Hx as (n & la & lb & Hla & Hlb & Ha & Hb & Hx).
subst x.
progress unfold I_mul_subtype.
exists n, (List.map rngl_opp la), lb.
rewrite List.length_map.
split; [ easy | ].
split; [ easy | ].
split. {
  intros x Hx.
  apply List.in_map_iff in Hx.
  destruct Hx as (y & Hyx & Hy).
  subst x.
  now apply ip_opp, Ha.
}
split; [ easy | ].
rewrite (rngl_opp_summation Hop).
apply rngl_summation_eq_compat.
intros i Hi.
rewrite <- (rngl_mul_opp_l Hop).
progress f_equal.
rewrite (List_map_nth' 0%L); [ easy | flia Hi Hla ].
Qed.

Theorem I_mul_mul_l a b :
  ∀ x y, I_mul_subtype a b y → I_mul_subtype a b (x * y).
Proof.
destruct_ic.
intros * H.
destruct H as (n & la & lb & Hla & Hlb & Ha & Hb & H).
subst y.
progress unfold I_mul_subtype.
exists n, (List.map (rngl_mul x) la), lb.
rewrite List.length_map.
split; [ easy | ].
split; [ easy | ].
split. {
  intros z Hz.
  apply List.in_map_iff in Hz.
  destruct Hz as (y & Hxy & Hz).
  subst z.
  now apply ip_mul_l, Ha.
}
split; [ easy | ].
rewrite (rngl_mul_summation_distr_l Hos).
apply rngl_summation_eq_compat.
intros i Hi.
rewrite rngl_mul_assoc.
progress f_equal.
rewrite (List_map_nth' 0%L); [ easy | flia Hi Hla ].
Qed.

Theorem I_mul_mul_r a b :
  ∀ x y, I_mul_subtype a b x → I_mul_subtype a b (x * y).
Proof.
destruct_ic.
intros * H.
destruct H as (n & la & lb & Hla & Hlb & Ha & Hb & H).
subst x.
progress unfold I_mul_subtype.
exists n, la, (List.map (λ z, rngl_mul z y) lb).
rewrite List.length_map.
split; [ easy | ].
split; [ easy | ].
split; [ easy | ].
split. {
  intros z Hz.
  apply List.in_map_iff in Hz.
  destruct Hz as (x & Hxy & Hx).
  subst z.
  now apply ip_mul_r, Hb.
}
rewrite (rngl_mul_summation_distr_r Hos).
apply rngl_summation_eq_compat.
intros i Hi.
rewrite <- rngl_mul_assoc.
progress f_equal.
rewrite (List_map_nth' 0%L); [ easy | flia Hi Hlb ].
Qed.
*)

(* to be completed
Definition I_mul' (a b : ideal' T) : ideal' T :=
  {| ip_subtype' := I_mul_subtype' a b;
     ip_zero' := I_mul_zero' a b;
     ip_add' := I_mul_add' a b;
     ip_opp' := I_mul_opp' a b;
     ip_mul_l' := I_mul_mul_l a b;
     ip_mul_r' := I_mul_mul_r a b |}.

(* opposite *)

Theorem I_opp_add a :
  ∀ x y, ip_subtype a (- x) → ip_subtype a (- y) → ip_subtype a (- (x + y)%L).
Proof.
destruct_ic.
intros * Hx Hy.
apply ip_opp in Hx, Hy.
rewrite (rngl_opp_involutive Hop) in Hx, Hy.
apply ip_opp.
now apply ip_add.
Qed.

Theorem I_opp_mul_l a :
  ∀ x y, ip_subtype a (- y) → ip_subtype a (- (x * y)%L).
Proof.
destruct_ic.
intros * H.
apply ip_opp, ip_mul_l.
rewrite <- (rngl_opp_involutive Hop).
now apply ip_opp.
Qed.

Theorem I_opp_mul_r a :
  ∀ x y, ip_subtype a (- x) → ip_subtype a (- (x * y)%L).
Proof.
destruct_ic.
intros * H.
apply ip_opp, ip_mul_r.
rewrite <- (rngl_opp_involutive Hop).
now apply ip_opp.
Qed.

Definition I_opp (a : ideal T) : ideal T :=
  {| ip_subtype x := ip_subtype a (-x);
     ip_zero := ip_opp a 0 (ip_zero a);
     ip_add := I_opp_add a;
     ip_opp x := ip_opp a (-x);
     ip_mul_l := I_opp_mul_l a;
     ip_mul_r := I_opp_mul_r a |}.

(* ideal ring like op *)

Definition I_ring_like_op : ring_like_op (ideal T) :=
  {| rngl_zero := I_zero;
     rngl_add := I_add;
     rngl_mul := I_mul;
     rngl_opt_one := Some I_one;
     rngl_opt_opp_or_psub :=
       match rngl_opt_opp_or_psub T with
       | Some (inl _) => Some (inl I_opp)
       | _ => None
       end;
     rngl_opt_inv_or_pdiv := None;
     rngl_opt_is_zero_divisor := Some (λ _, True);
     rngl_opt_eq_dec := None;
     rngl_opt_leb := None |}.

End a.

Declare Scope ideal_scope.
Delimit Scope ideal_scope with I.
Bind Scope ideal_scope with ideal.

Notation "0" := I_zero : ideal_scope.
Notation "1" := I_one : ideal_scope.
Notation "a + b" := (I_add a b) : ideal_scope.
(*
Notation "a - b" := (rngl_sub a b) : ideal_scope.
Notation "a * b" := (rngl_mul a b) : ideal_scope.
Notation "- a" := (rngl_opp a) : ideal_scope.
*)

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ic : ideal_ctx T}.

(* ideal ring like prop *)

(* to be completed *)
Theorem I_add_comm : ∀ a b, (a + b)%I = (b + a)%I.
Proof.
intros.
progress unfold I_add.
Print ideal.
...

(*
Theorem I_add_assoc : let roi := I_ring_like_op in
  ∀ a b c : ideal P, (a + (b + c))%L = (a + b + c)%L.
Proof. intros; apply eq_ideal_eq, rngl_add_assoc. Qed.

Theorem I_add_0_l : let roi := I_ring_like_op in
  ∀ a : ideal P, (0 + a)%L = a.
Proof. intros; apply eq_ideal_eq, rngl_add_0_l. Qed.

Theorem I_mul_assoc : let roi := I_ring_like_op in
  ∀ a b c : ideal P, (a * (b * c))%L = (a * b * c)%L.
Proof. intros; apply eq_ideal_eq, rngl_mul_assoc. Qed.

Arguments rngl_opt_one T {ring_like_op}.

Theorem I_opt_mul_1_l : let roi := I_ring_like_op in
  if rngl_has_1 (ideal P) then ∀ a : ideal P, (1 * a)%L = a
  else not_applicable.
Proof.
intros; cbn.
remember (rngl_has_1 _) as oni eqn:Honi; symmetry in Honi.
destruct oni; [ | easy ].
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honi |-*.
  progress unfold roi in Honi; cbn in Honi.
  progress unfold I_opt_one in Honi; cbn in Honi.
  now destruct rngl_opt_one.
}
intros.
apply eq_ideal_eq; cbn.
specialize (rngl_mul_1_l Hon (i_val a)) as H1.
progress unfold rngl_one in H1.
progress unfold roi.
progress unfold I_ring_like_op.
progress unfold rngl_one; cbn.
progress unfold rngl_has_1 in Honi.
progress unfold roi in Honi; cbn in Honi.
progress unfold rngl_has_1 in Hon.
remember I_opt_one as ion eqn:Hion; symmetry in Hion.
progress unfold I_opt_one in Hion.
destruct ion as [ione| ]; [ | easy ].
clear Honi.
destruct (rngl_opt_one T) as [one| ]; [ | easy ].
clear Hon.
destruct (Bool.bool_dec _ _) as [Hone| ]; [ | easy ].
injection Hion; clear Hion; intros; subst ione; cbn.
easy.
Qed.

Theorem I_mul_add_distr_l : let roi := I_ring_like_op in
  ∀ a b c : ideal P, (a * (b + c))%L = (a * b + a * c)%L.
Proof. intros; apply eq_ideal_eq, rngl_mul_add_distr_l. Qed.

Theorem I_opt_mul_comm : let roi := I_ring_like_op in
  if rngl_mul_is_comm T then ∀ a b : ideal P, (a * b)%L = (b * a)%L
  else not_applicable.
Proof.
intros.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
intros; apply eq_ideal_eq; cbn.
now apply rngl_mul_comm.
Qed.

Theorem I_opt_mul_1_r : let roi := I_ring_like_op in
  if rngl_mul_is_comm T then not_applicable
  else if rngl_has_1 (ideal P) then ∀ a : ideal P, (a * 1)%L = a
  else not_applicable.
Proof.
intros; cbn.
destruct rngl_mul_is_comm; [ easy | ].
remember (rngl_has_1 _) as oni eqn:Honi; symmetry in Honi.
destruct oni; [ | easy ].
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honi |-*.
  progress unfold roi in Honi; cbn in Honi.
  progress unfold I_opt_one in Honi; cbn in Honi.
  now destruct rngl_opt_one.
}
intros.
apply eq_ideal_eq; cbn.
specialize (rngl_mul_1_r Hon (i_val a)) as H1.
progress unfold rngl_one in H1.
progress unfold roi.
progress unfold I_ring_like_op.
progress unfold rngl_one; cbn.
progress unfold rngl_has_1 in Honi.
progress unfold roi in Honi; cbn in Honi.
progress unfold rngl_has_1 in Hon.
remember I_opt_one as ion eqn:Hion; symmetry in Hion.
progress unfold I_opt_one in Hion.
destruct ion as [ione| ]; [ | easy ].
clear Honi.
destruct (rngl_opt_one T) as [one| ]; [ | easy ].
clear Hon.
destruct (Bool.bool_dec _ _) as [Hone| ]; [ | easy ].
injection Hion; clear Hion; intros; subst ione; cbn.
easy.
Qed.

Theorem I_opt_mul_add_distr_r : let roi := I_ring_like_op in
  if rngl_mul_is_comm T then not_applicable
  else ∀ a b c : ideal P, ((a + b) * c)%L = (a * c + b * c)%L.
Proof.
intros.
remember rngl_mul_is_comm as ic eqn:Hic; symmetry in Hic.
destruct ic; [ easy | ].
intros; apply eq_ideal_eq; cbn.
apply rngl_mul_add_distr_r.
Qed.

Theorem I_opt_add_opp_diag_l : let roi := I_ring_like_op in
  if rngl_has_opp (ideal P) then ∀ a : ideal P, (- a + a)%L = 0%L
  else not_applicable.
Proof.
intros.
specialize (eq_refl (@rngl_has_opp T ro)) as Hop.
unfold rngl_has_opp in Hop at 2.
unfold rngl_has_opp, rngl_opp; cbn.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
destruct os as [opp| psub]; [ | easy ].
intros; apply eq_ideal_eq, (rngl_add_opp_diag_l Hop).
Qed.

Theorem rngl_has_psub_I_has_psub :
  let roi := I_ring_like_op in
  rngl_has_psub T = rngl_has_psub (ideal P).
Proof.
progress unfold rngl_has_psub; cbn.
remember (rngl_opt_opp_or_psub T) as os eqn:Hos.
symmetry in Hos.
destruct os as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem I_opt_add_sub : let roi := I_ring_like_op in
  if rngl_has_psub (ideal P) then ∀ a b : ideal P, (a + b - b)%L = a
  else not_applicable.
Proof.
intros.
remember (rngl_has_psub (ideal P)) as sui eqn:Hsui; symmetry in Hsui.
destruct sui; [ | easy ].
specialize (rngl_has_psub_has_no_opp Hsui) as Hopi.
assert (Hsu : @rngl_has_psub T ro = true). {
  unfold rngl_has_psub in Hsui |-*.
  cbn in Hsui.
  destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
  now destruct os.
}
specialize (rngl_has_psub_has_no_opp Hsu) as Hop.
intros.
apply eq_ideal_eq; cbn.
specialize rngl_opt_add_sub as H1.
unfold rngl_has_psub in H1.
unfold rngl_sub, rngl_psub.
rewrite Hopi, Hsui.
unfold rngl_sub in H1.
rewrite Hsu, Hop in H1.
progress unfold rngl_has_psub in Hsui, Hsu.
progress unfold rngl_has_opp in Hopi, Hop.
progress unfold roi.
progress unfold roi in Hopi.
progress unfold roi in Hsui.
cbn in Hsui, Hopi, Hsu, Hop |-*.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
destruct os as [opp| psub]; [ easy | ].
unfold I_psub, I_add; cbn.
apply H1.
Qed.

Theorem I_opt_sub_add_distr :
  let roi := I_ring_like_op in
  if rngl_has_psub (ideal P) then
    ∀ a b c : ideal P, (a - (b + c))%L = (a - b - c)%L
  else not_applicable.
Proof.
intros.
remember (rngl_has_psub (ideal P)) as sui eqn:Hsui; symmetry in Hsui.
destruct sui; [ | easy ].
specialize (rngl_has_psub_has_no_opp Hsui) as Hopi.
assert (Hsu : @rngl_has_psub T ro = true). {
  unfold rngl_has_psub in Hsui |-*.
  cbn in Hsui.
  destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
  now destruct os.
}
specialize (rngl_has_psub_has_no_opp Hsu) as Hop.
intros.
apply eq_ideal_eq; cbn.
specialize rngl_opt_sub_add_distr as H1.
unfold rngl_has_psub in H1.
unfold rngl_sub, rngl_psub.
rewrite Hopi, Hsui.
unfold rngl_sub in H1.
rewrite Hsu, Hop in H1.
progress unfold rngl_has_psub in Hsui, Hsu.
progress unfold rngl_has_opp in Hopi, Hop.
progress unfold roi.
progress unfold roi in Hopi.
progress unfold roi in Hsui.
cbn in Hsui, Hopi, Hsu, Hop |-*.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
destruct os as [opp| psub]; [ easy | ].
unfold I_psub, I_add; cbn.
apply H1.
Qed.

Theorem I_opt_sub_0_l :
  let roi := I_ring_like_op in
  if rngl_has_psub (ideal P) then ∀ a : ideal P, (0 - a)%L = 0%L
  else not_applicable.
Proof.
intros.
remember (rngl_has_psub (ideal P)) as sui eqn:Hsui; symmetry in Hsui.
destruct sui; [ | easy ].
specialize (rngl_has_psub_has_no_opp Hsui) as Hopi.
assert (Hsu : @rngl_has_psub T ro = true). {
  unfold rngl_has_psub in Hsui |-*.
  cbn in Hsui.
  destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
  now destruct os.
}
specialize (rngl_has_psub_has_no_opp Hsu) as Hop.
intros.
apply eq_ideal_eq; cbn.
specialize rngl_opt_sub_0_l as H1.
unfold rngl_has_psub in H1.
unfold rngl_sub, rngl_psub.
rewrite Hopi, Hsui.
unfold rngl_sub in H1.
rewrite Hsu, Hop in H1.
progress unfold rngl_has_psub in Hsui, Hsu.
progress unfold rngl_has_opp in Hopi, Hop.
progress unfold roi.
progress unfold roi in Hopi.
progress unfold roi in Hsui.
cbn in Hsui, Hopi, Hsu, Hop |-*.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
destruct os as [opp| psub]; [ easy | ].
unfold I_psub, I_add; cbn.
apply H1.
Qed.

Theorem I_ord_le_dec :
  let roi := I_ring_like_op : ring_like_op (ideal P) in
  rngl_is_ordered (ideal P) = true →
  ∀ a b : ideal P, {(a ≤ b)%L} + {¬ (a ≤ b)%L}.
Proof.
intros roi Hor *.
specialize rngl_opt_ord as H1.
progress unfold rngl_is_ordered in Hor; cbn in Hor.
progress unfold I_opt_leb in Hor.
progress unfold rngl_is_ordered in H1.
destruct rngl_opt_leb; [ cbn in H1 | easy ].
specialize (rngl_ord_le_dec (i_val a) (i_val b)) as H2.
destruct H2 as [H2| H2]; [ left | right ]. {
  progress unfold rngl_le; cbn.
  progress unfold I_opt_leb.
  progress unfold rngl_le in H2.
  now destruct rngl_opt_leb.
} {
  intros H; apply H2; clear H2; rename H into H2.
  progress unfold rngl_le in H2; cbn in H2.
  progress unfold I_opt_leb in H2.
  progress unfold rngl_le.
  now destruct rngl_opt_leb.
}
Qed.

Theorem I_ord_le_refl :
  let roi := I_ring_like_op : ring_like_op (ideal P) in
  rngl_is_ordered (ideal P) = true →
  ∀ a : ideal P, (a ≤ a)%L.
Proof.
intros roi Hor *.
specialize rngl_opt_ord as H1.
progress unfold rngl_is_ordered in Hor; cbn in Hor.
progress unfold I_opt_leb in Hor.
progress unfold rngl_is_ordered in H1.
destruct rngl_opt_leb; [ cbn in H1 | easy ].
specialize (rngl_ord_le_refl (i_val a)) as H2.
progress unfold rngl_le; cbn.
progress unfold I_opt_leb.
progress unfold rngl_le in H2.
now destruct rngl_opt_leb.
Qed.

Theorem I_ord_le_antisymm :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  ∀ a b : ideal P, (a ≤ b)%L → (b ≤ a)%L → a = b.
Proof.
intros roi Hor a b Hab Hba.
specialize rngl_opt_ord as H1.
progress unfold rngl_is_ordered in Hor; cbn in Hor.
progress unfold I_opt_leb in Hor.
progress unfold rngl_is_ordered in H1.
destruct rngl_opt_leb; [ cbn in H1 | easy ].
specialize (rngl_ord_le_antisymm (i_val a) (i_val b)) as H2.
progress unfold rngl_le in Hab, Hba.
progress unfold rngl_le in H2.
progress unfold roi in Hab, Hba.
progress unfold I_ring_like_op in Hab, Hba.
cbn in Hab, Hba.
progress unfold I_opt_leb in Hab, Hba.
destruct rngl_opt_leb as [le| ]; [ | easy ].
apply eq_ideal_eq.
apply (H2 Hab Hba).
Qed.

Theorem I_ord_le_trans :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  ∀ a b c : ideal P, (a ≤ b)%L → (b ≤ c)%L → (a ≤ c)%L.
Proof.
intros roi Hor * Hab Hba.
specialize rngl_opt_ord as H1.
progress unfold rngl_is_ordered in Hor; cbn in Hor.
progress unfold I_opt_leb in Hor.
progress unfold rngl_is_ordered in H1.
destruct rngl_opt_leb; [ cbn in H1 | easy ].
specialize (rngl_ord_le_trans (i_val a) (i_val b) (i_val c)) as H2.
progress unfold rngl_le in Hab, Hba.
progress unfold rngl_le in H2.
progress unfold roi in Hab, Hba.
progress unfold I_ring_like_op in Hab, Hba.
progress unfold rngl_le.
progress unfold roi.
progress unfold I_ring_like_op.
cbn in Hab, Hba |-*.
progress unfold I_opt_leb in Hab, Hba.
progress unfold I_opt_leb.
destruct rngl_opt_leb as [le| ]; [ | easy ].
apply (H2 Hab Hba).
Qed.

Theorem rngl_is_ordered_ideal :
  let roi := I_ring_like_op : ring_like_op (ideal P) in
  rngl_is_ordered (ideal P) = rngl_is_ordered T.
Proof.
intros.
progress unfold rngl_is_ordered; cbn.
progress unfold I_opt_leb.
now destruct rngl_opt_leb.
Qed.

Theorem rngl_has_opp_or_psub_ideal :
  let roi := I_ring_like_op : ring_like_op (ideal P) in
  rngl_has_opp_or_psub (ideal P) = rngl_has_opp_or_psub T.
Proof.
intros.
progress unfold rngl_has_opp_or_psub; cbn.
destruct (rngl_opt_opp_or_psub T) as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem I_ord_add_le_mono_l :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  ∀ a b c : ideal P, (b ≤ c)%L ↔ (a + b ≤ a + c)%L.
Proof.
intros roi Hor; cbn.
progress unfold roi in Hor.
rewrite rngl_is_ordered_ideal in Hor.
remember (rngl_has_opp_or_psub (ideal P)) as os eqn:Hos.
symmetry in Hos.
progress unfold roi in Hos.
rewrite rngl_has_opp_or_psub_ideal in Hos.
intros.
specialize (rngl_add_le_mono_l Hor) as H2.
specialize (H2 (i_val a) (i_val b) (i_val c)).
progress unfold rngl_le in H2.
progress unfold rngl_le; cbn.
progress unfold I_opt_leb.
now destruct (rngl_opt_leb).
Qed.

Theorem I_ord_mul_le_compat_nonneg :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  if (rngl_has_1 (ideal P) && rngl_has_inv_or_pdiv (ideal P))%bool then
    ∀ a b c d : ideal P, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L
  else not_applicable.
Proof.
intros roi Hor; cbn.
now rewrite Bool.andb_false_r.
Qed.

Theorem I_ord_mul_le_compat_nonpos :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  if (rngl_has_1 (ideal P) && rngl_has_inv_or_pdiv (ideal P))%bool then
    ∀ a b c d : ideal P, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L
  else not_applicable.
Proof.
intros roi Hor; cbn.
now rewrite Bool.andb_false_r.
Qed.

Theorem I_ord_not_le :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  ∀ a b : ideal P, ¬ (a ≤ b)%L → a ≠ b ∧ (b ≤ a)%L.
Proof.
intros roi Hor.
intros * Hab.
specialize rngl_opt_ord as H1.
progress unfold rngl_is_ordered in Hor; cbn in Hor.
progress unfold I_opt_leb in Hor.
progress unfold rngl_is_ordered in H1.
destruct rngl_opt_leb; [ cbn in H1 | easy ].
specialize rngl_ord_not_le as H2.
specialize (H2 (i_val a) (i_val b)).
progress unfold rngl_le in Hab.
progress unfold rngl_le in H2.
progress unfold roi in Hab.
progress unfold I_ring_like_op in Hab.
progress unfold rngl_le.
progress unfold roi.
progress unfold I_ring_like_op.
cbn in Hab |-*.
progress unfold I_opt_leb in Hab.
progress unfold I_opt_leb.
destruct rngl_opt_leb as [le| ]. {
  specialize (H2 Hab).
  split; [ | easy ].
  intros H; subst b.
  now apply Hab; clear Hab.
}
now specialize (H2 Hab).
Qed.

Theorem I_opt_integral :
  let roi := I_ring_like_op in
  ∀ a b : ideal P,
  (a * b)%L = 0%L
   → a = 0%L ∨ b = 0%L ∨ rngl_is_zero_divisor a ∨ rngl_is_zero_divisor b.
Proof.
intros * Hab.
progress unfold rngl_is_zero_divisor.
progress unfold rngl_opt_is_zero_divisor.
cbn.
remember (rngl_opt_is_zero_divisor T) as ozd eqn:Hozd.
symmetry in Hozd.
apply eq_ideal_eq in Hab.
cbn in Hab.
apply rngl_opt_integral in Hab.
destruct Hab as [Hab| [Hab| Hab]]. {
  now left; apply eq_ideal_eq.
} {
  now right; left; apply eq_ideal_eq.
}
destruct ozd as [f| ]. {
  destruct Hab as [Hab| Hab]. {
    right; right; left.
    progress unfold rngl_is_zero_divisor in Hab.
    cbn in Hozd.
    destruct (rngl_opt_is_zero_divisor T); [ | easy ].
    now injection Hozd; clear Hozd; intros; subst f.
  } {
    right; right; right.
    progress unfold rngl_is_zero_divisor in Hab.
    cbn in Hozd.
    destruct (rngl_opt_is_zero_divisor T); [ | easy ].
    now injection Hozd; clear Hozd; intros; subst f.
  }
}
progress unfold rngl_is_zero_divisor in Hab.
rewrite Hozd in Hab.
now destruct Hab.
Qed.

Theorem i_val_rngl_mul_nat : let roi := I_ring_like_op in
  ∀ a i, i_val (rngl_mul_nat a i) = rngl_mul_nat (i_val a) i.
Proof.
intros.
induction i; [ easy | cbn ].
f_equal; apply IHi.
Qed.

Theorem I_characteristic_prop : let roi := I_ring_like_op in
  if rngl_has_1 (ideal P) then
    if rngl_characteristic T =? 0 then ∀ i : nat, rngl_of_nat (S i) ≠ 0%L
    else
      (∀ i : nat, 0 < i < rngl_characteristic T → rngl_of_nat i ≠ 0%L) ∧
      rngl_of_nat (rngl_characteristic T) = 0%L
  else not_applicable.
Proof.
intros; cbn.
remember (rngl_has_1 (ideal P)) as oni eqn:Honi; symmetry in Honi.
destruct oni; [ | easy ].
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honi |-*.
  progress unfold roi in Honi; cbn in Honi.
  progress unfold I_opt_one in Honi.
  now destruct (rngl_opt_one T).
}
specialize rngl_opt_characteristic_prop as H1.
rewrite Hon in H1.
rewrite if_bool_if_dec in H1 |-*.
progress unfold roi.
progress unfold I_ring_like_op.
progress unfold rngl_one; cbn.
progress unfold I_opt_one.
progress unfold rngl_has_1 in Hon.
progress unfold rngl_has_1 in Honi; cbn in Honi.
progress unfold I_opt_one in Honi.
destruct (Sumbool.sumbool_of_bool _) as [Hcz| Hcz]. {
  apply Nat.eqb_eq in Hcz.
  intros.
  apply neq_ideal_neq; cbn.
  specialize (H1 i) as H2.
  cbn in H2.
  specialize i_val_rngl_mul_nat as H3.
  progress unfold rngl_mul_nat in H3.
  progress unfold mul_nat in H3; cbn in H3.
  rewrite H3; cbn.
  progress unfold rngl_one in H2.
  destruct (rngl_opt_one T) as [one| ]; [ | easy ].
  now destruct (Bool.bool_dec (P one) true).
}
destruct H1 as (Hbef, Hch).
progress unfold rngl_of_nat.
progress unfold rngl_of_nat in Hch.
split. {
  intros i Hi.
  specialize (Hbef i Hi) as H1.
  apply neq_ideal_neq.
  rewrite i_val_rngl_mul_nat; cbn.
  progress unfold rngl_of_nat in H1.
  progress unfold rngl_one in H1.
  destruct (rngl_opt_one T) as [one| ]; [ | easy ].
  now destruct (Bool.bool_dec (P one) true).
}
apply eq_ideal_eq.
rewrite i_val_rngl_mul_nat; cbn.
progress unfold rngl_one in Hch.
destruct (rngl_opt_one T) as [one| ]; [ | easy ].
now destruct (Bool.bool_dec (P one) true).
Qed.

Fixpoint List_map {A B} (f : A → B) l :=
  match l with
  | nil => nil
  | (a :: t)%list => (f a :: List_map f t)%list
  end.

Definition I_ring_like_when_ord (Hor : rngl_is_ordered (ideal P) = true) :=
  {| rngl_ord_le_dec := I_ord_le_dec Hor;
     rngl_ord_le_refl := I_ord_le_refl Hor;
     rngl_ord_le_antisymm := I_ord_le_antisymm Hor;
     rngl_ord_le_trans := I_ord_le_trans Hor;
     rngl_ord_add_le_mono_l := I_ord_add_le_mono_l Hor;
     rngl_ord_mul_le_compat_nonneg := I_ord_mul_le_compat_nonneg Hor; (* fails *)
     rngl_ord_mul_le_compat_nonpos := I_ord_mul_le_compat_nonpos Hor;
     rngl_ord_not_le := I_ord_not_le Hor |}.

Theorem I_ring_like_ord :
  let roi := I_ring_like_op in
  if rngl_is_ordered (ideal P) then ring_like_ord (ideal P)
  else not_applicable.
Proof.
intros.
remember (rngl_is_ordered (ideal P)) as or eqn:Hor.
symmetry in Hor.
destruct or; [ | easy ].
apply (I_ring_like_when_ord Hor).
Qed.
*)

Definition I_ring_like_prop : ring_like_prop (ideal T) :=
  let roi := I_ring_like_op in
  {| rngl_mul_is_comm := rngl_mul_is_comm T;
     rngl_is_archimedean := false;
     rngl_is_alg_closed := false;
     rngl_characteristic := rngl_characteristic T;
     rngl_add_comm := I_add_comm;
     rngl_add_assoc := true; (*I_add_assoc;*)
     rngl_add_0_l := true; (*I_add_0_l;*)
     rngl_mul_assoc := true; (*I_mul_assoc;*)
     rngl_opt_mul_1_l := true; (*I_opt_mul_1_l;*)
     rngl_mul_add_distr_l := true; (*I_mul_add_distr_l;*)
     rngl_opt_mul_comm := true; (*I_opt_mul_comm;*)
     rngl_opt_mul_1_r := true; (*I_opt_mul_1_r;*)
     rngl_opt_mul_add_distr_r := true; (*I_opt_mul_add_distr_r;*)
     rngl_opt_add_opp_diag_l := true; (*I_opt_add_opp_diag_l;*)
     rngl_opt_add_sub := true; (*I_opt_add_sub;*)
     rngl_opt_sub_add_distr := true; (*I_opt_sub_add_distr;*)
     rngl_opt_sub_0_l := true; (*I_opt_sub_0_l;*)
     rngl_opt_mul_inv_diag_l := NA;
     rngl_opt_mul_inv_diag_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_integral := true; (*I_opt_integral;*)
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := true; (*I_characteristic_prop;*)
     rngl_opt_ord := NA; (*I_ring_like_ord;*)
     rngl_opt_archimedean := NA |}.
*)

End a.

(* attempt to implement ideals on finite or enumerable sets

(* finite or enumerable sets *)

Inductive eset T :=
  | E_finite : list T → eset T
  | E_infinite : (nat → T) → eset T.

Arguments E_finite {T} l%_L.

Axiom LPO : ∀ (u : nat → bool), ( ∀ i, u i = false ) + { i : nat | u i = true }.

Declare Scope eset_scope.
Delimit Scope eset_scope with E.
Bind Scope eset_scope with eset.

Definition eset_mem {T} {ro : ring_like_op T} x (s : eset T) :=
  match s with
  | E_finite l => List.existsb (rngl_eqb x) l
  | E_infinite _ u =>
      match LPO (λ i, rngl_eqb (u i) x) with
      | inl _ => false
      | inr _ => true
      end
  end.

Arguments eset_mem {T ro} x%_L s%_E.

Notation "x '∈' l" := (eset_mem x l = true) : eset_scope.

(* attempt to implement such ideals *)

Record ideal' {T} {ro : ring_like_op T} := mk_id
  { id_set : eset T;
    id_zero : (0%L ∈ id_set)%E;
    id_add : ∀ a b, (a ∈ id_set → b ∈ id_set → a + b ∈ id_set)%E;
    id_opp : ∀ a, (a ∈ id_set → -a ∈ id_set)%E;
    id_mul_l : ∀ a b, (b ∈ id_set → a * b ∈ id_set)%E;
    id_mul_r : ∀ a b, (a ∈ id_set → a * b ∈ id_set)%E }.

Arguments ideal' T {ro}.

Class ideal_ctx' T {ro : ring_like_op T} :=
  { ic_op' : rngl_has_opp T = true;
    ic_eo' : rngl_has_eq_dec_or_order T = true }.

Ltac destruct_ic' :=
  set (Hop := ic_op');
  set (Heo := ic_eo');
  set (Hos := rngl_has_opp_has_opp_or_psub Hop).

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ic : ideal_ctx' T}.

Theorem I_zero_zero' : (0 ∈ E_finite [0%L])%E.
Proof.
destruct_ic'.
apply Bool.orb_true_iff; left.
apply (rngl_eqb_refl Heo).
Qed.

Theorem I_zero_add' a b :
  (a ∈ E_finite [0%L])%E
  → (b ∈ E_finite [0%L])%E
  → (a + b ∈ E_finite [0%L])%E.
Proof.
destruct_ic'.
intros Ha Hb.
apply Bool.orb_true_iff in Ha, Hb.
apply Bool.orb_true_iff; left.
destruct Ha as [Ha| ]; [ | easy ].
destruct Hb as [Hb| ]; [ | easy ].
apply (rngl_eqb_eq Heo) in Ha, Hb; subst.
apply (rngl_eqb_eq Heo).
apply rngl_add_0_l.
Qed.

Theorem I_zero_opp' a : (a ∈ E_finite [0%L])%E → (- a ∈ E_finite [0%L])%E.
...

Definition I_zero' : ideal' T :=
  {| id_set := E_finite [0]%L;
     id_zero := I_zero_zero';
     id_add := I_zero_add';
     id_opp := I_zero_opp';
     id_mul_l := true;
     id_mul_r := true |}.

...

(* old stuff *)

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ic : ideal_ctx T}.

(* ideal ring like prop *)

Theorem I_add_comm : ∀ a b, (a + b)%I = (b + a)%I.
Proof.
intros.
progress unfold I_add.
Print I_add_subtype.
Theorem glop :
  ∀ a b z, I_add_subtype a b z → I_add_subtype b a z.
Proof.
intros * H.
destruct H as (x & y & Hz & Hx & Hy).
exists y, x.
now rewrite rngl_add_comm.
Qed.
Axiom pouet : ∀ A B (U V : A → B), (∀ x, U x = V x) → U = V.
...
specialize (pouet _ _ (I_add_subtype a b) (I_add_subtype b a)) as H2.
rewrite H2.
...
} {
Axiom toto :
  ∀ A (P Q : A → A → Prop),
  (∀ x y, P x y ↔ Q x y)
  → (∃ x y, P x y) = (∃ x y, Q x y).
apply toto.
intros.
split; intros (H1 & H2 & H3). {
  split; [ easy | ].
...
f_equal.
apply and_comm.
split. {
 intros H.
...
specialize (toto T) as H1.
set (P := λ x y, z = (x + y)%L ∧ ip_subtype a x ∧ ip_subtype b y).
set (Q := λ x y, z = (x + y)%L ∧ ip_subtype b x ∧ ip_subtype a y).
specialize (H1 P Q).
subst P Q.
cbn in H1.
...

Theorem I_add_assoc : let roi := I_ring_like_op in
  ∀ a b c : ideal P, (a + (b + c))%L = (a + b + c)%L.
Proof. intros; apply eq_ideal_eq, rngl_add_assoc. Qed.

Theorem I_add_0_l : let roi := I_ring_like_op in
  ∀ a : ideal P, (0 + a)%L = a.
Proof. intros; apply eq_ideal_eq, rngl_add_0_l. Qed.

Theorem I_mul_assoc : let roi := I_ring_like_op in
  ∀ a b c : ideal P, (a * (b * c))%L = (a * b * c)%L.
Proof. intros; apply eq_ideal_eq, rngl_mul_assoc. Qed.

Arguments rngl_opt_one T {ring_like_op}.

Theorem I_opt_mul_1_l : let roi := I_ring_like_op in
  if rngl_has_1 (ideal P) then ∀ a : ideal P, (1 * a)%L = a
  else not_applicable.
Proof.
intros; cbn.
remember (rngl_has_1 _) as oni eqn:Honi; symmetry in Honi.
destruct oni; [ | easy ].
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honi |-*.
  progress unfold roi in Honi; cbn in Honi.
  progress unfold I_opt_one in Honi; cbn in Honi.
  now destruct rngl_opt_one.
}
intros.
apply eq_ideal_eq; cbn.
specialize (rngl_mul_1_l Hon (i_val a)) as H1.
progress unfold rngl_one in H1.
progress unfold roi.
progress unfold I_ring_like_op.
progress unfold rngl_one; cbn.
progress unfold rngl_has_1 in Honi.
progress unfold roi in Honi; cbn in Honi.
progress unfold rngl_has_1 in Hon.
remember I_opt_one as ion eqn:Hion; symmetry in Hion.
progress unfold I_opt_one in Hion.
destruct ion as [ione| ]; [ | easy ].
clear Honi.
destruct (rngl_opt_one T) as [one| ]; [ | easy ].
clear Hon.
destruct (Bool.bool_dec _ _) as [Hone| ]; [ | easy ].
injection Hion; clear Hion; intros; subst ione; cbn.
easy.
Qed.

Theorem I_mul_add_distr_l : let roi := I_ring_like_op in
  ∀ a b c : ideal P, (a * (b + c))%L = (a * b + a * c)%L.
Proof. intros; apply eq_ideal_eq, rngl_mul_add_distr_l. Qed.

Theorem I_opt_mul_comm : let roi := I_ring_like_op in
  if rngl_mul_is_comm T then ∀ a b : ideal P, (a * b)%L = (b * a)%L
  else not_applicable.
Proof.
intros.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
intros; apply eq_ideal_eq; cbn.
now apply rngl_mul_comm.
Qed.

Theorem I_opt_mul_1_r : let roi := I_ring_like_op in
  if rngl_mul_is_comm T then not_applicable
  else if rngl_has_1 (ideal P) then ∀ a : ideal P, (a * 1)%L = a
  else not_applicable.
Proof.
intros; cbn.
destruct rngl_mul_is_comm; [ easy | ].
remember (rngl_has_1 _) as oni eqn:Honi; symmetry in Honi.
destruct oni; [ | easy ].
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honi |-*.
  progress unfold roi in Honi; cbn in Honi.
  progress unfold I_opt_one in Honi; cbn in Honi.
  now destruct rngl_opt_one.
}
intros.
apply eq_ideal_eq; cbn.
specialize (rngl_mul_1_r Hon (i_val a)) as H1.
progress unfold rngl_one in H1.
progress unfold roi.
progress unfold I_ring_like_op.
progress unfold rngl_one; cbn.
progress unfold rngl_has_1 in Honi.
progress unfold roi in Honi; cbn in Honi.
progress unfold rngl_has_1 in Hon.
remember I_opt_one as ion eqn:Hion; symmetry in Hion.
progress unfold I_opt_one in Hion.
destruct ion as [ione| ]; [ | easy ].
clear Honi.
destruct (rngl_opt_one T) as [one| ]; [ | easy ].
clear Hon.
destruct (Bool.bool_dec _ _) as [Hone| ]; [ | easy ].
injection Hion; clear Hion; intros; subst ione; cbn.
easy.
Qed.

Theorem I_opt_mul_add_distr_r : let roi := I_ring_like_op in
  if rngl_mul_is_comm T then not_applicable
  else ∀ a b c : ideal P, ((a + b) * c)%L = (a * c + b * c)%L.
Proof.
intros.
remember rngl_mul_is_comm as ic eqn:Hic; symmetry in Hic.
destruct ic; [ easy | ].
intros; apply eq_ideal_eq; cbn.
apply rngl_mul_add_distr_r.
Qed.

Theorem I_opt_add_opp_diag_l : let roi := I_ring_like_op in
  if rngl_has_opp (ideal P) then ∀ a : ideal P, (- a + a)%L = 0%L
  else not_applicable.
Proof.
intros.
specialize (eq_refl (@rngl_has_opp T ro)) as Hop.
unfold rngl_has_opp in Hop at 2.
unfold rngl_has_opp, rngl_opp; cbn.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
destruct os as [opp| psub]; [ | easy ].
intros; apply eq_ideal_eq, (rngl_add_opp_diag_l Hop).
Qed.

Theorem rngl_has_psub_I_has_psub :
  let roi := I_ring_like_op in
  rngl_has_psub T = rngl_has_psub (ideal P).
Proof.
progress unfold rngl_has_psub; cbn.
remember (rngl_opt_opp_or_psub T) as os eqn:Hos.
symmetry in Hos.
destruct os as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem I_opt_add_sub : let roi := I_ring_like_op in
  if rngl_has_psub (ideal P) then ∀ a b : ideal P, (a + b - b)%L = a
  else not_applicable.
Proof.
intros.
remember (rngl_has_psub (ideal P)) as sui eqn:Hsui; symmetry in Hsui.
destruct sui; [ | easy ].
specialize (rngl_has_psub_has_no_opp Hsui) as Hopi.
assert (Hsu : @rngl_has_psub T ro = true). {
  unfold rngl_has_psub in Hsui |-*.
  cbn in Hsui.
  destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
  now destruct os.
}
specialize (rngl_has_psub_has_no_opp Hsu) as Hop.
intros.
apply eq_ideal_eq; cbn.
specialize rngl_opt_add_sub as H1.
unfold rngl_has_psub in H1.
unfold rngl_sub, rngl_psub.
rewrite Hopi, Hsui.
unfold rngl_sub in H1.
rewrite Hsu, Hop in H1.
progress unfold rngl_has_psub in Hsui, Hsu.
progress unfold rngl_has_opp in Hopi, Hop.
progress unfold roi.
progress unfold roi in Hopi.
progress unfold roi in Hsui.
cbn in Hsui, Hopi, Hsu, Hop |-*.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
destruct os as [opp| psub]; [ easy | ].
unfold I_psub, I_add; cbn.
apply H1.
Qed.

Theorem I_opt_sub_add_distr :
  let roi := I_ring_like_op in
  if rngl_has_psub (ideal P) then
    ∀ a b c : ideal P, (a - (b + c))%L = (a - b - c)%L
  else not_applicable.
Proof.
intros.
remember (rngl_has_psub (ideal P)) as sui eqn:Hsui; symmetry in Hsui.
destruct sui; [ | easy ].
specialize (rngl_has_psub_has_no_opp Hsui) as Hopi.
assert (Hsu : @rngl_has_psub T ro = true). {
  unfold rngl_has_psub in Hsui |-*.
  cbn in Hsui.
  destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
  now destruct os.
}
specialize (rngl_has_psub_has_no_opp Hsu) as Hop.
intros.
apply eq_ideal_eq; cbn.
specialize rngl_opt_sub_add_distr as H1.
unfold rngl_has_psub in H1.
unfold rngl_sub, rngl_psub.
rewrite Hopi, Hsui.
unfold rngl_sub in H1.
rewrite Hsu, Hop in H1.
progress unfold rngl_has_psub in Hsui, Hsu.
progress unfold rngl_has_opp in Hopi, Hop.
progress unfold roi.
progress unfold roi in Hopi.
progress unfold roi in Hsui.
cbn in Hsui, Hopi, Hsu, Hop |-*.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
destruct os as [opp| psub]; [ easy | ].
unfold I_psub, I_add; cbn.
apply H1.
Qed.

Theorem I_opt_sub_0_l :
  let roi := I_ring_like_op in
  if rngl_has_psub (ideal P) then ∀ a : ideal P, (0 - a)%L = 0%L
  else not_applicable.
Proof.
intros.
remember (rngl_has_psub (ideal P)) as sui eqn:Hsui; symmetry in Hsui.
destruct sui; [ | easy ].
specialize (rngl_has_psub_has_no_opp Hsui) as Hopi.
assert (Hsu : @rngl_has_psub T ro = true). {
  unfold rngl_has_psub in Hsui |-*.
  cbn in Hsui.
  destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
  now destruct os.
}
specialize (rngl_has_psub_has_no_opp Hsu) as Hop.
intros.
apply eq_ideal_eq; cbn.
specialize rngl_opt_sub_0_l as H1.
unfold rngl_has_psub in H1.
unfold rngl_sub, rngl_psub.
rewrite Hopi, Hsui.
unfold rngl_sub in H1.
rewrite Hsu, Hop in H1.
progress unfold rngl_has_psub in Hsui, Hsu.
progress unfold rngl_has_opp in Hopi, Hop.
progress unfold roi.
progress unfold roi in Hopi.
progress unfold roi in Hsui.
cbn in Hsui, Hopi, Hsu, Hop |-*.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
destruct os as [opp| psub]; [ easy | ].
unfold I_psub, I_add; cbn.
apply H1.
Qed.

Theorem I_ord_le_dec :
  let roi := I_ring_like_op : ring_like_op (ideal P) in
  rngl_is_ordered (ideal P) = true →
  ∀ a b : ideal P, {(a ≤ b)%L} + {¬ (a ≤ b)%L}.
Proof.
intros roi Hor *.
specialize rngl_opt_ord as H1.
progress unfold rngl_is_ordered in Hor; cbn in Hor.
progress unfold I_opt_leb in Hor.
progress unfold rngl_is_ordered in H1.
destruct rngl_opt_leb; [ cbn in H1 | easy ].
specialize (rngl_ord_le_dec (i_val a) (i_val b)) as H2.
destruct H2 as [H2| H2]; [ left | right ]. {
  progress unfold rngl_le; cbn.
  progress unfold I_opt_leb.
  progress unfold rngl_le in H2.
  now destruct rngl_opt_leb.
} {
  intros H; apply H2; clear H2; rename H into H2.
  progress unfold rngl_le in H2; cbn in H2.
  progress unfold I_opt_leb in H2.
  progress unfold rngl_le.
  now destruct rngl_opt_leb.
}
Qed.

Theorem I_ord_le_refl :
  let roi := I_ring_like_op : ring_like_op (ideal P) in
  rngl_is_ordered (ideal P) = true →
  ∀ a : ideal P, (a ≤ a)%L.
Proof.
intros roi Hor *.
specialize rngl_opt_ord as H1.
progress unfold rngl_is_ordered in Hor; cbn in Hor.
progress unfold I_opt_leb in Hor.
progress unfold rngl_is_ordered in H1.
destruct rngl_opt_leb; [ cbn in H1 | easy ].
specialize (rngl_ord_le_refl (i_val a)) as H2.
progress unfold rngl_le; cbn.
progress unfold I_opt_leb.
progress unfold rngl_le in H2.
now destruct rngl_opt_leb.
Qed.

Theorem I_ord_le_antisymm :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  ∀ a b : ideal P, (a ≤ b)%L → (b ≤ a)%L → a = b.
Proof.
intros roi Hor a b Hab Hba.
specialize rngl_opt_ord as H1.
progress unfold rngl_is_ordered in Hor; cbn in Hor.
progress unfold I_opt_leb in Hor.
progress unfold rngl_is_ordered in H1.
destruct rngl_opt_leb; [ cbn in H1 | easy ].
specialize (rngl_ord_le_antisymm (i_val a) (i_val b)) as H2.
progress unfold rngl_le in Hab, Hba.
progress unfold rngl_le in H2.
progress unfold roi in Hab, Hba.
progress unfold I_ring_like_op in Hab, Hba.
cbn in Hab, Hba.
progress unfold I_opt_leb in Hab, Hba.
destruct rngl_opt_leb as [le| ]; [ | easy ].
apply eq_ideal_eq.
apply (H2 Hab Hba).
Qed.

Theorem I_ord_le_trans :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  ∀ a b c : ideal P, (a ≤ b)%L → (b ≤ c)%L → (a ≤ c)%L.
Proof.
intros roi Hor * Hab Hba.
specialize rngl_opt_ord as H1.
progress unfold rngl_is_ordered in Hor; cbn in Hor.
progress unfold I_opt_leb in Hor.
progress unfold rngl_is_ordered in H1.
destruct rngl_opt_leb; [ cbn in H1 | easy ].
specialize (rngl_ord_le_trans (i_val a) (i_val b) (i_val c)) as H2.
progress unfold rngl_le in Hab, Hba.
progress unfold rngl_le in H2.
progress unfold roi in Hab, Hba.
progress unfold I_ring_like_op in Hab, Hba.
progress unfold rngl_le.
progress unfold roi.
progress unfold I_ring_like_op.
cbn in Hab, Hba |-*.
progress unfold I_opt_leb in Hab, Hba.
progress unfold I_opt_leb.
destruct rngl_opt_leb as [le| ]; [ | easy ].
apply (H2 Hab Hba).
Qed.

Theorem rngl_is_ordered_ideal :
  let roi := I_ring_like_op : ring_like_op (ideal P) in
  rngl_is_ordered (ideal P) = rngl_is_ordered T.
Proof.
intros.
progress unfold rngl_is_ordered; cbn.
progress unfold I_opt_leb.
now destruct rngl_opt_leb.
Qed.

Theorem rngl_has_opp_or_psub_ideal :
  let roi := I_ring_like_op : ring_like_op (ideal P) in
  rngl_has_opp_or_psub (ideal P) = rngl_has_opp_or_psub T.
Proof.
intros.
progress unfold rngl_has_opp_or_psub; cbn.
destruct (rngl_opt_opp_or_psub T) as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem I_ord_add_le_mono_l :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  ∀ a b c : ideal P, (b ≤ c)%L ↔ (a + b ≤ a + c)%L.
Proof.
intros roi Hor; cbn.
progress unfold roi in Hor.
rewrite rngl_is_ordered_ideal in Hor.
remember (rngl_has_opp_or_psub (ideal P)) as os eqn:Hos.
symmetry in Hos.
progress unfold roi in Hos.
rewrite rngl_has_opp_or_psub_ideal in Hos.
intros.
specialize (rngl_add_le_mono_l Hor) as H2.
specialize (H2 (i_val a) (i_val b) (i_val c)).
progress unfold rngl_le in H2.
progress unfold rngl_le; cbn.
progress unfold I_opt_leb.
now destruct (rngl_opt_leb).
Qed.

Theorem I_ord_mul_le_compat_nonneg :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  if (rngl_has_1 (ideal P) && rngl_has_inv_or_pdiv (ideal P))%bool then
    ∀ a b c d : ideal P, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L
  else not_applicable.
Proof.
intros roi Hor; cbn.
now rewrite Bool.andb_false_r.
Qed.

Theorem I_ord_mul_le_compat_nonpos :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  if (rngl_has_1 (ideal P) && rngl_has_inv_or_pdiv (ideal P))%bool then
    ∀ a b c d : ideal P, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L
  else not_applicable.
Proof.
intros roi Hor; cbn.
now rewrite Bool.andb_false_r.
Qed.

Theorem I_ord_not_le :
  let roi := I_ring_like_op in
  rngl_is_ordered (ideal P) = true →
  ∀ a b : ideal P, ¬ (a ≤ b)%L → a ≠ b ∧ (b ≤ a)%L.
Proof.
intros roi Hor.
intros * Hab.
specialize rngl_opt_ord as H1.
progress unfold rngl_is_ordered in Hor; cbn in Hor.
progress unfold I_opt_leb in Hor.
progress unfold rngl_is_ordered in H1.
destruct rngl_opt_leb; [ cbn in H1 | easy ].
specialize rngl_ord_not_le as H2.
specialize (H2 (i_val a) (i_val b)).
progress unfold rngl_le in Hab.
progress unfold rngl_le in H2.
progress unfold roi in Hab.
progress unfold I_ring_like_op in Hab.
progress unfold rngl_le.
progress unfold roi.
progress unfold I_ring_like_op.
cbn in Hab |-*.
progress unfold I_opt_leb in Hab.
progress unfold I_opt_leb.
destruct rngl_opt_leb as [le| ]. {
  specialize (H2 Hab).
  split; [ | easy ].
  intros H; subst b.
  now apply Hab; clear Hab.
}
now specialize (H2 Hab).
Qed.

Theorem I_opt_integral :
  let roi := I_ring_like_op in
  ∀ a b : ideal P,
  (a * b)%L = 0%L
   → a = 0%L ∨ b = 0%L ∨ rngl_is_zero_divisor a ∨ rngl_is_zero_divisor b.
Proof.
intros * Hab.
progress unfold rngl_is_zero_divisor.
progress unfold rngl_opt_is_zero_divisor.
cbn.
remember (rngl_opt_is_zero_divisor T) as ozd eqn:Hozd.
symmetry in Hozd.
apply eq_ideal_eq in Hab.
cbn in Hab.
apply rngl_opt_integral in Hab.
destruct Hab as [Hab| [Hab| Hab]]. {
  now left; apply eq_ideal_eq.
} {
  now right; left; apply eq_ideal_eq.
}
destruct ozd as [f| ]. {
  destruct Hab as [Hab| Hab]. {
    right; right; left.
    progress unfold rngl_is_zero_divisor in Hab.
    cbn in Hozd.
    destruct (rngl_opt_is_zero_divisor T); [ | easy ].
    now injection Hozd; clear Hozd; intros; subst f.
  } {
    right; right; right.
    progress unfold rngl_is_zero_divisor in Hab.
    cbn in Hozd.
    destruct (rngl_opt_is_zero_divisor T); [ | easy ].
    now injection Hozd; clear Hozd; intros; subst f.
  }
}
progress unfold rngl_is_zero_divisor in Hab.
rewrite Hozd in Hab.
now destruct Hab.
Qed.

Theorem i_val_rngl_mul_nat : let roi := I_ring_like_op in
  ∀ a i, i_val (rngl_mul_nat a i) = rngl_mul_nat (i_val a) i.
Proof.
intros.
induction i; [ easy | cbn ].
f_equal; apply IHi.
Qed.

Theorem I_characteristic_prop : let roi := I_ring_like_op in
  if rngl_has_1 (ideal P) then
    if rngl_characteristic T =? 0 then ∀ i : nat, rngl_of_nat (S i) ≠ 0%L
    else
      (∀ i : nat, 0 < i < rngl_characteristic T → rngl_of_nat i ≠ 0%L) ∧
      rngl_of_nat (rngl_characteristic T) = 0%L
  else not_applicable.
Proof.
intros; cbn.
remember (rngl_has_1 (ideal P)) as oni eqn:Honi; symmetry in Honi.
destruct oni; [ | easy ].
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honi |-*.
  progress unfold roi in Honi; cbn in Honi.
  progress unfold I_opt_one in Honi.
  now destruct (rngl_opt_one T).
}
specialize rngl_opt_characteristic_prop as H1.
rewrite Hon in H1.
rewrite if_bool_if_dec in H1 |-*.
progress unfold roi.
progress unfold I_ring_like_op.
progress unfold rngl_one; cbn.
progress unfold I_opt_one.
progress unfold rngl_has_1 in Hon.
progress unfold rngl_has_1 in Honi; cbn in Honi.
progress unfold I_opt_one in Honi.
destruct (Sumbool.sumbool_of_bool _) as [Hcz| Hcz]. {
  apply Nat.eqb_eq in Hcz.
  intros.
  apply neq_ideal_neq; cbn.
  specialize (H1 i) as H2.
  cbn in H2.
  specialize i_val_rngl_mul_nat as H3.
  progress unfold rngl_mul_nat in H3.
  progress unfold mul_nat in H3; cbn in H3.
  rewrite H3; cbn.
  progress unfold rngl_one in H2.
  destruct (rngl_opt_one T) as [one| ]; [ | easy ].
  now destruct (Bool.bool_dec (P one) true).
}
destruct H1 as (Hbef, Hch).
progress unfold rngl_of_nat.
progress unfold rngl_of_nat in Hch.
split. {
  intros i Hi.
  specialize (Hbef i Hi) as H1.
  apply neq_ideal_neq.
  rewrite i_val_rngl_mul_nat; cbn.
  progress unfold rngl_of_nat in H1.
  progress unfold rngl_one in H1.
  destruct (rngl_opt_one T) as [one| ]; [ | easy ].
  now destruct (Bool.bool_dec (P one) true).
}
apply eq_ideal_eq.
rewrite i_val_rngl_mul_nat; cbn.
progress unfold rngl_one in Hch.
destruct (rngl_opt_one T) as [one| ]; [ | easy ].
now destruct (Bool.bool_dec (P one) true).
Qed.

Fixpoint List_map {A B} (f : A → B) l :=
  match l with
  | nil => nil
  | (a :: t)%list => (f a :: List_map f t)%list
  end.

Definition I_ring_like_when_ord (Hor : rngl_is_ordered (ideal P) = true) :=
  {| rngl_ord_le_dec := I_ord_le_dec Hor;
     rngl_ord_le_refl := I_ord_le_refl Hor;
     rngl_ord_le_antisymm := I_ord_le_antisymm Hor;
     rngl_ord_le_trans := I_ord_le_trans Hor;
     rngl_ord_add_le_mono_l := I_ord_add_le_mono_l Hor;
     rngl_ord_mul_le_compat_nonneg := I_ord_mul_le_compat_nonneg Hor; (* fails *)
     rngl_ord_mul_le_compat_nonpos := I_ord_mul_le_compat_nonpos Hor;
     rngl_ord_not_le := I_ord_not_le Hor |}.

Theorem I_ring_like_ord :
  let roi := I_ring_like_op in
  if rngl_is_ordered (ideal P) then ring_like_ord (ideal P)
  else not_applicable.
Proof.
intros.
remember (rngl_is_ordered (ideal P)) as or eqn:Hor.
symmetry in Hor.
destruct or; [ | easy ].
apply (I_ring_like_when_ord Hor).
Qed.

Definition I_ring_like_prop : ring_like_prop (ideal T) :=
  let roi := I_ring_like_op in
  {| rngl_mul_is_comm := rngl_mul_is_comm T;
     rngl_is_archimedean := false;
     rngl_is_alg_closed := false;
     rngl_characteristic := rngl_characteristic T;
     rngl_add_comm := I_add_comm;
     rngl_add_assoc := true; (*I_add_assoc;*)
     rngl_add_0_l := true; (*I_add_0_l;*)
     rngl_mul_assoc := true; (*I_mul_assoc;*)
     rngl_opt_mul_1_l := true; (*I_opt_mul_1_l;*)
     rngl_mul_add_distr_l := true; (*I_mul_add_distr_l;*)
     rngl_opt_mul_comm := true; (*I_opt_mul_comm;*)
     rngl_opt_mul_1_r := true; (*I_opt_mul_1_r;*)
     rngl_opt_mul_add_distr_r := true; (*I_opt_mul_add_distr_r;*)
     rngl_opt_add_opp_diag_l := true; (*I_opt_add_opp_diag_l;*)
     rngl_opt_add_sub := true; (*I_opt_add_sub;*)
     rngl_opt_sub_add_distr := true; (*I_opt_sub_add_distr;*)
     rngl_opt_sub_0_l := true; (*I_opt_sub_0_l;*)
     rngl_opt_mul_inv_diag_l := NA;
     rngl_opt_mul_inv_diag_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_integral := true; (*I_opt_integral;*)
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := true; (*I_characteristic_prop;*)
     rngl_opt_ord := NA; (*I_ring_like_ord;*)
     rngl_opt_archimedean := NA |}.

End a.
*)
