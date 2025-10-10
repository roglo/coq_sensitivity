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

(* ideal: non empty set type with some properties *)
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

(* for propositional and functional extensionalities *)
From Stdlib Require Import PropExtensionality.
From Stdlib Require Import FunctionalExtensionality.
(* provides the axioms:
- propositional_extensionality :
     ∀ P Q : Prop, P ↔ Q → P = Q.
- functional_extensionality_dep :
     ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x),
     (∀ x : A, f x = g x)
     → f = g
*)

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
     rngl_one := I_one;
     rngl_add := I_add;
     rngl_mul := I_mul;
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
*)
Notation "a * b" := (I_mul a b) : ideal_scope.
(*
Notation "- a" := (rngl_opp a) : ideal_scope.
*)

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ic : ideal_ctx T}.

Theorem eq_ideal_eq : ∀ a b,
  ip_subtype a = ip_subtype b
  → a = b.
Proof.
intros * Hab.
destruct a.
destruct b.
cbn in *.
subst.
f_equal.
apply proof_irrelevance.
apply proof_irrelevance.
apply proof_irrelevance.
apply proof_irrelevance.
apply proof_irrelevance.
Qed.

Theorem I_add_subtype_comm a b z : I_add_subtype a b z = I_add_subtype b a z.
Proof.
progress unfold I_add_subtype.
apply propositional_extensionality.
split; intros (x & y & H1 & H2 & H3). {
  exists y, x.
  now rewrite rngl_add_comm.
} {
  exists y, x.
  now rewrite rngl_add_comm.
}
Qed.

Theorem I_add_comm : ∀ a b, (a + b)%I = (b + a)%I.
Proof.
intros.
apply eq_ideal_eq.
apply functional_extensionality_dep.
intros z.
apply I_add_subtype_comm.
Qed.

(*
Print Assumptions eq_ideal_eq.
Print Assumptions I_add_comm.
*)

Theorem I_add_subtype_assoc_l a b c x z :
  ip_subtype a x
  → ip_subtype (b + c)%I z
  → I_add_subtype (a + b) c (x + z)%L.
Proof.
intros H1 H2.
cbn in H2.
progress unfold I_add_subtype; cbn.
progress unfold I_add_subtype in H2.
progress unfold I_add_subtype.
destruct H2 as (y & t & H & H2 & H3); subst z.
rename t into z.
move y before x; move z before y.
exists (x + y)%L, z.
split; [ apply rngl_add_assoc | ].
split; [ | easy ].
now exists x, y.
Qed.

Theorem I_add_subtype_assoc a b c x :
  I_add_subtype a (b + c) x = I_add_subtype (a + b) c x.
Proof.
destruct_ic.
apply propositional_extensionality.
split; intros (y & z & H & H1 & H2); subst x. {
  now apply I_add_subtype_assoc_l.
} {
  rewrite I_add_subtype_comm.
  rewrite I_add_comm.
  rewrite rngl_add_comm.
  apply I_add_subtype_assoc_l; [ easy | ].
  now rewrite I_add_comm.
}
Qed.

Theorem I_add_assoc : ∀ a b c, (a + (b + c))%I = ((a + b) + c)%I.
Proof.
intros.
apply eq_ideal_eq.
apply functional_extensionality_dep.
intros x; cbn.
apply I_add_subtype_assoc.
Qed.

Theorem I_add_subtype_0_l a x : I_add_subtype 0 a x = ip_subtype a x.
Proof.
destruct_ic.
progress unfold I_add_subtype; cbn.
apply propositional_extensionality.
split. {
  intros (y & z & H & H1 & H2); subst x y.
  now rewrite rngl_add_0_l.
} {
  intros H1.
  exists 0%L, x.
  now rewrite rngl_add_0_l.
}
Qed.

Theorem I_add_0_l a : (0 + a)%I = a.
Proof.
intros.
apply eq_ideal_eq; cbn.
apply functional_extensionality_dep.
apply I_add_subtype_0_l.
Qed.

Theorem forall_exists_exists_forall {A B} (da : A) (dn : B) P la :
  (∀ a, a ∈ la → ∃ n, P a n)
  → ∃ nl,
    ∀ i, i ∈ List.seq 0 (length nl) → P (List.nth i la da) (List.nth i nl dn).
Proof.
intros * Ha.
induction la as [| a]; [ now exists [] | ].
assert (H : ∀ a, a ∈ la → ∃ n, P a n). {
  intros b Hb.
  apply Ha.
  now right.
}
specialize (IHla H); clear H.
destruct IHla as (nl, H1).
destruct (Ha a (List.in_eq _ _)) as (na, Hna).
exists (na :: nl).
intros i Hi.
destruct i; [ easy | cbn ].
apply H1.
apply List.in_seq in Hi.
apply List.in_seq.
destruct Hi as (_, Hi); cbn in Hi.
split; [ easy | ].
now apply Nat.succ_lt_mono in Hi.
Qed.

(* to be completed *)
Theorem I_mul_subtype_assoc a b c x :
  I_mul_subtype a (b * c) x = I_mul_subtype (a * b) c x.
Proof.
destruct_ic.
apply propositional_extensionality.
split; intros (n & lx & lyz & Hx & Hyz & H1 & H2 & H); subst x. {
  cbn in H2.
  assert (H : ∀ yz, yz ∈ lyz → I_mul_subtype b c yz) by easy.
  clear H2; rename H into H2.
  progress unfold I_mul_subtype in H2.
  apply (forall_exists_exists_forall 0%L 0) in H2.
  destruct H2 as (nl, H2).
  cbn in H2.
  apply (forall_exists_exists_forall 0 []) in H2.
  destruct H2 as (nll1, H2).
  apply (forall_exists_exists_forall 0 []) in H2.
  destruct H2 as (nll2, H2).
...

cbn in H2.
Search (List.nth _ (List.seq _ _)).
...
rewrite List.seq_nth in H2.
...
Search ListDef.Forall.
...
Check glop.
specialize glop as H3.
specialize (H3 T 0%L).
(* chais pas *)
...
  assert
    (∃ ln llx lly,
     List.map
       (λ i,
        let lx := List.nth i llx
  progress unfold I_mul_subtype.
...
exists n, lx, ly.
split; [ easy | ].
split; [ easy | ].
split. {
  intros z Hz.
  exists n, lx, ly.
  split; [ easy | ].
  split; [ easy | ].
  split; [ easy | ].
  split. {
    intros y Hy'.
    specialize (H2 y Hy').
    destruct H2 as (n' & lx' & ly' & Hx' & Hy'' & H2 & H3 & H).
    subst y.
...
  destruct H2 as (y & t & H & H2 & H3); subst z.
  rename t into z.
  move y before x; move z before y.
  exists (x + y)%L, z.
  split; [ apply rngl_add_assoc | ].
  split; [ | easy ].
  now exists x, y.
} {
  progress unfold I_add_subtype in H1.
  progress unfold I_add_subtype.
  destruct H1 as (x & t & H & H1 & H3); subst y.
  rename t into y.
  exists x, (y + z)%L.
  split; [ symmetry; apply rngl_add_assoc | ].
  split; [ easy | ].
  now exists y, z.
}
...

Theorem I_mul_assoc a b c : (a * (b * c))%I = ((a * b) * c)%I.
Proof.
apply eq_ideal_eq; cbn.
apply functional_extensionality_dep.
apply I_add_subtype_0_l.
...

(*
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
specialize (rngl_mul_1_l (i_val a)) as H1.
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
specialize (rngl_mul_1_r (i_val a)) as H1.
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
now destruct rngl_opt_leb.
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
rewrite in H1.
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
     rngl_add_assoc := I_add_assoc;
     rngl_add_0_l := I_add_0_l;
     rngl_mul_assoc := I_mul_assoc;
     rngl_mul_1_l := true; (*I_opt_mul_1_l;*)
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
