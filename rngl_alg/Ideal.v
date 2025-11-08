(* Ideal.v *)

(* ideals on a RingLike *)

Set Nested Proofs Allowed.
Require Import Stdlib.Arith.Arith.
Import List.ListNotations.
Import Init.Nat.
Require Import RingLike.Utf8.
Require Import RingLike.Core.
Require Import RingLike.Misc.
Require Import RingLike.Utils.
Require Import RingLike.IterAdd.
Require Import RingLike.IterMax.
Require Import RingLike.Nat_algebra.

(* ideal: non empty set type with some properties *)
(* drawback: elementary properties, like commutativity of addition of ideals
   cannot be proven *)
(* another version of ideals using bool instead of Prop follows *)

Record ideal {T} {ro : ring_like_op T} := mk_ip
  { i_subset : T → Prop;
    i_zero : i_subset 0%L;
    i_add x y : i_subset x → i_subset y → i_subset (x + y)%L;
    i_opp x : i_subset x → i_subset (- x)%L;
    i_mul_l t x : i_subset x → i_subset (t * x)%L;
    i_mul_r x t : i_subset x → i_subset (x * t)%L }.

Declare Scope ideal_scope.
Delimit Scope ideal_scope with I.
Bind Scope ideal_scope with ideal.

Arguments ideal T {ro}.
Arguments i_subset {T ro} i%_I a%_L.
Arguments i_opp {T ro} i%_I x%_L.

Notation "x '∈' a" := (i_subset a x) : ideal_scope.

Class ideal_ctx T {ro : ring_like_op T} :=
  { ix_op : rngl_has_opp T = true }.

Ltac destruct_ix :=
  set (Hop := ix_op);
  set (Hos := rngl_has_opp_has_opp_or_psub Hop).

(* to be moved somewhere else, probably IterAdd.v *)

Definition rngl_is_additive_integral T {ro : ring_like_op T} :=
  (∀ a b : T, (a + b = 0 → a = 0 ∧ b = 0)%L).

Theorem eq_rngl_summation_list_zero
  {T} {ro : ring_like_op T} {rp : ring_like_prop T} {A} :
  rngl_is_additive_integral T
  → ∀ (l : list A) f,
  ∑ (i ∈ l), f i = 0%L
  → ∀ i, i ∈ l → f i = 0%L.
Proof.
intros Hai * Hs * Hl.
progress unfold iter_list in Hs.
revert i Hl.
induction l as [| a l]; intros; [ easy | ].
cbn in Hs.
rewrite rngl_add_0_l in Hs.
rewrite fold_left_rngl_add_fun_from_0 in Hs.
apply Hai in Hs.
destruct Hl as [Hl| Hl]; [ now subst a | ].
now apply IHl.
Qed.

Theorem eq_rngl_summation_zero
  {T} {ro : ring_like_op T} {rp : ring_like_prop T} :
  rngl_is_additive_integral T →
  ∀ a b f, ∑ (i = a, b), f i = 0%L
  → ∀ i, a ≤ i ≤ b → f i = 0%L.
Proof.
intros Hai * Hs * Hab.
apply (eq_rngl_summation_list_zero Hai (List.seq a (S b - a))).
rewrite rngl_summation_seq_summation.
rewrite Nat.add_sub_assoc.
rewrite Nat.add_comm, Nat.add_sub.
now rewrite Nat_sub_succ_1.
flia Hab.
flia Hab.
apply List.in_seq.
flia Hab.
Qed.

Theorem nat_is_additive_integral : rngl_is_additive_integral nat.
Proof.
intros a b Hab.
now apply Nat.eq_add_0.
Qed.

(* to be moved too *)
Theorem List_map_f_seq :
  ∀ A B d (f : A → B) la,
  (List.map (λ i, f (List.nth i la d)) (List.seq 0 (length la)) =
   List.map f la)%L.
Proof.
intros.
induction la as [| a]; [ easy | ].
cbn - [ List.nth ].
progress f_equal.
now rewrite List_map_seq.
Qed.

Notation "'∑' ( ( i , j ) ∈ l ) , g" :=
  (iter_list l (λ c '(i, j), (c + g)%L) 0%L)
  (at level 45, l at level 60,
   right associativity,
   format "'[hv  ' ∑  ( ( i ,  j )  ∈  l ) ,  '/' '[' g ']' ']'").

Theorem rngl_summation_list_pair {T} {ro : ring_like_op T}  :
  ∀ A l (f : A → A → T),
  ∑ ((x, y) ∈ l), f x y = ∑ (xy ∈ l), f (fst xy) (snd xy).
Proof.
intros.
progress unfold iter_list; cbn.
apply List_fold_left_ext_in.
now intros (x, y) z Hxy.
Qed.

Theorem forall_pair {A B} {P : A → B → Prop} :
  (∀ a b, P a b) ↔ (∀ ab, P (fst ab) (snd ab)).
Proof.
split; intros * H *; [ apply H | ].
apply (H (a, b)).
Qed.

Theorem forall_pair_in {A B P l} :
  (∀ ab : A * B, (fst ab, snd ab) ∈ l → P ab) ↔
  (∀ ab : A * B, ab ∈ l → P ab).
Proof.
intros.
now split; intros H * Hab; apply H; destruct ab.
Qed.

Theorem forall_in_seq {A B} da db la lb (P : A → B → Prop) :
  length la = length lb →
  (∀ i,
   i ∈ List.seq 0 (length la) → P (List.nth i la da) (List.nth i lb db)) ↔
  (∃ lab, la = List.map fst lab ∧ lb = List.map snd lab ∧
   ∀ ab, ab ∈ lab → P (fst ab) (snd ab)).
Proof.
intros * Hlab.
split; intros Hp. {
  exists (List.combine la lb).
  split. {
    clear P Hp.
    revert lb Hlab.
    induction la as [| a]; intros; [ easy | ].
    destruct lb; [ easy | ].
    cbn in Hlab |-*.
    apply Nat.succ_inj in Hlab.
    f_equal.
    now apply IHla.
  }
  split. {
    clear P Hp.
    revert la Hlab.
    induction lb as [| b]; intros. {
      apply List.length_zero_iff_nil in Hlab.
      now subst la.
    }
    destruct la; [ easy | ].
    cbn in Hlab |-*.
    apply Nat.succ_inj in Hlab.
    f_equal.
    now apply IHlb.
  }
  intros (a, b) Hab.
  apply (List.In_nth _ _ (da, db)) in Hab.
  destruct Hab as (i & Hi & Hab).
  rewrite List.length_combine in Hi.
  rewrite List.combine_nth in Hab; [ | easy ].
  injection Hab; clear Hab; intros; subst a b; cbn.
  apply Hp.
  apply List.in_seq.
  apply Nat.min_glb_lt_iff in Hi.
  easy.
} {
  intros i Hi.
  destruct Hp as (lab & Hla & Hlb & Hp).
  subst la lb.
  clear Hlab.
  apply List.in_seq in Hi.
  rewrite List.length_map in Hi.
  rewrite (List_map_nth' (da, db) da); [ | easy ].
  rewrite (List_map_nth' (da, db) db); [ | easy ].
  apply Hp.
  now apply List.nth_In.
}
Qed.

(* end to be added *)

(* for propositional and functional extensionalities *)
Require Import Stdlib.Logic.PropExtensionality.
Require Import Stdlib.Logic.FunctionalExtensionality.
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
Proof. destruct_ix; intros; subst; apply (rngl_opp_0 Hop). Qed.

Theorem I_zero_mul_l a b : b = 0%L → (a * b = 0)%L.
Proof.
destruct_ix.
intros; subst; apply (rngl_mul_0_r Hos).
Qed.

Theorem I_zero_mul_r a b : a = 0%L → (a * b = 0)%L.
Proof.
destruct_ix.
intros; subst; apply (rngl_mul_0_l Hos).
Qed.

(* addition *)

Definition I_add_subset a b z :=
  ∃ x y, (x ∈ a)%I ∧ (y ∈ b)%I ∧ z = (x + y)%L.

Arguments I_add_subset a b z%_L.

Theorem I_add_zero a b : I_add_subset a b 0%L.
Proof.
exists 0%L, 0%L.
split; [ apply i_zero | ].
split; [ apply i_zero | ].
symmetry; apply rngl_add_0_l.
Qed.

Theorem I_add_add a b :
  ∀ x y,
  I_add_subset a b x → I_add_subset a b y → I_add_subset a b (x + y)%L.
Proof.
intros * Hx Hy.
destruct Hx as (x1 & x2 & Hx & Hx1 & Hx2).
destruct Hy as (y1 & y2 & Hy & Hy1 & Hy2).
subst x y.
exists (x1 + y1)%L, (x2 + y2)%L.
split; [ now apply i_add | ].
split; [ now apply i_add | ].
do 2 rewrite rngl_add_assoc.
progress f_equal.
apply rngl_add_add_swap.
Qed.

Theorem I_add_opp a b : ∀ x, I_add_subset a b x → I_add_subset a b (- x).
Proof.
destruct_ix.
intros * Hx.
destruct Hx as (x1 & x2 & Hx & Hx1 & Hx2); subst.
exists (- x1)%L, (- x2)%L.
split; [ now apply i_opp | ].
split; [ now apply i_opp | ].
rewrite rngl_add_comm.
rewrite (rngl_add_opp_r Hop).
rewrite <- (rngl_opp_sub_distr Hop).
rewrite (rngl_sub_opp_r Hop).
now f_equal.
Qed.

Theorem I_add_mul_l a b :
  ∀ x y, I_add_subset a b y → I_add_subset a b (x * y).
Proof.
intros * H.
destruct H as (x1 & x2 & Hx & Hx1 & Hx2); subst.
exists (x * x1)%L, (x * x2)%L.
split; [ now apply i_mul_l | ].
split; [ now apply i_mul_l | ].
apply rngl_mul_add_distr_l.
Qed.

Theorem I_add_mul_r a b :
  ∀ x y, I_add_subset a b x → I_add_subset a b (x * y).
Proof.
intros * H.
destruct H as (x1 & x2 & Hx & Hx1 & Hx2); subst.
exists (x1 * y)%L, (x2 * y)%L.
split; [ now apply i_mul_r | ].
split; [ now apply i_mul_r | ].
apply rngl_mul_add_distr_r.
Qed.

(* multiplication *)

Definition I_mul_subset_prop a b z lxy :=
  length lxy ≠ 0 ∧
  (∀ x y, (x, y) ∈ lxy → (x ∈ a)%I ∧ (y ∈ b)%I) ∧
  z = ∑ ((x, y) ∈ lxy), x * y.

Definition I_mul_subset a b z := ∃ lxy, I_mul_subset_prop a b z lxy.

Arguments I_mul_subset a b z%_L.

Theorem I_mul_zero a b : I_mul_subset a b 0%L.
Proof.
destruct_ix.
exists [(0, 0)%L].
split; [ easy | ].
split. {
  cbn; intros x y Hxy; destruct Hxy as [Hxy| ]; [ | easy ].
  injection Hxy; clear Hxy; intros; subst x y.
  split; apply i_zero.
}
symmetry.
progress unfold iter_list; cbn.
rewrite (rngl_mul_0_l Hos).
apply rngl_add_0_l.
Qed.

Theorem I_mul_add a b :
  ∀ x y,
  I_mul_subset a b x → I_mul_subset a b y → I_mul_subset a b (x + y)%L.
Proof.
intros * Hx Hy.
destruct Hx as (lab1 & Hlab1 & Hab1 & Hx).
destruct Hy as (lab2 & Hlab2 & Hab2 & Hy).
subst x y.
progress unfold I_mul_subset.
progress unfold I_mul_subset_prop.
exists (lab1 ++ lab2).
rewrite List.length_app.
split; [ flia Hlab1 Hlab2 | ].
split. {
  intros x y Hxy.
  apply List.in_app_or in Hxy.
  now destruct Hxy; [ apply Hab1 | apply Hab2 ].
}
do 3 rewrite rngl_summation_list_pair.
symmetry; apply rngl_summation_list_app.
Qed.

Theorem I_mul_opp a b : ∀ x, I_mul_subset a b x → I_mul_subset a b (- x).
Proof.
destruct_ix.
intros z (lxy & Hlxy & Hab & Hz); subst z.
progress unfold I_mul_subset.
progress unfold I_mul_subset_prop.
exists (List.map (λ xy, (- fst xy, snd xy))%L lxy).
rewrite List.length_map.
split; [ easy | ].
split. {
  intros x y Hxy'.
  apply List.in_map_iff in Hxy'.
  destruct Hxy' as ((x', y') & Hxy' & Hxyl).
  injection Hxy'; clear Hxy'; intros; subst x y.
  specialize (Hab _ _ Hxyl).
  now split; [ apply i_opp | ].
}
do 2 rewrite rngl_summation_list_pair.
rewrite (rngl_opp_summation_list Hop).
rewrite rngl_summation_list_map; cbn.
apply rngl_summation_list_eq_compat.
intros i Hi.
now rewrite (rngl_mul_opp_l Hop).
Qed.

Theorem I_mul_mul_l a b :
  ∀ x y, I_mul_subset a b y → I_mul_subset a b (x * y).
Proof.
destruct_ix.
intros * (lxy & Hlxy & Hab & Hz).
subst y; rename x into t.
progress unfold I_mul_subset.
progress unfold I_mul_subset_prop.
exists (List.map (λ '(x, y), (t * x, y)%L) lxy).
rewrite List.length_map.
split; [ easy | ].
split. {
  intros x' y' Hxy'.
  apply List.in_map_iff in Hxy'.
  destruct Hxy' as ((x, y) & H & Hxy').
  injection H; clear H; intros; subst x' y'.
  specialize (Hab _ _ Hxy').
  now split; [ apply i_mul_l | ].
}
do 2 rewrite rngl_summation_list_pair.
rewrite (rngl_mul_summation_list_distr_l Hos).
rewrite rngl_summation_list_map.
apply rngl_summation_list_eq_compat.
intros (x, y) Hxy; cbn.
apply rngl_mul_assoc.
Qed.

Theorem I_mul_mul_r a b :
  ∀ x y, I_mul_subset a b x → I_mul_subset a b (x * y).
Proof.
destruct_ix.
intros * (lxy & Hlxy & Hab & Hz).
subst x; rename y into t.
progress unfold I_mul_subset.
progress unfold I_mul_subset_prop.
exists (List.map (λ '(x, y), (x, y * t)%L) lxy).
rewrite List.length_map.
split; [ easy | ].
split. {
  intros x y Hxy.
  apply List.in_map_iff in Hxy.
  destruct Hxy as ((x', y') & H & Hxy).
  injection H; clear H; intros; subst x y.
  specialize (Hab _ _ Hxy).
  now split; [ | apply i_mul_r ].
}
do 2 rewrite rngl_summation_list_pair.
rewrite (rngl_mul_summation_list_distr_r Hos).
rewrite rngl_summation_list_map.
apply rngl_summation_list_eq_compat.
intros (x, y) Hxy; cbn.
symmetry; apply rngl_mul_assoc.
Qed.

(* opposite *)

Theorem I_opp_add a :
  ∀ x y : T, (- x ∈ a)%I → (- y ∈ a)%I → (- (x + y)%L ∈ a)%I.
Proof.
destruct_ix.
intros * Hx Hy.
apply i_opp in Hx, Hy.
rewrite (rngl_opp_involutive Hop) in Hx, Hy.
apply i_opp.
now apply i_add.
Qed.

Theorem I_opp_mul_l a :
  ∀ t x : T, (- x ∈ a)%I → (- (t * x)%L ∈ a)%I.
Proof.
destruct_ix.
intros * H.
apply i_opp, i_mul_l.
rewrite <- (rngl_opp_involutive Hop).
now apply i_opp.
Qed.

Theorem I_opp_mul_r a :
  ∀ x t : T, (- x ∈ a)%I → (- (x * t)%L ∈ a)%I.
Proof.
destruct_ix.
intros * H.
apply i_opp, i_mul_r.
rewrite <- (rngl_opp_involutive Hop).
now apply i_opp.
Qed.

(* *)

Definition I_zero : ideal T :=
  {| i_subset a := a = 0%L;
     i_zero := eq_refl;
     i_add := I_zero_add;
     i_opp := I_zero_opp;
     i_mul_l := I_zero_mul_l;
     i_mul_r := I_zero_mul_r |}.

Definition I_one : ideal T :=
  {| i_subset a := True;
     i_zero := I;
     i_add _ _ _ _ := I;
     i_opp _ _ := I;
     i_mul_l _ _ _ := I;
     i_mul_r _ _ _ := I |}.

Definition I_add (a b : ideal T) : ideal T :=
  {| i_subset := I_add_subset a b;
     i_zero := I_add_zero a b;
     i_add := I_add_add a b;
     i_opp := I_add_opp a b;
     i_mul_l := I_add_mul_l a b;
     i_mul_r := I_add_mul_r a b |}.

Definition I_mul (a b : ideal T) : ideal T :=
  {| i_subset := I_mul_subset a b;
     i_zero := I_mul_zero a b;
     i_add := I_mul_add a b;
     i_opp := I_mul_opp a b;
     i_mul_l := I_mul_mul_l a b;
     i_mul_r := I_mul_mul_r a b |}.

Definition I_opp (a : ideal T) : ideal T :=
  {| i_subset x := i_subset a (-x);
     i_zero := i_opp a 0 (i_zero a);
     i_add := I_opp_add a;
     i_opp x := i_opp a (-x);
     i_mul_l := I_opp_mul_l a;
     i_mul_r := I_opp_mul_r a |}.

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

Theorem List_seq_rngl_summation_r {T} a lb (f : T → _) :
  List.seq a (∑ (i ∈ lb), f i) =
  List.fold_left (λ la d, la ++ List.seq (a + length la) d)
    (List.map f lb) [].
Proof.
intros.
revert a.
induction lb as [| b]; intros; [ easy | ].
rewrite rngl_summation_list_cons.
rewrite List.seq_app.
rewrite List.map_cons.
cbn - [ rngl_zero rngl_add ].
rewrite Nat.add_0_r.
rewrite IHlb.
clear IHlb.
remember (f b) as b'.
clear b Heqb'; rename b' into b.
revert a b.
induction lb as [| c]; intros; cbn; [ now rewrite List.app_nil_r | ].
rewrite List.length_seq.
rewrite Nat.add_0_r.
rewrite <- List.seq_app.
rewrite <- IHlb.
rewrite List.app_assoc.
rewrite <- List.seq_app.
rewrite <- IHlb.
now rewrite Nat.add_assoc.
Qed.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ix : ideal_ctx T}.

Theorem eq_ideal_eq : ∀ a b,
  i_subset a = i_subset b
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

Theorem I_add_subset_comm a b z : I_add_subset a b z = I_add_subset b a z.
Proof.
progress unfold I_add_subset.
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
apply I_add_subset_comm.
Qed.

Theorem I_add_subset_assoc_l a b c x z :
  (x ∈ a)%I → (z ∈ b + c)%I → I_add_subset (a + b) c (x + z)%L.
Proof.
intros H1 H2.
cbn in H2.
progress unfold I_add_subset; cbn.
progress unfold I_add_subset in H2.
progress unfold I_add_subset.
destruct H2 as (y & t & H & H2 & H3); subst z.
rename t into z.
move y before x; move z before y.
exists (x + y)%L, z.
split; [ now exists x, y | ].
split; [ easy | ].
apply rngl_add_assoc.
Qed.

Theorem I_add_subset_assoc a b c x :
  I_add_subset a (b + c) x = I_add_subset (a + b) c x.
Proof.
destruct_ix.
apply propositional_extensionality.
split; intros (y & z & H & H1 & H2); subst x. {
  now apply I_add_subset_assoc_l.
} {
  rewrite I_add_subset_comm.
  rewrite I_add_comm.
  rewrite rngl_add_comm.
  apply I_add_subset_assoc_l; [ easy | ].
  now rewrite I_add_comm.
}
Qed.

Theorem I_add_assoc : ∀ a b c, (a + (b + c))%I = ((a + b) + c)%I.
Proof.
intros.
apply eq_ideal_eq.
apply functional_extensionality_dep.
intros x; cbn.
apply I_add_subset_assoc.
Qed.

Theorem I_add_subset_0_l a x : I_add_subset 0 a x = (x ∈ a)%I.
Proof.
destruct_ix.
progress unfold I_add_subset; cbn.
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
apply I_add_subset_0_l.
Qed.

Theorem forall_exists_exists_forall {A B} (da : A) (db : B) P Q la :
  (∀ a, a ∈ la → P a ∧ ∃ n, Q a n)
  ↔ ∃ lb, length lb = length la ∧
    ∀ i,
    i ∈ List.seq 0 (length lb)
    → P (List.nth i la da) ∧ Q (List.nth i la da) (List.nth i lb db).
Proof.
intros.
split. {
  intros Ha.
  induction la as [| a]; [ now exists [] | ].
  assert (H : ∀ a, a ∈ la → P a ∧ ∃ n, Q a n). {
    intros b Hb.
    apply Ha.
    now right.
  }
  specialize (IHla H); clear H.
  destruct IHla as (nl & H1 & H2).
  destruct (Ha a (List.in_eq _ _)) as (HP & na & Hna).
  exists (na :: nl).
  split; [ now cbn; f_equal | ].
  intros i Hi.
  destruct i; [ easy | cbn ].
  apply H2.
  apply List.in_seq in Hi.
  apply List.in_seq.
  destruct Hi as (_, Hi); cbn in Hi.
  split; [ easy | ].
  now apply Nat.succ_lt_mono in Hi.
} {
  intros (lb & H1 & H2) * Ha.
  apply (List.In_nth _ _ da) in Ha.
  destruct Ha as (n & Hna & Ha).
  subst a.
  specialize (H2 n).
  assert (H : n ∈ List.seq 0 (length lb)). {
    rewrite H1.
    now apply List.in_seq.
  }
  specialize (H2 H); clear H.
  split; [ easy | ].
  now exists (List.nth n lb db).
}
Qed.

Theorem I_subset_mul_assoc_l :
  ∀ a b c x y z, (x ∈ a → y ∈ b → z ∈ c → x * y * z ∈ a * b * c)%I.
Proof.
intros * Ha Hb Hc.
exists [(x * y, z)]%L.
split; [ easy | ].
split. {
  intros x' y' Hxy.
  destruct Hxy as [Hxy| Hxy]; [ | easy ].
  injection Hxy; clear Hxy; intros; subst x' y'.
  split; [ | now apply Hc; left ].
  exists [(x, y)].
  split; [ easy | ].
  split. {
    intros x' y' Hxy.
    destruct Hxy as [Hxy| Hxy]; [ | easy ].
    now injection Hxy; clear Hxy; intros; subst x y.
  }
  progress unfold iter_list; cbn; symmetry.
  apply rngl_add_0_l.
}
progress unfold iter_list; cbn; symmetry.
apply rngl_add_0_l.
Qed.

Theorem I_subset_mul_assoc_r :
  ∀ a b c x y z, (x ∈ a → y ∈ b → z ∈ c → x * y * z ∈ a * (b * c))%I.
Proof.
intros * Ha Hb Hc.
exists [(x, y * z)]%L.
split; [ easy | ].
split. {
  intros x' y' Hxy.
  destruct Hxy as [Hxy| Hxy]; [ | easy ].
  injection Hxy; clear Hxy; intros; subst x' y'.
  split; [ easy | ].
  exists [(y, z)].
  split; [ easy | ].
  split. {
    intros x' y' Hxy.
    destruct Hxy as [Hxy| Hxy]; [ | easy ].
    now injection Hxy; clear Hxy; intros; subst x' y'.
  }
  progress unfold iter_list; cbn; symmetry.
  apply rngl_add_0_l.
}
progress unfold iter_list; cbn; symmetry.
rewrite rngl_add_0_l.
apply rngl_mul_assoc.
Qed.

Theorem I_subset_sum_mul_assoc_l {A} :
  ∀ a b c li (f g h : A → T),
  (∀ i, i ∈ li → (f i ∈ a)%I)
  → (∀ i, i ∈ li → (g i ∈ b)%I)
  → (∀ i, i ∈ li → (h i ∈ c)%I)
  → (∑ (i ∈ li), f i * g i * h i ∈ a * b * c)%I.
Proof.
intros * Ha Hb Hc.
induction li as [| i1]. {
  rewrite rngl_summation_list_empty; [ | easy ].
  apply i_zero.
}
rewrite rngl_summation_list_cons.
assert (H : ∀ i, i ∈ li → (f i ∈ a)%I). {
  now intros i Hi; apply Ha; right.
}
specialize (IHli H); clear H.
assert (H : ∀ i, i ∈ li → (g i ∈ b)%I). {
  now intros i Hi; apply Hb; right.
}
specialize (IHli H); clear H.
assert (H : ∀ i, i ∈ li → (h i ∈ c)%I). {
  now intros i Hi; apply Hc; right.
}
specialize (IHli H); clear H.
apply i_add; [ | apply IHli ].
clear - Ha Hb Hc.
apply I_subset_mul_assoc_l.
now apply Ha; left.
now apply Hb; left.
now apply Hc; left.
Qed.

Theorem I_subset_sum_mul_assoc_r {A} :
  ∀ a b c li (f g h : A → T),
  (∀ i, i ∈ li → (f i ∈ a)%I)
  → (∀ i, i ∈ li → (g i ∈ b)%I)
  → (∀ i, i ∈ li → (h i ∈ c)%I)
  → (∑ (i ∈ li), f i * g i * h i ∈ a * (b * c))%I.
Proof.
intros * Ha Hb Hc.
induction li as [| i1]. {
  rewrite rngl_summation_list_empty; [ | easy ].
  apply i_zero.
}
rewrite rngl_summation_list_cons.
assert (H : ∀ i, i ∈ li → (f i ∈ a)%I). {
  now intros i Hi; apply Ha; right.
}
specialize (IHli H); clear H.
assert (H : ∀ i, i ∈ li → (g i ∈ b)%I). {
  now intros i Hi; apply Hb; right.
}
specialize (IHli H); clear H.
assert (H : ∀ i, i ∈ li → (h i ∈ c)%I). {
  now intros i Hi; apply Hc; right.
}
specialize (IHli H); clear H.
apply i_add; [ | apply IHli ].
clear - Ha Hb Hc.
(**)
apply I_subset_mul_assoc_r.
(*
apply I_subset_mul_assoc_l.
*)
now apply Ha; left.
now apply Hb; left.
now apply Hc; left.
Qed.

Theorem I_subset_sum_sum_mul_assoc_l {A B} :
  ∀ a b c li lj (f g h : A → B → T),
  (∀ i j, i ∈ li → j ∈ lj i → (f i j ∈ a)%I)
  → (∀ i j, i ∈ li → j ∈ lj i → (g i j ∈ b)%I)
  → (∀ i j, i ∈ li → j ∈ lj i → (h i j ∈ c)%I)
  → (∑ (i ∈ li), ∑ (j ∈ lj i), f i j * g i j * h i j ∈ a * b * c)%I.
Proof.
destruct_ix.
intros * Ha Hb Hc.
induction li as [| i1]. {
  rewrite rngl_summation_list_empty; [ | easy ].
  exists [(0, 0)]%L.
  split; [ easy | ].
  split. {
    intros x y Hxy.
    destruct Hxy as [Hxy| Hxy]; [ | easy ].
    injection Hxy; clear Hxy; intros; subst x y.
    split; apply i_zero.
  }
  rewrite rngl_summation_list_pair; symmetry.
  rewrite rngl_summation_list_only_one.
  apply (rngl_mul_0_l Hos).
}
rewrite rngl_summation_list_cons.
assert (H : ∀ i j, i ∈ li → j ∈ lj i → (f i j ∈ a)%I). {
  now intros * Hi Hj; apply Ha; [ right | ].
}
specialize (IHli H); clear H.
assert (H : ∀ i j, i ∈ li → j ∈ lj i → (g i j ∈ b)%I). {
  now intros * Hi Hj; apply Hb; [ right | ].
}
specialize (IHli H); clear H.
assert (H : ∀ i j, i ∈ li → j ∈ lj i → (h i j ∈ c)%I). {
  now intros * Hi Hj; apply Hc; [ right | ].
}
specialize (IHli H); clear H.
apply i_add; [ | apply IHli ].
apply I_subset_sum_mul_assoc_l.
now intros i Hi; apply Ha; [ left | ].
now intros i Hi; apply Hb; [ left | ].
now intros i Hi; apply Hc; [ left | ].
Qed.

Theorem I_subset_sum_sum_mul_assoc_r {A B} :
  ∀ a b c li lj (f g h : A → B → T),
  (∀ i j, i ∈ li → j ∈ lj i → (f i j ∈ a)%I)
  → (∀ i j, i ∈ li → j ∈ lj i → (g i j ∈ b)%I)
  → (∀ i j, i ∈ li → j ∈ lj i → (h i j ∈ c)%I)
  → (∑ (i ∈ li), ∑ (j ∈ lj i), f i j * g i j * h i j ∈ a * (b * c))%I.
Proof.
destruct_ix.
intros * Ha Hb Hc.
induction li as [| i1]. {
  rewrite rngl_summation_list_empty; [ | easy ].
  exists [(0, 0)]%L.
  split; [ easy | ].
  split. {
    intros x y Hxy.
    destruct Hxy as [Hxy| Hxy]; [ | easy ].
    injection Hxy; clear Hxy; intros; subst x y.
    split; apply i_zero.
  }
  rewrite rngl_summation_list_pair; symmetry.
  rewrite rngl_summation_list_only_one.
  apply (rngl_mul_0_l Hos).
}
rewrite rngl_summation_list_cons.
assert (H : ∀ i j, i ∈ li → j ∈ lj i → (f i j ∈ a)%I). {
  now intros * Hi Hj; apply Ha; [ right | ].
}
specialize (IHli H); clear H.
assert (H : ∀ i j, i ∈ li → j ∈ lj i → (g i j ∈ b)%I). {
  now intros * Hi Hj; apply Hb; [ right | ].
}
specialize (IHli H); clear H.
assert (H : ∀ i j, i ∈ li → j ∈ lj i → (h i j ∈ c)%I). {
  now intros * Hi Hj; apply Hc; [ right | ].
}
specialize (IHli H); clear H.
apply i_add; [ | apply IHli ].
(**)
apply I_subset_sum_mul_assoc_r.
(*
apply I_subset_sum_mul_assoc_l.
*)
now intros i Hi; apply Ha; [ left | ].
now intros i Hi; apply Hb; [ left | ].
now intros i Hi; apply Hc; [ left | ].
Qed.

(* I_mul_subset a (b * c) z → I_mul_subset (a * b) c z *)
Theorem I_subset_mul_assoc_l_mul_assoc_r a b c :
  ∀ z, (z ∈ a * (b * c) → z ∈ (a * b) * c)%I.
Proof.
destruct_ix.
intros t Ht.
cbn in Ht.
progress unfold I_mul_subset in Ht.
destruct Ht as (lx_yz & Hlx_yz & Ha_bc & Ht).
remember (∀ x yz, _) as x in Ha_bc; subst x. (* renaming *)
rewrite rngl_summation_list_pair in Ht.
remember (∑ (x_yz ∈ _), _) as x in Ht; subst x. (* renaming *)
specialize ((proj1 forall_pair) Ha_bc) as H1.
cbn in H1.
clear Ha_bc; rename H1 into Ha_bc.
specialize ((proj1 forall_pair_in) Ha_bc) as H1.
cbn in H1.
clear Ha_bc; rename H1 into Ha_bc.
apply (forall_exists_exists_forall (0, 0)%L []) in Ha_bc.
destruct Ha_bc as (llyz & Hllyz & Hxyz).
remember (length lx_yz) as n eqn:Hn.
rename Hlx_yz into H; rename Hn into Hlx_yz; rename H into Hn.
move Hn before n; symmetry in Hlx_yz.
move Hlx_yz before Hllyz.
move llyz before lx_yz.
rewrite Hllyz in Hxyz.
set (P u v := (fst u ∈ a)%I ∧ I_mul_subset_prop b c (snd u) v).
specialize (forall_in_seq (0, 0)%L [] lx_yz llyz P) as H1.
rewrite Hlx_yz, Hllyz in H1.
specialize (H1 eq_refl).
subst P; cbn in H1.
specialize (proj1 H1) as H2; clear H1.
specialize (H2 Hxyz).
clear Hxyz; rename H2 into Hxyz.
destruct Hxyz as (lxyz & Hllyzm & Hlx_yzm & Hxyz).
subst lx_yz llyz.
move Hllyz before Hlx_yz.
rewrite List.length_map in Hlx_yz, Hllyz.
clear Hlx_yz; rename Hllyz into Hlxyz.
rewrite rngl_summation_list_map in Ht.
remember (∀ xyz, _) as x in Hxyz; subst x. (* renaming *)
remember (∑ (xyz ∈ _), _) as x in Ht; subst x. (* renaming *)
assert (∀ xyz, xyz ∈ lxyz → snd (fst xyz) = ∑ ((y, z) ∈ snd xyz), y * z). {
  intros * H.
  now specialize (Hxyz _ H) as (Ha & Hllxyz & Hbc & H1).
}
erewrite rngl_summation_list_eq_compat in Ht; [ | now intros; rewrite H ].
clear H.
cbn in Ht.
erewrite rngl_summation_list_eq_compat in Ht. 2: {
  intros i Hi.
  rewrite rngl_summation_list_pair.
  rewrite (rngl_mul_summation_list_distr_l Hos).
  erewrite rngl_summation_list_eq_compat. 2: {
    intros j Hj.
    rewrite rngl_mul_assoc.
    reflexivity.
  }
  remember (∑ (yz ∈ _), _) as x in |-*; subst x. (* renaming *)
  reflexivity.
}
clear - Ht Hxyz.
remember (∑ (xyz ∈ _), _) as x in Ht; subst x. (* renaming *)
subst t.
(**)
apply I_subset_sum_sum_mul_assoc_l. {
  intros * Hi Hj.
  now specialize (Hxyz _ Hi).
} {
  intros * Hi Hj.
  specialize (Hxyz _ Hi).
  destruct Hxyz as (_, H).
  destruct H as (lli & H1 & H2).
  destruct j as (j, k).
  now specialize (H1 j k Hj).
} {
  intros * Hi Hj.
  specialize (Hxyz _ Hi).
  destruct Hxyz as (_, H).
  destruct H as (lli & H1 & H2).
  destruct j as (j, k).
  now specialize (H1 j k Hj).
}
Qed.

(* I_mul_subset (a * b) c z → I_mul_subset a (b * c) z *)
Theorem I_subset_mul_assoc_l_mul_assoc_l a b c :
  ∀ z, (z ∈ (a * b) * c → z ∈ a * (b * c))%I.
Proof.
destruct_ix.
intros t Ht.
cbn in Ht.
progress unfold I_mul_subset in Ht.
destruct Ht as (lx_yz & Hlx_yz & Ha_bc & Ht).
remember (∀ x yz, _) as x in Ha_bc; subst x. (* renaming *)
rewrite rngl_summation_list_pair in Ht.
remember (∑ (x_yz ∈ _), _) as x in Ht; subst x. (* renaming *)
specialize ((proj1 forall_pair) Ha_bc) as H1.
cbn in H1.
clear Ha_bc; rename H1 into Ha_bc.
specialize ((proj1 forall_pair_in) Ha_bc) as H1.
cbn in H1.
clear Ha_bc; rename H1 into Ha_bc.
(**)
assert (H : ∀ ab, ab ∈ lx_yz → (snd ab ∈ c)%I ∧ I_mul_subset a b (fst ab)). {
  intros ab Hab.
  now specialize (Ha_bc ab Hab).
}
apply (forall_exists_exists_forall (0, 0)%L []) in H.
clear Ha_bc; rename H into Ha_bc.
(*
apply (forall_exists_exists_forall (0, 0)%L []) in Ha_bc.
*)
destruct Ha_bc as (llyz & Hllyz & Hxyz).
remember (length lx_yz) as n eqn:Hn.
rename Hlx_yz into H; rename Hn into Hlx_yz; rename H into Hn.
move Hn before n; symmetry in Hlx_yz.
move Hlx_yz before Hllyz.
move llyz before lx_yz.
rewrite Hllyz in Hxyz.
(**)
set (P u v := (snd u ∈ c)%I ∧ I_mul_subset_prop a b (fst u) v).
(*
set (P u v := (fst u ∈ a)%I ∧ I_mul_subset_prop b c (snd u) v).
*)
specialize (forall_in_seq (0, 0)%L [] lx_yz llyz P) as H1.
rewrite Hlx_yz, Hllyz in H1.
specialize (H1 eq_refl).
subst P; cbn in H1.
specialize (proj1 H1) as H2; clear H1.
specialize (H2 Hxyz).
clear Hxyz; rename H2 into Hxyz.
destruct Hxyz as (lxyz & Hllyzm & Hlx_yzm & Hxyz).
subst lx_yz llyz.
move Hllyz before Hlx_yz.
rewrite List.length_map in Hlx_yz, Hllyz.
clear Hlx_yz; rename Hllyz into Hlxyz.
rewrite rngl_summation_list_map in Ht.
remember (∀ xyz, _) as x in Hxyz; subst x. (* renaming *)
remember (∑ (xyz ∈ _), _) as x in Ht; subst x. (* renaming *)
(**)
assert (∀ xyz, xyz ∈ lxyz → fst (fst xyz) = ∑ ((y, z) ∈ snd xyz), y * z). {
  intros * H.
  now specialize (Hxyz _ H) as (Ha & Hllxyz & Hbc & H1).
}
(*
assert (∀ xyz, xyz ∈ lxyz → snd (fst xyz) = ∑ ((y, z) ∈ snd xyz), y * z). {
  intros * H.
  now specialize (Hxyz _ H) as (Ha & Hllxyz & Hbc & H1).
}
*)
erewrite rngl_summation_list_eq_compat in Ht; [ | now intros; rewrite H ].
clear H.
cbn in Ht.
erewrite rngl_summation_list_eq_compat in Ht. 2: {
  intros i Hi.
  rewrite rngl_summation_list_pair.
(**)
  rewrite (rngl_mul_summation_list_distr_r Hos).
(*
  rewrite (rngl_mul_summation_list_distr_l Hos).
  erewrite rngl_summation_list_eq_compat. 2: {
    intros j Hj.
    rewrite rngl_mul_assoc.
    reflexivity.
  }
*)
  remember (∑ (yz ∈ _), _) as x in |-*; subst x. (* renaming *)
  reflexivity.
}
clear - Ht Hxyz.
remember (∑ (xyz ∈ _), _) as x in Ht; subst x. (* renaming *)
subst t.
(**)
apply I_subset_sum_sum_mul_assoc_r. {
  intros * Hi Hj.
  specialize (Hxyz _ Hi).
  destruct Hxyz as (_, H).
  destruct H as (lli & H1 & H2).
  destruct j as (j, k).
  now specialize (H1 j k Hj).
} {
  intros * Hi Hj.
  specialize (Hxyz _ Hi).
  destruct Hxyz as (_, H).
  destruct H as (lli & H1 & H2).
  destruct j as (j, k).
  now specialize (H1 j k Hj).
} {
  intros * Hi Hj.
  now specialize (Hxyz _ Hi).
}
(*
apply I_subset_sum_sum_mul_assoc_l. {
  intros * Hi Hj.
  now specialize (Hxyz _ Hi).
} {
  intros * Hi Hj.
  specialize (Hxyz _ Hi).
  destruct Hxyz as (_, H).
  destruct H as (lli & H1 & H2).
  destruct j as (j, k).
  now specialize (H1 j k Hj).
} {
  intros * Hi Hj.
  specialize (Hxyz _ Hi).
  destruct Hxyz as (_, H).
  destruct H as (lli & H1 & H2).
  destruct j as (j, k).
  now specialize (H1 j k Hj).
}
*)
Qed.

Theorem I_mul_subset_assoc a b c x :
  I_mul_subset a (b * c) x = I_mul_subset (a * b) c x.
Proof.
apply propositional_extensionality.
split.
now apply I_subset_mul_assoc_l_mul_assoc_r.
now apply I_subset_mul_assoc_l_mul_assoc_l.
Qed.

Theorem I_mul_assoc a b c : (a * (b * c))%I = ((a * b) * c)%I.
Proof.
apply eq_ideal_eq; cbn.
apply functional_extensionality_dep.
apply I_mul_subset_assoc.
Qed.

Theorem I_mul_subset_1_l a :
  ∀ x, I_mul_subset 1 a x = (x ∈ a)%I.
Proof.
destruct_ix.
intros.
apply propositional_extensionality.
split. {
  intros (lxy & Hlxy & H1 & H); subst x.
  rewrite rngl_summation_list_pair.
  induction lxy as [| (x, y)]; [ easy | ].
  clear Hlxy.
  destruct (Nat.eq_dec (length lxy) 0) as [Hnz| Hnz]. {
    apply List.length_zero_iff_nil in Hnz.
    subst lxy.
    rewrite rngl_summation_list_only_one.
    apply i_mul_l; cbn.
    now apply (H1 x y); left.
  }
  specialize (IHlxy Hnz).
  rewrite rngl_summation_list_cons; cbn.
  apply i_add. {
    apply i_mul_l.
    now apply (H1 x y); left.
  }
  apply IHlxy.
  intros x' y' Hxy'.
  now apply H1; right.
} {
  intros Hax.
  exists [(1%L, x)].
  split; [ easy | ].
  split. {
    intros y z Hyz.
    destruct Hyz as [Hy| Hy]; [ | easy ].
    now injection Hy; clear Hy; intros; subst y z.
  }
  rewrite rngl_summation_list_pair.
  rewrite rngl_summation_list_only_one.
  cbn; symmetry.
  apply rngl_mul_1_l.
}
Qed.

Theorem I_mul_1_l : ∀ a : ideal T, (1 * a)%I = a.
Proof.
intros.
apply eq_ideal_eq; cbn.
apply functional_extensionality_dep.
intros.
apply I_mul_subset_1_l.
Qed.

(* to be completed
Theorem I_mul_add_distr_l :
  ∀ a b c : ideal T, (a * (b + c))%I = (a * b + a * c)%I.
...
*)

Theorem I_mul_subset_comm :
  rngl_mul_is_comm T = true →
  ∀ a b x, I_mul_subset a b x = I_mul_subset b a x.
Proof.
intros Hic *.
progress unfold I_mul_subset.
progress unfold I_mul_subset_prop.
apply propositional_extensionality.
split; intros (lxy & Hlxy & H1 & H). {
  exists (List.map (λ xy, (snd xy, fst xy)) lxy).
  rewrite List.length_map.
  split; [ easy | ].
  split. {
    intros y z Hyz.
    apply List.in_map_iff in Hyz.
    destruct Hyz as ((u, v) & Hu & Huv).
    injection Hu; clear Hu; intros; subst u v.
    rewrite and_comm.
    now apply H1.
  }
  subst x.
  do 2 rewrite rngl_summation_list_pair.
  rewrite rngl_summation_list_map; cbn.
  apply rngl_summation_list_eq_compat.
  intros.
  apply (rngl_mul_comm Hic).
} {
  exists (List.map (λ xy, (snd xy, fst xy)) lxy).
  rewrite List.length_map.
  split; [ easy | ].
  split. {
    intros y z Hyz.
    apply List.in_map_iff in Hyz.
    destruct Hyz as ((u, v) & Hu & Huv).
    injection Hu; clear Hu; intros; subst u v.
    rewrite and_comm.
    now apply H1.
  }
  subst x.
  do 2 rewrite rngl_summation_list_pair.
  rewrite rngl_summation_list_map; cbn.
  apply rngl_summation_list_eq_compat.
  intros.
  apply (rngl_mul_comm Hic).
}
Qed.

Theorem I_opt_mul_comm :
  if rngl_mul_is_comm T then ∀ a b : ideal T, (a * b)%I = (b * a)%I
  else not_applicable.
Proof.
remember (rngl_mul_is_comm T) as ic eqn:Hic.
symmetry in Hic.
destruct ic; [ | easy ].
intros.
apply eq_ideal_eq; cbn.
apply functional_extensionality_dep.
intros.
apply (I_mul_subset_comm Hic).
Qed.

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

(* to be completed
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
     rngl_mul_1_l := I_mul_1_l;
     rngl_mul_add_distr_l := I_mul_add_distr_l;
     rngl_opt_mul_comm := I_opt_mul_comm;
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
