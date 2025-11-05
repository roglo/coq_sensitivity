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

(* to be completed, mais peut-être mauvaise piste à annuler
Theorem I_mul_subset_assoc a b c x :
  I_mul_subset a (b * c) x = I_mul_subset (a * b) c x.
Proof.
destruct_ix.
apply propositional_extensionality.
split. {
(*
  intros (l_xy_z & Hl_xy_z & Hab_c & H); subst x.
  remember (∀ xy z, _) as x in Hab_c; subst x. (* renaming *)
  remember (∑ ((xy, z) ∈ _), _) as x; subst x. (* renaming *)
...
  Hab_c : ∀ xy z : T, (xy, z) ∈ l_xy_z → i_subset (a * b) xy ∧ i_subset c z
  ============================
  I_mul_subset a (b * c) (∑ ((xy, z) ∈ l_xy_z), xy * z)
  progress unfold I_mul_subset.
*)
  intros (l_x_yz & Hl_x_yz & Ha_bc & H); subst x.
  remember (∀ x yz, _) as x in Ha_bc; subst x. (* renaming *)
  remember (∑ ((x, yz) ∈ _), _) as x; subst x. (* renaming *)
(*
  Ha_bc : ∀ x yz : T, (x, yz) ∈ l_x_yz → i_subset a x ∧ i_subset (b * c) yz
  ============================
  I_mul_subset (a * b) c (∑ ((x, yz) ∈ l_x_yz), x * yz)
*)
  cbn in Ha_bc.
  progress unfold I_mul_subset in Ha_bc.
  specialize ((proj1 forall_pair) Ha_bc) as H1.
  cbn in H1.
  clear Ha_bc; rename H1 into Ha_bc.
  specialize ((proj1 forall_pair_in) Ha_bc) as H1.
  cbn in H1.
  clear Ha_bc; rename H1 into Ha_bc.
  apply (forall_exists_exists_forall (0, 0)%L []) in Ha_bc.
  rename Hl_x_yz into Hnl.
  destruct Ha_bc as (nll & H & Habc).
  rewrite <- H in Hnl; symmetry in H.
  rename H into Hl_x_yz.
  progress unfold I_mul_subset.
  eenough (H : ∃ l_xy_z, _) by apply H. (* renaming *)
(*
  assert
    (∃ inl_xyz, length inl_xyz = length nl ∧
     ∀ inl ixyz, (inl, ixyz) ∈ inl_xyz →
     i_subset a (fst ixyz)
     ∧ length inl ≠ 0
        ∧ (∀ x y : T, (x, y) ∈ inl → i_subset b x ∧ i_subset c y)
          ∧ snd ixyz = ∑ ((x, y) ∈ inl), x * y). {
    exists
      (List.map (λ i, (List.nth i nl [], List.nth i l_x_yz (0, 0)%L))
         (List.seq 0 (length nl))).
    rewrite List.length_map, List.length_seq.
    split; [ easy | ].
    intros inl ixyz Hii.
    apply List.in_map_iff in Hii.
    destruct Hii as (i & Hii & Hi).
    specialize (Habc _ Hi).
    now injection Hii; clear Hii; intros; subst inl ixyz.
  }
  clear Habc.
  destruct H as (inl_xyz & Hnl_xyz & Habc).
*)
(**)
  remember 0 as i in nll.
  clear Heqi.
  specialize (Habc i).
  enough (Hi : i ∈ List.seq 0 (length nll)).
  specialize (Habc Hi).
  remember (∑ ((y, z) ∈ _), _) as x in Habc; subst x. (* renaming *)
  remember (∀ y z, _) as x in Habc; subst x. (* renaming *)
  destruct Habc as (Ha & Hnlz & Hbc & Hxy_z).
  remember (fst (List.nth i l_x_yz (0, 0)%L)) as x eqn:Hx.
  remember (snd (List.nth i l_x_yz (0, 0)%L)) as xyz eqn:Hxyz.
...
(* to try to guess what could be the first value *)
  specialize (Habc 0).
  cbn in Habc.
  assert (H : 0 ∈ List.seq 0 (length nll)) by (apply List.in_seq; flia Hnl).
  specialize (Habc H); clear H.
  remember (∑ ((x, yz) ∈ _), _) as x in Habc; subst x. (* renaming *)
  destruct Habc as (Ha & Hnlz & Hbc & Hxy_z).
  destruct l_x_yz as [| l_x_yz_0]; [ now symmetry in Hl_x_yz | ].
  clear Hnl; cbn in Hl_x_yz, Ha, Hnlz, Hbc, Hxy_z.
  destruct nll as [| nl]; [ easy | ].
  cbn in Hl_x_yz; apply Nat.succ_inj in Hl_x_yz.
  cbn in Hnlz, Hbc, Hxy_z.
  destruct nl as [| (x1, y1)]; [ easy | clear Hnlz ].
  cbn in Hbc.
  destruct nll as [| nl2]. {
    cbn in Hl_x_yz.
    apply List.length_zero_iff_nil in Hl_x_yz.
    subst l_x_yz.
...
(**)
  exists [List.hd (0, 0) l_x_yz]%L.
  split; [ easy | ].
  split. {
    intros xy z H.
    destruct H as [Hxy_z| H]; [ | easy ].
    destruct l_x_yz as [| x_yz]. {
      injection Hxy_z; clear Hxy_z; intros; subst xy z.
      split; apply i_zero.
    }
    cbn in Hxy_z.
...
  }
  destruct l_x_yz as [| xy_z]; [ easy | clear Hl_x_yz ].
  do 2 rewrite rngl_summation_list_pair.
  rewrite rngl_summation_list_cons.
  rewrite rngl_summation_list_only_one.
  cbn.
...
  remember l_x_yz as l_xy_z in a. (* pour rire *)
  assert (Hnl2 : length l_xy_z = length nl) by congruence.
  clear Heql_xy_z .
  move Hnl2 before Hnl.
  move l_xy_z before l_x_yz.
  exists l_xy_z.
  split; [ congruence | ].
  split. {
    intros xy z Hab_c.
    apply (List.In_nth _ _ (0, 0)%L) in Hab_c.
    destruct Hab_c as (n & Hn & Hab_c).
    rewrite List.split_nth in Hab_c.
    injection Hab_c; clear Hab_c; intros Hz Hxy.
    move Hxy after Hz.
    rewrite Hnl2 in Hn.
    split. {
      subst xy.
      specialize (Habc n).
      assert (H : n ∈ List.seq 0 (length nl)) by now apply List.in_seq.
      specialize (Habc H); clear H.
      destruct Habc as (Ha & Hlnl & Hbc & Habc).
      cbn.
      progress unfold I_mul_subset.
...
  remember (∑ (i = 1, n), nl.[i-1]) as m eqn:Hm.
(**)
...
(**)
  remember
    (List.flat_map
       (λ i,
          ListDef.map
            (λ j : nat, (la.[i - 1] * (ListDef.nth (i - 1) llb []).[j - 1])%L)
            (List.seq 1 nl.[i - 1]))
       (ListDef.seq 1 n)) as lab eqn:Hdab.
  remember
    (List.flat_map
       (λ i,
          List.map (λ j, (ListDef.nth (i - 1) llc []).[j - 1])
            (List.seq 1 nl.[i - 1]))
         (List.seq 1 n)) as lc eqn:Hdc.
  assert (Hlab : length lab = m). {
    subst lab.
    rewrite List_flat_length_map.
    replace add with (@rngl_add nat _) by easy.
    replace 0 with (@rngl_zero nat _) at 2 by easy.
    rewrite rngl_summation_seq_summation; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub.
    erewrite rngl_summation_eq_compat; [ symmetry; apply Hm | ].
    intros i Hi.
    now rewrite List.length_map, List.length_seq.
  }
  assert (Hlc : length lc = m). {
    subst lc.
    rewrite List_flat_length_map.
    replace add with (@rngl_add nat _) by easy.
    replace 0 with (@rngl_zero nat _) at 2 by easy.
    rewrite rngl_summation_seq_summation; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub.
    erewrite rngl_summation_eq_compat; [ symmetry; apply Hm | ].
    intros i Hi.
    now rewrite List.length_map, List.length_seq.
  }
  move lc before lab.
  assert (Hmz : m ≠ 0). {
    intros H; move H at top; subst m.
    symmetry in Hm.
    move Hm at bottom.
    move Hbc at bottom.
    move Hnz at bottom.
    specialize (eq_rngl_summation_zero nat_is_additive_integral) as H2.
    specialize (H2 _ _ _ Hm); cbn in Hbc; clear Hm.
    specialize (Hbc 0).
    assert (H : 0 ∈ List.seq 0 n) by now destruct n; [ | left ].
    specialize (Hbc H); clear H.
    destruct Hbc as (Hnlz, _).
    specialize (H2 1).
    assert (H : 1 ≤ 1 ≤ n) by flia Hnz.
    now specialize (H2 H); clear H.
  }
(* essai 1 *)
  remember (max m n) as p eqn:Hp.
  exists p.
  exists (lab ++ List.repeat 0%L (p - m)).
  exists (lc ++ List.repeat 0%L (p - m)).
  do 2 rewrite List.length_app.
  rewrite List.repeat_length.
  rewrite Hlab, Hlc.
  rewrite (Nat.add_comm m).
  rewrite Nat.sub_add; [ | rewrite Hp; apply Nat.le_max_l ].
  split; [ flia Hnz Hp | ].
  split; [ easy | ].
  split; [ easy | ].
  split. {
    intros xy Hxy.
    apply List.in_app_or in Hxy.
    destruct Hxy as [Hxy| Hxy]. 2: {
      apply List.repeat_spec in Hxy; subst xy.
      apply i_zero.
    }
    rewrite Hdab in Hxy.
    apply List.in_flat_map in Hxy.
    destruct Hxy as (i & Hi & Hxy).
    apply List.in_map_iff in Hxy.
    destruct Hxy as (j & Hxy & Hj).
    move j before i.
    move Hj before Hi.
    subst xy.
    remember (List.nth (i - 1) llb []) as lb eqn:Hdlb.
    specialize (Hbc (i - 1)).
    rewrite <- Hdlb in Hbc.
    assert (H : i - 1 ∈ ListDef.seq 0 n). {
      apply List.in_seq.
      apply List.in_seq in Hi.
      flia Hi.
    }
    specialize (Hbc H); clear H.
    destruct Hbc as (_ & Hlb & _ & Hb & _).
    clear - Hi Hj Ha Hla Hdlb Hb Hlb.
    move lb before la.
    move Hb before Ha.
    move i before n; move j before i.
    move Hlb before Hla.
    apply List.in_seq in Hi.
    apply List.in_seq in Hj.
    exists 1, [la.[i-1]], [lb.[j-1]].
    split; [ easy | ].
    split; [ easy | ].
    split; [ easy | ].
    split. {
      intros x Hx.
      destruct Hx as [Hx| ]; [ subst x | easy ].
      apply Ha.
      apply List.nth_In.
      flia Hla Hi.
    }
    split. {
      intros y Hy.
      destruct Hy as [Hy| ]; [ subst y | easy ].
      rewrite Hdlb.
      apply Hb; rewrite <- Hdlb.
      apply List.nth_In.
      rewrite Hlb.
      replace 0 with (@rngl_zero nat _) at 3 by easy.
      flia Hj.
    }
    rewrite rngl_summation_only_one.
    rewrite Nat.sub_diag; cbn.
    easy.
  }
  split. {
    intros z Hz.
    apply List.in_app_or in Hz.
    destruct Hz as [Hz| Hz]. 2: {
      apply List.repeat_spec in Hz; subst z.
      apply i_zero.
    }
    rewrite Hdc in Hz.
    apply List.in_flat_map in Hz.
    destruct Hz as (i & Hi & Hz).
    apply List.in_map_iff in Hz.
    destruct Hz as (j & Hz & Hj).
    move j before i.
    move Hj before Hi.
    subst z.
    specialize (Hbc (i - 1)).
    assert (H : i - 1 ∈ ListDef.seq 0 n). {
      apply List.in_seq.
      apply List.in_seq in Hi.
      flia Hi.
    }
    specialize (Hbc H); clear H.
    destruct Hbc as (_ & _ & Hlc' & _ & Hc & _).
    apply Hc.
    apply List.nth_In.
    rewrite Hlc'.
    replace 0 with (@rngl_zero nat _) at 3 by easy.
    apply List.in_seq in Hj.
    flia Hj.
  }
  erewrite (rngl_summation_eq_compat _ _ _ p). 2: {
    intros i Hi.
    progress replace ((lab ++ _).[_]) with lab.[i-1]. {
      progress replace ((lc ++ _).[_]) with lc.[i-1]. {
        reflexivity.
      }
      destruct (lt_dec (i - 1) (length lc)) as [H1| H1]. {
        now symmetry; apply List.app_nth1.
      }
      apply Nat.nlt_ge in H1.
      rewrite List.app_nth2; [ | easy ].
      rewrite List.nth_repeat.
      now apply List.nth_overflow.
    }
    destruct (lt_dec (i - 1) (length lab)) as [H1| H1]. {
      now symmetry; apply List.app_nth1.
    }
    apply Nat.nlt_ge in H1.
    rewrite List.app_nth2; [ | easy ].
    rewrite List.nth_repeat.
    now apply List.nth_overflow.
  }
  cbn.
  progress replace (∑ (i = 1, n), _)
    with (∑ (i = 1, p), la.[i - 1] * lbc.[i - 1]). 2: {
    rewrite (rngl_summation_split n).
    rewrite (all_0_rngl_summation_0 (n + 1)).
    apply rngl_add_0_r.
    intros i Hi.
    rewrite List.nth_overflow.
    apply (rngl_mul_0_l Hos).
    flia Hla Hi.
    flia Hp.
  }
  (* ouais, mais c'est pas dans le même ordre, hein *)
  rewrite rngl_summation_eq_compat with
    (h := λ i,
       (la.[i - 1] *
        ∑ (j = 1, p),
          (ListDef.nth (i - 1) llb []).[j - 1] *
          (ListDef.nth (i - 1) llc []).[j - 1])%L). 2: {
    intros i Hi.
    destruct (lt_dec (i - 1) n) as [H1| H1]. 2: {
      apply Nat.nlt_ge in H1.
      rewrite (List.nth_overflow la); [ | now rewrite Hla ].
      now do 2 rewrite (rngl_mul_0_l Hos).
    }
    progress f_equal.
    specialize (Hbc (i - 1)).
    assert (H : i - 1 ∈ List.seq 0 n) by now apply List.in_seq.
    specialize (Hbc H); clear H.
    destruct Hbc as (_ & Hlb & _ & _ & _ & Hbc).
    rewrite Hbc.
    rewrite (rngl_summation_split (List.nth (i - 1) nl 0) _ _ p). {
      rewrite (all_0_rngl_summation_0 _ p).
      symmetry; apply rngl_add_0_r.
      intros j Hj.
      rewrite List.nth_overflow; [ | rewrite Hlb; flia Hj ].
      apply (rngl_mul_0_l Hos).
    }
    split; [ flia | ].
    apply -> Nat.succ_le_mono.
    rewrite Hp.
    eapply Nat.le_trans; [ | apply Nat.le_max_l ].
    rewrite Hm.
    rewrite (rngl_summation_split3 i). 2: {
      split; [ easy | flia H1 ].
    }
    replace 0 with (@rngl_zero nat _) at 2 by easy.
    rewrite Nat.add_shuffle0.
    apply Nat.le_add_l.
  }
  erewrite rngl_summation_eq_compat. 2: {
    intros i Hi.
    rewrite (rngl_mul_summation_distr_l Hos).
    remember (∑ (j = _, _), _) as x in |-*; subst x. (* renaming *)
    easy.
  }
  cbn.
  rewrite rngl_summation_summation_exch.
  (* ouais, chais pas. Y a de l'idée, mais faut voir *)
  set (u := λ i, List.nth (i - 1) llb []).
  set (v := λ i, List.nth (i - 1) llc []).
  erewrite List_flat_map_ext' in Hdab. 2: {
    intros j Hj.
    specialize (Hbc (j - 1)); move Hbc at bottom.
    assert (H : j - 1 ∈ ListDef.seq 0 n). {
      apply List.in_seq.
      apply List.in_seq in Hj.
      flia Hj.
    }
    specialize (Hbc H); clear H.
    destruct Hbc as (_ & H & _).
    progress replace 0 with (@rngl_zero nat _) in H at 3 by easy.
    rewrite <- H.
    progress fold (u j).
    remember (λ k, _) as x in |-*; subst x. (* renaming *)
    easy.
  }
  erewrite List_flat_map_ext' in Hdc. 2: {
    intros j Hj.
    specialize (Hbc (j - 1)); move Hbc at bottom.
    assert (H : j - 1 ∈ ListDef.seq 0 n). {
      apply List.in_seq.
      apply List.in_seq in Hj.
      flia Hj.
    }
    specialize (Hbc H); clear H.
    destruct Hbc as (_ & _ & H & _).
    progress replace 0 with (@rngl_zero nat _) in H at 3 by easy.
    rewrite <- H.
    progress fold (v j).
    remember (λ k, _) as x in |-*; subst x. (* renaming *)
    rewrite List_map_seq.
    erewrite List.map_ext_in. 2: {
      intros k Hk.
      rewrite Nat.add_comm, Nat.add_sub.
      easy.
    }
    rewrite <- List_map_nth_seq.
    easy.
  }
  erewrite rngl_summation_eq_compat. 2: {
    intros i Hi.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      progress fold (u j).
      progress fold (v j).
      easy.
    }
    remember (∑ (j = _, _), _) as x in |-*; subst x. (* renaming *)
    easy.
  }
  rewrite Hdab, Hdc.
  remember (∑ (i = _, _), _) as x in |-*.
  erewrite rngl_summation_eq_compat. 2: {
    intros i Hi.
    erewrite List.flat_map_ext. 2: {
      intros j.
      rewrite List_map_seq.
      erewrite List.map_ext_in. 2: {
        intros k Hk.
        rewrite Nat.add_comm, Nat.add_sub.
        reflexivity.
      }
      rewrite List_map_f_seq.
(*
      remember (List.map (λ y, _) _) as y in |-*; subst y. (* renaming *)
*)
      reflexivity.
    }
    reflexivity.
  }
  subst x.
Theorem glop :
  List.nth (i - 1)
    (List.flat_map (λ j : nat, ListDef.map (rngl_mul la.[j - 1]) (u j))
        (ListDef.seq 1 n))
    d =
  (List.nth (i - 1) (List.flat_map u (ListDef.seq 1 n)) d) *
...
  ============================
  ∑ (i = 1, p), ∑ (j = 1, p), la.[j - 1] * ((u j).[i - 1] * (v j).[i - 1]) =
  ∑ (i = 1, p),
    (List.flat_map (λ j : nat, ListDef.map (rngl_mul la.[j - 1]) (u j))
       (ListDef.seq 1 n))
      .[i - 1] *
    (List.flat_map v (ListDef.seq 1 n)).[i - 1]
... fin essai 1
  exists m, lab, lc.
  split; [ easy | ].
  split; [ easy | ].
  split; [ easy | ].
  split. {
    intros xy Hxy.
    rewrite Hdab in Hxy.
    apply List.in_flat_map in Hxy.
    destruct Hxy as (i & Hi & Hxy).
    apply List.in_map_iff in Hxy.
    destruct Hxy as (j & Hxy & Hj).
    move j before i.
    move Hj before Hi.
    subst xy.
    remember (List.nth (i - 1) llb []) as lb eqn:Hdlb.
    specialize (Hbc (i - 1)).
    rewrite <- Hdlb in Hbc.
    assert (H : i - 1 ∈ ListDef.seq 0 n). {
      apply List.in_seq.
      apply List.in_seq in Hi.
      flia Hi.
    }
    specialize (Hbc H); clear H.
    destruct Hbc as (_ & Hlb & _ & Hb & _).
    clear - Hi Hj Ha Hla Hdlb Hb Hlb.
    move lb before la.
    move Hb before Ha.
    move i before n; move j before i.
    move Hlb before Hla.
    apply List.in_seq in Hi.
    apply List.in_seq in Hj.
    exists 1, [la.[i-1]], [lb.[j-1]].
    split; [ easy | ].
    split; [ easy | ].
    split; [ easy | ].
    split. {
      intros x Hx.
      destruct Hx as [Hx| ]; [ subst x | easy ].
      apply Ha.
      apply List.nth_In.
      flia Hla Hi.
    }
    split. {
      intros y Hy.
      destruct Hy as [Hy| ]; [ subst y | easy ].
      rewrite Hdlb.
      apply Hb; rewrite <- Hdlb.
      apply List.nth_In.
      rewrite Hlb.
      replace 0 with (@rngl_zero nat _) at 3 by easy.
      flia Hj.
    }
    rewrite rngl_summation_only_one.
    rewrite Nat.sub_diag; cbn.
    easy.
  }
  split. {
    intros z Hz.
    rewrite Hdc in Hz.
    apply List.in_flat_map in Hz.
    destruct Hz as (i & Hi & Hz).
    apply List.in_map_iff in Hz.
    destruct Hz as (j & Hz & Hj).
    move j before i.
    move Hj before Hi.
    subst z.
    specialize (Hbc (i - 1)).
    assert (H : i - 1 ∈ ListDef.seq 0 n). {
      apply List.in_seq.
      apply List.in_seq in Hi.
      flia Hi.
    }
    specialize (Hbc H); clear H.
    destruct Hbc as (_ & _ & Hlc' & _ & Hc & _).
    apply Hc.
    apply List.nth_In.
    rewrite Hlc'.
    replace 0 with (@rngl_zero nat _) at 3 by easy.
    apply List.in_seq in Hj.
    flia Hj.
  }
  erewrite rngl_summation_eq_compat. 2: {
    intros i Hi.
    apply (f_equal (rngl_mul _)).
    specialize (Hbc (i-1)).
    assert (H : i - 1 ∈ ListDef.seq 0 n). {
      apply List.in_seq.
      flia Hi.
    }
    specialize (Hbc H); clear H.
    destruct Hbc as (_ & _ & _ & _ & _ & Hbc).
    rewrite Hbc.
    remember (∑ (j = _, _), _) as x in |-*; subst x. (* renaming *)
    reflexivity.
  }
  cbn.
  erewrite rngl_summation_eq_compat. 2: {
    intros i Hi.
    rewrite (rngl_mul_summation_distr_l Hos).
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite rngl_mul_assoc.
      reflexivity.
    }
    remember (∑ (j = _, _), _) as x in |-*; subst x. (* renaming *)
    reflexivity.
  }
  cbn.
...
  (* conseils de ChatGPT: *)
  exists m.
  remember
    (List.concat
       (List.map
         (λ i : nat,
            List.map
              (λ j : nat,
                 ((la.[i-1] * (ListDef.nth (i-1) llb []).[j-1])%L,
                  (ListDef.nth (i-1) llc []).[j-1])%L)
              (List.seq 1 nl.[i-1]))
         (List.seq 1 n))) as pairs eqn:Hpairs.
  remember (List.map fst pairs) as lab eqn:Hdab.
  remember (List.map snd pairs) as lc eqn:Hdc.
  exists lab, lc.
  assert (Hlpairs : length pairs = m). {
    rewrite Hpairs.
    rewrite List.length_concat.
    progress unfold List.list_sum.
    rewrite <- (List.rev_involutive (List.map (length (A:=T*T)) _)).
    rewrite List.fold_left_rev_right.
    do 2 rewrite <- List.map_rev.
    replace add with (@rngl_add nat _) by easy.
    replace 0 with (@rngl_zero nat _) at 2 by easy.
    rewrite List.map_map.
    erewrite List_fold_left_ext_in. 2: {
      intros i j Hij.
      apply rngl_add_comm.
    }
    erewrite List.map_ext_in. 2: {
      intros i Hi.
      rewrite List.length_map.
      rewrite List.length_seq.
      reflexivity.
    }
    rewrite fold_iter_list.
    rewrite rngl_summation_list_map.
    rewrite rngl_summation_list_rev.
    rewrite rngl_summation_seq_summation; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub.
    easy.
  }
  assert (Hlab : length lab = m) by now subst lab; rewrite List.length_map.
  assert (Hlc : length lc = m) by now subst lc; rewrite List.length_map.
  move lc before lab.
  assert (Hmz : m ≠ 0). {
    intros H; move H at top; subst m.
    symmetry in Hm.
    move Hm at bottom.
    move Hbc at bottom.
    move Hnz at bottom.
    specialize (eq_rngl_summation_zero nat_is_additive_integral) as H2.
    specialize (H2 _ _ _ Hm); cbn in Hbc; clear Hm.
    specialize (Hbc 0).
    assert (H : 0 ∈ List.seq 0 n) by now destruct n; [ | left ].
    specialize (Hbc H); clear H.
    destruct Hbc as (Hnlz, _).
    specialize (H2 1).
    assert (H : 1 ≤ 1 ≤ n) by flia Hnz.
    now specialize (H2 H); clear H.
  }
  split; [ easy | ].
  split; [ easy | ].
  split; [ easy | ].
  split. {
    intros xy Hxy.
    rewrite Hdab in Hxy.
    apply List.in_map_iff in Hxy.
    destruct Hxy as ((xy', z), Hxyz).
    cbn in Hxyz.
    destruct Hxyz as (H, Hxyz); subst xy'.
    rewrite Hpairs in Hxyz.
    apply List.in_concat in Hxyz.
    destruct Hxyz as (lxyz, (Hlxyz, Hxyz)).
    apply List.in_map_iff in Hlxyz.
    destruct Hlxyz as (i, (Hlxyz, Hi)).
    subst lxyz.
    apply List.in_map_iff in Hxyz.
    destruct Hxyz as (j, (Hxyz, Hj)).
    move j before i.
    injection Hxyz; clear Hxyz; intros Hz Hxy.
    clear z Hz.
    cbn.
    remember (List.nth (i - 1) llb []) as lb eqn:Hdlb.
    progress unfold I_mul_subset.
    apply List.in_seq in Hi.
    apply List.in_seq in Hj.
    exists 1, [la.[i-1]], [lb.[j-1]].
    split; [ easy | ].
    split; [ easy | ].
    split; [ easy | ].
    split. {
      intros x Hx.
      destruct Hx as [Hx| ]; [ subst x | easy ].
      apply Ha.
      apply List.nth_In.
      flia Hla Hi.
    }
    split. {
      intros y Hy.
      destruct Hy as [Hy| ]; [ subst y | easy ].
      rewrite Hdlb.
      specialize (Hbc (i - 1)).
      rewrite <- Hdlb in Hbc.
      assert (H : i - 1 ∈ ListDef.seq 0 n). {
        apply List.in_seq.
        flia Hi.
      }
      specialize (Hbc H); clear H.
      destruct Hbc as (_ & Hlb & _ & Hb & _).
      apply Hb; rewrite <- Hdlb.
      apply List.nth_In.
      rewrite Hlb.
      replace 0 with (@rngl_zero nat _) at 3 by easy.
      flia Hj.
    }
    rewrite rngl_summation_only_one.
    rewrite Nat.sub_diag; cbn.
    easy.
  }
  split. {
    intros z Hz.
    rewrite Hdc in Hz.
    apply List.in_map_iff in Hz.
    destruct Hz as ((xy, z'), Hz).
    cbn in Hz.
    destruct Hz as (H, Hxyz); subst z'.
    rewrite Hpairs in Hxyz.
    apply List.in_concat in Hxyz.
    destruct Hxyz as (lxyz, (Hlxyz, Hxyz)).
    apply List.in_map_iff in Hlxyz.
    destruct Hlxyz as (i, (Hlxyz, Hi)).
    subst lxyz.
    apply List.in_map_iff in Hxyz.
    destruct Hxyz as (j, (Hxyz, Hj)).
    move j before i.
    injection Hxyz; clear Hxyz; intros Hz Hxy.
    clear xy Hxy; subst z.
    apply List.in_seq in Hi.
    apply List.in_seq in Hj.
    specialize (Hbc (i - 1)).
    assert (H : i - 1 ∈ ListDef.seq 0 n). {
      apply List.in_seq.
      flia Hi.
    }
    specialize (Hbc H); clear H.
    destruct Hbc as (_ & _ & Hlc' & _ & Hc & _).
    apply Hc.
    apply List.nth_In.
    rewrite Hlc'.
    replace 0 with (@rngl_zero nat _) at 3 by easy.
    flia Hj.
  }
  erewrite rngl_summation_eq_compat. 2: {
    intros i Hi.
    apply (f_equal (rngl_mul _)).
    specialize (Hbc (i-1)).
    assert (H : i - 1 ∈ ListDef.seq 0 n). {
      apply List.in_seq.
      flia Hi.
    }
    specialize (Hbc H); clear H.
    destruct Hbc as (_ & _ & _ & _ & _ & Hbc).
    rewrite Hbc.
    remember (∑ (j = _, _), _) as x in |-*; subst x. (* renaming *)
    reflexivity.
  }
  cbn.
  erewrite rngl_summation_eq_compat. 2: {
    intros i Hi.
    rewrite (rngl_mul_summation_distr_l Hos).
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite rngl_mul_assoc.
      reflexivity.
    }
    remember (∑ (j = _, _), _) as x in |-*; subst x. (* renaming *)
    reflexivity.
  }
  cbn.
  (*
  Transformer la somme double en somme sur la concaténation (flatten).
  Après application pour tous les ii, tu obtiens une somme double
    ∑i=1n∑j=1nl[i−1]  Ti,j∑i=1n​∑j=1nl[i−1]​Ti,j​, avec
    Ti,j:=(la[i−1]⋅llbi[j−1])⋅llci[j−1]Ti,j​:=(la[i−1]⋅llbi​[j−1])⋅llci​[j−1].

  Utilise le lemme général sum_over_i_sum_over_j =
  sum_over_flattened_list (souvent appelé sum_flat_map ou
  sum_concat_map) :

  cela dit que la somme double est égale à la somme sur la liste obtenue
  en concaténant, pour chaque i, la liste map (fun j => T_{i,j}) (seq 1
  nl[i-1]).  Mais cette liste exacte est celle que tu as définie dans
  pairs (voir Hpairs).
  *)
  progress unfold iter_seq.
  do 2 rewrite Nat_sub_succ_1.
  rewrite rngl_summation_summation_list_flat_map'.
  erewrite List.flat_map_ext. 2: {
    intros i.
    rewrite Nat_sub_succ_1.
    reflexivity.
  }
  (* ouais, je crois que c'est ça *)
  (*
  Remplacer la liste construite par pairs (utiliser Hpairs).
  Grâce à Hpairs tu peux remplacer la liste concaténée par pairs.
  Après sum_flat_map et Hpairs, la somme devient la somme sur pairs
  de fst(pair)*snd(pair) (avec les notations appropriées).
  *)
...
  rewrite Hpairs in Hdab, Hdc.
  rewrite List.concat_map in Hdab, Hdc.
  rewrite List.map_map in Hdab, Hdc.
  rewrite <- List.flat_map_concat_map in Hdab, Hdc.
  remember (List.flat_map (λ i, _)) as x in Hdab; subst x. (* renaming *)
  remember (List.flat_map (λ i, _)) as x in Hdc; subst x. (* renaming *)
  erewrite List.flat_map_ext in Hdab. 2: {
    intros i.
    rewrite List.map_map; cbn.
    remember (List.map (λ j, _) _) as x in |-*; subst x. (* renaming *)
    reflexivity.
  }
  erewrite List.flat_map_ext in Hdc. 2: {
    intros i.
    rewrite List.map_map; cbn.
    rewrite List_map_seq.
    erewrite List.map_ext_in. 2: {
      intros j Hj.
      rewrite Nat.add_comm, Nat.add_sub.
      reflexivity.
    }
    reflexivity.
  }
  erewrite List_flat_map_ext' in Hdab. 2: {
    intros i Hi.
    move Hbc at bottom.
    specialize (Hbc (i - 1)).
    assert (H : i - 1 ∈ ListDef.seq 0 n). {
      apply List.in_seq in Hi.
      apply List.in_seq.
      flia Hi.
    }
    specialize (Hbc H); clear H.
    destruct Hbc as (_ & H1 & _ & _ & _).
    rewrite <- H1.
    reflexivity.
  }
  erewrite List_flat_map_ext' in Hdc. 2: {
    intros i Hi.
    move Hbc at bottom.
    specialize (Hbc (i - 1)).
    assert (H : i - 1 ∈ ListDef.seq 0 n). {
      apply List.in_seq in Hi.
      apply List.in_seq.
      flia Hi.
    }
    specialize (Hbc H); clear H.
    destruct Hbc as (_ & _ & H1 & _ & _ & _).
    rewrite <- H1.
    rewrite <- List_map_nth_seq.
    reflexivity.
  }
  rewrite List.flat_map_concat_map in Hdab, Hdc |-*.
  rewrite <- List.seq_shift in Hdab, Hdc.
  rewrite List.map_map in Hdab, Hdc.
  erewrite List.map_ext_in in Hdab. 2: {
    intros i Hi.
    rewrite Nat_sub_succ_1.
    reflexivity.
  }
  erewrite List.map_ext_in in Hdc. 2: {
    intros i Hi.
    rewrite Nat_sub_succ_1.
    reflexivity.
  }
  rewrite <- Hllb in Hdab.
  rewrite <- Hllc in Hdc.
  rewrite <- List_map_nth_seq in Hdc.
  rewrite <- List.flat_map_concat_map in Hpairs, Hdab |-*.
(*
...
(*
  erewrite List_flat_map_ext'. 2: {
    intros i Hi.
    erewrite List.map_ext_in. 2: {
      intros j Hj.
      rewrite <- rngl_mul_assoc.
      reflexivity.
    }
    reflexivity.
  }
*)
remember (List.flat_map _ _) as x in |-*.
remember (List.flat_map _ _) as y in Hpairs.
move y after x.
move Hpairs at bottom.
...
*)
  remember (List.flat_map _ _) as x in |-*.
  assert (Hx : length x = m). {
    subst x.
    rewrite List_flat_length_map.
    replace add with (@rngl_add nat _) by easy.
    replace 0 with (@rngl_zero nat _) at 2 by easy.
    rewrite rngl_summation_seq_summation; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub.
    rewrite Hm.
    apply rngl_summation_eq_compat.
    intros i Hi.
    rewrite List.length_map.
    now rewrite List.length_seq.
  }
(*
  subst x.
  rewrite <- rngl_summation_summation_list_flat_map'.
  move Hbc at bottom.
  erewrite rngl_summation_list_eq_compat. 2: {
    intros i Hi.
    specialize (Hbc (i - 1)).
    assert (H : i - 1 ∈ List.seq 0 n). {
      apply List.in_seq in Hi.
      apply List.in_seq; flia Hi.
    }
    specialize (Hbc H); clear H.
    destruct Hbc as (H1 & H2 & _).
    rewrite <- H2.
    reflexivity.
  }
  cbn.
...
}
...
*)
  replace x with
    (List.map
       (λ i,
          let aa := List.nth i pairs (0, 0)%L in
          (fst aa * snd aa)%L)
       (List.seq 0 m)). 2: {
    subst x.
    rewrite Hm.
    progress unfold iter_seq at 1.
    rewrite List_seq_rngl_summation_r.
    rewrite Nat_sub_succ_1.
    rewrite <- List.seq_shift at 1.
    rewrite List.map_map.
    erewrite (List.map_ext_in _ _ (List.seq 0 n)). 2: {
      intros; rewrite Nat_sub_succ_1; reflexivity.
    }
    rewrite <- Hnl at 1.
    rewrite <- List_map_nth_seq.
    cbn.
...
    replace (List.fold_left _ _ []) with (List.seq 0 m). 2: {
      clear - nl Hnl Hm.
      subst m n.
      progress unfold iter_seq.
      progress unfold iter_list.
      rewrite Nat_sub_succ_1.
      rewrite <- List.seq_shift.
      rewrite List_fold_left_map.
      erewrite List_fold_left_ext_in. 2: {
        intros * Hb.
        now rewrite Nat_sub_succ_1.
      }
      cbn.
      induction nl as [| n]; [ easy | ].
      rewrite List.length_cons.
      rewrite <- Nat.add_1_l.
      rewrite List.seq_app.
      replace (List.seq 0 1) with [0] by easy.
      rewrite Nat.add_0_l.
      rewrite List.fold_left_app.
      remember (List.fold_left _ [0] 0) as x.
      cbn in Heqx; subst x.
      rewrite <- List.seq_shift.
      rewrite List_fold_left_map.
      erewrite List_fold_left_ext_in. 2: {
        now intros * Hb; cbn.
      }
      specialize fold_left_rngl_add_fun_from_0 as H1.
      rewrite (H1 nat n); clear H1.
      cbn.
      rewrite Nat.add_comm.
      rewrite List.seq_app.
      rewrite IHnl; cbn.
      clear IHnl.
revert nl.
induction n; intros. {
apply List.app_nil_r.
}
symmetry.
Search (List.seq _ (S _)).
rewrite List.seq_S.
Search (List.fold_left _ _ (_ ++ _)).

rewrite <- List.cons_seq.
rewrite List_seq_succ_r.
...
  ============================
  List.fold_left (λ (la : list nat) (d : nat), la ++ ListDef.seq (length la) d) nl (ListDef.seq 0 n) =
  List.fold_left (λ (la : list nat) (d : nat), la ++ ListDef.seq (length la) d) nl [] ++
  ListDef.seq (List.fold_left (λ c i : nat, c + ListDef.nth i nl 0) (ListDef.seq 0 (length nl)) 0) n
...
Print fold_left_op_fun_from_d.
rewrite (fold_left_op_fun_from_d []).
...
      rewrite (fold_left_op_fun_from_d []).
Print fold_left_rngl_add_fun_from_0.
Check fold_left_op_fun_from_d.
      rewrite (H1 nat n); clear H1.
...
).

replace n with (rngl_of_nat n).

...
      cbn - [ List.nth rngl_zero ].
      rewrite rngl_add_0_l.
...
Search (List.seq _ _ = List.seq _ _).
rewrite List_seq_shiftr.
...
      cbn - [ List.nth rngl_zero ].
symmetry.
specialize (@List_seq_rngl_summation_r (list nat) 0) as H1.
(* pffff.... fait chier *)
...
cbn - [ rngl_add rngl_zero ] in H1.
rewrite (fold_left_op_fun_from_d []).
fold_left_rngl_add_fun_from_0:
  ∀ {T : Type} {ro : ring_like_op T},
    ring_like_prop T
    → ∀ (A : Type) (a : T) (l : list A) (f : A → T),
        List.fold_left (λ (c : T) (i : A), (c + f i)%L) l a =
        (a + List.fold_left (λ (c : T) (i : A), c + f i) l 0)%L
fold_left_op_fun_from_d:
  ∀ {T A : Type} (d : T) (op : T → T → T) (a : T) (l : list A) (f : A → T),
    (∀ x : T, op d x = x)
    → (∀ x : T, op x d = x)
      → (∀ a0 b c : T, op a0 (op b c) = op (op a0 b) c)
        → List.fold_left (λ (c : T) (i : A), op c (f i)) l a =
          op a (List.fold_left (λ (c : T) (i : A), op c (f i)) l d)
List_seq_rngl_summation_r:
  ∀ {T : Type} (a : nat) (lb : list T) (f : T → nat),
    ListDef.seq a (∑ (i ∈ lb), f i) =
    List.fold_left
      (λ (la : list nat) (d : nat), la ++ ListDef.seq (a + length la) d)
      (ListDef.map f lb) []

      rewrite List_nth_0_cons, Nat.add_0_l.
...
    rewrite Hdab, Heqx.
    rewrite Hllb.
    progress f_equal.
    apply List.map_ext_in.
    intros i Hi.
    rewrite Nat_sub_succ_1.
    specialize (Hbc i Hi).
    move Hbc at bottom.
    destruct Hbc as (_ & H1 & _).
    rewrite H1.
    apply List.map_ext_in.
    intros j Hj.
(* chiasse de pute, y a un truc qui déconne *)
...
Theorem glop {A B} :
  ∀ (llb : list (list A)) (f : _ → _ → B),
  List.map
    (λ i : nat, List.map (f i) (List.seq 1 (length (ListDef.nth i llb []))))
    (List.seq 0 (length llb)) =
  [].
Proof.
intros.
induction llb as [| lb]; [ easy | ].
rewrite List.length_cons.
rewrite List.seq_S.
rewrite Nat.add_0_l.
erewrite List.map_ext_in. 2: {
  intros i Hi.
  destruct (Nat.eq_dec i 0) as [Hiz| Hiz]. 2: {
    replace i with (S (i - 1)) at 2 by flia Hiz.
    rewrite List_nth_succ_cons.
    reflexivity.
  }
  cbn - [ List.nth ].
  apply List.in_app_or in Hi.
  destruct Hi as [Hi| Hi]. {
...
  destruct Hi as [Hi| Hi].
... ...
rewrite (glop _ (λ i j, (la.[i] * (List.nth i llb []).[j-1])%L)) in Hdab.
...
Theorem glop {A B} :
  ∀ llb (f : _ → _ → list A → B),
  List.map
    (λ i : nat,
       List.map
         (λ j : nat, f i j (ListDef.nth i llb []))
         (List.seq 1 (length (ListDef.nth i llb []))))
    (List.seq 0 (length llb)) =
  [].
Proof.
intros.
induction llb as [| lb]; [ easy | ].
rewrite List.length_cons.
rewrite List.seq_S.
rewrite Nat.add_0_l.
erewrite List.map_ext_in. 2: {
  intros i Hi.
  destruct (Nat.eq_dec i 0) as [Hiz| Hiz]. 2: {
    replace i with (S (i - 1)) at 1 by flia Hiz.
    rewrite List_nth_succ_cons.
    erewrite List.map_ext_in. 2: {
      intros j Hj.
      replace i with (S (i - 1)) at 2 by flia Hiz.
      rewrite List_nth_succ_cons.
      reflexivity.
    }
... ...
   subst i.
   rewrite List_nth_0_cons.
...
rewrite (glop _ (λ i j lla, (la.[i] * lla.[j-1])%L)) in Hdab.
...
Search (List.map (λ _, List.map _ _) _).
Theorem glip :
  ∀ la f,
  List.map (λ i, List.map f (List.seq 1 (f i))) (List.seq 0 (length la)) =
  List.map f (List.map (λ i, List.seq 1 (f i)) la).
...
List_map_nth_seq:
  ∀ {A : Type} (d : A) (la : list A),
    la =
    ListDef.map (λ i : nat, ListDef.nth i la d) (ListDef.seq 0 (length la))
List_map_seq:
  ∀ (A : Type) (f : nat → A) (sta len : nat),
    ListDef.map f (ListDef.seq sta len) =
    ListDef.map (λ i : nat, f (sta + i)) (ListDef.seq 0 len)
... ...
rewrite (glop _ (λ i j lla, (la.[i] * lla.[j-1])%L)) in Hdab.
...
  subst lc.
Search (List.map _ (List.seq _ _)).
Search (List.map (λ _, List.map _ _) _).
...
Check @List_map_nth_seq.
Check List.concat_map.
...
  rewrite <- rngl_summation_summation_list_flat_map' in Hdab.
  rewrite <- rngl_summation_summation_list_flat_map'.
  erewrite List_flat_map_ext'. 2: {
    intros i Hi.
...
  rewrite List.flat_map_concat_map in Hdab, Hdc |-*.
...
  rewrite <- List.concat_map in Hdab. , Hdc |-*.
Search (List.flat_map _ _ = List.flat_map _ _).
  Check List.flat_map_concat_map.
Search List.concat.
Check List.concat_map.
...
    destruct Hbc as (_ & _ & _ & HHHHHHHHHHH & _ & _).
...
Search (List.map _ (List.seq _ _)).
List_map_nth_seq:
  ∀ {A : Type} (d : A) (la : list A),
    la =
    ListDef.map (λ i : nat, ListDef.nth i la d) (ListDef.seq 0 (length la))
...
    reflexivity.
  }
Search (List.map _ (List.seq _ _)).
...
    remember (List.map (λ j, _) _) as x in |-*; subst x. (* renaming *)
    reflexivity.
  }
...
  rewrite <- List.flat_map_concat_map in Hpairs.
...
  rewrite <- Hpairs.
...
  rewrite <- rngl_summation_summation_list_flat_map.
Search (∑ (_ ∈ List.map _ _), _).
  erewrite rngl_summation_list_eq_compat. 2: {
    intros i Hi.
    rewrite rngl_summation_list_map.
    rewrite Nat_sub_succ_1.
    reflexivity.
  }
  cbn.
  ============================
  ∑ (i ∈ ListDef.seq 1 n),
    ∑ (i0 ∈ ListDef.seq 1 (ListDef.nth (i - 1) nl 0)),
      la.[i - 1] * (ListDef.nth (i - 1) llb []).[i0 - 1] * (ListDef.nth (i - 1) llc []).[i0 - 1] =
(* ah, chais pas *)
...
  ∑ (i = a, b), ∑ (j = c i, d i), f i j =
  ∑ (i ∈
     List.concat
       (List.map
          (λ i, List.map (λ j, f i j) (List.seq (c i) (S (d i) - c i)))
          (List.seq a (S b - a)))),
     i.
Proof.
progress unfold iter_seq.
Check rngl_summation_summation_list_flat_map.
...
rewrite rngl_summation_summation_list_flat_map.
rewrite <- List.flat_map_concat_map.
apply rngl_summation_summation_list_concat.
Qed.
... ...
rewrite rngl_summation_summation_concat.
...
  ∑ (i = a, b), ∑ (j = c, d), f i j = ∑ (i = 0, (b - a) * (d - c)),
...
  ∑ (i ∈ la), ∑ (j ∈ lb), f i j = ∑ (i ...
  ∑ (i = a, b), ∑ (j = c, d), f i j = ∑ (i = 0, (b - a) * (d - c)),
Search (∑ (_ = _, _), ∑ (_ = _, _), _).
...
  symmetry.
  rewrite Hdab, Hdc, Hpairs.
  erewrite rngl_summation_eq_compat. 2: {
    intros i Hi.
    rewrite (List_map_nth' (0, 0)%L 0%L). 2: {
      rewrite List.length_concat.
      progress unfold List.list_sum.
      rewrite <- (List.rev_involutive (List.map (length (A:=T*T)) _)).
      rewrite List.fold_left_rev_right.
      do 2 rewrite <- List.map_rev.
      replace add with (@rngl_add nat _) by easy.
      replace 0 with (@rngl_zero nat _) at 3 by easy.
      rewrite List.map_map.
      erewrite List_fold_left_ext_in. 2: {
        intros; apply rngl_add_comm.
      }
      erewrite List.map_ext_in. 2: {
        intros.
        rewrite List.length_map.
        rewrite List.length_seq.
        reflexivity.
      }
      rewrite fold_iter_list.
      rewrite rngl_summation_list_map.
      rewrite rngl_summation_list_rev.
      rewrite rngl_summation_seq_summation; [ | easy ].
      rewrite Nat.add_comm, Nat.add_sub.
      remember (∑ (j = _, _), _) as x; subst x. (* renaming *)
      rewrite <- Hm.
      flia Hi.
    }
...
} {
  progress unfold I_add_subset in H1.
  progress unfold I_add_subset.
  destruct H1 as (x & t & H & H1 & H3); subst y.
  rename t into y.
  exists x, (y + z)%L.
  split; [ symmetry; apply rngl_add_assoc | ].
  split; [ easy | ].
  now exists y, z.
}
...
*)

(* to be completed
Theorem glop a b c : ∀ z, (z ∈ a * (b * c) → z ∈ (a * b) * c)%I.
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
destruct Ha_bc as (llyz & Hllyz & Hyz).
remember (length lx_yz) as n eqn:Hn.
rename Hlx_yz into H; rename Hn into Hlx_yz; rename H into Hn.
move Hn before n; symmetry in Hlx_yz.
move Hlx_yz before Hllyz.
move llyz before lx_yz.
rewrite Hllyz in Hyz.
(**)
set (P u v := (fst u ∈ a)%I ∧ I_mul_subset_prop b c (snd u) v).
specialize (forall_in_seq (0, 0)%L [] lx_yz llyz P) as H1.
rewrite Hlx_yz, Hllyz in H1.
specialize (H1 eq_refl).
subst P; cbn in H1.
specialize (proj1 H1) as H2; clear H1.
specialize (H2 Hyz).
clear Hyz; rename H2 into Hyz.
destruct Hyz as (lx_yz_lyz & Hllyzm & Hlx_yzm & Hyz).
subst lx_yz llyz.
move Hllyz before Hlx_yz.
rewrite List.length_map in Hlx_yz, Hllyz.
clear Hlx_yz; rename Hllyz into Hlx_yz_lyz.
rewrite rngl_summation_list_map in Ht.
remember (∀ x_yz_lyz, _) as x in Hyz; subst x. (* renaming *)
remember (∑ (x_yz_lyz ∈ _), _) as x in Ht; subst x. (* renaming *)
assert
  (∀ x_yz_lyz,
   x_yz_lyz ∈ lx_yz_lyz
   → snd (fst x_yz_lyz) = ∑ ((y, z) ∈ snd x_yz_lyz), y * z). {
  intros * Hx_yz_lyz.
  specialize (Hyz _ Hx_yz_lyz) as (Ha & Hllx_yz_lyz & Hbc & H).
  easy.
}
erewrite rngl_summation_list_eq_compat in Ht. 2: {
  intros i Hi.
  rewrite H; [ | easy ].
  easy.
}
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
remember (∑ (x_yz_lyz ∈ _), _) as x in Ht; subst x. (* renaming *)
...
... pfff... ci-dessous vraiment chiant...
  remember (max n (Max (l ∈ llyz), length l)) as m eqn:Hm.
  remember
    (List.map
       (λ ll, (fst ll ++ List.repeat (0, 0)%L (m - length (fst ll)), snd ll))
       (lab ++ List.repeat ([], (0, 0)%L) (m - n)))
    as lab'.
  move lab' before lab.
  remember (List.map fst lab') as llyz' eqn:Hllyzm'.
  move llyz' before llyz.
  move Hllyzm' before Hllyzm.
  remember (List.map snd lab') as lx_yz' eqn:Hlx_yzm'.
  move lx_yz' before lx_yz.
  move Hlx_yzm' before Hlx_yzm.
  assert (Hyz' :
    ∀ ab : list (T * T) * (T * T),
      ab ∈ lab'
      → (fst (snd ab) ∈ a)%I
(*
        ∧ length (fst ab) ≠ 0
*)
          ∧ (∀ x y : T, (x, y) ∈ fst ab → (x ∈ b)%I ∧ (y ∈ c)%I)
            ∧ snd (snd ab) = ∑ ((x, y) ∈ fst ab), x * y). {
    intros ab Hab.
    subst lab'.
    apply List.in_map_iff in Hab.
    destruct Hab as (ll & Hab1 & Hab2).
    apply List.in_app_or in Hab2.
    destruct Hab2 as [Hab2| Hab2]. {
      specialize (Hyz _ Hab2).
      subst ab.
...
    destruct Hab2 as [Hab2| Hab2]; [ now specialize (Hyz ab Hab) | ].
    apply List.repeat_spec in Hab.
    subst ab; cbn.
    split; [ apply i_zero | ].
    split. {
      intros y z H.
      apply List.repeat_spec in H.
      injection H; clear H; intros; subst y z.
      split; apply i_zero.
    }
    symmetry.
    rewrite rngl_summation_list_pair.
    apply all_0_rngl_summation_list_0.
    intros (x, y) H; cbn.
    apply List.repeat_spec in H.
    injection H; clear H; intros; subst x y.
    apply (rngl_mul_0_l Hos).
  }
  move Hyz' before Hyz.
  assert (H : length lab = n). {
    rewrite <- Hlx_yz.
    rewrite Hlx_yzm.
    symmetry; apply List.length_map.
  }
  assert (Hlx_yz' : length lx_yz' = m). {
    subst lx_yz' lab'.
    rewrite List.length_map.
    rewrite List.length_app.
    rewrite List.repeat_length, H, Nat.add_comm.
    apply Nat.sub_add.
    subst m.
    apply Nat.le_max_l.
  }
  move Hlx_yz' before Hlx_yz.
  move m before n.
  assert (Hllyz' : length llyz' = m). {
    subst llyz' lab'.
    rewrite List.length_map.
    rewrite List.length_app.
    rewrite List.repeat_length, H, Nat.add_comm, Hm.
    apply Nat.sub_add.
    subst m.
    apply Nat.le_max_l.
  }
  move Hllyz' before Hllyz.
  assert (Ht' : t = ∑ (x_yz ∈ lx_yz'), fst x_yz * snd x_yz). {
    rewrite (rngl_summation_list_split _ _ _ n).
    rewrite Hlx_yzm', Heqlab'.
    rewrite List.firstn_map, List.skipn_map.
    rewrite List.firstn_app, List.skipn_app.
    rewrite H, Nat.sub_diag.
    rewrite List.firstn_0, List.skipn_0.
    rewrite List.skipn_all2; [ | flia H ].
    rewrite List.app_nil_r.
    rewrite <- List.firstn_map.
    rewrite <- Hlx_yzm.
    rewrite List.firstn_all2; [ | flia Hlx_yz ].
    cbn.
    rewrite List.map_repeat.
    rewrite (all_0_rngl_summation_list_0 _ (List.repeat _ _)). 2: {
      intros (x, y) Hxy.
      apply List.repeat_spec in Hxy; cbn in Hxy.
      injection Hxy; clear Hxy; intros; subst x y.
      apply (rngl_mul_0_l Hos).
    }
    symmetry; rewrite Ht.
    apply rngl_add_0_r.
  }
  move Ht' before Ht.
  assert (H1 : ∀ l, l ∈ llyz' → length l = m). {
    intros l Hl.
    rewrite <- Hllyz'.
    rewrite Hllyzm' in Hl |-*.
    rewrite List.length_map.
    apply List.in_map_iff in Hl.
    destruct Hl as (l2 & Hl & Hl').
    subst l.
    rewrite Heqlab'.
    rewrite List.length_app.
    rewrite H, List.repeat_length, Nat.add_comm.
    rewrite Heqlab' in Hl'.
    apply List.in_app_or in Hl'.
    destruct Hl' as [Hl'| Hl']. {
...
  clear lx_yz llyz lab Hyz Ht Hlx_yz Hllyz Hllyzm Hlx_yzm Heqlab' H Hm.
...
assert
  (∃ lx ly lz,
   t = ∑ (i = 0, m), lx.[i] * ∑ (j = 0, m), ly.[j] * lz.[j]). {
...
erewrite rngl_summation_list_eq_compat in Ht. 2: {
  intros x_yz Hx_yz; cbn.
  specialize (Ha_bc (fst x_yz) (snd x_yz)).
  rewrite <- surjective_pairing in Ha_bc.
  specialize (Ha_bc Hx_yz).
  destruct Ha_bc as (Ha, Hbc).
  cbn in Hbc.
  progress unfold I_mul_subset in Hbc.
  destruct Hbc as (lxy & Hlxy & Hab & Hu).
  rewrite Hu.
...

Theorem I_mul_assoc a b c : (a * (b * c))%I = ((a * b) * c)%I.
Proof.
apply eq_ideal_eq; cbn.
apply functional_extensionality_dep.
...
*)

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

(* to be completed
Theorem I_mul_add_distr_l :
  ∀ a b c : ideal T, (a * (b + c))%I = (a * b + a * c)%I.
...
*)

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
