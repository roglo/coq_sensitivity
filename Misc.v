(* Theorems of general usage, which could be (or not) in Coq library *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Psatz Sorted Permutation Decidable.
Import List List.ListNotations.
Arguments length {A}.

(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Notation "n !" := (fact n) (at level 1, format "n !").
Notation "x '∈' l" := (List.In x l) (at level 70).
Notation "x '∉' l" := (¬ List.In x l) (at level 70).

Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level) :
                          nat_scope.
Notation "x < y ≤ z" := (x < y ∧ y <= z)%nat (at level 70, y at next level) :
                          nat_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%nat (at level 70, y at next level) :
                          nat_scope.
Notation "x < y < z" := (x < y ∧ y < z)%nat (at level 70, y at next level).

Notation "∃! x .. y , p" :=
  (ex (unique (λ x, .. (ex (unique (λ y, p))) ..)))
    (at level 200, x binder, right associativity)
  : type_scope.

Definition List_combine_all {A} (l1 l2 : list A) (d : A) :=
  let '(l'1, l'2) :=
    match List.length l1 ?= List.length l2 with
    | Eq => (l1, l2)
    | Lt => (l1 ++ List.repeat d (List.length l2 - List.length l1), l2)
    | Gt => (l1, l2 ++ List.repeat d (List.length l1 - List.length l2))
    end
  in
  List.combine l'1 l'2.

Theorem List_cons_app A (a : A) l : a :: l = [a] ++ l.
Proof. easy. Qed.

Theorem List_skipn_1 : ∀ A (l : list A), skipn 1 l = tl l.
Proof. easy. Qed.

Theorem List_fold_left_map :
  ∀ A B C (f : A → B → A) (g : C → B) (l : list C) a,
  fold_left f (map g l) a = fold_left (λ c b, f c (g b)) l a.
Proof.
intros.
revert a.
induction l as [| c]; intros; [ easy | apply IHl ].
Qed.

Theorem List_fold_left_id : ∀ A B (l : list B) (a : A),
  fold_left (λ c _, c) l a = a.
Proof.
intros A B l a.
now induction l.
Qed.

(* iterations in list of naturals
   in order to later define syntaxes : Max, Σ, Π, ...
   e.g. "Σ (i ∈ l), f i", "Π (i ∈ l), f i", ... *)

Definition iter_list {A B} (l : list B) f (d : A) := fold_left f l d.

(* iterations in indexed sequences
   in order to later define syntaxes : Max, Σ, Π, ...
   e.g. "Σ (i = b, e), f i", "Π (i = b, e), f i" *)

Definition iter_seq {T} b e f (d : T) := iter_list (seq b (S e - b)) f d.

Arguments iter_seq : simpl never.
Arguments iter_list : simpl never.

(* maximum of several values *)

Notation "'Max' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, max c (g)) 0)
  (at level 45, i at level 0, b at level 60, e at level 60) : nat_scope.

Notation "'Max' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, max c (g)) 0)
  (at level 45, i at level 0, l at level 60) : nat_scope.

Theorem fold_left_max_fun_from_0 : ∀ a l (f : nat → _),
  fold_left (λ c i, max c (f i)) l a =
  max a (fold_left (λ c i, max c (f i)) l 0).
Proof.
intros.
revert a.
induction l as [| x l]; intros; [ symmetry; apply Nat.max_0_r | cbn ].
rewrite IHl; symmetry; rewrite IHl.
now rewrite Nat.max_assoc.
Qed.

Theorem Max_fold_left_max : ∀ b e f,
  Max (i = b, e), f i = fold_left max (map f (seq b (S e - b))) 0.
Proof.
intros.
unfold iter_seq.
symmetry.
apply List_fold_left_map.
Qed.

Theorem Max_lub_lt : ∀ b e f n,
  0 < n
  → (∀ i, b ≤ i ≤ e → f i < n)
  → Max (i = b, e), f i < n.
Proof.
intros * Hn Hf.
unfold iter_seq.
remember (S e - b) as len eqn:Hlen.
destruct len; [ easy | ].
replace e with (b + len) in Hf by flia Hlen.
clear e Hlen.
revert b Hf.
induction len; intros. {
  now apply Hf; rewrite Nat.add_0_r.
}
unfold iter_list.
remember (S len) as slen; cbn; subst slen.
rewrite fold_left_max_fun_from_0.
remember (fold_left _ _ _) as x eqn:Hx.
destruct (le_dec (f b) x) as [Hfx| Hfx]. {
  rewrite Nat.max_r; [ | easy ].
  subst x.
  apply IHlen.
  intros i Hi.
  apply Hf; flia Hi.
}
rewrite Nat.max_l; [ | flia Hfx ].
apply Hf; flia.
Qed.

Theorem Max_lub_le : ∀ b e f n,
  (∀ i, b ≤ i ≤ e → f i ≤ n)
  → Max (i = b, e), f i ≤ n.
Proof.
intros * Hf.
unfold iter_seq.
remember (S e - b) as len eqn:Hlen.
destruct len; [ apply Nat.le_0_l | ].
replace e with (b + len) in Hf by flia Hlen.
clear e Hlen.
revert b Hf.
induction len; intros. {
  now apply Hf; rewrite Nat.add_0_r.
}
unfold iter_list.
remember (S len) as slen; cbn; subst slen.
rewrite fold_left_max_fun_from_0.
remember (fold_left _ _ _) as x eqn:Hx.
destruct (le_dec (f b) x) as [Hfx| Hfx]. {
  rewrite Nat.max_r; [ | easy ].
  subst x.
  apply IHlen.
  intros i Hi.
  apply Hf; flia Hi.
}
rewrite Nat.max_l; [ | flia Hfx ].
apply Hf; flia.
Qed.

Theorem Max_le_compat : ∀ b e g h,
  (∀ i, b ≤ i ≤ e → g i ≤ h i)
  → Max (i = b, e), g i ≤ Max (i = b, e), h i.
Proof.
intros * Hgh.
unfold iter_seq, iter_list; cbn - [ "-" ].
remember (S e - b) as n eqn:Hn.
remember 0 as a eqn:Ha; clear Ha.
revert a b Hn Hgh.
induction n as [| n IHn]; intros; [ easy | cbn ].
do 2 rewrite (fold_left_max_fun_from_0 (max _ _)).
do 2 rewrite <- Nat.max_assoc.
apply Nat.max_le_compat_l.
apply Nat.max_le_compat; [ apply Hgh; flia Hn | ].
apply IHn; [ flia Hn | ].
intros i Hbie.
apply Hgh; flia Hbie.
Qed.

Theorem fold_iter_list : ∀ {A B} (f : A → B → A) l d,
  fold_left f l d = iter_list l f d.
Proof. easy. Qed.

Theorem fold_iter_seq : ∀ {T} b e f (d : T),
  fold_left f (seq b (S e - b)) d = iter_seq b e f d.
Proof. easy. Qed.

Theorem fold_iter_seq_2 : ∀ {T} b len f (d : T),
  0 < b + len
  → fold_left f (seq b len) d = iter_seq b (b + len - 1) f d.
Proof.
intros * Hblen.
unfold iter_seq.
now replace (S (b + len - 1) - b) with len by flia Hblen.
Qed.

Theorem List_seq_cut : ∀ i sta len,
  i ∈ seq sta len
  → seq sta len = seq sta (i - sta) ++ [i] ++ seq (S i) (sta + len - S i).
Proof.
intros * His.
apply in_seq in His.
replace len with (i - sta + (len - (i - sta))) at 1 by flia His.
rewrite seq_app.
f_equal.
replace (sta + (i - sta)) with i by flia His.
replace (len - (i - sta)) with (1 + (sta + len - S i)) by flia His.
rewrite seq_app; cbn.
now rewrite Nat.add_1_r.
Qed.

Theorem List_sorted_in_seq : ∀ sta len a b la1 la2 la3,
  seq sta len = la1 ++ a :: la2 ++ b :: la3 → a < b.
Proof.
intros * Hs.
revert sta a b la1 la2 la3 Hs.
induction len; intros. {
  apply (f_equal length) in Hs; cbn in Hs.
  rewrite app_length in Hs; cbn in Hs.
  rewrite app_length in Hs; cbn in Hs.
  flia Hs.
}
cbn in Hs.
destruct la1 as [| c]. {
  cbn in Hs.
  injection Hs; clear Hs; intros Hs H; subst a.
  assert (H : b ∈ seq (S sta) len). {
    rewrite Hs.
    now apply in_app_iff; right; left.
  }
  now apply in_seq in H.
}
cbn in Hs.
injection Hs; clear Hs; intros Hs H; subst c.
now apply IHlen in Hs.
Qed.

Theorem List_seq_nothing_after_last : ∀ n n' la1 la2 la3,
  ¬ seq 0 (S n) = la1 ++ n :: la2 ++ n' :: la3.
Proof.
intros * Hs.
assert (H : n' ≤ n). {
  assert (H : n' ∈ seq 0 (S n)). {
    rewrite Hs.
    apply in_app_iff; right; right.
    now apply in_app_iff; right; left.
  }
  apply in_seq in H.
  now apply Nat.lt_succ_r.
}
apply List_sorted_in_seq in Hs.
now apply Nat.nlt_ge in H.
Qed.

Theorem iter_shift : ∀ {T} b k f (d : T),
  b ≤ k
  → iter_seq b k f d =
    iter_seq 0 (k - b) (λ c i, f c (b + i)) d.
Proof.
intros * Hbk.
unfold iter_seq, iter_list.
rewrite Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | easy ].
remember (S k - b)%nat as len; clear Heqlen.
clear k Hbk.
revert b d.
induction len; intros; [ easy | ].
rewrite seq_S; symmetry.
rewrite seq_S; symmetry.
do 2 rewrite fold_left_app; cbn.
now rewrite IHlen.
Qed.

Theorem fold_left_add_fun_from_0 {A} : ∀ a l (f : A → nat),
  fold_left (λ c i, c + f i) l a =
  a + fold_left (λ c i, c + f i) l 0.
Proof.
intros.
revert a.
induction l as [| x l]; intros; [ symmetry; apply Nat.add_0_r | cbn ].
rewrite IHl; symmetry; rewrite IHl.
apply Nat.add_assoc.
Qed.

Theorem fold_left_mul_fun_from_1 {A} : ∀ a l (f : A → nat),
  fold_left (λ c i, c * f i) l a =
  a * fold_left (λ c i, c * f i) l 1.
Proof.
intros.
revert a.
induction l as [| x l]; intros; [ symmetry; apply Nat.mul_1_r | cbn ].
rewrite IHl; symmetry; rewrite IHl.
rewrite Nat.add_0_r.
apply Nat.mul_assoc.
Qed.

Theorem fold_left_mul_from_1 : ∀ a l,
  fold_left Nat.mul l a = a * fold_left Nat.mul l 1.
Proof.
intros.
revert a.
induction l as [| x l]; intros; [ symmetry; apply Nat.mul_1_r | cbn ].
rewrite IHl; symmetry; rewrite IHl.
rewrite Nat.add_0_r.
apply Nat.mul_assoc.
Qed.

Theorem fold_right_max_ge : ∀ m l, m ≤ fold_right max m l.
Proof.
intros.
induction l as [| a]; [ easy | cbn ].
etransitivity; [ apply IHl | ].
apply Nat.le_max_r.
Qed.

(* *)

Theorem match_id {A} : ∀ a (b : A), match a with O => b | S _ => b end = b.
Proof. now intros; destruct a. Qed.

Theorem Nat_sub_sub_swap : ∀ a b c, a - b - c = a - c - b.
Proof.
intros.
rewrite <- Nat.sub_add_distr.
rewrite Nat.add_comm.
now rewrite Nat.sub_add_distr.
Qed.

Theorem Nat_add_div_same : ∀ a b c,
  Nat.divide c a
  → a / c + b / c = (a + b) / c.
Proof.
intros * Hca.
destruct (Nat.eq_dec c 0) as [Hcz| Hcz]; [ now subst c | ].
destruct Hca as (d, Hd).
rewrite Hd, Nat.div_mul; [ | easy ].
now rewrite Nat.div_add_l.
Qed.

Theorem Nat_sub_div_same: ∀ a b c,
  Nat.divide c a
  → Nat.divide c b
  → a / c - b / c = (a - b) / c.
Proof.
intros * Hca Hcb.
destruct (Nat.eq_dec c 0) as [Hcz| Hcz]; [ now subst c | ].
destruct Hca as (ka, Hka).
destruct Hcb as (kb, Hkb).
subst a b.
rewrite Nat.div_mul; [ | easy ].
rewrite Nat.div_mul; [ | easy ].
rewrite <- Nat.mul_sub_distr_r.
now rewrite Nat.div_mul.
Qed.

Theorem Nat_mod_add_same_l : ∀ a b, a ≠ 0 → (a + b) mod a = b mod a.
Proof.
intros * Ha.
rewrite <- Nat.add_mod_idemp_l; [ | easy ].
now rewrite Nat.mod_same.
Qed.

Theorem Nat_mod_add_same_r : ∀ a b, b ≠ 0 → (a + b) mod b = a mod b.
Proof.
intros * Ha.
rewrite <- Nat.add_mod_idemp_r; [ | easy ].
now rewrite Nat.mod_same, Nat.add_0_r.
Qed.

Theorem Nat_div_add_same_l : ∀ a b, a ≠ 0 → (a + b) / a = 1 + b / a.
Proof.
intros * Ha.
replace a with (1 * a) at 1 by apply Nat.mul_1_l.
rewrite Nat.add_comm.
rewrite Nat.div_add; [ apply Nat.add_comm | easy ].
Qed.

Theorem Nat_div_add_same_r : ∀ a b, b ≠ 0 → (a + b) / b = a / b + 1.
Proof.
intros * Ha.
replace b with (1 * b) at 1 by apply Nat.mul_1_l.
now rewrite Nat.div_add.
Qed.

Theorem Nat_sub_succ_1 : ∀ n, S n - 1 = n.
Proof. now intros; rewrite Nat.sub_succ, Nat.sub_0_r. Qed.

Theorem Nat_eq_mod_sub_0 : ∀ a b c,
  a mod c = b mod c → (a - b) mod c = 0.
Proof.
intros * Hab.
destruct (Nat.eq_dec c 0) as [Hcz| Hcz]. {
  subst c; cbn in Hab |-*.
  subst; flia.
}
specialize (Nat.div_mod a c Hcz) as H1.
specialize (Nat.div_mod b c Hcz) as H2.
rewrite H1, H2, Hab.
rewrite (Nat.add_comm (c * (b / c))).
rewrite Nat.sub_add_distr, Nat.add_sub.
rewrite <- Nat.mul_sub_distr_l, Nat.mul_comm.
now apply Nat.mod_mul.
Qed.

Theorem Nat_mod_add_r_mul_l : ∀ a b c,
  b ≠ 0 → (a + b * c) mod b = a mod b.
Proof.
intros * Hbz.
rewrite Nat.mul_comm.
now apply Nat.mod_add.
Qed.

Theorem Nat_mod_add_l_mul_l : ∀ a b c,
  b ≠ 0 → (b * c + a) mod b = a mod b.
Proof.
intros * Hbz.
rewrite Nat.add_comm, Nat.mul_comm.
now apply Nat.mod_add.
Qed.

Theorem Nat_mod_add_l_mul_r : ∀ a b c,
  b ≠ 0 → (c * b + a) mod b = a mod b.
Proof.
intros * Hbz.
rewrite Nat.add_comm.
now apply Nat.mod_add.
Qed.

Theorem Nat_mod_0_mod_div : ∀ a b,
  0 < b ≤ a → a mod b = 0 → a mod (a / b) = 0.
Proof.
intros * Hba Ha.
assert (Hbz : b ≠ 0) by flia Hba.
assert (Habz : a / b ≠ 0). {
  intros H.
  apply Nat.div_small_iff in H; [ | flia Hba ].
  now apply Nat.nle_gt in H.
}
specialize (Nat.div_mod a (a / b) Habz) as H1.
specialize (Nat.div_mod a b Hbz) as H2.
rewrite Ha, Nat.add_0_r in H2.
rewrite H2 in H1 at 3.
rewrite Nat.div_mul in H1; [ | easy ].
rewrite Nat.mul_comm in H1.
flia H1 H2.
Qed.

Theorem Nat_mod_0_div_div : ∀ a b,
  0 < b ≤ a → a mod b = 0 → a / (a / b) = b.
Proof.
intros * Hba Ha.
assert (Hbz : b ≠ 0) by flia Hba.
assert (Habz : a / b ≠ 0). {
  intros H.
  apply Nat.div_small_iff in H; [ | easy ].
  now apply Nat.nle_gt in H.
}
specialize (Nat.div_mod a (a / b) Habz) as H1.
rewrite Nat_mod_0_mod_div in H1; [ | easy | easy ].
rewrite Nat.add_0_r in H1.
apply (Nat.mul_cancel_l _ _ (a / b)); [ easy | ].
rewrite <- H1; symmetry.
rewrite Nat.mul_comm.
apply Nat.mod_divide in Ha; [ | easy ].
rewrite <- Nat.divide_div_mul_exact; [ | easy | easy ].
now rewrite Nat.mul_comm, Nat.div_mul.
Qed.

Theorem Nat_fact_succ : ∀ n, fact (S n) = S n * fact n.
Proof. easy. Qed.

Theorem Nat_div_lt_le_mul : ∀ a b c, b ≠ 0 → a / b < c → a ≤ b * c.
Proof.
intros * Hbz Habc.
apply (Nat.mul_le_mono_l _ _ b) in Habc.
transitivity (b * S (a / b)); [ | easy ].
specialize (Nat.div_mod a b Hbz) as H1.
rewrite <- Nat.add_1_r.
rewrite Nat.mul_add_distr_l, Nat.mul_1_r.
rewrite H1 at 1.
apply Nat.add_le_mono_l.
now apply Nat.lt_le_incl, Nat.mod_upper_bound.
Qed.

Theorem Nat_div_interv : ∀ n a b,
  n * b ≤ a < (n + 1) * b
  → a / b = n.
Proof.
intros * Hn.
revert a b Hn.
induction n; intros.
-rewrite Nat.mul_0_l, Nat.mul_1_l in Hn.
 now apply Nat.div_small.
-specialize (IHn (a - b) b) as H1.
 assert (H : n * b ≤ a - b < (n + 1) * b). {
   destruct Hn as (H2, H3).
   assert (Hba : b ≤ a). {
     eapply Nat.le_trans; [ | apply H2 ].
     apply Nat.le_add_r.
   }
   split.
   -apply (Nat.add_le_mono_r _ _ b).
    replace (n * b + b) with (S n * b) by apply Nat.add_comm.
    rewrite Nat.sub_add; [ apply H2 | easy ].
   -apply (Nat.add_lt_mono_r _ _ b).
    rewrite Nat.sub_add; [ | easy ].
    rewrite Nat.add_1_r in H3; cbn in H3.
    rewrite Nat.add_1_r; cbn.
    now rewrite Nat.add_assoc, Nat.add_shuffle0 in H3.
 }
 specialize (H1 H); clear H.
 assert (H : b ≤ a). {
   apply (Nat.mul_le_mono_pos_l _ _ (S n)); [ apply Nat.lt_0_succ | ].
   eapply le_trans; [ apply Hn | apply Nat.le_add_r ].
 }
 destruct b.
 +now do 2 rewrite Nat.mul_0_r in Hn.
 +replace a with (S b + (a - S b)); cycle 1. {
    rewrite Nat.add_sub_assoc; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  rewrite Nat_div_add_same_l; [ | easy ].
  rewrite Nat.add_1_l.
  now f_equal.
Qed.

Theorem Nat_le_add_l : ∀ a b, b ≤ a + b.
Proof.
intros.
replace b with (0 + b) at 1 by easy.
apply Nat.add_le_mono_r.
apply Nat.le_0_l.
Qed.

Theorem Nat_mul_sub_div_le : ∀ a b c,
  c ≤ a * b
  → (a * b - c) / b ≤ a.
Proof.
intros * Hc.
destruct (zerop b) as [Hb| Hb]. {
  subst b; cbn; apply Nat.le_0_l.
}
apply Nat.neq_0_lt_0 in Hb.
remember (a * b - c) as d eqn:Hd.
assert (H1 : a = (c + d) / b). {
  rewrite Hd.
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  now rewrite Nat.div_mul.
}
rewrite H1.
apply Nat.div_le_mono; [ easy | ].
apply Nat_le_add_l.
Qed.

Theorem Nat_mod_less_small : ∀ n a b,
  n * b ≤ a < (n + 1) * b
  → a mod b = a - n * b.
Proof.
intros * Hab.
assert (Hb : b ≠ 0). {
  now intros Hb; rewrite Hb, (Nat.mul_comm (n + 1)) in Hab.
}
replace a with (a - n * b + n * b) at 1 by now apply Nat.sub_add.
rewrite Nat.mod_add; [ | easy ].
apply Nat.mod_small.
apply Nat.add_lt_mono_r with (p := n * b).
rewrite Nat.add_comm in Hab; cbn in Hab.
now rewrite Nat.sub_add.
Qed.

Theorem Nat_div_less_small : ∀ n a b,
  n * b ≤ a < (n + 1) * b
  → a / b = n.
Proof.
intros * Hab.
assert (Hb : b ≠ 0). {
  now intros Hb; rewrite Hb, (Nat.mul_comm (n + 1)) in Hab.
}
replace a with (a - n * b + n * b) at 1 by now apply Nat.sub_add.
rewrite Nat.div_add; [ | easy ].
replace n with (0 + n) at 3 by easy; f_equal.
apply Nat.div_small.
apply Nat.add_lt_mono_r with (p := n * b).
rewrite Nat.add_comm in Hab; cbn in Hab.
now rewrite Nat.sub_add.
Qed.

Theorem Nat_divide_fact_fact : ∀ n d, Nat.divide (fact (n - d)) (fact n).
Proof.
intros *.
revert n.
induction d; intros; [ rewrite Nat.sub_0_r; apply Nat.divide_refl | ].
destruct n; [ apply Nat.divide_refl | ].
rewrite Nat.sub_succ.
apply (Nat.divide_trans _ (fact n)); [ apply IHd | ].
rewrite Nat_fact_succ.
now exists (S n).
Qed.

Theorem Nat_divide_small_fact : ∀ n k, 0 < k ≤ n → Nat.divide k (fact n).
Proof.
intros * Hkn.
revert k Hkn.
induction n; intros; [ flia Hkn | ].
rewrite Nat_fact_succ.
destruct (Nat.eq_dec k (S n)) as [Hksn| Hksn]. {
  rewrite Hksn.
  apply Nat.divide_factor_l.
}
apply (Nat.divide_trans _ (fact n)). {
  apply IHn; flia Hkn Hksn.
}
apply Nat.divide_factor_r.
Qed.

Theorem Nat_divide_mul_fact : ∀ n a b,
  0 < a ≤ n
  → 0 < b ≤ n
  → a < b
  → Nat.divide (a * b) (fact n).
Proof.
intros * Han Hbn Hab.
exists (fact (a - 1) * (fact (b - 1) / fact a) * (fact n / fact b)).
rewrite Nat.mul_comm.
rewrite (Nat.mul_shuffle0 _ b).
do 2 rewrite Nat.mul_assoc.
replace (a * fact (a - 1)) with (fact a). 2: {
  destruct a; [ flia Han | ].
  rewrite Nat_fact_succ.
  now rewrite Nat.sub_succ, Nat.sub_0_r.
}
replace (fact a * (fact (b - 1) / fact a)) with (fact (b - 1)). 2: {
  specialize (Nat_divide_fact_fact (b - 1) (b - 1 - a)) as H1.
  replace (b - 1 - (b - 1 - a)) with a in H1 by flia Hab.
  destruct H1 as (c, Hc).
  rewrite Hc, Nat.div_mul; [ | apply fact_neq_0 ].
  apply Nat.mul_comm.
}
rewrite Nat.mul_comm, Nat.mul_assoc.
replace (b * fact (b - 1)) with (fact b). 2: {
  destruct b; [ flia Hbn | ].
  rewrite Nat_fact_succ.
  now rewrite Nat.sub_succ, Nat.sub_0_r.
}
replace (fact b * (fact n / fact b)) with (fact n). 2: {
  specialize (Nat_divide_fact_fact n (n - b)) as H1.
  replace (n - (n - b)) with b in H1 by flia Hbn.
  destruct H1 as (c, Hc).
  rewrite Hc, Nat.div_mul; [ | apply fact_neq_0 ].
  apply Nat.mul_comm.
}
easy.
Qed.

(** Bezout commutes *)

Theorem Nat_bezout_comm : ∀ a b g,
  b ≠ 0 → Nat.Bezout a b g → Nat.Bezout b a g.
Proof.
intros * Hbz (u & v & Huv).
destruct (Nat.eq_0_gt_0_cases a) as [Haz| Haz]. {
  rewrite Haz in Huv |-*.
  rewrite Nat.mul_0_r in Huv; symmetry in Huv.
  apply Nat.eq_add_0 in Huv.
  rewrite (proj1 Huv).
  now exists 0, 0; Nat.nzsimpl.
}
apply Nat.neq_0_lt_0 in Haz.
destruct (Nat.lt_trichotomy (u / b) (v / a)) as [Hm|Hm]. {
  apply Nat.lt_le_incl in Hm.
  remember (v / a + 1) as k eqn:Hk.
  exists (k * a - v), (k * b - u).
  do 2 rewrite Nat.mul_sub_distr_r.
  rewrite Huv.
  rewrite (Nat.add_comm _ (v * b)).
  rewrite Nat.sub_add_distr.
  rewrite Nat.add_sub_assoc. 2: {
    apply (Nat.add_le_mono_r _ _ (v * b)).
    rewrite <- Huv.
    rewrite Nat.sub_add. 2: {
      rewrite Nat.mul_shuffle0.
      apply Nat.mul_le_mono_r.
      rewrite Hk.
      specialize (Nat.div_mod v a Haz) as H1.
      rewrite Nat.mul_add_distr_r, Nat.mul_1_l, Nat.mul_comm.
      rewrite H1 at 1.
      apply Nat.add_le_mono_l.
      apply Nat.lt_le_incl.
      apply Nat.mod_bound_pos; [ apply Nat.le_0_l | ].
      now apply Nat.neq_0_lt_0.
    }
    apply Nat.mul_le_mono_r.
    rewrite Hk.
    specialize (Nat.div_mod u b Hbz) as H1.
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l, Nat.mul_comm.
    rewrite H1 at 1.
    apply Nat.add_le_mono; [ now apply Nat.mul_le_mono_l | ].
    apply Nat.lt_le_incl.
    apply Nat.mod_bound_pos; [ apply Nat.le_0_l | ].
    now apply Nat.neq_0_lt_0.
  }
  rewrite Nat.add_comm, Nat.add_sub.
  now rewrite Nat.mul_shuffle0.
} {
  remember (u / b + 1) as k eqn:Hk.
  exists (k * a - v), (k * b - u).
  do 2 rewrite Nat.mul_sub_distr_r.
  rewrite Huv.
  rewrite (Nat.add_comm _ (v * b)).
  rewrite Nat.sub_add_distr.
  rewrite Nat.add_sub_assoc. 2: {
    apply (Nat.add_le_mono_r _ _ (v * b)).
    rewrite Nat.sub_add. 2: {
      rewrite Nat.mul_shuffle0.
      apply Nat.mul_le_mono_r.
      rewrite Hk.
      specialize (Nat.div_mod v a Haz) as H1.
      rewrite Nat.mul_add_distr_r, Nat.mul_1_l, Nat.mul_comm.
      rewrite H1 at 1.
      apply Nat.add_le_mono. {
        apply Nat.mul_le_mono_l.
        destruct Hm as [Hm| Hm]; [ now rewrite Hm | ].
        now apply Nat.lt_le_incl.
      }
      apply Nat.lt_le_incl.
      apply Nat.mod_bound_pos; [ apply Nat.le_0_l | ].
      now apply Nat.neq_0_lt_0.
    }
    rewrite <- Huv.
    apply Nat.mul_le_mono_r.
    rewrite Hk.
    specialize (Nat.div_mod u b Hbz) as H1.
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l, Nat.mul_comm.
    rewrite H1 at 1.
    apply Nat.add_le_mono_l.
    apply Nat.lt_le_incl.
    apply Nat.mod_bound_pos; [ apply Nat.le_0_l | ].
    now apply Nat.neq_0_lt_0.
  }
  rewrite Nat.add_comm, Nat.add_sub.
  now rewrite Nat.mul_shuffle0.
}
Qed.

Theorem Nat_bezout_mul : ∀ a b c,
  Nat.Bezout a c 1
  → Nat.Bezout b c 1
  → Nat.Bezout (a * b) c 1.
Proof.
intros * (ua & uc & Hu) (vb & vc & Hv).
exists (ua * vb).
replace (ua * vb * (a * b)) with ((ua * a) * (vb * b)) by flia.
rewrite Hu, Hv.
exists (uc * vc * c + uc + vc).
ring.
Qed.

Theorem Nat_gcd_le_l : ∀ a b, a ≠ 0 → Nat.gcd a b ≤ a.
Proof.
intros * Haz.
specialize (Nat.gcd_divide_l a b) as H1.
destruct H1 as (c, Hc); rewrite Hc at 2.
destruct c; [ easy | flia ].
Qed.

Theorem Nat_gcd_le_r : ∀ a b, b ≠ 0 → Nat.gcd a b ≤ b.
Proof.
intros * Hbz.
specialize (Nat.gcd_divide_r a b) as H1.
destruct H1 as (c, Hc); rewrite Hc at 2.
destruct c; [ easy | flia ].
Qed.

Theorem Nat_gcd_1_mul_l : ∀ a b c,
  Nat.gcd a c = 1
  → Nat.gcd b c = 1
  → Nat.gcd (a * b) c = 1.
Proof.
intros * Hac Hbc.
destruct (Nat.eq_dec c 0) as [Hcz| Hcz]. {
  now subst c; rewrite Nat.gcd_comm in Hac, Hbc; cbn in Hac, Hbc; subst a b.
}
destruct (Nat.eq_dec a 0) as [Haz| Haz]; [ now subst a | ].
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]. {
  now subst b; rewrite Nat.mul_0_r.
}
apply Nat.bezout_1_gcd.
apply Nat_bezout_mul. {
  rewrite <- Hac.
  apply Nat.gcd_bezout_pos.
  flia Haz.
} {
  rewrite <- Hbc.
  apply Nat.gcd_bezout_pos.
  flia Hbz.
}
Qed.

Theorem Nat_gcd_1_mul_r : ∀ a b c,
  Nat.gcd a b = 1
  → Nat.gcd a c = 1
  → Nat.gcd a (b * c) = 1.
Proof.
intros * Hab Hac.
rewrite Nat.gcd_comm.
now apply Nat_gcd_1_mul_l; rewrite Nat.gcd_comm.
Qed.

Theorem Nat_gcd_sub_diag_l : ∀ m n, n ≤ m → Nat.gcd m (m - n) = Nat.gcd m n.
Proof.
intros * Hnm.
replace m with (n + (m - n)) at 1 by flia Hnm.
rewrite Nat.gcd_comm.
rewrite Nat.gcd_add_diag_r.
rewrite Nat.gcd_comm.
rewrite Nat.gcd_sub_diag_r; [ | easy ].
apply Nat.gcd_comm.
Qed.

(* (a ^ b) mod c defined like that so that we can use "Compute"
   for testing; proved equal to (a ^ b) mod c just below *)

Fixpoint Nat_pow_mod_loop a b c :=
  match b with
  | 0 => 1 mod c
  | S b' => (a * Nat_pow_mod_loop a b' c) mod c
  end.

Definition Nat_pow_mod a b c := Nat_pow_mod_loop a b c.

Theorem Nat_pow_mod_is_pow_mod : ∀ a b c,
  c ≠ 0 → Nat_pow_mod a b c = (a ^ b) mod c.
Proof.
intros * Hcz.
revert a.
induction b; intros; [ easy | ].
cbn; rewrite IHb.
now rewrite Nat.mul_mod_idemp_r.
Qed.

Theorem Nat_sqr_sub_sqr : ∀ a b, a ^ 2 - b ^ 2 = (a + b) * (a - b).
Proof.
intros.
destruct (lt_dec a b) as [Hab| Hba]. {
  rewrite (proj2 (Nat.sub_0_le _ _)). 2: {
    now apply Nat.pow_le_mono_l, Nat.lt_le_incl.
  }
  rewrite (proj2 (Nat.sub_0_le _ _)). 2: {
    now apply Nat.lt_le_incl.
  }
  now rewrite Nat.mul_0_r.
}
apply Nat.nlt_ge in Hba.
rewrite Nat.mul_add_distr_r.
rewrite Nat.mul_sub_distr_l.
rewrite Nat.mul_sub_distr_l.
rewrite Nat.add_sub_assoc; [ | now apply Nat.mul_le_mono_l ].
rewrite (Nat.mul_comm b).
rewrite Nat.sub_add; [ | now apply Nat.mul_le_mono_l ].
now do 2 rewrite Nat.pow_2_r.
Qed.

Theorem Nat_sqr_sub_1 : ∀ a, a ^ 2 - 1 = (a + 1) * (a - 1).
Proof.
intros.
destruct (Nat.eq_dec a 0) as [Haz| Haz]; [ now subst a | ].
rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
rewrite Nat.add_sub_assoc; [ | flia Haz ].
rewrite Nat.pow_2_r.
rewrite Nat.sub_add; [ easy | ].
destruct a; [ easy | flia ].
Qed.

Theorem Nat_sub_sub_assoc : ∀ a b c,
  c ≤ b ≤ a + c
  → a - (b - c) = a + c - b.
Proof.
intros * (Hcb, Hba).
revert a c Hcb Hba.
induction b; intros.
-apply Nat.le_0_r in Hcb; subst c.
 now rewrite Nat.add_0_r.
-destruct c; [ now rewrite Nat.add_0_r | ].
 apply Nat.succ_le_mono in Hcb.
 rewrite Nat.add_succ_r in Hba.
 apply Nat.succ_le_mono in Hba.
 specialize (IHb a c Hcb Hba) as H1.
 rewrite Nat.sub_succ, H1.
 rewrite Nat.add_succ_r.
 now rewrite Nat.sub_succ.
Qed.

Theorem Nat_sub_sub_distr : ∀ a b c, c ≤ b ≤ a → a - (b - c) = a - b + c.
Proof.
intros.
rewrite <- Nat.add_sub_swap; [ | easy ].
apply Nat_sub_sub_assoc.
split; [ easy | ].
apply (Nat.le_trans _ a); [ easy | ].
apply Nat.le_add_r.
Qed.

Theorem Nat_sqr_sub : ∀ a b, b ≤ a → (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b.
Proof.
intros * Hba.
do 3 rewrite Nat.pow_2_r.
rewrite Nat.mul_sub_distr_l.
do 2 rewrite Nat.mul_sub_distr_r.
rewrite (Nat.mul_comm b).
rewrite <- Nat.sub_add_distr.
rewrite Nat.add_comm.
rewrite Nat.sub_add_distr.
rewrite Nat_sub_sub_distr. 2: {
  split; [ now apply Nat.mul_le_mono_r | now apply Nat.mul_le_mono_l ].
}
replace 2 with (1 + 1) by easy.
rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
rewrite Nat.mul_add_distr_r.
rewrite Nat.sub_add_distr; f_equal.
rewrite Nat.add_sub_swap; [ easy | ].
now apply Nat.mul_le_mono_l.
Qed.

Theorem Nat_sqr_add : ∀ a b, (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b.
Proof.
intros.
do 3 rewrite Nat.pow_2_r; flia.
Qed.

Theorem Nat_mod_pow_mod : ∀ a b c, (a mod b) ^ c mod b = a ^ c mod b.
Proof.
intros.
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]; [ now subst b | ].
revert a b Hbz.
induction c; intros; [ easy | cbn ].
rewrite Nat.mul_mod_idemp_l; [ | easy ].
rewrite <- Nat.mul_mod_idemp_r; [ | easy ].
rewrite IHc; [ | easy ].
now rewrite Nat.mul_mod_idemp_r.
Qed.

Theorem Nat_mul_le_pos_l : ∀ a b, 1 ≤ a → b ≤ a * b.
Proof.
intros * Ha.
replace b with (1 * b) at 1 by apply Nat.mul_1_l.
apply Nat.mul_le_mono_nonneg_r; [ apply Nat.le_0_l | easy ].
Qed.

Theorem Nat_mul_le_pos_r : ∀ a b, 1 ≤ b → a ≤ a * b.
Proof.
intros * Ha.
replace a with (a * 1) at 1 by apply Nat.mul_1_r.
apply Nat.mul_le_mono_nonneg_l; [ apply Nat.le_0_l | easy ].
Qed.

Notation "a ≡ b 'mod' c" := (a mod c = b mod c) (at level 70, b at level 36).
Notation "a ≢ b 'mod' c" := (a mod c ≠ b mod c) (at level 70, b at level 36).

Theorem Nat_mul_mod_cancel_r : ∀ a b c n,
  Nat.gcd c n = 1
  → a * c ≡ (b * c) mod n
  → a ≡ b mod n.
Proof.
intros * Hg Hab.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  cbn in Hab.
  rewrite Nat.gcd_0_r in Hg.
  subst c.
  do 2 rewrite Nat.mul_1_r in Hab.
  now subst a.
}
destruct (le_dec b a) as [Hba| Hba]. {
  apply Nat_eq_mod_sub_0 in Hab.
  rewrite <- Nat.mul_sub_distr_r in Hab.
  apply Nat.mod_divide in Hab; [ | easy ].
  rewrite Nat.gcd_comm in Hg.
  rewrite Nat.mul_comm in Hab.
  specialize (Nat.gauss n c (a - b) Hab Hg) as H1.
  destruct H1 as (k, Hk).
  replace a with (b + k * n) by flia Hba Hk.
  now rewrite Nat.mod_add.
} {
  apply Nat.nle_gt in Hba.
  symmetry in Hab.
  apply Nat_eq_mod_sub_0 in Hab.
  rewrite <- Nat.mul_sub_distr_r in Hab.
  apply Nat.mod_divide in Hab; [ | easy ].
  rewrite Nat.gcd_comm in Hg.
  rewrite Nat.mul_comm in Hab.
  specialize (Nat.gauss n c (b - a) Hab Hg) as H1.
  destruct H1 as (k, Hk).
  replace b with (a + k * n) by flia Hba Hk.
  now rewrite Nat.mod_add.
}
Qed.

Theorem Nat_mul_mod_cancel_l : ∀ a b c n,
  Nat.gcd c n = 1
  → c * a ≡ (c * b) mod n
  → a ≡ b mod n.
Proof.
intros * Hg Hab.
setoid_rewrite Nat.mul_comm in Hab.
now apply Nat_mul_mod_cancel_r in Hab.
Qed.

Theorem Nat_eq_max_0 : ∀ a b, max a b = 0 → a = 0 ∧ b = 0.
Proof.
intros * Hm.
destruct (le_dec a b) as [H| H]. {
  rewrite Nat.max_r in Hm; [ | easy ].
  now subst b; apply Nat.le_0_r in H.
}
apply Nat.nle_gt, Nat.lt_le_incl in H.
rewrite Nat.max_l in Hm; [ | easy ].
now subst a; apply Nat.le_0_r in H.
Qed.

Theorem Nat_le_fold_left_max : ∀ ln n k,
  n ≤ k → n ≤ fold_left max ln k.
Proof.
intros * Hnk.
revert k Hnk.
induction ln as [| m]; intros; [ easy | ].
apply IHln.
transitivity k; [ easy | ].
apply Nat.le_max_l.
Qed.

Theorem Nat_le_fold_left_fold_left_max : ∀ lln n k,
  n ≤ k → n ≤ fold_left (λ m ln, fold_left max ln m) lln k.
Proof.
intros * Hnk.
revert k Hnk.
induction lln as [| ln]; intros; [ easy | cbn ].
apply IHlln.
now apply Nat_le_fold_left_max.
Qed.

Theorem Nat_fold_left_max_le : ∀ nl n k,
  n ≤ k
  → fold_left max nl n ≤ fold_left max nl k.
Proof.
intros * Hkn.
revert n k Hkn.
induction nl as [| n1]; intros; [ easy | cbn ].
apply IHnl.
now apply Nat.max_le_compat_r.
Qed.

Theorem Nat_fold_left_fold_left_max_le : ∀ nll a b,
  a ≤ b
  → fold_left (λ m nl, fold_left max nl m) nll a ≤
     fold_left (λ m nl, fold_left max nl m) nll b.
Proof.
intros * Hab.
revert a b Hab.
induction nll as [| nl]; intros; [ easy | cbn ].
apply IHnll.
now apply Nat_fold_left_max_le.
Qed.

Definition Nat_le_neq_lt : ∀ x y : nat, x ≤ y → x ≠ y → (x < y)%nat :=
  λ x y Hxy Hnxy,
  match le_lt_eq_dec x y Hxy with
  | left Hle => Hle
  | right Heq => match Hnxy Heq with end
  end.

Theorem List_hd_nth_0 {A} : ∀ l (d : A), hd d l = nth 0 l d.
Proof. intros; now destruct l. Qed.

Theorem List_map_map_map {A B C D} : ∀ (f : A → B → C) (g : A → D → B) h l,
  map (λ d, map (f d) (map (g d) (h d))) l =
  map (λ d, map (λ x, (f d (g d x))) (h d)) l.
Proof.
intros.
induction l as [| a l]; [ easy | cbn ].
now rewrite List.map_map, IHl.
Qed.

Theorem List_flat_map_length {A B} : ∀ (l : list A) (f : _ → list B),
  length (flat_map f l) =
    List.fold_right Nat.add 0 (map length (map f l)).
Proof.
intros.
induction l as [| a l]; [ easy | cbn ].
now rewrite app_length, IHl.
Qed.

Theorem List_last_seq : ∀ i n, n ≠ 0 → last (seq i n) 0 = i + n - 1.
Proof.
intros * Hn.
destruct n; [ easy | clear Hn ].
revert i; induction n; intros. {
  cbn; symmetry.
  apply Nat.add_sub.
}
remember (S n) as sn; cbn; subst sn.
remember (seq (S i) (S n)) as l eqn:Hl.
destruct l; [ easy | ].
rewrite Hl.
replace (i + S (S n)) with (S i + S n) by flia.
apply IHn.
Qed.

Theorem List_last_In {A} : ∀ (d : A) l, l ≠ [] → In (last l d) l.
Proof.
intros * Hl.
destruct l as [| a l]; [ easy | clear Hl ].
revert a.
induction l as [| b l]; intros; [ now left | ].
remember (b :: l) as l'; cbn; subst l'.
right; apply IHl.
Qed.

Theorem List_last_app_not_nil_r : ∀ A (la lb : list A) d,
  lb ≠ []
  → last (la ++ lb) d = last lb d.
Proof.
intros A * Hlb.
destruct lb as [| b]; [ easy | clear Hlb ].
revert b lb.
induction la as [| a]; intros; [ easy | cbn ].
rewrite IHla.
remember (la ++ b :: lb) as lc eqn:Hlc.
destruct lc as [| c]; [ | easy ].
now destruct la.
Qed.

Theorem List_last_app {A} : ∀ l (d a : A), List.last (l ++ [a]) d = a.
Proof.
intros.
now apply List_last_app_not_nil_r.
Qed.

Theorem List_rev_last : ∀ A l (d : A),
  last (rev l) d = hd d l.
Proof.
intros.
induction l; [ easy | cbn ].
apply List_last_app.
Qed.

Theorem List_map_fun : ∀ A B d l l' (f : A → B),
  length l = length l'
  → (∀ i, f (nth i l d) = f (nth i l' d))
  → map f l = map f l'.
Proof.
intros * Hlen Hf.
revert l' Hlen Hf.
induction l as [| a l]; intros; [ now destruct l' | ].
destruct l' as [| a' l']; [ easy | cbn ].
specialize (Hf 0) as H1; cbn in H1.
rewrite H1; f_equal.
cbn in Hlen; apply Nat.succ_inj in Hlen.
apply IHl; [ easy | ].
intros i.
now specialize (Hf (S i)).
Qed.

Theorem List_map_nth_in : ∀ A B (f : A → B) a b l n,
  n < length l → nth n (map f l) b = f (nth n l a).
Proof.
intros * Hnl.
revert n Hnl.
induction l as [| c l]; intros; [ easy | ].
cbn in Hnl; cbn.
destruct n; [ easy | ].
apply Nat.succ_lt_mono in Hnl.
now apply IHl.
Qed.

Theorem List_seq_eq_nil : ∀ b len, seq b len = [] → len = 0.
Proof.
intros * Hb.
now induction len.
Qed.

Theorem List_firstn_seq : ∀ n start len,
  firstn n (seq start len) = seq start (min n len).
Proof.
intros.
revert start len.
induction n; intros; [ easy | cbn ].
remember (seq start len) as l eqn:Hl; symmetry in Hl.
destruct l as [| a l]; [ now destruct len | ].
destruct len; [ easy | cbn in Hl; cbn ].
injection Hl; clear Hl; intros Hl Ha.
subst start; f_equal.
rewrite <- Hl; apply IHn.
Qed.

Theorem List_filter_all_true {A} : ∀ f (l : list A),
  (∀ a, a ∈ l → f a = true) → filter f l = l.
Proof.
intros * Hf.
induction l as [| a l]; [ easy | ].
cbn; rewrite Hf; [ | now left ].
rewrite IHl; [ easy | ].
intros b Hb.
apply Hf.
now right.
Qed.

Theorem List_filter_all_false {A} : ∀ f (l : list A),
  (∀ a, a ∈ l → f a = false) → filter f l = [].
Proof.
intros * Hf.
induction l as [| a l]; [ easy | ].
cbn; rewrite Hf; [ | now left ].
apply IHl; intros b Hb.
now apply Hf; right.
Qed.

Theorem List_filter_nil {A} : ∀ f (l : list A),
  filter f l = [] → (∀ a, a ∈ l → f a = false).
Proof.
intros * Hf a Ha.
induction l as [| b l]; [ easy | ].
cbn in Hf.
remember (f b) as c eqn:Hc; symmetry in Hc.
destruct c; [ easy | ].
destruct Ha as [Ha| Ha]; [ now subst b | ].
now apply IHl.
Qed.

Theorem List_filter_filter {A} : ∀ (f g : A → _) l,
  filter f (filter g l) = filter (λ a, andb (f a) (g a)) l.
Proof.
intros.
induction l as [| a l]; [ easy | cbn ].
remember (andb (f a) (g a)) as b eqn:Hb; symmetry in Hb.
destruct b. {
  apply Bool.andb_true_iff in Hb.
  rewrite (proj2 Hb); cbn.
  rewrite (proj1 Hb); cbn.
  now rewrite IHl.
} {
  apply Bool.andb_false_iff in Hb.
  destruct Hb as [Hb| Hb]. {
    remember (g a) as c eqn:Hc; symmetry in Hc.
    destruct c; [ | apply IHl ].
    cbn; rewrite Hb.
    apply IHl.
  } {
    rewrite Hb; cbn.
    apply IHl.
  }
}
Qed.

Theorem List_filter_filter_comm {A} : ∀ (f : A → _) g l,
  filter f (filter g l) = filter g (filter f l).
Proof.
intros.
induction l as [| a l]; [ easy | cbn ].
remember (g a) as bg eqn:Hbg; symmetry in Hbg.
remember (f a) as bf eqn:Hbf; symmetry in Hbf.
move bf before bg.
destruct bg, bf; cbn. {
  rewrite Hbg, Hbf.
  now rewrite IHl.
} {
  now rewrite Hbf, IHl.
} {
  now rewrite Hbg, IHl.
} {
  apply IHl.
}
Qed.

Theorem List_fold_filter_comm {A B} : ∀ f g (al : list A) (l : list B),
  fold_left (λ l a, filter (f a) l) al (filter g l) =
  filter g (fold_left (λ l a, filter (f a) l) al l).
Proof.
intros.
revert l.
induction al as [| a al]; intros; [ easy | ].
cbn.
rewrite <- IHal.
now rewrite List_filter_filter_comm.
Qed.

Theorem List_length_cons : ∀ A (a : A) la, length (a :: la) = S (length la).
Proof. easy. Qed.

Theorem List_length_filter_negb {A} : ∀ f (l : list A),
  NoDup l
  → length (filter f l) = length l - length (filter (λ x, negb (f x)) l).
Proof.
intros * Hl.
induction l as [| a l]; [ easy | ].
cbn - [ "-" ].
remember (f a) as b eqn:Hb; symmetry in Hb.
destruct b; cbn - [ "-" ]. {
  rewrite IHl; [ | now apply NoDup_cons_iff in Hl ].
  rewrite Nat.sub_succ_l; [ easy | ].
  clear.
  induction l as [| a l]; [ easy | cbn ].
  destruct (negb (f a)); cbn. {
    now apply Nat.succ_le_mono in IHl.
  } {
    transitivity (length l); [ easy | flia ].
  }
} {
  rewrite Nat.sub_succ.
  apply IHl.
  now apply NoDup_cons_iff in Hl.
}
Qed.

Theorem List_length_filter_or {A B} : ∀ (p q : A) (l : list B) f g,
  length (filter (λ a, (f p a || g q a)%bool) l) =
  length (filter (f p) l) + length (filter (g q) l) -
  length (filter (λ a, (f p a && g q a)%bool) l).
Proof.
intros.
induction l as [| a l]; [ easy | cbn ].
remember (f p a) as b eqn:Hb; symmetry in Hb.
remember (g q a) as c eqn:Hc; symmetry in Hc.
assert (Hpq :
  length (filter (λ a, (f p a && g q a)%bool) l) ≤
  length (filter (f p) l) + length (filter (g q) l)). {
  clear.
  induction l as [| a l]; [ easy | cbn ].
  remember (f p a) as b eqn:Hb; symmetry in Hb.
  remember (g q a) as c eqn:Hc; symmetry in Hc.
  destruct b, c; cbn; [ flia IHl | flia IHl | flia IHl | easy ].
}
destruct b, c; cbn - [ "-" ]. {
  rewrite IHl.
  rewrite <- Nat.sub_succ_l; [ flia | easy ].
} {
  rewrite IHl.
  now rewrite <- Nat.sub_succ_l.
} {
  rewrite IHl.
  rewrite <- Nat.sub_succ_l; [ flia | easy ].
} {
  apply IHl.
}
Qed.

(* map2: map with two lists *)

Fixpoint map2 {A B C} (f : A → B → C) la lb :=
  match la with
  | [] => []
  | a :: la' =>
      match lb with
      | [] => []
      | b :: lb' => f a b :: map2 f la' lb'
      end
  end.
Theorem map2_nth : ∀ A B C (f : A → B → C) la lb a b c n,
  n < length la
  → n < length lb
  → nth n (map2 f la lb) c = f (nth n la a) (nth n lb b).
Proof.
intros * Hla Hlb.
revert n lb Hla Hlb.
induction la as [| a']; intros; [ easy | cbn ].
destruct lb as [| b']; [ easy | cbn ].
destruct n; [ easy | cbn ].
cbn in Hla, Hlb.
apply Nat.succ_lt_mono in Hla.
apply Nat.succ_lt_mono in Hlb.
destruct n; [ now apply IHla | ].
now apply IHla.
Qed.

Theorem map2_map_l : ∀ A B C D (f : C → B → D) g (la : list A) (lb : list B),
  map2 f (map g la) lb = map2 (λ a b, f (g a) b) la lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
f_equal.
apply IHla.
Qed.

Theorem map2_map_r : ∀ A B C D (f : A → C → D) g (la : list A) (lb : list B),
  map2 f la (map g lb) = map2 (λ a b, f a (g b)) la lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
f_equal.
apply IHla.
Qed.

Theorem List_fold_left_map2 :
  ∀ A B C D (f : A → B → A) (g : C → D → B) lc ld (a : A),
  fold_left f (map2 g lc ld) a =
  fold_left (λ b c, f b (g (fst c) (snd c))) (combine lc ld) a.
Proof.
intros.
revert ld a.
induction lc as [| c]; intros; [ easy | cbn ].
destruct ld as [| d]; [ easy | cbn ].
apply IHlc.
Qed.

Theorem map2_length : ∀ A B C (f : A → B → C) la lb,
  length (map2 f la lb) = min (length la) (length lb).
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
now rewrite IHla.
Qed.

(* end map2 *)

Theorem not_equiv_imp_False : ∀ P : Prop, (P → False) ↔ ¬ P.
Proof. easy. Qed.

Theorem Sorted_Sorted_seq : ∀ start len, Sorted.Sorted lt (seq start len).
Proof.
intros.
revert start.
induction len; intros; [ apply Sorted.Sorted_nil | ].
cbn; apply Sorted.Sorted_cons; [ apply IHlen | ].
clear IHlen.
induction len; [ apply Sorted.HdRel_nil | ].
cbn. apply Sorted.HdRel_cons.
apply Nat.lt_succ_diag_r.
Qed.

Theorem Forall_inv_tail {A} : ∀ P (a : A) l, Forall P (a :: l) → Forall P l.
Proof.
intros * HF.
now inversion HF.
Qed.

Theorem NoDup_app_comm {A} : ∀ l l' : list A,
  NoDup (l ++ l') → NoDup (l' ++ l).
Proof.
intros * Hll.
revert l Hll.
induction l' as [| a l']; intros; [ now rewrite app_nil_r in Hll | ].
cbn; constructor. {
  intros Ha.
  apply NoDup_remove_2 in Hll; apply Hll.
  apply in_app_or in Ha.
  apply in_or_app.
  now destruct Ha; [ right | left ].
}
apply IHl'.
now apply NoDup_remove_1 in Hll.
Qed.

Theorem List_in_app_app_swap {A} : ∀ (a : A) l1 l2 l3,
  In a (l1 ++ l3 ++ l2)
  → In a (l1 ++ l2 ++ l3).
Proof.
intros * Hin.
revert l2 l3 Hin.
induction l1 as [| a2 l1]; intros. {
  cbn in Hin; cbn.
  apply in_app_or in Hin.
  apply in_or_app.
  now destruct Hin; [ right | left ].
}
cbn in Hin; cbn.
destruct Hin as [Hin| Hin]; [ now left | right ].
now apply IHl1.
Qed.

Theorem List_in_removelast : ∀ A l (x : A), x ∈ removelast l → x ∈ l.
Proof.
intros * Hx.
revert x Hx.
induction l as [| a]; intros; [ easy | ].
cbn in Hx.
destruct l as [| b]; [ easy | ].
destruct Hx as [Hx| Hx]; [ now left | right ].
now apply IHl.
Qed.

Theorem List_fold_left_ext_in : ∀ A B (f g : A → B → A) l a,
  (∀ b c, b ∈ l → f c b = g c b)
  → fold_left f l a = fold_left g l a.
Proof.
intros * Hfg.
revert a.
induction l as [| d]; intros; [ easy | cbn ].
rewrite (Hfg d a); [ | now left ].
apply IHl.
intros b c Hb.
apply Hfg.
now right.
Qed.

Theorem List_fold_left_mul_assoc : ∀ a b l,
  fold_left Nat.mul l a * b = fold_left Nat.mul l (a * b).
Proof.
intros.
revert a b.
induction l as [| c l]; intros; [ easy | ].
cbn; rewrite IHl.
now rewrite Nat.mul_shuffle0.
Qed.

Theorem List_fold_left_max_map_le : ∀ A (l : list A) d f g,
  (∀ i, i ∈ l → f i ≤ g i)
  → fold_left max (map f l) d ≤ fold_left max (map g l) d.
Proof.
intros A * Hfg.
revert d.
induction l as [| a]; intros; [ easy | cbn ].
etransitivity. {
  apply IHl.
  intros i Hi.
  now apply Hfg; right.
}
apply Nat_fold_left_max_le.
apply Nat.max_le_compat_l.
apply Hfg.
now left.
Qed.

Theorem List_apply_fold_left : ∀ A B C x l (f : B → A → B) (g : B → C),
  (∀ y i, i ∈ l → g (f y i) = g y)
  → g (fold_left f l x) = g x.
Proof.
intros * Hg.
revert x.
induction l as [| y]; intros; [ easy | cbn ].
rewrite IHl. 2: {
  intros z i Hi.
  now apply Hg; right.
}
now apply Hg; left.
Qed.

Theorem List_firstn_map {A B} : ∀ n l (f : A → B),
  firstn n (map f l) = map f (firstn n l).
Proof.
intros.
revert n.
induction l as [| a l]; intros; [ now cbn; do 2 rewrite firstn_nil | ].
destruct n; [ easy | cbn ].
now rewrite IHl.
Qed.

Theorem List_list_prod_nil_r {A B} : ∀ l : list A,
  list_prod l ([] : list B) = [].
Proof.
intros.
now induction l.
Qed.

Theorem List_eq_rev_nil {A} : ∀ (l : list A), rev l = [] → l = [].
Proof.
intros * Hl.
destruct l as [| a]; [ easy | cbn in Hl ].
now apply app_eq_nil in Hl.
Qed.

Theorem List_eq_rev_l : ∀ A (la lb : list A),
  rev la = lb → la = rev lb.
Proof.
intros * Hll.
subst lb; symmetry.
apply rev_involutive.
Qed.

Theorem List_eq_rev_r : ∀ A (la lb : list A),
  la = rev lb → rev la = lb.
Proof.
intros * Hll.
subst la.
apply rev_involutive.
Qed.

Theorem List_rev_inj : ∀ A (la lb : list A), rev la = rev lb → la = lb.
Proof.
intros A * Hll.
apply List_eq_rev_l in Hll.
now rewrite rev_involutive in Hll.
Qed.

Theorem List_repeat_succ_app : ∀ A (a : A) n,
  repeat a (S n) = repeat a n ++ [a].
Proof.
intros A *.
induction n; [ easy | ].
now cbn; f_equal.
Qed.

Theorem List_rev_repeat : ∀ A (a : A) n, rev (repeat a n) = repeat a n.
Proof.
intros.
induction n; [ easy | ].
rewrite List_repeat_succ_app at 2; cbn.
now rewrite IHn.
Qed.

Theorem List_nth_repeat : ∀ A (a d : A) i n,
  nth i (repeat a n) d = if lt_dec i n then a else d.
Proof.
intros A *.
destruct (lt_dec i n) as [Hin| Hin]. {
  revert i Hin.
  induction n; intros; [ easy | cbn ].
  destruct i; [ easy | ].
  apply Nat.succ_lt_mono in Hin.
  now apply IHn.
}
apply Nat.nlt_ge in Hin.
apply nth_overflow.
now rewrite repeat_length.
Qed.

Theorem List_nth_error_Some_iff : ∀ A (l : list A) n x d,
  nth_error l n = Some x ↔ nth n l d = x ∧ n < length l.
Proof.
intros.
split. {
  intros Hx.
  split; [ now apply nth_error_nth | ].
  apply nth_error_Some.
  congruence.
} {
  intros (Hn, Hx).
  subst x.
  now apply nth_error_nth'.
}
Qed.

Theorem List_app_cons : ∀ A (l1 l2 : list A) a,
  l1 ++ a :: l2 = l1 ++ [a] ++ l2.
Proof. easy. Qed.

Theorem List_last_nth : ∀ A l (d : A), last l d = nth (length l - 1) l d.
Proof.
intros.
destruct l as [| a]; [ easy | ].
cbn - [ last nth ].
rewrite Nat.sub_0_r.
revert a.
induction l as [| b]; intros; [ easy | ].
cbn - [ last nth ].
remember (b :: l) as l'; cbn; subst l'.
apply IHl.
Qed.

Theorem List_last_nth_cons : ∀ A l (a d : A),
  last (a :: l) d = nth (length l) (a :: l) d.
Proof.
intros.
rewrite List_last_nth.
now cbn; rewrite Nat.sub_0_r.
Qed.

Theorem List_last_cons_cons : ∀ A l (x y d : A),
  last (x :: y :: l) d = last (y :: l) d.
Proof. easy. Qed.

Theorem List_skipn_map : ∀ A B (f : A → B) l n,
  skipn n (map f l) = map f (skipn n l).
Proof.
intros.
revert n.
induction l as [| a]; intros; [ now do 2 rewrite skipn_nil | cbn ].
destruct n; [ easy | cbn; apply IHl ].
Qed.

Theorem List_skipn_seq : ∀ n start len,
  n ≤ len → skipn n (seq start len) = seq (start + n) (len - n).
Proof.
intros * Hnlen.
revert n start Hnlen.
induction len; intros; [ now rewrite skipn_nil | cbn ].
destruct n; [ now cbn; rewrite Nat.add_0_r | cbn ].
rewrite <- Nat.add_succ_comm.
apply Nat.succ_le_mono in Hnlen.
now apply IHlen.
Qed.

Theorem List_skipn_cons_nth_skipn_succ : ∀ A n (l : list A) d,
  n < length l
  → skipn n l = nth n l d :: skipn (S n) l.
Proof.
intros * Hn.
revert l Hn.
induction n; intros; [ now destruct l | ].
destruct l as [| a]; [ easy | ].
cbn in Hn.
apply Nat.succ_lt_mono in Hn.
remember (S (S n)) as sn; cbn; subst sn.
remember (S n) as sn; cbn; subst sn.
now apply IHn.
Qed.

Theorem List_skipn_last : ∀ A (la : list A) d,
  la ≠ []
  → skipn (length la - 1) la = [last la d].
Proof.
intros * Hla.
destruct la as [| a]; [ easy | clear Hla ].
cbn - [ skipn last ].
rewrite Nat.sub_0_r.
rewrite List_skipn_cons_nth_skipn_succ with (d := d); [ | cbn; flia ].
f_equal; [ | apply skipn_all ].
symmetry.
apply List_last_nth_cons.
Qed.

Theorem List_eq_iff : ∀ A (l1 l2 : list A),
  l1 = l2 ↔ (length l1 = length l2 ∧ ∀ d i, nth i l1 d = nth i l2 d).
Proof.
split; [ now intros; subst l2 | ].
intros (Hlen & Hll).
revert l2 Hlen Hll.
induction l1 as [| a1]; intros. {
  symmetry in Hlen.
  now apply length_zero_iff_nil in Hlen.
}
destruct l2 as [| a2]; [ easy | ].
cbn in Hlen.
apply Nat.succ_inj in Hlen.
f_equal; [ apply (Hll a1 0) | ].
apply IHl1; [ easy | ].
intros.
now specialize (Hll d (S i)).
Qed.

Theorem List_eq_map_seq : ∀ A (la : list A) d,
  la = map (λ i, nth i la d) (seq 0 (length la)).
Proof.
intros.
induction la as [| a]; [ easy | ].
cbn; f_equal.
rewrite <- seq_shift.
now rewrite map_map.
Qed.

(* common for summations and products *)

Theorem fold_left_op_fun_from_d : ∀ T A d op a l (f : A → _)
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  fold_left (λ (c : T) i, op c (f i)) l a =
  op a (fold_left (λ (c : T) i, op c (f i)) l d).
Proof.
intros.
revert a.
induction l as [| x l]; intros; [ symmetry; apply op_d_r | cbn ].
rewrite IHl; symmetry; rewrite IHl.
rewrite op_d_l.
apply op_assoc.
Qed.

Theorem iter_list_all_d : ∀ T A d op (l : list A) f
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  (∀ i, i ∈ l → f i = d)
  → iter_list l (λ (c : T) i, op c (f i)) d = d.
Proof.
intros * op_d_l op_d_r op_assoc Hz.
unfold iter_list.
induction l as [| a]; [ easy | cbn ].
rewrite (fold_left_op_fun_from_d d); [ | easy | easy | easy ].
rewrite IHl. {
  rewrite op_d_l, op_d_r.
  now apply Hz; left.
}
intros i Hi.
apply Hz.
now right.
Qed.

Theorem iter_seq_all_d : ∀ T d op b e f
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  (∀ i : nat, b ≤ i ≤ e → f i = d)
  → iter_seq b e (λ (c : T) (i : nat), op c (f i)) d = d.
Proof.
intros * op_d_l od_d_r op_assoc Hz.
apply iter_list_all_d; [ easy | easy | easy | ].
intros i Hi.
apply in_seq in Hi.
apply Hz; flia Hi.
Qed.

Theorem iter_list_split_first : ∀ T A d op l z f
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  l ≠ []
  → iter_list l (λ (c : T) (i : A), op c (f i)) d =
    op (f (hd z l)) (iter_list (tl l) (λ (c : T) (i : A), op c (f i)) d).
Proof.
intros * op_d_l op_d_r op_assoc Hl.
unfold iter_list.
destruct l as [| a]; [ easy | cbn ].
rewrite op_d_l.
now rewrite fold_left_op_fun_from_d with (d := d).
Qed.

Theorem iter_seq_split_first : ∀ T d op b k g
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  b ≤ k
  → iter_seq b k (λ (c : T) (i : nat), op c (g i)) d =
    op (g b) (iter_seq (S b) k (λ (c : T) (i : nat), op c (g i)) d).
Proof.
intros * op_d_l op_d_r op_assoc Hbk.
unfold iter_seq, iter_list.
remember (S k - b) as len eqn:Hlen.
replace (S k - S b) with (len - 1) by flia Hlen.
assert (H : len ≠ 0) by flia Hlen Hbk.
clear k Hbk Hlen.
rename H into Hlen.
destruct len; [ easy | cbn ].
rewrite op_d_l, Nat.sub_0_r.
apply fold_left_op_fun_from_d. {
  apply op_d_l.
} {
  apply op_d_r.
} {
  apply op_assoc.
}
Qed.

Theorem iter_list_split_last : ∀ T A d (op : T → T → T) l (g : A → T) z,
  l ≠ []
  → iter_list l (λ c i, op c (g i)) d =
    op (iter_list (removelast l) (λ c i, op c (g i)) d) (g (last l z)).
Proof.
intros * Hlz.
unfold iter_list.
induction l as [| a] using rev_ind; [ easy | clear IHl Hlz ].
rewrite removelast_last.
rewrite last_last.
now rewrite fold_left_app.
Qed.

Theorem List_removelast_seq : ∀ b len,
  len ≠ 0
  → removelast (seq b len) = seq b (len - 1).
Proof.
intros * Hlen.
destruct len; [ easy | clear Hlen ].
rewrite seq_S.
rewrite removelast_last; cbn.
now rewrite Nat.sub_0_r.
Qed.

Theorem iter_seq_split_last : ∀ T d (op : T → T → T) b k g,
  b ≤ k
  → iter_seq b k (λ (c : T) (i : nat), op c (g i)) d =
    op (iter_seq (S b) k (λ (c : T) (i : nat), op c (g (i - 1)%nat)) d) (g k).
Proof.
intros * Hbk.
unfold iter_seq, iter_list.
remember (S k - S b) as len eqn:Hlen.
rewrite Nat.sub_succ in Hlen.
replace (S k - b) with (S len) by flia Hbk Hlen.
replace k with (b + len) by flia Hbk Hlen.
rewrite <- seq_shift.
rewrite List_fold_left_map.
rewrite seq_S.
rewrite fold_left_app.
cbn; f_equal.
apply List_fold_left_ext_in.
intros i c Hi.
now rewrite Nat.sub_0_r.
Qed.

Theorem iter_seq_split : ∀ T d op j g b k
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
   b ≤ S j ≤ S k
  → iter_seq b k (λ (c : T) (i : nat), op c (g i)) d =
    op (iter_seq b j (λ (c : T) (i : nat), op c (g i)) d)
      (iter_seq (j + 1) k (λ (c : T) (i : nat), op c (g i)) d).
Proof.
intros * op_d_l op_d_r op_assoc (Hbj, Hjk).
unfold iter_seq, iter_list.
remember (S j - b) as len1 eqn:Hlen1.
remember (S k - b) as len2 eqn:Hlen2.
move len2 before len1.
replace (S k - (j + 1)) with (len2 - len1) by flia Hlen1 Hlen2 Hbj.
replace (j + 1) with (b + len1) by flia Hlen1 Hbj.
assert (Hll : len1 ≤ len2) by flia Hlen1 Hlen2 Hjk.
clear - Hll op_d_l op_d_r op_assoc.
revert b len2 Hll.
induction len1; intros. {
  cbn; rewrite Nat.add_0_r, Nat.sub_0_r; symmetry.
  apply op_d_l.
}
destruct len2; [ flia Hll | ].
apply Nat.succ_le_mono in Hll; cbn.
rewrite op_d_l.
rewrite (fold_left_op_fun_from_d d _ (g b)); [ | easy | easy | easy ].
rewrite (fold_left_op_fun_from_d d _ (g b)); [ | easy | easy | easy ].
rewrite <- op_assoc; f_equal.
replace len2 with (len1 + (len2 - len1)) at 1 by flia Hll.
rewrite seq_app, fold_left_app.
rewrite (fold_left_op_fun_from_d d); [ | easy | easy | easy ].
now rewrite Nat.add_succ_comm.
Qed.

Theorem iter_list_app : ∀ A B (d : A) (f : A → B → A) la lb,
  iter_list (la ++ lb) f d = iter_list lb f (iter_list la f d).
Proof.
intros.
unfold iter_list.
now rewrite fold_left_app.
Qed.

Theorem iter_list_cons : ∀ A B d op (a : B) la f
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  iter_list (a :: la) (λ (c : A) i, op c (f i)) d =
  op (f a) (iter_list la (λ (c : A) i, op c (f i)) d).
Proof.
intros.
unfold iter_list; cbn.
rewrite op_d_l.
now apply (fold_left_op_fun_from_d d).
Qed.

Theorem iter_list_eq_compat : ∀ A B d (op : A → A → A) (l : list B) g h,
  (∀ i, i ∈ l → g i = h i)
  → iter_list l (λ c i, op c (g i)) d =
    iter_list l (λ c i, op c (h i)) d.
Proof.
intros * Hgh.
unfold iter_list.
revert d.
induction l as [| a]; intros; [ easy | cbn ].
rewrite Hgh; [ | now left ].
apply IHl.
intros i Hi.
apply Hgh.
now right.
Qed.

Theorem iter_seq_eq_compat : ∀ T d (op : T → T → T) b k g h,
  (∀ i, b ≤ i ≤ k → g i = h i)
  → iter_seq b k (λ c i, op c (g i)) d =
    iter_seq b k (λ c i, op c (h i)) d.
Proof.
intros * Hgh.
apply iter_list_eq_compat.
intros i Hi.
apply Hgh.
apply in_seq in Hi.
flia Hi.
Qed.

Theorem iter_seq_succ_succ : ∀ {T} (d : T) b k f,
  iter_seq (S b) (S k) f d =
  iter_seq b k (λ c i, f c (S i)) d.
Proof.
intros.
unfold iter_seq, iter_list.
rewrite Nat.sub_succ.
remember (S k - b)%nat as len; clear Heqlen.
rewrite <- seq_shift.
now rewrite List_fold_left_map.
Qed.

Theorem iter_seq_succ_succ' : ∀ {T} (d : T) b k f,
  iter_seq (S b) (S k) (λ c i, f c (i - 1)) d =
  iter_seq b k (λ c i, f c i) d.
Proof.
intros.
unfold iter_seq, iter_list.
rewrite Nat.sub_succ.
rewrite <- seq_shift.
rewrite List_fold_left_map.
apply List_fold_left_ext_in.
intros j i Hj.
f_equal.
rewrite Nat.sub_succ.
apply Nat.sub_0_r.
Qed.

Theorem iter_seq_empty : ∀ T d (op : T → T → T) b k g,
  k < b
  → iter_seq b k (λ (c : T) (i : nat), op c (g i)) d = d.
Proof.
intros * Hkb.
unfold iter_seq.
now replace (S k - b) with 0 by flia Hkb.
Qed.

Theorem iter_list_distr : ∀ T A d op g h (l : list A)
  (op_d_l : ∀ x, op d x = x)
  (op_comm : ∀ a b, op a b = op b a)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  iter_list l (λ (c : T) (i : A), op c (op (g i) (h i))) d =
  op (iter_list l (λ (c : T) (i : A), op c (g i)) d)
    (iter_list l (λ (c : T) (i : A), op c (h i)) d).
Proof.
intros.
unfold iter_list.
induction l as [| a]; [ symmetry; apply op_d_l | cbn ].
rewrite (fold_left_op_fun_from_d d); [ | easy | | easy ]. 2: {
  intros; rewrite op_comm; apply op_d_l.
}
symmetry.
rewrite (fold_left_op_fun_from_d d); [ | easy | | easy ]. 2: {
  intros; rewrite op_comm; apply op_d_l.
}
rewrite fold_iter_list.
rewrite (fold_left_op_fun_from_d d); [ | easy | | easy ]. 2: {
  intros; rewrite op_comm; apply op_d_l.
}
rewrite IHl.
do 2 rewrite fold_iter_list.
remember (iter_list _ _ _) as b eqn:Hb in |-*.
remember (iter_list _ _ _) as c eqn:Hc in |-*.
do 3 rewrite op_d_l.
do 2 rewrite op_assoc.
f_equal.
symmetry.
rewrite (op_comm _ b).
rewrite op_assoc.
f_equal.
apply op_comm.
Qed.

Theorem iter_seq_distr : ∀ T d op g h b k
  (op_d_l : ∀ x, op d x = x)
  (op_comm : ∀ a b, op a b = op b a)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  iter_seq b k (λ (c : T) (i : nat), (op c (op (g i) (h i)))) d =
  op
    (iter_seq b k (λ (c : T) (i : nat), op c (g i)) d)
    (iter_seq b k (λ (c : T) (i : nat), op c (h i)) d).
Proof.
intros.
now apply iter_list_distr.
Qed.

Theorem iter_seq_inv : ∀ T d op inv b e f
  (inv_d : inv d = d)
  (inv_op_distr : ∀ a b, inv (op a b) = op (inv a) (inv b)),
  inv (iter_seq b e (λ (c : T) (i : nat), op c (f i)) d) =
  iter_seq b e (λ (c : T) (i : nat), op c (inv (f i))) d.
Proof.
intros.
unfold iter_seq, iter_list.
remember (S e - b) as len.
clear e Heqlen.
revert b.
induction len; intros; [ now apply inv_d | ].
rewrite seq_S; cbn.
rewrite fold_left_app; cbn.
rewrite fold_left_app; cbn.
rewrite <- IHlen.
now rewrite inv_op_distr.
Qed.

(* *)

Theorem NoDup_app_app_swap {A} : ∀ l1 l2 l3 : list A,
  NoDup (l1 ++ l2 ++ l3) → NoDup (l1 ++ l3 ++ l2).
Proof.
intros * Hlll.
revert l2 l3 Hlll.
induction l1 as [| a1 l1]; intros; [ now cbn; apply NoDup_app_comm | ].
cbn; constructor. {
  intros Hin.
  cbn in Hlll.
  apply NoDup_cons_iff in Hlll.
  destruct Hlll as (Hin2, Hlll).
  apply Hin2; clear Hin2.
  now apply List_in_app_app_swap.
}
apply IHl1.
cbn in Hlll.
now apply NoDup_cons_iff in Hlll.
Qed.

Theorem NoDup_concat_rev {A} : ∀ (ll : list (list A)),
  NoDup (concat (rev ll)) → NoDup (concat ll).
Proof.
intros * Hll.
destruct ll as [| l ll]; [ easy | ].
cbn; cbn in Hll.
rewrite concat_app in Hll; cbn in Hll.
rewrite app_nil_r in Hll.
apply NoDup_app_comm.
revert l Hll.
induction ll as [| l' ll]; intros; [ easy | ].
cbn in Hll; cbn.
rewrite concat_app in Hll; cbn in Hll.
rewrite app_nil_r, <- app_assoc in Hll.
rewrite <- app_assoc.
apply NoDup_app_app_swap.
rewrite app_assoc.
apply NoDup_app_comm.
now apply IHll.
Qed.

Theorem NoDup_filter {A} : ∀ (f : A → _) l, NoDup l → NoDup (filter f l).
Proof.
intros * Hnd.
induction l as [| a l]; [ easy | cbn ].
remember (f a) as b eqn:Hb; symmetry in Hb.
apply NoDup_cons_iff in Hnd.
destruct Hnd as (Hal, Hl).
destruct b. {
  constructor; [ | now apply IHl ].
  intros H; apply Hal.
  now apply filter_In in H.
}
now apply IHl.
Qed.

Theorem NoDup_map_iff {A B} : ∀ d l (f : A → B),
  NoDup (map f l)
  ↔ (∀ i j,
      i < length l → j < length l → f (nth i l d) = f (nth j l d) → i = j).
Proof.
intros.
split. {
  intros Hnd i j Hi Hj Hij.
  revert i j Hi Hj Hij.
  induction l as [| a l]; intros; [ easy | ].
  cbn in Hnd.
  apply NoDup_cons_iff in Hnd.
  destruct Hnd as (Hnin, Hnd).
  specialize (IHl Hnd).
  destruct i. {
    destruct j; [ easy | exfalso ].
    cbn in Hij, Hj; clear Hi.
    apply Nat.succ_lt_mono in Hj.
    rewrite Hij in Hnin; apply Hnin; clear Hnin.
    now apply in_map, nth_In.
  }
  cbn in Hi, Hj.
  destruct j; [ exfalso | ]. {
    cbn in Hij, Hj; clear Hj.
    apply Nat.succ_lt_mono in Hi.
    rewrite <- Hij in Hnin; apply Hnin; clear Hnin.
    now apply in_map, nth_In.
  }
  apply Nat.succ_lt_mono in Hi.
  apply Nat.succ_lt_mono in Hj.
  cbn in Hij.
  f_equal.
  now apply IHl.
} {
  intros Hinj.
  induction l as [| a l]; [ constructor | cbn ].
  apply NoDup_cons. {
    intros Hcon.
    apply in_map_iff in Hcon.
    destruct Hcon as (b & Hba & Hb).
    symmetry in Hba.
    apply (In_nth _ _ d) in Hb.
    destruct Hb as (n & Hlen & Hnth).
    specialize (Hinj 0 (S n)) as H1.
    cbn in H1; rewrite Hnth in H1.
    apply Nat.succ_lt_mono in Hlen.
    now specialize (H1 (Nat.lt_0_succ _) Hlen Hba).
  }
  apply IHl.
  intros i j Hi Hj Hij.
  apply Nat.succ_lt_mono in Hi.
  apply Nat.succ_lt_mono in Hj.
  specialize (Hinj (S i) (S j) Hi Hj Hij) as H1.
  now apply Nat.succ_inj in H1.
}
Qed.

Theorem NoDup_app_remove_l : ∀ A (l l' : list A), NoDup (l ++ l') → NoDup l'.
Proof.
intros * Hnd.
apply NoDup_app_comm in Hnd.
revert l Hnd.
induction l' as [| b]; intros; [ constructor | ].
cbn in Hnd.
apply NoDup_cons_iff in Hnd.
destruct Hnd as (H1, H2).
constructor; [ | now apply IHl' in H2 ].
intros H; apply H1.
now apply in_or_app; left.
Qed.

Theorem NoDup_app_remove_r : ∀ A (l l' : list A), NoDup (l ++ l') → NoDup l.
Proof.
intros * Hnd.
apply NoDup_app_comm in Hnd.
now apply NoDup_app_remove_l in Hnd.
Qed.

Theorem NoDup_app_iff : ∀ A (l l' : list A),
  NoDup (l ++ l') ↔
    NoDup l ∧ NoDup l' ∧ (∀ a, a ∈ l → a ∉ l').
Proof.
intros.
split. {
  intros Hnd.
  split; [ now apply NoDup_app_remove_r in Hnd | ].
  split; [ now apply NoDup_app_remove_l in Hnd | ].
  intros a Ha Ha'.
  revert l' Hnd Ha'.
  induction l as [| b]; intros; [ easy | ].
  destruct Ha as [Ha| Ha]. {
    subst b.
    apply NoDup_app_comm in Hnd.
    apply NoDup_remove_2 in Hnd.
    apply Hnd.
    now apply in_app_iff; left.
  }
  apply (IHl Ha l'); [ | easy ].
  cbn in Hnd.
  now apply NoDup_cons_iff in Hnd.
} {
  intros * (Hnl & Hnl' & Hll).
  revert l' Hnl' Hll.
  induction l as [| b l]; intros; [ easy | cbn ].
  constructor. {
    intros Hb.
    apply in_app_or in Hb.
    destruct Hb as [Hb| Hb]. {
      now apply NoDup_cons_iff in Hnl.
    } {
      now specialize (Hll b (or_introl eq_refl)) as H1.
    }
  } {
    apply NoDup_cons_iff in Hnl.
    apply IHl; [ easy | easy | ].
    intros a Ha.
    now apply Hll; right.
  }
}
Qed.

Theorem NoDup_prod {A} {B} : ∀ (l : list A) (l' : list B),
  NoDup l → NoDup l' → NoDup (list_prod l l').
Proof.
intros * Hnl Hnl'.
revert l' Hnl'.
induction l as [| a l]; intros; [ constructor | ].
cbn.
apply NoDup_app_iff.
split. {
  induction l' as [| b l']; [ constructor | ].
  apply NoDup_cons. {
    intros Hab.
    apply NoDup_cons_iff in Hnl'; apply Hnl'.
    clear - Hab.
    induction l' as [| c l']; [ easy | ].
    cbn in Hab.
    destruct Hab as [Hab| Hab]. {
      injection Hab; clear Hab; intros; subst c.
      now left.
    } {
      now right; apply IHl'.
    }
  }
  apply IHl'.
  now apply NoDup_cons_iff in Hnl'.
}
split. {
  apply IHl; [ | easy ].
  now apply NoDup_cons_iff in Hnl.
} {
  intros (a', b) Hab.
  assert (H : a = a'). {
    clear - Hab.
    induction l' as [| b' l']; [ easy | ].
    cbn in Hab.
    destruct Hab as [Hab| Hab]; [ congruence | ].
    now apply IHl'.
  }
  subst a'.
  intros H.
  apply in_prod_iff in H.
  now apply NoDup_cons_iff in Hnl.
}
Qed.

Theorem Permutation_fold_mul : ∀ l1 l2 a,
  Permutation l1 l2 → fold_left Nat.mul l1 a = fold_left Nat.mul l2 a.
Proof.
intros * Hperm.
induction Hperm using Permutation_ind; [ easy | | | ]. {
  cbn; do 2 rewrite <- List_fold_left_mul_assoc.
  now rewrite IHHperm.
} {
  now cbn; rewrite Nat.mul_shuffle0.
}
etransitivity; [ apply IHHperm1 | apply IHHperm2 ].
Qed.

Theorem iter_list_permut : ∀ T A (d : T) (op : T → T → T) (l1 l2 : list A) f
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_comm : ∀ a b, op a b = op b a)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  Permutation l1 l2
  → iter_list l1 (λ (c : T) i, op c (f i)) d =
    iter_list l2 (λ (c : T) i, op c (f i)) d.
Proof.
intros * op_d_l op_d_r op_comm op_assoc Hl.
specialize (Permutation_length Hl) as H1.
remember (length l2) as n eqn:H2.
move H1 after H2; symmetry in H2.
destruct n. {
  apply length_zero_iff_nil in H1.
  apply length_zero_iff_nil in H2.
  now subst l1 l2.
}
revert n H1 H2.
induction Hl; intros; [ easy | | | ]. {
  cbn in H1, H2.
  apply Nat.succ_inj in H1.
  apply Nat.succ_inj in H2.
  rewrite iter_list_cons; [ | easy | easy | easy ].
  rewrite iter_list_cons; [ | easy | easy | easy ].
  f_equal.
  destruct n. {
    apply length_zero_iff_nil in H1.
    apply length_zero_iff_nil in H2.
    now subst l l'.
  }
  now apply IHHl with (n := n).
} {
  destruct n; [ easy | ].
  cbn in H1, H2.
  do 2 apply Nat.succ_inj in H1.
  do 2 apply Nat.succ_inj in H2.
  do 4 (rewrite iter_list_cons; [ | easy | easy | easy ]).
  do 2 rewrite op_assoc.
  f_equal; apply op_comm.
} {
  specialize (Permutation_length Hl2) as H3.
  rewrite H2 in H3.
  rewrite (IHHl1 n); [ | easy | easy ].
  rewrite (IHHl2 n); [ | easy | easy ].
  easy.
}
Qed.

Theorem not_forall_in_interv_imp_exist : ∀ a b (P : nat → Prop),
  (∀ n, decidable (P n))
  → a ≤ b
  → (¬ (∀ n, a ≤ n ≤ b → ¬ P n))
  → ∃ n, P n.
Proof.
intros * Hdec Hab Hnab.
revert a Hab Hnab.
induction b; intros. {
  apply Nat.le_0_r in Hab; subst a.
  exists 0.
  destruct (Hdec 0) as [H1| H1]; [ easy | ].
  exfalso; apply Hnab.
  intros * Hn.
  now replace n with 0 by flia Hn.
}
destruct (Nat.eq_dec a (S b)) as [Hasb| Hasb]. {
  exists (S b).
  destruct (Hdec (S b)) as [H1| H1]; [ easy | ].
  exfalso; apply Hnab.
  intros * Hn.
  now replace n with (S b) by flia Hasb Hn.
}
assert (H : a ≤ b) by flia Hab Hasb.
move H before Hab; clear Hab Hasb; rename H into Hab.
destruct (Hdec (S b)) as [H1| H1]; [ now exists (S b) | ].
apply (IHb a); [ easy | ].
intros H; apply Hnab.
intros n Hn.
destruct (Nat.eq_dec n (S b)) as [H2| H2]; [ now rewrite H2 | ].
apply H; flia Hn H2.
Qed.

Fixpoint merge {A} (le : A → A → bool) l1 l2 :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | a1::l1', a2::l2' =>
      if le a1 a2 then a1 :: merge le l1' l2 else a2 :: merge_aux l2'
  end
  in merge_aux l2.

Fixpoint merge_list_to_stack {A} (le : A → A → bool) stack l :=
  match stack with
  | [] => [Some l]
  | None :: stack' => Some l :: stack'
  | Some l' :: stack' => None :: merge_list_to_stack le stack' (merge le l' l)
  end.

Fixpoint merge_stack {A} (le : A → A → bool) stack :=
  match stack with
  | [] => []
  | None :: stack' => merge_stack le stack'
  | Some l :: stack' => merge le l (merge_stack le stack')
  end.

Fixpoint iter_merge {A} (le : A → A → bool) stack l :=
  match l with
  | [] => merge_stack le stack
  | a::l' => iter_merge le (merge_list_to_stack le stack [a]) l'
  end.

Definition bsort {A} (le : A → A → bool) := iter_merge le [].

(* *)

Theorem if_eqb_eq_dec : ∀ A i j (a b : A),
  (if i =? j then a else b) = (if Nat.eq_dec i j then a else b).
Proof.
intros.
remember (i =? j) as ij eqn:Hij.
symmetry in Hij.
destruct ij. {
  apply Nat.eqb_eq in Hij.
  now destruct (Nat.eq_dec i j).
} {
  apply Nat.eqb_neq in Hij.
  now destruct (Nat.eq_dec i j).
}
Qed.

Theorem if_ltb_lt_dec : ∀ A i j (a b : A),
  (if i <? j then a else b) = (if lt_dec i j then a else b).
Proof.
intros.
remember (i <? j) as ij eqn:Hij.
symmetry in Hij.
destruct ij. {
  apply Nat.ltb_lt in Hij.
  now destruct (lt_dec i j).
} {
  apply Nat.ltb_nlt in Hij.
  now destruct (lt_dec i j).
}
Qed.

Theorem if_leb_le_dec : ∀ A i j (a b : A),
  (if i <=? j then a else b) = (if le_dec i j then a else b).
Proof.
intros.
remember (i <=? j) as ij eqn:Hij.
symmetry in Hij.
destruct ij. {
  apply Nat.leb_le in Hij.
  now destruct (le_dec i j).
} {
  apply Nat.leb_nle in Hij.
  now destruct (le_dec i j).
}
Qed.

Theorem Nat_ltb_mono_l : ∀ a b c, (a + b <? a + c) = (b <? c).
Proof.
intros.
remember (_ <? _) as x eqn:Hx in |-*; symmetry in Hx.
remember (_ <? _) as y eqn:Hy in |-*; symmetry in Hy.
destruct x, y; [ easy | | | easy ]. {
  apply Nat.ltb_lt in Hx.
  apply Nat.ltb_nlt in Hy.
  flia Hx Hy.
} {
  apply Nat.ltb_nlt in Hx.
  apply Nat.ltb_lt in Hy.
  flia Hx Hy.
}
Qed.

Theorem Nat_ltb_mono_r : ∀ a b c, (a + c <? b + c) = (a <? b).
Proof.
intros.
rewrite (Nat.add_comm a).
rewrite (Nat.add_comm b).
apply Nat_ltb_mono_l.
Qed.

Theorem Nat_b2n_upper_bound : ∀ b, Nat.b2n b ≤ 1.
Proof.
intros; destruct b; cbn; flia.
Qed.

Definition bool_of_sumbool {A B : Prop} (P : sumbool A B) :=
  match P with
  | left _ _ => true
  | right _ _ => false
  end.

Definition sumbool_or {A B C D : Prop} (P : sumbool A B) (Q : sumbool C D) :=
  orb (bool_of_sumbool P) (bool_of_sumbool Q).

Definition sumbool_and {A B C D : Prop} (P : sumbool A B) (Q : sumbool C D) :=
  andb (bool_of_sumbool P) (bool_of_sumbool Q).

Notation "a ∨∨ b" := (sumbool_or a b) (at level 85).
Notation "a ∧∧ b" := (sumbool_and a b) (at level 80).

Arguments iter_list {A B}%type l%list f%function : simpl never.
