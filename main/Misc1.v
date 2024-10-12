(* Misc1.v *)
(* Theorems of general usage, which could be (or not) in Coq library *)
(* First file used in ../trigo_without_pi *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith Psatz.
Import List.ListNotations Init.Nat.
Open Scope list.

Global Hint Resolve Nat.le_0_l : core.
Global Hint Resolve Nat.lt_0_succ : core.
Global Hint Resolve Nat.lt_succ_diag_r : core.

(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Notation "n !" := (fact n) (at level 1, format "n !").

Notation "x '∈' l" := (List.In x l) (at level 70).
Notation "x '∉' l" := (¬ List.In x l) (at level 70).
Notation "E ⊂ F" := (List.incl E F) (at level 70).

Notation "l .( i )" := (List.nth (i - 1) l 0) (at level 1, format "l .( i )").

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

Notation "x ≠? y" := (negb (Nat.eqb x y)) (at level 70) : nat_scope.

Theorem List_fold_left_map :
  ∀ A B C (f : A → B → A) (g : C → B) (l : list C) a,
  List.fold_left f (List.map g l) a = List.fold_left (λ c b, f c (g b)) l a.
Proof.
intros.
revert a.
induction l as [| c]; intros; [ easy | apply IHl ].
Qed.

(* iterations in a list
   in order to later define syntaxes : Max, Σ, Π, ...
   e.g. "Σ (i ∈ l), f i", "Π (i ∈ l), f i", ... *)

Definition iter_list {A B} (l : list B) f (d : A) := List.fold_left f l d.

(* iterations in indexed sequences
   in order to later define syntaxes : Max, Σ, Π, ...
   e.g. "Σ (i = b, e), f i", "Π (i = b, e), f i" *)

Definition iter_seq {T} b e f (d : T) := iter_list (List.seq b (S e - b)) f d.

Arguments iter_seq : simpl never.
Arguments iter_list : simpl never.

(*
(* maximum of several values *)

(* commented because Max could apply only on nat because it needs
   a minimum, which is 0 in nat, but not in all ring-like types *)

Notation "'Max' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, max c (g)) 0)
  (at level 45, i at level 0, b at level 60, e at level 60) : nat_scope.

Notation "'Max' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, max c (g)) 0)
  (at level 45, i at level 0, l at level 60) : nat_scope.
*)

Theorem fold_iter_list : ∀ {A B} (f : A → B → A) l d,
  List.fold_left f l d = iter_list l f d.
Proof. easy. Qed.

Theorem fold_iter_seq : ∀ A b e f (d : A),
  iter_list (List.seq b (S e - b)) f d = iter_seq b e f d.
Proof. easy. Qed.

Theorem iter_shift : ∀ {T} s b k f (d : T),
  s ≤ b ≤ k
  → iter_seq b k f d =
    iter_seq (b - s) (k - s) (λ c i, f c (s + i)) d.
Proof.
intros * (Hsb, Hbk).
progress unfold iter_seq, iter_list.
replace (S (k - s) - (b - s)) with (S (k - b)) by flia Hsb Hbk.
rewrite <- Nat.sub_succ_l; [ | easy ].
remember (S k - b)%nat as len; clear Heqlen.
clear k Hbk.
revert b d Hsb.
induction len; intros; [ easy | ].
rewrite List.seq_S; symmetry.
rewrite List.seq_S; symmetry.
do 2 rewrite List.fold_left_app; cbn.
rewrite IHlen; [ | easy ].
now replace (s + (b - s + len)) with (b + len) by flia Hsb.
Qed.

(* conversions if ...? into if ..._dec *)

Theorem if_bool_if_dec : ∀ A (b : bool) (x y : A),
  (if b then x else y) =
  if Sumbool.sumbool_of_bool b then x else y.
Proof.
intros.
now destruct (Sumbool.sumbool_of_bool b); subst b.
Qed.

(* *)

Theorem Nat_mul_2_l : ∀ n, 2 * n = n + n.
Proof.
intros; cbn.
now rewrite Nat.add_0_r.
Qed.

Theorem Nat_sub_succ_1 : ∀ n, S n - 1 = n.
Proof. now intros; rewrite Nat.sub_succ, Nat.sub_0_r. Qed.

Theorem Nat_lt_lt_add_mul : ∀ a b c n, a < b → c < n → c + n * a < n * b.
Proof.
intros * Hab Hcn.
revert a b c Hab Hcn.
induction n; intros; [ easy | cbn ].
destruct c. {
  cbn.
  apply Nat.add_lt_le_mono; [ easy | ].
  now apply Nat.mul_le_mono_l, Nat.lt_le_incl.
}
apply Nat.succ_lt_mono in Hcn.
specialize (IHn a b c Hab Hcn).
rewrite Nat.add_assoc, Nat.add_shuffle0, Nat.add_comm.
apply Nat.add_lt_le_mono; [ easy | ].
apply IHn.
Qed.

Notation "a ≡ b 'mod' c" := (a mod c = b mod c) (at level 70, b at level 36).
Notation "a ≢ b 'mod' c" := (a mod c ≠ b mod c) (at level 70, b at level 36).

Theorem List_nth_succ_cons : ∀ {A} (a : A) la i,
  List.nth (S i) (a :: la) = List.nth i la.
Proof. easy. Qed.

(* List_map2: map with two lists *)

Fixpoint List_map2 {A B C} (f : A → B → C) la lb :=
  match la with
  | [] => []
  | a :: la' =>
      match lb with
      | [] => []
      | b :: lb' => f a b :: List_map2 f la' lb'
      end
  end.

(* end List_map2 *)

Theorem min_add_sub_max : ∀ a b, min (a + (b - a)) (b + (a - b)) = max a b.
Proof.
intros.
destruct (le_dec a b) as [Hab| Hab]. {
  rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
  rewrite (proj2 (Nat.sub_0_le _ _) Hab).
  rewrite Nat.add_0_r, Nat.min_id; symmetry.
  now apply Nat.max_r.
} {
  apply Nat.nle_gt, Nat.lt_le_incl in Hab.
  rewrite Nat.min_comm, Nat.max_comm.
  rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
  rewrite (proj2 (Nat.sub_0_le _ _) Hab).
  rewrite Nat.add_0_r, Nat.min_id; symmetry.
  now apply Nat.max_r.
}
Qed.

(* rank: rank of the first element satisfying a predicate *)
(* like "find" but returning the rank, not the element itself *)

Fixpoint List_rank_loop i [A] (f : A → bool) (l : list A) : nat :=
  match l with
  | [] => i
  | x :: tl => if f x then i else List_rank_loop (S i) f tl
end.

Definition List_rank [A] := @List_rank_loop 0 A.

(* end List_rank *)

Theorem Nat_mod_fact_upper_bound : ∀ k n, k mod n! < n!.
Proof.
intros.
apply Nat.mod_upper_bound, fact_neq_0.
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

(* butn: list without its nth element *)

Definition List_butn {A} n (l : list A) :=
  List.firstn n l ++ List.skipn (S n) l.

(* end butn *)

(* insert in a list (List.reverse of List_butn) *)

Definition insert_at A k (la : list A) e :=
  List.firstn k la ++ e :: List.skipn k la.

(* end insert_at *)

(* replace in a list *)

Definition replace_at {A} k (la : list A) e :=
  List.firstn k la ++ e :: List.skipn (S k) la.

Theorem replace_at_succ_cons : ∀ A i a b (l : list A),
  replace_at (S i) (a :: l) b = a :: replace_at i l b.
Proof. easy. Qed.

(* end replace_at *)

(* List_repeat_apply: applying a function n times *)

Fixpoint List_repeat_apply {A} n (f : A → A) a :=
  match n with
  | 0 => a
  | S n' => List_repeat_apply n' f (f a)
  end.

(* end List.repeat_apply *)

(* equivalence & equality *)

Definition equivalence {A} (eqv : A → A → bool) :=
  (∀ a, eqv a a = true) ∧
  (∀ a b, eqv a b = true → eqv b a = true) ∧
  (∀ a b c, eqv a b = true → eqv b c = true → eqv a c = true).

Definition equality {A} (eqb : A → A → bool) := ∀ a b, eqb a b = true ↔ a = b.

Theorem equality_refl {A} {eqb : A → _} : equality eqb → ∀ a, eqb a a = true.
Proof.
intros * Heqb *.
now apply Heqb.
Qed.

(* *)

Theorem option_eq_dec : ∀ A : Type,
  (∀ x y : A, {x = y} + {x ≠ y})
  → (∀ x y : option A, {x = y} + {x ≠ y}).
Proof.
intros * Hed *.
destruct x as [x| ]. {
  destruct y as [y| ]; [ | now right ].
  destruct (Hed x y) as [H1| H1]; [ now left; subst y | right ].
  intros H; apply H1.
  now injection H.
}
destruct y as [y| ]; [ now right | now left ].
Qed.

(* *)

Fixpoint list_compare {A} (compare : A → A → comparison) la lb :=
  match la with
  | [] =>
      match lb with
      | [] => Eq
      | b :: lb' => Lt
      end
  | a :: la' =>
      match lb with
      | [] => Gt
      | b :: lb' =>
          match compare a b with
          | Eq => list_compare compare la' lb'
          | Lt => Lt
          | Gt => Gt
          end
      end
  end.

(* list_eqv *)

Fixpoint list_eqv {A} (eqv : A → A → bool) la lb :=
  match la with
  | [] =>
      match lb with
      | [] => true
      | b :: lb' => false
      end
  | a :: la' =>
      match lb with
      | [] => false
      | b :: lb' => if eqv a b then list_eqv eqv la' lb' else false
      end
  end.

Theorem list_eqb_eq : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lb, list_eqv eqb la lb = true ↔ la = lb.
Proof.
intros * Heqb *.
split; intros Hlab. {
  revert lb Hlab.
  induction la as [| a]; intros; [ now destruct lb | cbn ].
  destruct lb as [| b]; [ easy | cbn in Hlab ].
  remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
  destruct ab; [ | easy ].
  apply Heqb in Hab; subst b; f_equal.
  now apply IHla.
} {
  subst lb.
  induction la as [| a]; [ easy | cbn ].
  now rewrite (equality_refl Heqb).
}
Qed.

Theorem list_eqb_neq : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lb, list_eqv eqb la lb = false → la ≠ lb.
Proof.
intros * Heqb * Hab H; subst lb.
induction la as [| a]; [ easy | cbn in Hab ].
rewrite (equality_refl Heqb) in Hab.
congruence.
Qed.

(* end list_eqv *)

(* list_leb *)

Fixpoint list_leb {A} (leb : A → A → bool) la lb :=
  match la with
  | [] => true
  | a :: la' =>
      match lb with
      | [] => false
      | b :: lb' =>
          if leb a b then
            if leb b a then list_leb leb la' lb' else true
          else false
      end
  end.

(* end list_leb *)

(* list_ltb *)

Fixpoint list_ltb {A} (ltb : A → A → bool) la lb :=
  match lb with
  | [] => false
  | b :: lb' =>
      match la with
      | [] => true
      | a :: la' =>
          if ltb a b then true
          else if ltb b a then false
          else list_ltb ltb la' lb'
      end
  end.

(* end list_ltb *)

(* pair_eqb *)

Definition pair_eqb {A B} (eqba : A → A → bool) (eqbb : B → B → bool) ab cd :=
  (eqba (fst ab) (fst cd) && eqbb (snd ab) (snd cd))%bool.

Theorem pair_eqb_eq : ∀ A B (eqba : A → _) (eqbb : B → _),
  equality eqba →
  equality eqbb →
  ∀ a b, pair_eqb eqba eqbb a b = true ↔ a = b.
Proof.
intros * Heqba Heqbb *.
split; intros Hab. {
  progress unfold pair_eqb in Hab.
  destruct a as (a1, a2).
  destruct b as (b1, b2).
  cbn in Hab.
  apply Bool.andb_true_iff in Hab.
  destruct Hab as (Ha, Hb).
  apply Heqba in Ha.
  apply Heqbb in Hb.
  congruence.
} {
  subst b.
  progress unfold pair_eqb.
  destruct a as (a1, a2); cbn.
  apply Bool.andb_true_iff.
  split. {
    apply (equality_refl Heqba).
  } {
    apply (equality_refl Heqbb).
  }
}
Qed.

(* end pair_eqb *)

Definition unsome {A} (d : A) o :=
  match o with
  | Some x => x
  | None => d
  end.

(* extract: like "find" but returning all details:
   - what is before
   - the value found
   - what is after *)

Fixpoint extract {A} (f : A → bool) l :=
  match l with
  | [] => None
  | a :: la =>
      if f a then Some ([], a, la)
      else
        match extract f la with
        | None => None
        | Some (bef, b, aft) => Some (a :: bef, b, aft)
        end
  end.

(* member: a computable "In" *)

Fixpoint member {A} (eqb : A → A → bool) a la :=
  match la with
  | [] => false
  | b :: lb => if eqb a b then true else member eqb a lb
  end.

Theorem member_true_iff : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ a la, member eqb a la = true ↔ ∃ l1 l2, la = l1 ++ a :: l2.
Proof.
intros * Heqb *.
split. {
  intros Hma.
  induction la as [| b]; [ easy | cbn in Hma ].
  remember (member eqb a la) as mal eqn:Hmal; symmetry in Hmal.
  destruct mal. {
    specialize (IHla eq_refl).
    destruct IHla as (l1 & l2 & Hla).
    subst la.
    now exists (b :: l1), l2.
  }
  remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
  destruct ab; [ | easy ].
  apply Heqb in Hab; subst b.
  now exists [], la.
} {
  intros (l1 & l2 & Hla).
  subst la.
  induction l1 as [| b]; cbn. {
    now rewrite (equality_refl Heqb).
  }
  now destruct (eqb a b).
}
Qed.

Theorem member_false_iff : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ a la, member eqb a la = false ↔ ∀ b, b ∈ la → a ≠ b.
Proof.
intros * Heqb *.
split. {
  intros Hma * Hb Hab; subst b.
  induction la as [| b]; [ easy | ].
  cbn in Hma.
  destruct Hb as [Hb| Hb]. {
    subst b.
    now rewrite (equality_refl Heqb) in Hma.
  }
  apply IHla; [ | easy ].
  now destruct (eqb a b).
} {
  intros Hla.
  induction la as [| b]; [ easy | cbn ].
  remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
  destruct ab. {
    apply Heqb in Hab; subst b.
    now specialize (Hla _ (or_introl eq_refl)).
  }
  apply IHla.
  intros c Hc.
  now apply Hla; right.
}
Qed.

(* end member *)

(* no_dup: a computable "NoDup" *)

Fixpoint no_dup {A} (eqb : A → A → bool) la :=
  match la with
  | [] => true
  | a :: la' => if member eqb a la' then false else no_dup eqb la'
  end.

Theorem no_dup_NoDup : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la, no_dup eqb la = true ↔ List.NoDup la.
Proof.
intros * Heqb *.
split; intros Hla. {
  induction la as [| a]; [ constructor | ].
  apply List.NoDup_cons_iff.
  cbn in Hla.
  rewrite if_bool_if_dec in Hla.
  destruct (Sumbool.sumbool_of_bool _) as [Hal| Hal]; [ easy | ].
  split; [ | now apply IHla ].
  intros H.
  now specialize (proj1 (member_false_iff Heqb _ _) Hal a H).
} {
  induction la as [| a]; [ easy | cbn ].
  rewrite if_bool_if_dec.
  apply List.NoDup_cons_iff in Hla.
  destruct (Sumbool.sumbool_of_bool _) as [Hal| Hal]; [ | now apply IHla ].
  apply (member_true_iff Heqb) in Hal.
  destruct Hla as (Hala & Hnd).
  destruct Hal as (l1 & l2 & H); subst la.
  exfalso; apply Hala.
  now apply List.in_or_app; right; left.
}
Qed.

Theorem no_dup_false_iff : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la, no_dup eqb la = false ↔
  ∃ l1 l2 l3 a, la = l1 ++ a :: l2 ++ a :: l3.
Proof.
intros * Heqb *.
split. {
  intros Had.
  induction la as [| a]; [ easy | cbn in Had ].
  remember (member eqb a la) as mal eqn:Hmal; symmetry in Hmal.
  destruct mal. 2: {
    specialize (IHla Had).
    destruct IHla as (l1 & l2 & l3 & b & Hlb).
    exists (a :: l1), l2, l3, b.
    now subst la.
  }
  clear Had.
  apply member_true_iff in Hmal; [ | easy ].
  destruct Hmal as (l1 & l2 & Hla); subst la.
  now exists [], l1, l2, a.
} {
  intros (l1 & l2 & l3 & a & Hla); subst la.
  induction l1 as [| b]; cbn. {
    remember (member eqb a (l2 ++ a :: l3)) as mal eqn:Hmal; symmetry in Hmal.
    destruct mal; [ easy | ].
    specialize (proj1 (member_false_iff Heqb _ _) Hmal a) as H1.
    assert (H : a ∈ l2 ++ a :: l3) by now apply List.in_or_app; right; left.
    now specialize (H1 H).
  }
  remember (member eqb b _) as mbl eqn:Hmbl; symmetry in Hmbl.
  now destruct mbl.
}
Qed.

(* end no_dup *)

Theorem NoDup_app_comm {A} : ∀ l l' : list A,
  List.NoDup (l ++ l') → List.NoDup (l' ++ l).
Proof.
intros * Hll.
revert l Hll.
induction l' as [| a l']; intros; [ now rewrite List.app_nil_r in Hll | ].
cbn; constructor. {
  intros Ha.
  apply List.NoDup_remove_2 in Hll; apply Hll.
  apply List.in_app_or in Ha.
  apply List.in_or_app.
  now destruct Ha; [ right | left ].
}
apply IHl'.
now apply List.NoDup_remove_1 in Hll.
Qed.

Theorem List_fold_left_ext_in : ∀ A B (f g : A → B → A) l a,
  (∀ b c, b ∈ l → f c b = g c b)
  → List.fold_left f l a = List.fold_left g l a.
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

(* common for all iterators *)

Theorem fold_left_op_fun_from_d : ∀ {T A} d op a l (f : A → _)
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  List.fold_left (λ (c : T) i, op c (f i)) l a =
  op a (List.fold_left (λ (c : T) i, op c (f i)) l d).
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
progress unfold iter_list.
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
apply List.in_seq in Hi.
apply Hz; flia Hi.
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
progress unfold iter_seq, iter_list.
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

Theorem iter_seq_split_last : ∀ T d (op : T → T → T) b k g,
  b ≤ k
  → iter_seq b k (λ (c : T) (i : nat), op c (g i)) d =
    op (iter_seq (S b) k (λ (c : T) (i : nat), op c (g (i - 1)%nat)) d) (g k).
Proof.
intros * Hbk.
progress unfold iter_seq, iter_list.
remember (S k - S b) as len eqn:Hlen.
rewrite Nat.sub_succ in Hlen.
replace (S k - b) with (S len) by flia Hbk Hlen.
replace k with (b + len) by flia Hbk Hlen.
rewrite <- List.seq_shift.
rewrite List_fold_left_map.
rewrite List.seq_S.
rewrite List.fold_left_app.
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
progress unfold iter_seq, iter_list.
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
rewrite List.seq_app, List.fold_left_app.
rewrite (fold_left_op_fun_from_d d); [ | easy | easy | easy ].
now rewrite Nat.add_succ_comm.
Qed.

Theorem iter_seq_split3 : ∀ T d op j g b k
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  b ≤ j ≤ k
  → iter_seq b k (λ (c : T) (i : nat), op c (g i)) d =
    op (op (iter_seq (S b) j (λ (c : T) (i : nat), op c (g (i - 1))) d) (g j))
      (iter_seq (j + 1) k (λ (c : T) (i : nat), op c (g i)) d).
Proof.
intros * op_d_l op_d_r op_assoc Hj.
rewrite iter_seq_split with (j := j); [ | easy | easy | easy | flia Hj ].
now rewrite iter_seq_split_last.
Qed.

Theorem iter_list_app : ∀ A B (d : A) (f : A → B → A) la lb,
  iter_list (la ++ lb) f d = iter_list lb f (iter_list la f d).
Proof.
intros.
progress unfold iter_list.
now rewrite List.fold_left_app.
Qed.

Theorem iter_list_cons : ∀ A B d op (a : B) la f
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  iter_list (a :: la) (λ (c : A) i, op c (f i)) d =
  op (f a) (iter_list la (λ (c : A) i, op c (f i)) d).
Proof.
intros.
progress unfold iter_list; cbn.
rewrite op_d_l.
now apply (fold_left_op_fun_from_d d).
Qed.

Theorem iter_list_eq_compat : ∀ A B d (op : A → A → A) (l : list B) g h,
  (∀ i, i ∈ l → g i = h i)
  → iter_list l (λ c i, op c (g i)) d =
    iter_list l (λ c i, op c (h i)) d.
Proof.
intros * Hgh.
progress unfold iter_list.
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
apply List.in_seq in Hi.
flia Hi.
Qed.

Theorem iter_seq_succ_succ : ∀ {T} (d : T) b k f,
  iter_seq (S b) (S k) f d =
  iter_seq b k (λ c i, f c (S i)) d.
Proof.
intros.
progress unfold iter_seq, iter_list.
rewrite Nat.sub_succ.
remember (S k - b)%nat as len; clear Heqlen.
rewrite <- List.seq_shift.
now rewrite List_fold_left_map.
Qed.

Theorem iter_seq_succ_succ' : ∀ {T} (d : T) b k f,
  iter_seq (S b) (S k) (λ c i, f c (i - 1)) d =
  iter_seq b k (λ c i, f c i) d.
Proof.
intros.
progress unfold iter_seq, iter_list.
rewrite Nat.sub_succ.
rewrite <- List.seq_shift.
rewrite List_fold_left_map.
apply List_fold_left_ext_in.
intros j i Hj.
f_equal.
rewrite Nat.sub_succ.
apply Nat.sub_0_r.
Qed.

Theorem iter_list_empty : ∀ T A d (op : T → T → T) (l : list A) g,
  l = []
  → iter_list l (λ c i, op c (g i)) d = d.
Proof.
now intros * Hl; subst l.
Qed.

Theorem iter_seq_empty : ∀ T d (op : T → T → T) b k g,
  k < b
  → iter_seq b k (λ (c : T) (i : nat), op c (g i)) d = d.
Proof.
intros * Hkb.
progress unfold iter_seq.
now replace (S k - b) with 0 by flia Hkb.
Qed.

Theorem iter_list_only_one : ∀ T A d (op : T → T → T) (g : A → T) a
  (op_d_l : ∀ x, op d x = x),
  iter_list [a] (λ c i, op c (g i)) d = g a.
Proof.
intros * op_d_l.
progress unfold iter_list; cbn.
apply op_d_l.
Qed.

Theorem iter_seq_only_one : ∀ T d (op : T → T → T) g n
  (op_d_l : ∀ x, op d x = x),
  iter_seq n n (λ c i, op c (g i)) d = g n.
Proof.
intros * op_d_l.
progress unfold iter_seq.
rewrite Nat.sub_succ_l; [ | easy ].
rewrite Nat.sub_diag.
now apply iter_list_only_one.
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
progress unfold iter_list.
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

Theorem iter_list_inv : ∀ T A d op inv (f : A → T) l
  (inv_op_distr : ∀ a b, inv (op a b) = op (inv a) (inv b)),
  inv (iter_list l (λ (c : T) i, op c (f i)) d) =
  iter_list l (λ (c : T) i, op c (inv (f i))) (inv d).
Proof.
intros.
progress unfold iter_list.
revert d.
induction l as [| a la]; intros; [ easy | cbn ].
rewrite IHla.
now rewrite inv_op_distr.
Qed.

Theorem iter_seq_inv : ∀ T d op inv b e f
  (inv_op_distr : ∀ a b, inv (op a b) = op (inv a) (inv b)),
  inv (iter_seq b e (λ (c : T) (i : nat), op c (f i)) d) =
  iter_seq b e (λ (c : T) (i : nat), op c (inv (f i))) (inv d).
Proof.
intros.
now apply iter_list_inv.
Qed.

Theorem iter_seq_rtl : ∀ T d op b k f
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_comm : ∀ a b, op a b = op b a)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  iter_seq b k (λ (c : T) (i : nat), op c (f i)) d =
  iter_seq b k (λ (c : T) (i : nat), op c (f (k + b - i))) d.
Proof.
intros.
destruct (le_dec (S k) b) as [Hkb| Hkb]. {
  progress unfold iter_seq.
  now replace (S k - b) with 0 by flia Hkb.
}
apply Nat.nle_gt in Hkb.
apply -> Nat.lt_succ_r in Hkb.
progress unfold iter_seq, iter_list.
remember (S k - b) as len eqn:Hlen.
replace k with (b + len - 1) by flia Hkb Hlen.
clear Hlen Hkb.
revert b.
induction len; intros; [ easy | ].
rewrite List.seq_S at 1; cbn.
rewrite List.fold_left_app; cbn.
symmetry.
rewrite fold_left_op_fun_from_d with (d := d); [ | easy | easy | easy ].
rewrite op_comm.
f_equal; [ | rewrite op_d_l; f_equal; flia ].
rewrite IHlen.
rewrite <- List.seq_shift.
rewrite List_fold_left_map.
apply List_fold_left_ext_in.
intros j c Hj.
apply List.in_seq in Hj.
f_equal; f_equal; flia.
Qed.

(* App : a notation for iterating concatenation of a list of lists *)

Notation "'App' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, c ++ g) [])
  (at level 45, i at level 0, b at level 60, e at level 60).

Notation "'App' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, c ++ g) [])
  (at level 45, i at level 0, l at level 60).

Theorem App_list_cons : ∀ A B (a : A) la (f : A → list B),
  App (i ∈ a :: la), f i = f a ++ App (i ∈ la), f i.
Proof.
intros.
apply iter_list_cons; [ easy | apply List.app_nil_r | ].
apply List.app_assoc.
Qed.

Theorem App_list_concat_map : ∀ A B (l : list A) (f : A → list B),
  App (a ∈ l), f a = List.concat (List.map f l).
Proof.
intros.
induction l as [| a]; [ easy | cbn ].
rewrite App_list_cons.
now rewrite IHl.
Qed.

(* cart_prod: cartesian product of several lists *)

Fixpoint cart_prod {A} (ll : list (list A)) :=
  match ll with
  | [] => [[]]
  | l :: ll' => List.flat_map (λ a, List.map (cons a) (cart_prod ll')) l
  end.

Theorem in_cart_prod_length : ∀ A (ll : list (list A)) l,
  l ∈ cart_prod ll → length l = length ll.
Proof.
intros * Hl.
revert l Hl.
induction ll as [| l1]; intros. {
  cbn in Hl.
  destruct Hl as [Hl| Hl]; [ now subst l | easy ].
}
cbn in Hl.
apply List.in_flat_map in Hl.
destruct Hl as (a & Hl1 & Ha).
apply List.in_map_iff in Ha.
destruct Ha as (l3 & Hl & Hl3).
subst l; cbn; f_equal.
now apply IHll.
Qed.

Theorem nth_in_cart_prod : ∀ A (d : A) ll l i,
  i < length ll
  → l ∈ cart_prod ll
  → List.nth i l d ∈ List.nth i ll [].
Proof.
intros * Hi Hll.
revert l i Hi Hll.
induction ll as [| l1]; intros; [ easy | ].
cbn in Hll |-*.
destruct i. {
  destruct ll as [| l2]. {
    apply List.in_flat_map in Hll.
    destruct Hll as (a & Ha & Hla).
    apply List.in_map_iff in Hla.
    now destruct Hla as (l2 & H & Hl2); subst l.
  }
  apply List.in_flat_map in Hll.
  destruct Hll as (a & Hl1 & Hl).
  apply List.in_map_iff in Hl.
  now destruct Hl as (l3 & H & Hl3); subst l.
}
cbn in Hi; apply Nat.succ_lt_mono in Hi.
destruct ll as [| l2]; [ easy | ].
apply List.in_flat_map in Hll.
destruct Hll as (a & Ha & Hl).
apply List.in_map_iff in Hl.
destruct Hl as (l3 & H & Hl3); subst l.
rewrite List_nth_succ_cons.
now apply IHll.
Qed.

(* end cart_prod *)

(* binomial *)
(* code borrowed from my work "coq_euler_prod_form" *)

Fixpoint binomial n k :=
  match k with
  | 0 => 1
  | S k' =>
      match n with
      | 0 => 0
      | S n' => binomial n' k' + binomial n' k
     end
  end.

(* end binomial *)

Theorem NoDup_app_remove_l :
  ∀ A (l l' : list A), List.NoDup (l ++ l') → List.NoDup l'.
Proof.
intros * Hnd.
apply NoDup_app_comm in Hnd.
revert l Hnd.
induction l' as [| b]; intros; [ constructor | ].
cbn in Hnd.
apply List.NoDup_cons_iff in Hnd.
destruct Hnd as (H1, H2).
constructor; [ | now apply IHl' in H2 ].
intros H; apply H1.
now apply List.in_or_app; left.
Qed.

Theorem NoDup_app_remove_r :
  ∀ A (l l' : list A), List.NoDup (l ++ l') → List.NoDup l.
Proof.
intros * Hnd.
apply NoDup_app_comm in Hnd.
now apply NoDup_app_remove_l in Hnd.
Qed.

(* "to_radix_loop u r i" is the last u digits of i in base r
   (in List.reverse) *)
Fixpoint to_radix_loop it r i :=
  match it with
  | 0 => []
  | S it' => i mod r :: to_radix_loop it' r (i / r)
  end.

(* conversion natural into radix r as a list of digits; i must be
   less than r^r; always return r digits; e.g. radix 10 37 =
   7; 3; 0 ... (eight 0s) *)
Definition to_radix r i := to_radix_loop r r i.

Definition to_radix_list r := List.map (to_radix r) (List.seq 0 (r ^ r)).

Fixpoint to_radix_inv r l :=
  match l with
  | [] => 0
  | d :: l' => d + r * to_radix_inv r l'
  end.

Theorem to_radix_loop_ub : ∀ it n k i,
  n ≠ 0 → List.nth i (to_radix_loop it n k) 0 < n.
Proof.
intros * Hnz.
revert n k i Hnz.
induction it; intros; [ destruct i; cbn; flia Hnz | cbn ].
destruct i; [ now apply Nat.mod_upper_bound | ].
now apply IHit.
Qed.

Theorem to_radix_ub : ∀ n k i, n ≠ 0 → List.nth i (to_radix n k) 0 < n.
Proof.
intros * Hnz.
now apply to_radix_loop_ub.
Qed.

Theorem to_radix_inv_to_radix_loop : ∀ it n k,
  to_radix_inv n (to_radix_loop it n k) = k mod (n ^ it).
Proof.
intros.
revert k.
induction it; intros; [ easy | cbn ].
rewrite IHit.
symmetry.
apply Nat.Div0.mod_mul_r.
Qed.

Theorem to_radix_loop_to_radix_inv : ∀ l d n it,
  length l + d = n
  → (∀ i, i ∈ l → i < n)
  → n ≤ it + d
  → to_radix_loop it n (to_radix_inv n l) = l ++ List.repeat 0 (it + d - n).
Proof.
intros * Hlen Hl Hit.
revert d n it Hlen Hl Hit.
induction l as [| a]; intros. {
  cbn - [ "-" ].
  cbn in Hlen; subst d.
  clear Hl Hit.
  rewrite Nat.add_sub.
  destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
    subst n; cbn.
    induction it; cbn; [ easy | now cbn; f_equal ].
  }
  induction it; [ easy | cbn ].
  rewrite Nat.mod_small; [ | flia Hnz ].
  rewrite Nat.div_small; [ | flia Hnz ].
  now f_equal.
}
cbn - [ "-" ].
destruct it; [ cbn in Hlen; flia Hlen Hit | ].
cbn - [ "-" ].
f_equal. {
  rewrite Nat.mul_comm, Nat.Div0.mod_add.
  now apply Nat.mod_small, Hl; left.
}
rewrite Nat.mul_comm, Nat.div_add; [ | now subst n ].
rewrite Nat.div_small; [ | now apply Hl; left ].
rewrite Nat.add_0_l.
cbn in Hlen, Hit.
rewrite <- Nat.add_succ_r in Hlen, Hit |-*.
apply IHl; [ easy | | easy ].
intros i Hi.
now apply Hl; right.
Qed.

(* *)

Theorem to_radix_inv_to_radix : ∀ n k,
  k < n ^ n → to_radix_inv n (to_radix n k) = k.
Proof.
intros * Hkn.
progress unfold to_radix.
rewrite to_radix_inv_to_radix_loop.
now apply Nat.mod_small.
Qed.

Theorem to_radix_to_radix_inv : ∀ n l,
  length l = n
  → (∀ i, i ∈ l → i < n)
  → to_radix n (to_radix_inv n l) = l.
Proof.
intros * Hlen Hl.
progress unfold to_radix.
specialize to_radix_loop_to_radix_inv as H1.
specialize (H1 l 0 n n).
do 2 rewrite Nat.add_0_r in H1.
specialize (H1 Hlen Hl (Nat.le_refl _)).
now rewrite Nat.sub_diag, List.app_nil_r in H1.
Qed.

Theorem to_radix_loop_length : ∀ n l it, length (to_radix_loop it n l) = it.
Proof.
intros.
revert n l.
induction it; intros; cbn; [ easy | f_equal; apply IHit ].
Qed.

Theorem to_radix_length : ∀ n l, length (to_radix n l) = n.
Proof.
intros.
progress unfold to_radix.
apply to_radix_loop_length.
Qed.

Theorem to_radix_inv_ub : ∀ n l,
  n ≠ 0
  → (∀ i, i < length l → List.nth i l 0 < n)
  → to_radix_inv n l < n ^ length l.
Proof.
intros * Hnz Hl.
revert n Hnz Hl.
induction l as [| a]; intros; cbn; [ easy | ].
apply Nat.neq_0_lt_0 in Hnz.
specialize (Hl 0 (Nat.lt_0_succ _)) as H1; cbn in H1.
apply Nat.neq_0_lt_0 in Hnz.
specialize (IHl n Hnz) as H2.
assert (H : ∀ i, i < length l → List.nth i l 0 < n). {
  intros i Hi.
  apply (Hl (S i)); cbn.
  now apply -> Nat.succ_lt_mono.
}
specialize (H2 H); clear H.
now apply Nat_lt_lt_add_mul.
Qed.

Theorem to_radix_inj : ∀ n i j,
  i < n ^ n
  → j < n ^ n
  → to_radix n i = to_radix n j
  → i = j.
Proof.
intros * Hi Hj Hij.
apply (f_equal (to_radix_inv n)) in Hij.
rewrite to_radix_inv_to_radix in Hij; [ | easy ].
rewrite to_radix_inv_to_radix in Hij; [ | easy ].
easy.
Qed.

(* *)

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

Global Hint Resolve Nat_mod_fact_upper_bound : core.
