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

(* end pair_eqb *)

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

(* end member *)

(* no_dup: a computable "NoDup" *)

Fixpoint no_dup {A} (eqb : A → A → bool) la :=
  match la with
  | [] => true
  | a :: la' => if member eqb a la' then false else no_dup eqb la'
  end.

(* end no_dup *)

(* App : a notation for iterating concatenation of a list of lists *)

Notation "'App' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, c ++ g) [])
  (at level 45, i at level 0, b at level 60, e at level 60).

Notation "'App' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, c ++ g) [])
  (at level 45, i at level 0, l at level 60).

(* cart_prod: cartesian product of several lists *)

Fixpoint cart_prod {A} (ll : list (list A)) :=
  match ll with
  | [] => [[]]
  | l :: ll' => List.flat_map (λ a, List.map (cons a) (cart_prod ll')) l
  end.

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

Theorem to_radix_loop_length : ∀ n l it, length (to_radix_loop it n l) = it.
Proof.
intros.
revert n l.
induction it; intros; cbn; [ easy | f_equal; apply IHit ].
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
