(* Theorems of general usage, which could be (or not) in Coq library *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Psatz.
Import List List.ListNotations Init.Nat.
Arguments length {A}.

Global Hint Resolve Nat.le_0_l : core.
Global Hint Resolve Nat.lt_0_succ : core.
Global Hint Resolve Nat.lt_succ_diag_r : core.

(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Notation "n !" := (fact n) (at level 1, format "n !").

Notation "x '∈' l" := (List.In x l) (at level 70).
Notation "x '∉' l" := (¬ List.In x l) (at level 70).
Notation "E ⊂ F" := (incl E F) (at level 70).

Notation "l .( i )" := (nth (i - 1) l 0) (at level 1, format "l .( i )").

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

Theorem Tauto_match_nat_same : ∀ A a (b : A),
  match a with 0 => b | S _ => b end = b.
Proof. now intros; destruct a. Qed.

Theorem List_fold_left_map :
  ∀ A B C (f : A → B → A) (g : C → B) (l : list C) a,
  fold_left f (map g l) a = fold_left (λ c b, f c (g b)) l a.
Proof.
intros.
revert a.
induction l as [| c]; intros; [ easy | apply IHl ].
Qed.

Definition AllLt l u := ∀ i, i ∈ l → i < u.

(* iterations in a list
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

Theorem fold_iter_list : ∀ {A B} (f : A → B → A) l d,
  fold_left f l d = iter_list l f d.
Proof. easy. Qed.

Theorem fold_iter_seq : ∀ A b e f (d : A),
  iter_list (seq b (S e - b)) f d = iter_seq b e f d.
Proof. easy. Qed.

Theorem fold_iter_seq' : ∀ A b len f (d : A),
  iter_list (seq b len) f d =
    if b + len =? 0 then d
    else iter_seq b (b + len - 1) f d.
Proof.
intros.
unfold iter_seq.
f_equal; f_equal.
remember (b + len =? 0) as x eqn:Hx; symmetry in Hx.
destruct x. {
  apply Nat.eqb_eq in Hx.
  now apply Nat.eq_add_0 in Hx; destruct Hx; subst b len.
}
apply Nat.eqb_neq in Hx.
destruct len. {
  rewrite Nat.add_0_r in Hx.
  destruct b; [ easy | cbn ].
  now rewrite Nat.add_sub, Nat.sub_diag.
}
rewrite Nat.sub_succ_l; [ cbn | flia ].
f_equal; f_equal; f_equal.
flia.
Qed.

Theorem List_seq_shift' : ∀ len sta,
  map (Nat.add sta) (seq 0 len) = seq sta len.
Proof.
assert (List_seq_shift_1 : ∀ len sta d,
  d ≤ sta
  → map (Nat.add (sta - d)) (seq d len) = seq sta len). {
  intros * Hd.
  revert sta d Hd.
  induction len; intros; [ easy | cbn ].
  rewrite Nat.sub_add; [ f_equal | easy ].
  rewrite <- seq_shift, map_map.
  symmetry.
  rewrite <- IHlen with (d := S d); [ | flia Hd ].
  cbn.
  now rewrite <- seq_shift, map_map.
}
intros.
specialize (List_seq_shift_1 len sta 0 (Nat.le_0_l sta)) as H1.
now rewrite Nat.sub_0_r in H1.
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

Theorem iter_shift : ∀ {T} s b k f (d : T),
  s ≤ b ≤ k
  → iter_seq b k f d =
    iter_seq (b - s) (k - s) (λ c i, f c (s + i)) d.
Proof.
intros * (Hsb, Hbk).
unfold iter_seq, iter_list.
replace (S (k - s) - (b - s)) with (S (k - b)) by flia Hsb Hbk.
rewrite <- Nat.sub_succ_l; [ | easy ].
remember (S k - b)%nat as len; clear Heqlen.
clear k Hbk.
revert b d Hsb.
induction len; intros; [ easy | ].
rewrite seq_S; symmetry.
rewrite seq_S; symmetry.
do 2 rewrite fold_left_app; cbn.
rewrite IHlen; [ | easy ].
now replace (s + (b - s + len)) with (b + len) by flia Hsb.
Qed.

Theorem fold_right_max_ge : ∀ m l, m ≤ fold_right max m l.
Proof.
intros.
induction l as [| a]; [ easy | cbn ].
etransitivity; [ apply IHl | ].
apply Nat.le_max_r.
Qed.

(* conversions if ...? into if ..._dec *)

Theorem bool_dec : ∀ b, { b = true } + { b = false }.
Proof.
intros.
now destruct b; [ left | right ].
Qed.

Theorem if_bool_if_dec : ∀ A (b : bool) (x y : A),
  (if b then x else y) =
  if bool_dec b then x else y.
Proof.
intros.
now destruct (bool_dec b); subst b.
Qed.

Theorem if_eqb_eq_dec : ∀ A i j (a b : A),
  (if i =? j then a else b) = (if Nat.eq_dec i j then a else b).
Proof.
intros.
destruct (Nat.eq_dec i j) as [H1| H1]. {
  now apply Nat.eqb_eq in H1; rewrite H1.
}
now apply Nat.eqb_neq in H1; rewrite H1.
Qed.

Theorem if_ltb_lt_dec : ∀ A i j (a b : A),
  (if i <? j then a else b) = (if lt_dec i j then a else b).
Proof.
intros.
destruct (lt_dec i j) as [H1| H1]. {
  now apply Nat.ltb_lt in H1; rewrite H1.
}
now apply Nat.ltb_nlt in H1; rewrite H1.
Qed.

Theorem if_leb_le_dec : ∀ A i j (a b : A),
  (if i <=? j then a else b) = (if le_dec i j then a else b).
Proof.
intros.
destruct (le_dec i j) as [H1| H1]. {
  now apply Nat.leb_le in H1; rewrite H1.
}
now apply Nat.leb_nle in H1; rewrite H1.
Qed.

(* *)

Theorem Nat_leb_add_mono_l : ∀ a b c, (a + b <=? a + c) = (b <=? c).
Proof.
intros.
remember (b <=? c) as x eqn:Hx; symmetry in Hx.
destruct x. {
  apply Nat.leb_le in Hx.
  now apply Nat.leb_le, Nat.add_le_mono_l.
}
apply Nat.leb_gt in Hx.
apply Nat.leb_gt.
now apply Nat.add_lt_mono_l.
Qed.

Theorem Nat_sub_sub_swap : ∀ a b c, a - b - c = a - c - b.
Proof.
intros.
rewrite <- Nat.sub_add_distr.
rewrite Nat.add_comm.
now rewrite Nat.sub_add_distr.
Qed.

Theorem Nat_sub_sub_distr : ∀ n m p, p ≤ m → n - (m - p) = n + p - m.
Proof.
intros n m p Hpm.
rewrite Nat.add_comm.
revert n m Hpm.
induction p; intros. {
  now rewrite Nat.sub_0_r, Nat.add_0_l.
}
destruct m as [| m]. {
  exfalso; revert Hpm; apply Nat.nle_succ_0.
}
rewrite Nat.sub_succ; cbn.
apply Nat.succ_le_mono in Hpm.
now apply IHp.
Qed.

Theorem Nat_sub_succ_1 : ∀ n, S n - 1 = n.
Proof. now intros; rewrite Nat.sub_succ, Nat.sub_0_r. Qed.

Theorem Nat_succ_sub_succ_r : ∀ a b, b < a → a - b = S (a - S b).
Proof. intros * Hba; flia Hba. Qed.

Theorem Nat_1_le_sub_lt : ∀ i j, 1 ≤ i ≤ j → i - 1 < j.
Proof.
intros * Hij.
destruct i; [ easy | ].
rewrite Nat_sub_succ_1.
apply Hij.
Qed.

Theorem Nat_mod_add_l_mul_r : ∀ a b c,
  b ≠ 0 → (c * b + a) mod b = a mod b.
Proof.
intros * Hbz.
rewrite Nat.add_comm.
now apply Nat.mod_add.
Qed.

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

Theorem Nat_fact_succ : ∀ n, fact (S n) = S n * fact n.
Proof. easy. Qed.

Notation "a ≡ b 'mod' c" := (a mod c = b mod c) (at level 70, b at level 36).
Notation "a ≢ b 'mod' c" := (a mod c ≠ b mod c) (at level 70, b at level 36).

Theorem List_hd_nth_0 {A} : ∀ l (d : A), hd d l = nth 0 l d.
Proof. intros; now destruct l. Qed.

Theorem List_hd_in : ∀ A (l : list A) d, 0 < length l → hd d l ∈ l.
Proof.
intros.
rewrite List_hd_nth_0.
now apply nth_In.
Qed.

Theorem List_map_fun : ∀ A B d l l' (f g : A → B),
  length l = length l'
  → (∀ i, i < length l → f (nth i l d) = g (nth i l' d))
  → map f l = map g l'.
Proof.
intros * Hlen Hf.
revert l' Hlen Hf.
induction l as [| a l]; intros; [ now destruct l' | ].
destruct l' as [| a' l']; [ easy | cbn ].
specialize (Hf 0 (Nat.lt_0_succ _)) as H1; cbn in H1.
rewrite H1; f_equal.
cbn in Hlen; apply Nat.succ_inj in Hlen.
apply IHl; [ easy | ].
intros i Hi.
apply Hf with (i := S i); cbn.
now apply -> Nat.succ_lt_mono.
Qed.

Theorem List_nth_nil : ∀ A i (d : A), nth i [] d = d.
Proof. now intros; destruct i. Qed.

Theorem List_nth_0_cons : ∀ A (a : A) la d, nth 0 (a :: la) d = a.
Proof. easy. Qed.

Theorem List_nth_succ_cons : ∀ A (a : A) la i, nth (S i) (a :: la) = nth i la.
Proof. easy. Qed.

Theorem List_map_nth' : ∀ A B a b (f : A → B) l n,
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

Theorem List_map_hd : ∀ A B a b (f : A → B) l,
  0 < length l → hd b (map f l) = f (hd a l).
Proof.
intros.
do 2 rewrite List_hd_nth_0.
now apply List_map_nth'.
Qed.

Theorem List_app_cons : ∀ A la lb (b : A), la ++ b :: lb = la ++ [b] ++ lb.
Proof. easy. Qed.

Theorem List_app_hd1 : ∀ A (l l' : list A) d,
  0 < length l → hd d (l ++ l') = hd d l.
Proof.
intros.
do 2 rewrite List_hd_nth_0.
now apply app_nth1.
Qed.

Theorem List_app_hd2 : ∀ A (l l' : list A) d,
  length l = 0 → hd d (l ++ l') = hd d l'.
Proof.
intros.
do 2 rewrite List_hd_nth_0.
rewrite app_nth2; [ easy | ].
now apply Nat.le_0_r.
Qed.

Theorem List_seq_eq_nil : ∀ b len, seq b len = [] → len = 0.
Proof.
intros * Hb.
now induction len.
Qed.

Theorem List_seq_hd : ∀ len start d, 0 < len → hd d (seq start len) = start.
Proof.
intros.
rewrite List_hd_nth_0.
rewrite seq_nth; [ | easy ].
apply Nat.add_0_r.
Qed.

Theorem List_filter_nil_iff {A} : ∀ f (l : list A),
  filter f l = [] ↔ (∀ a, a ∈ l → f a = false).
Proof.
intros.
split. {
  intros Hf a Ha.
  induction l as [| b l]; [ easy | ].
  cbn in Hf.
  remember (f b) as c eqn:Hc; symmetry in Hc.
  destruct c; [ easy | ].
  destruct Ha as [Ha| Ha]; [ now subst b | ].
  now apply IHl.
} {
  intros Hf.
  induction l as [| a]; [ easy | cbn ].
  rewrite Hf; [ | now left ].
  apply IHl.
  intros b Hb.
  now apply Hf; right.
}
Qed.

Theorem List_cons_length : ∀ A (a : A) la, length (a :: la) = S (length la).
Proof. easy. Qed.

Theorem List_cons_is_app : ∀ A (a : A) la, a :: la = [a] ++ la.
Proof. easy. Qed.

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

Theorem map_map2 : ∀ A B C D (f : A → B) (g : C → D → A) la lb,
  map f (map2 g la lb) = map2 (λ a b, f (g a b)) la lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
now rewrite IHla.
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

Theorem map2_nil_l : ∀ A B C (f : A → B → C) la, map2 f [] la = [].
Proof.
intros.
now destruct la.
Qed.

Theorem map2_nil_r : ∀ A B C (f : A → B → C) la, map2 f la [] = [].
Proof.
intros.
now destruct la.
Qed.

Theorem in_map2_iff : ∀ A B C (f : A → B → C) la lb c,
  c ∈ map2 f la lb ↔
  ∃ i,
  i < min (length la) (length lb) ∧ ∃ a b, f (nth i la a) (nth i lb b) = c.
Proof.
intros.
split. {
  intros Hc.
  revert lb Hc.
  induction la as [| a]; intros; [ easy | ].
  destruct lb as [| b]; [ easy | ].
  cbn in Hc.
  destruct Hc as [Hc| Hc]. {
    exists 0.
    split; [ cbn; flia | now exists a, b ].
  }
  specialize (IHla _ Hc) as H1.
  destruct H1 as (i & Him & a' & b' & Hi).
  exists (S i).
  split; [ cbn; flia Him | ].
  now exists a', b'.
} {
  intros (i & Him & a' & b' & Hi).
  revert lb i Him Hi.
  induction la as [| a]; intros; [ easy | ].
  destruct lb as [| b]; [ easy | ].
  cbn in Him, Hi |-*.
  destruct i; [ now left | right ].
  apply Nat.succ_lt_mono in Him.
  now apply IHla in Hi.
}
Qed.

Theorem map2_ext_in : ∀ A B C (f g : A → B → C) la lb,
  (∀ a b, a ∈ la → b ∈ lb → f a b = g a b) → map2 f la lb = map2 g la lb.
Proof.
intros * Hab.
revert lb Hab.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | ].
f_equal; [ now apply Hab; left | ].
apply IHla.
intros a' b' Ha' Hb'.
now apply Hab; right.
Qed.

Theorem map2_diag : ∀ A B (f : A → A → B) la,
  map2 f la la = map (λ i, f i i) la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
now rewrite IHla.
Qed.

Theorem map2_map2_seq_l : ∀ A B C (f : A → B → C) d la lb,
  map2 f la lb = map2 (λ i b, f (nth i la d) b) (seq 0 (length la)) lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | ].
f_equal.
rewrite <- seq_shift.
rewrite map2_map_l.
apply IHla.
Qed.

Theorem map2_map2_seq_r : ∀ A B C (f : A → B → C) d la lb,
  map2 f la lb = map2 (λ a i, f a (nth i lb d)) la (seq 0 (length lb)).
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
f_equal.
rewrite <- seq_shift.
rewrite map2_map_r.
apply IHla.
Qed.

Theorem map2_app_l : ∀ A B C l1 l2 l (f : A → B → C),
  map2 f (l1 ++ l2) l =
  map2 f l1 (firstn (length l1) l) ++ map2 f l2 (skipn (length l1) l).
Proof.
intros.
revert l2 l.
induction l1 as [| a1]; intros; [ easy | cbn ].
destruct l as [| a]; [ now rewrite map2_nil_r | cbn ].
f_equal.
apply IHl1.
Qed.

Theorem repeat_app_map2 : ∀ A (la lb : list A) n,
  repeat (la ++ lb) n = map2 (λ x y, app x y) (repeat la n) (repeat lb n).
Proof.
intros.
induction n; [ easy | cbn ].
f_equal; apply IHn.
Qed.

(* end map2 *)

(* rank: rank of the first element satisfying a predicate *)
(* like "find" but returning the rank, not the element itself *)

Fixpoint List_rank_loop i A (f : A → bool) (l : list A) : nat :=
  match l with
  | [] => i
  | x :: tl => if f x then i else List_rank_loop (S i) f tl
end.

Definition List_rank := List_rank_loop 0.

Theorem List_rank_loop_interv : ∀ A f (l : list A) i,
  i ≤ List_rank_loop i f l ≤ i + length l.
Proof.
intros.
revert i.
induction l as [| a]; intros; cbn; [ now rewrite Nat.add_0_r | ].
destruct (f a). {
  split; [ easy | ].
  apply Nat.le_add_r.
}
specialize (IHl (S i)).
rewrite Nat.add_succ_comm in IHl.
split; [ flia IHl | easy ].
Qed.

Theorem List_rank_loop_if : ∀ A d f (l : list A) i j,
  List_rank_loop i f l = j
  → (∀ k, i ≤ k < j → f (nth (k - i) l d) = false) ∧
    (j < i + length l ∧ f (nth (j - i) l d) = true ∨
     j = i + length l).
Proof.
intros * Hi.
(**)
split. {
  intros p Hp.
  remember (p - i) as k eqn:Hk.
  replace p with (i + k) in Hp by flia Hp Hk.
  destruct Hp as (_, Hp).
  clear p Hk.
  revert i l Hi Hp.
  induction k; intros. {
    rewrite Nat.add_0_r in Hp.
    destruct l as [| a]. {
      now subst j; apply Nat.lt_irrefl in Hp.
    }
    cbn in Hi |-*.
    destruct (f a); [ | easy ].
    now subst j; apply Nat.lt_irrefl in Hp.
  }
  destruct l as [| a]; [ subst j; cbn in Hp; flia Hp | ].
  cbn in Hi |-*.
  rewrite <- Nat.add_succ_comm in Hp.
  remember (f a) as b eqn:Hb; symmetry in Hb.
  destruct b; [ subst j; flia Hp | ].
  now apply IHk with (i := S i).
}
remember (j - i) as k eqn:Hk.
replace j with (i + k) in Hi |-*. 2: {
  specialize (List_rank_loop_interv f l i) as H1.
  rewrite Hi in H1.
  flia Hk H1.
}
clear j Hk.
revert i l Hi.
induction k; intros. {
  rewrite Nat.add_0_r in Hi |-*.
  destruct l; [ now right; symmetry; apply Nat.add_0_r | ].
  left; cbn in Hi |-*.
  split; [ flia | ].
  destruct (f a); [ easy | ].
  specialize (List_rank_loop_interv f l (S i)) as H1.
  rewrite Hi in H1; flia H1.
}
destruct l; cbn in Hi; [ flia Hi | ].
destruct (f a); [ flia Hi | cbn in Hi ].
rewrite <- Nat.add_succ_comm in Hi.
apply IHk in Hi; cbn.
now do 2 rewrite <- Nat.add_succ_comm.
Qed.

Theorem List_rank_if : ∀ A d f (l : list A) i,
  List_rank f l = i
  → (∀ j, j < i → f (nth j l d) = false) ∧
    (i < length l ∧ f (nth i l d) = true ∨ i = length l).
Proof.
intros * Hi.
apply List_rank_loop_if with (d := d) in Hi.
rewrite Nat.sub_0_r in Hi; cbn in Hi.
destruct Hi as (Hbef, Hat).
split; [ | easy ].
intros j Hj.
specialize (Hbef j).
rewrite Nat.sub_0_r in Hbef.
now apply Hbef.
Qed.

(* end List_rank *)

Theorem Nat_b2n_upper_bound : ∀ b, Nat.b2n b ≤ 1.
Proof.
intros; destruct b; cbn; flia.
Qed.

Theorem Nat_mod_fact_upper_bound : ∀ k n, k mod n! < n!.
Proof.
intros.
apply Nat.mod_upper_bound, fact_neq_0.
Qed.

Theorem List_skipn_skipn : ∀ A i j (la : list A),
  skipn i (skipn j la) = skipn (i + j) la.
Proof.
intros.
revert j.
induction la as [| a]; intros; cbn. {
  now do 3 rewrite skipn_nil.
}
destruct j; [ now rewrite Nat.add_0_r | ].
rewrite skipn_cons.
rewrite <- Nat.add_succ_comm, Nat.add_succ_l.
rewrite skipn_cons.
apply IHla.
Qed.

Theorem List_skipn_is_cons : ∀ A (d : A) la n,
  n < length la
  → skipn n la = nth n la d :: skipn (S n) la.
Proof.
intros * Hn.
revert n Hn.
induction la as [| a]; intros; [ easy | ].
destruct n; [ easy | ].
cbn in Hn; apply Nat.succ_lt_mono in Hn.
rewrite List_nth_succ_cons.
do 2 rewrite skipn_cons.
now apply IHla.
Qed.

Theorem Nat_lt_lt_sum_mul_lt_sum_mul : ∀ a b c d,
  a < b
  → c < d
  → a * d + b * c < a * c + b * d.
Proof.
intros * Hab Hcd.
rewrite Nat.add_comm.
apply Nat.lt_add_lt_sub_r.
rewrite <- Nat.add_sub_assoc; [ | apply Nat.mul_le_mono_r; flia Hab ].
rewrite <- Nat.mul_sub_distr_r.
apply Nat.lt_sub_lt_add_l.
rewrite <- Nat.mul_sub_distr_r.
apply Nat.mul_lt_mono_pos_l; [ | easy ].
flia Hab.
Qed.

(* butn: list without its nth element *)

Definition butn {A} n (l : list A) :=
  firstn n l ++ skipn (S n) l.

Theorem fold_butn : ∀ A n (l : list A),
  firstn n l ++ skipn (S n) l = butn n l.
Proof. easy. Qed.

Theorem butn_nil : ∀ A n, butn n ([] : list A) = [].
Proof. now intros; destruct n. Qed.

Theorem butn_cons : ∀ A (a : A) la n, butn (S n) (a :: la) = a :: butn n la.
Proof.
intros.
unfold butn.
now rewrite firstn_cons, skipn_cons.
Qed.

Theorem map_butn : ∀ A B (f : A → B) la n,
  map f (butn n la) = butn n (map f la).
Proof.
intros.
revert n.
induction la as [| a]; intros; cbn; [ now do 2 rewrite butn_nil | ].
destruct n; [ easy | ].
do 2 rewrite butn_cons.
cbn; f_equal.
apply IHla.
Qed.

Theorem butn_out : ∀ A (l : list A) i, length l ≤ i → butn i l = l.
Proof.
intros * Hi.
revert i Hi.
induction l as [| a]; intros; [ apply butn_nil | ].
destruct i; [ easy | ].
cbn in Hi; apply Nat.succ_le_mono in Hi.
rewrite butn_cons.
now rewrite IHl.
Qed.

Theorem butn_length : ∀ A n (l : list A),
  length (butn n l) = length l - Nat.b2n (n <? length l).
Proof.
intros.
unfold Nat.b2n; rewrite if_bool_if_dec.
destruct (bool_dec (n <? length l)) as [Hnl| Hnl]. 2: {
  apply Nat.ltb_ge in Hnl; rewrite Nat.sub_0_r.
  now rewrite butn_out.
}
apply Nat.ltb_lt in Hnl.
revert n Hnl.
induction l as [| a]; intros; [ easy | ].
cbn; rewrite Nat.sub_0_r.
destruct n; [ easy | ].
rewrite butn_cons; cbn.
cbn in Hnl.
apply Nat.succ_lt_mono in Hnl.
rewrite IHl; [ | easy ].
destruct (length l); [ easy | ].
now cbn; rewrite Nat.sub_0_r.
Qed.

Theorem nth_butn_before : ∀ A (l : list A) i j d,
  j ≤ i
  → nth i (butn j l) d = nth (i + 1) l d.
Proof.
intros * Hji.
revert i j Hji.
induction l as [| a]; intros; cbn. {
  rewrite butn_nil.
  now destruct i.
}
destruct j; [ now rewrite Nat.add_1_r | ].
destruct i; [ easy | ].
apply Nat.succ_le_mono in Hji.
rewrite butn_cons; cbn.
now apply IHl.
Qed.

Theorem nth_butn_after : ∀ A (l : list A) i j d,
  i < j
  → nth i (butn j l) d = nth i l d.
Proof.
intros * Hij.
revert i j Hij.
induction l as [| a]; intros; cbn. {
  rewrite butn_nil.
  now destruct i.
}
destruct j; [ easy | ].
destruct i; [ easy | ].
apply Nat.succ_lt_mono in Hij.
rewrite butn_cons; cbn.
now apply IHl.
Qed.

Theorem nth_butn : ∀ A (l : list A) i j d,
  nth i (butn j l) d = nth (i + Nat.b2n (j <=? i)) l d.
Proof.
intros.
remember (j <=? i) as b eqn:Hb; symmetry in Hb.
destruct b. {
  apply Nat.leb_le in Hb.
  now rewrite nth_butn_before.
} {
  apply Nat.leb_gt in Hb.
  rewrite nth_butn_after; [ | easy ].
  now rewrite Nat.add_0_r.
}
Qed.

Theorem in_butn : ∀ A (l : list A) i a, a ∈ butn i l → a ∈ l.
Proof.
intros * Ha.
revert i Ha.
induction l as [| b]; intros. {
  now rewrite butn_nil in Ha.
}
destruct i; [ now right | ].
rewrite butn_cons in Ha.
destruct Ha as [Ha| Ha]; [ now left | right ].
now apply IHl in Ha.
Qed.

Theorem map_butn_seq : ∀ A (f : _ → A) n sta len,
  map f (butn n (seq sta len)) =
  map (λ i, f (i + Nat.b2n (sta + n <=? i)))
    (seq sta (len - Nat.b2n (n <? len))).
Proof.
intros.
revert n sta.
induction len; intros; [ now rewrite butn_nil | ].
destruct n. {
  cbn; rewrite Nat.sub_0_r, Nat.add_0_r.
  rewrite <- seq_shift.
  rewrite map_map.
  apply map_ext_in.
  intros i Hi.
  apply in_seq in Hi.
  rewrite <- Nat.add_1_r.
  destruct (le_dec sta i) as [H| H]; [ | easy ].
  now apply Nat.leb_le in H; rewrite H.
}
unfold Nat.b2n.
rewrite if_bool_if_dec.
destruct (bool_dec (S n <? S len)) as [Hn| Hn]. {
  apply Nat.ltb_lt in Hn.
  cbn - [ butn ].
  rewrite Nat.sub_0_r, butn_cons; cbn.
  apply Nat.succ_lt_mono in Hn.
  rewrite IHlen.
  destruct len; [ easy | ].
  unfold Nat.b2n.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec n (S len)) as [H| H]; [ clear H | easy ].
  rewrite Nat_sub_succ_1; cbn - [ "<=?" ].
  f_equal. {
    rewrite if_leb_le_dec.
    destruct (le_dec (sta + S n) sta) as [H| H]; [ flia H | clear H ].
    now rewrite Nat.add_0_r.
  }
  apply map_ext_in.
  intros i Hi.
  now rewrite (Nat.add_succ_r sta).
} {
  apply Nat.ltb_ge in Hn.
  rewrite Nat.sub_0_r.
  rewrite butn_out; [ | now rewrite seq_length ].
  apply map_ext_in.
  intros i Hi.
  apply in_seq in Hi.
  rewrite if_leb_le_dec.
  destruct (le_dec (sta + S n) i) as [H| H]; [ flia Hn Hi H | ].
  now rewrite Nat.add_0_r.
}
Qed.

Theorem butn_app : ∀ A (l1 l2 : list A) i,
  butn i (l1 ++ l2) =
    if i <? length l1 then butn i l1 ++ l2
    else l1 ++ butn (i - length l1) l2.
Proof.
intros.
rewrite if_ltb_lt_dec.
unfold butn.
rewrite firstn_app, skipn_app.
destruct (lt_dec i (length l1)) as [Hil| Hil]. {
  rewrite (proj2 (Nat.sub_0_le i _)); [ | now apply Nat.lt_le_incl ].
  rewrite (proj2 (Nat.sub_0_le _ _)); [ | easy ].
  rewrite firstn_O, skipn_O, app_nil_r.
  apply app_assoc.
} {
  apply Nat.nlt_ge in Hil.
  rewrite firstn_all2; [ | easy ].
  rewrite skipn_all2. 2: {
    now apply Nat.lt_le_incl; apply -> Nat.succ_le_mono.
  }
  rewrite app_nil_l.
  rewrite Nat.sub_succ_l; [ | easy ].
  symmetry; apply app_assoc.
}
Qed.

(* end butn *)

(* insert in a list (reverse of butn) *)

Definition insert_at A k (la : list A) e :=
  firstn k la ++ e :: skipn k la.

(* end insert_at *)

(* replace in a list *)

Definition replace_at {A} k (la : list A) e :=
  firstn k la ++ e :: skipn (S k) la.

Theorem replace_at_succ_cons : ∀ A i a b (l : list A),
  replace_at (S i) (a :: l) b = a :: replace_at i l b.
Proof. easy. Qed.

(* end replace_at *)

(* repeat_apply: applying a function n times *)

Fixpoint repeat_apply A n (f : A → A) a :=
  match n with
  | 0 => a
  | S n' => repeat_apply n' f (f a)
  end.

Theorem List_fold_left_nop_r : ∀ A B (a : A) (lb : list B) (f : A → _),
  fold_left (λ c _, f c) lb a = repeat_apply (length lb) f a.
Proof.
intros.
revert a.
induction lb as [| b]; intros; [ easy | cbn ].
apply IHlb.
Qed.

Theorem repeat_apply_id : ∀ A len f (a : A),
  (∀ a, f a = a)
  → repeat_apply len f a = a.
Proof.
intros * Hid.
revert a.
induction len; intros; [ easy | cbn ].
rewrite IHlen.
apply Hid.
Qed.

(* end repeat_apply *)

(* equivalence & equality *)

Definition equivalence {A} (eqv : A → A → bool) :=
  (∀ a, eqv a a = true) ∧
  (∀ a b, eqv a b = true → eqv b a = true) ∧
  (∀ a b c, eqv a b = true → eqv b c = true → eqv a c = true).

Definition equality {A} (eqb : A → A → bool) := ∀ a b, eqb a b = true ↔ a = b.

Theorem equality_refl {A} (eqb : A → _) : equality eqb → ∀ a, eqb a a = true.
Proof.
intros * Heqb *.
now apply Heqb.
Qed.

Theorem equality_in_dec : ∀ A (eqb : A → _) (Heqb : equality eqb) (a : A) la,
  { a ∈ la } + { a ∉ la }.
Proof.
intros.
induction la as [| b]; [ now right | ].
remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ now apply Heqb in Hab; subst b; left; left | ].
destruct IHla as [H1| H1]; [ now left; right | right ].
intros H2; apply H1; clear H1.
destruct H2 as [H2| H2]; [ | easy ].
subst b.
now rewrite (equality_refl Heqb) in Hab.
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

Definition comparator {A} (compare : A → _) :=
  ∀ a b, compare a b = Eq ↔ a = b.

(* list_eqv *)

Fixpoint list_eqv A (eqv : A → A → bool) la lb :=
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

Theorem list_eqb_eq : ∀ A (eqb : A → _),
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

Theorem list_eqb_neq : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb, list_eqv eqb la lb = false → la ≠ lb.
Proof.
intros * Heqb * Hab H; subst lb.
induction la as [| a]; [ easy | cbn in Hab ].
rewrite (equality_refl Heqb) in Hab.
congruence.
Qed.

Theorem equality_list_eqv : ∀ A (eqb : A → _),
  equality eqb ↔ equality (list_eqv eqb).
Proof.
intros.
split. {
  intros Heqb la lb.
  now apply list_eqb_eq.
} {
  intros Heqb a b.
  unfold equality in Heqb.
  split. {
    intros Hab.
    specialize (Heqb [a] [b]).
    cbn in Heqb.
    rewrite Hab in Heqb.
    specialize (proj1 Heqb eq_refl) as H1.
    now injection H1.
  } {
    intros Hab; subst b.
    specialize (Heqb [a] [a]).
    cbn in Heqb.
    specialize (proj2 Heqb eq_refl) as H1.
    now destruct (eqb a a).
  }
}
Qed.

(* end list_eqv *)

(* list_leb *)

Fixpoint list_leb A (leb : A → A → bool) la lb :=
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

Fixpoint list_ltb A (ltb : A → A → bool) la lb :=
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
  unfold pair_eqb in Hab.
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
  unfold pair_eqb.
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

Definition unsome A (d : A) o :=
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

Theorem extract_Some_iff : ∀ A (f : A → _) l a bef aft,
  extract f l = Some (bef, a, aft)
  ↔ (∀ x, x ∈ bef → f x = false) ∧ f a = true ∧ l = bef ++ a :: aft.
Proof.
intros.
split. {
  intros He.
  revert a bef aft He.
  induction l as [| b]; intros; [ easy | cbn ].
  cbn in He.
  remember (f b) as fb eqn:Hfb; symmetry in Hfb.
  destruct fb. {
    now injection He; clear He; intros; subst bef b aft.
  }
  remember (extract f l) as lal eqn:Hlal; symmetry in Hlal.
  destruct lal as [((bef', x), aft') | ]; [ | easy ].
  injection He; clear He; intros; subst bef x aft'.
  rename bef' into bef.
  specialize (IHl _ _ _ eq_refl) as H1.
  destruct H1 as (H1 & H2 & H3).
  split. {
    intros c Hc.
    destruct Hc as [Hc| Hc]; [ now subst c | ].
    now apply H1.
  }
  split; [ easy | ].
  now cbn; f_equal.
} {
  intros He.
  destruct He as (Hbef & Hf & Hl).
  subst l.
  revert a aft Hf.
  induction bef as [| b]; intros; cbn; [ now rewrite Hf | ].
  rewrite Hbef; [ | now left ].
  rewrite IHbef; [ easy | | easy ].
  now intros c Hc; apply Hbef; right.
}
Qed.

Theorem extract_None_iff : ∀ A (f : A → _) l,
  extract f l = None ↔ ∀ a, a ∈ l → f a = false.
Proof.
intros.
split. {
  intros He * Ha.
  revert a Ha.
  induction l as [| b]; intros; [ easy | ].
  cbn in He.
  remember (f b) as fb eqn:Hfb; symmetry in Hfb.
  destruct fb; [ easy | ].
  destruct Ha as [Ha| Ha]; [ now subst b | ].
  apply IHl; [ | easy ].
  now destruct (extract f l) as [((bef, x), aft)| ].
} {
  intros Hf.
  induction l as [| a]; [ easy | cbn ].
  rewrite Hf; [ | now left ].
  rewrite IHl; [ easy | ].
  intros c Hc.
  now apply Hf; right.
}
Qed.

(* member: a computable "In" *)

Fixpoint member A (eqb : A → A → bool) a la :=
  match la with
  | [] => false
  | b :: lb => if eqb a b then true else member eqb a lb
  end.

Theorem member_true_iff : ∀ A (eqb : A → _),
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

Theorem member_false_iff : ∀ A (eqb : A → _),
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

Fixpoint no_dup A (eqb : A → A → bool) la :=
  match la with
  | [] => true
  | a :: la' => if member eqb a la' then false else no_dup eqb la'
  end.

Theorem no_dup_NoDup : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la, no_dup eqb la = true ↔ NoDup la.
Proof.
intros * Heqb *.
split; intros Hla. {
  induction la as [| a]; [ constructor | ].
  apply NoDup_cons_iff.
  cbn in Hla.
  rewrite if_bool_if_dec in Hla.
  destruct (bool_dec (member eqb a la)) as [Hal| Hal]; [ easy | ].
  split; [ | now apply IHla ].
  intros H.
  now specialize (proj1 (member_false_iff Heqb _ _) Hal a H).
} {
  induction la as [| a]; [ easy | cbn ].
  rewrite if_bool_if_dec.
  apply NoDup_cons_iff in Hla.
  destruct (bool_dec (member eqb a la)) as [Hal| Hal]; [ | now apply IHla ].
  apply (member_true_iff Heqb) in Hal.
  destruct Hla as (Hala & Hnd).
  destruct Hal as (l1 & l2 & H); subst la.
  exfalso; apply Hala.
  now apply in_or_app; right; left.
}
Qed.

Theorem no_dup_false_iff : ∀ A (eqb : A → _),
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
    assert (H : a ∈ l2 ++ a :: l3) by now apply in_or_app; right; left.
    now specialize (H1 H).
  }
  remember (member eqb b _) as mbl eqn:Hmbl; symmetry in Hmbl.
  now destruct mbl.
}
Qed.

(* end no_dup *)

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

Theorem List_fold_right_ext_in : ∀ A B (f g : B → A → A) l a,
  (∀ b c, b ∈ l → f b c = g b c)
  → fold_right f a l = fold_right g a l.
Proof.
intros * Hfg.
revert a.
induction l as [| d]; intros; [ easy | cbn ].
rewrite (Hfg d); [ | now left ].
rewrite IHl; [ easy | ].
intros b c Hb.
apply Hfg.
now right.
Qed.

Theorem List_fold_left_map_nth_len : ∀ A (la : list A) sta len f d,
  fold_left (λ lb k, map (λ i, nth (f k i) lb d) (seq 0 (length lb)))
    (seq sta len) la =
  fold_left (λ lb k, map (λ i, nth (f k i) lb d) (seq 0 (length la)))
    (seq sta len) la.
Proof.
intros.
revert sta la.
induction len; intros; [ easy | cbn ].
rewrite IHlen.
apply List_fold_left_ext_in.
intros i lb Hi; apply in_seq in Hi.
now rewrite map_length, seq_length.
Qed.

Theorem List_eq_firstn_nil : ∀ A n (l : list A),
  firstn n l = [] → n = 0 ∨ l = [].
Proof.
intros * Hnl.
revert l Hnl.
induction n; intros; [ now left | right ].
destruct l as [| x]; [ easy | easy ].
Qed.

Theorem List_eq_skipn_nil: ∀ A n (l : list A), skipn n l = [] → length l ≤ n.
Proof.
intros * Hnl.
revert l Hnl.
induction n; intros; [ now cbn in Hnl; subst l | ].
destruct l as [| x]; [ easy | ].
cbn in Hnl |-*.
apply -> Nat.succ_le_mono.
now apply IHn.
Qed.

Theorem List_eq_rev_nil {A} : ∀ (l : list A), rev l = [] → l = [].
Proof.
intros * Hl.
destruct l as [| a]; [ easy | cbn in Hl ].
now apply app_eq_nil in Hl.
Qed.

Theorem List_map_seq : ∀ A (f : _ → A) sta len,
  map f (seq sta len) = map (λ i, f (sta + i)) (seq 0 len).
Proof.
intros.
revert sta.
induction len; intros; [ easy | cbn ].
symmetry.
rewrite <- seq_shift, map_map.
rewrite Nat.add_0_r; f_equal.
symmetry.
rewrite IHlen.
apply map_ext_in.
intros i Hi.
now rewrite Nat.add_succ_comm.
Qed.

Theorem List_map_seq_length : ∀ A (f : _ → A) a len,
  length (map f (seq a len)) = len.
Proof.
intros.
now rewrite map_length, seq_length.
Qed.

Theorem List_map_map_seq : ∀ A B (f : A → B) d la,
  map f la = map (λ i, f (nth i la d)) (seq 0 (length la)).
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
f_equal.
rewrite <- seq_shift.
now rewrite map_map.
Qed.

Theorem List_map_nth_seq : ∀ A (la : list A) d,
  la = map (λ i, nth i la d) (seq 0 (length la)).
Proof.
intros.
induction la as [| a]; [ easy | ].
cbn; f_equal.
rewrite <- seq_shift.
now rewrite map_map.
Qed.

Theorem List_map_nth_seq' : ∀ A (la : list A) d n,
  n = length la
  → la = map (λ i, nth i la d) (seq 0 n).
Proof.
intros * Hn.
subst n.
apply List_map_nth_seq.
Qed.

Theorem List_map_repeat : ∀ A B x n (f : A → B),
  map f (repeat x n) = repeat (f x) n.
Proof.
intros.
induction n; [ easy | cbn ].
f_equal; apply IHn.
Qed.

Theorem List_rev_rev : ∀ A (la lb : list A), rev la = rev lb → la = lb.
Proof.
intros * Hab.
apply (f_equal (λ l, rev l)) in Hab.
now do 2 rewrite rev_involutive in Hab.
Qed.

Theorem List_rev_symm : ∀ A (la lb : list A), rev la = lb → la = rev lb.
Proof.
intros * Hab.
now subst lb; rewrite rev_involutive.
Qed.

Theorem List_rev_repeat : ∀ A (x : A) n,
  rev (repeat x n) = repeat x n.
Proof.
intros.
induction n; [ easy | cbn ].
rewrite repeat_cons; f_equal.
apply IHn.
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

Theorem List_nth_firstn : ∀ A (l : list A) i j d,
  i < j
  → nth i (firstn j l) d = nth i l d.
Proof.
intros * Hij.
revert i j Hij.
induction l as [| a la]; intros; [ now rewrite firstn_nil | ].
destruct j; [ easy | ].
rewrite firstn_cons.
destruct i; [ easy | cbn ].
apply IHla.
now apply Nat.succ_lt_mono.
Qed.

Theorem List_nth_skipn : ∀ A (l : list A) i j d,
  nth i (skipn j l) d = nth (i + j) l d.
Proof.
intros.
revert i j.
induction l as [| a la]; intros. {
  rewrite skipn_nil; cbn.
  now destruct i, j.
}
destruct j; [ now rewrite Nat.add_0_r | ].
rewrite Nat.add_succ_r; cbn.
apply IHla.
Qed.

Theorem List_app_eq_app' :
  ∀ (X : Type) (x1 x2 y1 y2 : list X),
    length x1 = length y1
    → x1 ++ x2 = y1 ++ y2
    → x1 = y1 ∧ x2 = y2.
Proof.
intros * Hxy Haa.
revert x2 y1 y2 Hxy Haa.
induction x1 as [| a1]; intros; cbn. {
  cbn in Hxy, Haa.
  symmetry in Hxy; apply length_zero_iff_nil in Hxy.
  now subst x2 y1.
}
destruct y1 as [| b1]; [ easy | ].
injection Haa; clear Haa; intros H1 H2; subst b1.
cbn in Hxy.
apply Nat.succ_inj in Hxy.
specialize (IHx1 x2 y1 y2 Hxy H1).
now destruct IHx1; subst y1 y2.
Qed.

Theorem List_last_cons_cons : ∀ A l (x y d : A),
  last (x :: y :: l) d = last (y :: l) d.
Proof. easy. Qed.

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

Theorem List_last_rev : ∀ A (l : list A) d,
  last (rev l) d = hd d l.
Proof.
intros.
destruct l as [| a]; [ easy | apply last_last ].
Qed.

Theorem List_last_nth : ∀ A (la : list A) d,
  last la d = nth (length la - 1) la d.
Proof.
intros.
destruct la as [| a] using rev_ind; [ easy | cbn ].
rewrite last_last, app_length, Nat.add_sub.
rewrite app_nth2; [ | now unfold ge ].
now rewrite Nat.sub_diag.
Qed.

(* common for all iterators *)

Theorem iter_list_seq : ∀ T d (op : T → T → T) b len f,
  len ≠ 0
  → iter_list (seq b len) (λ c i, op c (f i)) d =
    iter_seq b (b + len - 1) (λ c i, op c (f i)) d.
Proof.
intros * Hlen.
unfold iter_seq.
f_equal; f_equal.
flia Hlen.
Qed.

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

Theorem iter_list_op_fun_from_d : ∀ T A d op a l (f : A → _)
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  iter_list l (λ (c : T) (i : A), op c (f i)) a =
  op a (iter_list l (λ (c : T) (i : A), op c (f i)) d).
Proof.
intros.
unfold iter_list.
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
unfold iter_seq.
now replace (S k - b) with 0 by flia Hkb.
Qed.

Theorem iter_list_only_one : ∀ T A d (op : T → T → T) (g : A → T) a
  (op_d_l : ∀ x, op d x = x),
  iter_list [a] (λ c i, op c (g i)) d = g a.
Proof.
intros * op_d_l.
unfold iter_list; cbn.
apply op_d_l.
Qed.

Theorem iter_seq_only_one : ∀ T d (op : T → T → T) g n
  (op_d_l : ∀ x, op d x = x),
  iter_seq n n (λ c i, op c (g i)) d = g n.
Proof.
intros * op_d_l.
unfold iter_seq.
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
  unfold iter_seq.
  now replace (S k - b) with 0 by flia Hkb.
}
apply Nat.nle_gt in Hkb.
apply -> Nat.lt_succ_r in Hkb.
unfold iter_seq, iter_list.
remember (S k - b) as len eqn:Hlen.
replace k with (b + len - 1) by flia Hkb Hlen.
clear Hlen Hkb.
revert b.
induction len; intros; [ easy | ].
rewrite seq_S at 1; cbn.
rewrite fold_left_app; cbn.
symmetry.
rewrite fold_left_op_fun_from_d with (d := d); [ | easy | easy | easy ].
rewrite op_comm.
f_equal; [ | rewrite op_d_l; f_equal; flia ].
rewrite IHlen.
rewrite <- seq_shift.
rewrite List_fold_left_map.
apply List_fold_left_ext_in.
intros j c Hj.
apply in_seq in Hj.
f_equal; f_equal; flia.
Qed.

(* *)

Theorem fold_left_max_from_0 : ∀ A a l (f : A → _),
  fold_left (λ c i, max c (f i)) l a =
  max a (fold_left (λ c i, max c (f i)) l 0).
Proof.
intros.
apply fold_left_op_fun_from_d. {
  now intros; apply max_r.
} {
  now intros; rewrite Nat.max_l.
} {
  apply Nat.max_assoc.
}
Qed.

Theorem max_list_app : ∀ A (la lb : list A) f,
  Max (i ∈ la ++ lb), f i = max (Max (i ∈ la), f i) (Max (i ∈ lb), f i).
Proof.
intros.
rewrite iter_list_app.
unfold iter_list.
apply fold_left_max_from_0.
Qed.

Theorem max_list_cons : ∀ A (a : A) la f,
  Max (i ∈ a :: la), f i = max (f a) (Max (i ∈ la), f i).
Proof.
intros.
apply iter_list_cons. {
  now intros; apply max_r.
} {
  now intros; rewrite Nat.max_l.
} {
  apply Nat.max_assoc.
}
Qed.

Theorem List_flat_map_length : ∀ A B (f : A → list B) l,
  length (flat_map f l) = iter_list l (fun c a => c + length (f a)) 0.
Proof.
intros.
induction l as [| a]; [ now rewrite iter_list_empty | cbn ].
rewrite app_length.
rewrite iter_list_cons; cycle 1. {
  apply Nat.add_0_l.
} {
  apply Nat.add_0_r.
} {
  apply Nat.add_assoc.
}
now cbn; f_equal.
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
apply iter_list_cons; [ easy | apply app_nil_r | ].
apply app_assoc.
Qed.

Theorem App_list_all_nil : ∀ A B l (f : A → list B),
  (∀ a, a ∈ l → f a = [])
  → App (a ∈ l), f a = [].
Proof.
intros * Hl.
apply iter_list_all_d; [ easy | apply app_nil_r | | easy ].
apply app_assoc.
Qed.

Theorem App_list_eq_nil : ∀ A B (l : list A) (f : A → list B),
  App (a ∈ l), f a = [] → ∀ a, a ∈ l → f a = [].
Proof.
intros * Happ * Hl.
induction l as [| b]; [ easy | ].
rewrite App_list_cons in Happ.
apply app_eq_nil in Happ.
destruct Hl as [Hl| Hl]; [ now subst a | ].
now apply IHl.
Qed.

Theorem App_list_concat_map : ∀ A B (l : list A) (f : A → list B),
  App (a ∈ l), f a = concat (map f l).
Proof.
intros.
induction l as [| a]; [ easy | cbn ].
rewrite App_list_cons.
now rewrite IHl.
Qed.

Theorem in_App_list : ∀ A B (f : A → list B) l y,
  y ∈ App (i ∈ l), f i ↔ (∃ x : A, x ∈ l ∧ y ∈ f x).
Proof.
intros.
rewrite App_list_concat_map.
rewrite <- flat_map_concat_map.
apply in_flat_map.
Qed.

Theorem App_split : ∀ A j (g : nat → list A) b k,
  b ≤ S j ≤ S k
  → App (i = b, k), g i = App (i = b, j), g i ++ App (i = j+1, k), g i.
Proof.
intros * Hbjk.
apply iter_seq_split; [ easy | | | easy ]. {
  apply app_nil_r.
} {
  apply app_assoc.
}
Qed.

Theorem App_list_app : ∀ A B (la lb : list A) (f : A → list B),
  App (i ∈ la ++ lb), f i = App (i ∈ la), f i ++ App (i ∈ lb), f i.
Proof.
intros.
rewrite iter_list_app.
unfold iter_list.
rewrite fold_left_op_fun_from_d with (d := []); [ easy | easy | | ]. {
  apply app_nil_r.
} {
  apply app_assoc.
}
Qed.

Theorem App_only_one : ∀ A (g : _ → list A) n, App (i = n, n), g i = g n.
Proof.
intros.
now apply iter_seq_only_one.
Qed.

(* cart_prod: cartesian product of several lists *)

Fixpoint cart_prod {A} (ll : list (list A)) :=
  match ll with
  | [] => [[]]
  | l :: ll' => flat_map (λ a, map (cons a) (cart_prod ll')) l
  end.

Theorem cart_prod_length : ∀ A (ll : list (list A)),
  ll ≠ []
  → length (cart_prod ll) = iter_list ll (fun c l => c * length l) 1.
Proof.
intros * Hll.
revert Hll.
induction ll as [| l1]; intros; [ easy | clear Hll; cbn ].
rewrite iter_list_cons; cycle 1.
  apply Nat.mul_1_l.
  apply Nat.mul_1_r.
  apply Nat.mul_assoc.
rewrite List_flat_map_length.
erewrite iter_list_eq_compat. 2: {
  intros i Hi.
  now rewrite map_length.
}
cbn.
destruct ll as [| l2]. {
  rewrite iter_list_empty with (l := []); [ | easy ].
  rewrite Nat.mul_1_r; cbn.
  induction l1 as [| a]; [ easy | ].
  rewrite iter_list_cons; cycle 1.
    apply Nat.add_0_l.
    apply Nat.add_0_r.
    apply Nat.add_assoc.
  now cbn; rewrite IHl1.
}
rewrite IHll; [ | easy ].
induction l1 as [| a]; [ easy | ].
rewrite iter_list_cons; cycle 1.
  apply Nat.add_0_l.
  apply Nat.add_0_r.
  apply Nat.add_assoc.
now cbn; rewrite IHl1.
Qed.

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
apply in_flat_map in Hl.
destruct Hl as (a & Hl1 & Ha).
apply in_map_iff in Ha.
destruct Ha as (l3 & Hl & Hl3).
subst l; cbn; f_equal.
now apply IHll.
Qed.

Theorem nth_in_cart_prod : ∀ A (d : A) ll l i,
  i < length ll
  → l ∈ cart_prod ll
  → nth i l d ∈ nth i ll [].
Proof.
intros * Hi Hll.
revert l i Hi Hll.
induction ll as [| l1]; intros; [ easy | ].
cbn in Hll |-*.
destruct i. {
  destruct ll as [| l2]. {
    apply in_flat_map in Hll.
    destruct Hll as (a & Ha & Hla).
    apply in_map_iff in Hla.
    now destruct Hla as (l2 & H & Hl2); subst l.
  }
  apply in_flat_map in Hll.
  destruct Hll as (a & Hl1 & Hl).
  apply in_map_iff in Hl.
  now destruct Hl as (l3 & H & Hl3); subst l.
}
cbn in Hi; apply Nat.succ_lt_mono in Hi.
destruct ll as [| l2]; [ easy | ].
apply in_flat_map in Hll.
destruct Hll as (a & Ha & Hl).
apply in_map_iff in Hl.
destruct Hl as (l3 & H & Hl3); subst l.
rewrite List_nth_succ_cons.
now apply IHll.
Qed.

Theorem in_cart_prod_iff : ∀ A (d : A) ll la,
  la ∈ cart_prod ll
  ↔ length la = length ll ∧ ∀ i, i < length la → nth i la d ∈ nth i ll [].
Proof.
intros.
split. {
  intros Hla.
  split; [ now apply in_cart_prod_length in Hla | ].
  intros i Hi.
  apply nth_in_cart_prod; [ | easy ].
  apply in_cart_prod_length in Hla.
  congruence.
} {
  intros (Hla & Hnth).
  revert la Hla Hnth.
  induction ll as [| lb]; intros. {
    now apply length_zero_iff_nil in Hla; subst la; left.
  }
  cbn.
  destruct la as [| a]; [ easy | ].
  cbn in Hla; apply Nat.succ_inj in Hla.
  apply in_flat_map.
  exists a.
  specialize (Hnth 0 (Nat.lt_0_succ _)) as H1; cbn in H1.
  split; [ easy | ].
  apply in_map_iff.
  exists la.
  split; [ easy | ].
  apply IHll; [ easy | ].
  intros i Hi.
  specialize (Hnth (S i)) as H2.
  cbn in H2.
  apply Nat.succ_lt_mono in Hi.
  now specialize (H2 Hi).
}
Qed.

(* end cart_prod *)

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

Theorem NoDup_butn : ∀ A k (la : list A), NoDup la → NoDup (butn k la).
Proof.
intros * Hnd.
apply NoDup_app_iff.
split. {
  rewrite <- (firstn_skipn k) in Hnd.
  now apply NoDup_app_iff in Hnd.
}
split. {
  rewrite <- (firstn_skipn (S k)) in Hnd.
  now apply NoDup_app_iff in Hnd.
}
intros i Hif.
rewrite <- (firstn_skipn (S k)) in Hnd.
apply NoDup_app_iff in Hnd.
destruct Hnd as (H1 & H2 & H3).
apply H3.
clear - Hif.
revert la Hif.
induction k; intros; [ easy | ].
destruct la as [| a]; [ easy | ].
rewrite firstn_cons in Hif |-*.
destruct Hif as [Hif| Hif]; [ now left | right ].
now apply IHk.
Qed.

Theorem NoDup_concat_if : ∀ A (ll : list (list A)),
  (∀ l, l ∈ ll → NoDup l)
  → (∀ i j, i ≠ j → ∀ a, a ∈ nth i ll [] → a ∉ nth j ll [])
  → NoDup (concat ll).
Proof.
intros * Hnd Hll.
induction ll as [| l]; [ constructor | cbn ].
apply NoDup_app_iff.
split; [ now apply Hnd; left | ].
split. {
  apply IHll. {
    intros l1 Hl1.
    now apply Hnd; right.
  }
  intros i j Hij a Ha.
  specialize (Hll (S i) (S j)).
  apply Hll; [ now intros H; injection H | easy ].
}
clear - Hnd Hll.
intros i Hi Hll'.
revert i l Hnd Hi Hll Hll'.
induction ll as [| l1]; intros; [ easy | ].
cbn in Hll'.
apply in_app_or in Hll'.
destruct Hll' as [Hll'| Hll']. 2: {
  apply IHll with (i := i) (l := l); [ | easy | | easy ]. {
    intros l2 Hl2.
    apply Hnd.
    destruct Hl2 as [Hl2| Hl2]; [ now left | now right; right ].
  }
  intros u v Huv a Ha.
  destruct u. {
    cbn in Ha.
    destruct v; [ easy | cbn ].
    specialize (Hll 0 (S (S v))) as H1.
    assert (H : 0 ≠ S (S v)) by easy.
    now specialize (H1 H a Ha).
  }
  cbn in Ha.
  destruct v. {
    specialize (Hll (S (S u)) 0) as H1.
    assert (H : S (S u) ≠ 0) by easy.
    now specialize (H1 H a Ha).
  }
  cbn.
  apply Nat.succ_inj_wd_neg in Huv.
  specialize (Hll _ _ Huv).
  now apply Hll.
}
now specialize (Hll 0 1 (Nat.neq_0_succ _) _ Hi).
Qed.

(* "to_radix_loop u r i" is the last u digits of i in base r (in reverse) *)
Fixpoint to_radix_loop it r i :=
  match it with
  | 0 => []
  | S it' => i mod r :: to_radix_loop it' r (i / r)
  end.

(* conversion natural into radix r as a list of digits; i must be
   less than r^r; always return r digits; e.g. radix 10 37 =
   7; 3; 0 ... (eight 0s) *)
Definition to_radix r i := to_radix_loop r r i.

Definition to_radix_list r := map (to_radix r) (seq 0 (r ^ r)).

Fixpoint to_radix_inv r l :=
  match l with
  | [] => 0
  | d :: l' => d + r * to_radix_inv r l'
  end.

Theorem to_radix_loop_ub : ∀ it n k i,
  n ≠ 0 → nth i (to_radix_loop it n k) 0 < n.
Proof.
intros * Hnz.
revert n k i Hnz.
induction it; intros; [ destruct i; cbn; flia Hnz | cbn ].
destruct i; [ now apply Nat.mod_upper_bound | ].
now apply IHit.
Qed.

Theorem to_radix_ub : ∀ n k i, n ≠ 0 → nth i (to_radix n k) 0 < n.
Proof.
intros * Hnz.
now apply to_radix_loop_ub.
Qed.

Theorem to_radix_inv_to_radix_loop : ∀ it n k,
  to_radix_inv n (to_radix_loop it n k) = k mod (n ^ it).
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  destruct it; [ easy | apply Nat.add_0_r ].
}
revert n k Hnz.
induction it; intros; [ easy | cbn ].
rewrite IHit; [ | easy ].
symmetry.
apply Nat.mod_mul_r; [ easy | ].
now apply Nat.pow_nonzero.
Qed.

Theorem to_radix_loop_to_radix_inv : ∀ l d n it,
  length l + d = n
  → (∀ i, i ∈ l → i < n)
  → n ≤ it + d
  → to_radix_loop it n (to_radix_inv n l) = l ++ repeat 0 (it + d - n).
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
  rewrite Nat.mul_comm, Nat.mod_add; [ | now subst n ].
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
unfold to_radix.
rewrite to_radix_inv_to_radix_loop.
now apply Nat.mod_small.
Qed.

Theorem to_radix_to_radix_inv : ∀ n l,
  length l = n
  → (∀ i, i ∈ l → i < n)
  → to_radix n (to_radix_inv n l) = l.
Proof.
intros * Hlen Hl.
unfold to_radix.
specialize to_radix_loop_to_radix_inv as H1.
specialize (H1 l 0 n n).
do 2 rewrite Nat.add_0_r in H1.
specialize (H1 Hlen Hl (le_refl _)).
now rewrite Nat.sub_diag, app_nil_r in H1.
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
unfold to_radix.
apply to_radix_loop_length.
Qed.

Theorem to_radix_inv_ub : ∀ n l,
  n ≠ 0
  → (∀ i, i < length l → nth i l 0 < n)
  → to_radix_inv n l < n ^ length l.
Proof.
intros * Hnz Hl.
revert n Hnz Hl.
induction l as [| a]; intros; cbn; [ easy | ].
apply Nat.neq_0_lt_0 in Hnz.
specialize (Hl 0 (Nat.lt_0_succ _)) as H1; cbn in H1.
apply Nat.neq_0_lt_0 in Hnz.
specialize (IHl n Hnz) as H2.
assert (H : ∀ i, i < length l → nth i l 0 < n). {
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

Definition abs_diff u v := if v <? u then u - v else v - u.

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

Arguments iter_list {A B}%type l%list f%function : simpl never.
Arguments iter_shift {T}%type s [b k]%nat.
Arguments "<?" : simpl never.

Global Hint Resolve Nat_mod_fact_upper_bound : core.
