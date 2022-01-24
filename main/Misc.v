(* Theorems of general usage, which could be (or not) in Coq library *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Psatz Sorted Permutation Decidable.
Import List List.ListNotations.
Arguments length {A}.

Global Hint Resolve Nat.le_0_l : core.
Global Hint Resolve Nat.lt_0_succ : core.
Global Hint Resolve Nat.lt_succ_diag_r : core.

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

Notation "x ≠? y" := (negb (Nat.eqb x y)) (at level 70) : nat_scope.

Theorem List_fold_left_map :
  ∀ A B C (f : A → B → A) (g : C → B) (l : list C) a,
  fold_left f (map g l) a = fold_left (λ c b, f c (g b)) l a.
Proof.
intros.
revert a.
induction l as [| c]; intros; [ easy | apply IHl ].
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

Theorem fold_iter_list : ∀ {A B} (f : A → B → A) l d,
  fold_left f l d = iter_list l f d.
Proof. easy. Qed.

Theorem fold_iter_seq : ∀ A b e f (d : A),
  iter_list (seq b (S e - b)) f d = iter_seq b e f d.
Proof. easy. Qed.

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

(*
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
*)

Theorem fold_right_max_ge : ∀ m l, m ≤ fold_right max m l.
Proof.
intros.
induction l as [| a]; [ easy | cbn ].
etransitivity; [ apply IHl | ].
apply Nat.le_max_r.
Qed.

(* *)

Theorem Nat_sub_sub_swap : ∀ a b c, a - b - c = a - c - b.
Proof.
intros.
rewrite <- Nat.sub_add_distr.
rewrite Nat.add_comm.
now rewrite Nat.sub_add_distr.
Qed.

Theorem Nat_sub_succ_1 : ∀ n, S n - 1 = n.
Proof. now intros; rewrite Nat.sub_succ, Nat.sub_0_r. Qed.

Theorem Nat_mod_add_l_mul_r : ∀ a b c,
  b ≠ 0 → (c * b + a) mod b = a mod b.
Proof.
intros * Hbz.
rewrite Nat.add_comm.
now apply Nat.mod_add.
Qed.

Theorem Nat_fact_succ : ∀ n, fact (S n) = S n * fact n.
Proof. easy. Qed.

Notation "a ≡ b 'mod' c" := (a mod c = b mod c) (at level 70, b at level 36).
Notation "a ≢ b 'mod' c" := (a mod c ≠ b mod c) (at level 70, b at level 36).

Theorem List_hd_nth_0 {A} : ∀ l (d : A), hd d l = nth 0 l d.
Proof. intros; now destruct l. Qed.

Theorem List_last_nth {A} : ∀ l (d : A), last l d = nth (length l - 1) l d.
Proof.
intros.
induction l using rev_ind; [ easy | ].
rewrite app_length; cbn.
rewrite Nat.add_sub.
rewrite last_last.
rewrite app_nth2; [ | now unfold ge ].
now rewrite Nat.sub_diag.
Qed.

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

Theorem List_in_firstn : ∀ A (a : A) k la, a ∈ firstn k la → a ∈ la.
Proof.
intros * Haf.
revert la Haf.
induction k; intros; [ easy | ].
destruct la as [| b]; [ easy | ].
cbn in Haf.
destruct Haf; [ now left | right ].
now apply IHk.
Qed.

Theorem List_in_skipn : ∀ A (a : A) k la, a ∈ skipn k la → a ∈ la.
Proof.
intros * Has.
revert la Has.
induction k; intros; [ easy | ].
destruct la as [| b]; [ easy | ].
cbn in Has.
right.
now apply IHk.
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

Theorem List_length_cons : ∀ A (a : A) la, length (a :: la) = S (length la).
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

(* end map2 *)

(* rank: rank of the first element satisfying a predicate *)
(* like "find" but returning the rank, not the element itself *)

Fixpoint List_rank_loop i A (f : A → bool) (l : list A) : option nat :=
  match l with
  | [] => None
  | x :: tl => if f x then Some i else List_rank_loop (S i) f tl
end.

Definition List_rank := List_rank_loop 0.

Theorem List_rank_loop_interv : ∀ A f (l : list A) i j,
  List_rank_loop i f l = Some j
  → i ≤ j < i + length l.
Proof.
intros * Hi.
revert i Hi.
induction l as [| a]; intros; [ easy | ].
cbn in Hi.
remember (f a) as b eqn:Hb; symmetry in Hb.
destruct b. {
  injection Hi; clear Hi; intros; subst i.
  cbn; flia.
}
specialize (IHl (S i) Hi).
cbn; flia IHl.
Qed.

Theorem List_rank_loop_Some : ∀ A d f (l : list A) i j,
  List_rank_loop i f l = Some j
  → j < i + length l ∧
    (∀ k, i ≤ k < j → f (nth (k - i) l d) = false) ∧
    f (nth (j - i) l d) = true.
Proof.
intros * Hi.
split. {
  remember (j - i) as k eqn:Hk.
  replace j with (i + k) in Hi |-*. 2: {
    specialize (List_rank_loop_interv f l i Hi) as H1.
    flia Hk H1.
  }
  apply Nat.add_lt_mono_l.
  clear j Hk.
  revert i l Hi.
  induction k; intros. {
    destruct l; [ easy | cbn; flia ].
  }
  destruct l as [| a]; [ easy | ].
  cbn in Hi |-*.
  remember (f a) as b eqn:Hb; symmetry in Hb.
  destruct b. {
    injection Hi; clear Hi; intros Hi; flia Hi.
  }
  rewrite <- Nat.add_succ_comm in Hi.
  apply -> Nat.succ_lt_mono.
  now apply (IHk (S i)).
}
split. {
  intros p Hp.
  remember (p - i) as k eqn:Hk.
  replace p with (i + k) in Hp by flia Hp Hk.
  destruct Hp as (_, Hp).
  clear p Hk.
  revert i l Hi Hp.
  induction k; intros. {
    destruct l as [| a]; [ easy | ].
    cbn in Hi |-*.
    destruct (f a); [ injection Hi; intros; subst i; flia Hp | easy ].
  }
  destruct l as [| a]; [ easy | ].
  cbn in Hi |-*.
  rewrite <- Nat.add_succ_comm in Hp.
  remember (f a) as b eqn:Hb; symmetry in Hb.
  destruct b. {
    injection Hi; clear Hi; intros; subst j; flia Hp.
  }
  now apply IHk with (i := S i).
} {
  remember (j - i) as k eqn:Hk.
  replace j with (i + k) in Hi. 2: {
    specialize (List_rank_loop_interv f l i Hi) as H1.
    flia Hk H1.
  }
  clear j Hk.
  revert i l Hi.
  induction k; intros. {
    rewrite Nat.add_0_r in Hi.
    revert i Hi.
    induction l as [| a]; intros; [ easy | ].
    cbn in Hi |-*.
    remember (f a) as b eqn:Hb; symmetry in Hb.
    destruct b; [ easy | exfalso ].
    specialize (List_rank_loop_interv f l (S i) Hi) as H1.
    flia H1.
  }
  destruct l as [| a]; [ easy | ].
  cbn in Hi |-*.
  remember (f a) as b eqn:Hb; symmetry in Hb.
  destruct b. {
    injection Hi; clear Hi; intros Hi; flia Hi.
  }
  rewrite <- Nat.add_succ_comm in Hi.
  now apply (IHk (S i)).
}
Qed.

Theorem List_rank_Some : ∀ A d f (l : list A) i,
  List_rank f l = Some i
  → i < length l ∧
    (∀ j, j < i → f (nth j l d) = false) ∧
    f (nth i l d) = true.
Proof.
intros * Hi.
apply List_rank_loop_Some with (d := d) in Hi.
rewrite Nat.sub_0_r in Hi.
destruct Hi as (Hil & Hk & Hi).
split; [ easy | ].
split; [ | easy ].
intros j Hj.
specialize (Hk j).
assert (H : 0 ≤ j < i) by flia Hj.
specialize (Hk H); clear H.
now rewrite Nat.sub_0_r in Hk.
Qed.

Theorem List_rank_loop_None : ∀ A (d : A) f l i,
  List_rank_loop i f l = None
  → ∀ j, i ≤ j < i + length l
  → f (nth (j - i) l d) = false.
Proof.
intros * Hi p Hp.
remember (p - i) as k eqn:Hk.
replace p with (i + k) in Hp by flia Hp Hk.
destruct Hp as (_, Hp).
apply Nat.add_lt_mono_l in Hp.
clear p Hk.
revert i l Hi Hp.
induction k; intros. {
  destruct l as [| a]; [ easy | ].
  cbn in Hi |-*.
  now destruct (f a).
}
destruct l as [| a]; [ easy | ].
cbn in Hi, Hp |-*.
apply Nat.succ_lt_mono in Hp.
remember (f a) as b eqn:Hb; symmetry in Hb.
destruct b; [ easy | ].
now apply IHk with (i := S i).
Qed.

Theorem List_rank_None : ∀ A d f (l : list A),
  List_rank f l = None
  → ∀ j, j < length l
  → f (nth j l d) = false.
Proof.
intros * Hi j Hj.
specialize (List_rank_loop_None d f l Hi) as H1.
specialize (H1 j).
rewrite Nat.sub_0_r in H1.
apply H1.
split; [ flia | easy ].
Qed.

Theorem List_rank_loop_Some_lt : ∀ A f (l : list A) i j,
  List_rank_loop i f l = Some j → j < i + length l.
Proof.
intros * Hij.
revert i Hij.
induction l as [| a]; intros; [ easy | ].
cbn in Hij, IHl |-*.
remember (f a) as b eqn:Hb; symmetry in Hb.
destruct b. {
  injection Hij; clear Hij; intros; subst j; flia.
}
rewrite <- Nat.add_succ_comm.
now apply IHl.
Qed.

Theorem List_rank_Some_lt : ∀ A f (l : list A) i,
  List_rank f l = Some i → i < length l.
Proof.
intros * Hi.
now apply List_rank_loop_Some_lt in Hi.
Qed.

Theorem find_vs_rank : ∀ A f l (d : A),
  find f l = option_map (λ i, nth i l d) (List_rank f l).
Proof.
intros.
remember (List_rank f l) as n eqn:Hn; symmetry in Hn.
destruct n as [n| ]; cbn. {
  apply (List_rank_Some d) in Hn.
  destruct Hn as (Hnl & Hfn & Hn).
  revert n Hnl Hfn Hn.
  induction l as [| a]; intros; [ easy | cbn ].
  remember (f a) as b eqn:Hb; symmetry in Hb.
  destruct b. {
    destruct n; [ easy | f_equal ].
    specialize (Hfn 0 (Nat.lt_0_succ _)).
    cbn in Hfn; congruence.
  }
  destruct n; [ cbn in Hn; congruence | ].
  cbn in Hnl, Hn.
  apply Nat.succ_lt_mono in Hnl.
  apply IHl; [ easy | | easy ].
  intros i Hi.
  apply (Hfn (S i)).
  now apply Nat.succ_lt_mono in Hi.
} {
  specialize (List_rank_None d _ _ Hn) as Hfn.
  clear Hn.
  induction l as [| a]; [ easy | cbn ].
  remember (f a) as b eqn:Hb; symmetry in Hb.
  destruct b. {
    specialize (Hfn 0 (Nat.lt_0_succ _)).
    cbn in Hfn; congruence.
  }
  apply IHl.
  intros i Hi.
  apply (Hfn (S i)).
  now apply Nat.succ_lt_mono in Hi.
}
Qed.

(* end List_rank *)

(* conversions if ...? into if ..._dec *)

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
unfold Nat.b2n; rewrite if_ltb_lt_dec.
destruct (lt_dec n (length l)) as [Hnl| Hnl]. 2: {
  apply Nat.nlt_ge in Hnl; rewrite Nat.sub_0_r.
  now rewrite butn_out.
}
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

Theorem map_butn_out : ∀ A (ll : list (list A)) i,
  (∀ l, l ∈ ll → length l ≤ i)
  → map (butn i) ll = ll.
Proof.
intros * Hi.
revert i Hi.
induction ll as [| la]; intros; [ easy | cbn ].
rewrite IHll. 2: {
  intros l Hl.
  now apply Hi; right.
}
f_equal.
specialize (Hi la (or_introl eq_refl)).
unfold butn.
rewrite firstn_all2; [ | easy ].
rewrite skipn_all2; [ | flia Hi ].
apply app_nil_r.
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
rewrite if_ltb_lt_dec.
destruct (lt_dec (S n) (S len)) as [Hn| Hn]. {
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
  apply Nat.nlt_ge in Hn.
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

Theorem butn_butn : ∀ A i j (la : list A),
  j ≤ i → butn i (butn j la) = butn j (butn (i + 1) la).
Proof.
intros * Hji.
unfold butn.
do 2 rewrite firstn_app.
do 2 rewrite <- app_assoc.
do 2 rewrite firstn_firstn.
rewrite Nat.min_r; [ | flia Hji ].
rewrite Nat.min_l; [ | flia Hji ].
f_equal.
do 2 rewrite skipn_app.
do 2 rewrite firstn_length.
destruct (le_dec (i + 1) (length la)) as [Hi1la| Hi1la]. 2: {
  apply Nat.nle_gt in Hi1la.
  rewrite (Nat.min_r (i + 1)); [ | flia Hi1la ].
  destruct (lt_dec j (length la)) as [Hjla| Hjla]. 2: {
    apply Nat.nlt_ge in Hjla.
    rewrite Nat.min_r; [ | easy ].
    rewrite skipn_all2; [ | flia Hjla ].
    rewrite firstn_nil, app_nil_l.
    rewrite firstn_all2; [ | easy ].
    rewrite firstn_all2. 2: {
      rewrite skipn_length.
      rewrite (proj2 (Nat.sub_0_le _ _)); [ flia | flia Hi1la ].
    }
    rewrite skipn_all2; [ | flia Hi1la ].
    rewrite app_nil_l.
    rewrite skipn_nil.
    rewrite skipn_all2; [ | flia Hi1la ].
    rewrite skipn_nil.
    rewrite app_nil_l, app_nil_r.
    rewrite skipn_all2; [ easy | ].
    rewrite firstn_length.
    rewrite Nat.min_r; [ | flia Hi1la ].
    flia Hjla.
  }
  rewrite Nat.min_l; [ | flia Hjla ].
  replace (j - length la) with 0 by flia Hjla.
  rewrite firstn_O, app_nil_l.
  rewrite skipn_firstn_comm.
  replace (j - S i) with 0 by flia Hi1la Hjla.
  rewrite firstn_O, app_nil_l.
  replace (S j - length la) with 0 by flia Hjla.
  rewrite skipn_O.
  rewrite firstn_skipn_comm.
  replace (S j + (i - j)) with (i + 1) by flia Hi1la Hjla.
  f_equal.
  rewrite List_skipn_skipn.
  f_equal.
  flia Hi1la Hjla.
}
rewrite Nat.min_l; [ | flia Hji Hi1la ].
rewrite Nat.min_l; [ | flia Hi1la ].
rewrite firstn_skipn_comm.
replace (S j + (i - j)) with (i + 1) by flia Hji.
replace (j - (i + 1)) with 0 by flia Hji.
rewrite firstn_O, app_nil_l.
f_equal.
rewrite skipn_firstn_comm.
replace (j - S i) with 0 by flia Hji.
rewrite firstn_O, app_nil_l.
replace (S j - (i + 1)) with 0 by flia Hji.
rewrite skipn_O.
rewrite List_skipn_skipn.
f_equal; flia Hji.
Qed.

(* end butn *)

(* insert in a list (reverse of butn) *)

Definition insert_at A k (la : list A) e :=
  firstn k la ++ e :: skipn k la.

(* end insert_at *)

(* replace in a list *)

Definition replace_at {A} k (la : list A) e :=
  firstn k la ++ e :: skipn (S k) la.

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

(* list_eqb *)

Fixpoint list_eqb A (eqb : A → A → bool) la lb :=
  match la with
  | [] =>
      match lb with
      | [] => true
      | b :: lb' => false
      end
  | a :: la' =>
      match lb with
      | [] => false
      | b :: lb' => if eqb a b then list_eqb eqb la' lb' else false
      end
  end.

Theorem list_eqb_eq : ∀ la lb, list_eqb Nat.eqb la lb = true → la = lb.
Proof.
intros * Hab.
revert lb Hab.
induction la as [| a]; intros; [ now destruct lb | cbn ].
destruct lb as [| b]; [ easy | cbn in Hab ].
rewrite if_eqb_eq_dec in Hab.
destruct (Nat.eq_dec a b) as [H1| H1]; [ | easy ].
destruct H1; f_equal.
now apply IHla.
Qed.

Theorem list_eqb_neq : ∀ la lb, list_eqb Nat.eqb la lb = false → la ≠ lb.
Proof.
intros * Hab H; subst lb.
induction la as [| a]; [ easy | cbn in Hab ].
rewrite Nat.eqb_refl in Hab.
congruence.
Qed.

(* end list_eqb *)

Definition unsome A (d : A) o :=
  match o with
  | Some x => x
  | None => d
  end.

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

Theorem List_eq_rev_nil {A} : ∀ (l : list A), rev l = [] → l = [].
Proof.
intros * Hl.
destruct l as [| a]; [ easy | cbn in Hl ].
now apply app_eq_nil in Hl.
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

Theorem NoDup_firstn : ∀ A k (la : list A), NoDup la → NoDup (firstn k la).
Proof.
intros * Hnd.
revert la Hnd.
induction k; intros; [ constructor | cbn ].
destruct la as [| a]; [ constructor | cbn ].
apply NoDup_cons_iff.
apply NoDup_cons_iff in Hnd.
destruct Hnd as (Ha & Hnd).
split. {
  intros Haf; apply Ha; clear Ha.
  now apply List_in_firstn in Haf.
}
now apply IHk.
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

(* bsort *)

Fixpoint bsort_insert {A} (ord : A → A → bool) a lsorted :=
  match lsorted with
  | [] => [a]
  | b :: l =>
      if ord a b then a :: lsorted
      else b :: bsort_insert ord a l
  end.

Fixpoint bsort_loop {A} (ord : A → A → bool) lsorted l :=
  match l with
  | [] => lsorted
  | a :: l' => bsort_loop ord (bsort_insert ord a lsorted) l'
  end.

Definition bsort {A} (ord : A → A → bool) := bsort_loop ord [].

(* bsort length *)

Theorem bsort_insert_length : ∀ A ord (a : A) lsorted,
  length (bsort_insert ord a lsorted) = S (length lsorted).
Proof.
intros.
induction lsorted as [| b]; intros; [ easy | cbn ].
destruct (ord a b); [ easy | ].
cbn; f_equal.
apply IHlsorted.
Qed.

Theorem bsort_loop_length : ∀ A ord (lsorted l : list A),
  length (bsort_loop ord lsorted l) = length lsorted + length l.
Proof.
intros.
revert lsorted.
induction l as [| a]; intros; [ now cbn; rewrite Nat.add_0_r | cbn ].
rewrite IHl, <- Nat.add_succ_comm; f_equal.
apply bsort_insert_length.
Qed.

Theorem bsort_length : ∀ A ord (l : list A), length (bsort ord l) = length l.
Proof.
intros.
apply bsort_loop_length.
Qed.

(* in bsort *)

Theorem in_bsort_insert : ∀ A (ord : A → A → bool) a b lsorted,
  a ∈ bsort_insert ord b lsorted
  → a ∈ b :: lsorted.
Proof.
intros * Ha.
revert a b Ha.
induction lsorted as [| c]; intros. {
  cbn in Ha.
  destruct Ha as [Ha| Ha]; [ now left | easy ].
}
cbn in Ha.
destruct (ord b c); [ easy | ].
cbn in Ha.
destruct Ha as [Ha| Ha]; [ now right; left | ].
apply IHlsorted in Ha.
destruct Ha as [Ha| Ha]; [ now left | now right; right ].
Qed.

Theorem in_bsort_loop : ∀ A (ord : A → A → bool) a lsorted l,
  a ∈ bsort_loop ord lsorted l
  → a ∈ lsorted ∨ a ∈ l.
Proof.
intros * Ha.
revert a lsorted Ha.
induction l as [| b]; intros; [ now left | ].
cbn in Ha.
apply IHl in Ha.
destruct Ha as [Ha| Ha]. {
  apply in_bsort_insert in Ha.
  destruct Ha as [Ha| Ha]; [ now right; left | now left ].
} {
  now right; right.
}
Qed.

Theorem in_bsort : ∀ A (ord : A → A → bool) a l, a ∈ bsort ord l → a ∈ l.
Proof.
intros * Ha.
apply in_bsort_loop in Ha.
now destruct Ha.
Qed.

(* bsort_rank: like bsort but return the rank of what have been
   sorted *)

Fixpoint bsort_rank_insert {A B} (ord : A → A → bool) (f : B → A) ia lrank :=
  match lrank with
  | [] => [ia]
  | ib :: l =>
      if ord (f ia) (f ib) then ia :: lrank
      else ib :: bsort_rank_insert ord f ia l
  end.

Fixpoint bsort_rank_loop {A} (ord : A → A → bool) f ia lrank (l : list A) :=
  match l with
  | [] => lrank
  | _ :: l' => bsort_rank_loop ord f (S ia) (bsort_rank_insert ord f ia lrank) l'
  end.

Definition bsort_rank {A} (ord : A → A → bool) l :=
  match l with
  | [] => []
  | d :: _ => bsort_rank_loop ord (λ i, nth i l d) 0 [] l
  end.

(*
Compute (let l := [2;7;1] in bsort_rank Nat.leb l).
Compute (let l := [5;2;2;7;0] in bsort_rank Nat.leb l).
Compute (let l := [5;2;2;7;0] in bsort_rank Nat.ltb l).
*)

Theorem length_bsort_rank_insert : ∀ A B ord (f : B → A) ia lrank,
  length (bsort_rank_insert ord f ia lrank) = S (length lrank).
Proof.
intros.
induction lrank as [| ib]; [ easy | cbn ].
destruct (ord (f ia) (f ib)); [ easy | cbn ].
now rewrite IHlrank.
Qed.

Theorem bsort_insert_bsort_rank_insert : ∀ A B ord ia (f : B → A) lrank,
  bsort_insert ord (f ia) (map f lrank) =
  map f (bsort_rank_insert ord f ia lrank).
Proof.
intros.
induction lrank as [| ib]; [ easy | cbn ].
destruct (ord (f ia) (f ib)); [ easy | ].
cbn; f_equal.
apply IHlrank.
Qed.

Theorem bsort_loop_bsort_rank_loop : ∀ A ord d (f : nat → A) lrank l,
  (∀ i, i < length l → f (length lrank + i) = nth i l d)
  → bsort_loop ord (map f lrank) l =
    map f (bsort_rank_loop ord f (length lrank) lrank l).
Proof.
intros * Hia.
revert lrank Hia.
induction l as [| a]; intros; [ easy | cbn ].
specialize (Hia 0 (Nat.lt_0_succ _)) as H1.
cbn in H1; rewrite Nat.add_0_r in H1.
rewrite <- H1.
rewrite bsort_insert_bsort_rank_insert.
rewrite IHl; [ now rewrite length_bsort_rank_insert | ].
intros i Hi.
rewrite length_bsort_rank_insert.
apply Nat.succ_lt_mono in Hi.
specialize (Hia (S i) Hi) as H2.
now rewrite <- Nat.add_succ_comm in H2.
Qed.

Theorem bsort_rank_insert_nth_indep : ∀ A ord (d d' : A) ia lrank l_ini,
  ia < length l_ini
  → (∀ i, i ∈ lrank → i < length l_ini)
  → bsort_rank_insert ord (λ i : nat, nth i l_ini d) ia lrank =
    bsort_rank_insert ord (λ i : nat, nth i l_ini d') ia lrank.
Proof.
intros * Hia Hini.
induction lrank as [| ib]; intros; [ easy | ].
cbn - [ nth ].
specialize (Hini ib (or_introl eq_refl)) as Hib.
rewrite (nth_indep _ _ d' Hia).
rewrite (nth_indep _ _ d' Hib).
remember (ord (nth ia l_ini d') (nth ib l_ini d')) as x eqn:Hx.
symmetry in Hx.
destruct x; [ easy | ].
f_equal.
apply IHlrank.
intros i Hi.
apply Hini.
now right.
Qed.

Theorem bsort_rank_loop_nth_indep : ∀ A ord (d d' : A) ia lrank l_ini l,
  ia < length l_ini
  → (∀ i, i ∈ lrank → i < length l_ini)
  → bsort_rank_loop ord (λ i, nth i l_ini d) ia lrank l =
    bsort_rank_loop ord (λ i, nth i l_ini d') ia lrank l.
Proof.
intros * Hia Hini.
clear Hia.
revert ia lrank Hini.
induction l as [| b]; intros; [ easy | ].
cbn - [ nth ].
rewrite bsort_rank_insert_nth_indep with (d' := d'); [ | | easy ].
...
rewrite bsort_rank_insert_nth_indep with (d' := d'); [ | easy | easy ].
destruct (Nat.eq_dec (S ia) (length l_ini)) as [Hil| Hil]. {
  rewrite Hil.
  destruct l as [| c]; [ easy | ].
  cbn.
...
destruct (Nat.eq_dec (S ia) (length l_ini)) as [Hil| Hil]. 2: {
  apply IHl; [ flia Hil Hia | ].
  intros i Hi.
...
}
...
  apply Hini.
Search (_ ∈ bsort_rank_insert _ _ _ _).
...
  rewrite bsort_rank_insert_nth_indep with (d' := d').
rewrite IHl.
...
f_equal.
apply bsort_rank_insert_nth_indep.
...
  intros i Hi.
  apply Hn.
  destruct Hi as [Hi| Hi]. 2: {
...
...

Theorem bsort_rank_loop_nth_indep : ∀ A ord (d d' : A) a ia lrank l,
  bsort_rank_loop ord (λ i, nth i (a :: l) d) ia lrank l =
  bsort_rank_loop ord (λ i, nth i (a :: l) d') ia lrank l.
Proof.
intros.
induction l as [| b]; [ easy | ].
cbn - [ nth ].
...

Theorem bsort_bsort_rank : ∀ A (ord : A → A → bool) (d : A) l,
  bsort ord l = map (λ i, nth i l d) (bsort_rank ord l).
Proof.
intros.
destruct l as [| d' l]; [ easy | ].
cbn - [ nth ].
replace [d'] with (map (λ i, nth i (d' :: l) d) [0]) by easy.
rewrite bsort_loop_bsort_rank_loop with (d := d').
cbn - [ nth ].
f_equal.
...
apply bsort_rank_loop_nth_indep.
...
  ============================
  map (λ i : nat, nth i (d' :: l) d)
    (bsort_rank_loop ord (λ i : nat, nth i (d' :: l) d) 1 [0] l) =
  map (λ i : nat, nth i (d' :: l) d)
    (bsort_rank_loop ord (λ i : nat, nth i (d' :: l) d') 1 [0] l)
...
rewrite bsort_loop_bsort_rank_loop with (d := d'); [ | ].

...
intros.
destruct l as [| d' l]; [ easy | ].
cbn - [ nth ].
rewrite map_ext_in with (g := λ i, nth i (d' :: l) d'). 2: {
  intros a Ha.
  apply nth_indep.
...
(* glop ci-dessous va pas... *)
Theorem glop : ∀ A ord f ia ib lrank (l : list A),
  (∀ i, i ∈ lrank → i < length lrank)
  → ib ∈ bsort_rank_loop ord f ia lrank l
  → ib < length lrank + length l.
Proof.
intros * Hil Hib.
revert ia ib lrank Hil Hib.
induction l as [| a]; intros; cbn in Hib. {
  rewrite Nat.add_0_r.
  apply Hil, Hib.
}
apply IHl in Hib. 2: {
  intros i Hi.
  rewrite length_bsort_rank_insert.
Print bsort_rank_insert.
Theorem glop : ∀ A B ord (f : B → A) ia ib lrank,
  ib ∈ bsort_rank_insert ord f ia lrank
  → ib < length lrank.
Proof.
...
...
  destruct l as [| b]; [ | cbn ].
...
remember (d' :: l') as l eqn:Hl; clear l' Hl.
...
rewrite map_ext_in with (g := λ i, nth i l d'). 2: {
  intros a Ha.
  apply nth_indep.
  destruct l as [| b]; [ easy | cbn ].
  cbn - [ nth ] in Ha.
  set (f := λ i, nth i (b :: l) b) in Ha.
  cbn in Ha; subst f.
  induction l as [| c]; [ cbn in Ha |-*; flia Ha | ].
  cbn - [ nth ] in IHl.
...
Search (_ ∈ bsort_rank _ _).
...
set (f := λ i, nth i l d).
destruct l as [| a1]; [ easy | ].
...
Theorem bsort_loop_bsort_rank_loop : ∀ A ord (d d' : A) lrank l_ini (l : list A),
  bsort ord (map (λ i, nth i l_ini d) lrank) = map (λ i, nth i l_ini d) lrank
  → l = skipn (length lrank) l_ini
  → bsort_loop ord (map (λ i, nth i l_ini d) lrank) l =
    map (λ i, nth i l_ini d)
      (bsort_rank_loop ord (λ i, nth i l d') (length lrank) lrank l).
Proof.
intros * Hs Hli.
set (f := λ i, nth i l_ini d) in Hs |-*.
revert lrank Hs Hli.
induction l as [| a]; intros; [ easy | ].
cbn - [ nth ].
assert (Ha : a = nth (length lrank) l_ini d). {
  clear - Hli.
  revert a l_ini Hli.
  induction lrank as [| ib]; intros; [ now cbn in Hli; rewrite <- Hli | ].
  cbn in Hli.
  destruct l_ini as [| b]; [ easy | cbn ].
  now apply IHlrank.
}
assert (Ha' : a = f (length lrank)) by easy.
clear Ha; rename Ha' into Ha.
assert (Hl : l = skipn (S (length lrank)) l_ini). {
  clear - Hli.
  revert lrank l Hli.
  induction l_ini as [| b]; intros; [ now rewrite skipn_nil in Hli | ].
  destruct lrank as [| ia]. {
    now injection Hli; clear Hli; intros; subst b l.
  }
  cbn in Hli.
  rewrite skipn_cons.
  rewrite List_length_cons.
  now apply IHl_ini.
}
clear Hli.
rewrite Ha at 1.
rewrite bsort_insert_bsort_rank_insert.
rewrite IHl; [ | | now rewrite length_bsort_rank_insert ]. 2: {
  remember (map f (bsort_rank_insert _ _ _ _)) as lsorted eqn:Hls.
  clear a Ha.
(**)
  subst lsorted.
(**)
  clear - Hs.
  induction lrank as [| ia]; [ easy | ].
  cbn in Hs |-*.
  remember (ord (f (S (length lrank))) (f ia)) as x eqn:Hx.
  symmetry in Hx.
  destruct x; cbn.
...
  destruct lrank as [| ia1]; [ easy | cbn ].
  remember (ord (f (S (length lrank))) (f ia1)) as x eqn:Hx.
  symmetry in Hx.
  destruct x; cbn. {
    remember (ord (f ia1) (f (S (length lrank)))) as y eqn:Hy.
    symmetry in Hy.
    destruct y; cbn. 2: {
      remember (map f lrank) as lsorted eqn:Hlsorted.
      remember (length lrank) as len eqn:Hlen.
      clear lrank Hs Hl Hlen Hlsorted.
      induction lsorted as [| a la]; [ easy | cbn ].
      remember (ord a (f (S len))) as z eqn:Hz.
      symmetry in Hz.
      destruct z. {
        destruct la as [| b].
...
  destruct lrank as [| ia2]. {
    cbn.
    remember (ord (f 1) (f ia1)) as x eqn:Hx.
    symmetry in Hx.
    destruct x; cbn; [ | now rewrite Hx ].
    remember (ord (f ia1) (f 1)) as y eqn:Hy.
    symmetry in Hy.
    destruct y; [ | easy ].
(* ord must be antisymmetric *)
    admit.
  }
  cbn.
}
...
Print bsort_rank_insert.
Theorem glop : ∀ A ord (d : A) ia lrank l,
  length lrank ≤ ia
  → bsort ord (map (λ i, nth i l d) lrank) = map (λ i, nth i l d) lrank
  → bsort ord (map (λ i, nth i l d)
      (bsort_rank_insert ord (λ i, nth i l d) ia lrank)) =
    map (λ i, nth i l d) (bsort_rank_insert ord (λ i, nth i l d) ia lrank).
Proof.
intros * Hia Hs.
revert d ia l Hia Hs.
induction lrank as [| ib]; intros; [ easy | cbn ].
remember (ord (nth ia l d) (nth ib l d)) as x eqn:Hx.
symmetry in Hx.
destruct x. {
  cbn.
  remember (ord (nth ib l d) (nth ia l d)) as y eqn:Hy.
  symmetry in Hy.
  destruct y. {
    cbn in Hs.
    rewrite <- Hs.
...
  } {
...
  }
} {
  cbn in Hs |-*.
  rewrite <- IHlrank.
...
apply (glop ord d (length lrank)) in Hs.
fold f in Hs.
congruence.
...
  clear - Hs Hls.
Search bsort.
Theorem bsort_bsort_rank_id : ∀ A ord (d : A) l lrank,
  length lrank = length l
  → bsort ord (map (λ i, nth i l d) lrank) = map (λ i, nth i l d) lrank
  → bsort_rank ord l = lrank.
Proof.
intros * Hl Hs.
revert l Hl Hs.
induction lrank as [| ia]; intros. {
  cbn in Hl.
  symmetry in Hl.
  now apply length_zero_iff_nil in Hl; subst l.
}
...
Theorem glop : ∀ A ord (d : A) l ia lrank,
  bsort_rank ord l = ia :: lrank
  ↔ ∀ a, a ∈ l → ord (nth ia l d) a = true.
Proof.
intros.
split. {
  intros Hl a Hal.
  induction lrank as [| ib]. {
    revert ia a Hal Hl.
    induction l as [| b]; intros; [ easy | ].
    destruct Hal as [Hal| Hal]. {
      subst b.
      destruct ia. {
        rewrite List_nth_0_cons.
        cbn - [ nth ] in Hl.
...
apply (glop _ d).
...
destruct l as [| a]; [ easy | ].
cbn in Hl.
apply Nat.succ_inj in Hl.
remember (a :: l) as l'; cbn in Hs; subst l'.
...
specialize (bsort_bsort_rank_id _ _ _ _ Hs) as H1.
...
  unfold bsort; subst lsorted.
  induction lrank as [| ia]; intros; [ easy | ].
  cbn in Hs |-*.
  destruct (ord (f (S (length lrank))) (f ia)). {
    cbn.
    destruct (ord (f ia) (f (S (length lrank)))). {
...
...
rewrite length_bsort_rank_insert.
...
assert (∃ lrank', bsort_insert ord a (map f lrank) = map f lrank'). {
  subst f; clear - Hs Ha.
  revert a Ha.
  induction lrank as [| ib]; intros; cbn in Ha. {
    exists [0]; cbn.
    now rewrite Ha.
  }
  destruct l_ini as [| a']; [ cbn in Ha | ]. {
    subst a.
    rewrite List_nth_nil in IHlrank.
    remember (λ i, nth i [] d) as f eqn:Hf.
    assert (H : bsort ord (map f lrank) = map f lrank). {
      cbn in Hs |-*.
      remember (map f lrank) as lsorted eqn:Hls.
      destruct lsorted as [| a]; [ easy | ].
      cbn in Hs |-*.
      destruct (ord a (f ib)). {
...
    specialize (IHlrank d eq_refl).
    destruct IHlrank as (lrank', Hr).
    exists (0 :: lrank').
    cbn - [ nth ].
    rewrite List_nth_nil.
    destruct (ord d d). {
      remember (λ i, nth i [] d) as f; cbn; subst f.
      f_equal.
      rewrite <- Hr; clear.
      induction lrank as [| ia]; [ easy | ].
      remember (λ i, nth i [] d) as f; cbn; subst f.
      rewrite List_nth_nil.
      destruct (ord d d); [ easy | ].
      now f_equal.
    } {
      now rewrite Hr.
    }
  }
  cbn in Ha.
  remember (nth (length lrank) (a' :: l_ini) d) as a'' eqn:Ha''.
  move Ha after Ha''.
  specialize (IHlrank a'' eq_refl).
  destruct IHlrank as (lrank', Hr).
  assert (H : a = nth (S (length lrank)) (a' :: l_ini) d) by easy.
  clear Ha; rename H into Ha; move Ha after Ha''.
  remember (a' :: l_ini) as l eqn:Hl.
  cbn.
  destruct (ord a (nth ib l d)). {
    exists (S (length lrank) :: ib :: lrank); cbn.
    now rewrite <- Ha.
  } {
    exists (ib :: lrank'); cbn.
    f_equal.
...
  }
}
destruct H as (lrank', Hr).
rewrite Hr.
...
  destruct l_ini as [| a']; [ easy | cbn ].
  cbn in Ha.
  destruct (ord a (f ib)). {
    rewrite Hf; cbn - [ nth ].
    exists (S (length lrank) :: ib :: lrank).
    now cbn; f_equal.
  } {
(**)
+    exists (ib :: ...)
...
    exists (ib :: S (length lrank) :: lrank).
    cbn - [ nth ]; f_equal.
    rewrite Hf.
    rewrite List_nth_succ_cons.
    rewrite <- Hf, <- Ha.
(* ouais, chais pas *)
...
apply (bsort_loop_bsort_rank_loop ord d d' []).
...

  map (λ i, nth i l d) (bsort_rank_loop ord d' l i reml lsorted) =
  bsort_loop ord (map (λ i, nth i l d) lsorted) (skipn (length lsorted) l).
Proof.
intros.
revert l i lsorted.
induction reml; intros; cbn. {
...
induction l as [| a]; [ easy | ].
cbn - [ nth ].
destruct l as [| b]; [ easy | ].
cbn - [ nth ].
unfold nth at 2 3.
cbn - [ nth ].
...


Fixpoint bsort_rank_insert {A B} (ord : A → A → bool) (ia : B) a lsorted :=
  match lsorted with
  | [] => [(ia, a)]
  | (ib, b) :: l =>
      if ord a b then (ia, a) :: lsorted
      else (ib, b) :: bsort_rank_insert ord ia a l
  end.

Fixpoint bsort_rank_loop {A} (ord : A → A → bool) lsorted l :=
  match l with
  | [] => lsorted
  | a :: l' =>
      bsort_rank_loop ord
        (bsort_rank_insert ord (length lsorted) a lsorted) l'
  end.

Definition bsort_rank {A} (ord : A → A → bool) := bsort_rank_loop ord [].

Print bsort_loop.

Theorem bsort_loop_bsort_loop_rank :  ∀ A (ord : A → A → bool) l lsorted,
  bsort_loop ord (map snd lsorted) l = map snd (bsort_rank_loop ord lsorted l).
Proof.
intros.
revert lsorted.
induction l as [| a]; intros; [ easy | cbn ].
rewrite <- IHl; clear IHl.
revert a l.
induction lsorted as [| b]; intros; [ easy | cbn ].
destruct b as (ib, b); cbn.
destruct (ord a b); [ easy | cbn ].
f_equal.
...
rewrite IHlsorted.
...
  bsort_loop ord (map snd lsorted) l =
  map (@snd nat A) (bsort_rank_loop ord lsorted l).
Proof.
intros.
revert lsorted.
induction l as [| a]; intros; [ easy | cbn ].
rewrite <- IHl; clear IHl.
f_equal; clear l.
induction lsorted as [| b]; [ easy | cbn ].
destruct b as (ib, b); cbn.
destruct (ord a b); [ easy | cbn ].
f_equal.
...
f_equal; apply IHlsorted.
Qed.

Theorem bsort_bsort_rank : ∀ A (ord : A → A → bool) (d : A) l,
  bsort ord l = map snd (bsort_rank ord l) ∧
  ∀ ia a, (ia, a) ∈ bsort_rank ord l → nth ia l d = a.
Proof.
intros.
split. {
  induction l as [| a]; [ easy | cbn ].
...
  now rewrite <- bsort_loop_bsort_loop_rank.
} {
  intros * Hia.
  revert ia a Hia.
  induction l as [| b]; intros; [ easy | ].
  destruct ia. {
    cbn.
Theorem in_bsort_rank_loop_cons : ∀ A (ord : A → A → bool) lsorted l a b,
  (0, a) ∈ bsort_rank_loop ord lsorted (b :: l)
  → b = a.
Proof.
intros * Hza.
revert a b lsorted Hza.
induction l as [| c]; intros. {
  cbn in Hza.
  revert a b Hza.
  induction lsorted as [| c]; intros. {
    cbn in Hza.
    destruct Hza as [Hza| Hza]; [ | easy ].
    now injection Hza.
  }
  destruct c as (ic, c).
  cbn in Hza.
  remember (ord b c) as b1 eqn:Hb1.
  symmetry in Hb1.
  destruct b1. {
    cbn in Hza.
    destruct Hza as [Hza| [Hza| Hza]]; [ easy | | ]. {
      injection Hza; clear Hza; intros; subst ic c.
...
Compute (let l := [2;7;1] in bsort_rank Nat.leb l).
Compute (let l := [5;2;2;7;0] in bsort_rank Nat.leb l).
...
Theorem in_bsort_rank_loop : ∀ A (ord : A → A → bool) lsorted l ia a,
  (ia, a) ∈ bsort_rank_loop ord lsorted l
  → nth ia (b :: l) d = a.

  Hia : (ia, a) ∈ bsort_rank_loop ord [(0, b)] l
  ============================
  nth ia (b :: l) d = a

...

  destruct ia. {
    cbn.
    clear IHl.
    revert a b Hia.
    induction l as [| c]; intros. {
      cbn in Hia.
      destruct Hia as [Hia| Hia]; [ | easy ].
      now injection Hia.
    }
    cbn in Hia.
    destruct (ord c b). {

...
    destruct l as [| c]. {
      cbn in Hia.
      destruct Hia as [Hia| Hia]; [ | easy ].
      now injection Hia.
    }
    cbn in Hia.
    destruct (ord c b). {
...
cbn - [ nth ].
split. {
  destruct l as [| b]; [ easy | ].
  cbn.
...

Fixpoint bsort_rank_insert {A} (ord : A → A → bool) d l ia lsorted :=
  match lsorted with
  | [] => [ia]
  | i :: lsorted' =>
      if ord (nth ia l d) (nth i l d) then ia :: lsorted
      else i :: bsort_rank_insert ord d l ia lsorted'
  end.

Fixpoint bsort_rank_loop {A} (ord : A → A → bool) d l i reml lsorted :=
  match reml with
  | 0 => lsorted
  | S reml' =>
      bsort_rank_loop ord d l (S i) reml'
        (bsort_rank_insert ord d l i lsorted)
  end.

Definition bsort_rank {A} (ord : A → A → bool) l :=
  match l with
  | [] => []
  | d :: _ => bsort_rank_loop ord d l 0 (length l) []
  end.

(* we should have
      bsort ord l = map (λ i, nth i l d) (bsort_rank ord l)
*)

(*
Theorem bsort_bsort_rank : ∀ A (ord : A → A → bool) (d : A) l,
  bsort ord l = map (λ i, nth i l d) (bsort_rank ord l).
Proof.
intros.
unfold bsort, bsort_rank.
destruct l as [| d' l']; [ easy | ].
remember (d' :: l') as l eqn:Hl; clear l' Hl.
Print bsort_loop.
Theorem bsort_loop_bsort_rank_loop : ∀ A ord (d d' : A) l i reml lsorted,
  map (λ i, nth i l d) (bsort_rank_loop ord d' l i reml lsorted) =
  bsort_loop ord (map (λ i, nth i l d) lsorted) (skipn (length lsorted) l).
Proof.
intros.
revert l i lsorted.
induction reml; intros; cbn. {
...
induction l as [| a]; [ easy | ].
cbn - [ nth ].
destruct l as [| b]; [ easy | ].
cbn - [ nth ].
unfold nth at 2 3.
cbn - [ nth ].
...
*)

(*
Compute (let l := [5;2;7;0] in bsort_rank Nat.leb l).
Compute (let l := [5;2;7;0] in (bsort Nat.leb l, map (λ i, nth i l 0) (bsort_rank Nat.leb l))).
*)
*)

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

Global Hint Resolve Nat_mod_fact_upper_bound : core.
