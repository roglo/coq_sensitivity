(* Theorems of general usage, which could be (or not) in Coq library *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Psatz Sorted Permutation Decidable.
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

Theorem match_id : ∀ A a (b : A), match a with 0 => b | S _ => b end = b.
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

Theorem Nat_succ_sub_succ_r : ∀ a b, b < a → a - b = S (a - S b).
Proof. intros * Hba; flia Hba. Qed.

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

Theorem List_map_const_is_repeat : ∀ A B b (f : A → B) l,
  (∀ a, f a = b)
  → map f l = repeat b (length l).
Proof.
intros * Hf.
induction l as [| a]; [ easy | ].
cbn; rewrite Hf; f_equal; apply IHl.
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

Theorem List_length_fold_right : ∀ A B (f : B → list A → list A) la lb,
  (∀ b l, length (f b l) = length l)
  → length (fold_right f la lb) = length la.
Proof.
intros * Hbl.
induction lb as [| b]; [ easy | cbn ].
now rewrite Hbl.
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

Theorem length_replace_at : ∀ A k la (e : A),
  k < length la
  → length (replace_at k la e) = length la.
Proof.
intros * Hkla.
unfold replace_at.
rewrite app_length, firstn_length.
rewrite List_length_cons, skipn_length.
flia Hkla.
Qed.

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

(* pair_eqb *)

Definition pair_eqb {A B} (eqb : A → B → _) ab cd :=
  (eqb (fst ab) (fst cd) && eqb (snd ab) (snd cd))%bool.

(* end pair_eqb *)

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

Theorem List_firstn_map_nth_seq : ∀ A (d : A) i l,
  i < length l
  → firstn i l = map (λ k : nat, nth k l d) (seq 0 i).
Proof.
intros * Hi.
revert i Hi.
induction l as [| j]; intros; [ easy | ].
cbn - [ nth ].
destruct i; [ easy | ].
cbn in Hi.
apply Nat.succ_lt_mono in Hi.
cbn - [ nth ].
f_equal.
rewrite <- seq_shift, map_map.
erewrite map_ext_in. 2: {
  intros k Hk.
  now rewrite List_nth_succ_cons.
}
now apply IHl.
Qed.

Theorem List_skipn_map_nth_seq : ∀ A (d : A) i l,
  skipn i l = map (λ k, nth (k + i) l d) (seq 0 (length l - i)).
Proof.
intros.
revert i.
induction l as [| j]; intros; [ apply skipn_nil | ].
rewrite List_length_cons.
destruct i. {
  rewrite Nat.sub_0_r.
  cbn - [ nth ]; f_equal.
  rewrite <- seq_shift, map_map.
  erewrite map_ext_in. 2: {
    intros k Hk.
    now rewrite Nat.add_0_r.
  }
  apply List_map_nth_seq.
}
cbn - [ nth ].
rewrite IHl.
apply map_ext_in.
intros k Hk.
now rewrite Nat.add_succ_r.
Qed.

Theorem length_nzero_iff_nnil : ∀ A (l : list A), length l ≠ 0 ↔ l ≠ [].
Proof.
intros.
now split; intros H1 H2; apply H1; apply length_zero_iff_nil.
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

Theorem iter_list_cons' : ∀ A B a l (f : A → B → A) d,
  iter_list (a :: l) f d = iter_list l f (f d a).
Proof. easy. Qed.

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

Theorem NoDup_skipn : ∀ A k (la : list A), NoDup la → NoDup (skipn k la).
Proof.
intros * Hnd.
revert la Hnd.
induction k; intros; [ easy | cbn ].
destruct la as [| a]; [ constructor | cbn ].
apply IHk.
now apply NoDup_cons_iff in Hnd.
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

(* isort: sort by insertion *)

Fixpoint isort_insert {A} (rel : A → A → bool) a lsorted :=
  match lsorted with
  | [] => [a]
  | b :: l =>
      if rel a b then a :: lsorted
      else b :: isort_insert rel a l
  end.

Fixpoint isort_loop {A} (rel : A → A → bool) lsorted l :=
  match l with
  | [] => lsorted
  | a :: l' => isort_loop rel (isort_insert rel a lsorted) l'
  end.

Definition isort {A} (rel : A → A → bool) := isort_loop rel [].

(* ssort: sort by selection *)

Fixpoint select_first {A} (rel : A → A → bool) a la :=
  match la with
  | [] => (a, [])
  | b :: lb =>
      let (c, lc) := select_first rel (if rel a b then a else b) lb in
      (c, (if rel a b then b else a) :: lc)
  end.

Fixpoint ssort_loop {A} (rel : A → A → bool) it l :=
  match it with
  | 0 => l
  | S it' =>
      match l with
      | [] => []
      | a :: la =>
          let (a', la') := select_first rel a la in
          a' :: ssort_loop rel it' la'
      end
  end.

Definition ssort {A} (rel : A → _) l := ssort_loop rel (length l) l.

(* bsort: bubble sort *)

Fixpoint bsort_swap {A} (rel : A → A → bool) it l :=
  match it with
  | 0 => None
  | S it' =>
      match l with
      | [] | [_] => None
      | a :: b :: l' =>
          if rel a b then
            match bsort_swap rel it' (b :: l') with
            | Some l'' => Some (a :: l'')
            | None => None
            end
          else
            Some (b :: a :: l')
      end
  end.

Fixpoint bsort_loop {A} (rel : A → A → bool) it l :=
  match it with
  | 0 => l
  | S it' =>
      match bsort_swap rel (length l) l with
      | Some l' => bsort_loop rel it' l'
      | None => l
      end
  end.

Definition bsort {A} (rel : A → _) l := bsort_loop rel (length l * length l) l.

(*
Compute (bsort Nat.leb [7;5;3;22;8]).
Definition succ_when_ge k a := a + Nat.b2n (k <=? a).
Fixpoint canon_sym_gr_list n k : list nat :=
  match n with
  | 0 => []
  | S n' =>
      k / n'! ::
      map (succ_when_ge (k / n'!)) (canon_sym_gr_list n' (k mod n'!))
  end.
Definition canon_sym_gr_list_list n : list (list nat) :=
  map (canon_sym_gr_list n) (seq 0 n!).
Compute (map (λ l, bsort Nat.leb l) (canon_sym_gr_list_list 6)).
*)

(* isort length *)

Theorem isort_insert_length : ∀ A rel (a : A) lsorted,
  length (isort_insert rel a lsorted) = S (length lsorted).
Proof.
intros.
induction lsorted as [| b]; intros; [ easy | cbn ].
destruct (rel a b); [ easy | ].
cbn; f_equal.
apply IHlsorted.
Qed.

Theorem isort_loop_length : ∀ A rel (lsorted l : list A),
  length (isort_loop rel lsorted l) = length lsorted + length l.
Proof.
intros.
revert lsorted.
induction l as [| a]; intros; [ now cbn; rewrite Nat.add_0_r | cbn ].
rewrite IHl, <- Nat.add_succ_comm; f_equal.
apply isort_insert_length.
Qed.

Theorem isort_length : ∀ A rel (l : list A), length (isort rel l) = length l.
Proof.
intros.
apply isort_loop_length.
Qed.

(* ssort length *)

Theorem select_first_length : ∀ A rel (a : A) la b lb,
  select_first rel a la = (b, lb)
  → length lb = length la.
Proof.
intros * Hab.
revert a b lb Hab.
induction la as [| a']; intros; cbn in Hab |-*. {
  now injection Hab; clear Hab; intros; subst b lb.
}
remember (rel a a') as x eqn:Hx; symmetry in Hx.
remember (select_first rel (if x then a else a') la) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as (c, lc).
injection Hab; clear Hab; intros; subst c lb.
cbn; f_equal.
now destruct x; apply IHla in Hlc.
Qed.

Theorem ssort_loop_length : ∀ A rel it (l : list A),
  length (ssort_loop rel it l) = length l.
Proof.
intros.
revert l.
induction it; intros; [ easy | cbn ].
destruct l as [| a]; [ easy | cbn ].
remember (select_first rel a l) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as (a', la'); cbn; f_equal.
rewrite IHit.
now apply select_first_length in Hlb.
Qed.

Theorem ssort_length : ∀ A rel (l : list A), length (ssort rel l) = length l.
Proof.
intros.
apply ssort_loop_length.
Qed.

(* *)

Theorem Permutation_cons_isort_insert : ∀ A (rel : A → _) a la lb,
  Permutation la lb
  → Permutation (a :: la) (isort_insert rel a lb).
Proof.
intros * Hab.
revert a la Hab.
induction lb as [| b]; intros; cbn. {
  apply Permutation_sym in Hab.
  now apply Permutation_nil in Hab; subst la.
}
remember (rel a b) as x eqn:Hx; symmetry in Hx.
destruct x; [ now constructor | ].
replace (b :: lb) with ([b] ++ lb) in Hab by easy.
apply Permutation_cons_app with (a := a) in Hab.
eapply Permutation_trans; [ apply Hab | cbn ].
apply perm_skip.
now apply IHlb.
Qed.

Theorem Permutation_isort_insert_sorted : ∀ A (rel : A → _) la lb c,
  Permutation la lb
  → Permutation (isort_insert rel c la) (isort_insert rel c lb).
Proof.
intros * Hp.
revert la Hp.
induction lb as [| b]; intros; cbn. {
  now apply Permutation_sym, Permutation_nil in Hp; subst la; cbn.
}
remember (rel c b) as x eqn:Hx; symmetry in Hx.
destruct x. {
  apply Permutation_sym.
  apply Permutation_cons_isort_insert.
  now apply Permutation_sym.
} {
  apply Permutation_sym.
  eapply Permutation_trans. 2: {
    apply Permutation_cons_isort_insert.
    apply Permutation_sym.
    apply Hp.
  }
  replace (c :: b :: lb) with ([c] ++ b :: lb) by easy.
  eapply Permutation_trans; [ | now apply Permutation_cons_app ]; cbn.
  constructor.
  apply Permutation_sym.
  eapply Permutation_trans; [ | apply IHlb; easy ].
  now apply Permutation_cons_isort_insert.
}
Qed.

Theorem Permutation_isort_loop_sorted : ∀ A (rel : A → _) la lb lc,
  Permutation la lb
  → Permutation (isort_loop rel la lc) (isort_loop rel lb lc).
Proof.
intros * Hp.
revert la lb Hp.
induction lc as [| c]; intros; [ easy | cbn ].
apply IHlc.
now apply Permutation_isort_insert_sorted.
Qed.

Theorem Permutation_isort_loop : ∀ A (rel : A → _) la lb,
  Permutation (la ++ lb) (isort_loop rel la lb).
Proof.
intros.
revert la.
induction lb as [| b]; intros; [ now rewrite app_nil_r | ].
specialize (IHlb (la ++ [b])) as H1.
rewrite <- app_assoc in H1; cbn in H1.
eapply Permutation_trans; [ apply H1 | ].
cbn.
clear IHlb H1.
revert lb b.
induction la as [| a]; intros; [ easy | ].
cbn.
remember (rel b a) as x eqn:Hx; symmetry in Hx.
destruct x. {
  apply Permutation_isort_loop_sorted.
  rewrite app_comm_cons.
  replace (b :: a :: la) with ([b] ++ (a :: la)) by easy.
  apply Permutation_app_comm.
} {
  apply Permutation_isort_loop_sorted.
  constructor.
  eapply Permutation_trans. 2: {
    now apply Permutation_cons_isort_insert.
  }
  apply Permutation_app_comm.
}
Qed.

Theorem Permutation_isort : ∀ A (rel : A → _) l, Permutation l (isort rel l).
Proof.
intros.
induction l as [| a]; [ easy | cbn ].
specialize Permutation_isort_loop as H1.
apply (H1 _ rel [a] l).
Qed.

(* in isort *)

Theorem in_isort_insert : ∀ A (rel : A → A → bool) a b lsorted,
  a ∈ isort_insert rel b lsorted
  → a ∈ b :: lsorted.
Proof.
intros * Ha.
revert a b Ha.
induction lsorted as [| c]; intros. {
  cbn in Ha.
  destruct Ha as [Ha| Ha]; [ now left | easy ].
}
cbn in Ha.
destruct (rel b c); [ easy | ].
cbn in Ha.
destruct Ha as [Ha| Ha]; [ now right; left | ].
apply IHlsorted in Ha.
destruct Ha as [Ha| Ha]; [ now left | now right; right ].
Qed.

Theorem in_isort_loop : ∀ A (rel : A → A → bool) a lsorted l,
  a ∈ isort_loop rel lsorted l
  → a ∈ lsorted ∨ a ∈ l.
Proof.
intros * Ha.
revert a lsorted Ha.
induction l as [| b]; intros; [ now left | ].
cbn in Ha.
apply IHl in Ha.
destruct Ha as [Ha| Ha]. {
  apply in_isort_insert in Ha.
  destruct Ha as [Ha| Ha]; [ now right; left | now left ].
} {
  now right; right.
}
Qed.

Theorem in_isort : ∀ A (rel : A → A → bool) a l, a ∈ isort rel l → a ∈ l.
Proof.
intros * Ha.
apply in_isort_loop in Ha.
now destruct Ha.
Qed.

(* isort_rank: like isort but return the rank of what have been
   sorted; its result, when applied to the initial list as an
   operator, returns the sorted list  *)

Fixpoint isort_rank_insert {A B} (rel : A → A → bool) (f : B → A) ia lrank :=
  match lrank with
  | [] => [ia]
  | ib :: l =>
      if rel (f ia) (f ib) then ia :: lrank
      else ib :: isort_rank_insert rel f ia l
  end.

Fixpoint isort_rank_loop {A} (rel : A → A → bool) f lrank (l : list A) :=
  match l with
  | [] => lrank
  | _ :: l' =>
      isort_rank_loop rel f (isort_rank_insert rel f (length lrank) lrank) l'
  end.

Definition isort_rank {A} (rel : A → A → bool) l :=
  match l with
  | [] => []
  | d :: _ => isort_rank_loop rel (λ i, nth i l d) [] l
  end.

(*
Compute (let l := [2;7;1] in isort_rank Nat.leb l).
Compute (let l := [5;10;2;7;0] in isort_rank Nat.leb l).
Compute (let l := [5;2;2;7;0] in isort_rank Nat.leb l).
Compute (let l := [5;2;2;7;0] in isort_rank Nat.ltb l).
*)

Theorem isort_rank_insert_length : ∀ A B rel (f : B → A) ia lrank,
  length (isort_rank_insert rel f ia lrank) = S (length lrank).
Proof.
intros.
induction lrank as [| ib]; [ easy | cbn ].
destruct (rel (f ia) (f ib)); [ easy | cbn ].
now rewrite IHlrank.
Qed.

Theorem isort_rank_loop_length : ∀ A rel (f : _ → A) lrank l,
  length (isort_rank_loop rel f lrank l) = length lrank + length l.
Proof.
intros.
revert lrank.
induction l as [| b]; intros; [ easy | cbn ].
rewrite IHl.
rewrite isort_rank_insert_length.
apply Nat.add_succ_comm.
Qed.

Theorem isort_rank_length : ∀ A rel (l : list A),
  length (isort_rank rel l) = length l.
Proof.
intros.
unfold isort_rank.
destruct l as [| d]; [ easy | ].
remember (d :: l) as l' eqn:Hl'.
clear l Hl'.
rename l' into l.
apply isort_rank_loop_length.
Qed.

Theorem isort_insert_isort_rank_insert : ∀ A B rel ia (f : B → A) lrank,
  isort_insert rel (f ia) (map f lrank) =
  map f (isort_rank_insert rel f ia lrank).
Proof.
intros.
induction lrank as [| ib]; [ easy | cbn ].
destruct (rel (f ia) (f ib)); [ easy | ].
cbn; f_equal.
apply IHlrank.
Qed.

Theorem isort_loop_isort_rank_loop : ∀ A rel d (f : nat → A) lrank l,
  (∀ i, i < length l → f (length lrank + i) = nth i l d)
  → isort_loop rel (map f lrank) l = map f (isort_rank_loop rel f lrank l).
Proof.
intros * Hia.
revert lrank Hia.
induction l as [| a]; intros; [ easy | cbn ].
specialize (Hia 0 (Nat.lt_0_succ _)) as H1.
cbn in H1; rewrite Nat.add_0_r in H1.
rewrite <- H1.
rewrite isort_insert_isort_rank_insert.
rewrite IHl; [ easy | ].
intros i Hi.
rewrite isort_rank_insert_length.
apply Nat.succ_lt_mono in Hi.
specialize (Hia (S i) Hi) as H2.
now rewrite <- Nat.add_succ_comm in H2.
Qed.

Theorem isort_rank_insert_nth_indep : ∀ A rel (d d' : A) ia lrank l_ini,
  ia < length l_ini
  → (∀ i, i ∈ lrank → i < length l_ini)
  → isort_rank_insert rel (λ i : nat, nth i l_ini d) ia lrank =
    isort_rank_insert rel (λ i : nat, nth i l_ini d') ia lrank.
Proof.
intros * Hia Hini.
induction lrank as [| ib]; [ easy | ].
cbn - [ nth ].
specialize (Hini ib (or_introl eq_refl)) as Hib.
rewrite (nth_indep _ _ d' Hia).
rewrite (nth_indep _ _ d' Hib).
remember (rel (nth ia l_ini d') (nth ib l_ini d')) as x eqn:Hx.
symmetry in Hx.
destruct x; [ easy | ].
f_equal.
apply IHlrank.
intros i Hi.
apply Hini.
now right.
Qed.

Theorem in_isort_rank_insert : ∀ A B rel (f : B → A) ia lrank i,
  i ∈ isort_rank_insert rel f ia lrank
  → i ∈ ia :: lrank.
Proof.
intros * Hil.
induction lrank as [| ib]; [ easy | ].
cbn in Hil.
destruct (rel (f ia) (f ib)); [ easy | ].
destruct Hil as [Hil| Hil]; [ now subst i; right; left | ].
specialize (IHlrank Hil).
destruct IHlrank as [Hi| Hi]; [ now subst i; left | now right; right ].
Qed.

Theorem isort_rank_loop_nth_indep : ∀ A rel (d d' : A) lrank l_ini l,
  length lrank + length l ≤ length l_ini
  → (∀ i, i ∈ lrank → i < length l_ini)
  → isort_rank_loop rel (λ i, nth i l_ini d) lrank l =
    isort_rank_loop rel (λ i, nth i l_ini d') lrank l.
Proof.
intros * Hia Hil.
revert lrank Hia Hil.
induction l as [| b]; intros; [ easy | ].
cbn - [ nth ] in Hia |-*.
rewrite isort_rank_insert_nth_indep with (d' := d'); [ | flia Hia | easy ].
rewrite <- Nat.add_succ_comm in Hia.
rewrite IHl; [ easy | now rewrite isort_rank_insert_length | ].
intros i Hi.
apply in_isort_rank_insert in Hi.
destruct Hi as [Hi| Hi]; [ subst i; flia Hia | ].
now apply Hil.
Qed.

Theorem isort_isort_rank : ∀ A (rel : A → A → bool) (d : A) l,
  isort rel l = map (λ i, nth i l d) (isort_rank rel l).
Proof.
intros.
destruct l as [| d' l]; [ easy | ].
cbn - [ nth ].
replace [d'] with (map (λ i, nth i (d' :: l) d) [0]) by easy.
rewrite isort_loop_isort_rank_loop with (d := d').
cbn - [ nth ].
f_equal. 2: {
  intros i Hi; cbn.
  now apply nth_indep.
}
apply isort_rank_loop_nth_indep; [ easy | ].
intros i Hi.
destruct Hi as [Hi| Hi]; [ subst i; cbn; easy | easy ].
Qed.

Theorem isort_rank_insert_ub : ∀ A (rel : A → _) ia lrank f i n,
  ia < n
  → (∀ i, i ∈ lrank → i < n)
  → nth i (isort_rank_insert rel f ia lrank) 0 < n.
Proof.
intros * Hia Hn.
revert i.
induction lrank as [| ib]; intros. {
  destruct i; [ easy | cbn ].
  rewrite match_id; flia Hia.
}
cbn - [ nth ].
remember (rel (f ia) (f ib)) as x eqn:Hx.
symmetry in Hx.
destruct x. {
  destruct i; [ easy | ].
  rewrite List_nth_succ_cons.
  destruct (lt_dec i (length (ib :: lrank))) as [Hii| Hii]. 2: {
    apply Nat.nlt_ge in Hii.
    rewrite nth_overflow; [ flia Hia | easy ].
  }
  now apply Hn, nth_In.
} {
  destruct i; [ now cbn; apply Hn; left | cbn ].
  apply IHlrank.
  intros j Hj.
  now apply Hn; right.
}
Qed.

Theorem isort_rank_loop_ub : ∀ A (rel : A → _) f lrank l i,
  length lrank + length l ≠ 0
  → (∀ i, i ∈ lrank → i < length lrank + length l)
  → nth i (isort_rank_loop rel f lrank l) 0 <
    length lrank + length l.
Proof.
intros * Hlz Hil.
destruct (lt_dec i (length lrank + length l)) as [Hir| Hir]. 2: {
  apply Nat.nlt_ge in Hir.
  rewrite nth_overflow; [ | now rewrite isort_rank_loop_length ].
  now apply Nat.neq_0_lt_0.
}
clear Hlz.
revert lrank Hil Hir.
induction l as [| b]; intros. {
  rewrite Nat.add_0_r in Hir.
  now apply Hil, nth_In.
}
cbn in Hir |-*.
rewrite <- Nat.add_succ_comm in Hir |-*.
specialize (in_isort_rank_insert) as H1.
specialize (H1 A nat rel f (length lrank) lrank).
remember (isort_rank_insert rel f (length lrank) lrank) as lr' eqn:Hlr'.
specialize isort_rank_insert_length as H2.
specialize (H2 A nat rel f (length lrank) lrank).
rewrite <- Hlr' in H2.
rewrite <- H2 in Hir |-*.
apply IHl; [ | easy ].
intros j Hj.
rewrite H2, Nat.add_succ_comm.
rewrite Hlr' in Hj.
apply in_isort_rank_insert in Hj.
destruct Hj as [Hj| Hj]; [ subst j; flia | ].
now apply Hil.
Qed.

Theorem isort_rank_ub : ∀ A rel (l : list A) i,
  l ≠ [] → nth i (isort_rank rel l) 0 < length l.
Proof.
intros * Hlz.
destruct l as [| ia]; [ easy | clear Hlz ].
cbn - [ nth ].
apply isort_rank_loop_ub; [ easy | ].
intros j Hj.
destruct Hj; [ now subst j; cbn | easy ].
Qed.

Theorem in_isort_rank_lt : ∀ A (rel : A → _) l i,
  i ∈ isort_rank rel l → i < length l.
Proof.
intros * Hi.
apply (In_nth _ _ 0) in Hi.
destruct Hi as (j & Hjl & Hji).
rewrite isort_rank_length in Hjl.
rewrite <- Hji.
apply isort_rank_ub.
now intros H; subst l.
Qed.

Theorem NoDup_isort_rank_insert : ∀ A (d : A) rel l_ini ia lrank,
  NoDup (ia :: lrank)
  → NoDup (isort_rank_insert rel (λ k : nat, nth k l_ini d) ia lrank).
Proof.
intros * Hnd.
revert ia Hnd.
induction lrank as [| ib]; intros. {
  cbn; constructor; [ easy | constructor ].
}
cbn.
destruct (rel (nth ia l_ini d) (nth ib l_ini d)); [ easy | ].
apply NoDup_cons_iff in Hnd.
destruct Hnd as (Hia, Hnd).
apply NoDup_cons_iff in Hnd.
destruct Hnd as (Hib, Hnd).
apply NoDup_cons. 2: {
  apply IHlrank.
  apply NoDup_cons_iff.
  split; [ | easy ].
  now intros H; apply Hia; right.
}
intros Hib'.
apply in_isort_rank_insert in Hib'.
destruct Hib' as [Hib'| Hib']; [ | easy ].
subst ib; apply Hia.
now left.
Qed.

Theorem NoDup_isort_rank_loop : ∀ A d rel l_ini (l : list A) lrank,
  NoDup lrank
  → AllLt lrank (length lrank)
  → NoDup (isort_rank_loop rel (λ k, nth k l_ini d) lrank l).
Proof.
intros * Hnd Halt.
revert lrank Hnd Halt.
induction l as [| a]; intros; [ easy | cbn ].
apply IHl.
apply NoDup_isort_rank_insert. 2: {
  rewrite isort_rank_insert_length.
  intros i Hi.
  apply in_isort_rank_insert in Hi.
  destruct Hi as [Hi| Hi]; [ now rewrite Hi | ].
  specialize (Halt _ Hi) as H1.
  flia H1.
}
apply NoDup_cons_iff.
split; [ | easy ].
intros H.
specialize (Halt _ H) as H1.
now apply Nat.lt_irrefl in H1.
Qed.

Theorem NoDup_isort_rank : ∀ A rel (l : list A), NoDup (isort_rank rel l).
Proof.
intros.
apply (proj2 (NoDup_nth _ 0)).
rewrite isort_rank_length.
intros i j Hi Hj Hij.
destruct l as [| d]; [ easy | ].
unfold isort_rank in Hij.
specialize (NoDup_isort_rank_loop d rel (d :: l) (d :: l) (NoDup_nil _)) as H1.
assert (H : AllLt [] (length ([] : list nat))) by easy.
specialize (H1 H); clear H.
specialize (proj1 (NoDup_nth _ 0) H1) as H2.
rewrite isort_rank_loop_length in H2.
rewrite Nat.add_0_l in H2.
apply (H2 i j Hi Hj Hij).
Qed.

Theorem eq_isort_rank_nil : ∀ A (rel : A → _) l,
  isort_rank rel l = [] → l = [].
Proof.
intros * Hl.
apply (f_equal length) in Hl.
rewrite isort_rank_length in Hl.
now apply length_zero_iff_nil in Hl.
Qed.

(* end isort_rank *)

(* sorted *)

Fixpoint sorted {A} (rel : A → A → bool) l :=
  match l with
  | [] => true
  | [a] => true
  | a :: (b :: _) as la => (rel a b && sorted rel la)%bool
  end.

Definition reflexive A (rel : A → A → bool) :=
  ∀ a, rel a a = true.

Definition antisymmetric A (rel : A → A → bool) :=
  ∀ a b, rel a b = true → rel b a = true → a = b.

Definition transitive A (rel : A → A → bool) :=
  ∀ a b c, rel a b = true → rel b c = true → rel a c = true.

Definition total_relation {A} (rel : A → _) := ∀ a b,
  (rel a b || rel b a)%bool = true.

Theorem total_relation_is_reflexive : ∀ A (rel : A → _),
  total_relation rel → reflexive rel.
Proof.
intros * Htot a.
specialize (Htot a a) as H1.
apply Bool.orb_true_iff in H1.
now destruct H1.
Qed.

Theorem sorted_cons_cons_true_iff : ∀ A (rel : A → A -> bool) a b l,
  sorted rel (a :: b :: l) = true
  ↔ rel a b = true ∧ sorted rel (b :: l) = true.
Proof.
intros.
apply Bool.andb_true_iff.
Qed.

Theorem sorted_cons : ∀ A (rel : A → _) a la,
  sorted rel (a :: la) = true → sorted rel la = true.
Proof.
intros * Hs.
cbn in Hs.
destruct la as [| a']; [ easy | ].
now apply Bool.andb_true_iff in Hs.
Qed.

Theorem sorted_extends : ∀ A (rel : A → _),
  transitive rel →
  ∀ a l,
  sorted rel (a :: l) = true
  → ∀ b, b ∈ l → rel a b = true.
Proof.
intros * Htra * Hsort b Hb.
induction l as [| c]; [ easy | ].
apply sorted_cons_cons_true_iff in Hsort.
destruct Hsort as (Hac, Hsort).
destruct Hb as [Hb| Hb]; [ now subst c | ].
apply IHl; [ | easy ].
destruct l as [| d]; [ easy | ].
apply sorted_cons_cons_true_iff in Hsort.
apply sorted_cons_cons_true_iff.
destruct Hsort as (Hcd, Hsort).
split; [ now apply Htra with (b := c) | easy ].
Qed.

Theorem sorted_app : ∀ A rel (la lb : list A),
  sorted rel (la ++ lb) = true
  → sorted rel la = true ∧ sorted rel lb = true ∧
    (transitive rel → ∀ a b, a ∈ la → b ∈ lb → rel a b = true).
Proof.
intros * Hab.
split. {
  revert lb Hab.
  induction la as [| a1]; intros; [ easy | ].
  destruct la as [| a2]; [ easy | ].
  cbn - [ sorted ] in Hab |-*.
  apply sorted_cons_cons_true_iff in Hab.
  apply sorted_cons_cons_true_iff.
  destruct Hab as (Haa & Hab).
  split; [ easy | ].
  now apply (IHla lb).
}
split. {
  revert lb Hab.
  induction la as [| a1]; intros; [ easy | ].
  destruct la as [| a2]. {
    cbn in Hab.
    destruct lb as [| b1]; [ easy | ].
    now apply Bool.andb_true_iff in Hab.
  }
  cbn - [ sorted ] in Hab.
  apply sorted_cons_cons_true_iff in Hab.
  destruct Hab as (Haa & Hab).
  now apply IHla.
} {
  intros Htrans * Ha Hb.
  revert a lb Ha Hab Hb.
  induction la as [| a1]; intros; [ easy | ].
  destruct Ha as [Ha| Ha]. 2: {
    apply (IHla a lb); [ easy | | easy ].
    cbn - [ sorted ] in Hab.
    now apply sorted_cons in Hab.
  }
  subst a1.
  cbn - [ sorted ] in Hab.
  apply sorted_extends with (l := la ++ lb); [ easy | easy | ].
  now apply in_or_app; right.
}
Qed.

Theorem sorted_app_iff : ∀ A rel,
  transitive rel →
  ∀ (la lb : list A),
  sorted rel (la ++ lb) = true
  ↔ sorted rel la = true ∧ sorted rel lb = true ∧
    (∀ a b, a ∈ la → b ∈ lb → rel a b = true).
Proof.
intros * Htra *.
split. {
  intros Hab.
  apply sorted_app in Hab.
  split; [ easy | ].
  split; [ easy | ].
  intros a b Ha Hb.
  now apply Hab.
} {
  intros (Ha & Hb & Hab).
  revert lb Hb Hab.
  induction la as [| a] using rev_ind; intros; [ easy | cbn ].
  rewrite <- app_assoc; cbn.
  apply IHla. {
    now apply sorted_app in Ha.
  } {
    cbn.
    destruct lb as [| b]; [ easy | ].
    rewrite Hab; cycle 1. {
      now apply in_or_app; right; left.
    } {
      now left.
    }
    now rewrite Hb.
  }
  intros a' b' Ha' Hb'.
  destruct Hb' as [Hb'| Hb']. {
    apply sorted_app in Ha.
    subst b'.
    apply Ha; [ easy | easy | now left ].
  } {
    apply Hab; [ | easy ].
    now apply in_or_app; left.
  }
}
Qed.

(* isort is sorted *)

Theorem isort_insert_is_sorted : ∀ A (rel : A → _),
  total_relation rel →
  ∀ a lsorted,
  sorted rel lsorted = true
  → sorted rel (isort_insert rel a lsorted) = true.
Proof.
intros * Hto * Hs.
induction lsorted as [| b]; [ easy | cbn ].
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  remember (b :: lsorted) as l; cbn; subst l.
  now apply Bool.andb_true_iff.
} {
  specialize (Hto a b) as Hba.
  rewrite Hab in Hba; cbn in Hba.
  destruct lsorted as [| c]; [ now cbn; rewrite Hba | ].
  remember (c :: lsorted) as l; cbn in Hs |-*; subst l.
  apply Bool.andb_true_iff in Hs.
  destruct Hs as (Hbc, Hs).
  rewrite IHlsorted; [ | easy ].
  cbn.
  remember (rel a c) as ac eqn:Hac; symmetry in Hac.
  destruct ac; [ now rewrite Hba | now rewrite Hbc ].
}
Qed.

Theorem isort_loop_is_sorted : ∀ A (rel : A → _),
  total_relation rel →
  ∀ lsorted l,
  sorted rel lsorted = true
  → sorted rel (isort_loop rel lsorted l) = true.
Proof.
intros * Hto * Hs.
revert lsorted Hs.
induction l as [| a]; intros; [ easy | cbn ].
now apply IHl, isort_insert_is_sorted.
Qed.

Theorem sorted_trans : ∀ A (rel : A → _),
  transitive rel →
  ∀ a b la,
  sorted rel (a :: la ++ [b]) = true →
  rel a b = true.
Proof.
intros * Htra * Hs.
revert a b Hs.
induction la as [| c]; intros. {
  cbn in Hs.
  now apply Bool.andb_true_iff in Hs.
}
remember (c :: la) as lb; cbn in Hs; subst lb.
rewrite <- app_comm_cons in Hs.
apply Bool.andb_true_iff in Hs.
destruct Hs as (Hac, Hs).
specialize (IHla _ _ Hs) as H1.
now apply Htra with (b := c).
Qed.

Theorem sorted_repeat : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  ∀ a la,
  sorted rel (a :: la ++ [a]) = true
  → la = repeat a (length la).
Proof.
intros * Hant Htra * Hs.
revert a Hs.
induction la as [| b]; intros; [ easy | cbn ].
remember (b :: la) as lb; cbn in Hs; subst lb.
rewrite <- app_comm_cons in Hs.
apply Bool.andb_true_iff in Hs.
destruct Hs as (Hab, Hs).
specialize (sorted_trans Htra _ _ _ Hs) as Hba.
specialize (Hant a b Hab Hba) as H1; subst b.
f_equal.
now apply IHla.
Qed.

Theorem cons_app_repeat : ∀ A (a : A) la,
  a :: la = la ++ [a]
  → la = repeat a (length la).
Proof.
intros * Hla.
induction la as [| b]; intros; [ easy | cbn ].
cbn in Hla.
injection Hla; clear Hla; intros Hla H1; subst b.
f_equal.
now apply IHla.
Qed.

Theorem isort_insert_trans_r : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  ∀ a b la,
  rel a b = true
  → isort_insert rel a la = la ++ [a]
  → isort_insert rel b (la ++ [a]) = la ++ [a; b].
Proof.
intros * Hant Htra * Hab Hs.
induction la as [| c]; cbn. {
  remember (rel b a) as ba eqn:Hba; symmetry in Hba.
  destruct ba; [ | easy ].
  now rewrite (Hant a b Hab Hba).
}
remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
destruct bc. {
  cbn in Hs.
  remember (rel a c) as ac eqn:Hac; symmetry in Hac.
  destruct ac. {
    injection Hs; clear Hs; intros Hs H1; subst c.
    specialize (Hant a b Hab Hbc) as H1; subst b.
    f_equal.
    now rewrite app_comm_cons, Hs, <- app_assoc.
  }
  specialize (Htra a b c Hab Hbc) as H1.
  congruence.
}
f_equal.
apply IHla.
cbn in Hs.
remember (rel a c) as ac eqn:Hac; symmetry in Hac.
destruct ac; [ | now injection Hs ].
injection Hs; clear Hs; intros Hs H1; subst c.
apply cons_app_repeat in Hs.
rewrite Hs.
remember (length la) as len eqn:Hlen.
clear - Hant Htra.
induction len; [ easy | cbn ].
destruct (rel a a). {
  f_equal.
  apply repeat_cons.
}
f_equal.
apply IHlen.
Qed.

Theorem sorted_isort_insert_r : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  ∀ a la,
  sorted rel (la ++ [a]) = true
  → isort_insert rel a la = la ++ [a].
Proof.
intros * Hant Htra * Hla.
revert a Hla.
induction la as [| b] using rev_ind; intros; [ easy | cbn ].
apply sorted_app in Hla.
destruct Hla as (Hla & _ & Htrr).
specialize (Htrr Htra).
specialize (IHla _ Hla) as H1.
destruct la as [| c]; cbn. {
  clear Hla H1.
  specialize (Htrr b a (or_introl eq_refl) (or_introl eq_refl)).
  rename Htrr into Hba.
  remember (rel a b) as ab eqn:Hab; symmetry in Hab.
  destruct ab; [ | easy ].
  apply Hant in Hba.
  now rewrite (Hba Hab).
}
specialize (Htrr c a (or_introl eq_refl) (or_introl eq_refl)) as Hca.
remember (rel a c) as ac eqn:Hac; symmetry in Hac.
destruct ac. {
  apply Hant in Hca.
  specialize (Hca Hac); subst c.
  f_equal.
  cbn in H1.
  remember (rel b a) as ba eqn:Hba; symmetry in Hba.
  destruct ba. {
    injection H1; clear H1; intros H1 H2; subst b.
    rewrite <- H1; cbn.
    now f_equal.
  }
  injection H1; clear H1; intros H1.
  apply Bool.not_true_iff_false in Hba.
  exfalso; apply Hba.
  apply Htrr; [ | now left ].
  now apply in_or_app; right; left.
}
f_equal.
cbn in H1.
remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
destruct bc. {
  injection H1; clear H1; intros H1 H2; subst c.
  rewrite <- H1; cbn.
  rewrite Hac.
  f_equal.
  rewrite <- app_comm_cons in Hla.
  specialize (sorted_repeat Hant Htra b la Hla) as Har.
  rewrite Har.
  remember (length la) as len eqn:Hlen; symmetry in Hlen.
  clear - Hac.
  induction len; [ easy | cbn ].
  rewrite Hac.
  f_equal; apply IHlen.
}
injection H1; clear H1; intros H1.
rewrite <- app_assoc; cbn.
specialize (Htrr b a) as Hba.
assert (H : b ∈ c :: la ++ [b]). {
  rewrite app_comm_cons.
  now apply in_or_app; right; left.
}
specialize (Hba H (or_introl eq_refl)); clear H.
now apply isort_insert_trans_r.
Qed.

Theorem sorted_isort_loop : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  ∀ ls l,
  sorted rel (ls ++ l) = true
  → isort_loop rel ls l = ls ++ l.
Proof.
intros * Hant Htra * Hs.
revert ls Hs.
induction l as [| a]; intros; cbn; [ now rewrite app_nil_r | ].
assert (H : isort_insert rel a ls = ls ++ [a]). {
  clear IHl.
  assert (H : sorted rel (ls ++ [a]) = true). {
    rewrite List_app_cons, app_assoc in Hs.
    now apply sorted_app in Hs.
  }
  clear l Hs; rename H into Hs.
  now apply sorted_isort_insert_r.
}
rewrite H.
symmetry.
rewrite List_app_cons, app_assoc.
symmetry.
apply IHl.
now rewrite <- app_assoc.
Qed.

Theorem ssort_loop_cons : ∀ A rel it a b (la lb : list A),
  length la ≤ it
  → select_first rel a la = (b, lb)
  → ssort_loop rel it (a :: la) = b :: ssort_loop rel it lb.
Proof.
intros * Hit Hab.
revert a b la lb Hit Hab.
induction it; intros; cbn. {
  apply Nat.le_0_r, length_zero_iff_nil in Hit; subst la.
  cbn in Hab.
  now injection Hab; clear Hab; intros; subst b lb.
}
destruct la as [| a']. {
  cbn in Hab.
  injection Hab; clear Hab; intros; subst b lb.
  now destruct it.
}
cbn in Hit.
apply Nat.succ_le_mono in Hit.
cbn in Hab |-*.
remember (rel a a') as x eqn:Hx; symmetry in Hx.
remember (select_first rel (if x then a else a') la) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as (c, lc).
injection Hab; clear Hab; intros; subst c lb.
f_equal.
remember (select_first rel (if x then a' else a) lc) as ld eqn:Hld.
symmetry in Hld.
destruct ld as (d, ld).
apply IHit; [ | easy ].
specialize select_first_length as H1.
specialize (H1 _ rel (if x then a else a') la b lc Hlc).
now rewrite H1.
Qed.

Theorem eq_ssort_loop_nil : ∀ A rel it (l : list A),
  ssort_loop rel it l = [] → l = [].
Proof.
intros * Hit.
revert l Hit.
induction it; intros; [ easy | ].
cbn in Hit.
destruct l as [| a la]; [ easy | exfalso ].
now destruct (select_first rel a la).
Qed.

Theorem select_first_sorted : ∀ A rel,
  transitive rel → ∀ (a b : A) la lb,
  sorted rel (a :: la) = true
  → select_first rel a la = (b, lb)
  → a = b ∧ la = lb.
Proof.
intros * Htr * Hs Hss.
revert a b lb Hs Hss.
induction la as [| c]; intros. {
  cbn in Hss.
  now injection Hss; intros.
}
remember (c :: la) as l; cbn in Hs; subst l.
apply Bool.andb_true_iff in Hs.
destruct Hs as (H1, H2).
cbn in Hss.
rewrite H1 in Hss.
remember (select_first rel a la) as ld eqn:Hld.
symmetry in Hld.
destruct ld as (d, ld).
injection Hss; clear Hss; intros; subst d lb.
rename ld into lb.
enough (H : a = b ∧ la = lb). {
  split; [ easy | now f_equal ].
}
apply IHla; [ | easy ].
cbn in H2 |-*.
destruct la as [| d]; [ easy | ].
apply Bool.andb_true_iff in H2.
apply Bool.andb_true_iff.
destruct H2 as (H2, H3).
split; [ | easy ].
now apply Htr with (b := c).
Qed.

Theorem sorted_ssort_loop : ∀ A (rel : A → _),
  transitive rel →
  ∀ it l,
  length l ≤ it
  → sorted rel l = true
  → ssort_loop rel it l = l.
Proof.
intros * Htr * Hit Hs.
revert l Hit Hs.
induction it; intros; [ easy | cbn ].
destruct l as [| a la]; [ easy | ].
cbn in Hit; apply Nat.succ_le_mono in Hit.
remember (select_first rel a la) as lb eqn:Hlb.
symmetry in Hlb.
destruct lb as (b, lb).
specialize (select_first_sorted Htr _ _ Hs Hlb) as H1.
destruct H1; subst b lb.
f_equal.
apply IHit; [ easy | ].
cbn in Hs.
destruct la as [| b]; [ easy | ].
now apply Bool.andb_true_iff in Hs.
Qed.

Theorem select_first_Permutation : ∀ A (rel : A → _) a b la lb,
  select_first rel a la = (b, lb)
  → Permutation (a :: la) (b :: lb).
Proof.
intros * Hab.
revert a b lb Hab.
induction la as [| c]; intros. {
  cbn in Hab.
  now injection Hab; clear Hab; intros; subst b lb.
}
cbn in Hab.
remember (if rel a c then a else c) as x eqn:Hx; symmetry in Hx.
remember (select_first rel x la) as ld eqn:Hld; symmetry in Hld.
destruct ld as (d, ld).
injection Hab; clear Hab; intros; subst d lb.
move c after b; move x before c.
move ld before la.
remember (rel a c) as ac eqn:Hac; symmetry in Hac.
specialize (IHla x b ld Hld) as H1.
destruct ac; subst x. {
  etransitivity; [ apply perm_swap | symmetry ].
  etransitivity; [ apply perm_swap | symmetry ].
  now apply perm_skip.
} {
  symmetry.
  etransitivity; [ apply perm_swap | symmetry ].
  now apply perm_skip.
}
Qed.

Theorem select_first_if : ∀ A (rel : A → _),
  transitive rel →
  total_relation rel →
  ∀ a b la lb,
  select_first rel a la = (b, lb)
  → (∀ c, c ∈ a :: la → rel b c = true) ∧
    (∀ c, c ∈ lb → rel b c = true) ∧
    Permutation (a :: la) (b :: lb).
Proof.
intros * Htr Htot * Hab.
revert a b lb Hab.
induction la as [| c]; intros. {
  cbn in Hab.
  injection Hab; clear Hab; intros; subst b lb.
  split; [ | easy ].
  intros c Hc.
  destruct Hc as [Hc| Hc]; [ | easy ].
  subst c.
  apply total_relation_is_reflexive in Htot.
  apply Htot.
}
cbn in Hab.
remember (if rel a c then a else c) as x eqn:Hx; symmetry in Hx.
remember (select_first rel x la) as ld eqn:Hld; symmetry in Hld.
destruct ld as (d, ld).
injection Hab; clear Hab; intros; subst d lb.
move c after b; move x before c.
move ld before la.
remember (rel a c) as ac eqn:Hac; symmetry in Hac.
specialize (IHla x b ld Hld) as H1.
destruct H1 as (H1 & H2 & H3).
split. {
  intros d Hd.
  destruct Hd as [Hd| [Hd| Hd]]. {
    subst d.
    destruct ac; subst x. {
      now specialize (H1 a (or_introl eq_refl)).
    }
    specialize (H1 c (or_introl eq_refl)) as H4.
    apply Htr with (b := c); [ easy | ].
    specialize (Htot a c) as H5.
    now rewrite Hac in H5; cbn in H5.
  } {
    subst d.
    destruct ac; subst x; [ | now apply H1; left ].
    apply Htr with (b := a); [ | easy ].
    now apply H1; left.
  } {
    now apply H1; right.
  }
}
split. {
  intros d Hd.
  destruct ac; subst x. {
    destruct Hd as [Hd| Hd]; [ | now apply H2 ].
    subst d.
    apply Htr with (b := a); [ | easy ].
    now apply H1; left.
  } {
    destruct Hd as [Hd| Hd]; [ | now apply H2 ].
    subst d.
    apply Htr with (b := c); [ now apply H1; left | ].
    specialize (Htot a c) as H5.
    now rewrite Hac in H5.
  }
}
destruct ac; subst x. {
  etransitivity; [ apply perm_swap | symmetry ].
  etransitivity; [ apply perm_swap | symmetry ].
  now apply perm_skip.
} {
  symmetry.
  etransitivity; [ apply perm_swap | symmetry ].
  now apply perm_skip.
}
Qed.

Theorem Permutation_select_first : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ a a' b' la lb la' lb',
  Permutation la lb
  → select_first rel a la = (a', la')
  → select_first rel a lb = (b', lb')
  → a' = b' ∧ Permutation la' lb'.
Proof.
intros * Hant Htr Htot * Hab Ha Hb.
revert a a' b' la' lb' Ha Hb.
induction Hab; intros. {
  cbn in Ha, Hb.
  injection Ha; intros; subst a' la'.
  injection Hb; intros; subst b' lb'.
  easy.
} {
  cbn in Ha, Hb.
  remember (rel a x) as ax eqn:Hax; symmetry in Hax.
  remember (if ax then a else x) as y eqn:Hy.
  remember (select_first rel y l) as ld eqn:Hld.
  remember (select_first rel y l') as le eqn:Hle.
  symmetry in Hld, Hle.
  destruct ld as (d, ld).
  destruct le as (e, le).
  injection Ha; clear Ha; intros; subst d la'.
  injection Hb; clear Hb; intros; subst e lb'.
  specialize (IHHab _ _ _ _ _ Hld Hle) as H1.
  split; [ easy | ].
  now apply Permutation_cons.
} {
  cbn in Ha, Hb.
  remember (if rel a y then a else y) as u eqn:Hu.
  remember (if rel a x then a else x) as v eqn:Hv.
  remember (rel u x) as ux eqn:Hux.
  remember (rel v y) as vy eqn:Hvy.
  remember (rel a x) as ax eqn:Hax.
  remember (rel a y) as ay eqn:Hay.
  symmetry in Hux, Hvy, Hax, Hay.
  move a before y; move a' before a; move b' before a'.
  move u before b'; move v before u.
  move ax after ay; move ux before ay; move vy before ux.
  remember (select_first rel (if ux then u else x) l) as ld eqn:Hld.
  remember (select_first rel (if vy then v else y) l) as le eqn:Hle.
  symmetry in Hld, Hle.
  destruct ld as (d, ld).
  destruct le as (e, le).
  injection Ha; clear Ha; intros; subst a' la'.
  injection Hb; clear Hb; intros; subst b' lb'.
  destruct ax; subst v. {
    destruct ay; subst u. {
      rewrite Hax in Hux; subst ux.
      rewrite Hay in Hvy; subst vy.
      rewrite Hld in Hle.
      injection Hle; intros; subst e le.
      split; [ easy | apply perm_swap ].
    }
    rewrite Hay in Hvy; subst vy.
    destruct ux. {
      rewrite Hld in Hle.
      injection Hle; intros; subst e le.
      split; [ easy | apply perm_swap ].
    }
    specialize (Htot y x) as H1.
    rewrite Hux in H1; cbn in H1.
    specialize (Htot a y) as H2.
    rewrite Hay in H2; cbn in H2.
    specialize (Htr x y a H1 H2) as H3.
    apply (Hant _ _ Hax) in H3; subst x.
    apply (Hant _ _ H1) in H2; subst y.
    rewrite Hld in Hle.
    now injection Hle; intros; subst e le.
  } {
    destruct ay; subst u. {
      rewrite Hax in Hux; subst ux.
      destruct vy. {
        rewrite Hld in Hle.
        injection Hle; intros; subst e le.
        split; [ easy | apply perm_swap ].
      }
      specialize (Htot x y) as H1.
      rewrite Hvy in H1; cbn in H1.
      specialize (Htot a x) as H2.
      rewrite Hax in H2; cbn in H2.
      specialize (Htr y x a H1 H2) as H3.
      apply (Hant _ _ Hay) in H3; subst y.
      apply (Hant _ _ H1) in H2; subst x.
      rewrite Hld in Hle.
      now injection Hle; intros; subst e le.
    }
    destruct ux. {
      destruct vy. {
        specialize (Hant _ _ Hux Hvy) as H1; subst y.
        rewrite Hld in Hle.
        now injection Hle; intros; subst e le.
      }
      rewrite Hld in Hle.
      now injection Hle; intros; subst e le.
    }
    destruct vy. {
      rewrite Hld in Hle.
      now injection Hle; intros; subst e le.
    }
    specialize (Htot x y) as H1.
    now rewrite Hux, Hvy in H1.
  }
} {
  remember (select_first rel a l') as lc eqn:Hlc.
  symmetry in Hlc.
  destruct lc as (c, lc).
  specialize (IHHab1 _ _ _ _ _ Ha Hlc) as H1.
  specialize (IHHab2 _ _ _ _ _ Hlc Hb) as H2.
  destruct H2 as (H3, H4).
  destruct H1 as (H1, H2).
  split; [ congruence | ].
  now transitivity lc.
}
Qed.

Theorem Permutation_ssort_loop : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ it la lb,
  length la = length lb
  → length la ≤ it
  → Permutation la lb
  → ssort_loop rel it la = ssort_loop rel it lb.
Proof.
intros * Hant Htr Htot * Hlab Hit Hab.
revert la lb Hlab Hit Hab.
induction it; intros; cbn. {
  apply Nat.le_0_r, length_zero_iff_nil in Hit; subst la.
  symmetry in Hlab.
  now apply length_zero_iff_nil in Hlab; subst lb.
}
destruct la as [| a]. {
  symmetry in Hlab.
  now apply length_zero_iff_nil in Hlab; subst lb.
}
destruct lb as [| b]; [ easy | ].
cbn in Hlab; apply Nat.succ_inj in Hlab.
cbn in Hit; apply Nat.succ_le_mono in Hit.
remember (select_first rel a la) as la' eqn:Hla'.
symmetry in Hla'.
destruct la' as (a', la').
remember (select_first rel b lb) as lb' eqn:Hlb'.
symmetry in Hlb'.
destruct lb' as (b', lb').
move b' before a'; move lb' before la'.
inversion Hab; subst. {
  rename H0 into Hpab.
  specialize (Permutation_select_first Hant Htr Htot) as H1.
  specialize (H1 _ _ _ _ _ _ _ Hpab Hla' Hlb').
  destruct H1 as (H1, H2); subst b'; f_equal.
  apply IHit; [ | | easy ]. {
    apply select_first_length in Hla', Hlb'; congruence.
  } {
    apply select_first_length in Hla', Hlb'; congruence.
  }
} {
  cbn in Hla', Hlb'.
  rename Hab into Hpab.
  remember (rel a b) as ab eqn:Hab; symmetry in Hab.
  remember (rel b a) as ba eqn:Hba; symmetry in Hba.
  remember (if ab then a else b) as abab eqn:Habab.
  remember (if ba then b else a) as baba eqn:Hbaba.
  remember (select_first rel abab l) as lc eqn:Hlc.
  remember (select_first rel baba l) as ld eqn:Hld.
  symmetry in Hlc, Hld.
  destruct lc as (c, lc).
  destruct ld as (d, ld).
  injection Hla'; clear Hla'; intros; subst c la'.
  injection Hlb'; clear Hlb'; intros; subst d lb'.
  destruct ab; subst abab. {
    destruct ba; subst baba. {
      specialize (Hant _ _ Hab Hba) as H1; subst b.
      rewrite Hlc in Hld.
      now injection Hld; intros; subst b' ld.
    }
    rewrite Hlc in Hld.
    now injection Hld; intros; subst b' ld.
  } {
    destruct ba; subst baba. {
      rewrite Hlc in Hld.
      now injection Hld; intros; subst b' ld.
    }
    specialize (Htot a b) as H1.
    now rewrite Hab, Hba in H1.
  }
} {
  rename l' into l.
  rename H into Haal.
  rename H0 into Hlbb.
  specialize (select_first_length rel a la Hla') as H1.
  specialize (select_first_length rel b lb Hlb') as H2.
  assert (Hab' : a' = b'). {
    apply (select_first_if Htr Htot) in Hla', Hlb'.
    destruct Hla' as (Hla1 & Hla2 & Hla3).
    destruct Hlb' as (Hlb1 & Hlb2 & Hlb3).
    specialize (Hla1 b') as H3.
    assert (H : b' ∈ a :: la). {
      apply perm_trans with (l := a :: la) in Hlb3; [ | easy ].
      apply Permutation_sym in Hlb3.
      specialize (Permutation_in b' Hlb3 (or_introl eq_refl)) as H4.
      easy.
    }
    specialize (H3 H); clear H.
    specialize (Hlb1 a') as H4.
    assert (H : a' ∈ b :: lb). {
      apply perm_trans with (l := b :: lb) in Hla3; [ | easy ].
      apply Permutation_sym in Hla3.
      specialize (Permutation_in a' Hla3 (or_introl eq_refl)) as H5.
      easy.
    }
    specialize (H4 H); clear H.
    now apply Hant.
  }
  subst b'; f_equal.
  apply IHit; [ congruence | congruence | ].
  apply (select_first_if Htr Htot) in Hla', Hlb'.
  destruct Hla' as (Hla1 & Hla2 & Hla3).
  destruct Hlb' as (Hlb1 & Hlb2 & Hlb3).
  apply Permutation_trans with (l := a' :: la') in Hab; [ | easy ].
  apply Permutation_sym in Hab, Hlb3.
  apply Permutation_trans with (l := a' :: lb') in Hab; [ | easy ].
  now apply Permutation_cons_inv, Permutation_sym in Hab.
}
Qed.

Theorem ssort_loop_Permutation : ∀ A (rel : A → _) la lb len,
  length la ≤ len
  → ssort_loop rel len la = lb
  → Permutation la lb.
Proof.
intros * Hlen Hs.
revert la lb Hlen Hs.
induction len; intros. {
  apply Nat.le_0_r, length_zero_iff_nil in Hlen; subst la.
  now cbn in Hs; subst lb.
}
cbn in Hs.
destruct la as [| a]; [ now subst lb | ].
cbn in Hlen; apply Nat.succ_le_mono in Hlen.
remember (select_first rel a la) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as (c, lc).
destruct lb as [| b]; [ easy | ].
injection Hs; clear Hs; intros Hs H; subst c.
specialize (IHlen lc lb) as H1.
assert (H : length lc ≤ len). {
  apply select_first_length in Hlc.
  congruence.
}
specialize (H1 H Hs); clear H.
apply (select_first_Permutation rel) in Hlc.
transitivity (b :: lc); [ easy | ].
now constructor.
Qed.

Theorem ssort_loop_is_sorted : ∀ A (rel : A → _),
  transitive rel →
  total_relation rel →
  ∀ l len,
  length l ≤ len
  → sorted rel (ssort_loop rel len l) = true.
Proof.
intros * Htr Htot * Hlen.
revert l Hlen.
induction len; intros; cbn. {
  now apply Nat.le_0_r, length_zero_iff_nil in Hlen; subst l.
}
destruct l as [| a la]; [ easy | cbn ].
cbn in Hlen; apply Nat.succ_le_mono in Hlen.
remember (select_first rel a la) as lb eqn:Hlb.
symmetry in Hlb.
destruct lb as (b, lb); cbn.
remember (ssort_loop rel len lb) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [| c]; [ easy | ].
apply Bool.andb_true_iff.
split. 2: {
  rewrite <- Hlc.
  apply IHlen.
  apply select_first_length in Hlb.
  congruence.
}
apply Bool.not_false_iff_true.
intros Hbc.
specialize (Htot b c) as Hcb.
rewrite Hbc in Hcb; cbn in Hcb.
apply ssort_loop_Permutation in Hlc. 2: {
  apply select_first_length in Hlb.
  congruence.
}
apply (select_first_if Htr Htot) in Hlb.
destruct Hlb as (_ & H2 & _).
specialize (H2 c).
assert (H : c ∈ lb). {
  apply Permutation_sym in Hlc.
  apply Permutation_in with (l := c :: lc); [ easy | now left ].
}
specialize (H2 H); clear H.
now rewrite H2 in Hbc.
Qed.

Theorem sorted_bsort_swap : ∀ A (rel : A → _),
  ∀ it la,
  sorted rel la = true
  → bsort_swap rel it la = None.
Proof.
intros * Hs.
revert la Hs.
induction it; intros; [ easy | cbn ].
destruct la as [| a]; [ easy | ].
destruct la as [| b]; [ easy | ].
remember (b :: la) as lb; cbn in Hs; subst lb.
apply Bool.andb_true_iff in Hs.
destruct Hs as (Hab, Hs).
rewrite Hab.
now rewrite IHit.
Qed.

Theorem sorted_bsort_loop : ∀ A (rel : A → _),
  ∀ it l,
  sorted rel l = true
  → bsort_loop rel it l = l.
Proof.
intros * Hs.
rename l into la.
revert la Hs.
induction it; intros; [ easy | cbn ].
remember (bsort_swap rel (length la) la) as lb eqn:Hlb.
symmetry in Hlb.
destruct lb as [lb| ]; [ | easy ].
now rewrite sorted_bsort_swap in Hlb.
Qed.

(* *)

Theorem sorted_isort : ∀ A (rel : A → _),
  antisymmetric rel →
  transitive rel →
  ∀ l,
  sorted rel l = true
  → isort rel l = l.
Proof.
intros * Hant Htra * Hs.
now apply sorted_isort_loop.
Qed.

Theorem sorted_ssort : ∀ A (rel : A → _),
  transitive rel → ∀ l,
  sorted rel l = true
  → ssort rel l = l.
Proof.
intros * Htr * Hs.
unfold ssort.
now apply sorted_ssort_loop.
Qed.

Theorem sorted_bsort : ∀ A (rel : A → _),
  ∀ l,
  sorted rel l = true
  → bsort rel l = l.
Proof.
intros * Hs.
now apply sorted_bsort_loop.
Qed.

(* *)

Theorem isort_is_sorted : ∀ A (rel : A → _),
  total_relation rel
  → ∀ l, sorted rel (isort rel l) = true.
Proof.
intros * Hto *.
destruct l as [| a]; [ easy | cbn ].
now apply isort_loop_is_sorted.
Qed.

Theorem ssort_is_sorted : ∀ A (rel : A → _),
  transitive rel →
  total_relation rel →
  ∀ l, sorted rel (ssort rel l) = true.
Proof.
intros * Htr Htot *.
now apply ssort_loop_is_sorted.
Qed.

(* *)

Theorem bsort_swap_Some : ∀ A (rel : A → _) it la lb,
  length la ≤ it
  → bsort_swap rel it la = Some lb
  → length la = length lb ∧
    ∃ lab a b la1 lb1 , rel a b = false ∧
    sorted rel (lab ++ [a]) = true ∧
    la = lab ++ a :: b :: la1 ∧
    lb = lab ++ b :: a :: lb1 ∧
    Permutation la1 lb1.
Proof.
intros * Hit Hs.
revert la lb Hit Hs.
induction it; intros; [ easy | ].
cbn in Hs.
destruct la as [| a]; [ easy | ].
cbn in Hit; apply Nat.succ_le_mono in Hit.
destruct la as [| b]; [ easy | ].
remember (rel a b) as ab eqn:Hab; symmetry in Hab.
remember (bsort_swap rel it _) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [lc| ]. 2: {
  destruct ab; [ easy | ].
  injection Hs; clear Hs; intros; subst lb.
  split; [ easy | ].
  now exists [], a, b, la, la.
}
destruct ab. 2: {
  injection Hs; clear Hs; intros; subst lb.
  split; [ easy | ].
  now exists [], a, b, la, la.
}
injection Hs; clear Hs; intros; subst lb.
specialize (IHit (b :: la) lc Hit Hlc) as H1.
destruct H1 as (Hll & H1).
destruct H1 as (lab & c & d & la1 & la2 & Hcd & Hs & Hbla & Hlcl & Hab1).
cbn in Hll |-*.
rewrite Hll.
split; [ easy | ].
exists (a :: lab), c, d, la1, la2.
rewrite Hbla, Hlcl.
split; [ easy | ].
split; [ cbn | easy ].
destruct lab as [| e]. {
  cbn in Hbla |-*.
  injection Hbla; clear Hbla; intros Hbla H; subst c.
  now rewrite Hab.
}
cbn in Hbla.
injection Hbla; clear Hbla; intros Hbla H; subst e.
now rewrite Hs; cbn; rewrite Hab.
Qed.

(* to be completed
Theorem sorted_bsort_loop_app : ∀ A (rel : A → _),
  transitive rel →
  total_relation rel →
  ∀ a b la lb it,
  sorted rel (bsort_loop rel it (la ++ [a])) = true
  → sorted rel (bsort_loop rel it (b :: lb)) = true
  → rel a b = true
  → sorted rel (bsort_loop rel it (la ++ a :: b :: lb)) = true.
Proof.
intros * Htra Htot * Hsa Hsb Hab.
revert a b la lb Hsa Hsb Hab.
induction it; intros; cbn. {
  remember (b :: lb) as l.
  cbn in Hsa, Hsb; subst l.
  do 2 rewrite List_app_cons.
  rewrite app_assoc.
  apply (sorted_app_iff Htra).
  split; [ easy | ].
  split; [ easy | ].
  intros c d Hc Hd.
  apply in_app_or in Hc, Hd.
  destruct Hc as [Hc| Hc]. {
    apply (sorted_app_iff Htra) in Hsa.
    destruct Hsa as (Hsa & _ & Hba).
    destruct Hd as [Hd| Hd]. {
      destruct Hd; [ subst d | easy ].
      apply (Htra _ a); [ | easy ].
      apply Hba; [ easy | now left ].
    }
    apply (Htra _ b). {
      apply (Htra _ a); [ | easy ].
      apply Hba; [ easy | now left ].
    }
    now apply (sorted_extends Htra _ _ Hsb).
  }
  destruct Hc; [ subst c | easy ].
  destruct Hd as [Hd| Hd]. {
    destruct Hd; [ now subst d | easy ].
  }
  apply (Htra _ b); [ easy | ].
  now apply (sorted_extends Htra _ _ Hsb).
}
remember (b :: lb) as lc; cbn in Hsa, Hsb; subst lc.
rewrite app_length; cbn.
rewrite Nat.add_comm; cbn.
remember (la ++ a :: b :: lb) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [| c]; [ easy | ].
destruct lc as [| d]; [ easy | ].
remember (rel c d) as cd eqn:Hcd.
symmetry in Hcd.
destruct cd. {
  destruct lc as [| e]; [ now cbn; rewrite Hcd | ].
  remember (rel d e) as de eqn:Hde.
  symmetry in Hde.
  destruct de. {
    remember (bsort_swap rel (length lb + length la) (e :: lc)) as lf eqn:Hlf.
    symmetry in Hlf.
    destruct lf as [lf| ]. {
      apply bsort_swap_Some in Hlf. 2: {
        cbn.
        apply (f_equal length) in Hlc.
        rewrite app_length in Hlc.
        cbn in Hlc; flia Hlc.
      }
      destruct Hlf as (Hlen & lab & f & g & la1 & lb1 & Hfg & Hsf & He & Hf & Hpab).
      subst lf.
      do 2 rewrite app_comm_cons.
      apply IHit. 3: {
        specialize (Htot f g) as Hgf.
        now rewrite Hfg in Hgf.
      } 2: {
(* quel bordel ! *)
...

Theorem bsort_loop_is_sorted : ∀ A (rel : A → _),
  total_relation rel →
  ∀ it l,
  length l * length l ≤ it
  → sorted rel (bsort_loop rel it l) = true.
Proof.
intros * Htot * Hit.
revert l Hit.
induction it; intros. {
  apply Nat.le_0_r, Nat.eq_mul_0 in Hit.
  assert (H : length l = 0) by now destruct Hit.
  now apply length_zero_iff_nil in H; subst l.
}
cbn.
remember (bsort_swap rel (length l) l) as lb eqn:Hlb.
symmetry in Hlb.
destruct lb as [lb| ]. 2: {
  clear - Hlb.
  remember (length l) as it eqn:H.
  assert (Hit : length l ≤ it) by flia H.
  clear - Hit Hlb.
  revert l Hit Hlb.
  induction it; intros. {
    now apply Nat.le_0_r, length_zero_iff_nil in Hit; subst l.
  }
  cbn in Hlb.
  destruct l as [| a]; [ easy | ].
  destruct l as [| b]; [ easy | ].
  remember (b :: l) as l'; cbn in Hit; subst l'.
  apply Nat.succ_le_mono in Hit.
  remember (rel a b) as ab eqn:Hab; symmetry in Hab.
  destruct ab. {
    specialize (IHit _ Hit) as H1.
    remember (b :: l) as l'; cbn; subst l'.
    apply Bool.andb_true_iff.
    split; [ easy | ].
    apply H1.
    now destruct (bsort_swap rel it (b :: l)).
  }
  now destruct (bsort_swap rel it (a :: l)).
}
specialize (bsort_swap_Some rel) as H1.
specialize (H1 (length l) l lb (le_refl _) Hlb).
destruct H1 as (Hll, H1).
destruct H1 as (lab & a & b & la1 & lb1 & Hab & Hs & Hla1 & Hlb1 & Hlab).
rewrite Hlb1.
remember (lab ++ [b]) as lb2 eqn:Hlb2.
specialize (IHit lb2) as H1.
assert (H : length lb2 * length lb2 ≤ it). {
  subst lb2.
  rewrite Hla1 in Hit.
  move Hit at bottom.
  rewrite app_length in Hit.
  cbn in Hit |-*.
  assert (H : length la1 = length lb1). {
    apply (f_equal length) in Hla1, Hlb1.
    rewrite app_length in Hla1, Hlb1.
    rewrite  Hll in Hla1.
    cbn in Hla1, Hlb1.
    flia Hla1 Hlb1.
  }
  rewrite H in Hit.
  rewrite app_length; cbn.
  flia Hit.
}
specialize (H1 H); clear H.
subst lb2.
remember (a :: lb1) as lb2 eqn:Hlb2.
specialize (IHit lb2) as H2.
assert (H : length lb2 * length lb2 ≤ it). {
  subst lb2.
  rewrite Hla1 in Hit.
  move Hit at bottom.
  rewrite app_length in Hit.
  cbn in Hit |-*.
  assert (H : length la1 = length lb1). {
    apply (f_equal length) in Hla1, Hlb1.
    rewrite app_length in Hla1, Hlb1.
    rewrite  Hll in Hla1.
    cbn in Hla1, Hlb1.
    flia Hla1 Hlb1.
  }
  rewrite H in Hit.
  flia Hit.
}
specialize (H2 H); clear H.
subst lb2.
specialize (Htot a b) as Hba.
rewrite Hab in Hba; cbn in Hba.
...
now apply sorted_bsort_loop_app.
...

Theorem bsort_is_sorted : ∀ A (rel : A → _),
  ∀ l, sorted rel (bsort rel l) = true.
Proof.
intros.
unfold bsort.
...
now apply bsort_loop_is_sorted.
Qed.
*)

Theorem isort_loop_ssort_loop : ∀ A rel,
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ (ls l : list A) it,
  it = length (ls ++ l)
  → sorted rel ls = true
  → isort_loop rel ls l = ssort_loop rel it (ls ++ l).
Proof.
intros * Hant Htr Htot * Hit Hs.
subst it.
revert ls Hs.
induction l as [| a]; intros. {
  cbn; rewrite app_nil_r.
  now symmetry; apply sorted_ssort.
}
cbn.
rewrite IHl; [ | now apply isort_insert_is_sorted ].
do 2 rewrite app_length.
rewrite isort_insert_length.
rewrite List_length_cons, <- Nat.add_succ_comm.
apply (Permutation_ssort_loop Hant Htr Htot). {
  do 2 rewrite app_length.
  rewrite isort_insert_length.
  now rewrite Nat.add_succ_comm.
} {
  now rewrite app_length, isort_insert_length.
}
apply Permutation_sym.
transitivity (a :: ls ++ l). 2: {
  rewrite app_comm_cons.
  apply Permutation_app; [ | easy ].
  now apply Permutation_cons_isort_insert.
}
rewrite app_comm_cons.
rewrite List_app_cons, app_assoc.
apply Permutation_app; [ | easy ].
apply Permutation_app_comm.
Qed.

(* isort and ssort return same *)

Theorem isort_ssort : ∀ (A : Type) (rel : A → A → bool),
  antisymmetric rel →
  transitive rel →
  total_relation rel →
  ∀ (l : list A),
  isort rel l = ssort rel l.
Proof.
intros * Hant Htr Htot *.
now apply isort_loop_ssort_loop.
Qed.

(* *)

Theorem Nat_leb_is_total_relation : total_relation Nat.leb.
Proof.
intros i j.
apply Bool.orb_true_iff.
destruct (le_dec i j) as [Hij| Hij]. {
  now apply Nat.leb_le in Hij; rewrite Hij; left.
} {
  apply Nat.nle_gt, Nat.lt_le_incl in Hij.
  now apply Nat.leb_le in Hij; rewrite Hij; right.
}
Qed.

Theorem Nat_leb_refl : reflexive Nat.leb.
Proof.
intros a.
apply Nat.leb_refl.
Qed.

Theorem Nat_leb_antisym : antisymmetric Nat.leb.
Proof.
intros a b Hab Hba.
apply Nat.leb_le in Hab, Hba.
now apply le_antisym.
Qed.

Theorem Nat_leb_trans : transitive Nat.leb.
Proof.
intros a b c Hab Hbc.
apply Nat.leb_le in Hab, Hbc.
apply Nat.leb_le.
now transitivity b.
Qed.

Theorem Nat_ltb_trans : transitive Nat.ltb.
Proof.
intros a b c Hab Hbc.
apply Nat.ltb_lt in Hab, Hbc.
apply Nat.ltb_lt.
now transitivity b.
Qed.

Theorem sorted_middle : ∀ A rel (a b : A) la lb lc,
  transitive rel
  → sorted rel (la ++ a :: lb ++ b :: lc) = true
  → rel a b = true.
Proof.
intros * Htrans Hsort.
replace (la ++ a :: lb ++ b :: lc) with (la ++ [a] ++ lb ++ [b] ++ lc)
  in Hsort by easy.
rewrite app_assoc in Hsort.
apply sorted_app in Hsort.
destruct Hsort as (Hla & Hsort & H1).
specialize (H1 Htrans).
apply H1; [ now apply in_or_app; right; left | ].
apply in_or_app; right.
now apply in_or_app; left; left.
Qed.

Theorem sorted_any : ∀ A (rel : A → A → bool) i j d l,
  transitive rel
  → sorted rel l = true
  → i < j
  → j < length l
  → rel (nth i l d) (nth j l d) = true.
Proof.
intros * Htrans Hsort Hij Hj.
assert (Hi : i < length l) by now transitivity j.
specialize nth_split as H1.
specialize (H1 A i l d Hi).
destruct H1 as (la & lb & Hl & Hla).
remember (nth i l d) as a eqn:Ha; clear Ha.
subst l i.
rewrite List_app_cons, app_assoc.
rewrite app_nth2; rewrite app_length, Nat.add_comm; cbn; [ | easy ].
remember (j - S (length la)) as k eqn:Hkj.
assert (Hk : k < length lb). {
  subst k.
  rewrite app_length in Hj; cbn in Hj.
  flia Hj Hij.
}
specialize nth_split as H1.
specialize (H1 A k lb d Hk).
destruct H1 as (lc & ld & Hl & Hlc).
remember (nth k lb d) as b eqn:Hb.
subst lb.
clear j k Hb Hij Hj Hkj Hk Hlc Hi.
rename lc into lb; rename ld into lc.
now apply sorted_middle in Hsort.
Qed.

Theorem sorted_ltb_leb_incl : ∀ l,
  sorted Nat.ltb l = true → sorted Nat.leb l = true.
Proof.
intros * Hs.
induction l as [| a]; [ easy | ].
cbn - [ Nat.ltb ] in Hs |-*.
destruct l as [| b]; [ easy | ].
apply Bool.andb_true_iff in Hs.
apply Bool.andb_true_iff.
destruct Hs as (Hab, Hs).
split; [ | now apply IHl ].
apply Nat.ltb_lt in Hab.
now apply Nat.leb_le, Nat.lt_le_incl.
Qed.

Theorem nth_isort_rank_insert_of_sorted :
  ∀ A d (rel : A → _) l_ini n ls,
  (∀ i, i ∈ ls → rel (nth n l_ini d) (nth i l_ini d) = false)
  → isort_rank_insert rel (λ j : nat, nth j l_ini d) n ls = ls ++ [n].
Proof.
intros * Hls.
induction ls as [| b]; [ easy | cbn ].
rewrite Hls; [ | now left ].
f_equal.
apply IHls.
intros j Hj.
apply Hls.
now right.
Qed.

Theorem nth_isort_rank_loop_of_nodup_sorted : ∀ A d (rel : A → _),
  antisymmetric rel
  → transitive rel
  → ∀ l_ini n l i,
  NoDup l_ini
  → sorted rel l_ini = true
  → n + length l = length l_ini
  → i < length l_ini
  → nth i (isort_rank_loop rel (λ j, nth j l_ini d) (seq 0 n) l) 0 = i.
Proof.
intros * Hant Htra * Hndi Hsi Hnl Hil.
revert n Hnl.
induction l; intros; cbn. {
  rewrite seq_nth; [ easy | ].
  now rewrite Nat.add_0_r in Hnl; subst n.
}
rewrite seq_length.
replace (isort_rank_insert _ _ _ _) with (seq 0 (S n)). 2: {
  symmetry.
  rewrite nth_isort_rank_insert_of_sorted; try easy. {
    symmetry; apply seq_S.
  }
  intros j Hj.
  apply in_seq in Hj.
  destruct Hj as (_, Hj); cbn in Hj.
  enough (H : rel (nth j l_ini d) (nth n l_ini d) = true). {
    specialize (Hant (nth j l_ini d) (nth n l_ini d) H) as H1.
    apply Bool.not_true_is_false.
    intros H'.
    specialize (H1 H').
    clear H H'.
    apply NoDup_nth in H1; [ | easy | | ]; cycle 1. {
      rewrite <- Hnl; cbn; flia Hj.
    } {
      rewrite <- Hnl; cbn; flia.
    }
    flia Hj H1.
  }
  apply sorted_any; [ easy | easy | easy | ].
  rewrite <- Hnl; cbn; flia.
}
cbn in Hnl.
rewrite <- Nat.add_succ_comm in Hnl.
now apply IHl.
Qed.

Theorem nth_isort_rank_of_nodup_sorted : ∀ A (rel : A → _),
  antisymmetric rel
  → transitive rel
  → ∀ l i,
  NoDup l
  → sorted rel l = true
  → i < length l
  → nth i (isort_rank rel l) 0 = i.
Proof.
intros * Hant Htra * Hnd Hs Hil.
destruct l as [| d]; [ easy | ].
cbn - [ isort_rank_loop nth ].
remember (d :: l) as l' eqn:Hl'.
clear l Hl'; rename l' into l.
replace [] with (seq 0 0) by easy.
now apply nth_isort_rank_loop_of_nodup_sorted.
Qed.

Theorem isort_rank_of_nodup_sorted : ∀ A (rel : A → _),
  antisymmetric rel
  → transitive rel
  → ∀ l,
  NoDup l
  → sorted rel l = true
  → isort_rank rel l = seq 0 (length l).
Proof.
intros * Hant Htra * Hnd Hs.
apply List_eq_iff.
rewrite isort_rank_length, seq_length.
split; [ easy | ].
intros d i.
destruct (lt_dec i (length l)) as [Hil| Hil]. 2: {
  apply Nat.nlt_ge in Hil.
  rewrite nth_overflow; [ | now rewrite isort_rank_length ].
  rewrite nth_overflow; [ | now rewrite seq_length ].
  easy.
}
rewrite seq_nth; [ cbn | easy ].
rewrite nth_indep with (d' := 0); [ | now rewrite isort_rank_length ].
clear d.
now apply nth_isort_rank_of_nodup_sorted.
Qed.

(* end sorted *)

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
