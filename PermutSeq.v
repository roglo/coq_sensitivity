(* permutations of sequences of natural numbers between 1 and n *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Bool.
Import List List.ListNotations.
Require Import Permutation.

Require Import Misc.
Require Import IterAnd.
Require Import Pigeonhole.

Definition ff_app l i := nth i l 0.

Definition comp {A B C} (f : B → C) (g : A → B) x := f (g x).
Definition comp_list (la lb : list nat) := map (ff_app la) lb.

(*
Theorem fold_ff_app : ∀ f i, nth i f 0 = ff_app f i.
Proof. easy. Qed.
*)

(*
Compute (comp_list [0;2;1] [2;1;0]).
Compute (map (comp (λ i, nth i [0;2;1] 0) (λ i, nth i [2;1;0] 0)) [0;1;2]).
*)

Notation "σ₁ ° σ₂" := (comp_list σ₁ σ₂) (at level 40).

Notation "'Comp' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, comp c g) (λ i, i))
  (at level 35, i at level 0, l at level 60).

(* Permutations of {0, 1, 2, ... n-1} *)

Definition is_permut_list l :=
  (∀ x, x ∈ l → x < length l) ∧
  (∀ i j, i < length l → j < length l → ff_app l i = ff_app l j → i = j).

Definition is_permut_list_bool l :=
  (⋀ (a ∈ l), (a <? length l)) &&
  (⋀ (i = 1, length l),
     (⋀ (j = 1, length l),
        ((ff_app l (i - 1) ≠? ff_app l (j - 1)) || (i =? j)))).

Definition is_permut n f := is_permut_list f ∧ length f = n.

Theorem List_map_ff_app_seq : ∀ l, l = map (ff_app l) (seq 0 (length l)).
Proof. intros; apply List_map_nth_seq. Qed.

Theorem is_permut_list_is_permut_list_bool : ∀ l,
  is_permut_list l ↔ is_permut_list_bool l = true.
Proof.
intros.
split. {
  intros (H1, H2).
  unfold is_permut_list_bool.
  apply andb_true_iff.
  split. {
    apply all_true_and_list_true_iff.
    intros i Hi.
    apply Nat.ltb_lt.
    now apply H1.
  } {
    apply all_true_and_seq_true_iff.
    intros i Hi.
    apply all_true_and_seq_true_iff.
    intros j Hj.
    apply orb_true_iff.
    specialize (H2 (i - 1) (j - 1)) as H3.
    assert (H : i - 1 < length l) by flia Hi.
    specialize (H3 H); clear H.
    assert (H : j - 1 < length l) by flia Hj.
    specialize (H3 H); clear H.
    destruct (Nat.eq_dec i j) as [Hij| Hij]. {
      subst j.
      now right; rewrite Nat.eqb_eq.
    }
    left.
    apply negb_true_iff.
    apply Nat.eqb_neq.
    intros H.
    specialize (H3 H).
    flia Hi Hj H3 Hij.
  }
} {
  intros Hb.
  unfold is_permut_list_bool in Hb.
  apply andb_true_iff in Hb.
  destruct Hb as (H1, H2).
  split. {
    intros i Hi.
    specialize (proj2 (all_true_and_list_true_iff _ _ _) H1) as H3.
    specialize (H3 _ Hi).
    now apply Nat.ltb_lt.
  } {
    clear H1.
    intros i j Hi Hj Hij.
    specialize (proj2 (all_true_and_list_true_iff _ _ _) H2) as H3.
    rewrite Nat_sub_succ_1 in H3.
    specialize (H3 (S i)).
    rewrite Nat_sub_succ_1 in H3.
    assert (H : S i ∈ seq 1 (length l)) by (apply in_seq; flia Hi).
    specialize (H3 H); clear H.
    specialize (proj2 (all_true_and_list_true_iff _ _ _) H3) as H4.
    rewrite Nat_sub_succ_1 in H4.
    specialize (H4 (S j)).
    rewrite Nat_sub_succ_1 in H4; cbn in H4.
    assert (H : S j ∈ seq 1 (length l)) by (apply in_seq; flia Hj).
    specialize (H4 H); clear H.
    apply orb_true_iff in H4.
    rewrite Nat.eqb_eq in H4.
    destruct H4 as [H4| H4]; [ | easy ].
    apply negb_true_iff in H4.
    now apply Nat.eqb_neq in H4.
  }
}
Qed.

(*
   Canonical Symmetric Group.

   In set theory, there is one only symmetric group of order n.

   Here, a symmetric group (of order n) is a list of n! permutations,
   which can be ordered in any order. There are actually n!! (factorial
   of factorial n) possible orders.

   There is one that we call "canonical" because the generated permutation
   are in alphabetic order.

   The canonical symmetric group is built this way. The k-th permutation
   is a vector of size n where
   - the first value is k/fact(n-1)
   - the rest is the (k mod fact(n-1))-th permutation of n-1 values
     (from 0 to n-2) where
     * all values less than the first value (k/fact(n-1)) are unchanged
     * all values greater or equal to it are increased by 1
   Example. For n=4 and k=0
   - first value: 0
   - rest: shift of 0;1;2 by 1, i.e. 1;2;3
   Result : 0;1;2;3
   Other example. For n=4 and k=13
   - first value: 13/3! = 13/6 = 2
   - rest: k' = 13 mod 3! = 13 mod 6 = 1 for n'=3, resulting 0;2;1
     0 and 1 are not shifted (both < 2), 2 is shifted, resulting 0;3;1
     final result: 2;0;3;1
  *)

(*
Definition canon_sym_gr_fun n (σ_n : nat → nat → nat) k j : nat :=
  match j with
  | 0 => k / n!
  | S j' => σ_n (k mod n!) j' + Nat.b2n (k / n! <=? σ_n (k mod n!) j')
  end.

Fixpoint canon_sym_gr_elem n : nat → nat → nat :=
  match n with
  | 0 => λ _ _, 0
  | S n' => canon_sym_gr_fun n' (canon_sym_gr_elem n')
  end.

Definition canon_sym_gr n : vector (vector nat) :=
  mk_vect
    (map (λ k, mk_vect (map (canon_sym_gr_elem n k) (seq 0 n))) (seq 0 n!)).
*)

Definition succ_when_ge k a := a + Nat.b2n (k <=? a).

(* k-th canonic permutation of order n *)
Fixpoint canon_sym_gr_list n k : list nat :=
  match n with
  | 0 => []
  | S n' =>
      k / n'! ::
      map (succ_when_ge (k / n'!)) (canon_sym_gr_list n' (k mod n'!))
  end.

(* all canonic permutations *)
Definition canon_sym_gr_list_list n : list (list nat) :=
  map (canon_sym_gr_list n) (seq 0 n!).

(*
Compute (let n := 4 in map (canon_sym_gr_list n) (seq 0 n!)).
Compute (let n := 3 in ((*canon_sym_gr n,*) canon_sym_gr_vect n)).
*)

Definition is_sym_gr_list n (ll : list (list nat)) :=
  (∀ i, i < length ll →
   length (nth i ll []) = n ∧
   is_permut_list (nth i ll [])) ∧
  (∀ i j, i < length ll → j < length ll →
   nth i ll [] = nth j ll [] → i = j) ∧
  (∀ l, length l = n → is_permut_list l → l ∈ ll).

(*
Definition vect_vect_nat_el (V : vector (vector nat)) i : vector nat :=
  nth i (vect_list V) empty_vect.
*)

(*
Fixpoint permut_fun_inv_loop f i j :=
  match i with
  | 0 => 42
  | S i' => if Nat.eq_dec (f i') j then i' else permut_fun_inv_loop f i' j
  end.

Definition permut_vect_inv (σ : vector nat) :=
  mk_vect
    (map (permut_fun_inv_loop (vect_el 0 σ) (vect_size σ))
       (seq 0 (vect_size σ))).
*)

(**)
Definition permut_list_inv l :=
  map (λ i, unsome 0 (List_find_nth (Nat.eqb i) l)) (seq 0 (length l)).
(**)

(* Computation of the inverse of a permutation by using the pigeonhole
   principle.
Fixpoint find_dup' f (la : list nat) :=
  match la with
  | [] => 0
  | n :: la' =>
      match find (λ n', f n' =? f n) la' with
      | None => find_dup' f la'
      | Some _ => n
      end
  end.

Definition permut_list_inv'' l :=
  map
    (λ i,
     find_dup' (λ j, if Nat.eq_dec j (length l) then i else nth j l 0)
       (seq 0 (S (length l))))
   (seq 0 (length l)).

Definition permut_list_inv' l :=
  map
    (λ i,
     fst (pigeonhole_fun (S (length l)) (λ j, nth j (l ++ [i]) 0)))
    (seq 0 (length l)).
*)

(*
Definition permut_list_inv' l :=
  map
    (λ i,
     let '(x, x') :=
       pigeonhole_fun (S (length l))
         (λ j, if Nat.eq_dec j (length l) then i else nth j l 0)
     in
x)
(*
     if Nat.eq_dec x (length l) then x' else x)
*)
    (seq 0 (length l)).
*)

(*
Compute (let n := 4 in canon_sym_gr_list n 3).
Compute (let n := 4 in map (λ i, let v := nth i (canon_sym_gr_list_list n) [] in (v, permut_list_inv v)) (seq 0 n!)).
Compute (let n := 4 in map (λ i, let v := nth i (canon_sym_gr_list_list n) [] in (permut_list_inv v, permut_list_inv' v)) (seq 0 (n! + 14))).
Compute (let n := 4 in map (λ i, let v := nth i (canon_sym_gr_list_list n) [] in list_eqb Nat.eqb (permut_list_inv v) (permut_list_inv' v)) (seq 0 (n! + 14))).
*)

(* *)

Theorem permut_list_without : ∀ n l,
  is_permut_list l
  → n < length l
  → (∀ i, i < length l → nth i l 0 ≠ n)
  → False.
Proof.
intros * Hp Hn Hnn.
destruct Hp as (Hp1, Hp2).
specialize (pigeonhole_list (length l) (n :: l)) as H1.
specialize (H1 (Nat.lt_succ_diag_r _)).
assert (H : ∀ x, x ∈ n :: l → x < length l). {
  intros z Hz.
  destruct Hz as [Hz| Hz]; [ now subst z | now apply Hp1 ].
}
specialize (H1 H); clear H.
remember (pigeonhole_comp_list (n :: l)) as xx eqn:Hxx.
symmetry in Hxx.
destruct xx as (x, x').
specialize (H1 x x' eq_refl).
destruct H1 as (Hxl & Hx'l & Hxx' & Hnxx).
destruct x. {
  destruct x'; [ easy | cbn in Hnxx ].
  cbn in Hx'l; apply Nat.succ_lt_mono in Hx'l.
  specialize (Hnn x' Hx'l).
  now symmetry in Hnxx.
} {
  cbn in Hxl; apply Nat.succ_lt_mono in Hxl.
  destruct x'. {
    cbn in Hnxx.
    now specialize (Hnn x Hxl).
  }
  cbn in Hnxx.
  cbn in Hx'l; apply Nat.succ_lt_mono in Hx'l.
  specialize (Hp2 x x' Hxl Hx'l Hnxx) as H1.
  now destruct H1.
}
Qed.

Theorem permut_inv_permut : ∀ n l i,
  is_permut n l
  → i < n
  → ff_app (permut_list_inv l) (ff_app l i) = i.
Proof.
intros * (Hp, Hl) Hin.
revert i l Hp Hl Hin.
induction n; intros; [ easy | cbn ].
destruct l as [| a]; [ easy | ].
destruct i. {
  unfold ff_app.
  rewrite List_nth_0_cons.
  unfold permut_list_inv.
  rewrite (List_map_nth' 0). 2: {
    now rewrite seq_length; apply Hp; left.
  }
  rewrite seq_nth; [ cbn | now apply Hp; left ].
  now rewrite Nat.eqb_refl.
}
unfold ff_app.
rewrite List_nth_succ_cons.
unfold permut_list_inv.
cbn in Hl.
apply Nat.succ_inj in Hl.
apply Nat.succ_lt_mono in Hin.
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  apply Hp; right.
  apply nth_In; congruence.
}
rewrite seq_nth. 2: {
  apply Hp; right.
  apply nth_In; congruence.
}
rewrite Nat.add_0_l.
unfold unsome.
remember (List_find_nth _ _) as j eqn:Hj.
symmetry in Hj.
destruct j as [j| ]. {
  apply List_find_nth_loop_Some with (d := 0) in Hj.
  destruct Hj as (Hjl & Hij & Hj).
  apply Nat.eqb_eq in Hj.
  rewrite Nat.sub_0_r in Hj.
  destruct Hp as (Hp1, Hp2).
  specialize (Hp2 (S i) j).
  assert (H : S i < length (a :: l)) by (cbn; rewrite Hl; flia Hin).
  specialize (Hp2 H Hjl); clear H.
  unfold ff_app in Hp2.
  rewrite List_nth_succ_cons in Hp2.
  now specialize (Hp2 Hj).
}
specialize (List_find_nth_None 0 _ _ Hj) as H1.
specialize (H1 (S i)).
assert (H : S i < length (a :: l)) by (cbn; flia Hin Hl).
specialize (H1 H); clear H.
now rewrite Nat.eqb_refl in H1.
Qed.

Theorem permut_permut_inv : ∀ n l i,
  is_permut n l
  → i < n
  → ff_app l (ff_app (permut_list_inv l) i) = i.
Proof.
intros * (Hp, Hl) Hin.
unfold permut_list_inv, unsome, ff_app.
rewrite (List_map_nth' 0); [ | rewrite seq_length; congruence ].
rewrite seq_nth; [ | congruence ].
rewrite Nat.add_0_l.
remember (List_find_nth _ _) as x eqn:Hx; symmetry in Hx.
destruct x as [x| ]. {
  apply (List_find_nth_Some 0) in Hx.
  destruct Hx as (Hxl & Hbef & Hix).
  now apply Nat.eqb_eq in Hix.
} {
  exfalso.
  rewrite <- Hl in Hin.
  apply (permut_list_without Hp Hin).
  intros j Hj.
  specialize (List_find_nth_None 0 _ _ Hx Hj) as H1.
  now apply Nat.eqb_neq, Nat.neq_sym in H1.
}
Qed.

Arguments permut_inv_permut n%nat [l]%list [i]%nat _ _.
Arguments permut_permut_inv n%nat [l]%list [i]%nat _ _.

(* transposition *)

Definition transposition i j k :=
  if k =? i then j else if k =? j then i else k.

Definition swap_elem (f : nat → nat) i j k :=
  f (transposition i j k).

Definition list_swap_elem {A} d (l : list A) i j :=
  map (λ k, nth (transposition i j k) l d) (seq 0 (length l)).

(*
Theorem permut_fun_inv_loop_ext_in : ∀ f g i j,
  (∀ k, k < i → f k = g k)
  → permut_fun_inv_loop f i j = permut_fun_inv_loop g i j.
Proof.
intros * Hfg.
revert j.
induction i; intros; [ easy | cbn ].
destruct (Nat.eq_dec (f i) j) as [Hf| Hf]. {
  destruct (Nat.eq_dec (g i) j) as [Hg| Hg]; [ easy | ].
  specialize (Hfg i (Nat.lt_succ_diag_r _)); congruence.
}
destruct (Nat.eq_dec (g i) j) as [Hg| Hg]. {
  specialize (Hfg i (Nat.lt_succ_diag_r _)); congruence.
}
apply IHi.
intros k Hk.
apply Hfg; flia Hk.
Qed.
*)

Theorem permut_list_ub : ∀ l i,
  is_permut_list l → i < length l → nth i l 0 < length l.
Proof.
intros * Hp Hin.
now apply Hp, nth_In.
Qed.

Theorem transposition_lt : ∀ i j k n,
  i < n
  → j < n
  → k < n
  → transposition i j k < n.
Proof.
intros * Hi Hj Hk.
unfold transposition.
do 2 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec k i); [ easy | ].
now destruct (Nat.eq_dec k j).
Qed.

Theorem transposition_out : ∀ i j k, k ≠ i → k ≠ j → transposition i j k = k.
Proof.
intros * Hi Hj.
unfold transposition.
do 2 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec k i) as [H| H]; [ easy | clear H ].
now destruct (Nat.eq_dec k j).
Qed.

Theorem transposition_id : ∀ i k, transposition i i k = k.
Proof.
intros.
unfold transposition.
do 2 rewrite if_eqb_eq_dec.
now destruct (Nat.eq_dec k i).
Qed.

Theorem transposition_1 : ∀ i j, transposition i j i = j.
Proof.
intros.
unfold transposition.
now rewrite Nat.eqb_refl.
Qed.

Theorem transposition_2 : ∀ i j, transposition i j j = i.
Proof.
intros.
unfold transposition.
rewrite Nat.eqb_refl.
rewrite if_eqb_eq_dec.
now destruct (Nat.eq_dec j i).
Qed.

Theorem transposition_comm : ∀ i j k, transposition i j k = transposition j i k.
Proof.
intros.
unfold transposition.
do 4 rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec k i) as [Hki| Hki]. {
  destruct (Nat.eq_dec k j) as [Hkj| Hkj]; [ congruence | easy ].
} {
  destruct (Nat.eq_dec k j) as [Hkj| Hkj]; [ congruence | easy ].
}
Qed.

Theorem list_swap_elem_is_permut : ∀ σ p q,
  p < length σ
  → q < length σ
  → is_permut_list σ
  → is_permut_list (list_swap_elem 0 σ p q).
Proof.
intros * Hp Hq Hσ.
unfold is_permut_list, list_swap_elem.
rewrite map_length, seq_length.
split; cbn. {
  intros i Hi.
  apply in_map_iff in Hi.
  destruct Hi as (j & Hji & Hj).
  apply in_seq in Hj.
  rewrite <- Hji.
  apply permut_list_ub; [ easy | ].
  now apply transposition_lt.
} {
  intros i j Hi Hj Hij.
  unfold ff_app in Hij.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  do 2 rewrite Nat.add_0_l in Hij.
  unfold transposition in Hij.
  do 4 rewrite if_eqb_eq_dec in Hij.
  destruct (Nat.eq_dec i p) as [Hip| Hip]. {
    subst i.
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ congruence | ].
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ now subst j; apply Hσ | ].
    apply Nat.neq_sym in Hjq.
    now exfalso; apply Hjq, Hσ.
  }
  destruct (Nat.eq_dec i q) as [Hiq| Hiq]. {
    destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ now subst i j; apply Hσ | ].
    destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ congruence | ].
    now apply Nat.neq_sym in Hjp; exfalso; apply Hjp; apply Hσ.
  }
  destruct (Nat.eq_dec j p) as [Hjp| Hjp]; [ now exfalso; apply Hiq, Hσ | ].
  destruct (Nat.eq_dec j q) as [Hjq| Hjq]; [ now exfalso; apply Hip, Hσ | ].
  now apply Hσ.
}
Qed.

(* *)

Definition rank_of_permut_in_sym_gr (sg : list (list nat)) σ :=
  unsome 0 (List_find_nth (list_eqb Nat.eqb σ) sg).

Theorem rank_of_permut_in_sym_gr_lt : ∀ n sg v,
  n ≠ 0
  → is_sym_gr_list n sg
  → rank_of_permut_in_sym_gr sg v < length sg.
Proof.
intros * Hnz Hsg.
unfold rank_of_permut_in_sym_gr.
unfold unsome.
remember (List_find_nth _ _) as i eqn:Hi; symmetry in Hi.
destruct i as [i| ]; [ now apply List_find_nth_Some_lt in Hi | ].
clear Hi.
destruct (lt_dec 0 (length sg)) as [Hs| Hs]; [ easy | ].
apply Nat.nlt_ge in Hs; exfalso.
apply Nat.le_0_r in Hs.
apply length_zero_iff_nil in Hs; subst sg.
destruct Hsg as (_ & _ & Hsurj).
cbn in Hsurj.
specialize (Hsurj (seq 0 n)) as H1.
rewrite seq_length in H1.
specialize (H1 eq_refl).
assert (H : is_permut_list (seq 0 n)). {
  split. {
    cbn; rewrite seq_length.
    intros i Hin.
    now rewrite in_seq in Hin.
  } {
    cbn; rewrite seq_length.
    intros i j Hi Hj Hij.
    unfold ff_app in Hij.
    rewrite seq_nth in Hij; [ | easy ].
    rewrite seq_nth in Hij; [ | easy ].
    easy.
  }
}
congruence.
Qed.

Theorem nth_rank_of_permut_in_sym_gr : ∀ sg l n,
  is_sym_gr_list n sg
  → is_permut_list l
  → length l = n
  → nth (rank_of_permut_in_sym_gr sg l) sg [] = l.
Proof.
intros * Hsg Hp Hs.
unfold rank_of_permut_in_sym_gr, unsome.
remember (List_find_nth _ _) as i eqn:Hi; symmetry in Hi.
destruct i as [i| ]. {
  apply List_find_nth_Some with (d := []) in Hi.
  destruct Hi as (His & Hji & Hi).
  now apply list_eqb_eq in Hi.
}
assert (H : l ∉ sg). {
  intros H.
  apply In_nth with (d := []) in H.
  destruct H as (j & Hj & Hjv).
  specialize (List_find_nth_None [] _ _ Hi Hj) as H.
  apply list_eqb_neq in H.
  now symmetry in Hjv.
}
exfalso; apply H; clear H.
now apply Hsg.
Qed.

Theorem rank_of_permut_in_sym_gr_list_el : ∀ n sg i,
  n ≠ 0
  → is_sym_gr_list n sg
  → i < length sg
  → rank_of_permut_in_sym_gr sg (nth i sg []) = i.
Proof.
intros * Hnz Hsg Hi.
unfold rank_of_permut_in_sym_gr, unsome.
remember (List_find_nth _ _) as j eqn:Hj; symmetry in Hj.
destruct j as [j| ]. {
  apply List_find_nth_Some with (d := []) in Hj.
  destruct Hj as (His & Hji & Hj).
  apply list_eqb_eq in Hj.
  destruct Hsg as (Hsg & Hinj & Hsurj).
  assert (Hjs : j < length sg). {
    destruct (lt_dec j (length sg)) as [Hjs| Hjs]; [ easy | exfalso ].
    apply Nat.nlt_ge in Hjs.
    rewrite (@nth_overflow _ _ j) in Hj; [ | easy ].
    specialize (Hsg i Hi) as H1.
    destruct H1 as (H1, H2).
    now rewrite Hj in H1; cbn in H1; subst n.
  }
  now apply Hinj.
}
specialize (List_find_nth_None [] _ _ Hj Hi) as H1.
now apply list_eqb_neq in H1.
Qed.

Theorem length_of_empty_sym_gr : ∀ sg,
  is_sym_gr_list 0 sg → length sg = 1.
Proof.
intros * Hsg.
destruct Hsg as (Hsg & Hinj & Hsurj).
specialize (Hsurj [] eq_refl) as H1.
assert (H : is_permut_list []). {
  now apply is_permut_list_is_permut_list_bool.
}
specialize (H1 H); clear H.
apply (In_nth _ _ []) in H1.
destruct H1 as (i & Hil & Hi).
destruct (Nat.eq_dec (length sg) 0) as [Hvz| Hvz]. {
  now rewrite Hvz in Hil.
}
destruct (Nat.eq_dec (length sg) 1) as [Hv1| Hv1]; [ easy | ].
specialize (Hsg 0) as H1.
specialize (Hsg 1) as H2.
specialize (Hinj 0 1) as H3.
assert (H : 0 < length sg) by flia Hvz.
specialize (H1 H); specialize (H3 H); clear H.
assert (H : 1 < length sg) by flia Hvz Hv1.
specialize (H2 H); specialize (H3 H); clear H.
destruct H1 as (H4, H5).
destruct H2 as (H6, H7).
enough (H : nth 0 sg [] = nth 1 sg []). {
  rewrite H in H3.
  now specialize (H3 eq_refl).
}
apply length_zero_iff_nil in H4, H6.
congruence.
Qed.

Fixpoint canon_sym_gr_inv_elem n k (j : nat) :=
  match n with
  | 0 => 0
  | S n' =>
      if lt_dec j (k / n'!) then
        S (canon_sym_gr_inv_elem n' (k mod n'!) j)
      else if lt_dec (k / n'!) j then
        S (canon_sym_gr_inv_elem n' (k mod n'!) (j - 1))
      else 0
  end.

Definition canon_sym_gr_inv_list n k : list nat :=
  map (canon_sym_gr_inv_elem n k) (seq 0 n).

Theorem length_canon_sym_gr_list_list : ∀ n,
  length (canon_sym_gr_list_list n) = n!.
Proof.
intros.
unfold canon_sym_gr_list_list.
now rewrite map_length, seq_length.
Qed.

Theorem length_canon_sym_gr_list : ∀ k n,
  length (canon_sym_gr_list n k) = n.
Proof.
intros.
revert k.
induction n; intros; [ easy | cbn ].
f_equal; rewrite map_length.
apply IHn.
Qed.

Theorem length_nth_canon_sym_gr_list_list : ∀ i n d,
  i < n!
  → length (nth i (canon_sym_gr_list_list n) d) = n.
Proof.
intros * Hin.
unfold canon_sym_gr_list_list.
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
apply length_canon_sym_gr_list.
Qed.

Theorem canon_sym_gr_list_ub : ∀ n k i,
  k < n!
  → i < n
  → nth i (canon_sym_gr_list n k) 0 < n.
Proof.
intros * Hkn Hi.
revert i k Hkn Hi.
induction n; intros; [ easy | cbn ].
destruct i. {
  apply Nat.div_lt_upper_bound; [ apply fact_neq_0 | ].
  now rewrite Nat.mul_succ_r, Nat.add_comm, Nat.mul_comm.
}
apply Nat.succ_lt_mono in Hi.
rewrite (List_map_nth' 0); [ | now rewrite length_canon_sym_gr_list ].
unfold succ_when_ge.
rewrite <- Nat.add_1_r.
apply Nat.add_lt_le_mono; [ | apply Nat_b2n_upper_bound ].
now apply IHn.
Qed.

Theorem canon_sym_gr_inv_sym_gr : ∀ n k i,
  k < n!
  → i < n
  → ff_app (canon_sym_gr_inv_list n k) (ff_app (canon_sym_gr_list n k) i) = i.
Proof.
intros * Hkn Hi.
unfold canon_sym_gr_inv_list.
unfold ff_app.
rewrite (List_map_nth' 0). 2: {
  rewrite seq_length.
  now apply canon_sym_gr_list_ub.
}
rewrite seq_nth; [ | now apply canon_sym_gr_list_ub ].
rewrite Nat.add_0_l.
revert k i Hi Hkn.
induction n; intros; [ easy | cbn ].
destruct i. {
  do 2 rewrite <- if_ltb_lt_dec.
  now rewrite Nat.ltb_irrefl.
}
apply Nat.succ_lt_mono in Hi.
rewrite (List_map_nth' 0); [ | now rewrite length_canon_sym_gr_list ].
unfold succ_when_ge.
unfold Nat.b2n.
rewrite if_leb_le_dec.
destruct (le_dec (k / n!) _) as [H1| H1]. {
  destruct (lt_dec _ (k / n!)) as [H| H]; [ flia H1 H | clear H ].
  destruct (lt_dec (k / n!) _) as [H| H]; [ clear H | flia H1 H ].
  f_equal; rewrite Nat.add_sub.
  now apply IHn.
} {
  rewrite Nat.add_0_r.
  destruct (lt_dec _ (k / n!)) as [H| H]; [ clear H | flia H1 H ].
  f_equal.
  now apply IHn.
}
Qed.

Theorem canon_sym_gr_inv_elem_ub : ∀ n k i,
  k < n!
  → i < n
  → canon_sym_gr_inv_elem n k i < n.
Proof.
intros * Hkn Hi.
revert i k Hkn Hi.
induction n; intros; [ easy | cbn ].
destruct (lt_dec i (k / n!)) as [Hikn| Hikn]. {
  apply -> Nat.succ_lt_mono.
  destruct (Nat.eq_dec i n) as [Hin| Hin]. {
    exfalso.
    subst i; clear Hi.
    rewrite Nat_fact_succ in Hkn.
    assert (Hkns : k / n! < S n). {
      apply Nat.div_lt_upper_bound; [ apply fact_neq_0 | ].
      now rewrite Nat.mul_comm.
    }
    flia Hikn Hkns.
  }
  apply IHn; [ easy | flia Hi Hin ].
}
destruct (lt_dec (k / n!) i) as [Hkni| Hkni]; [ | flia ].
apply -> Nat.succ_lt_mono.
apply IHn; [ easy | flia Hi Hkni ].
Qed.

Theorem canon_sym_gr_sym_gr_inv : ∀ n k i,
  k < n!
  → i < n
  → ff_app (canon_sym_gr_list n k) (ff_app (canon_sym_gr_inv_list n k) i) = i.
Proof.
intros * Hkn Hi.
unfold canon_sym_gr_inv_list.
unfold ff_app.
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
rewrite Nat.add_0_l.
revert k i Hi Hkn.
induction n; intros; [ easy | cbn ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  now apply Nat.lt_1_r in Hkn, Hi; subst k i.
}
apply Nat.neq_0_lt_0 in Hnz.
destruct i. {
  destruct (lt_dec 0 (k / n!)) as [Hzkn| Hzkn]. {
    unfold succ_when_ge.
    rewrite (List_map_nth' 0). 2: {
      rewrite length_canon_sym_gr_list.
      now apply canon_sym_gr_inv_elem_ub.
    }
    rewrite IHn; [ | easy | easy ].
    unfold Nat.b2n.
    rewrite if_leb_le_dec.
    destruct (le_dec (k / n!) 0) as [Hknz| Hknz]; [ | easy ].
    now apply Nat.nlt_ge in Hknz.
  }
  apply Nat.nlt_ge in Hzkn.
  apply Nat.le_0_r in Hzkn.
  now rewrite Hzkn; cbn.
}
apply Nat.succ_lt_mono in Hi.
destruct (lt_dec (S i) (k / n!)) as [Hsikn| Hsikn]. {
  destruct (Nat.eq_dec (S i) n) as [Hsin| Hsin]. {
    rewrite Hsin in Hsikn.
    rewrite Nat_fact_succ in Hkn.
    assert (Hkns : k / n! < S n). {
      apply Nat.div_lt_upper_bound; [ apply fact_neq_0 | ].
      now rewrite Nat.mul_comm.
    }
    flia Hsikn Hkns.
  }
  rewrite (List_map_nth' 0). 2: {
    rewrite length_canon_sym_gr_list.
    apply canon_sym_gr_inv_elem_ub; [ easy | flia Hi Hsin ].
  }
  rewrite IHn; [ | flia Hi Hsin | easy ].
  unfold succ_when_ge, Nat.b2n.
  apply Nat.nle_gt in Hsikn.
  apply Nat.leb_nle in Hsikn.
  now rewrite Hsikn, Nat.add_0_r.
}
apply Nat.nlt_ge in Hsikn.
destruct (lt_dec (k / n!) (S i)) as [Hknsi| Hknsi]; [ | flia Hsikn Hknsi ].
rewrite Nat_sub_succ_1.
rewrite (List_map_nth' 0).  2: {
  rewrite length_canon_sym_gr_list.
  now apply canon_sym_gr_inv_elem_ub.
}
rewrite IHn; [ | easy | easy ].
unfold succ_when_ge.
unfold Nat.b2n.
rewrite if_leb_le_dec.
destruct (le_dec (k / n!) i) as [Hkni| Hkni]; [ apply Nat.add_1_r | ].
now apply Nat.succ_le_mono in Hknsi.
Qed.

Theorem nth_canon_sym_gr_list_inj1 : ∀ n k i j,
  k < fact n
  → i < n
  → j < n
  → ff_app (canon_sym_gr_list n k) i = ff_app (canon_sym_gr_list n k) j
  → i = j.
Proof.
intros * Hk Hi Hj Hij.
rewrite <- canon_sym_gr_inv_sym_gr with (n := n) (k := k); [ | easy | easy ].
symmetry.
rewrite <- canon_sym_gr_inv_sym_gr with (n := n) (k := k); [ | easy | easy ].
symmetry.
now rewrite Hij.
Qed.

(* rank in canon symmetric group *)

(*
Definition sub_canon_permut_fun (f : nat → nat) i :=
  f (S i) - Nat.b2n (f 0 <? f (S i)).

Fixpoint rank_of_permut_in_canon_sym_gr n (f : nat → nat) : nat :=
  match n with
  | 0 => 0
  | S n' => f 0 * n'! + rank_of_permut_in_canon_sym_gr n' (sub_canon_permut_fun f)
  end.

Definition rank_of_permut_in_canon_sym_gr_vect n (v : vector nat) : nat :=
  rank_of_permut_in_canon_sym_gr n (vect_el 0 v).
*)

(* *)

Definition sub_canon_permut_list (l : list nat) :=
  map (λ a, a - Nat.b2n (hd 0 l <? a)) (tl l).

Fixpoint rank_of_permut_in_canon_sym_gr_list n (l : list nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
      hd 0 l * n'! +
      rank_of_permut_in_canon_sym_gr_list n' (sub_canon_permut_list l)
  end.

(*
Compute (let n := 4 in map (λ i, let v := vect_el empty_vect (canon_sym_gr n) i in (rank_of_permut_in_canon_sym_gr_vect n v, rank_of_permut_in_canon_sym_gr_vect n v)) (seq 0 (n! + 10))).
*)

Theorem sub_canon_permut_list_elem_ub : ∀ l i,
  is_permut_list l
  → S i < length l
  → nth i (sub_canon_permut_list l) 0 < length l - 1.
Proof.
intros * (Hvn, Hn) Hin.
destruct l as [| a]; [ easy | ].
cbn - [ "<?" ] in Hin |-*.
rewrite Nat.sub_0_r.
apply Nat.succ_lt_mono in Hin.
rewrite (List_map_nth' 0); [ | easy ].
unfold Nat.b2n.
rewrite if_ltb_lt_dec.
destruct (lt_dec a (nth i l 0)) as [Hal| Hal]. {
  enough (H : nth i l 0 < S (length l)) by flia Hal H.
  now apply Hvn; right; apply nth_In.
}
apply Nat.nlt_ge in Hal.
rewrite Nat.sub_0_r.
destruct (Nat.eq_dec (nth i l 0) a) as [Hia| Hia]. {
  rewrite Hia.
  apply Nat.succ_lt_mono in Hin.
  symmetry in Hia.
  now specialize (Hn 0 (S i) (Nat.lt_0_succ _) Hin Hia).
}
specialize (Hvn a (or_introl eq_refl)); cbn in Hvn.
flia Hvn Hal Hia.
Qed.

Theorem sub_canon_sym_gr_elem_inj1 : ∀ l i j,
  is_permut_list l
  → S i < length l
  → S j < length l
  → nth i (sub_canon_permut_list l) 0 = nth j (sub_canon_permut_list l) 0
  → i = j.
Proof.
intros * (Hvn, Hn) Hin Hjn Hij.
destruct l as [| a]; [ easy | ].
cbn - [ "<?" ] in Hin, Hjn, Hij.
apply Nat.succ_lt_mono in Hin, Hjn.
rewrite (List_map_nth' 0) in Hij; [ | easy ].
rewrite (List_map_nth' 0) in Hij; [ | easy ].
unfold Nat.b2n in Hij.
do 2 rewrite if_ltb_lt_dec in Hij.
destruct (lt_dec a (nth i l 0)) as [Hai| Hai]. {
  destruct (lt_dec a (nth j l 0)) as [Haj| Haj]. {
    apply Nat.succ_inj.
    apply Nat.succ_lt_mono in Hin, Hjn.
    apply Hn; [ easy | easy | ].
    cbn; flia Hai Haj Hij.
  }
  apply Nat.nlt_ge in Haj.
  rewrite Nat.sub_0_r in Hij.
  apply Nat.succ_lt_mono in Hjn.
  specialize (Hn 0 (S j) (Nat.lt_0_succ _) Hjn) as H1.
  cbn in H1.
  replace (nth j l 0) with a in H1 by flia Hai Haj Hij.
  now specialize (H1 eq_refl).
}
apply Nat.nlt_ge in Hai.
rewrite Nat.sub_0_r in Hij.
destruct (lt_dec a (nth j l 0)) as [Haj| Haj]. {
  apply Nat.succ_lt_mono in Hin.
  specialize (Hn (S i) 0 Hin (Nat.lt_0_succ _)) as H1.
  cbn in H1.
  replace (nth i l 0) with a in H1 by flia Hai Haj Hij.
  now specialize (H1 eq_refl).
}
rewrite Nat.sub_0_r in Hij.
apply Nat.succ_inj.
apply Nat.succ_lt_mono in Hin, Hjn.
now apply Hn.
Qed.

Theorem length_sub_canon_permut_list : ∀ l,
  length (sub_canon_permut_list l) = length l - 1.
Proof.
intros.
destruct l as [| a]; [ easy | ].
now cbn; rewrite map_length, Nat.sub_0_r.
Qed.

Theorem rank_of_canon_permut_ub : ∀ n l,
  is_permut_list l
  → length l = n
  → rank_of_permut_in_canon_sym_gr_list n l < n!.
Proof.
intros * (Hvn, Hn) Hln.
revert l Hvn Hn Hln.
induction n; intros; cbn; [ flia | ].
rewrite Nat.add_comm.
apply Nat.add_lt_le_mono. {
  apply IHn. {
    intros i Hi.
    apply (In_nth _ _ 0) in Hi.
    destruct Hi as (j & Hj & Hji).
    rewrite <- Hji.
    rewrite length_sub_canon_permut_list in Hj |-*.
    apply sub_canon_permut_list_elem_ub; [ easy | flia Hj ].
  } {
    intros i j Hi Hj.
    rewrite length_sub_canon_permut_list in Hi, Hj.
    apply sub_canon_sym_gr_elem_inj1; [ easy | flia Hi | flia Hj ].
  }
  now rewrite length_sub_canon_permut_list, Hln, Nat_sub_succ_1.
}
apply Nat.mul_le_mono_r.
specialize (Hvn (hd 0 l)).
assert (H : hd 0 l ∈ l). {
  rewrite List_hd_nth_0; apply nth_In; rewrite Hln; flia.
}
specialize (Hvn H); clear H.
rewrite Hln in Hvn.
now apply Nat.succ_le_mono in Hvn.
Qed.

Theorem sub_canon_permut_list_is_permut : ∀ l,
  is_permut_list l
  → is_permut_list (sub_canon_permut_list l).
Proof.
intros * Hl.
split. {
  intros i Hi.
  apply (In_nth _ _ 0) in Hi.
  destruct Hi as (j & Hj & Hji).
  rewrite <- Hji.
  rewrite length_sub_canon_permut_list in Hj |-*.
  apply sub_canon_permut_list_elem_ub; [ easy | flia Hj ].
} {
  intros i j Hi Hj Hij.
  rewrite length_sub_canon_permut_list in Hi, Hj.
  apply sub_canon_sym_gr_elem_inj1 in Hij; [ easy | easy | | ]. {
    flia Hi.
  } {
    flia Hj.
  }
}
Qed.

(*
Theorem permut_in_canon_sym_gr_of_its_rank : ∀ n f,
  is_permut_fun f n
  → ∀ i, i < n
  → canon_sym_gr_elem n (rank_of_permut_in_canon_sym_gr n f) i = f i.
*)
Theorem permut_in_canon_sym_gr_of_its_rank : ∀ n l,
  is_permut_list l
  → length l = n
  → canon_sym_gr_list n (rank_of_permut_in_canon_sym_gr_list n l) = l.
Proof.
intros * (Hvn, Hn) Hln.
revert l Hvn Hn Hln.
induction n; intros; [ now apply length_zero_iff_nil in Hln | cbn ].
destruct l as [| a]; [ easy | ].
f_equal. {
  cbn - [ sub_canon_permut_list ].
  rewrite Nat.div_add_l; [ | apply fact_neq_0 ].
  rewrite <- Nat.add_0_r; f_equal.
  apply Nat.div_small.
  apply rank_of_canon_permut_ub. 2: {
    cbn; rewrite map_length.
    now cbn in Hln; apply Nat.succ_inj in Hln.
  }
  now apply sub_canon_permut_list_is_permut.
} {
  cbn in Hln.
  apply Nat.succ_inj in Hln.
  rewrite Nat.div_add_l; [ | apply fact_neq_0 ].
  rewrite Nat_mod_add_l_mul_r; [ | apply fact_neq_0 ].
  rewrite Nat.mod_small. 2: {
    apply rank_of_canon_permut_ub. 2: {
      rewrite length_sub_canon_permut_list; cbn.
      now rewrite Hln, Nat.sub_0_r.
    }
    now apply sub_canon_permut_list_is_permut.
  }
  rewrite IHn; cycle 1. {
    intros i Hi.
    apply (In_nth _ _ 0) in Hi.
    destruct Hi as (j & Hj & Hji).
    rewrite <- Hji.
    apply permut_list_ub; [ | easy ].
    now apply sub_canon_permut_list_is_permut.
  } {
    intros i j Hi Hj.
    rewrite length_sub_canon_permut_list in Hi, Hj.
    cbn in Hi, Hj.
    rewrite Nat.sub_0_r in Hi, Hj.
    apply sub_canon_sym_gr_elem_inj1; [ easy | cbn; flia Hi | cbn; flia Hj ].
  } {
    rewrite length_sub_canon_permut_list; cbn.
    now rewrite Nat.sub_0_r.
  }
  cbn - [ sub_canon_permut_list ].
  unfold succ_when_ge.
  remember (rank_of_permut_in_canon_sym_gr_list _ _) as x.
  cbn - [ "<=?" ]; subst x.
  rewrite map_map.
  rewrite List_map_map_seq with (d := 0).
  rewrite List_map_nth_seq with (d := 0).
  apply map_ext_in_iff.
  intros i Hi; apply in_seq in Hi.
  unfold Nat.b2n.
  rewrite if_ltb_lt_dec.
  destruct (lt_dec a (nth i l 0)) as [Hai| Hai]. {
    rewrite if_leb_le_dec.
    destruct (le_dec _ _) as [H1| H1]; [ apply Nat.sub_add; flia Hai | ].
    exfalso.
    apply H1; clear H1.
    rewrite Nat.div_small; [ flia Hai | ].
    apply rank_of_canon_permut_ub; [ | now cbn; rewrite map_length ].
    now apply sub_canon_permut_list_is_permut.
  }
  apply Nat.nlt_ge in Hai.
  rewrite Nat.sub_0_r.
  rewrite Nat.div_small. 2: {
    apply rank_of_canon_permut_ub. 2: {
      rewrite length_sub_canon_permut_list; cbn; rewrite Hln.
      apply Nat.sub_0_r.
    }
    now apply sub_canon_permut_list_is_permut.
  }
  rewrite Nat.add_0_r, if_leb_le_dec.
  destruct (le_dec _ _) as [H1| H1]; [ | apply Nat.add_0_r ].
  exfalso.
  apply Nat.le_antisymm in H1; [ symmetry in H1 | easy ].
  specialize (Hn 0 (S i) (Nat.lt_0_succ _)) as H2.
  assert (H : S i < length (a :: l)) by (cbn; flia Hi).
  now specialize (H2 H H1); clear H.
}
Qed.

Theorem canon_sym_gr_list_is_permut_list : ∀ n k,
  k < n!
  → is_permut_list (canon_sym_gr_list n k).
Proof.
intros * Hkn.
split. {
  intros i Hi.
  rewrite length_canon_sym_gr_list.
  apply (In_nth _ _ 0) in Hi.
  destruct Hi as (j & Hj & Hji).
  rewrite length_canon_sym_gr_list in Hj.
  rewrite <- Hji.
  now apply canon_sym_gr_list_ub.
} {
  intros * Hi Hj Hij.
  rewrite length_canon_sym_gr_list in Hi, Hj.
  now apply nth_canon_sym_gr_list_inj1 in Hij.
}
Qed.

Theorem canon_sym_gr_list_is_permut : ∀ n k,
  k < n!
  → is_permut n (canon_sym_gr_list n k).
Proof.
intros * Hkn.
split; [ now apply canon_sym_gr_list_is_permut_list | ].
apply length_canon_sym_gr_list.
Qed.

Theorem canon_sym_gr_list_list_elem_is_permut : ∀ n k,
  k < n!
  → is_permut n (nth k (canon_sym_gr_list_list n) []).
Proof.
intros * Hkn.
unfold canon_sym_gr_list_list.
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
now apply canon_sym_gr_list_is_permut.
Qed.

Theorem canon_sym_gr_sub_canon_permut_list : ∀ n k,
  canon_sym_gr_list n (k mod n!) =
  sub_canon_permut_list (canon_sym_gr_list (S n) k).
Proof.
intros.
destruct n; intros; [ easy | ].
cbn - [ "<?" fact ].
f_equal. {
  unfold succ_when_ge.
  rewrite <- Nat.add_sub_assoc. 2: {
    unfold Nat.b2n.
    rewrite if_leb_le_dec, if_ltb_lt_dec.
    destruct (le_dec _ _) as [H| H]; [ destruct (lt_dec _ _); cbn; flia | ].
    rewrite Nat.add_0_r.
    apply Nat.nle_gt in H.
    destruct (lt_dec _ _) as [Hqr| Hqr]; [ flia H Hqr | easy ].
  }
  symmetry; rewrite <- Nat.add_0_r; f_equal.
  unfold Nat.b2n.
  rewrite if_leb_le_dec, if_ltb_lt_dec.
  destruct (le_dec _ _) as [H1| H1]; [ | easy ].
  destruct (lt_dec _ _) as [H2| H2]; [ easy | flia H1 H2 ].
}
rewrite map_map.
rewrite map_map.
apply map_ext_in.
intros i Hi.
remember (succ_when_ge (_ mod _ / _) _) as x eqn:Hx.
unfold succ_when_ge, Nat.b2n.
rewrite if_leb_le_dec, if_ltb_lt_dec.
rewrite <- Nat.add_sub_assoc. 2: {
  destruct (le_dec _ _) as [H| H]; [ destruct (lt_dec _ _); cbn; flia | ].
  rewrite Nat.add_0_r.
  apply Nat.nle_gt in H.
  destruct (lt_dec _ _) as [Hqr| Hqr]; [ flia H Hqr | easy ].
}
symmetry; rewrite <- Nat.add_0_r; f_equal.
destruct (le_dec _ _) as [H1| H1]; [ | easy ].
destruct (lt_dec _ _) as [H2| H2]; [ easy | flia H1 H2 ].
Qed.

Theorem rank_of_canon_permut_of_canon_rank : ∀ n k,
  k < n!
  → rank_of_permut_in_canon_sym_gr_list n (canon_sym_gr_list n k) = k.
Proof.
intros * Hkn.
revert k Hkn.
induction n; intros; [ now apply Nat.lt_1_r in Hkn | ].
cbn - [ canon_sym_gr_list ].
remember (sub_canon_permut_list _) as x; cbn; subst x.
specialize (Nat.div_mod k (fact n) (fact_neq_0 _)) as H1.
rewrite Nat.mul_comm in H1.
replace (k / fact n * fact n) with (k - k mod fact n) by flia H1.
rewrite <- Nat.add_sub_swap; [ | apply Nat.mod_le, fact_neq_0 ].
apply Nat.add_sub_eq_r; f_equal.
clear H1.
rewrite <- (IHn (k mod fact n)) at 1; [ | easy ].
f_equal.
apply canon_sym_gr_sub_canon_permut_list.
Qed.

Theorem rank_in_sym_gr_of_rank_in_canon_sym_gr_prop : ∀ n sg,
  is_sym_gr_list n sg
  → ∀ k : fin_t n!,
      (rank_of_permut_in_sym_gr sg
         (nth (proj1_sig k) (canon_sym_gr_list_list n) []) <? length sg) =
      true.
Proof.
intros * Hsg k.
apply Nat.ltb_lt.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  destruct k as (k, pk); cbn.
  apply Nat.ltb_lt, Nat.lt_1_r in pk; subst k.
  specialize (length_of_empty_sym_gr Hsg) as Hs.
  destruct sg as [| v]; [ easy | ].
  destruct sg; [ clear Hs | easy ].
  destruct Hsg as (Hsg & _ & _).
  specialize (Hsg 0 Nat.lt_0_1); cbn in Hsg.
  destruct Hsg as (H1, H2).
  apply length_zero_iff_nil in H1; subst v.
  apply Nat.lt_0_1.
}
now apply rank_of_permut_in_sym_gr_lt with (n := n).
Qed.

Theorem rank_in_canon_sym_gr_of_rank_in_sym_gr_prop : ∀ n sg,
  is_sym_gr_list n sg
  → ∀ k : fin_t (length sg),
      (rank_of_permut_in_canon_sym_gr_list n (nth (proj1_sig k) sg []) <? n!)
      = true.
Proof.
intros * Hsg k.
destruct Hsg as (Hsg & Hinj & Hsurj).
apply Nat.ltb_lt.
destruct k as (k, pk); cbn.
apply Nat.ltb_lt in pk.
specialize (Hsg k pk).
now apply rank_of_canon_permut_ub.
Qed.

Definition rank_in_sym_gr_of_rank_in_canon_sym_gr n sg
    (Hsg : is_sym_gr_list n sg) (k : fin_t n!) : fin_t (length sg) :=
  exist (λ a : nat, (a <? length sg) = true)
    (rank_of_permut_in_sym_gr sg
      (nth (proj1_sig k) (canon_sym_gr_list_list n) []))
    (rank_in_sym_gr_of_rank_in_canon_sym_gr_prop Hsg k).

Definition rank_in_canon_sym_gr_of_rank_in_sym_gr  n sg
    (Hsg : is_sym_gr_list n sg) (k : fin_t (length sg)) : fin_t n! :=
  exist (λ a : nat, (a <? n!) = true)
    (rank_of_permut_in_canon_sym_gr_list n (nth (proj1_sig k) sg []))
    (rank_in_canon_sym_gr_of_rank_in_sym_gr_prop Hsg k).

Theorem rank_in_sym_gr_of_rank_in_canon_sym_gr_of_its_inverse : ∀ n sg
    (Hsg : is_sym_gr_list n sg) k,
  rank_in_sym_gr_of_rank_in_canon_sym_gr Hsg
    (rank_in_canon_sym_gr_of_rank_in_sym_gr Hsg k) = k.
Proof.
intros.
destruct k as (k, pk); cbn - [ "<?" ].
apply eq_exist_uncurried.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  specialize (length_of_empty_sym_gr Hsg) as Hs.
  specialize (proj1 (Nat.ltb_lt _ _) pk) as Hk.
  rewrite Hs in Hk.
  apply Nat.lt_1_r in Hk; subst k.
  assert (p : rank_of_permut_in_sym_gr sg [] = 0). {
    unfold rank_of_permut_in_sym_gr, unsome; cbn.
    destruct sg as [| v]; [ easy | ].
    destruct sg; [ cbn | easy ].
    destruct Hsg as (Hsg & _ & _).
    specialize (Hsg 0 Nat.lt_0_1); cbn in Hsg.
    destruct Hsg as (H1, H2).
    now apply length_zero_iff_nil in H1; subst v.
  }
  exists p.
  apply (Eqdep_dec.UIP_dec Bool.bool_dec).
}  
cbn.
assert
  (p :
   rank_of_permut_in_sym_gr sg
     (nth (rank_of_permut_in_canon_sym_gr_list n (nth k sg []))
        (canon_sym_gr_list_list n) []) = k). {
  apply Nat.ltb_lt in pk.
  destruct Hsg as (Hsg & Hinj & Hsurj).
  specialize (Hsg k pk) as H1.
  unfold canon_sym_gr_list_list.
  rewrite (List_map_nth' 0). 2: {
    rewrite seq_length.
    now apply rank_of_canon_permut_ub.
  }
  rewrite seq_nth; [ | now apply rank_of_canon_permut_ub ].
  rewrite Nat.add_0_l.
  rewrite permut_in_canon_sym_gr_of_its_rank; [ | easy | easy ].
  now apply rank_of_permut_in_sym_gr_list_el with (n := n).
}
exists p.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Theorem rank_in_canon_sym_gr_of_rank_in_sym_gr_of_its_inverse : ∀ n sg
    (Hsg : is_sym_gr_list n sg) k,
  rank_in_canon_sym_gr_of_rank_in_sym_gr Hsg
    (rank_in_sym_gr_of_rank_in_canon_sym_gr Hsg k) = k.
Proof.
intros.
destruct k as (k, pk); cbn - [ "<?" ].
apply eq_exist_uncurried; cbn.
assert
  (p :
   rank_of_permut_in_canon_sym_gr_list n
     (nth (rank_of_permut_in_sym_gr sg (nth k (canon_sym_gr_list_list n) []))
        sg []) = k). {
  specialize (proj1 (Nat.ltb_lt _ _) pk) as Hkn.
  unfold canon_sym_gr_list_list.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ cbn | easy ].
  rewrite (@nth_rank_of_permut_in_sym_gr _ _ n); cycle 1. {
    easy.
  } {
    now apply canon_sym_gr_list_is_permut.
  } {
    apply length_canon_sym_gr_list.
  }
  now apply rank_of_canon_permut_of_canon_rank.
}
exists p.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Theorem sym_gr_size : ∀ n sg, is_sym_gr_list n sg → length sg = n!.
Proof.
intros * Hsg.
apply (bijective_fin_t _ _ (rank_in_canon_sym_gr_of_rank_in_sym_gr Hsg)).
exists (rank_in_sym_gr_of_rank_in_canon_sym_gr Hsg).
split. {
  intros x.
  apply rank_in_sym_gr_of_rank_in_canon_sym_gr_of_its_inverse.
} {
  intros y.
  apply rank_in_canon_sym_gr_of_rank_in_sym_gr_of_its_inverse.
}
Qed.

(* *)

Record sym_gr_list n :=
  { sg_list : list (list nat);
    sg_prop : is_sym_gr_list n sg_list }.

Theorem canon_sym_gr_list_list_is_permut : ∀ n k,
  k < n!
  → is_permut_list (nth k (canon_sym_gr_list_list n) []).
Proof.
intros * Hkn.
unfold is_permut_list.
cbn; unfold canon_sym_gr_list_list.
rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
rewrite seq_nth; [ | easy ].
now apply canon_sym_gr_list_is_permut.
Qed.

Theorem canon_sym_gr_list_inj : ∀ n i j,
  i < fact n
  → j < fact n
  → canon_sym_gr_list n i = canon_sym_gr_list n j
  → i = j.
Proof.
intros * Hi Hj Hij.
apply (f_equal (@rank_of_permut_in_canon_sym_gr_list n)) in Hij.
rewrite rank_of_canon_permut_of_canon_rank in Hij; [ | easy ].
rewrite rank_of_canon_permut_of_canon_rank in Hij; [ | easy ].
easy.
Qed.

Theorem canon_sym_gr_is_sym_gr_list : ∀ n,
  is_sym_gr_list n (canon_sym_gr_list_list n).
Proof.
intros.
split. {
  rewrite length_canon_sym_gr_list_list.
  intros i Hi.
  unfold canon_sym_gr_list_list.
  rewrite (List_map_nth' 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ | easy ].
  rewrite length_canon_sym_gr_list.
  split; [ easy | ].
  now apply canon_sym_gr_list_is_permut.
}
split. {
  rewrite length_canon_sym_gr_list_list.
  intros i j Hi Hj Hij.
  unfold canon_sym_gr_list_list in Hij.
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
  rewrite seq_nth in Hij; [ | easy ].
  rewrite seq_nth in Hij; [ | easy ].
  now apply canon_sym_gr_list_inj in Hij.
} {
  intros l Hl Hp.
  unfold canon_sym_gr_list_list.
  apply in_map_iff.
  exists (rank_of_permut_in_canon_sym_gr_list n l).
  rewrite permut_in_canon_sym_gr_of_its_rank; [ | easy | easy ].
  split; [ easy | ].
  apply in_seq.
  split; [ flia | ].
  now apply rank_of_canon_permut_ub.
}
Qed.

Theorem rank_of_permut_in_canon_gr_list_inj : ∀ n la lb,
  is_permut_list la
  → is_permut_list lb
  → length la = n
  → length lb = n
  → rank_of_permut_in_canon_sym_gr_list n la =
    rank_of_permut_in_canon_sym_gr_list n lb
  → la = lb.
Proof.
intros * Hla Hlb Han Hbn Hrr.
apply (f_equal (canon_sym_gr_list n)) in Hrr.
rewrite permut_in_canon_sym_gr_of_its_rank in Hrr; [ | easy | easy ].
rewrite permut_in_canon_sym_gr_of_its_rank in Hrr; [ | easy | easy ].
easy.
Qed.

(*
Definition permut_fun_inv_loop' f n i :=
  let '(x, x') :=
    pigeonhole_fun (S n) (λ j, if Nat.eq_dec j n then i else f j)
  in
  if Nat.eq_dec x n then x' else x.

Theorem fun_find_permut_fun_inv_loop' : ∀ l n,
  is_permut_list l
  → length l = n
  → ∀ i, i < n
  → nth i (permut_list_inv l) 0 = permut_fun_inv_loop' l n i.
...
Theorem fun_find_permut_fun_inv_loop' : ∀ l n,
  is_permut_list l n
  → ∀ i, i < n
  → permut_fun_inv_loop f n i = permut_fun_inv_loop' f n i.
Proof.
intros * (Hfub, Hinj) * Hin.
unfold permut_fun_inv_loop'.
remember (pigeonhole_fun _ _) as xx eqn:Hxx.
symmetry in Hxx.
destruct xx as (j, j').
unfold pigeonhole_fun in Hxx.
remember (find_dup _ _) as fd eqn:Hfd.
symmetry in Hfd.
destruct fd as [(x, x')| ]. {
  injection Hxx; clear Hxx; intros; subst x x'.
  apply find_dup_some in Hfd.
  destruct Hfd as (Hij & la1 & la2 & la3 & Hfd).
  destruct (Nat.eq_dec j n) as [Hjn| Hjn]. {
    subst j.
    destruct (Nat.eq_dec j' n) as [Hin'| Hin']. {
      subst j'; clear Hij.
      exfalso.
      revert Hfd.
      apply List_seq_nothing_after_last.
    }
    subst i.
    apply fun_find_prop; [ easy | ].
    assert (H : j' ∈ seq 0 (S n)). {
      rewrite Hfd.
      apply in_app_iff; right; right.
      now apply in_app_iff; right; left.
    }
    apply in_seq in H.
    flia Hin' H.
  }
  destruct (Nat.eq_dec j' n) as [Hjn'| Hjn']. {
    subst j' i.
    apply fun_find_prop; [ easy | ].
    assert (H : j ∈ seq 0 (S n)). {
      rewrite Hfd.
      apply in_app_iff; right.
      now left.
    }
    apply in_seq in H.
    flia Hjn H.
  }
  apply Hinj in Hij; cycle 1. {
    assert (H : j ∈ seq 0 (S n)). {
      rewrite Hfd.
      apply in_app_iff; right.
      now left.
    }
    apply in_seq in H.
    flia Hjn H.
  } {
    assert (H : j' ∈ seq 0 (S n)). {
      rewrite Hfd.
      apply in_app_iff; right; right.
      now apply in_app_iff; right; left.
    }
    apply in_seq in H.
    flia Hjn' H.
  }
  subst j'.
  exfalso.
  specialize (seq_NoDup (S n) 0) as H1.
  rewrite Hfd in H1.
  apply NoDup_app_remove_l in H1.
  rewrite app_comm_cons in H1.
  specialize (proj1 (NoDup_app_iff _ _) H1) as (_ & _ & H2).
  specialize (H2 j (or_introl eq_refl)).
  apply H2.
  now left.
}
injection Hxx; clear Hxx; intros; subst j j'.
apply find_dup_none in Hfd.
replace (if Nat.eq_dec _ _ then _ else _) with 0. 2: {
  now destruct (Nat.eq_dec 0 n).
}
specialize (proj1 (NoDup_map_iff 0 _ _) Hfd) as H1.
rewrite seq_length in H1.
assert
  (H2 : ∀ j k,
   j < S n
   → k < S n
   → (if Nat.eq_dec j n then i else f j) = (if Nat.eq_dec k n then i else f k)
   → j = k). {
  intros j k Hj Hk.
  specialize (H1 j k Hj Hk).
  now do 2 rewrite seq_nth in H1.
}
clear H1; rename H2 into H1.
apply not_NoDup_map_f_seq with (b := n) in Hfd; [ easy | flia | ].
intros j Hj.
destruct (Nat.eq_dec j n) as [Hjn| Hjn]; [ easy | ].
apply Hfub.
flia Hj Hjn.
Qed.
*)

(* the proof that "vect_el σ (vect_el (permut_vect_inv σ) i) = i"
   is proven by the pigeonhole principle *)

(*
Theorem pigeonhole' : ∀ f n,
  (∀ i, i < n → f i < n)
  → (∀ i j, i < n → j < n → f i = f j → i = j)
  → ∀ i, i < n
  → ∀ j, j = permut_fun_inv_loop' f n i
  → j < n ∧ f j = i.
Proof.
intros * Hp1 Hp2 * Hin * Hj.
subst j.
unfold permut_fun_inv_loop'.
remember (pigeonhole_fun _ _) as xx eqn:Hxx.
symmetry in Hxx.
destruct xx as (x, x').
specialize pigeonhole as H1.
specialize (H1 (S n) n).
specialize (H1 (λ j, if Nat.eq_dec j n then i else f j)).
specialize (H1 (Nat.lt_succ_diag_r n)).
cbn in H1.
assert (H : ∀ j, j < S n → (if Nat.eq_dec j n then i else f j) < n). {
  intros j Hj.
  destruct (Nat.eq_dec j n) as [Hjn| Hjn]; [ now subst j | ].
  apply Hp1; flia Hj Hjn.
}
specialize (H1 H x x' Hxx); clear H.
destruct H1 as (Hxn & Hx'n & Hxx' & H1).
destruct (Nat.eq_dec x n) as [H2| H2]. {
  subst x.
  destruct (Nat.eq_dec x' n) as [H2| H2]; [ now subst x' | ].
  split; [ flia Hx'n H2 | easy ].
} {
  destruct (Nat.eq_dec x' n) as [H3| H3]. {
    split; [ flia Hxn H2 | easy ].
  }
  apply Hp2 in H1; [ easy | flia Hxn H2 | flia Hx'n H3 ].
}
Qed.

Theorem fun_permut_fun_inv_loop : ∀ f n,
  is_permut_fun f n
  → ∀ i, i < n
  → f (permut_fun_inv_loop f n i) = i.
Proof.
intros * (Hp1, Hp2) * Hin.
rewrite fun_find_permut_fun_inv_loop'; [ | easy | easy ].
apply (proj2 (pigeonhole' f Hp1 Hp2 Hin eq_refl)).
Qed.
*)

(*
Theorem permut_fun_inv_loop_is_permut : ∀ n f,
  is_permut_fun f n
  → is_permut_fun (permut_fun_inv_loop f n) n.
Proof.
intros * Hp.
destruct Hp as (Hp1, Hp2).
split. {
  intros i Hin; cbn.
  rewrite fun_find_permut_fun_inv_loop'; [ | easy | easy ].
  unfold permut_fun_inv_loop'.
  remember (pigeonhole_fun _ _) as xx eqn:Hxx.
  symmetry in Hxx; destruct xx as (x, x').
  destruct (Nat.eq_dec x n) as [Hxn| Hxn]. {
    subst x.
    unfold pigeonhole_fun in Hxx.
    remember (find_dup _ _) as fd eqn:Hfd; symmetry in Hfd.
    destruct fd as [(x, n')| ]. {
      injection Hxx; clear Hxx; intros; subst x x'.
      apply find_dup_some in Hfd.
      destruct Hfd as (Hij & la1 & la2 & la3 & Hfd).
      exfalso.
      revert Hfd.
      apply List_seq_nothing_after_last.
    }
    now injection Hxx; clear Hxx; intros; subst n x'.
  } {
    unfold pigeonhole_fun in Hxx.
    remember (find_dup _ _) as fd eqn:Hfd; symmetry in Hfd.
    destruct fd as [(n'', n')| ]. {
      injection Hxx; clear Hxx; intros; subst x x'.
      apply find_dup_some in Hfd.
      destruct Hfd as (Hij & la1 & la2 & la3 & Hfd).
      destruct (Nat.eq_dec n'' n) as [Hn''n| Hn''n]; [ now subst n'' | ].
      destruct (Nat.eq_dec n' n) as [Hn'n| Hn'n]. {
        subst n'.
        now apply List_sorted_in_seq in Hfd.
      }
      assert (H : n' ∈ seq 0 (S n)). {
        rewrite Hfd.
        apply in_app_iff; right; right.
        now apply in_app_iff; right; left.
      }
      apply in_seq in H.
      apply List_sorted_in_seq in Hfd.
      apply (Nat.lt_le_trans _ n'); [ easy | flia H ].
    }
    injection Hxx; clear Hxx; intros; subst x x'.
    flia Hin.
  }
}
intros i j Hi Hj Hij.
cbn in Hij.
rewrite fun_find_permut_fun_inv_loop' in Hij; [ | easy | easy ].
rewrite fun_find_permut_fun_inv_loop' in Hij; [ | easy | easy ].
unfold permut_fun_inv_loop' in Hij.
remember (pigeonhole_fun _ _) as xx eqn:Hxx in Hij.
remember (pigeonhole_fun _ _) as yy eqn:Hyy in Hij.
symmetry in Hxx; destruct xx as (x, x').
symmetry in Hyy; destruct yy as (y, y').
move y before x; move y' before x'.
unfold pigeonhole_fun in Hxx, Hyy.
remember (find_dup _ _) as fdi eqn:Hfdi in Hxx.
remember (find_dup _ _) as fdj eqn:Hfdj in Hyy.
symmetry in Hfdi, Hfdj.
move fdj before fdi.
move Hfdj before Hfdi.
destruct fdi as [(x1, x2)| ]. {
  injection Hxx; clear Hxx; intros; subst x1 x2.
  apply find_dup_some in Hfdi.
  destruct Hfdi as (Hij1 & la1 & la2 & la3 & Hfdi).
  destruct (Nat.eq_dec x n) as [Hxn| Hxn]. {
    subst x.
    now apply List_seq_nothing_after_last in Hfdi.
  }
  destruct fdj as [(x1, x2)| ]. {
    injection Hyy; clear Hyy; intros; subst x1 x2.
    apply find_dup_some in Hfdj.
    destruct Hfdj as (Hij2 & lb1 & lb2 & lb3 & Hfdj).
    destruct (Nat.eq_dec y n) as [Hyn| Hyn]; subst y. {
      now apply List_seq_nothing_after_last in Hfdj.
    }
    clear Hyn.
    destruct (Nat.eq_dec x' n) as [Hx'n| Hx'n]. {
      subst x'.
      destruct (Nat.eq_dec y' n) as [Hy'n| Hy'n]; [ congruence | ].
      apply Hp2 in Hij2; cycle 1. {
        assert (H : x ∈ seq 0 (S n)). {
          rewrite Hfdi.
          now apply in_app_iff; right; left.
        }
        apply in_seq in H; cbn in H; flia Hxn H.
      } {
        assert (H : y' ∈ seq 0 (S n)). {
          rewrite Hfdj.
          apply in_app_iff; right; right.
          now apply in_app_iff; right; left.
        }
        apply in_seq in H; cbn in H; flia Hy'n H.
      }
      subst y'.
      apply List_sorted_in_seq in Hfdj.
      now apply Nat.lt_irrefl in Hfdj.
    }
    apply Hp2 in Hij1; cycle 1. {
      assert (H : x ∈ seq 0 (S n)). {
        rewrite Hfdi.
        now apply in_app_iff; right; left.
      }
      apply in_seq in H; cbn in H; flia Hxn H.
    } {
      assert (H : x' ∈ seq 0 (S n)). {
        rewrite Hfdi.
        apply in_app_iff; right; right.
        now apply in_app_iff; right; left.
      }
      apply in_seq in H; cbn in H; flia Hx'n H.
    }
    subst x'.
    apply List_sorted_in_seq in Hfdi.
    now apply Nat.lt_irrefl in Hfdi.
  }
  apply find_dup_none in Hfdj.
  exfalso; revert Hfdj.
  apply not_NoDup_map_f_seq with (b := n); [ flia | ].
  intros k Hk.
  destruct (Nat.eq_dec k n) as [Hkn| Hkn]; [ easy | ].
  apply Hp1; flia Hk Hkn.
}
apply find_dup_none in Hfdi.
exfalso; revert Hfdi.
apply not_NoDup_map_f_seq with (b := n); [ flia | ].
intros k Hk.
destruct (Nat.eq_dec k n) as [Hkn| Hkn]; [ easy | ].
apply Hp1; flia Hk Hkn.
Qed.
*)

(*
Theorem permut_fun_without_last : ∀ n i (a : _ → nat),
  is_permut_fun a (S n)
  → i = permut_fun_inv_loop a (S n) n
  → ∃ b,
     is_permut_fun b n ∧
     map a (seq 0 i ++ seq (S i) (n - i)) = map b (seq 0 n).
Proof.
intros * Hp Hi.
exists (λ j, if lt_dec j i then a j else a (j + 1)).
split. 2: {
  destruct n. {
    cbn in Hi; cbn.
    destruct (Nat.eq_dec (a 0) 0) as [Haz| Haz]; [ now subst i | exfalso ].
    apply Haz.
    destruct Hp as (Hp1, Hp2).
    enough (H : a 0 < 1) by flia H.
    apply Hp1; flia.
  }
  destruct (Nat.eq_dec (a (S n)) (S n)) as [Han| Han]. {
    remember (S n) as sn; cbn in Hi; subst sn.
    rewrite Han in Hi.
    destruct (Nat.eq_dec (S n) (S n)) as [H| H]; [ clear H | easy ].
    subst i.
    rewrite Nat.sub_diag; cbn.
    f_equal.
    rewrite app_nil_r.
    apply map_ext_in.
    intros i Hi.
    apply in_seq in Hi.
    now destruct (lt_dec i (S n)).
  }
  destruct (Nat.eq_dec i (S n)) as [Hsni| Hsni]. {
    rewrite Hsni, Nat.sub_diag.
    cbn; f_equal.
    rewrite app_nil_r.
    apply map_ext_in.
    intros j Hj.
    destruct (lt_dec j (S n)) as [Hjsn| Hjsn]; [ easy | ].
    exfalso; apply Hjsn; clear Hjsn.
    now apply in_seq in Hj.
  }
  symmetry.
  rewrite (List_seq_cut i). 2: {
    apply in_seq.
    split; [ flia | cbn ].
    enough (H : i < S (S n)) by flia Hsni H.
    rewrite Hi.
    apply permut_ub; [ | flia ].
    now apply permut_fun_inv_loop_is_permut.
  }
  symmetry; cbn - [ "-" ].
  rewrite Nat.sub_0_r, Nat.sub_succ.
  rewrite Nat.sub_succ_l. 2: {
    assert (H : i < S (S n)). {
      rewrite Hi.
      apply permut_ub; [ | flia ].
      now apply permut_fun_inv_loop_is_permut.
    }
    flia Hsni H.
  }
  do 2 rewrite map_app.
  f_equal. {
    apply map_ext_in_iff.
    intros j Hj.
    destruct (lt_dec j i) as [Hji| Hji]; [ easy | ].
    now apply in_seq in Hj.
  }
  cbn.
  destruct (lt_dec i i) as [H| H]; [ now apply lt_irrefl in H | clear H ].
  rewrite Nat.add_1_r; f_equal.
  rewrite <- seq_shift.
  rewrite map_map.
  apply map_ext_in_iff.
  intros j Hj.
  rewrite Nat.add_1_r.
  destruct (lt_dec j i) as [Hji| Hji]; [ | easy ].
  apply in_seq in Hj.
  flia Hj Hji.
}
split. {
  intros j Hj.
  assert (Hin : a i = n). {
    rewrite Hi.
    apply fun_permut_fun_inv_loop; [ easy | flia ].
  }
  destruct (lt_dec j i) as [Hji| Hji]. {
    destruct (Nat.eq_dec (a j) n) as [Hajn| Hajn]. {
      rewrite <- Hajn in Hin.
      apply Hp in Hin; [ flia Hji Hin | | flia Hj ].
      rewrite Hi.
      apply permut_ub; [ | flia ].
      now apply permut_fun_inv_loop_is_permut.
    }
    enough (H : a j < S n) by flia Hajn H.
    apply Hp; flia Hj.
  }
  apply Nat.nlt_ge in Hji.
  destruct Hp as (Hp1, Hp2).
  apply Nat.succ_lt_mono in Hj.
  specialize (Hp1 _ Hj) as H1.
  rewrite Nat.add_1_r.
  destruct (Nat.eq_dec (a (S j)) n) as [Hajn| Hajn]. {
    rewrite <- Hajn in Hin.
    apply Hp2 in Hin; [ flia Hin Hji | flia Hj Hji | easy ].
  }
  flia H1 Hajn.
}
intros j k Hj Hk Hjk.
destruct (lt_dec j i) as [Hji| Hji]. {
  destruct (lt_dec k i) as [Hki| Hki]. {
    apply Hp in Hjk; [ easy | flia Hj | flia Hk ].
  }
  apply Nat.nlt_ge in Hki.
  apply Hp in Hjk; [ flia Hji Hki Hjk | flia Hj | flia Hk ].
}
destruct (lt_dec k i) as [Hki| Hki]. {
  apply Hp in Hjk; [ | flia Hj | flia Hk ].
  apply Nat.nlt_ge in Hji.
  flia Hji Hki Hjk.
}
apply Hp in Hjk; [ flia Hjk | flia Hj | flia Hk ].
Qed.
*)

Theorem length_permut_list_inv : ∀ l,
  length (permut_list_inv l) = length l.
Proof.
intros.
destruct l as [| a]; [ easy | cbn ].
now rewrite map_length, seq_length.
Qed.

Theorem in_permut_list_inv_lt : ∀ l i, i ∈ permut_list_inv l → i < length l.
Proof.
(*
intros * Hi.
unfold permut_list_inv in Hi.
apply in_map_iff in Hi.
destruct Hi as (j & Hji & Hj).
apply in_seq in Hj.
remember (pigeonhole_fun _ _) as xx eqn:Hxx.
symmetry in Hxx.
destruct xx as (x, x').
...
apply pigeonhole with (b := length l) in Hxx; [ | flia | ]. 2: {
  intros k Hk.
  destruct (Nat.eq_dec k (length l)) as [Hkl| Hkl]; [ easy | ].
  destruct (Nat.eq_dec x (length l)) as [Hxl| Hxl]. {
    subst x x'.
...
probably needs is_permut_list l as extra hypothesis
*)
intros * Hi.
unfold permut_list_inv in Hi.
apply in_map_iff in Hi.
destruct Hi as (j & Hji & Hj).
apply in_seq in Hj.
unfold unsome in Hji.
remember (List_find_nth _ _) as k eqn:Hk.
symmetry in Hk.
destruct k as [k| ]. {
  subst k.
  now apply (List_find_nth_Some 0) in Hk.
}
subst i; flia Hj.
Qed.

Theorem permut_list_inv_inj : ∀ l,
  is_permut_list l
  → ∀ i j, i < length l → j < length l
  → nth i (permut_list_inv l) 0 = nth j (permut_list_inv l) 0
  → i = j.
Proof.
intros * Hp * Hi Hj Hij.
unfold permut_list_inv in Hij.
rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
rewrite (List_map_nth' 0) in Hij; [ | now rewrite seq_length ].
rewrite seq_nth in Hij; [ | easy ].
rewrite seq_nth in Hij; [ | easy ].
do 2 rewrite Nat.add_0_l in Hij.
unfold unsome in Hij.
remember (List_find_nth (Nat.eqb i) l) as x eqn:Hx.
remember (List_find_nth (Nat.eqb j) l) as y eqn:Hy.
move y before x.
symmetry in Hx, Hy.
destruct x as [x| ]. {
  apply (List_find_nth_Some 0) in Hx.
  destruct Hx as (Hxl & Hxbef & Hxwhi).
  destruct y as [y| ]. {
    apply (List_find_nth_Some 0) in Hy.
    destruct Hy as (Hyl & Hybef & Hywhi).
    apply Nat.eqb_eq in Hxwhi, Hywhi.
    destruct Hij; congruence.
  }
  subst x; exfalso.
  apply (permut_list_without Hp Hj).
  intros k Hk.
  specialize (List_find_nth_None 0 _ _ Hy Hk) as H1.
  apply Nat.eqb_neq in H1.
  now apply Nat.neq_sym.
} {
  exfalso.
  apply (permut_list_without Hp Hi).
  intros k Hk.
  specialize (List_find_nth_None 0 _ _ Hx Hk) as H1.
  apply Nat.eqb_neq in H1.
  now apply Nat.neq_sym.
}
Qed.

Theorem permut_list_inv_is_permut : ∀ l,
  is_permut_list l
  → is_permut_list (permut_list_inv l).
Proof.
intros * Hl.
split. {
  intros i Hi.
  rewrite length_permut_list_inv.
  now apply in_permut_list_inv_lt.
} {
  rewrite length_permut_list_inv.
  intros i j Hi Hj Hij.
  now apply permut_list_inv_inj in Hij.
}
Qed.

Theorem permut_list_Permutation : ∀ l n,
  is_permut n l
  → Permutation l (seq 0 n).
Proof.
intros * (Hp, Hln).
symmetry.
revert l Hp Hln.
induction n; intros. {
  now apply length_zero_iff_nil in Hln; subst l.
}
rewrite seq_S; cbn.
remember (ff_app (permut_list_inv l) n) as i eqn:Hi.
rewrite (List_map_ff_app_seq l).
remember (seq 0 n) as s eqn:Hs.
rewrite (List_seq_cut i); subst s. 2: {
  subst i.
  apply in_seq.
  split; [ flia | ].
  rewrite <- length_permut_list_inv.
  apply permut_list_ub; [ | rewrite length_permut_list_inv, Hln; flia ].
  now apply permut_list_inv_is_permut.
}
rewrite Nat.sub_0_r; cbn.
rewrite map_app; cbn.
rewrite Hi at 2.
rewrite (permut_permut_inv _ (conj Hp Hln) (Nat.lt_succ_diag_r _)).
apply Permutation_elt.
rewrite app_nil_r.
rewrite <- map_app.
rewrite Hln; cbn.
assert (Hin : i ≤ n). {
  apply Nat.lt_succ_r.
  rewrite Hi, <- Hln.
  rewrite <- length_permut_list_inv.
  apply permut_list_ub; [ apply permut_list_inv_is_permut, Hp | ].
  rewrite length_permut_list_inv, Hln.
  apply Nat.lt_succ_diag_r.
}
apply IHn. 2: {
  rewrite map_length, app_length, seq_length, seq_length.
  rewrite Nat.add_sub_assoc; [ now rewrite Nat.add_comm, Nat.add_sub | easy ].
}
assert (Hn : n = nth i l 0). {
  rewrite Hi; symmetry.
  apply (permut_permut_inv (S n)); [ easy | flia ].
}
split. {
  intros j Hj.
  rewrite map_length, app_length, seq_length, seq_length.
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  apply in_map_iff in Hj.
  destruct Hj as (k & Hkj & Hk).
  apply in_app_iff in Hk.
  subst j.
  assert (Hkn : nth k l 0 < n). {
    specialize permut_list_ub as H1.
    specialize (H1 l k Hp).
    rewrite Hln in H1.
    assert (H : k < S n). {
      destruct Hk as [Hk| Hk]; apply in_seq in Hk; flia Hk Hin.
    }
    specialize (H1 H); clear H.
    enough (H : nth k l 0 ≠ n) by flia H H1.
    intros H; rewrite Hn in H.
    apply Hp in H; [ | | flia Hin Hln ]. 2: {
      rewrite Hln.
      destruct Hk as [Hk| Hk]; apply in_seq in Hk; flia Hk Hin.
    }
    subst k.
    destruct Hk as [Hk| Hk]; apply in_seq in Hk; flia Hk.
  }
  destruct Hk as [Hk| Hk]; [ now apply in_seq in Hk | ].
  apply in_seq in Hk.
  now replace (S i + (n - i)) with (S n) in Hk by flia Hin.
} {
  rewrite map_length, map_app, app_length, seq_length, seq_length.
  unfold ff_app.
  replace (i + (n - i)) with n by flia Hin.
  intros j k Hj Hk Hjk.
  destruct (lt_dec j i) as [Hji| Hji]. {
    rewrite app_nth1 in Hjk; [ | now rewrite map_length, seq_length ].
    rewrite (List_map_nth' 0) in Hjk; [ | now rewrite seq_length ].
    rewrite seq_nth in Hjk; [ | easy ].
    destruct (lt_dec k i) as [Hki| Hki]. {
      rewrite app_nth1 in Hjk; [ | now rewrite map_length, seq_length ].
      rewrite (List_map_nth' 0) in Hjk; [ | now rewrite seq_length ].
      rewrite seq_nth in Hjk; [ | easy ].
      apply Hp in Hjk; [ easy | flia Hln Hj | flia Hln Hk ].
    }
    apply Nat.nlt_ge in Hki; exfalso.
    rewrite app_nth2 in Hjk; [ | now rewrite map_length, seq_length ].
    rewrite map_length, seq_length in Hjk.
    rewrite (List_map_nth' 0) in Hjk; [ | rewrite seq_length; flia Hk Hki ].
    rewrite seq_nth in Hjk; [ | flia Hk Hki ].
    replace (S i + (k - i)) with (S k) in Hjk by flia Hki.
    apply Hp in Hjk; [ flia Hjk Hji Hki | flia Hln Hj | flia Hln Hk ].
  }
  apply Nat.nlt_ge in Hji.
  rewrite app_nth2 in Hjk; [ | now rewrite map_length, seq_length ].
  rewrite map_length, seq_length in Hjk.
  rewrite (List_map_nth' 0) in Hjk; [ | rewrite seq_length; flia Hj Hji ].
  rewrite seq_nth in Hjk; [ | flia Hj Hji ].
  replace (S i + (j - i)) with (S j) in Hjk by flia Hji.
  destruct (lt_dec k i) as [Hki| Hki]. {
    rewrite app_nth1 in Hjk; [ | now rewrite map_length, seq_length ].
    rewrite (List_map_nth' 0) in Hjk; [ | now rewrite seq_length ].
    rewrite seq_nth in Hjk; [ | easy ].
    apply Hp in Hjk; [ flia Hjk Hji Hki | flia Hln Hj | flia Hln Hk ].
  }
  apply Nat.nlt_ge in Hki.
  rewrite app_nth2 in Hjk; [ | now rewrite map_length, seq_length ].
  rewrite map_length, seq_length in Hjk.
  rewrite (List_map_nth' 0) in Hjk; [ | rewrite seq_length; flia Hk Hki ].
  rewrite seq_nth in Hjk; [ | flia Hk Hki ].
  replace (S i + (k - i)) with (S k) in Hjk by flia Hki.
  apply Hp in Hjk; [ flia Hjk Hji Hki | flia Hln Hj | flia Hln Hk ].
}
Qed.
