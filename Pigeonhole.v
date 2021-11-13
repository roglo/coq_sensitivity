(* Pigeonhole
   f : A → B & card B < card A → f non injective *)

(* borrowed 2021-01-17 from my development "coq_euler_prod_form" *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Misc.

Fixpoint find_dup f (la : list nat) :=
  match la with
  | [] => None
  | n :: la' =>
      match find (λ n', f n' =? f n) la' with
      | None => find_dup f la'
      | Some n' => Some (n, n')
      end
  end.

Definition pigeonhole_fun a (f : nat → nat) :=
  match find_dup f (seq 0 a) with
  | Some (n, n') => (n, n')
  | None => (0, 0)
  end.

(**)

Fixpoint search_double_loop {A} eqb i (l : list A) :=
  match l with
  | a :: l' =>
      match List_find_nth (eqb a) l' with
      | Some j => (i, j + 1)
      | None => search_double_loop eqb (S i) l'
      end
  | [] => (0, 0)
  end.

(* from the list "l", return a couple of nat "(i, j)" where
   * j = 0, if there is no double value in "l"
   * j = S _, if the i-th value and the (i+j)-th value are equal *)
Definition List_search_double {A} eqb l := @search_double_loop A eqb 0 l.

(**)
Compute (let l := [3;4;1;4] in (List_search_double Nat.eqb l)).
Compute (let l := [7;4;1;7;7;2] in (List_search_double Nat.eqb l)).
(**)

Theorem search_double_loop_0_r : ∀ l i j,
  search_double_loop Nat.eqb i l = (j, 0)
  → j = 0 ∧ NoDup l.
Proof.
intros * Hxx.
assert (Hj : j = 0). {
  revert i j Hxx.
  induction l as [| a]; cbn; intros. {
    now injection Hxx; clear Hxx; intros; subst j.
  }
  remember (List_find_nth _ _) as b eqn:Hb.
  symmetry in Hb.
  destruct b as [b| ]; [ now rewrite Nat.add_1_r in Hxx | ].
  apply (IHl (S i) j Hxx).
}
split; [ easy | subst j ].
revert i Hxx.
induction l as [| a]; cbn; intros; [ constructor | ].
remember (List_find_nth _ _) as b eqn:Hb.
symmetry in Hb.
destruct b as [b| ]; [ now rewrite Nat.add_1_r in Hxx | ].
specialize (IHl (S i) Hxx) as H1.
constructor; [ | easy ].
intros Ha.
apply (In_nth _ _ 0) in Ha.
destruct Ha as (n & Hn & Hna).
specialize (List_find_nth_None 0 _ _ Hb) as H2.
specialize (H2 n Hn).
apply Nat.eqb_neq in H2.
now symmetry in Hna.
Qed.

Theorem search_double_loop_succ_r_lt : ∀ l i j k,
  search_double_loop Nat.eqb i l = (j, S k)
  → i ≤ j ∧ j + S k < i + length l.
Proof.
intros * Hxx.
revert i j k Hxx.
induction l as [| a]; intros; [ easy | ].
rewrite <- Nat.add_succ_comm.
cbn in Hxx |-*.
remember (List_find_nth _ _) as b eqn:Hb.
symmetry in Hb.
destruct b as [b| ]. {
  rewrite Nat.add_1_r in Hxx.
  injection Hxx; clear Hxx; intros; subst j k.
  split; [ easy | ].
  apply (List_find_nth_Some 0) in Hb.
  flia Hb.
}
specialize (IHl (S i) j k Hxx) as H1.
flia H1.
Qed.

(* "a" = #holes, "l" = list representing #pigeon → #hole *)
Theorem pigeonhole_from : ∀ i a l,
  a < length l
  → (∀ x, x ∈ l → x < a)
  → ∀ p dp,
    search_double_loop Nat.eqb i l = (p, dp)
  → (p, dp) = (0, 0) ∨
    i ≤ p ∧ p + dp < i + length l ∧ dp ≠ 0 ∧
    nth (p - i) l 0 = nth (p + dp - i) l 0.
Proof.
intros * Hnl Hn * Hxx.
destruct dp. {
  left; apply search_double_loop_0_r in Hxx.
  now destruct Hxx; subst p.
}
right.
rewrite <- and_assoc, and_comm, and_assoc.
split; [ easy | ].
rewrite and_comm, and_assoc.
clear a Hnl Hn.
split. {
  revert i Hxx.
  induction l as [| x]; intros; [ easy | ].
  cbn in Hxx.
  remember (List_find_nth _ _) as b eqn:Hb.
  symmetry in Hb.
  destruct b as [b| ]. {
    apply (List_find_nth_Some 0) in Hb.
    destruct Hb as (Hb & Hbef & Heq).
    apply Nat.eqb_eq in Heq.
    rewrite Nat.add_1_r in Hxx.
    now injection Hxx; clear Hxx; intros; subst p dp.
  }
  specialize (IHl (S i) Hxx); flia IHl.
}
split. {
  revert i Hxx.
  induction l as [| x]; intros; [ easy | ].
  cbn in Hxx.
  remember (List_find_nth _ _) as b eqn:Hb.
  symmetry in Hb.
  destruct b as [b| ]. {
    apply (List_find_nth_Some 0) in Hb.
    destruct Hb as (Hb & Hbef & Heq).
    apply Nat.eqb_eq in Heq.
    rewrite Nat.add_1_r in Hxx.
    injection Hxx; clear Hxx; intros; subst p dp.
    apply Nat.add_lt_mono_l; cbn.
    now apply -> Nat.succ_lt_mono.
  }
  specialize (IHl (S i) Hxx).
  cbn; flia IHl.
}
revert i Hxx.
induction l as [| x]; intros; [ easy | ].
cbn in Hxx.
remember (List_find_nth _ _) as b eqn:Hb.
symmetry in Hb.
destruct b as [b| ]. {
  apply (List_find_nth_Some 0) in Hb.
  destruct Hb as (Hb & Hbef & Heq).
  apply Nat.eqb_eq in Heq.
  rewrite Nat.add_1_r in Hxx.
  injection Hxx; clear Hxx; intros; subst p dp.
  now rewrite Nat.sub_diag, Nat.add_comm, Nat.add_sub; cbn.
}
destruct (lt_dec i p) as [Hip| Hip]. {
  specialize (IHl (S i) Hxx).
  rewrite Nat.add_comm.
  replace (p - i) with (S (p - S i)) by flia Hip.
  rewrite Nat.add_succ_l, Nat.sub_succ_l; [ cbn | flia Hip ].
  now replace (dp + p - i) with (p + S dp - S i) by flia Hip.
}
apply Nat.nlt_ge in Hip.
apply search_double_loop_succ_r_lt in Hxx.
flia Hxx Hip.
Qed.

Theorem NoDup_firstn : ∀ A n (l : list A), NoDup l → NoDup (firstn n l).
Proof.
intros * Hnd.
rewrite <- (firstn_skipn n) in Hnd.
now apply NoDup_app_remove_r in Hnd.
Qed.

Theorem pigeonhole_basis : ∀ a l,
  a < length l
  → (∀ x, x ∈ l → x < a)
  → NoDup l
  → False.
Proof.
intros * Hnl Hn Hnd.
Search Permutation.Permutation.
...
intros * Hnl Hn Hnd.
(*
specialize (NoDup_firstn _ a l Hnd) as Hnd'.
specialize (proj1 (NoDup_nth (firstn a l) 0) Hnd') as H1.
rewrite firstn_length in H1.
rewrite Nat.min_l in H1; [ | flia Hnl ].
*)
rewrite (List_split_at_pos 0 l Hnl) in Hnd.
rewrite List_app_cons in Hnd.
rewrite app_assoc in Hnd.
apply NoDup_app_remove_r in Hnd.
apply NoDup_app_comm in Hnd; cbn in Hnd.
specialize (Hn (nth a l 0)) as H1.
assert (H : nth a l 0 ∈ l) by now apply nth_In.
specialize (H1 H); clear H.
apply NoDup_cons_iff in Hnd.
destruct Hnd as (Ha, Hnd).
...
apply Ha; clear Ha.
Search (_ ∈ firstn _ _).
...
Search (nth _ (firstn _ _)).
rewrite <- List_nth_firstn with (j := S a).
apply nth_In.
specialize (NoDup_cons Hnd) as H2.
Search (NoDup (_ :: _)).
...
Search (NoDup (_ :: _)).
Search (NoDup (seq _ _)).
Search Permutation.Permutation.
Permutation.NoDup_Permutation_bis:
  ∀ (A : Type) (l l' : list A),
    NoDup l → length l' ≤ length l → incl l l' → Permutation.Permutation l l'
Permutation.NoDup_Permutation:
  ∀ (A : Type) (l l' : list A),
    NoDup l
    → NoDup l' → (∀ x : A, x ∈ l ↔ x ∈ l') → Permutation.Permutation l l'
...
Search (nth _ (firstn _ _)).
rewrite List_nth_firstn in H1.
Search (NoDup).
...
specialize (ListDec.NoDup_dec Nat.eq_dec (firstn a l)) as Hd.
...
intros * Hnl Hn Hnd.
revert l Hnl Hn Hnd.
induction a; intros. {
  destruct l as [| b]; [ easy | ].
  now specialize (Hn b (or_introl eq_refl)).
}
destruct l as [| b]; [ easy | cbn in Hnl ].
apply Nat.succ_lt_mono in Hnl.
remember (filter (λ i, nth i l 0 =? a) l) as la eqn:Hla.
...

(* "a" = #holes, "l" = list representing #pigeon → #hole *)
Theorem pigeonhole : ∀ a l,
  a < length l
  → (∀ x, x ∈ l → x < a)
  → ∀ p dp,
    List_search_double Nat.eqb l = (p, dp)
  → p + dp < length l ∧ dp ≠ 0 ∧ nth p l 0 = nth (p + dp) l 0.
Proof.
intros * Hnl Hn * Hxx.
specialize (pigeonhole_from 0 a l Hnl Hn p dp Hxx) as H1.
do 2 rewrite Nat.sub_0_r in H1.
destruct H1 as [H1| H1]; [ | easy ].
injection H1; clear H1; intros; subst p dp.
exfalso.
unfold List_search_double in Hxx.
apply search_double_loop_0_r in Hxx.
destruct Hxx as (_, Hnd).
...
now apply pigeonhole_basis in Hn.
...

Theorem pigeonhole' : ∀ nb_of_holes hole_of_pigeon,
  nb_of_holes < length hole_of_pigeon
  → (∀ hole, hole ∈ hole_of_pigeon → hole < nb_of_holes)
  → ∀ pigeon_1 pigeon_2,
    search_two_pigeons_sharing_hole hole_of_pigeon = (pigeon_1, pigeon_2)
  → pigeon_1 < length hole_of_pigeon ∧ pigeon_2 < length hole_of_pigeon ∧
    pigeon_1 ≠ pigeon_2 ∧
    nth pigeon_1 hole_of_pigeon 0 = nth pigeon_2 hole_of_pigeon 0.
Proof.
intros * Hnl Hn * Hxx.
unfold search_two_pigeons_sharing_hole in Hxx.
...
destruct (lt_dec x x') as [H1| H1]. {
  revert x x' n Hnl Hn Hxx H1.
  induction l as [| a]; intros; [ easy | ].
  cbn in Hxx.
  remember (List_find_nth (Nat.eqb a) l) as i eqn:Hi.
  symmetry in Hi.
  destruct i as [i| ]. {
    injection Hxx; clear Hxx; intros; subst x x'; clear H1.
    apply (List_find_nth_Some 0) in Hi.
    destruct Hi as (Hi & Hbef & Hwhi).
    split; [ cbn; flia | ].
    apply Nat.eqb_eq in Hwhi.
    split. {
      now rewrite Nat.add_1_r; cbn; apply -> Nat.succ_lt_mono.
    }
    now rewrite Nat.add_1_r.
  }
  specialize (List_find_nth_None 0 _ _ Hi) as H2.
  apply find_dup'_lt in Hxx.
  destruct Hxx as [Hxx| Hxx]. {
    subst l.
    apply Nat.lt_1_r in Hnl; subst n.
    now specialize (Hn a (or_introl eq_refl)).
  }
  split; [ easy | ].
  split; [ easy | ].
  split; [ flia H1 | ].
  specialize (Hn a (or_introl eq_refl)) as H3.
  specialize (Hn 0) as H4.
...

Theorem find_dup_some : ∀ f x x' la,
  find_dup f la = Some (x, x')
  → f x = f x' ∧
     ∃ la1 la2 la3, la = la1 ++ x :: la2 ++ x' :: la3.
Proof.
intros * Hfd.
induction la as [| a]; [ easy | ].
cbn in Hfd.
remember (find (λ x', f x' =? f a) la) as r eqn:Hr.
symmetry in Hr.
destruct r as [n'| ]. {
  injection Hfd; clear Hfd; intros; subst x x'.
  apply find_some in Hr; cbn in Hr.
  destruct Hr as (Hx'la, Hba).
  apply Nat.eqb_eq in Hba.
  split; [ easy | ].
  exists []; cbn.
  apply in_split in Hx'la.
  destruct Hx'la as (l1 & l2 & Hll).
  exists l1, l2.
  now rewrite Hll.
} {
  specialize (IHla Hfd).
  destruct IHla as (H & la1 & la2 & la3 & Hll).
  split; [ easy | ].
  now exists (a :: la1), la2, la3; rewrite Hll.
}
Qed.

...

Theorem find_dup_none : ∀ f la,
  find_dup f la = None → NoDup (map f la).
Proof.
intros * Hnd.
induction la as [| a]; [ constructor | cbn ].
constructor. {
  cbn in Hnd.
  remember (find _ _) as b eqn:Hb; symmetry in Hb.
  destruct b; [ easy | ].
  specialize (find_none _ _ Hb) as H1; cbn in H1; cbn.
  intros Ha.
  specialize (IHla Hnd).
  clear - IHla H1 Ha.
  induction la as [ | b]; [ easy | ].
  cbn in Ha.
  cbn in IHla.
  destruct Ha as [Ha| Ha]. {
    specialize (H1 b (or_introl eq_refl)).
    now apply Nat.eqb_neq in H1.
  } {
    apply NoDup_cons_iff in IHla.
    destruct IHla as (Hn, Hnd).
    specialize (IHla0 Hnd).
    apply IHla0; [ | easy ].
    intros x Hx.
    now apply H1; right.
  }
} {
  apply IHla.
  cbn in Hnd.
  remember (find _ _) as b eqn:Hb; symmetry in Hb.
  now destruct b.
}
Qed.

Theorem not_NoDup_map_f_seq : ∀ a b f,
  b < a
  → (∀ x, x < a → f x < b)
  → NoDup (map f (seq 0 a))
  → False.
Proof.
intros * Hba Hf Hfd.
revert a f Hba Hf Hfd.
induction b; intros; [ now specialize (Hf _ Hba) | ].
destruct a; [ flia Hba | ].
apply Nat.succ_lt_mono in Hba.
remember (filter (λ i, f i =? b) (seq 0 (S a))) as la eqn:Hla.
symmetry in Hla.
destruct la as [| x1]. {
  assert (H : ∀ x, x < a → f x < b). {
    intros x Hx.
    destruct (Nat.eq_dec (f x) b) as [Hfxb| Hfxb]. {
      specialize (List_filter_nil _ _ Hla x) as H1.
      assert (H : x ∈ seq 0 (S a)). {
        apply in_seq.
        flia Hx.
      }
      specialize (H1 H); clear H; cbn in H1.
      now apply Nat.eqb_neq in H1.
    }
    assert (H : x < S a) by flia Hx.
    specialize (Hf x H); clear H.
    flia Hf Hfxb.
  }
  specialize (IHb a f Hba H); clear H.
  rewrite <- Nat.add_1_r in Hfd.
  rewrite seq_app in Hfd; cbn in Hfd.
  rewrite map_app in Hfd; cbn in Hfd.
  specialize (NoDup_remove_1 _ _ _ Hfd) as H1.
  now rewrite app_nil_r in H1.
}
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]. {
  subst b.
  destruct a; [ flia Hba | ].
  specialize (Hf a) as H1.
  assert (H : a < S (S a)) by flia.
  specialize (H1 H); clear H.
  specialize (Hf (S a) (Nat.lt_succ_diag_r _)) as H2.
  apply Nat.lt_1_r in H1.
  apply Nat.lt_1_r in H2.
  do 2 rewrite <- Nat.add_1_r in Hfd.
  do 2 rewrite seq_app in Hfd; cbn in Hfd.
  rewrite <- app_assoc in Hfd.
  do 2 rewrite map_app in Hfd.
  cbn in Hfd.
  apply NoDup_remove_2 in Hfd.
  apply Hfd.
  apply in_app_iff; right.
  now rewrite H1, Nat.add_1_r, H2; left.
}
destruct la as [| x2]. {
  specialize (IHb a (λ i, if lt_dec i x1 then f i else f (i + 1)) Hba).
  cbn in IHb.
  assert (H : ∀ x, x < a → (if lt_dec x x1 then f x else f (x + 1)) < b). {
    intros x Hx.
    destruct (lt_dec x x1) as [Hxx| Hxx]. {
      assert (Hxb : f x ≠ b). {
        intros Hxb.
        assert (H : x ∈ filter (λ i, f i =? b) (seq 0 (S a))). {
          apply filter_In.
          split; [ apply in_seq; cbn; flia Hx | ].
          now apply Nat.eqb_eq.
        }
        rewrite Hla in H.
        destruct H as [H| H]; [ flia Hxx H| easy ].
      }
      specialize (Hf x).
      assert (H : x < S a) by flia Hx.
      specialize (Hf H); clear H.
      flia Hf Hxb.
    }
    apply Nat.nlt_ge in Hxx.
    specialize (Hf (x + 1)).
    assert (H : x + 1 < S a) by flia Hx.
    specialize (Hf H); clear H.
    assert (Hxb : f (x + 1) ≠ b). {
      intros Hxb.
      assert (H : x + 1 ∈ filter (λ i, f i =? b) (seq 0 (S a))). {
        apply filter_In.
        split; [ apply in_seq; cbn; flia Hx | ].
        now apply Nat.eqb_eq.
      }
      rewrite Hla in H.
      destruct H as [H| H]; [ flia Hxx H| easy ].
    }
    flia Hf Hxb.
  }
  specialize (IHb H); clear H.
  apply IHb; clear - Hfd.
  specialize (proj1 (NoDup_map_iff 0 _ _) Hfd) as H1.
  apply (NoDup_map_iff 0).
  intros x x' Hx Hx' Hxx.
  rewrite seq_length in Hx, Hx', H1.
  rewrite seq_nth in Hxx; [ | easy ].
  rewrite seq_nth in Hxx; [ cbn | easy ].
  cbn in Hxx.
  destruct (lt_dec x x1) as [Hxx1| Hxx1]. {
    destruct (lt_dec x' x1) as [Hx'x1| Hx'x1]. {
      apply H1; [ flia Hx | flia Hx' | ].
      rewrite seq_nth; [ | flia Hx ].
      rewrite seq_nth; [ easy | flia Hx' ].
    } {
      apply Nat.nlt_ge in Hx'x1.
      assert (H : x = x' + 1). {
        apply H1; [ flia Hx | flia Hx' | ].
        rewrite seq_nth; [ | flia Hx ].
        rewrite seq_nth; [ easy | flia Hx' ].
      }
      flia Hxx1 Hx'x1 H.
    }
  }
  apply Nat.nlt_ge in Hxx1.
  destruct (lt_dec x' x1) as [Hx'x1| Hx'x1]. {
    assert (H : x + 1 = x'). {
      apply H1; [ flia Hx | flia Hx' | ].
      rewrite seq_nth; [ | flia Hx ].
      rewrite seq_nth; [ easy | flia Hx' ].
    }
    flia Hxx1 Hx'x1 H.
  } {
    apply Nat.nlt_ge in Hx'x1.
    apply (Nat.add_cancel_r _ _ 1).
    apply H1; [ flia Hx | flia Hx' | ].
    rewrite seq_nth; [ | flia Hx ].
    rewrite seq_nth; [ easy | flia Hx' ].
  }
}
assert (Hx1 : x1 ∈ x1 :: x2 :: la) by now left.
assert (Hx2 : x2 ∈ x1 :: x2 :: la) by now right; left.
rewrite <- Hla in Hx1.
rewrite <- Hla in Hx2.
apply filter_In in Hx1.
apply filter_In in Hx2.
destruct Hx1 as (Hx1, Hfx1).
destruct Hx2 as (Hx2, Hfx2).
apply Nat.eqb_eq in Hfx1.
apply Nat.eqb_eq in Hfx2.
assert (H : x1 ≠ x2). {
  intros H; subst x2.
  clear - Hla.
  specialize (seq_NoDup (S a) 0) as H1.
  specialize (NoDup_filter (λ i, f i =? b) H1) as H2.
  rewrite Hla in H2.
  apply NoDup_cons_iff in H2.
  destruct H2 as (H2, _); apply H2.
  now left.
}
clear - Hfd Hx1 Hx2 H Hfx1 Hfx2.
remember (seq 0 (S a)) as l; clear a Heql.
apply H; clear H.
specialize (proj1 (NoDup_map_iff 0 l (λ x, f x)) Hfd) as H1.
cbn in H1.
apply (In_nth _ _ 0) in Hx1.
apply (In_nth _ _ 0) in Hx2.
destruct Hx1 as (n1 & Hn1 & Hx1).
destruct Hx2 as (n2 & Hn2 & Hx2).
specialize (H1 _ _ Hn1 Hn2) as H2.
rewrite Hx1, Hx2, Hfx1, Hfx2 in H2.
rewrite <- Hx1, <- Hx2.
f_equal.
now apply H2.
Qed.

Theorem pigeonhole : ∀ a b f,
  b < a
  → (∀ x, x < a → f x < b)
  → ∀ x x', pigeonhole_fun a f = (x, x')
  → x < a ∧ x' < a ∧ x ≠ x' ∧ f x = f x'.
Proof.
intros * Hba Hf * Hpf.
unfold pigeonhole_fun in Hpf.
remember (find_dup _ _) as fd eqn:Hfd.
symmetry in Hfd.
destruct fd as [(n, n') |]. {
  injection Hpf; clear Hpf; intros; subst n n'.
  specialize (find_dup_some f _ _ _ Hfd) as (Hfxx & la1 & la2 & la3 & Hll).
  assert (Hxy : x ∈ seq 0 a). {
    rewrite Hll.
    apply in_app_iff.
    now right; left.
  }
  apply in_seq in Hxy; cbn in Hxy.
  destruct Hxy as (_, Hxa).
  assert (Hx' : x' ∈ seq 0 a). {
    rewrite Hll.
    apply in_app_iff; right; right.
    now apply in_app_iff; right; left.
  }
  apply in_seq in Hx'.
  split; [ easy | ].
  split; [ easy | ].
  split; [ | easy ].
  specialize (seq_NoDup a 0) as H.
  rewrite Hll in H.
  apply NoDup_remove_2 in H.
  intros Hxx; apply H; subst x'.
  apply in_app_iff; right.
  now apply in_app_iff; right; left.
} {
  apply find_dup_none in Hfd.
  exfalso.
  now apply not_NoDup_map_f_seq in Hf.
}
Qed.

Theorem pigeonhole_exist : ∀ a b f,
  b < a
  → (∀ x, x < a → f x < b)
  → ∃ x x', x < a ∧ x' < a ∧ x ≠ x' ∧ f x = f x'.
Proof.
intros * Hba Hf.
remember (pigeonhole_fun a f) as xx' eqn:Hpf.
symmetry in Hpf.
destruct xx' as (x, x').
exists x, x'.
now apply (pigeonhole a b).
Qed.

(* fin_t : finite type, implemented with type "sig" *)

Definition fin_t n := {a : nat | (a <? n) = true}.

Theorem fin_t_fun_le : ∀ m n (f : fin_t m → fin_t n) g,
  (∀ y, f (g y) = y) → n ≤ m.
Proof.
intros * Hfg.
specialize (pigeonhole) as H1.
specialize (H1 n m).
apply Nat.nlt_ge; intros Hmn.
set (f' := λ y : nat,
  match lt_dec y n with
  | left Hyn =>
      let H := proj2 (Nat.ltb_lt y n) Hyn in
      proj1_sig (g (exist (λ a, (a <? n) = true) y H))
  | right b => 0
  end).
specialize (H1 f' Hmn).
assert (H : ∀ x, x < n → f' x < m). {
  intros x Hx; unfold f'; cbn - [ "<?" ].
  destruct (lt_dec x n) as [H| H]; [ | flia Hx H ].
  remember (g _) as y eqn:Hy.
  destruct y as (y, py).
  now apply Nat.ltb_lt.
}
specialize (H1 H); clear H.
unfold pigeonhole_fun in H1.
remember (find_dup f' (seq 0 n)) as x eqn:Hx; symmetry in Hx.
destruct x as [(n1, n2)| ]; [ | now apply (H1 0 0 eq_refl) ].
specialize (H1 n1 n2 eq_refl).
destruct H1 as (Hn1n & Hn2n & Hnn & Hfnn).
unfold f' in Hfnn.
destruct (lt_dec n1 n) as [H1| H]; [ | flia Hn1n H ].
destruct (lt_dec n2 n) as [H2| H]; [ | flia Hn2n H ].
remember (g _) as x eqn:Hx' in Hfnn.
remember (g _) as y eqn:Hy' in Hfnn.
destruct x as (x, px).
destruct y as (y, py).
cbn in Hfnn.
subst y.
move py before px.
assert (H : px = py). {
  clear - px py.
  apply (Eqdep_dec.UIP_dec Bool.bool_dec).
}
destruct H.
rewrite Hy' in Hx'.
apply (f_equal f) in Hx'.
do 2 rewrite Hfg in Hx'.
now injection Hx'; intros H; symmetry in H.
Qed.

Theorem bijective_fin_t : ∀ m n (f : fin_t m → fin_t n),
  FinFun.Bijective f → m = n.
Proof.
intros * Hf.
destruct Hf as (g & Hgf & Hfg).
destruct (Nat.lt_trichotomy m n) as [Hmn| [Hmn| Hmn]]; [ | easy | ]. {
  exfalso.
  apply Nat.nle_gt in Hmn; apply Hmn; clear Hmn.
  now apply fin_t_fun_le in Hfg.
} {
  exfalso.
  apply Nat.nle_gt in Hmn; apply Hmn; clear Hmn.
  now apply fin_t_fun_le in Hgf.
}
Qed.

(* end fin_t *)
