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

Theorem List_in_split' :
  ∀ (A : Type) (eq_dec : ∀ x y : A, {x = y} + {x ≠ y}) (x : A) (l : list A),
  x ∈ l → ∃ l1 l2 : list A, l = l1 ++ x :: l2 ∧ x ∉ l1.
Proof.
intros * eq_dec * Hx.
revert x Hx.
induction l as [| y]; intros; [ easy | ].
destruct Hx as [Hx| Hx]. {
  subst y.
  now exists [], l.
}
specialize (IHl _ Hx) as H1.
destruct H1 as (l1 & l2 & Hll & Hl1).
rewrite Hll.
destruct (eq_dec y x) as [Hxy| Hxy]. {
  subst y.
  now exists [], (l1 ++ x :: l2).
}
exists (y :: l1), l2.
split; [ easy | ].
intros H; apply Hl1.
now destruct H.
Qed.

Theorem List_eq_dec_In_nth :
  ∀ (A : Type) (eq_dec : ∀ x y : A, {x = y} + {x ≠ y}) (l : list A) (x d : A),
  x ∈ l →
  ∃ n : nat, n < length l ∧ nth n l d = x ∧ ∀ m, m < n → nth m l d ≠ x.
Proof.
intros * eq_dec * Hxl.
revert x Hxl.
induction l as [| y]; intros; [ easy | ].
rewrite List_length_cons.
destruct Hxl as [Hxl| Hxl]. {
  subst y.
  exists 0.
  rewrite List_nth_0_cons.
  split; [ flia | easy ].
}
specialize (IHl x Hxl) as H1.
destruct H1 as (n & Hnl & Hyx & Hm).
destruct (eq_dec y x) as [Hxy| Hxy]. {
  subst y.
  exists 0.
  split; [ flia | easy ].
}
exists (S n).
rewrite List_nth_succ_cons.
split; [ now apply Nat.succ_lt_mono in Hnl | ].
split; [ easy | ].
intros m Hm'.
destruct m; [ easy | cbn ].
apply Nat.succ_lt_mono in Hm'.
now apply Hm.
Qed.

Theorem List_find_some_if :
  ∀ (A : Type) (eq_dec : ∀ x y : A, {x = y} + {x ≠ y}) f d (l : list A) x,
  find f l = Some x →
  ∃ i, i < length l ∧ x = nth i l d ∧ f x = true ∧
  ∀ j, j < i → f (nth j l d) = false.
Proof.
intros * eq_dec * Hf.
specialize (find_some _ _ Hf) as H1.
destruct H1 as (Hx, Hfx).
apply (List_eq_dec_In_nth A eq_dec l x d) in Hx.
destruct Hx as (i & Hi & Hix & Hx).
exists i.
split; [ easy | ].
split; [ easy | ].
split; [ easy | ].
intros j Hj.
revert i j Hi Hix Hx Hj.
induction l as [| a]; intros; [ easy | ].
cbn in Hf.
remember (f a) as b eqn:Hb; symmetry in Hb.
destruct b. {
  injection Hf; clear Hf; intros; subst a.
  clear Hb.
  destruct i; [ easy | ].
  now specialize (Hx 0 (Nat.lt_0_succ _)) as H1.
}
destruct i; [ easy | ].
cbn in Hi, Hix; apply Nat.succ_lt_mono in Hi.
destruct j; [ easy | cbn ].
apply Nat.succ_lt_mono in Hj.
apply IHl with (i := i); [ easy | easy | easy | | easy ].
intros m Hm.
specialize (Hx (S m)); cbn in Hx.
apply Hx.
now apply -> Nat.succ_lt_mono.
Qed.

Theorem find_dup_some : ∀ f x x' la,
  find_dup f la = Some (x, x')
  → f x = f x' ∧
    ∃ la1 la2 la3, la = la1 ++ x :: la2 ++ x' :: la3 ∧
    ∀ x'', x'' ∈ la1 ++ la2 → f x'' ≠ f x.
Proof.
intros * Hfd.
induction la as [| a]; [ easy | ].
cbn in Hfd.
remember (find (λ x', f x' =? f a) la) as r eqn:Hr.
symmetry in Hr.
destruct r as [n'| ]. {
  injection Hfd; clear Hfd; intros; subst x x'.
  apply (List_find_some_if _ Nat.eq_dec _ 0) in Hr.
  destruct Hr as (i & Hi & Hn'i & Heq & Hbef).
  apply Nat.eqb_eq in Heq.
  split; [ easy | ].
  exists []; cbn.
  assert (Hx'la : n' ∈ la) by now rewrite Hn'i; apply nth_In.
  apply (List_in_split' _ Nat.eq_dec) in Hx'la.
  destruct Hx'la as (l1 & l2 & Hla & Hn').
  exists l1, l2.
  rewrite Hla.
  split; [ easy | ].
  intros n'' Hx''.
  assert (Hil : i = length l1). {
    rewrite Hla in Hn'i.
    destruct (Nat.lt_trichotomy i (length l1)) as [Hil| [Hil| Hil]]. {
      rewrite app_nth1 in Hn'i; [ | easy ].
      exfalso; apply Hn'; clear Hn'.
      now subst n'; apply nth_In.
    } {
      easy.
    } {
      rewrite app_nth2 in Hn'i; [ | flia Hil ].
      specialize (Hbef (length l1) Hil) as H1.
      apply Nat.eqb_neq in H1.
      rewrite Hla in H1.
      rewrite app_nth2 in H1; [ | now unfold ge ].
      now rewrite Nat.sub_diag in H1; cbn in H1.
    }
  }
(**)
  apply (List_eq_dec_In_nth _ Nat.eq_dec _ _ 0) in Hx''.
  destruct Hx'' as (j & Hj & Hjn & Hbefn).
(*
  apply (In_nth _ _ 0) in Hx''.
  destruct Hx'' as (j & Hj & Hjn).
*)
  rewrite <- Hil in Hj.
  specialize (Hbef _ Hj) as H1.
  apply Nat.eqb_neq in H1.
  rewrite Hla in H1.
  rewrite app_nth1 in H1; [ | now rewrite Hil in Hj ].
  now rewrite Hjn in H1.
} {
  specialize (IHla Hfd).
  destruct IHla as (Hxx & la1 & la2 & la3 & Hll & Hbef).
(**)
  split; [ easy | ].
  exists (a :: la1), la2, la3; rewrite Hll.
  split; [ easy | ].
  intros x'' Hx''.
  destruct Hx'' as [Hx''| Hx'']. {
    subst x''.
    specialize (find_none _ _ Hr x) as H1.
    assert (H : x ∈ la). {
      rewrite Hll.
      now apply in_or_app; right; left.
    }
    specialize (H1 H); clear H.
    apply Nat.eqb_neq in H1.
    now apply Nat.neq_sym in H1.
  }
  now apply Hbef.
}
Qed.

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
  specialize (find_dup_some f _ _ _ Hfd) as H.
  destruct H as (Hfxx & la1 & la2 & la3 & Hll & Hbef).
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

(* version list instead of fun *)

(*
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
*)

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

Definition pigeonhole_comp_list l :=
  match find_dup (λ i, nth i l 0) (seq 0 (length l)) with
  | Some (n, n') => (n, n')
  | None => (0, 0)
  end.

Definition pigeonhole_comp_list' l :=
  match List_search_double Nat.eqb l with
  | (n, S n') => (n, n + S n')
  | (_, 0) => (0, 0)
  end.

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

Theorem search_double_loop_succ_r_if : ∀ l i j k,
  search_double_loop Nat.eqb i l = (j, S k)
  → i ≤ j ∧ j + S k < i + length l ∧
    (∀ a b, i ≤ a < j → a + S b < i + length l →
     nth (a - i) l 0 ≠ nth (a + S b - i) l 0) ∧
    (∀ b, b < k → nth (j - i) l 0 ≠ nth (j + S b - i) l 0) ∧
    nth (j - i) l 0 = nth (j + S k - i) l 0.
Proof.
intros * Hxx.
revert i j k Hxx.
induction l as [| a]; intros; [ easy | ].
rewrite <- Nat.add_succ_comm.
cbn in Hxx.
remember (List_find_nth _ _) as b eqn:Hb.
symmetry in Hb.
destruct b as [b| ]. {
  rewrite Nat.add_1_r in Hxx.
  injection Hxx; clear Hxx; intros; subst j k.
  split; [ easy | ].
  replace (S i + b - i) with (S b) by flia.
  rewrite Nat.sub_diag, List_nth_0_cons, List_nth_succ_cons.
  apply (List_find_nth_Some 0) in Hb.
  destruct Hb as (Hbl & Hbef & Heq).
  apply Nat.eqb_eq in Heq; subst a.
  split; [ cbn; flia Hbl | ].
  split; [ intros j k Hij Hjk; flia Hij | ].
  split; [ | easy ].
  intros j Hj.
  replace (i + S j - i) with (S j) by flia; cbn.
  specialize (Hbef j Hj).
  now apply Nat.eqb_neq in Hbef.
}
specialize (IHl (S i) j k Hxx) as H1.
rewrite List_length_cons.
destruct H1 as (H1 & H2 & H3 & H4 & H5).
split; [ flia H1 | ].
split; [ flia H2 | ].
split. {
  intros c d Hicj Hcdi.
  destruct (Nat.eq_dec c i) as [Hci| Hci]. {
    subst c.
    rewrite Nat.sub_diag, Nat.add_comm, Nat.add_sub; cbn.
    apply List_find_nth_None with (d := 0) (j := d) in Hb; [ | flia Hcdi ].
    now apply Nat.eqb_neq in Hb.
  }
  replace (c - i) with (S (c - S i)) by flia Hicj Hci.
  replace (c + S d - i) with (S (c + S d - S i)) by flia Hicj; cbn.
  apply H3; [ flia Hicj Hci | flia Hcdi ].
}
replace (j - i) with (S (j - S i)) by flia H1.
replace (S j + k - i) with (S (j + S k - S i)) by flia H1.
split; [ | easy ].
intros c Hc.
replace (j + S c - i) with (S (j + S c - S i)) by flia H1; cbn.
now apply H4.
Qed.

Theorem glop : ∀ l, pigeonhole_comp_list l = pigeonhole_comp_list' l.
Proof.
intros.
unfold pigeonhole_comp_list, pigeonhole_comp_list'.
remember (find_dup _ _) as a eqn:Ha.
remember (List_search_double _ _) as b eqn:Hb.
symmetry in Ha, Hb.
move b before a.
destruct b as (y, y').
destruct a as [(x, x')| ]. {
  apply find_dup_some in Ha.
  destruct Ha as (Hxx & la1 & la2 & la3 & Hla & Hbef).
  assert (Hlla1 : length la1 < length l). {
    apply (f_equal length) in Hla.
    rewrite seq_length, app_length in Hla.
    cbn in Hla; flia Hla.
  }
  assert (Hlla2 : length la1 + S (length la2) < length l). {
    apply (f_equal length) in Hla.
    rewrite seq_length, app_length in Hla; cbn in Hla.
    rewrite app_length in Hla; cbn in Hla.
    flia Hla.
  }
  assert (Hx : x < length l). {
    rewrite (List_seq_cut (length la1)) in Hla. 2: {
      apply in_seq.
      split; [ flia | easy ].
    }
    rewrite Nat.sub_0_r, Nat.add_0_l in Hla.
    apply List_app_eq_app' in Hla; [ | now rewrite seq_length ].
    destruct Hla as (Hla1 & Hla).
    cbn in Hla.
    now injection Hla; clear Hla; intros Hla Hla2; subst x.
  }
  assert (Hx' : x' < length l). {
    rewrite (List_seq_cut (length la1 + S (length la2))) in Hla. 2: {
      apply in_seq.
      split; [ flia | easy ].
    }
    rewrite Nat.sub_0_r, Nat.add_0_l in Hla.
    rewrite seq_app in Hla; cbn in Hla.
    rewrite <- app_assoc in Hla.
    apply List_app_eq_app' in Hla; [ | now rewrite seq_length ].
    destruct Hla as (Hla1 & Hla).
    cbn in Hla.
    injection Hla; clear Hla; intros Hla Hla2; subst x.
    apply List_app_eq_app' in Hla; [ | now rewrite seq_length ].
    destruct Hla as (Hla2 & Hla).
    injection Hla; clear Hla; intros Hla H; subst x'.
    easy.
  }
  destruct y'. {
    apply search_double_loop_0_r in Hb.
    destruct Hb as (_, Hb); clear y.
    specialize (proj1 (NoDup_nth l 0) Hb x x') as H1.
    specialize (H1 Hx Hx' Hxx).
    subst x'.
    apply (f_equal (map (λ i, nth i l 0))) in Hla.
    rewrite <- List_map_nth_seq in Hla.
    rewrite Hla in Hb.
    apply NoDup_map_inv in Hb.
    apply NoDup_app_iff in Hb.
    destruct Hb as (_ & Hb & _).
    apply NoDup_cons_iff in Hb.
    destruct Hb as (Hb, _).
    exfalso; apply Hb.
    apply in_app_iff; right.
    now left.
  }
  apply search_double_loop_succ_r_if in Hb; cbn in Hb.
  destruct Hb as (_ & Hyyl & Hcab & Hby & Hyy).
  do 2 rewrite Nat.sub_0_r in Hyy.
  assert (Hxlx : x < x') by now apply List_sorted_in_seq in Hla.
  destruct (Nat.lt_trichotomy x y) as [Hxy| [Hxy| Hxy]]. {
    exfalso.
    apply (Hcab x (x' - S x)); [ flia Hxy | | ]. 2: {
      do 2 rewrite Nat.sub_0_r.
      now replace (x + S (x' - S x)) with x' by flia Hxlx.
    }
    flia Hxlx Hx'.
  } {
    subst y; f_equal.
    destruct (Nat.lt_trichotomy x' (x + S y')) as [Hxy'| [Hxy'| Hxy']]. {
      exfalso.
      specialize (Hby (x' - S x)) as H1.
      assert (H : x' - S x < y') by flia Hxy' Hxlx.
      specialize (H1 H); clear H.
      do 2 rewrite Nat.sub_0_r in H1.
      rewrite <- Nat.sub_succ_l in H1 by easy; cbn in H1.
      rewrite Nat.add_sub_assoc in H1; [ | flia Hxlx ].
      now rewrite Nat.add_comm, Nat.add_sub in H1.
    } {
      easy.
    } {
      specialize (Hbef (x + S y')) as H1.
      assert (H : x + S y' ∈ la1 ++ la2). {
        apply in_or_app; right.
move Hla at bottom.
move Hxy' at bottom.
remember (x + S y') as z eqn:Hz.
assert (Hxz : x < z < x') by flia Hz Hxy'.
clear Hxy'.
...
(*
assert (la2 = seq (S (length la1)) (length la2)). {
Search (seq _ (length _)).
...
        clear - Hla Hxy' Hlla1.
Search (_ ∈ _ ↔ _).
in_seq: ∀ len start n : nat, n ∈ seq start len ↔ start ≤ n < start + len
Check In_nth.
Check nth_In.
*)
        rewrite (List_seq_cut (length la1)) in Hla. 2: {
          apply in_seq.
          split; [ flia | easy ].
        }
        apply List_app_eq_app' in Hla. 2: {
          now rewrite seq_length, Nat.sub_0_r.
        }
        destruct Hla as (_, Hla); cbn in Hla.
        injection Hla; clear Hla; intros Hxl Hla.
...
        rewrite (List_seq_cut (length la2)) in Hxl. 2: {
          apply in_seq.
...
        apply (f_equal (map (λ i, nth i l 0))) in Hla.
        rewrite <- List_map_nth_seq in Hla.
    rewrite Hla in Hb.
Check nth_In.
Check In_nth.
Check List_sorted_in_seq.
...
    replace x' with (x + S (x' - S x)) by flia Hxlx.
    f_equal; f_equal.
...
rewrite Hxx in Hyy.
...
destruct y'. {
  clear Hby.
...
    specialize (Hcab x y') as H1.
...
    do 2 rewrite Nat.sub_0_r in H1.
...
    specialize (Hcab x (x' - S x)) as H1.
    assert (H : 0 ≤ x < y) by (split; [ flia | easy ]).
    specialize (H1 H); clear H.
    enough (H : x < x').
    replace (x + S (x' - S x)) with x' in H1 by flia H.
...
      apply (f_equal length) in Hla.
      rewrite seq_length in Hla; rewrite Hla.
      assert (H : x = length la1). {
...
        apply (f_equal (map (λ i, nth i l 0))) in Hla.
        rewrite <- List_map_nth_seq in Hla.
      rewrite Hla, map_length.
      rewrite app_length; cbn.
      rewrite app_length; cbn.
...

Theorem pigeonhole_list : ∀ a l,
  a < length l
  → (∀ x, x ∈ l → x < a)
  → ∀ x x', pigeonhole_comp_list l = (x, x')
  → x < length l ∧ x' < length l ∧ x ≠ x' ∧ nth x l 0 = nth x' l 0.
Proof.
intros * Hal Hla * Hpcl.
unfold pigeonhole_comp_list in Hpcl.
remember (find_dup _ _) as fd eqn:Hfd.
symmetry in Hfd.
destruct fd as [(n, n') |]. {
  injection Hpcl; clear Hpcl; intros; subst n n'.
  specialize (find_dup_some _ _ _ _ Hfd) as (Hfxx & la1 & la2 & la3 & Hll).
  assert (Hxy : x ∈ seq 0 (length l)). {
    rewrite Hll.
    apply in_app_iff.
    now right; left.
  }
  apply in_seq in Hxy; cbn in Hxy.
  destruct Hxy as (_, Hxa).
  assert (Hx' : x' ∈ seq 0 (length l)). {
    rewrite Hll.
    apply in_app_iff; right; right.
    now apply in_app_iff; right; left.
  }
  apply in_seq in Hx'.
  split; [ easy | ].
  split; [ easy | ].
  split; [ | easy ].
  specialize (seq_NoDup (length l) 0) as H.
  rewrite Hll in H.
  apply NoDup_remove_2 in H.
  intros Hxx; apply H; subst x'.
  apply in_app_iff; right.
  now apply in_app_iff; right; left.
} {
  apply find_dup_none in Hfd.
  exfalso.
Check not_NoDup_map_f_seq.
...
  apply not_NoDup_map_f_seq with (b := a) in Hfd; [ easy | easy | ].
  intros y Hy.
  apply Hla.
  now apply nth_In.
}
Qed.

Theorem pigeonhole_list_exist : ∀ a l,
  a < length l
  → (∀ x, x ∈ l → x < a)
  → ∃ x x', x < length l ∧ x' < length l ∧ x ≠ x' ∧ nth x l 0 = nth x' l 0.
Proof.
intros * Hal Hla.
remember (pigeonhole_comp_list l) as xx' eqn:Hpf.
symmetry in Hpf.
destruct xx' as (x, x').
exists x, x'.
now apply (pigeonhole_list a l).
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
