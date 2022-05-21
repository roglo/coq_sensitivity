(* Testing if a list is a permutation of another one *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.

Import List List.ListNotations.
Require Import Misc.

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

Fixpoint is_permutation {A} (eqb : A → A → bool) (la lb : list A) :=
  match la with
  | [] => match lb with [] => true | _ => false end
  | a :: la' =>
      match extract (eqb a) lb with
      | None => false
      | Some (bef, _, aft) => is_permutation eqb la' (bef ++ aft)
      end
  end.

Definition permutation A (eqb : A → _) la lb := is_permutation eqb la lb = true.

Theorem fold_permutation : ∀ A (eqb : A → _) la lb,
  is_permutation eqb la lb = true → permutation eqb la lb.
Proof. easy. Qed.

(*
Require Import Relations.

(* allows to use "reflexivity" (or "easy"), "symmetry" and "transitivity"
   on goals eqb x y = true, without having to add "apply Heqb" before *)
Section a.

Context {A : Type}.
Context {eqb : A → A → bool}.
Context {Heqb : equality eqb}.

Definition eqp a b := eqb a b = true.

Theorem eqp_refl : reflexive _ eqp.
Proof. now intros x; apply Heqb. Qed.

Theorem eqp_sym : symmetric _ eqp.
Proof. now intros x y Hxy; apply Heqb in Hxy; apply Heqb; symmetry. Qed.

Theorem eqp_trans : transitive _ eqp.
Proof.
intros x y z Hxy Hyz.
apply Heqb in Hxy, Hyz; apply Heqb.
now transitivity y.
Qed.

Add Parametric Relation : A eqp
 reflexivity proved by eqp_refl
 symmetry proved by eqp_sym
 transitivity proved by eqp_trans
 as eqp_rel.
*)

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

Theorem permutation_cons_l_iff : ∀ A (eqb : A → _) a la lb,
  permutation eqb (a :: la) lb
  ↔ match extract (eqb a) lb with
     | Some (bef, _, aft) => permutation eqb la (bef ++ aft)
     | None => False
     end.
Proof.
intros.
unfold permutation; cbn.
remember (extract (eqb a) lb) as lxl eqn:Hlxl.
now destruct lxl as [((bef, x), aft)| ].
Qed.

(* *)

Theorem permutation_cons_inv : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb a,
  permutation eqb (a :: la) (a :: lb) → permutation eqb la lb.
Proof.
intros * Heqb * Hpab.
apply permutation_cons_l_iff in Hpab.
cbn in Hpab.
now rewrite (equality_refl Heqb) in Hpab.
Qed.

Theorem permutation_app_inv_aux : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb lc ld a,
  a ∉ la
  → a ∉ lc
  → permutation eqb (la ++ a :: lb) (lc ++ a :: ld)
  → permutation eqb (la ++ lb) (lc ++ ld).
Proof.
intros * Heqb * Hala Halc Hp.
revert lb lc ld a Hp Hala Halc.
induction la as [| b]; intros. {
  clear Hala; cbn in Hp |-*.
  apply permutation_cons_l_iff in Hp.
  remember (extract (eqb a) (lc ++ a :: ld)) as lxl eqn:Hlxl.
  symmetry in Hlxl.
  destruct lxl as [((bef, x), aft)| ]; [ | easy ].
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef & H & Hlb).
  apply Heqb in H; subst x.
  apply app_eq_app in Hlb.
  destruct Hlb as (l & Hlb).
  destruct Hlb as [(H1, H2)| (H1, H2)]. {
    subst lc.
    destruct l as [| b]; cbn in H2. {
      injection H2; clear H2; intros; subst aft.
      now rewrite app_nil_r.
    }
    injection H2; clear H2; intros H2 H; subst b.
    exfalso; apply Halc.
    now apply in_or_app; right; left.
  }
  subst bef.
  destruct l as [| b]; cbn in H2. {
    injection H2; clear H2; intros; subst aft.
    now rewrite app_nil_r in Hp.
  }
  injection H2; clear H2; intros H2 H; subst b.
  specialize (Hbef a) as H1.
  assert (H : a ∈ lc ++ a :: l) by now apply in_or_app; right; left.
  specialize (H1 H); clear H.
  now rewrite (equality_refl Heqb) in H1.
}
cbn in Hp |-*.
apply permutation_cons_l_iff in Hp.
remember (extract (eqb b) (lc ++ a :: ld)) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x.
apply app_eq_app in Hlb.
destruct Hlb as (l & Hlb).
destruct Hlb as [(H1, H2)| (H1, H2)]. {
  subst lc.
  destruct l as [| c]; cbn in H2. {
    injection H2; clear H2; intros; subst aft b.
    now exfalso; apply Hala; left.
  }
  injection H2; clear H2; intros H2 H; subst c aft.
  rewrite <- app_assoc.
  apply permutation_cons_l_iff.
  remember (extract (eqb b) (bef ++ (b :: l) ++ ld)) as lxl eqn:Hlxl.
  symmetry in Hlxl.
  destruct lxl as [((bef', x), aft')| ]. 2: {
    specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
    specialize (H1 b).
    assert (H : b ∈ bef ++ (b :: l) ++ ld). {
      now apply in_or_app; right; left.
    }
    specialize (H1 H); clear H.
    now rewrite (equality_refl Heqb) in H1.
  }
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef' & H & Hlb).
  apply Heqb in H; subst x.
  apply app_eq_app in Hlb.
  destruct Hlb as (l' & Hlb).
  destruct Hlb as [(H1, H2)| (H1, H2)]. {
    subst bef.
    destruct l' as [| c]; cbn in H2. 2: {
      injection H2; clear H2; intros H2 H; subst c aft'.
      specialize (Hbef b) as H1.
      assert (H : b ∈ bef' ++ b :: l'). {
        now apply in_or_app; right; left.
      }
      specialize (H1 H); clear H.
      now rewrite (equality_refl Heqb) in H1.
    }
    injection H2; clear H2; intros; subst aft'.
    rewrite app_nil_r in Hp, Halc.
    rewrite app_assoc.
    apply IHla with (a := a); cycle 1. {
      now intros H; apply Hala; right.
    } {
      intros H; apply Halc.
      apply in_app_or in H.
      apply in_or_app.
      now destruct H as [H| H]; [ left | right; right ].
    }
    now rewrite <- app_assoc.
  }
  subst bef'.
  destruct l' as [| c]; cbn in H2. 2: {
    injection H2; clear H2; intros H2 H; subst c.
    specialize (Hbef' b) as H1.
    assert (H : b ∈ bef ++ b :: l'). {
      now apply in_or_app; right; left.
    }
    specialize (H1 H); clear H.
    now rewrite (equality_refl Heqb) in H1.
  }
  injection H2; clear H2; intros H2; subst aft'.
  rewrite app_nil_r in Hbef' |-*.
  rewrite app_assoc.
  apply IHla with (a := a); cycle 1. {
    now intros H; apply Hala; right.
  } {
    intros H; apply Halc.
    apply in_app_or in H.
    apply in_or_app.
    now destruct H as [H| H]; [ left | right; right ].
  }
  now rewrite <- app_assoc.
}
subst bef.
apply permutation_cons_l_iff.
remember (extract (eqb b) (lc ++ ld)) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef, x), aft')| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  specialize (H1 b).
  assert (H : b ∈ lc ++ ld). {
    apply in_or_app; right.
    specialize (in_elt b l aft) as H3.
    rewrite <- H2 in H3.
    destruct H3 as [H3| H3]; [ subst b | easy ].
    now exfalso; apply Hala; left.
  }
  specialize (H1 H); clear H.
  now rewrite (equality_refl Heqb) in H1.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef' & H & Hlb).
apply Heqb in H; subst x.
apply app_eq_app in Hlb.
destruct Hlb as (l' & Hlb).
destruct Hlb as [(H1, H3)| (H1, H3)]. 2: {
  subst bef ld.
  rewrite app_comm_cons in H2.
  apply app_eq_app in H2.
  destruct H2 as (l'' & H2).
  destruct H2 as [(H2, H4)| (H2, H4)]. {
    destruct l'' as [| c]. {
      rewrite app_nil_r in H2; subst l; cbn in H4.
      injection H4; clear H4; intros; subst aft'.
      rewrite <- app_assoc.
      apply IHla with (a := a); [ | | easy ]. 2: {
        now intros H; apply Hala; right.
      }
      now rewrite app_comm_cons, app_assoc.
    }
    cbn in H4.
    injection H4; clear H4; intros H4 H; subst c aft.
    specialize (Hbef' b) as H1.
    assert (H : b ∈ lc ++ l'). {
      apply in_or_app; right.
      specialize (in_elt b l l'') as H3.
      rewrite <- H2 in H3.
      destruct H3 as [H3| H3]; [ subst b | easy ].
      now exfalso; apply Hala; left.
    }
    specialize (H1 H); clear H.
    now rewrite (equality_refl Heqb) in H1.
  }
  subst l.
  destruct l'' as [| c]. {
    rewrite app_nil_r in Hp.
    cbn in H4.
    injection H4; clear H4; intros; subst aft'.
    rewrite <- app_assoc.
    apply IHla with (a := a); [ | | easy ]. 2: {
      now intros H; apply Hala; right.
    }
    now rewrite app_comm_cons, app_assoc.
  }
  cbn in H4.
  injection H4; clear H4; intros H4 H; subst c aft'.
  specialize (Hbef b) as H1.
  assert (H : b ∈ lc ++ (a :: l') ++ b :: l''). {
    apply in_or_app; right.
    now apply in_or_app; right; left.
  }
  specialize (H1 H); clear H.
  now rewrite (equality_refl Heqb) in H1.
}
subst lc.
move H2 before H3.
destruct l as [| c]. {
  cbn in H2.
  injection H2; clear H2; intros; subst b aft.
  now exfalso; apply Hala; left.
}
cbn in H2.
injection H2; clear H2; intros H2 H; subst c ld.
destruct l' as [| c]. {
  cbn in H3.
  rewrite app_nil_r in Hp, Hbef, Halc.
  destruct l as [| c]. {
    cbn in H3.
    injection H3; clear H3; intros; subst aft'.
    rewrite <- app_assoc in Hp; cbn in Hp.
    apply IHla with (a := a); [ easy | | easy ].
    now intros H; apply Hala; right.
  }
  cbn in H3.
  injection H3; clear H3; intros H3 H; subst c aft'.
  specialize (Hbef b) as H1.
  assert (H : b ∈ bef ++ a :: b :: l). {
    now apply in_or_app; right; right; left.
  }
  specialize (H1 H); clear H.
  now rewrite (equality_refl Heqb) in H1.
}
cbn in H3.
injection H3; clear H3; intros H3 H; subst c.
specialize (Hbef b) as H1.
assert (H : b ∈ (bef ++ b :: l') ++ a :: l). {
  apply in_or_app; left.
  now apply in_or_app; right; left.
}
specialize (H1 H); clear H.
now rewrite (equality_refl Heqb) in H1.
Qed.

(* *)

Theorem permutation_refl : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l, permutation eqb l l.
Proof.
intros * Heqb *.
induction l as [| a]; [ easy | cbn ].
apply permutation_cons_l_iff; cbn.
now rewrite (equality_refl Heqb).
Qed.

Theorem permutation_in_r : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb a, permutation eqb la lb → a ∈ lb → a ∈ la.
Proof.
intros * Heqb * Hpab Hlb.
revert a lb Hpab Hlb.
induction la as [| b]; intros; [ now destruct lb | ].
apply permutation_cons_l_iff in Hpab.
remember (extract (eqb b) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlba).
apply Heqb in H; subst x lb.
apply in_app_or in Hlb.
destruct Hlb as [Hlb| Hlb]. 2: {
  destruct Hlb as [Hlb| Hlb]; [ now left | right ].
  apply (IHla a (bef ++ aft) Hpab).
  now apply in_or_app; right.
}
right; apply (IHla a (bef ++ aft) Hpab).
now apply in_or_app; left.
Qed.

Theorem permutation_sym : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb, permutation eqb la lb → permutation eqb lb la.
Proof.
intros * Heqb * Hab.
revert la Hab.
induction lb as [| b]; intros; [ now destruct la | cbn ].
apply permutation_cons_l_iff.
remember (extract (eqb b) la) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1; clear Hlxl.
  specialize (permutation_in_r Heqb) as H2.
  specialize (H2 _ _ b Hab).
  specialize (H2 (or_introl eq_refl)).
  specialize (H1 _ H2).
  now rewrite (equality_refl Heqb) in H1.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (H1 & H2 & H3).
apply Heqb in H2; subst x.
subst la.
apply IHlb.
replace lb with ([] ++ lb) by easy.
apply permutation_app_inv_aux with (a := b); [ easy | | easy | easy ].
intros H; specialize (H1 _ H).
now rewrite (equality_refl Heqb) in H1.
Qed.

Theorem permutation_nil_l : ∀ A (eqb : A → _) l,
  permutation eqb [] l → l = [].
Proof. now intros; destruct l. Qed.

Theorem permutation_nil_r : ∀ A (eqb : A → _) l,
  permutation eqb l [] → l = [].
Proof. now intros; destruct l. Qed.

Theorem permutation_trans : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb lc,
  permutation eqb la lb → permutation eqb lb lc → permutation eqb la lc.
Proof.
intros * Heqb * Hab Hbc.
revert lb lc Hab Hbc.
induction la as [| a]; intros; cbn. {
  now cbn in Hab, Hbc; destruct lb.
}
cbn in Hab.
apply permutation_cons_l_iff.
remember (extract (eqb a) lc) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  clear Hlxl.
  apply permutation_cons_l_iff in Hab.
  remember (extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef, x), aft) | ]; [ | easy ].
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef & H & Hlb).
  apply Heqb in H; subst x.
  apply (permutation_sym Heqb) in Hbc.
  specialize (permutation_in_r Heqb) as H2.
  specialize (H2 _ _ a Hbc).
  assert (H : a ∈ lb) by now subst lb; apply in_or_app; right; left.
  specialize (H2 H); clear H.
  specialize (H1 _ H2).
  now rewrite (equality_refl Heqb) in H1.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x.
apply permutation_cons_l_iff in Hab.
remember (extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef', x), aft')| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef' & H & Hlb').
apply Heqb in H; subst x.
subst lb lc.
apply IHla with (lb := bef' ++ aft'); [ easy | ].
assert (Hanb : a ∉ bef). {
  intros H; apply Hbef in H.
  now rewrite (equality_refl Heqb) in H.
}
assert (Hanb' : a ∉ bef'). {
  intros H; apply Hbef' in H.
  now rewrite (equality_refl Heqb) in H.
}
clear Hbef Hbef'.
clear la IHla Hab.
now apply permutation_app_inv_aux in Hbc.
Qed.

(* *)

(*
(* allows to use "reflexivity" (or "easy"), "symmetry" and "transitivity"
   on goals "permutation eqb la lb", instead of applying
   "permutation_refl", "permutation_sym" and "permutation_trans".
*)
Section a.

Context {A : Type}.
Context {eqb : A → A → bool}.
Context {Heqb : equality eqb}.

Add Parametric Relation : (list A) (permutation eqb)
 reflexivity proved by (permutation_refl Heqb)
 symmetry proved by (permutation_sym Heqb)
 transitivity proved by (permutation_trans Heqb)
 as permutation_rel.
*)

(* theorems equivalent to Permutation type *)

Theorem permutation_nil_nil : ∀ A (eqb : A → _), permutation eqb [] [].
Proof. easy. Qed.

Theorem permutation_skip : ∀ A (eqb : A → _),
  equality eqb →
  ∀ a la lb, permutation eqb la lb → permutation eqb (a :: la) (a :: lb).
Proof.
intros * Heqb * Hpab; cbn.
apply permutation_cons_l_iff; cbn.
now rewrite (equality_refl Heqb).
Qed.

Theorem permutation_swap : ∀ A (eqb : A → _),
  equality eqb →
  ∀ a b la, permutation eqb (b :: a :: la) (a :: b :: la).
Proof.
intros * Heqb *.
apply permutation_cons_l_iff; cbn.
rewrite (equality_refl Heqb).
remember (eqb b a) as ba eqn:Hba; symmetry in Hba.
destruct ba; [ | now apply permutation_refl ].
apply Heqb in Hba; subst b.
now apply permutation_refl.
Qed.

(* *)

Theorem permutation_add_inv : ∀ A (eqb : A → _) (Heqb : equality eqb),
  ∀ a la lb,
  permutation eqb la lb
  → ∀ lc ld,
  permutation eqb (a :: lc) la
  → permutation eqb (a :: ld) lb
  → permutation eqb lc ld.
Proof.
intros * Heqb * Hab * Hc Hd.
apply permutation_cons_l_iff in Hc, Hd.
remember (extract (eqb a) la) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((befa, x), afta)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (H1 & H & H3).
apply Heqb in H; subst x la.
remember (extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((befb, x), aftb)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (H2 & H & H4).
apply Heqb in H; subst x lb.
move H2 before H1.
apply (permutation_app_inv_aux Heqb) in Hab; cycle 1. {
  intros H; specialize (H1 _ H).
  now rewrite (equality_refl Heqb) in H1.
} {
  intros H; specialize (H2 _ H).
  now rewrite (equality_refl Heqb) in H2.
}
apply (permutation_trans Heqb) with (lb := befa ++ afta); [ easy | ].
apply (permutation_trans Heqb) with (lb := befb ++ aftb); [ easy | ].
now apply (permutation_sym Heqb).
Qed.

(* *)

Theorem permutation_in : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb a, permutation eqb la lb → a ∈ la → a ∈ lb.
Proof.
intros * Heqb * Hpab Hla.
revert a lb Hpab Hla.
induction la as [| b]; intros; [ easy | ].
apply permutation_cons_l_iff in Hpab.
remember (extract (eqb b) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x lb.
destruct Hla as [Hla| Hla]. {
  now subst b; apply in_or_app; right; left.
}
assert (Ha : a ∈ bef ++ aft) by now apply IHla.
apply in_app_or in Ha.
apply in_or_app.
now destruct Ha; [ left | right; right ].
Qed.

Theorem permutation_app_tail : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l l' tl,
  permutation eqb l l' → permutation eqb (l ++ tl) (l' ++ tl).
Proof.
intros * Heqb * Hll'.
revert l' tl Hll'.
induction l as [| a]; intros. {
  destruct l'; [ apply (permutation_refl Heqb) | easy ].
}
rewrite <- app_comm_cons; cbn in Hll' |-*.
apply permutation_cons_l_iff in Hll'.
remember (extract (eqb a) l') as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef', x), aft')| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x.
apply permutation_cons_l_iff.
remember (extract (eqb a) (l' ++ tl)) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1; clear Hlxl.
  specialize (H1 a).
  assert (H : a ∈ l' ++ tl). {
    subst l'.
    apply in_or_app; left.
    now apply in_or_app; right; left.
  }
  specialize (H1 H).
  now rewrite (equality_refl Heqb) in H1.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef' & H & Hlb').
apply Heqb in H; subst x.
subst l'.
rewrite <- app_assoc in Hlb'; cbn in Hlb'.
apply app_eq_app in Hlb'.
destruct Hlb' as (l' & H1).
destruct H1 as [(H1, H2)| (H1, H2)]. {
  subst bef'.
  destruct l' as [| b]. {
    cbn in H2.
    injection H2; clear H2; intros H2; subst aft.
    rewrite app_assoc.
    rewrite app_nil_r in Hll'.
    now apply IHl.
  }
  cbn in H2.
  injection H2; clear H2; intros H2 H; subst b aft.
  specialize (Hbef a).
  assert (H : a ∈ bef ++ a :: l') by now apply in_or_app; right; left.
  specialize (Hbef H); clear H.
  now rewrite (equality_refl Heqb) in Hbef.
}
subst bef.
destruct l' as [| b]. {
  cbn in H2.
  injection H2; clear H2; intros; subst aft.
  rewrite app_nil_r, app_assoc.
  now apply IHl.
}
cbn in H2.
injection H2; clear H2; intros H2 H; subst b.
specialize (Hbef' a).
assert (H : a ∈ bef' ++ a :: l') by now apply in_or_app; right; left.
specialize (Hbef' H); clear H.
now rewrite (equality_refl Heqb) in Hbef'.
Qed.

Theorem permutation_app_head : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l tl tl',
  permutation eqb tl tl' → permutation eqb (l ++ tl) (l ++ tl').
Proof.
intros * Heqb * Hll'.
revert tl tl' Hll'.
induction l as [| a]; intros; [ easy | ].
apply permutation_cons_l_iff; cbn.
rewrite (equality_refl Heqb).
now apply IHl.
Qed.

Theorem permutation_app : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l m l' m',
  permutation eqb l l'
  → permutation eqb m m'
  → permutation eqb (l ++ m) (l' ++ m').
Proof.
intros * Heqb * Hll' Hmm'.
apply (permutation_trans Heqb) with (lb := l ++ m'). {
  now apply permutation_app_head.
}
now apply permutation_app_tail.
Qed.

Theorem permutation_cons_append : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l x, permutation eqb (x :: l) (l ++ [x]).
Proof.
intros * Heqb *.
revert x.
induction l as [| a]; intros; [ now apply permutation_refl | cbn ].
eapply (permutation_trans Heqb); [ apply (permutation_swap Heqb) | ].
now apply permutation_skip.
Qed.

Theorem permutation_app_comm : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l l', permutation eqb (l ++ l') (l' ++ l).
Proof.
intros * Heqb *.
remember (length (l ++ l')) as len eqn:Hlen; symmetry in Hlen.
revert l l' Hlen.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct len. {
  apply length_zero_iff_nil in Hlen.
  apply app_eq_nil in Hlen.
  destruct Hlen; subst l l'.
  now apply permutation_refl.
}
destruct l as [| a]. {
  rewrite app_nil_r.
  now apply permutation_refl.
}
cbn in Hlen; apply Nat.succ_inj in Hlen; cbn.
apply permutation_cons_l_iff.
remember (extract (eqb a) (l' ++ a :: l)) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ].  2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  specialize (H1 a).
  assert (H : a ∈ l' ++ a :: l) by now apply in_or_app; right; left.
  specialize (H1 H); clear H.
  now rewrite equality_refl in H1.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x.
eapply (permutation_trans Heqb). {
  apply IHlen with (m := length (l ++ l')); [ | easy ].
  now rewrite Hlen.
}
apply app_eq_app in Hlb.
destruct Hlb as (l'' & Hlb).
destruct Hlb as [(H1, H2)| (H1, H2)]. {
  rewrite H1, <- app_assoc.
  apply (permutation_app_head Heqb).
  destruct l'' as [| x]. {
    cbn in H2.
    injection H2; clear H2; intros; subst aft.
    now apply permutation_refl.
  }
  cbn in H2.
  injection H2; clear H2; intros H2 H; subst x.
  destruct l as [| b]. {
    rewrite app_nil_r, H2.
    replace (a :: l'') with ([a] ++ l'') by easy.
    apply IHlen with (m := (length ([a] ++ l''))); [ | easy ].
    subst len; cbn.
    apply -> Nat.succ_lt_mono.
    rewrite H1; cbn.
    rewrite app_length; cbn.
    flia.
  }
  rewrite H2, List_app_cons, app_assoc.
  apply (permutation_sym Heqb).
  do 2 rewrite List_app_cons, app_assoc.
  apply (permutation_app_tail Heqb).
  apply (permutation_app_tail Heqb).
  apply IHlen with (m := length (l'' ++ [a])); [ | easy ].
  rewrite <- Hlen, H1;cbn.
  do 3 rewrite app_length; cbn.
  flia.
}
destruct l'' as [| x]. {
  cbn in H2.
  injection H2; clear H2; intros; subst aft.
  rewrite app_nil_r in H1; subst bef.
  now apply permutation_refl.
}
cbn in H2.
injection H2; clear H2; intros H2 H; subst x.
rewrite H1, H2.
rewrite List_app_cons.
do 2 rewrite app_assoc.
apply (permutation_app_tail Heqb).
rewrite <- app_assoc.
apply (permutation_app_head Heqb).
apply IHlen with (m := length (l'' ++ [a])); [ | easy ].
rewrite <- Hlen, H2.
do 3 rewrite app_length; cbn; flia.
Qed.

Theorem permutation_cons_app : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l l1 l2 a,
  permutation eqb l (l1 ++ l2)
  → permutation eqb (a :: l) (l1 ++ a :: l2).
Proof.
intros * Heqb * H12; cbn.
apply permutation_cons_l_iff.
remember (extract (eqb a) (l1 ++ a :: l2)) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  clear Hlxl.
  specialize (H1 a).
  rewrite (equality_refl Heqb) in H1.
  apply Bool.diff_true_false, H1.
  now apply in_or_app; right; left.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x.
apply app_eq_app in Hlb.
destruct Hlb as (l' & Hlb).
destruct Hlb as [(H1, H2)| (H1, H2)]. {
  subst l1.
  destruct l' as [| b]; cbn in H2. {
    rewrite app_nil_r in H12.
    now injection H2; clear H2; intros; subst aft.
  }
  injection H2; clear H2; intros H2 H; subst b aft.
  remember ((bef ++ a :: l') ++ l2) as lb eqn:Hlb.
  apply (permutation_trans Heqb) with (lb := lb); [ easy | subst lb ].
  rewrite <- app_assoc.
  apply (permutation_app_head Heqb).
  rewrite List_app_cons, app_assoc.
  apply (permutation_app_tail Heqb).
  replace (a :: l') with ([a] ++ l') by easy.
  now apply permutation_app_comm.
}
destruct l' as [| b]. {
  cbn in H2; rewrite app_nil_r in H1.
  now injection H2; clear H2; intros; subst bef aft.
}
cbn in H2.
injection H2; clear H2; intros H2 H; subst b.
specialize (Hbef a).
assert (H : a ∈ bef) by now rewrite H1; apply in_or_app; right; left.
specialize (Hbef H).
now rewrite equality_refl in Hbef.
Qed.

Theorem permutation_middle : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb a,
  permutation eqb (a :: la ++ lb) (la ++ a :: lb).
Proof.
intros * Heqb *.
apply (permutation_cons_app Heqb).
now apply permutation_refl.
Qed.

Theorem permutation_elt : ∀ A (eqb : A → _),
  equality eqb →
  ∀ (la lb lc ld : list A) (a : A),
  permutation eqb (la ++ lb) (lc ++ ld)
  → permutation eqb (la ++ a :: lb) (lc ++ a :: ld).
Proof.
intros * Heqb * Hpab.
eapply (permutation_trans Heqb). {
  apply (permutation_sym Heqb).
  apply (permutation_middle Heqb).
}
now apply (permutation_cons_app Heqb).
Qed.

Theorem permutation_rev_l : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l, permutation eqb (rev l) l.
Proof.
intros * Heqb *.
induction l as [| a]; [ easy | cbn ].
eapply (permutation_trans Heqb). {
  apply (permutation_sym Heqb).
  apply (permutation_cons_append Heqb).
}
now apply (permutation_skip Heqb).
Qed.

Theorem permutation_length : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb, permutation eqb la lb → length la = length lb.
Proof.
intros * Heqb * Hpab.
unfold permutation in Hpab.
revert lb Hpab.
induction la as [| a]; intros. {
  now apply permutation_nil_l in Hpab; subst lb.
}
cbn in Hpab.
remember (extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb); subst lb.
apply Heqb in H; subst x.
rewrite app_length; cbn.
rewrite Nat.add_succ_r, <- app_length; f_equal.
now apply IHla.
Qed.

Theorem permutation_app_inv : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb lc ld a,
  permutation eqb (la ++ a :: lb) (lc ++ a :: ld)
  → permutation eqb (la ++ lb) (lc ++ ld).
Proof.
intros * Heqb * Hp.
specialize (permutation_add_inv Heqb) as H1.
apply (H1 a _ _ Hp (la ++ lb) (lc ++ ld)). {
  rewrite (List_cons_is_app a).
  rewrite (List_cons_is_app _ lb).
  do 2 rewrite app_assoc.
  apply (permutation_app_tail Heqb).
  apply (permutation_app_comm Heqb).
} {
  rewrite (List_cons_is_app a).
  rewrite (List_cons_is_app _ ld).
  do 2 rewrite app_assoc.
  apply (permutation_app_tail Heqb).
  apply (permutation_app_comm Heqb).
}
Qed.

Theorem permutation_app_inv_l : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l l1 l2,
  permutation eqb (l ++ l1) (l ++ l2) → permutation eqb l1 l2.
Proof.
intros * Heqb * H12.
revert l1 l2 H12.
induction l as [| a]; intros; [ easy | ].
cbn in H12.
apply permutation_cons_l_iff in H12; cbn in H12.
rewrite (equality_refl Heqb) in H12.
rewrite app_nil_l in H12.
now apply IHl.
Qed.

Theorem permutation_app_inv_r : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l l1 l2,
  permutation eqb (l1 ++ l) (l2 ++ l) → permutation eqb l1 l2.
Proof.
intros * Heqb * Hll.
apply (permutation_app_inv_l Heqb) with (l := l).
eapply (permutation_trans Heqb); [ now apply permutation_app_comm | ].
eapply (permutation_trans Heqb); [ apply Hll | ].
now apply permutation_app_comm.
Qed.

Theorem permutation_length_1 : ∀ A (eqb : A → _),
  equality eqb →
  ∀ a b,
  permutation eqb [a] [b] → a = b.
Proof.
intros * Heqb * Hpab.
unfold permutation in Hpab; cbn in Hpab.
remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ now apply Heqb in Hab | easy ].
Qed.

Theorem permutation_length_1_inv : ∀ A (eqb : A → _) (Heqb : equality eqb),
  ∀ a l, permutation eqb [a] l → l = [a].
Proof.
intros * Heqb * Ha.
apply permutation_cons_l_iff in Ha.
remember (extract (eqb a) l) as ll eqn:Hll; symmetry in Hll.
destruct ll as [((bef, x), aft)| ]; [ | easy ].
apply extract_Some_iff in Hll.
destruct Hll as (H1 & H & H2).
apply permutation_nil_l in Ha.
apply app_eq_nil in Ha.
destruct Ha; subst bef aft; cbn in H2; subst l.
f_equal; symmetry.
now apply Heqb.
Qed.

(**)

Theorem List_rank_loop_eqb_inside : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l1 l2 a i,
  List_rank_loop i (eqb a) (l1 ++ a :: l2) ≠ None.
Proof.
intros * Heqb *.
revert i.
induction l1 as [| b]; intros. {
  cbn.
  now rewrite (equality_refl Heqb).
}
cbn.
remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ easy | ].
apply IHl1.
Qed.

Theorem List_rank_eqb_inside : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l1 l2 a,
  List_rank (eqb a) (l1 ++ a :: l2) ≠ None.
Proof.
intros * Heqb *.
unfold List_rank.
now apply List_rank_loop_eqb_inside.
Qed.

Theorem List_rank_loop_extract : ∀ A (la : list A) f i,
  List_rank_loop i f la =
  match extract f la with
  | Some (bef, _, _) => Some (i + length bef)
  | None => None
  end.
Proof.
intros.
revert i.
induction la as [| a]; intros; [ easy | cbn ].
remember (f a) as fa eqn:Hfa; symmetry in Hfa.
destruct fa; [ now rewrite Nat.add_0_r | ].
rewrite IHla.
remember (extract f la) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
now cbn; rewrite Nat.add_succ_r.
Qed.

Theorem List_rank_extract : ∀ A (la : list A) f,
  List_rank f la =
  match extract f la with
  | Some (bef, _, _) => Some (length bef)
  | None => None
  end.
Proof.
intros.
apply List_rank_loop_extract.
Qed.

Theorem List_rank_not_None : ∀ n l i,
  permutation Nat.eqb l (seq 0 n)
  → i < n
  → List_rank (Nat.eqb i) l ≠ None.
Proof.
intros n f i Hp Hi Hx.
rewrite List_rank_extract in Hx.
remember (extract (Nat.eqb i) f) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ easy | clear Hx ].
specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
specialize (H1 i).
assert (H : i ∈ f). {
  apply (permutation_sym Nat_eqb_equality) in Hp.
  apply (permutation_in Nat_eqb_equality) with (la := seq 0 n); [ easy | ].
  now apply in_seq.
}
specialize (H1 H); clear H.
now apply Nat.eqb_neq in H1.
Qed.

(* permutation_fun : bijective function from permutation *)

Definition option_eqb {A} (eqb : A → A → bool) ao bo :=
  match (ao, bo) with
  | (Some a, Some b) => eqb a b
  | _ => false
  end.

Fixpoint permutation_assoc_loop {A} eqb (la : list A) lbo :=
  match la with
  | [] => []
  | a :: la' =>
      match extract (λ bo, option_eqb eqb bo (Some a)) lbo with
      | Some (befo, _, afto) =>
          length befo :: permutation_assoc_loop eqb la' (befo ++ None :: afto)
      | None => []
      end
  end.

Definition permutation_assoc {A} (eqb : A → _) la lb :=
  permutation_assoc_loop eqb la (map Some lb).

Definition permutation_fun {A} (eqb : A → _) la lb i :=
  unsome 0 (List_rank (Nat.eqb i) (permutation_assoc eqb la lb)).

Fixpoint filter_Some {A} (lao : list (option A)) :=
  match lao with
  | [] => []
  | Some a :: lao' => a :: filter_Some lao'
  | None :: lao' => filter_Some lao'
  end.

Theorem filter_Some_inside : ∀ A l1 l2 (x : option A),
  filter_Some (l1 ++ x :: l2) =
    filter_Some l1 ++
    match x with
    | Some a => a :: filter_Some l2
    | None => filter_Some l2
    end.
Proof.
intros.
revert x l2.
induction l1 as [| yo]; intros; [ easy | ].
cbn - [ option_eqb ].
destruct yo; [ | apply IHl1 ].
cbn; f_equal; apply IHl1.
Qed.

Theorem filter_Some_map_Some : ∀ A (la : list A),
  filter_Some (map Some la) = la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
now f_equal.
Qed.

Theorem permutation_assoc_loop_length : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lbo,
  permutation eqb la (filter_Some lbo)
  → length (permutation_assoc_loop eqb la lbo) = length la.
Proof.
intros * Heqb * Hpab.
revert lbo Hpab.
induction la as [| a]; intros; [ easy | ].
cbn - [ option_eqb ].
remember (extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  cbn - [ option_eqb ] in H1.
  specialize (H1 (Some a)).
  assert (H : Some a ∈ lbo). {
    specialize (permutation_in Heqb) as H2.
    specialize (H2 _ _ a Hpab (or_introl eq_refl)).
    clear - H2.
    induction lbo as [| bo]; [ easy | cbn in H2 ].
    destruct bo as [b| ]. {
      destruct H2 as [H3| H3]; [ now subst b; left | ].
      now right; apply IHlbo.
    }
    now right; apply IHlbo.
  }
  specialize (H1 H); clear H.
  cbn in H1.
  now rewrite (equality_refl Heqb) in H1.
}
cbn; f_equal.
apply IHla.
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & Hxa & Hlbo).
cbn in Hxa.
destruct x as [b| ]; [ | easy ].
apply Heqb in Hxa; subst b.
subst lbo.
rewrite filter_Some_inside in Hpab |-*.
apply (permutation_app_inv Heqb [] _ _ _ _ Hpab).
Qed.

Theorem permutation_assoc_length : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb,
  permutation eqb la lb
  → length (permutation_assoc eqb la lb) = length la.
Proof.
intros * Heqb * Hpab.
apply (permutation_assoc_loop_length Heqb).
now rewrite filter_Some_map_Some.
Qed.

(* transposition list *)

Fixpoint transp_loop {A} (eqb : A → A → bool) i la lb :=
  match lb with
  | [] => []
  | b :: lb' =>
      match extract (eqb b) la with
      | Some ([], _, la2) => transp_loop eqb (S i) la2 lb'
      | Some (a :: la1, _, la2) =>
          (i, S (i + length la1)) ::
          transp_loop eqb (S i) (la1 ++ a :: la2) lb'
      | None => []
      end
  end.

(* list of transpositions to be done to "la" to get "lb" *)
Definition transp_list {A} (eqb : A → _) la lb := transp_loop eqb 0 la lb.

Definition swap_d {A} d i j (la : list A) :=
   map (λ k, nth (if k =? i then j else if k =? j then i else k) la d)
     (seq 0 (length la)).

Definition swap {A} i j (la : list A) :=
  match la with
  | [] => []
  | d :: _ => swap_d d i j la
  end.

Definition apply_transp_list {A} trl (la : list A) :=
  fold_left (λ lb ij, swap (fst ij) (snd ij) lb) trl la.

Definition shift_transp i trl := map (λ ij, (fst ij + i, snd ij + i)) trl.

Theorem fold_apply_transp_list : ∀ A trl (la : list A),
  fold_left (λ lb ij, swap (fst ij) (snd ij) lb) trl la =
  apply_transp_list trl la.
Proof. easy. Qed.

Theorem transp_loop_shift : ∀ A (eqb : A → _),
  equality eqb →
  ∀ i la lb,
  transp_loop eqb i la lb = shift_transp i (transp_list eqb la lb).
Proof.
intros * Heqb *.
revert i la.
induction lb as [| b]; intros; [ easy | cbn ].
remember (extract (eqb b) la) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & Hx & Hla).
apply Heqb in Hx; subst x.
subst la.
destruct bef as [| a]. {
  do 2 rewrite IHlb.
  unfold shift_transp; cbn.
  rewrite map_map; cbn.
  apply map_ext_in.
  intros ij Hij.
  now do 2 rewrite <- Nat.add_assoc.
}
cbn.
f_equal; [ now rewrite Nat.add_comm | ].
do 2 rewrite IHlb.
unfold shift_transp; cbn.
rewrite map_map; cbn.
apply map_ext_in.
intros ij Hij.
now do 2 rewrite <- Nat.add_assoc.
Qed.

Theorem swap_length : ∀ A (la : list A) i j,
  length (swap i j la) = length la.
Proof.
intros.
unfold swap, swap_d.
destruct la as [| a]; [ easy | ].
now rewrite List_map_seq_length.
Qed.

Theorem apply_transp_list_shift_1_cons : ∀ A (a : A) la trl,
  (∀ ij, ij ∈ trl → fst ij < snd ij < length la)
  → apply_transp_list (shift_transp 1 trl) (a :: la) =
    a :: apply_transp_list trl la.
Proof.
intros * Htrl.
revert a la Htrl.
induction trl as [| ij]; intros; [ easy | ].
cbn - [ "=?" shift_transp ].
destruct ij as (i, j).
cbn - [ shift_transp ].
unfold apply_transp_list in IHtrl.
rewrite <- IHtrl; cbn. 2: {
  intros ij Hij.
  rewrite swap_length.
  now apply Htrl; right.
}
do 2 rewrite Nat.add_1_r.
f_equal; f_equal.
unfold swap.
destruct la as [| d]; [ easy | ].
rewrite <- seq_shift.
rewrite map_map.
apply map_ext_in.
intros k Hk; cbn.
apply in_seq in Hk.
destruct Hk as (_, Hk); cbn in Hk.
do 4 rewrite if_eqb_eq_dec.
specialize (Htrl _ (or_introl eq_refl)) as Hij.
cbn in Hij.
destruct (Nat.eq_dec k i) as [Hki| Hki]. {
  subst k.
  destruct j; [ easy | ].
  apply nth_indep; flia Hij.
}
destruct (Nat.eq_dec k j) as [Hkj| Hkj]. {
  subst k.
  destruct i; [ easy | ].
  apply nth_indep; flia Hij.
}
destruct k; [ easy | ].
apply Nat.succ_lt_mono in Hk.
now apply nth_indep.
Qed.

Theorem in_transp_loop_length : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb,
  length la = length lb
  → ∀ i j k,
  (i, j) ∈ transp_loop eqb k la lb
  → i < j < k + length la.
Proof.
intros * Heqb * Hlab * Htab.
revert k la Hlab Htab.
induction lb as [| b]; intros; [ easy | ].
cbn in Htab.
remember (extract (eqb b) la) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & Hx & Hla); subst la.
apply Heqb in Hx; subst x.
rewrite app_length in Hlab; cbn in Hlab.
rewrite Nat.add_succ_r in Hlab.
apply Nat.succ_inj in Hlab.
destruct bef as [| c]; cbn. {
  rewrite <- Nat.add_succ_comm.
  now apply IHlb.
}
destruct Htab as [Htab | Htab]. {
  injection Htab; clear Htab; intros; subst k j.
  split; [ flia | ].
  rewrite app_length; cbn.
  rewrite <- Nat.add_succ_comm, <- Nat.add_succ_l.
  apply Nat.add_lt_mono_l; flia.
}
specialize (IHlb (S k) (bef ++ c :: aft)) as H1.
assert (H : length (bef ++ c :: aft) = length lb). {
  rewrite app_length; cbn.
  now rewrite Nat.add_succ_r.
}
specialize (H1 H Htab); clear H.
rewrite app_length in H1 |-*; cbn in H1 |-*.
now rewrite Nat.add_succ_r.
Qed.

Theorem in_transp_list_length : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb,
  length la = length lb
  → ∀ i j,
  (i, j) ∈ transp_list eqb la lb
  → i < j < length la.
Proof.
intros * Heqb * Hlab * Htab.
apply (in_transp_loop_length Heqb la lb Hlab i j 0 Htab).
Qed.

Theorem permutation_transp_list : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb,
  permutation eqb la lb
  → apply_transp_list (transp_list eqb la lb) la = lb.
Proof.
intros * Heqb * Hpab.
revert la Hpab.
induction lb as [| b]; intros; cbn. {
  now apply permutation_nil_r in Hpab.
}
remember (extract (eqb b) la) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  specialize (H1 b).
  specialize (permutation_in_r Heqb) as H.
  specialize (H _ _ b Hpab (or_introl eq_refl)).
  specialize (H1 H); clear H.
  now rewrite (equality_refl Heqb) in H1.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & Hx & Hla).
apply Heqb in Hx; subst x.
subst la.
assert (H : permutation eqb (bef ++ aft) lb). {
  apply (permutation_cons_inv Heqb) with (a := b).
  eapply (permutation_trans Heqb); [ | apply Hpab ].
  rewrite (List_cons_is_app b aft), app_assoc.
  rewrite app_comm_cons.
  apply (permutation_app_tail Heqb).
  now apply permutation_cons_append.
}
move H before Hpab; clear Hpab; rename H into Hpab.
destruct bef as [| a]. {
  cbn.
  rewrite (transp_loop_shift Heqb).
  rewrite fold_apply_transp_list.
  rewrite apply_transp_list_shift_1_cons. 2: {
    intros (i, j) Hij; cbn.
    apply (permutation_length Heqb) in Hpab.
    now apply (in_transp_list_length Heqb _ _ Hpab).
  }
  f_equal.
  now apply IHlb.
}
cbn - [ swap ].
replace (swap _ _ _) with (b :: bef ++ a :: aft). 2: {
  cbn.
  rewrite app_nth2; [ | now unfold ge ].
  rewrite Nat.sub_diag; cbn; f_equal.
  rewrite <- seq_shift, map_map; cbn.
  rewrite List_map_nth_seq with (la := bef ++ a :: aft) (d := a).
  do 2 rewrite app_length.
  apply map_ext_in.
  intros i Hi.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec i (length bef)) as [Hib| Hib]. {
    rewrite Hib.
    rewrite app_nth2; [ | now unfold ge ].
    now rewrite Nat.sub_diag.
  }
  destruct (lt_dec i (length bef)) as [Hibl| Hibg]. {
    rewrite app_nth1; [ | easy ].
    now rewrite app_nth1.
  }
  rewrite app_nth2; [ | flia Hib Hibg ].
  rewrite app_nth2; [ | flia Hib Hibg ].
  now replace (i - length bef) with (S (i - S (length bef))) by flia Hib Hibg.
}
rewrite (transp_loop_shift Heqb).
cbn in Hpab.
assert (H : permutation eqb (bef ++ a :: aft) lb). {
  eapply (permutation_trans Heqb); [ | apply Hpab ].
  rewrite (List_cons_is_app a aft), app_assoc.
  rewrite app_comm_cons.
  apply (permutation_app_tail Heqb).
  apply (permutation_sym Heqb).
  now apply permutation_cons_append.
}
move H before Hpab; clear Hpab; rename H into Hpab.
rewrite fold_apply_transp_list.
rewrite apply_transp_list_shift_1_cons. 2: {
  intros (i, j) Hij; cbn.
  apply (permutation_length Heqb) in Hpab.
  now apply (in_transp_list_length Heqb _ _ Hpab).
}
f_equal.
apply (IHlb _ Hpab).
Qed.

Theorem swap_d_inside : ∀ A (d : A) l1 l2 l3 x y,
  swap_d d (length l1) (S (length (l1 ++ l2))) (l1 ++ x :: l2 ++ y :: l3) =
  l1 ++ y :: l2 ++ x :: l3.
Proof.
intros.
unfold swap_d.
rewrite List_map_nth_seq with (d := d).
do 3 rewrite app_length; cbn.
do 2 rewrite app_length; cbn.
apply map_ext_in.
intros i Hi.
do 2 rewrite if_eqb_eq_dec.
remember (length l1) as len1 eqn:Hl1.
remember (length l2) as len2 eqn:Hl2.
move len2 before len1.
destruct (lt_dec i len1) as [Hi1| Hi1]. {
  destruct (Nat.eq_dec i len1) as [H| H]; [ flia Hi1 H | clear H].
  destruct (Nat.eq_dec i (S (len1 + len2))) as [H| H]; [ flia Hi1 H | ].
  clear H.
  rewrite Hl1 in Hi1.
  rewrite app_nth1; [ now rewrite app_nth1 | easy ].
}
apply Nat.nlt_ge in Hi1.
symmetry.
rewrite app_nth2; [ | now rewrite Hl1 in Hi1 ].
destruct (Nat.eq_dec i len1) as [Hi2| Hi2]. {
  rewrite Hi2, Hl1, Nat.sub_diag; cbn.
  rewrite Hl1 in Hi1, Hi2.
  rewrite app_nth2; [ | flia ].
  rewrite <- Nat.add_succ_r, Nat.add_comm, Nat.add_sub.
  rewrite List_nth_succ_cons.
  rewrite app_nth2; [ | now unfold ge; subst len2 ].
  now rewrite Hl2, Nat.sub_diag, List_nth_0_cons.
}
assert (H : len1 < i) by flia Hi1 Hi2; clear Hi1 Hi2; rename H into Hi1.
replace (i - length l1) with (S (i - S (length l1))) by flia Hl1 Hi1; cbn.
rewrite <- Hl1.
symmetry.
rewrite app_nth2. 2: {
  destruct (Nat.eq_dec i (S (len1 + len2))) as [H| H]; [ | flia Hl1 Hi1 ].
  flia Hl1 Hi1.
}
destruct (lt_dec i (S (len1 + len2))) as [Hi2| Hi2]. {
  destruct (Nat.eq_dec i (S (len1 + len2))) as [H| H]; [ flia Hi2 H | ].
  clear H.
  rewrite <- Hl1.
  replace (i - len1) with (S (i - S len1)) by flia Hi1.
  rewrite List_nth_succ_cons.
  rewrite app_nth1; [ | rewrite <- Hl2; flia Hi1 Hi2 ].
  rewrite app_nth1; [ | rewrite <- Hl2; flia Hi1 Hi2 ].
  easy.
}
apply Nat.nlt_ge in Hi2.
destruct (Nat.eq_dec i (S (len1 + len2))) as [Hi3| Hi3]. {
  rewrite Hl1, Nat.sub_diag, List_nth_0_cons at 1.
  rewrite Hi3.
  rewrite <- Nat.add_succ_l, Nat.add_comm, Nat.add_sub; cbn.
  rewrite app_nth2; [ | now unfold ge; rewrite Hl2 ].
  now rewrite Hl2, Nat.sub_diag.
}
assert (H : S (len1 + len2) < i) by flia Hi2 Hi3.
clear Hi2 Hi3; rename H into Hi2.
rewrite <- Hl1.
replace (i - len1) with (S (i - S len1)) by flia Hi1.
rewrite List_nth_succ_cons.
rewrite app_nth2; [ | rewrite <- Hl2; flia Hi2 ].
rewrite app_nth2; [ | rewrite <- Hl2; flia Hi2 ].
rewrite <- Hl2.
now replace (i - S len1 - len2) with (S (i - S len1 - S len2)) by flia Hi2.
Qed.

Theorem permutation_transp_inside : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l1 l2 l3 x y,
  permutation eqb (l1 ++ y :: l2 ++ x :: l3) (l1 ++ x :: l2 ++ y :: l3).
Proof.
intros * Heqb *.
rewrite List_cons_is_app.
rewrite (List_cons_is_app x).
rewrite (List_cons_is_app x (l2 ++ _)).
rewrite (List_cons_is_app y l3).
apply (permutation_app_head Heqb).
do 4 rewrite app_assoc.
apply (permutation_app_tail Heqb).
eapply (permutation_trans Heqb); [ | apply (permutation_app_comm Heqb) ].
rewrite <- app_assoc.
apply (permutation_app_head Heqb).
apply (permutation_app_comm Heqb).
Qed.

Theorem permutation_swap_any : ∀ A (eqb : A → _),
  equality eqb →
  ∀ i j la,
  i < j < length la
  → permutation eqb (swap i j la) la.
Proof.
intros * Heqb * Hij.
unfold swap.
destruct la as [| d]; [ apply permutation_nil_nil | ].
remember (d :: la) as lb eqn:Hlb.
clear la Hlb; rename lb into la.
assert (H : i < length la) by flia Hij.
specialize (nth_split la d H) as H1; clear H.
destruct H1 as (l1 & l2 & Hla & Hi).
remember (nth i la d) as x eqn:Hx.
subst la.
rewrite app_length in Hij; cbn in Hij.
assert (H : j - S i < length l2) by flia Hij Hi.
specialize (nth_split l2 d H) as H1; clear H.
destruct H1 as (l3 & l4 & Hl2 & Hj).
remember (nth (j - S i) l2 d) as y eqn:Hy.
subst l2; rename l3 into l2; rename l4 into l3.
assert (H : j = S (length (l1 ++ l2))). {
  rewrite app_length, Hj, Hi.
  flia Hij.
}
rewrite <- Hi, H.
rewrite swap_d_inside.
now apply permutation_transp_inside.
Qed.

(* *)

Require Import Permutation.

Theorem Permutation_permutation : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb, Permutation la lb ↔ permutation eqb la lb.
Proof.
intros * Heqb *.
split. {
  intros Hpab.
  revert lb Hpab.
  induction la as [| a]; intros; cbn. {
    now apply Permutation_nil in Hpab; subst lb.
  }
  apply permutation_cons_l_iff.
  remember (extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef, x), aft) | ]. {
    apply extract_Some_iff in Hlxl.
    destruct Hlxl as (Hbef & Hax & Hlb).
    apply Heqb in Hax; subst x.
    apply IHla.
    apply Permutation_cons_app_inv with (a := a).
    now rewrite <- Hlb.
  }
  specialize (Permutation_in a Hpab (or_introl eq_refl)) as H.
  specialize (proj1 (extract_None_iff _ _) Hlxl a H) as Hla; clear H.
  now rewrite (equality_refl Heqb) in Hla.
} {
  intros Hpab.
  revert lb Hpab.
  induction la as [| a]; intros; cbn in Hpab; [ now destruct lb | ].
  apply permutation_cons_l_iff in Hpab.
  remember (extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef, x), aft) | ]; [ | easy ].
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef & Hax & Hlb).
  apply Heqb in Hax; subst x.
  subst lb.
  apply Permutation_cons_app.
  now apply IHla.
}
Qed.
