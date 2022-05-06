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

Definition equality {A} (eqb : A → A → bool) := ∀ a b, eqb a b = true ↔ a = b.
Definition permutation A (eqb : A → _) la lb := is_permutation eqb la lb = true.

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

Theorem permutation_cons_inv : ∀ A eqb la lb (a : A) (Heqb : equality eqb),
  permutation eqb (a :: la) (a :: lb) → permutation eqb la lb.
Proof.
intros * Heqb * Hpab.
apply permutation_cons_l_iff in Hpab.
cbn in Hpab.
now rewrite (equality_refl Heqb) in Hpab.
Qed.

Theorem permutation_in : ∀ A (eqb : A → _),
  equality eqb →
  ∀ la lb,
  permutation eqb la lb →
  (∀ a, a ∈ la ↔ a ∈ lb).
Proof.
intros * Heqb * Hab *.
split. {
  intros Hla.
  revert a lb Hab Hla.
  induction la as [| b]; intros; [ easy | cbn ].
  apply permutation_cons_l_iff in Hab.
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
} {
  intros Hlb.
  revert a lb Hab Hlb.
  induction la as [| b]; intros; [ now destruct lb | ].
  apply permutation_cons_l_iff in Hab.
  remember (extract (eqb b) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef, x), aft)| ]; [ | easy ].
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef & H & Hlba).
  apply Heqb in H; subst x lb.
  apply in_app_or in Hlb.
  destruct Hlb as [Hlb| Hlb]. 2: {
    destruct Hlb as [Hlb| Hlb]; [ now left | right ].
    apply (IHla a (bef ++ aft) Hab).
    now apply in_or_app; right.
  }
  right; apply (IHla a (bef ++ aft) Hab).
  now apply in_or_app; left.
}
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
  specialize (permutation_in Heqb Hab) as H2.
  specialize (proj2 (H2 b) (or_introl eq_refl)) as H3.
  specialize (H1 _ H3).
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
  specialize (permutation_in Heqb Hbc) as H2.
  specialize (H2 a) as H3.
  assert (H : a ∈ lb) by now subst lb; apply in_or_app; right; left.
  specialize (proj1 H3 H) as H4; clear H.
  specialize (H1 _ H4).
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

(* *)

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

(**)

Theorem permutation_cons_append : ∀ A (eqb : A → _),
  equality eqb →
  ∀ l x, permutation eqb (x :: l) (l ++ [x]).
Proof.
intros * Heqb *.
remember (length l) as len eqn:Hlen; symmetry in Hlen.
revert x l Hlen.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct len. {
  apply length_zero_iff_nil in Hlen; subst l.
  now apply permutation_refl.
}
destruct l as [| y]; [ easy | ].
cbn in Hlen; apply Nat.succ_inj in Hlen.
apply permutation_cons_l_iff; cbn.
remember (eqb x y) as xy eqn:Hxy; symmetry in Hxy.
destruct xy. {
  cbn; apply Heqb in Hxy; subst y.
  apply permutation_cons_l_iff.
  remember (extract (eqb x) (l ++ [x])) as lxl eqn:Hlxl.
  symmetry in Hlxl.
  destruct lxl as [((bef', y), aft)| ]. 2: {
    specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
    specialize (H1 x).
    assert (H : x ∈ l ++ [x]) by now apply in_or_app; right; left.
    specialize (H1 H); clear H.
    now rewrite equality_refl in H1.
  }
  apply extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef & H & Hlb).
  apply Heqb in H; subst x.
  apply app_eq_app in Hlb.
  destruct Hlb as (l' & Hlb).
  destruct Hlb as [(H1, H2)| (H1, H2)]. {
    rewrite H1.
    apply (permutation_app_head Heqb).
    destruct l' as [| x]. {
      cbn in H2.
      now injection H2; clear H2; intros; subst aft.
    }
    cbn in H2.
    injection H2; clear H2; intros H2 H; subst y aft.
    apply IHlen with (m := length l'); [ | easy ].
    rewrite <- Hlen, H1.
    rewrite app_length; cbn; flia.
  }
  destruct l'; [ | now destruct l' ].
  cbn in H2.
  rewrite app_nil_r in H1.
  injection H2; clear H2; intros; subst l aft.
  rewrite app_nil_r.
  now apply permutation_refl.
}
remember (extract (eqb x) (l ++ [x])) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, z), aft)| ]. 2: {
  specialize (proj1 (extract_None_iff _ _) Hlxl) as H1.
  specialize (H1 x).
  assert (H : x ∈ l ++ [x]) by now apply in_or_app; right; left.
  specialize (H1 H); clear H.
  now rewrite equality_refl in H1.
}
apply extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst z.
apply permutation_cons_l_iff; cbn.
rewrite (equality_refl Heqb), app_nil_l.
apply (permutation_app_inv_r Heqb) with (l := [x]).
rewrite Hlb, <- app_assoc.
apply (permutation_app_head Heqb).
eapply IHlen; [ | easy ].
rewrite <- Hlen.
apply (f_equal length) in Hlb; cbn in Hlb.
do 2 rewrite app_length in Hlb; cbn in Hlb.
rewrite Nat.add_1_r, Nat.add_succ_r in Hlb.
rewrite Hlb; flia.
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

Theorem Nat_eqb_equality : equality Nat.eqb.
Proof.
intros a b.
apply Nat.eqb_eq.
Qed.

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
