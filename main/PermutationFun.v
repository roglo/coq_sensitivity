(* Testing if a list is a permutation of another one *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith Permutation.

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

Theorem equality_refl {A} (eqb : A → _) : equality eqb → ∀ a, eqb a a = true.
Proof.
intros * Heqb *.
now apply Heqb.
Qed.

Theorem extract_Some : ∀ A (f : A → _) l a bef aft,
  extract f l = Some (bef, a, aft) → f a = true ∧ l = bef ++ a :: aft.
Proof.
intros * He.
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
split; [ easy | ].
now cbn; f_equal.
Qed.

Theorem extract_None : ∀ A (f : A → _) l,
  extract f l = None → l = [] ∨ ∀ a, a ∈ l → f a = false.
Proof.
intros * He.
induction l as [| a]; [ now left | right ].
intros b Hb.
cbn in He.
assert (H : extract f l = None). {
  destruct (f a); [ easy | ].
  remember (extract f l) as lxl eqn:Hlxl; symmetry in Hlxl.
  now destruct lxl as [((bef, x), aft)| ].
}
specialize (IHl H); clear H.
destruct IHl as [Hl| Hf]. {
  subst l.
  destruct Hb as [Hb| Hb]; [ subst b | easy ].
  now destruct (f a).
}
destruct Hb as [Hb| Hb]; [ | now apply Hf ].
subst b.
now destruct (f a).
Qed.

(* to be completed
Theorem Permutation_permutation : ∀ A (eqb : A → _) la lb,
  equality eqb →
  Permutation la lb
  ↔ is_permutation eqb la lb = true.
Proof.
intros * Heqb.
split. {
  intros Hpab.
  revert lb Hpab.
  induction la as [| a]; intros; cbn. {
    now apply Permutation_nil in Hpab; subst lb.
  }
  remember (extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef, x), aft) | ]. {
    apply extract_Some in Hlxl.
    destruct Hlxl as (Hax, Hlb).
    apply Heqb in Hax; subst x.
    apply IHla.
    apply Permutation_cons_app_inv with (a := a).
    now rewrite <- Hlb.
  }
  apply extract_None in Hlxl.
  destruct Hlxl as [Hlb| Hla]. {
    subst lb.
    apply Permutation_sym in Hpab.
    now apply Permutation_nil_cons in Hpab.
  }
  specialize (Permutation_in a Hpab (or_introl eq_refl)) as H.
  specialize (Hla a H); clear H.
  now rewrite (equality_refl Heqb) in Hla.
} {
...
*)
