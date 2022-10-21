(* Polynomial.v *)

(* polynomials on a RingLike *)

Set Nested Proofs Allowed.
Set Implicit Arguments.

Require Import Utf8 Arith.
Import List ListNotations Init.Nat.

Require Import Misc RingLike IterAdd IterAnd.
Require Import PermutationFun SortingFun.

(* definition of a monomial *)

Record monom T := Mon { mcoeff : T; mdeg : nat }.

Arguments Mon {T} mcoeff%F mdeg%nat.

(*
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
Compute (Mon (-3) 4).
*)

Notation "c ·" := (Mon c 0) (at level 1, format "c ·").
Notation "c * ☓" := (Mon c 1) (at level 1, format "c * ☓").
Notation "c * ☓ ^ a" := (Mon c a) (at level 1, format "c * ☓ ^ a").

(* definition of a polynomial *)

Record polyn T := mk_polyn { monl : list (monom T) }.

Arguments mk_polyn {T} monl%list.
Arguments polyn T%type.

(*
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
Compute (mk_polyn [Mon 3 5]).
Compute (mk_polyn [Mon 3 5; Mon (-5) 2; Mon 8 0]).
Compute (mk_polyn [3*☓^5; (-5)*☓^2; 8*☓^0]).
Compute (Mon 3 8).
Compute [3*☓^5; (-5)*☓^2; 8*☓^0].
*)

(* canonicity of a polynomial
   i.e. the fact that the degrees are in decreasing order
   and that there are no nul coefficient. *)

Definition is_canon_monl T {ro : ring_like_op T} (la : list (monom T)) :=
  (is_sorted (λ x y, mdeg y <? mdeg x) la &&
   ⋀ (x ∈ la), (mcoeff x ≠? 0)%F)%bool.

Definition is_canon_polyn T {ro : ring_like_op T} (p : polyn T) :=
  is_canon_monl (monl p).

(* notation for polynomials *)

Notation "« »" := (mk_polyn []).
Notation "« x »" := (mk_polyn (cons x nil)) (x at level 40).
Notation "« x + y + .. + z »" :=
  (mk_polyn (cons x (cons y .. (cons z nil) ..)))
  (x at level 40, y at level 40, z at level 40,
   format "«  x  +  y  +  ..  +  z  »").
(*
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
Compute (mk_polyn [Mon 3 5]).
Compute (mk_polyn [Mon 3 5; Mon (-5) 2; Mon 8 0]).
Compute (mk_polyn [3*☓^5; (-5)*☓^2; 88·]).
Compute « 3*☓^5 ».
Compute « 88· ».
Compute « 3*☓^5 + (-5)*☓^2 ».
Compute « 3*☓^5 + (-5)*☓^2 + 88· ».
Compute (Mon 3 8).
Compute [3].
Compute [(3+2)%nat].
*)

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).

(* 0 and 1 as polynomials *)

Definition polyn_zero := mk_polyn [] : polyn T.
Definition polyn_one := mk_polyn [Mon 1 0] : polyn T.

(* addition *)

Definition monl_add (la lb : list (monom T)) := la ++ lb.

(*
End a.
Arguments is_canon_polyn {T ro} p.
Arguments monl {T} p.
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
Compute (is_canon_polyn «3*☓^5 + 5*☓^2 + 8*☓»).
Compute (is_canon_polyn «3*☓^5 + 5*☓^2 + 8*☓^7»).
Compute (monl_add (monl «3*☓^5 + 5*☓^2 + 8*☓») (monl «3*☓^5 + 5*☓^2 + 8*☓»)).
Compute (monl_add (monl «3*☓^5 + 5*☓^2 + 8*☓») (monl «3*☓^5 + (-5)*☓^2 + 8*☓»)).
Compute (monl_add (monl «3*☓^5 + 5*☓^2 + 8*☓») (monl « »)).
Compute (monl_add (monl « ») (monl «3*☓^5 + (-5)*☓^2 + 8*☓»)).
*)

Definition polyn_add (pa pb : polyn T) :=
  mk_polyn (monl_add (monl pa) (monl pb)).

(*
End a.
Arguments is_canon_polyn {T ro} p.
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
Compute (polyn_add «3*☓^5 + 5*☓^2 + 8*☓» «3*☓^5 + 5*☓^2 + 8*☓»).
Compute (polyn_add «3*☓^5 + 5*☓^2 + 8*☓» «3*☓^5 + (-5)*☓^2 + 7·»).
Compute (is_canon_polyn (polyn_add «3*☓^5 + 5*☓^2 + 8*☓» «3*☓^5 + 5*☓^2 + 8*☓»)).
Compute (polyn_add «3*☓^5 + 5*☓^2 + 8*☓» «3*☓^5 + (-5)*☓^7 + 7·»).
Compute (is_canon_polyn (polyn_add «3*☓^5 + 5*☓^2 + 8*☓» «3*☓^5 + (-5)*☓^7 + 7·»)).
*)

(* multiplication *)

Fixpoint monl_mul_mon_l ma lb :=
  match lb with
  | [] => []
  | mb :: lb' =>
      let c := (mcoeff ma * mcoeff mb)%F in
      Mon c (mdeg ma + mdeg mb) :: monl_mul_mon_l ma lb'
  end.

Fixpoint monl_mul la lb :=
  match la with
  | [] => []
  | ma :: la' => monl_add (monl_mul_mon_l ma lb) (monl_mul la' lb)
  end.

Definition polyn_mul pa pb := mk_polyn (monl_mul (monl pa) (monl pb)).

(*
End a.
Arguments polyn_mul {T ro} (pa pb).
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
Compute (polyn_mul «1*☓ + 1·» «1*☓ + (-1)·»).
Compute (polyn_mul «3*☓^5 + 1·» «1*☓ + (-1)·»).
Compute (polyn_mul «1*☓ + (-1)·» «3*☓^5 + 1·»).
*)

(* opposite *)

Definition monl_opp la := map (λ m, Mon (- mcoeff m)%F (mdeg m)) la.
Definition polyn_opp p := mk_polyn (monl_opp (monl p)).

(* subtraction *)

Definition monl_sub (la lb : list (monom T)) :=
  match rngl_opt_opp_or_sous with
  | Some (inl _) => monl_add la (monl_opp lb)
  | Some (inr _) => []
  | None => []
  end.

Definition polyn_sub pa pb := mk_polyn (monl_sub (monl pa) (monl pb)).

(*
End a.
Arguments polyn_mul {T ro} (pa pb).
Arguments polyn_opp {T ro} p.
Arguments polyn_sub {T ro} (pa pb).
(**)
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
(*
Require Import NatRingLike.
*)
Compute (mk_polyn [Mon 1 2]).
Compute (polyn_sub «1*☓ » «3*☓^5 + 1·»).
Compute (polyn_sub «3*☓^5 + 1·» « 2*☓^5 »).
Compute « 1*☓^2 ».
Compute (polyn_opp «1*☓»).
Compute (polyn_opp «1*☓ + 1·»).
Compute (polyn_opp «1*☓ + (-1)·»).
Compute (polyn_opp «3*☓^5 + 1·»).
Compute (polyn_opp «3*☓^5»).
Compute (polyn_mul «1*☓ + (-1)·» «3*☓^5 + 1·»).
Compute (polyn_opp (polyn_mul «3*☓^5 + 1·» «1*☓ + (-1)·»)).
*)

(* normalisation
   return a polynomial whose degree are in decreasing order
   and no coefficient is nul *)

Definition same_deg_sum_coeff ma la :=
  match la with
  | [] => [ma]
  | mb :: lc =>
      if mdeg ma =? mdeg mb then (mcoeff ma + mcoeff mb)*☓^(mdeg ma) :: lc
      else ma :: mb :: lc
  end.

Definition merge_same_deg la := fold_right same_deg_sum_coeff [] la.

Definition monl_norm (la : list (monom T)) :=
  filter (λ ma, (mcoeff ma ≠? 0)%F)
    (merge_same_deg (isort (λ ma mb, mdeg mb <=? mdeg ma) la)).

Definition polyn_norm pa := mk_polyn (monl_norm (monl pa)).

Theorem fold_merge_same_deg : ∀ la,
  fold_right same_deg_sum_coeff [] la = merge_same_deg la.
Proof. easy. Qed.

(*
End a.
Arguments polyn_norm {T ro} pa.
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
Compute (polyn_norm « 1*☓^2 + 1· + (-1)· »).
Compute (polyn_norm « 1· + 1*☓^2 + (-1)· »).
Compute (polyn_norm « »).
Compute (polyn_norm « 1*☓^2 + 1· + (-1)· »).
Compute (polyn_norm « 7· + 1*☓^2 + 1· + (-1)· »).
*)

(* euclidean division *)

Fixpoint monl_quot_rem_loop it (la lb : list (monom T)) :
    list (monom T) * list (monom T) :=
  match it with
  | 0 => ([], [Mon (rngl_of_nat 97) 0]) (* algo err: not enough iterations *)
  | S it' =>
      match la with
      | [] => ([], [])
      | ma :: la' =>
          match lb with
          | [] => ([], []) (* division by zero *)
          | mb :: _ =>
              let c := (mcoeff ma / mcoeff mb)%F in
              if ((c =? 0)%F || (mdeg ma <? mdeg mb))%bool then ([], la)
              else
                let mq := Mon c (mdeg ma - mdeg mb) in
                let lr := monl_norm (monl_sub la (monl_mul lb [mq])) in
                let (lq', lr') := monl_quot_rem_loop it' lr lb in
                (mq :: lq', lr')
          end
      end
  end.

Definition monl_quot_rem_nb_iter (la lb : list (monom T)) :=
  S (length la).

Definition monl_quot_rem la lb :=
  monl_quot_rem_loop (monl_quot_rem_nb_iter la lb) la lb.

Definition polyn_quot_rem pa pb :=
  let (lq, lr) := monl_quot_rem (monl pa) (monl pb) in
  (mk_polyn lq, mk_polyn lr).

Definition polyn_quot pa pb := fst (polyn_quot_rem pa pb).
Definition polyn_rem pa pb := snd (polyn_quot_rem pa pb).

(*
End a.
Arguments monl_norm {T ro} la%list.
Arguments monl_quot_rem_loop {T ro} it%nat (la lb)%list.
Arguments monl_quot_rem {T ro} (la lb)%list.
Arguments polyn_norm {T ro} pa.
Arguments polyn_rem {T ro} pa pb.
Arguments polyn_quot_rem {T ro} (pa pb).
Arguments polyn_quot {T ro} (pa pb).
Arguments polyn_rem {T ro} (pa pb).
Arguments monl_mul {T ro} (la lb)%list.
Arguments monl_sub {T ro} (la lb)%list.
(*
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
*)
Require Import RnglAlg.Qrl.
Require Import RnglAlg.Rational.
Import Q.Notations.
Open Scope Q_scope.
(**)
Compute (polyn_norm « 1*☓^2 + 1· + (-1)· »).
Compute (polyn_norm « 7· + 1*☓^2 + 1· + (-1)· »).
Compute (polyn_quot_rem «1*☓^2 + (-1)·» «2·»).
Compute (polyn_quot_rem «4*☓^2 + (-1)·» «2·»).
Compute (polyn_quot_rem «1*☓^2 + (-1)·» «2*☓»).
Compute (polyn_quot_rem «1·» «2·»).
Compute (polyn_quot_rem «1*☓^2 + 3*☓ + 7·» «1*☓ + 1·»).
Compute (polyn_quot_rem «1*☓^2 + 3*☓ + 7·» «2*☓ + 1·»).
(*
     = (« 〈1╱2〉*☓ + 〈5╱4〉· », « 〈23╱4〉· »)
     : polyn Q * polyn Q
*)
Compute (polyn_quot_rem «1*☓^2 + 3*☓ + 7·» «»).
Compute (polyn_quot_rem «» «1*☓^2 + 3*☓ + 7·»).
*)

End a.

(* polynomial notations *)

Declare Scope P_scope.
Delimit Scope P_scope with P.

Arguments is_canon_polyn {T ro} p%P.
Arguments merge_same_deg {T ro} la%list.
Arguments monl_add {T} (la lb)%list.
Arguments monl_mul {T ro} (la lb)%list.
Arguments monl_norm {T ro} la%list.
Arguments monl_opp {T ro} la%list.
Arguments polyn_add {T} (pa pb)%P.
Arguments polyn_mul {T ro} (pa pb)%P.
Arguments polyn_norm {T ro} pa%P.
Arguments polyn_one {T ro}.
Arguments polyn_opp {T ro} p%P.
Arguments polyn_quot {T ro} (pa pb)%P.
Arguments same_deg_sum_coeff {T ro} ma la%list.

Module polynomial_Notations.

Notation "pa + pb" := (polyn_add pa pb) : P_scope.
Notation "pa * pb" := (polyn_mul pa pb) : P_scope.
Notation "pa - pb" := (polyn_sub pa pb) : P_scope.

End polynomial_Notations.

Import polynomial_Notations.

(* canon_polyn: normalised polynomial
   its degrees are in decreasing order
   and that there are no nul coefficient. *)
Record canon_polyn T {ro : ring_like_op T} := mk_canon_polyn
  { cp_polyn : polyn T;
    cp_prop : is_canon_polyn cp_polyn = true }.

Arguments canon_polyn T {ro}.
Arguments mk_canon_polyn {T ro} cp_polyn%P.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).
Context {Heq : rngl_has_eqb = true}.
(*
Context {Hop : rngl_has_opp = true}.
*)
Context {H10 : rngl_has_1_neq_0 = true}.

(* equality of canonical polynomials is equivalent to
   equality on polynomials because of unicity of
   proof of equality between booleans *)

Theorem canon_polyn_eq_eq : ∀ (pa pb : canon_polyn T),
  pa = pb ↔ cp_polyn pa = cp_polyn pb.
Proof.
intros.
split; [ now intros; subst pb | ].
intros Hab.
destruct pa as (pa, ppa).
destruct pb as (pb, ppb).
cbn in Hab; subst pb.
f_equal.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

(* *)

Definition monom_eqb ma mb :=
  (rngl_eqb (mcoeff ma) (mcoeff mb) && Nat.eqb (mdeg ma) (mdeg mb))%bool.

Theorem monom_eqb_eq : equality monom_eqb.
Proof.
intros ma mb.
split; intros Hab. {
  destruct ma as (ca, da).
  destruct mb as (cb, db).
  unfold monom_eqb in Hab; cbn in Hab.
  apply Bool.andb_true_iff in Hab.
  destruct Hab as (Hcab, Hdab).
  apply (rngl_eqb_eq Heq) in Hcab; subst cb.
  apply Nat.eqb_eq in Hdab; subst db.
  easy.
} {
  subst mb.
  unfold monom_eqb.
  rewrite Nat.eqb_refl, Bool.andb_true_r.
  apply equality_refl.
  unfold equality.
  apply (rngl_eqb_eq Heq).
}
Qed.

(* could add here ring-like of general polynomials (not necessarily
   canonical, with a specific equality (equivalence relation) *)
(* but... but... actually it is not possible, because my present
   version of ring-likes use Leibnitz equality; for example the
   axiom of commutativity of addition is written
     a + b = b + a
   and not, e.g.
     myeq (a+b) (b+a)
*)

(* ... *)

(* canonical polynomial ring-like operators *)

(* limited to normalised (or canonical) polynomials in order to use
   normal equality instead of equivalence relation as equality because
   normal equality allows to replace expressions without questioning *)

Theorem zero_is_canon_polyn : is_canon_polyn polyn_zero = true.
Proof.
now cbn; rewrite iter_list_empty.
Qed.

Theorem one_is_canon_polyn : is_canon_polyn polyn_one = true.
Proof.
cbn; rewrite iter_list_only_one; [ cbn | easy ].
apply Bool.negb_true_iff.
apply (rngl_eqb_neq Heq).
apply (rngl_1_neq_0 H10).
Qed.

Definition canon_polyn_zero := mk_canon_polyn polyn_zero zero_is_canon_polyn.
Definition canon_polyn_one := mk_canon_polyn polyn_one one_is_canon_polyn.

Theorem in_merge_same_deg : ∀ (ma : monom T) la,
  ma ∈ merge_same_deg la
  → mdeg ma ∈ map (λ mb, mdeg mb) la.
Proof.
intros * Hma.
unfold merge_same_deg in Hma.
revert ma Hma.
induction la as [| mb]; intros; [ easy | ].
cbn - [ In ] in Hma |-*.
unfold same_deg_sum_coeff in Hma at 1.
remember (fold_right same_deg_sum_coeff [] la) as lb eqn:Hlb.
symmetry in Hlb.
destruct lb as [| mc]. {
  destruct Hma as [Hma| Hma]; [ now subst mb; left | easy ].
}
rewrite if_eqb_eq_dec in Hma.
destruct (Nat.eq_dec (mdeg mb) (mdeg mc)) as [Hmbc| Hmbc]. {
  destruct Hma as [Hma| Hma]; [ now subst ma; left | ].
  now right; apply IHla; right.
}
destruct Hma as [Hma| Hma]; [ now subst mb; left | ].
now right; apply IHla.
Qed.

Theorem sorted_lt_sorted_le_mdeg : ∀ la : list (monom T),
  let f := λ ma mb, mdeg mb <? mdeg ma in
  let g := λ ma mb, mdeg mb <=? mdeg ma in
  sorted f la
  → sorted g la.
Proof.
intros * Hs.
assert (Htraf : transitive f). {
  unfold f; intros a b c Hab Hbc.
  apply Nat.ltb_lt in Hab, Hbc.
  apply Nat.ltb_lt.
  now transitivity (mdeg b).
}
assert (Htrag : transitive g). {
  unfold g; intros a b c Hab Hbc.
  apply Nat.leb_le in Hab, Hbc.
  apply Nat.leb_le.
  now transitivity (mdeg b).
}
induction la as [| ma]; [ easy | cbn ].
assert (H : sorted f la) by now apply sorted_cons in Hs.
specialize (IHla H); clear H.
apply (sorted_cons_iff Htrag).
apply (sorted_cons_iff Htraf) in Hs.
split; [ easy | ].
intros mb Hmb.
destruct Hs as (Hsf, Hs).
specialize (Hs _ Hmb).
apply Nat.ltb_lt in Hs.
apply Nat.leb_le.
now apply Nat.lt_le_incl.
Qed.

Theorem sorted_le_sorted_lt_merge_same_deg : ∀ la,
  let f := λ ma mb, mdeg mb <=? mdeg ma in
  let g := λ ma mb, mdeg mb <? mdeg ma in
  sorted f la
  → sorted g (merge_same_deg la).
Proof.
intros * Hs.
assert (Htrf : transitive f). {
  intros ma mb mc Hmab Hmbc.
  unfold f in Hmab, Hmbc|-*.
  apply Nat.leb_le in Hmab, Hmbc.
  apply Nat.leb_le.
  now transitivity (mdeg mb).
}
assert (Htrg : transitive g). {
  intros ma mb mc Hmab Hmbc.
  unfold f in Hmab, Hmbc|-*.
  apply Nat.ltb_lt in Hmab, Hmbc.
  apply Nat.ltb_lt.
  now transitivity (mdeg mb).
}
unfold merge_same_deg.
induction la as [| ma]; [ easy | cbn ].
assert (H : sorted f la) by now apply sorted_cons in Hs.
specialize (IHla H); clear H.
unfold same_deg_sum_coeff at 1.
remember (fold_right same_deg_sum_coeff [] la) as lb eqn:Hlb.
symmetry in Hlb.
destruct lb as [| mb]; [ easy | ].
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec (mdeg ma) (mdeg mb)) as [Hdab| Hdab]. {
  apply (sorted_cons_iff Htrg).
  apply (sorted_cons_iff Htrg) in IHla.
  split; [ easy | ].
  intros b Hb.
  destruct IHla as (Hsb, Hgb).
  unfold g in Hgb |-*; cbn.
  rewrite <- Hdab in Hgb.
  now apply Hgb.
}
apply (sorted_cons_iff Htrg).
split; [ easy | ].
intros mc Hmc.
destruct Hmc as [Hmc| Hmc]. {
  subst mc.
  apply (sorted_cons_iff Htrf) in Hs.
  destruct Hs as (Hsfa, Hfa).
  apply (sorted_cons_iff Htrg) in IHla.
  destruct IHla as (Hsgb, Hggb).
  unfold g; cbn.
  apply Nat.ltb_lt.
  specialize (Hfa mb) as H1.
  destruct la as [| mc]; [ easy | ].
  cbn in Hlb.
  unfold same_deg_sum_coeff in Hlb at 1.
  remember (fold_right same_deg_sum_coeff [] la) as ld eqn:Hld.
  symmetry in Hld.
  destruct ld as [| md]. {
    injection Hlb; clear Hlb; intros; subst mc lb.
    specialize (H1 (or_introl eq_refl)).
    unfold f in H1; cbn in H1.
    apply Nat.leb_le in H1.
    flia Hdab H1.
  }
  erewrite if_eqb_eq_dec in Hlb.
  destruct (Nat.eq_dec (mdeg mc) (mdeg md)) as [Hdcd| Hdcd]. {
    injection Hlb; clear Hlb; intros; subst mb ld.
    cbn in Hdab |-*.
    specialize (Hfa _ (or_introl eq_refl)) as H2.
    unfold f in H2; cbn in H2.
    apply Nat.leb_le in H2.
    flia Hdab H2.
  }
  injection Hlb; clear Hlb; intros; subst mc lb.
  specialize (H1 (or_introl eq_refl)).
  unfold f in H1; cbn in H1.
  apply Nat.leb_le in H1.
  flia Hdab H1.
}
unfold g; cbn.
apply Nat.ltb_lt.
destruct la as [| md]; [ easy | ].
cbn in Hlb.
unfold same_deg_sum_coeff in Hlb at 1.
remember (fold_right same_deg_sum_coeff [] la) as ld eqn:Hld.
symmetry in Hld.
destruct ld as [| me]. {
  now injection Hlb; clear Hlb; intros; subst md lb.
}
erewrite if_eqb_eq_dec in Hlb.
destruct (Nat.eq_dec (mdeg md) (mdeg me)) as [Hdde| Hdde]. {
  injection Hlb; clear Hlb; intros; subst mb ld.
  cbn in Hdab |-*.
  apply (sorted_cons_iff Htrg) in IHla.
  unfold g in IHla; cbn in IHla.
  destruct IHla as (Hsb, Hbd).
  specialize (Hbd _ Hmc) as H1.
  apply Nat.ltb_lt in H1.
  apply (Nat.lt_le_trans _ (mdeg md)); [ easy | ].
  apply (sorted_cons_iff Htrf) in Hs.
  destruct Hs as (Hsa, Hbf).
  specialize (Hbf md (or_introl eq_refl)) as H2.
  unfold f in H2; cbn in H2.
  now apply Nat.leb_le in H2.
}
injection Hlb; clear Hlb; intros; subst md lb.
apply (sorted_cons_iff Htrf) in Hs.
destruct Hs as (Hsa, Hfa).
specialize (Hfa _ (or_introl eq_refl)) as H1.
unfold f in H1; cbn in H1.
apply Nat.leb_le in H1.
apply (Nat.lt_le_trans _ (mdeg mb)); [ | easy ].
apply (sorted_cons_iff Htrg) in IHla.
destruct IHla as (Hsc, Hgc).
specialize (Hgc _ Hmc) as H2.
unfold g in H2; cbn in H2.
now apply Nat.ltb_lt in H2.
Qed.

Theorem monl_norm_is_sorted : ∀ la,
  sorted (λ x y : monom T, mdeg y <? mdeg x) (monl_norm la).
Proof.
intros.
unfold monl_norm.
set (f := λ x y : monom T, mdeg y <? mdeg x).
set (g := λ x y : monom T, mdeg y <=? mdeg x).
assert (Htrf : transitive f). {
  intros ma mb mc Hmab Hmbc.
  apply Nat.ltb_lt in Hmab, Hmbc.
  apply Nat.ltb_lt.
  now transitivity (mdeg mb).
}
assert (Httg : total_relation g). {
  intros ma mb.
  unfold g; cbn.
  apply Nat_leb_total_relation.
}
apply (sorted_filter Htrf).
apply sorted_le_sorted_lt_merge_same_deg.
now apply sorted_isort.
Qed.

Theorem in_monl_norm_neq_mcoeff_0 : ∀ la ma,
  ma ∈ monl_norm la
  → mcoeff ma ≠ 0%F.
Proof.
intros * Ha.
unfold monl_norm in Ha.
apply filter_In in Ha.
apply (rngl_eqb_neq Heq).
now apply Bool.negb_true_iff.
Qed.

Theorem monl_norm_is_canon_monl : ∀ la,
  is_canon_monl (monl_norm la) = true.
Proof.
intros.
unfold is_canon_monl.
apply Bool.andb_true_iff.
split. {
  rewrite fold_sorted.
  apply monl_norm_is_sorted.
}
apply all_true_and_list_true_iff.
intros ma Hma.
apply Bool.negb_true_iff.
apply (rngl_eqb_neq Heq).
now apply in_monl_norm_neq_mcoeff_0 in Hma.
Qed.

Theorem polyn_norm_is_canon_polyn : ∀ pa,
  is_canon_polyn (polyn_norm pa) = true.
Proof.
intros.
destruct pa as (la); cbn.
unfold is_canon_polyn.
unfold polyn_norm.
cbn - [ monl_norm ].
apply monl_norm_is_canon_monl.
Qed.

(* canon polyn addition *)

Theorem canon_polyn_add_prop : ∀ pa pb,
  is_canon_polyn (polyn_norm (cp_polyn pa + cp_polyn pb)) = true.
Proof.
intros.
destruct pa as (pa, ppa).
destruct pb as (pb, ppb).
move pb before pa; cbn.
apply polyn_norm_is_canon_polyn.
Qed.

Definition canon_polyn_add (pa pb : canon_polyn T) :=
  mk_canon_polyn (polyn_norm (polyn_add (cp_polyn pa) (cp_polyn pb)))
    (canon_polyn_add_prop pa pb).

(* canon polyn multiplication *)

Theorem canon_polyn_mul_prop : ∀ pa pb,
  is_canon_polyn (polyn_norm (cp_polyn pa * cp_polyn pb)) = true.
Proof.
intros.
destruct pa as (pa, ppa).
destruct pb as (pb, ppb).
move pb before pa; cbn.
apply polyn_norm_is_canon_polyn.
Qed.

Definition canon_polyn_mul (pa pb : canon_polyn T) :=
  mk_canon_polyn (polyn_norm (polyn_mul (cp_polyn pa) (cp_polyn pb)))
    (canon_polyn_mul_prop pa pb).

(* canon polyn opposite or subtraction *)

Theorem canon_polyn_opp_prop : ∀ pa,
  is_canon_polyn (polyn_norm (polyn_opp (cp_polyn pa))) = true.
Proof.
intros.
destruct pa as (pa, ppa).
apply polyn_norm_is_canon_polyn.
Qed.

Definition canon_polyn_opp pa :=
  mk_canon_polyn
    (polyn_norm (polyn_opp (cp_polyn pa)))
    (canon_polyn_opp_prop pa).

Definition canon_polyn_opt_opp_or_sous :
   option
     ((canon_polyn T → canon_polyn T) +
      (canon_polyn T → canon_polyn T → canon_polyn T)) :=
  match (@rngl_opt_opp_or_sous T ro) with
  | Some (inl _) => Some (inl canon_polyn_opp)
  | Some (inr _) => None
  | None => None
  end.

(* canon polyn quotient *)

Theorem canon_polyn_quot_prop : ∀ pa pb,
  is_canon_polyn (polyn_norm (polyn_quot (cp_polyn pa) (cp_polyn pb))) = true.
Proof.
intros.
destruct pa as (pa, ppa).
destruct pb as (pb, ppb).
move pb before pa; cbn.
apply polyn_norm_is_canon_polyn.
Qed.

Definition canon_polyn_quot pa pb :=
  mk_canon_polyn
    (polyn_norm (polyn_quot (cp_polyn pa) (cp_polyn pb)))
    (canon_polyn_quot_prop pa pb).

Definition canon_polyn_opt_inv_or_quot :
   option
     ((canon_polyn T → canon_polyn T) +
      (canon_polyn T → canon_polyn T → canon_polyn T)) :=
  match (@rngl_opt_inv_or_quot T ro) with
  | Some _ => Some (inr canon_polyn_quot)
  | None => None
  end.

(* canon polyn eqb *)

Definition polyn_eqb pa pb := list_eqv monom_eqb (monl pa) (monl pb).
Definition canon_polyn_eqb pa pb := polyn_eqb (cp_polyn pa) (cp_polyn pb).

Definition canon_polyn_opt_eqb :=
  match @rngl_opt_eqb T ro with
  | Some _ => Some canon_polyn_eqb
  | None => None
  end.

Definition polyn_ring_like_op : ring_like_op (canon_polyn T) :=
  {| rngl_zero := canon_polyn_zero;
     rngl_one := canon_polyn_one;
     rngl_add := canon_polyn_add;
     rngl_mul := canon_polyn_mul;
     rngl_opt_opp_or_sous := canon_polyn_opt_opp_or_sous;
     rngl_opt_inv_or_quot := canon_polyn_opt_inv_or_quot;
     rngl_opt_eqb := canon_polyn_opt_eqb;
     rngl_opt_le := None |}.

(* allows to use ring-like theorems on polynomials *)
Canonical Structure polyn_ring_like_op.

(* to search for ring-like polynomials operators in the context *)
Global Existing Instance polyn_ring_like_op.

(* canonical polynomial ring-like properties *)

(* canon_polyn: commutativity of addition *)

Theorem eq_merge_same_deg_nil : ∀ (la : list (monom T)),
  merge_same_deg la = [] → la = [].
Proof.
intros * Hma.
destruct la as [| ma]; [ easy | ].
cbn in Hma.
unfold same_deg_sum_coeff in Hma at 1.
destruct (fold_right _ _ _) as [| mb lb]; [ easy | ].
now destruct (mdeg ma =? mdeg mb).
Qed.

Theorem eq_merge_same_deg_unit : ∀ (la : list (monom T)) ma,
  merge_same_deg la = [ma] → ∀ mb, mb ∈ la → mdeg ma = mdeg mb.
Proof.
intros * Hma mb Hmb.
revert ma mb Hma Hmb.
induction la as [| mc]; intros; [ easy | ].
cbn in Hma.
rewrite fold_merge_same_deg in Hma.
destruct Hmb as [Hmb| Hmb]. {
  subst mc.
  unfold same_deg_sum_coeff in Hma.
  remember (merge_same_deg la) as lb eqn:Hlb; symmetry in Hlb.
  destruct lb as [| mc]. {
    now injection Hma; clear Hma; intros; subst mb.
  }
  rewrite if_eqb_eq_dec in Hma.
  destruct (Nat.eq_dec (mdeg mb) (mdeg mc)) as [Hbc| Hbc]; [ | easy ].
  now injection Hma; clear Hma; intros; subst ma.
}
unfold same_deg_sum_coeff in Hma.
remember (merge_same_deg la) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| md]. {
  now apply eq_merge_same_deg_nil in Hlb; subst la.
}
rewrite if_eqb_eq_dec in Hma.
destruct (Nat.eq_dec (mdeg mc) (mdeg md)) as [Hcd| Hcd]; [ | easy ].
injection Hma; clear Hma; intros; subst ma lb; cbn.
specialize (IHla md mb eq_refl Hmb) as H1.
congruence.
Qed.

(*
Theorem eq_merge_same_deg_cons : ∀ (la lb : list (monom T)) mb,
  merge_same_deg la = mb :: lb
  → ∃ i, 0 < i ≤ length la ∧
    (∀ ma, ma ∈ firstn i la → mdeg ma = mdeg mb) ∧
    merge_same_deg (skipn i la) = lb ∧
    mcoeff mb = ∑ (ma ∈ firstn i la), mcoeff ma ∧
(**)
    mdeg (nth i la (Mon 0 (S (mdeg mb)))) ≠ mdeg mb.
(*
    mdeg (hd (Mon 0 (S (mdeg mb))) (skipn i la)) ≠ mdeg mb.
*)
Proof.
intros * Hma.
revert mb lb Hma.
induction la as [| ma]; intros; [ easy | ].
cbn in Hma.
rewrite fold_merge_same_deg in Hma.
unfold same_deg_sum_coeff in Hma.
remember (merge_same_deg la) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| mc]. {
  apply eq_merge_same_deg_nil in Hlc; subst la.
  injection Hma; clear Hma; intros; subst mb lb; cbn.
  exists 1; cbn - [ In ].
  split; [ easy | ].
  split. {
    intros mb Hmb.
    destruct Hmb as [Hmb| ]; [ now subst mb | easy ].
  }
  split; [ easy | ].
  rewrite rngl_summation_list_only_one.
  split; [ easy | ].
  apply Nat.neq_succ_diag_l.
}
rewrite if_eqb_eq_dec in Hma.
destruct (Nat.eq_dec _ _) as [Hac| Hac]. 2: {
  injection Hma; clear Hma; intros; subst mb lb.
  cbn - [ In ].
  exists 1.
  split. {
    split; [ easy | ].
    now apply -> Nat.succ_le_mono.
  }
  split. {
    intros mb Hmb; cbn - [ In ] in Hmb.
    destruct Hmb as [Hmb| ]; [ now subst mb | easy ].
  }
  split; [ easy | ].
  split. 2: {
    destruct la as [| mb]; [ easy | cbn ].
    cbn in Hlc.
    intros H; apply Hac; clear Hac.
    rewrite fold_merge_same_deg in Hlc.
    unfold same_deg_sum_coeff in Hlc.
    destruct (merge_same_deg la) as [| md ld]. {
      now injection Hlc; clear Hlc; intros; subst mc lc.
    }
    rewrite if_eqb_eq_dec in Hlc.
    destruct (Nat.eq_dec _ _) as [Hbd| Hbd]. {
      now injection Hlc; clear Hlc; intros; subst mc lc.
    }
    now injection Hlc; clear Hlc; intros; subst mc lc.
  }
  now cbn; rewrite rngl_summation_list_only_one.
}
injection Hma; clear Hma; intros; subst lc mb.
cbn - [ In ].
specialize (IHla mc lb eq_refl) as H1.
destruct H1 as (j & Hjl & Hfj & Hmj & Hcj & Hc).
exists (S j).
split. {
  split; [ easy | ].
  now apply -> Nat.succ_le_mono.
}
split. {
  intros mb Hmb.
  cbn - [ In ] in Hmb.
  destruct Hmb as [Hmb| Hmb]; [ now subst mb | ].
  specialize (Hfj _ Hmb) as H1.
  congruence.
}
split; [ easy | ].
split; [ cbn | now rewrite Hac ].
rewrite rngl_summation_list_cons.
now f_equal.
Qed.
*)

Theorem merge_same_deg_cons_eq_cons : ∀ (ma mb : monom T) la lb,
  merge_same_deg (ma :: la) = mb :: lb
  → mdeg ma = mdeg mb.
Proof.
intros * Hab.
destruct la as [| mc]; cbn. {
  cbn in Hab.
  now injection Hab; clear Hab; intros; subst mb.
}
remember (mc :: la) as lc eqn:Hlc.
cbn in Hab; subst lc.
rewrite fold_merge_same_deg in Hab.
unfold same_deg_sum_coeff in Hab.
remember (merge_same_deg (mc :: la)) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [| md]. {
  now injection Hab; clear Hab; intros; subst mb.
}
rewrite if_eqb_eq_dec in Hab.
now destruct (Nat.eq_dec _ _); injection Hab; clear Hab; intros; subst mb.
Qed.

Theorem merge_same_deg_app_eq_cons : ∀ la lb lc cc dc,
  merge_same_deg (la ++ lb) = cc*☓^dc :: lc
  → mdeg (hd 0*☓^(S dc) lb) ≠ dc
  → (∀ ma : monom T, ma ∈ la → mdeg ma = dc)
  → merge_same_deg lb = lc.
Proof.
intros * Habc Hb Hdc.
revert lb lc cc dc Habc Hb Hdc.
induction la as [| ma]; intros. {
  cbn - [ merge_same_deg ] in Habc.
  destruct lb as [| mb]; [ easy | ].
  cbn in Hb.
  cbn in Habc; rewrite fold_merge_same_deg in Habc.
  clear Hdc; exfalso.
  unfold same_deg_sum_coeff in Habc.
  remember (merge_same_deg lb) as la eqn:Hla; symmetry in Hla.
  destruct la as [| ma]. {
    now injection Habc; clear Habc; intros; subst mb.
  }
  rewrite if_eqb_eq_dec in Habc.
  destruct (Nat.eq_dec _ _) as [Hba| Hba]. {
    now injection Habc; clear Habc; intros; subst dc.
  }
  now injection Habc; clear Habc; intros; subst mb.
}
cbn in Habc; rewrite fold_merge_same_deg in Habc.
unfold same_deg_sum_coeff in Habc.
remember (merge_same_deg (la ++ lb)) as ld eqn:Hld; symmetry in Hld.
destruct ld as [| (cd, dd)]. {
  apply eq_merge_same_deg_nil, app_eq_nil in Hld.
  destruct Hld; subst la lb.
  now injection Habc; intros; subst lc.
}
rewrite if_eqb_eq_dec in Habc.
destruct (Nat.eq_dec _ _) as [Had| Had]. {
  cbn in Had; subst dd.
  cbn in Habc.
  injection Habc; clear Habc; intros; subst ld cc dc.
  apply IHla in Hld; [ easy | easy | ].
  intros mb Hmb.
  now apply Hdc; right.
}
injection Habc; clear Habc; intros; subst ma lc.
cbn in Had.
clear IHla Hb.
assert (Hdc' : ∀ ma, ma ∈ la → mdeg ma ≠ dd). {
  intros ma Hma.
  specialize (Hdc _ (or_intror Hma)) as H1.
  congruence.
}
clear Hdc Had.
revert lb cd dd ld Hld Hdc'.
induction la as [| ma]; intros; [ easy | ].
cbn in Hld; rewrite fold_merge_same_deg in Hld.
unfold same_deg_sum_coeff in Hld.
remember (merge_same_deg (la ++ lb)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| mc]. {
  injection Hld; clear Hld; intros; subst ma ld.
  now specialize (Hdc' _ (or_introl eq_refl)).
}
rewrite if_eqb_eq_dec in Hld.
destruct (Nat.eq_dec _ _) as [Hac| Hac]. {
  injection Hld; clear Hld; intros; subst cd dd ld.
  now specialize (Hdc' _ (or_introl eq_refl)).
}
injection Hld; clear Hld; intros; subst ma ld.
now specialize (Hdc' _ (or_introl eq_refl)).
Qed.

Theorem eq_merge_same_deg_cons_iff : ∀ (la lb : list (monom T)) mb,
  merge_same_deg la = mb :: lb
  ↔ ∃ i, 0 < i ≤ length la ∧
    (∀ ma, ma ∈ firstn i la → mdeg ma = mdeg mb) ∧
    merge_same_deg (skipn i la) = lb ∧
    mcoeff mb = ∑ (ma ∈ firstn i la), mcoeff ma ∧
    mdeg (nth i la (Mon 0 (S (mdeg mb)))) ≠ mdeg mb.
Proof.
intros.
split. {
  intros * Hma.
  revert mb lb Hma.
  induction la as [| ma]; intros; [ easy | ].
  cbn in Hma.
  rewrite fold_merge_same_deg in Hma.
  unfold same_deg_sum_coeff in Hma.
  remember (merge_same_deg la) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as [| mc]. {
    apply eq_merge_same_deg_nil in Hlc; subst la.
    injection Hma; clear Hma; intros; subst mb lb; cbn.
    exists 1; cbn - [ In ].
    split; [ easy | ].
    split. {
      intros mb Hmb.
      destruct Hmb as [Hmb| ]; [ now subst mb | easy ].
    }
    split; [ easy | ].
    rewrite rngl_summation_list_only_one.
    split; [ easy | ].
    apply Nat.neq_succ_diag_l.
  }
  rewrite if_eqb_eq_dec in Hma.
  destruct (Nat.eq_dec _ _) as [Hac| Hac]. 2: {
    injection Hma; clear Hma; intros; subst mb lb.
    cbn - [ In ].
    exists 1.
    split. {
      split; [ easy | ].
      now apply -> Nat.succ_le_mono.
    }
    split. {
      intros mb Hmb; cbn - [ In ] in Hmb.
      destruct Hmb as [Hmb| ]; [ now subst mb | easy ].
    }
    split; [ easy | ].
    split. 2: {
      destruct la as [| mb]; [ easy | cbn ].
      cbn in Hlc.
      intros H; apply Hac; clear Hac.
      rewrite fold_merge_same_deg in Hlc.
      unfold same_deg_sum_coeff in Hlc.
      destruct (merge_same_deg la) as [| md ld]. {
        now injection Hlc; clear Hlc; intros; subst mc lc.
      }
      rewrite if_eqb_eq_dec in Hlc.
      destruct (Nat.eq_dec _ _) as [Hbd| Hbd]. {
        now injection Hlc; clear Hlc; intros; subst mc lc.
      }
      now injection Hlc; clear Hlc; intros; subst mc lc.
    }
    now cbn; rewrite rngl_summation_list_only_one.
  }
  injection Hma; clear Hma; intros; subst lc mb.
  cbn - [ In ].
  specialize (IHla mc lb eq_refl) as H1.
  destruct H1 as (j & Hjl & Hfj & Hmj & Hcj & Hc).
  exists (S j).
  split. {
    split; [ easy | ].
    now apply -> Nat.succ_le_mono.
  }
  split. {
    intros mb Hmb.
    cbn - [ In ] in Hmb.
    destruct Hmb as [Hmb| Hmb]; [ now subst mb | ].
    specialize (Hfj _ Hmb) as H1.
    congruence.
  }
  split; [ easy | ].
  split; [ cbn | now rewrite Hac ].
  rewrite rngl_summation_list_cons.
  now f_equal.
} {
  intros H.
  destruct H as (i & Hil & Hfi & Hdb & Hcb & Hnb).
  destruct mb as (cb, db).
  cbn in Hfi, Hcb, Hnb.
  subst cb lb.
  revert i db Hil Hfi Hnb.
  induction la as [| ma]; intros; [ cbn in Hil; flia Hil | ].
  cbn; rewrite fold_merge_same_deg.
  destruct i; [ easy | ].
  destruct Hil as (_, Hil); cbn in Hil.
  apply Nat.succ_le_mono in Hil.
  cbn - [ In ] in Hfi.
  cbn in Hnb.
  cbn - [ merge_same_deg ].
  rewrite rngl_summation_list_cons.
  unfold same_deg_sum_coeff.
  remember (merge_same_deg la) as lb eqn:Hlb; symmetry in Hlb.
  destruct lb as [| mb]. {
    apply eq_merge_same_deg_nil in Hlb; subst la.
    rewrite rngl_summation_list_empty; [ | apply firstn_nil ].
    rewrite rngl_add_0_r, skipn_nil; cbn.
    rewrite <- (Hfi _ (or_introl eq_refl)).
    now destruct ma.
  }
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec _ _) as [Hab| Hab]. {
    rewrite (Hfi _ (or_introl eq_refl)).
    f_equal. 2: {
      symmetry.
      assert (Hfi' : ∀ ma, ma ∈ firstn i la → mdeg ma = db). {
        intros mc Hma.
        now apply Hfi; right.
      }
      rename i into n.
      rewrite <- (firstn_skipn n la) in Hlb, Hnb.
      move db before n.
      rewrite app_nth2 in Hnb. 2: {
        rewrite firstn_length, min_l; [ now unfold ge | easy ].
      }
      rewrite firstn_length, min_l in Hnb; [ | easy ].
      rewrite Nat.sub_diag in Hnb.
      remember (firstn n la) as lc eqn:Hlc; symmetry in Hlc.
      remember (skipn n la) as ld eqn:Hld; symmetry in Hld.
      rewrite <- List_hd_nth_0 in Hnb.
      clear Hlc Hld IHla Hil.
      specialize (Hfi ma (or_introl eq_refl)) as H1.
      rewrite H1 in Hab.
      clear ma Hfi H1.
      symmetry in Hab.
      clear la n.
      destruct mb as (cc, dc).
      cbn in Hab; subst db.
      rename lc into la; rename lb into lc; rename ld into lb.
      move la before lc; move lb before lc.
      now apply merge_same_deg_app_eq_cons in Hlb.
    }
    f_equal; f_equal.
    destruct i. {
      specialize (Hfi ma (or_introl eq_refl)).
      cbn; rewrite rngl_summation_list_empty; [ | easy ].
      destruct la as [| mc]; [ easy | ].
      apply merge_same_deg_cons_eq_cons in Hlb; cbn in Hnb.
      congruence.
    }
    specialize (IHla (S i) db) as H1.
    assert (H : 0 < S i ≤ length la) by easy.
    specialize (H1 H); clear H.
    assert (H : ∀ ma, ma ∈ firstn (S i) la → mdeg ma = db). {
      intros mc Hmc.
      now apply Hfi; right.
    }
    specialize (H1 H); clear H.
    specialize (H1 Hnb).
    remember (S i) as si.
    injection H1; clear H1; intros H1 H2; subst si.
    now rewrite H2.
  }
  specialize (Hfi _ (or_introl eq_refl)) as H1.
  destruct la as [| mc]; [ easy | ].
  destruct i. {
    cbn; rewrite rngl_summation_list_empty; [ | easy ].
    rewrite rngl_add_0_r.
    f_equal; [ now rewrite <- H1; destruct ma | easy ].
  }
  cbn - [ In ] in Hfi.
  specialize (Hfi _ (or_intror (or_introl eq_refl))) as H2.
  apply merge_same_deg_cons_eq_cons in Hlb.
  congruence.
}
Qed.

(*
Theorem pouet : ∀ (la lb : list (monom T)) mb,
  merge_same_deg la = mb :: lb
  → mdeg (hd (Mon 0 (S (mdeg mb))) lb) ≠ mdeg mb.
Proof.
intros * Hma.
apply eq_merge_same_deg_cons in Hma.
destruct Hma as (j & Hjl & Hfj & Hmj & Hcj & Hc); cbn.
destruct lb as [| ma]; [ apply Nat.neq_succ_diag_l | cbn ].
apply eq_merge_same_deg_cons in Hmj.
destruct Hmj as (k & Hkl & Hfk & Hmj & Hck & Hk).
destruct lb as [| mc]. {
  apply eq_merge_same_deg_nil in Hmj.
  rewrite List_skipn_skipn in Hmj.
Search (skipn _ _ = []).
...
*)

Theorem eq_merge_same_deg_cons_cons : ∀ la lb (ma mb : monom T),
  merge_same_deg la = ma :: mb :: lb
  → mdeg ma ≠ mdeg mb.
Proof.
intros * Hma.
intros Hab.
destruct ma as (ca, da).
destruct mb as (cb, db).
cbn in Hab; subst db.
revert ca cb da lb Hma.
induction la as [| ma]; intros; [ easy | ].
cbn in Hma.
rewrite fold_merge_same_deg in Hma.
unfold same_deg_sum_coeff in Hma.
remember (merge_same_deg la) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| mb]; [ easy | ].
rewrite if_eqb_eq_dec in Hma.
destruct (Nat.eq_dec _ _) as [Hab| Hab]. {
  injection Hma; clear Hma; intros; subst lc ca da.
  destruct ma as (ca, da).
  destruct mb as (cc, dc).
  cbn in Hlc, Hab; subst dc.
  apply (IHla _ _ _ _ eq_refl).
}
now injection Hma; clear Hma; intros; subst lc ma mb.
Qed.

Theorem merge_same_deg_idemp : ∀ (la : list (monom T)),
  merge_same_deg (merge_same_deg la) = merge_same_deg la.
Proof.
intros.
remember (merge_same_deg la) as lb eqn:Hlb; symmetry in Hlb.
revert la Hlb.
induction lb as [| ma]; intros; [ easy | cbn ].
rewrite fold_merge_same_deg.
unfold same_deg_sum_coeff.
remember (merge_same_deg lb) as lc eqn:Hlc in |-*; symmetry in Hlc.
destruct lc as [| mb]. {
  f_equal.
  destruct lb as [| mc]; [ easy | exfalso ].
  cbn in Hlc.
  rewrite fold_merge_same_deg in Hlc.
  unfold same_deg_sum_coeff in Hlc.
  destruct (merge_same_deg lb) as [| md ld]; [ easy | ].
  now destruct (mdeg mc =? mdeg md).
}
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec (mdeg ma) (mdeg mb)) as [Hab| Hab]. {
  exfalso; clear IHlb.
  move la after lb.
  destruct lb as [| mc]; [ easy | ].
  apply eq_merge_same_deg_cons_cons in Hlb.
  rewrite Hab in Hlb; clear Hab.
  cbn in Hlc.
  rewrite fold_merge_same_deg in Hlc.
  unfold same_deg_sum_coeff in Hlc.
  clear la ma.
  remember (merge_same_deg lb) as la eqn:Hla.
  symmetry in Hla.
  destruct la as [| ma]. {
    now injection Hlc; clear Hlc; intros; subst mc lc.
  }
  rewrite if_eqb_eq_dec in Hlc.
  destruct (Nat.eq_dec _ _) as [Hca| Hca]. {
    now injection Hlc; clear Hlc; intros; subst lc mb.
  }
  now injection Hlc; clear Hlc; intros; subst mb lc.
}
f_equal.
rewrite <- Hlc.
clear lc mb Hlc Hab.
revert ma lb IHlb Hlb.
induction la as [| mb]; intros; [ easy | ].
cbn in Hlb.
rewrite fold_merge_same_deg in Hlb.
unfold same_deg_sum_coeff in Hlb.
remember (merge_same_deg la) as ld eqn:Hld.
symmetry in Hld.
destruct ld as [| md]. {
  now injection Hlb; clear Hlb; intros; subst lb.
}
rewrite if_eqb_eq_dec in Hlb.
destruct (Nat.eq_dec _ _) as [Hbd| Hbd]. 2: {
  injection Hlb; clear Hlb; intros; subst mb lb.
  now apply (IHlb la).
}
injection Hlb; clear Hlb; intros; subst ma ld.
now apply IHla with (ma := md).
Qed.

Theorem merge_same_deg_app_idemp_r : ∀ (la lb : list (monom T)),
  merge_same_deg (la ++ lb) = merge_same_deg (la ++ merge_same_deg lb).
Proof.
intros.
revert lb.
induction la as [| ma]; intros; [ symmetry; apply merge_same_deg_idemp | cbn ].
do 2 rewrite fold_merge_same_deg.
now rewrite IHla.
Qed.

Theorem merge_same_deg_rev : ∀ (la : list (monom T)),
  merge_same_deg (rev la) = rev (merge_same_deg la).
Proof.
intros.
remember (merge_same_deg la) as lb eqn:Hlb; symmetry in Hlb.
revert la Hlb.
induction lb as [| mb]; intros. {
  now apply eq_merge_same_deg_nil in Hlb; subst la.
}
apply eq_merge_same_deg_cons_iff in Hlb.
destruct Hlb as (j & Hjl & Hfj & Hmj & Hcj & Hc); cbn.
specialize (IHlb _ Hmj) as H1.
rewrite <- H1; clear H1.
specialize (firstn_rev (length la - j) la) as H1.
replace (length la - (length la - j)) with j in H1 by flia Hjl.
rewrite <- (Nat.add_0_l j) in Hc.
rewrite <- List_nth_skipn in Hc.
rewrite <- H1; clear H1.
rewrite <- (rev_involutive la) in Hcj, Hfj, Hmj, Hc.
rewrite firstn_rev in Hcj, Hfj.
rewrite skipn_rev in Hmj, Hc.
rewrite rev_length in Hcj, Hfj, Hmj, Hc.
remember (length la - j) as i eqn:Hi.
remember (skipn i (rev la)) as lc.
rewrite (rngl_summation_list_permut _ monom_eqb_eq _ lc) in Hcj. 2: {
  apply (permutation_rev_l monom_eqb_eq).
}
subst lc.
assert (Hil : i < length (rev la)) by (rewrite rev_length; flia Hjl Hi).
assert (Hfi : ∀ ma, ma ∈ skipn i (rev la) → mdeg ma = mdeg mb). {
  intros ma Hma.
  apply in_rev in Hma.
  now specialize (Hfj ma Hma).
}
clear j lb IHlb Hjl Hfj Hi Hmj.
remember (rev la) as lc eqn:Hlc.
clear la Hlc; rename lc into la.
rewrite <- (firstn_skipn i la) at 1.
rewrite <- (firstn_skipn i la) in Hil.
remember (firstn i la) as lc eqn:Hlc.
remember (skipn i la) as lb eqn:Hlb.
assert (Hbz : lb ≠ []). {
  intros H; move H at top; subst lb.
  symmetry in Hlb.
  apply List_eq_skipn_nil in Hlb.
  rewrite firstn_all2 in Hlc; [ | easy ].
  subst lc.
  rewrite app_nil_r in Hil.
  now apply Nat.nle_gt in Hil.
}
clear la i Hlb Hlc Hil.
rename lc into la.
move la after lb.
assert (Hla : mdeg (last la (Mon 0 (S (mdeg mb)))) ≠ mdeg mb). {
  destruct la as [| ma] using rev_ind; [ easy | ].
  rewrite rev_app_distr in Hc; cbn in Hc.
  now rewrite last_last.
}
clear Hc.
destruct mb as (cb, db).
cbn in Hcj, Hfi, Hla.
subst cb.
symmetry.
revert lb Hfi Hla Hbz.
induction la as [| ma]; intros. {
  do 2 rewrite app_nil_l; symmetry.
  clear Hla.
  induction lb as [| ma]; [ easy | clear Hbz ].
  rewrite rngl_summation_list_cons.
  cbn; rewrite fold_merge_same_deg.
  assert (H : ∀ ma, ma ∈ lb → mdeg ma = db). {
    intros mb Hma.
    now apply Hfi; right.
  }
  specialize (IHlb H); clear H.
  destruct lb as [| mb lb]. {
    cbn; rewrite rngl_summation_list_empty; [ | easy ].
    rewrite rngl_add_0_r.
    specialize (Hfi _ (or_introl eq_refl)).
    rewrite <- Hfi.
    now destruct ma.
  }
  assert (H : mb :: lb ≠ []) by easy.
  specialize (IHlb H); clear H.
  rewrite IHlb; cbn.
  rewrite Hfi; [ | now left ].
  now rewrite Nat.eqb_refl.
}
cbn.
do 2 rewrite fold_merge_same_deg.
rewrite <- IHla; [ | easy | | easy ]. 2: {
  destruct la as [| mb] using rev_ind; [ cbn; flia | ].
  rewrite List_cons_is_app, app_assoc in Hla.
  rewrite last_last in Hla.
  now rewrite last_last.
}
unfold same_deg_sum_coeff.
remember (merge_same_deg la) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| mc]; cbn. {
  apply eq_merge_same_deg_nil in Hlc; subst la; cbn.
  cbn in Hla.
  now apply Nat.eqb_neq in Hla; rewrite Hla.
}
now destruct (mdeg ma =? mdeg mc).
Qed.

Theorem merge_same_deg_app_idemp_l : ∀ (la lb : list (monom T)),
  merge_same_deg (la ++ lb) = merge_same_deg (merge_same_deg la ++ lb).
Proof.
intros.
rewrite <- (rev_involutive (la ++ lb)).
rewrite (merge_same_deg_rev (rev (la ++ lb))).
rewrite rev_app_distr.
rewrite merge_same_deg_app_idemp_r.
rewrite merge_same_deg_rev.
rewrite <- rev_app_distr.
rewrite merge_same_deg_rev.
apply rev_involutive.
Qed.

Theorem merge_same_deg_same_deg : ∀ da (la : list (monom T)),
  (∀ j, j < length la → mdeg (nth j la 0·) = da)
  → merge_same_deg la =
      match la with
      | [] => []
      | _ => [Mon (∑ (ma ∈ la), mcoeff ma) da]
      end.
Proof.
intros * Hdd.
revert da Hdd.
induction la as [| ma]; intros; [ easy | ].
cbn; rewrite fold_merge_same_deg.
unfold same_deg_sum_coeff.
rewrite (IHla da). 2: {
  intros j Hj.
  assert (H : S j < length (ma :: la)) by now cbn; flia Hj.
  now specialize (Hdd _ H); clear H.
}
destruct la as [| mb]. {
  f_equal.
  rewrite rngl_summation_list_only_one.
  rewrite <- Hdd with (j := 0); [ | cbn; flia ].
  now destruct ma.
}
cbn.
specialize (Hdd 0) as H1.
assert (H : 0 < length (ma :: mb :: la)) by now cbn; flia.
specialize (H1 H); clear H; cbn in H1.
rewrite H1, Nat.eqb_refl; symmetry.
now rewrite rngl_summation_list_cons.
Qed.

Theorem merge_same_deg_isort_app_comm : ∀ la lb : list (monom T),
  let rel := λ ma mb, mdeg mb <=? mdeg ma in
  merge_same_deg (isort rel (la ++ lb)) =
  merge_same_deg (isort rel (lb ++ la)).
Proof.
intros.
assert (Htot : total_relation rel). {
  unfold rel; intros ma mb.
  apply Nat_leb_total_relation.
}
assert (Href : reflexive rel). {
  unfold rel; intros a.
  apply Nat.leb_refl.
}
assert (Htra : transitive rel). {
  unfold rel; intros a b c Hab Hbc.
  apply Nat.leb_le in Hab, Hbc.
  apply Nat.leb_le.
  now transitivity (mdeg b).
}
remember (isort rel (la ++ lb)) as lab eqn:Hlab; symmetry in Hlab.
remember (isort rel (lb ++ la)) as lba eqn:Hlba; symmetry in Hlba.
move lba before lab.
specialize (sorted_sorted_permuted_not_antisym monom_eqb_eq Href Htra) as Hrr.
specialize (Hrr (Mon 0 0) lab lba).
assert (Hsab : sorted rel lab) by now rewrite <- Hlab; apply sorted_isort.
specialize (Hrr Hsab).
assert (Hsba : sorted rel lba) by now rewrite <- Hlba; apply sorted_isort.
specialize (Hrr Hsba).
assert (Hpab : permutation monom_eqb lab lba). {
  rewrite <- Hlab, <- Hlba.
  apply (permutation_trans monom_eqb_eq) with (lb := lb ++ la). 2: {
    apply permuted_isort, monom_eqb_eq.
  }
  apply (permutation_trans monom_eqb_eq) with (lb := la ++ lb). {
    apply (permutation_sym monom_eqb_eq).
    apply permuted_isort, monom_eqb_eq.
  }
  apply (permutation_app_comm monom_eqb_eq).
}
specialize (Hrr Hpab).
unfold rel in Hrr.
assert (Hdd : ∀ i, mdeg (nth i lab (0·)) = mdeg (nth i lba (0·))). {
  intros i.
  specialize (Hrr i).
  destruct Hrr as (H1, H2).
  apply Nat.leb_le in H1, H2.
  now apply Nat.le_antisymm.
}
clear Hrr.
clear Hlab Hlba.
clear la lb.
rename lab into la.
rename lba into lb.
rename Hsab into Hsa.
rename Hsba into Hsb.
(**)
remember (length la) as len eqn:Hlena; symmetry in Hlena.
assert (Hlenb : length lb = len). {
  apply permutation_length in Hpab; congruence.
}
revert la lb Hsa Hsb Hpab Hdd Hlena Hlenb.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct len. {
  now apply length_zero_iff_nil in Hlena, Hlenb; subst la lb.
}
remember (List_rank (λ mb, mdeg mb ≠? mdeg (hd (Mon 0 0) la)) la) as n eqn:Hn.
assert (Hpf : permutation monom_eqb (firstn n la) (firstn n lb)). {
  clear - Heq Hn Hlena Hlenb Hpab Hdd Hsa.
  rewrite <- Hlenb in Hlena; clear Hlenb.
  symmetry in Hn.
  apply (List_rank_if (Mon 0 0)) in Hn.
  destruct Hn as (Hbn, Hnl).
  destruct Hnl as [Hnl| Hnl]. 2: {
    rewrite Hnl at 1.
    rewrite Hlena in Hnl.
    rewrite Hnl.
    now do 2 rewrite firstn_all.
  }
  destruct Hnl as (Hnl, Haa).
  apply (permutation_firstn (0·) monom_eqb_eq) with
      (P := λ ma, mdeg ma = mdeg (hd (0·) la)); [ | | easy ]. {
    intros i Hi.
    specialize (Hbn _ Hi) as H1.
    apply Bool.negb_false_iff in H1.
    apply Nat.eqb_eq in H1.
    split; [ easy | ].
    now rewrite <- Hdd, H1.
  } {
    intros i Hi.
    apply Bool.negb_true_iff in Haa.
    apply Nat.eqb_neq in Haa.
    rewrite <- Hdd.
    clear - Haa Hsa Hi rel.
    enough (H : mdeg (nth i la (0·)) ≠ mdeg (hd (0·) la)) by easy.
    intros Hiz; apply Haa; clear Haa.
    (* lemma, here, perhaps? *)
    destruct la as [| ma]; [ now destruct n | ].
    cbn - [ nth ] in Hiz |-*.
    destruct n; [ easy | cbn ].
    destruct i; [ easy | cbn in Hi, Hiz ].
    assert (H : n ≤ i < length la) by flia Hi.
    clear Hi; rename H into Hi.
    destruct Hi as (Hni, Hia).
    (* or statring the lemma here... *)
    assert (Htra : transitive rel). {
      unfold rel; intros a b c Hab Hbc.
      apply Nat.leb_le in Hab, Hbc.
      apply Nat.leb_le.
      now transitivity (mdeg b).
    }
    apply (sorted_cons_iff Htra) in Hsa.
    destruct Hsa as (Hsa, Hba).
    assert (H : ∀ mb, mb ∈ la → mdeg mb ≤ mdeg ma). {
      intros mb Hmb.
      specialize (Hba _ Hmb).
      now apply Nat.leb_le in Hba.
    }
    move H before Hba; clear Hba.
    rename H into Hba.
    revert la i Hsa Hba Hiz Hni Hia.
    induction n; intros. {
      destruct i; [ easy | ].
      destruct la as [| mb]; [ easy | ].
      cbn in Hia |-*; apply Nat.succ_lt_mono in Hia.
      cbn in Hiz.
      specialize (Hba _ (or_introl eq_refl)) as H1.
      apply (sorted_cons_iff Htra) in Hsa.
      destruct Hsa as (Hsa, Hb'a).
      specialize (Hb'a (nth i la (0·))) as H2.
      assert (H : nth i la (0·) ∈ la) by now apply nth_In.
      specialize (H2 H); clear H.
      apply Nat.leb_le in H2.
      rewrite Hiz in H2.
      now apply Nat.le_antisymm.
    }
    destruct i; [ easy | ].
    destruct la as [| mb]; [ easy | ].
    cbn in Hiz, Hia |-*; apply Nat.succ_lt_mono in Hia.
    apply Nat.succ_le_mono in Hni.
    apply sorted_cons in Hsa.
    apply IHn with (i := i); [ easy | | easy | easy | easy ].
    intros mc Hmc.
    now apply Hba; right.
  }
}
assert (Hps : permutation monom_eqb (skipn n la) (skipn n lb)). {
  rewrite <- (firstn_skipn n la) in Hpab.
  rewrite <- (firstn_skipn n lb) in Hpab.
  apply permutation_app_permutation_l with (la := firstn n la) in Hpab;
    [ easy | apply monom_eqb_eq | easy ].
}
symmetry in Hn.
apply (List_rank_if (Mon 0 0)) in Hn.
destruct Hn as (Hbn, Hnl).
assert (H : ∀ j, j < n → mdeg (nth j la (0·)) = mdeg (hd (0·) la)). {
  intros j Hj.
  specialize (Hbn _ Hj).
  apply Bool.negb_false_iff in Hbn.
  now apply Nat.eqb_eq in Hbn.
}
move H before Hbn; clear Hbn; rename H into Hbn.
destruct Hnl as [(Hnl, Hdab)| Hnl]. {
  apply Bool.negb_true_iff in Hdab.
  apply Nat.eqb_neq in Hdab.
  assert (H1 : merge_same_deg (firstn n la) = merge_same_deg (firstn n lb)). {
    apply (IHlen n); [ congruence | | | easy | | | ]. {
      clear lb len Hdab Hpf Hsb Hpab Hdd Hlenb IHlen Hlena Hps.
      revert n Hbn Hnl.
      induction la as [| ma]; intros; [ easy | ].
      assert (H : sorted rel la) by now apply sorted_cons in Hsa.
      specialize (IHla H); clear H.
      destruct n; [ easy | ].
      cbn in Hnl; apply Nat.succ_lt_mono in Hnl.
      specialize (IHla n); cbn.
      apply (sorted_cons_iff Htra) in Hsa.
      apply (sorted_cons_iff Htra).
      destruct Hsa as (Hsa, Hsb).
      split. {
        rewrite <- (firstn_skipn n) in Hsa.
        now apply (sorted_app_iff Htra) in Hsa.
      }
      intros mb Hma.
      apply Hsb.
      rewrite <- (firstn_skipn n).
      now apply in_or_app; left.
    } {
      rewrite Hlena, <- Hlenb in Hnl.
      assert (Hbn' : ∀ j, j < n → (mdeg (nth j lb (0·)) = mdeg (hd (0·) lb))). {
        intros j Hj.
        rewrite <- Hdd.
        rewrite List_hd_nth_0, <- Hdd, <- List_hd_nth_0.
        now apply Hbn.
      }
      clear la len IHlen Hsa Hpab Hdd Hlena Hlenb Hbn Hdab Hpf Hps.
      rename Hbn' into Hbn.
      revert n Hbn Hnl.
      induction lb as [| mb]; intros; [ easy | ].
      assert (H : sorted rel lb) by now apply sorted_cons in Hsb.
      specialize (IHlb H); clear H.
      destruct n; [ easy | ].
      cbn in Hnl; apply Nat.succ_lt_mono in Hnl.
      specialize (IHlb n); cbn.
      apply (sorted_cons_iff Htra) in Hsb.
      apply (sorted_cons_iff Htra).
      destruct Hsb as (Hsb, Hsbb).
      split. {
        rewrite <- (firstn_skipn n) in Hsb.
        now apply (sorted_app_iff Htra) in Hsb.
      }
      intros ma Hma.
      apply Hsbb.
      rewrite <- (firstn_skipn n).
      now apply in_or_app; left.
    } {
      intros i.
      destruct (lt_dec i n) as [Hin| Hin]. 2: {
        apply Nat.nlt_ge in Hin.
        rewrite nth_overflow. 2: {
          rewrite firstn_length, min_l; [ easy | ].
          now apply Nat.lt_le_incl.
        }
        rewrite nth_overflow. 2: {
          rewrite firstn_length, min_l; [ easy | ].
          rewrite Hlenb, <- Hlena.
          now apply Nat.lt_le_incl.
        }
        easy.
      }
      rewrite List_nth_firstn; [ | easy ].
      rewrite List_nth_firstn; [ | easy ].
      apply Hdd.
    } {
      rewrite firstn_length.
      apply min_l.
      now apply Nat.lt_le_incl.
    } {
      rewrite firstn_length.
      apply min_l.
      now rewrite Hlenb, <- Hlena; apply Nat.lt_le_incl.
    }
  }
  assert (H2 : merge_same_deg (skipn n la) = merge_same_deg (skipn n lb)). {
    destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
      subst n; cbn.
      now rewrite List_hd_nth_0 in Hdab.
    }
    apply (IHlen (length la - n)); [ | | | easy | | | ]. {
      rewrite Hlena; flia Hnz.
    } {
      rewrite <- (firstn_skipn n) in Hsa.
      now apply (sorted_app_iff Htra) in Hsa.
    } {
      rewrite <- (firstn_skipn n) in Hsb.
      now apply (sorted_app_iff Htra) in Hsb.
    } {
      intros i.
      do 2 rewrite List_nth_skipn.
      apply Hdd.
    } {
      now rewrite skipn_length.
    } {
      now rewrite skipn_length, Hlena, <- Hlenb.
    }
  }
  rewrite <- (firstn_skipn n la).
  rewrite <- (firstn_skipn n lb).
  rewrite merge_same_deg_app_idemp_r, H2.
  rewrite <- merge_same_deg_app_idemp_r.
  rewrite merge_same_deg_app_idemp_l, H1.
  rewrite <- merge_same_deg_app_idemp_l.
  easy.
}
clear Hpf Hps; subst n.
clear len IHlen Hlenb Hlena.
clear Hsa Hsb.
remember (mdeg (hd (Mon 0 0) la)) as da; clear Heqda.
move da before lb.
clear rel Htot Href Htra.
rewrite merge_same_deg_same_deg with (da := da); [ | easy ].
rewrite merge_same_deg_same_deg with (da := da). 2: {
  intros; rewrite <- Hdd; apply Hbn.
  apply permutation_length in Hpab; congruence.
}
destruct la as [| ma]. {
  destruct lb; [ easy | ].
  now apply permutation_nil_l in Hpab.
}
destruct lb as [| mb]. {
  now apply permutation_nil_r in Hpab.
}
f_equal; f_equal.
now apply (rngl_summation_list_permut _ monom_eqb_eq).
Qed.

Theorem monl_norm_add_comm : ∀ (la lb : list (monom T)),
  monl_norm (monl_add la lb) = monl_norm (monl_add lb la).
Proof.
intros.
unfold monl_add, monl_norm.
f_equal.
apply merge_same_deg_isort_app_comm.
Qed.

Theorem canon_polyn_add_comm : ∀ a b : canon_polyn T, (a + b)%F = (b + a)%F.
Proof.
intros; cbn.
destruct a as (pa, ppa).
destruct b as (pb, ppb).
move pb before pa.
apply canon_polyn_eq_eq; cbn.
unfold polyn_add, polyn_norm.
cbn - [ merge_same_deg ].
f_equal.
apply monl_norm_add_comm.
Qed.

Theorem canon_monl_is_filter_deg_non_zero : ∀ (P : list (monom T)),
  is_canon_monl P = true
  → P = filter (λ ma, (mcoeff ma ≠? 0)%F) P.
Proof.
intros * PP.
unfold is_canon_monl in PP.
apply Bool.andb_true_iff in PP.
destruct PP as (Hps & Hpc).
specialize (proj2 (all_true_and_list_true_iff _ _ _) Hpc) as H1.
cbn in H1.
clear Hpc Hps.
induction P as [| ma la]; [ easy | cbn ].
rewrite H1; [ f_equal | now left ].
apply IHla.
intros mb Hmb.
now apply H1; right.
Qed.

Theorem merge_same_deg_cons_filter_cons : ∀ (P Q R : list (monom T)) m m',
  let rel := λ ma mb, mdeg mb <=? mdeg ma in
  let f := λ ma, (mcoeff ma ≠? 0)%F in
  sorted rel P
  → merge_same_deg P = m :: Q
  → filter f Q = m' :: R
  → mdeg m' < mdeg m.
Proof.
intros * Hs Hlc Hcb.
specialize (sorted_le_sorted_lt_merge_same_deg Hs) as H1.
set (rel' := λ ma mb, mdeg mb <? mdeg ma) in H1.
move rel' before rel.
assert (Htra' : transitive rel'). {
  unfold rel; intros a b c Hab Hbc.
  apply Nat.ltb_lt in Hab, Hbc.
  apply Nat.ltb_lt.
  now transitivity (mdeg b).
}
move Htra' before f.
rewrite Hlc in H1.
apply sorted_cons_iff in H1; [ | easy ].
destruct H1 as (Hsq & Hdd).
unfold rel' in Hdd.
assert (H : m' ∈ Q). {
  assert (H : m' ∈ filter f Q) by now rewrite Hcb; left.
  now apply filter_In in H.
}
specialize (Hdd _ H).
now apply Nat.ltb_lt in Hdd.
Qed.

Theorem filter_merge_filter : ∀ P : list (monom T),
  let rel := λ ma mb, mdeg mb <=? mdeg ma in
  let f := λ ma, (mcoeff ma ≠? 0)%F in
  sorted rel P
  → filter f (merge_same_deg (filter f P)) = filter f (merge_same_deg P).
Proof.
intros * Hs.
assert (Htra : transitive rel). {
  unfold rel; intros a b c Hab Hbc.
  apply Nat.leb_le in Hab, Hbc.
  apply Nat.leb_le.
  now transitivity (mdeg b).
}
induction P as [| ma la]; [ easy | cbn ].
assert (H : sorted rel la) by now apply sorted_cons in Hs.
specialize (IHla H); clear H.
do 2 rewrite fold_merge_same_deg.
remember (f ma) as fa eqn:Hfa; symmetry in Hfa.
destruct fa. {
  cbn; rewrite fold_merge_same_deg.
  unfold same_deg_sum_coeff.
  remember (merge_same_deg (filter f la)) as lb eqn:Hlb; symmetry in Hlb.
  remember (merge_same_deg la) as lc eqn:Hlc; symmetry in Hlc.
  destruct lb as [| mb]. {
    cbn; rewrite Hfa.
    destruct lc as [| mc]; [ now cbn; rewrite Hfa | ].
    cbn in IHla; symmetry in IHla.
    remember (f mc) as fc eqn:Hfc; symmetry in Hfc.
    destruct fc; [ easy | cbn ].
    rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec (mdeg ma) (mdeg mc)) as [Hac| Hac]. {
      unfold f in Hfc, Hfa.
      apply Bool.negb_false_iff in Hfc.
      apply (rngl_eqb_eq Heq) in Hfc.
      rewrite Hfc, rngl_add_0_r.
      cbn; rewrite IHla.
      unfold f; cbn.
      rewrite Hfa.
      now destruct ma.
    }
    now cbn; rewrite Hfa, Hfc, IHla.
  }
  cbn in IHla.
  remember (f mb) as fb eqn:Hfb; symmetry in Hfb.
  destruct fb. {
    destruct lc as [| mc]; [ easy | ].
    cbn in IHla.
    remember (f mc) as fc eqn:Hfc; symmetry in Hfc.
    destruct fc. {
      injection IHla; clear IHla; intros H1 H2; subst mc.
      do 2 rewrite if_eqb_eq_dec.
      destruct (Nat.eq_dec (mdeg ma) (mdeg mb)) as [Hab| Hab]. {
        now cbn; rewrite <- H1.
      }
      now cbn; rewrite <- H1.
    }
    generalize Hfc; intros H.
    unfold f in H; cbn in H.
    apply Bool.negb_false_iff in H.
    apply (rngl_eqb_eq Heq) in H.
    rewrite H, rngl_add_0_r; clear H.
    do 2 rewrite if_eqb_eq_dec.
    symmetry in IHla.
    assert (Hac' : mdeg mc ≤ mdeg ma). {
      apply (sorted_cons_iff Htra) in Hs.
      destruct Hs as (Hs, Hra).
      assert (H : mc ∈ merge_same_deg la) by now rewrite Hlc; left.
      apply in_merge_same_deg in H.
      apply in_map_iff in H.
      destruct H as (md & Hmd & Hmda).
      apply Hra in Hmda.
      unfold rel in Hmda.
      apply Nat.leb_le in Hmda.
      now rewrite Hmd in Hmda.
    }
    generalize Hs; intros H.
    apply sorted_cons in H.
    specialize (merge_same_deg_cons_filter_cons H Hlc IHla) as H1.
    clear H.
    destruct (Nat.eq_dec (mdeg ma) (mdeg mb)) as [Hab| Hab]. {
      flia Hac' H1 Hab.
    }
    destruct (Nat.eq_dec (mdeg ma) (mdeg mc)) as [Hac| Hac]. {
      cbn; rewrite Hfa, Hfb.
      unfold f at 2; cbn.
      unfold f in Hfa; cbn in Hfa.
      rewrite Hfa.
      rewrite IHla.
      now destruct ma.
    }
    now cbn; rewrite Hfa, Hfb, Hfc, IHla.
  } {
    destruct lc as [| mc]. {
      now apply eq_merge_same_deg_nil in Hlc; subst la.
    }
    assert (Hac' : mdeg mc ≤ mdeg ma). {
      apply (sorted_cons_iff Htra) in Hs.
      destruct Hs as (Hs, Hra).
      assert (H : mc ∈ merge_same_deg la) by now rewrite Hlc; left.
      apply in_merge_same_deg in H.
      apply in_map_iff in H.
      destruct H as (md & Hmd & Hmda).
      apply Hra in Hmda.
      unfold rel in Hmda.
      apply Nat.leb_le in Hmda.
      now rewrite Hmd in Hmda.
    }
    generalize Hfb; intros H.
    unfold f in H; cbn in H.
    apply Bool.negb_false_iff in H.
    apply (rngl_eqb_eq Heq) in H.
    rewrite H, rngl_add_0_r; clear H.
    do 2 rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec (mdeg ma) (mdeg mb)) as [Hdab| Hdab]. {
      destruct (Nat.eq_dec (mdeg ma) (mdeg mc)) as [Hdac| Hdac]. {
        cbn; rewrite IHla; cbn.
        remember (f mc) as fc eqn:Hfc; symmetry in Hfc.
        destruct fc. 2: {
          generalize Hfc; intros H.
          unfold f in H; cbn in H.
          apply Bool.negb_false_iff in H.
          apply (rngl_eqb_eq Heq) in H.
          now rewrite H, rngl_add_0_r; clear H.
        }
        exfalso.
        clear Hac'.
        cbn in IHla; rewrite Hfc in IHla.
        assert (H : sorted rel (filter f la)). {
          apply sorted_cons in Hs.
          now apply (sorted_filter Htra).
        }
        specialize (merge_same_deg_cons_filter_cons H Hlb IHla) as H1.
        rewrite <- Hdab, Hdac in H1.
        now apply Nat.lt_irrefl in H1.
      }
      cbn; rewrite Hfa.
      unfold f at 1; cbn.
      generalize Hfa; intros H.
      unfold f in H; rewrite H; clear H.
      f_equal; [ now destruct ma | easy ].
    } {
      destruct (Nat.eq_dec (mdeg ma) (mdeg mc)) as [Hdac| Hdac]. {
        cbn; rewrite Hfa, Hfb.
        unfold f at 2; cbn.
        cbn in IHla.
        remember (f mc) as fc eqn:Hfc; symmetry in Hfc.
        destruct fc. 2: {
          generalize Hfc; intros H.
          unfold f in H.
          apply Bool.negb_false_iff in H.
          apply (rngl_eqb_eq Heq) in H.
          rewrite H, rngl_add_0_r.
          unfold f in Hfa; rewrite Hfa.
          f_equal; [ now destruct ma | easy ].
        }
        exfalso.
        clear Hac'.
        assert (H : sorted rel (filter f la)). {
          apply sorted_cons in Hs.
          now apply (sorted_filter Htra).
        }
        specialize (merge_same_deg_cons_filter_cons H Hlb IHla) as H1.
        clear H.
        rewrite <- Hdac in H1.
        clear - rp Htra Hs Hlb H1.
        assert (H : mb ∈ mb :: lb) by now left.
        rewrite <- Hlb in H.
        specialize (in_merge_same_deg _ _ H) as H2; clear H.
        apply in_map_iff in H2.
        destruct H2 as (mc & Hmc & Hmca).
        apply filter_In in Hmca.
        destruct Hmca as (Hmca & Hfc).
        apply (sorted_cons_iff Htra) in Hs.
        destruct Hs as (Hs, Hma).
        specialize (Hma _ Hmca).
        unfold rel in Hma.
        apply Nat.leb_le, Nat.nlt_ge in Hma.
        now rewrite Hmc in Hma.
      } {
        now cbn; rewrite Hfa, Hfb; f_equal.
      }
    }
  }
}
rewrite IHla.
unfold same_deg_sum_coeff.
remember (merge_same_deg la) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| mb]; cbn; [ now rewrite Hfa | ].
cbn in IHla.
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec _ _) as [Hab| Hab]; cbn; [ | now rewrite Hfa ].
generalize Hfa; intros H.
unfold f in H.
apply Bool.negb_false_iff in H.
apply (rngl_eqb_eq Heq) in H.
rewrite H, rngl_add_0_l, Hab; clear H.
unfold f at 1 4; cbn.
now destruct mb.
Qed.

Theorem sorted_summation_filter_merge_coeff : ∀ (P : list (monom T)) d,
  let rel := λ ma mb, mdeg mb <=? mdeg ma in
  let f := λ m, mdeg m =? d in
  sorted rel P
  → ∑ (m ∈ filter f (merge_same_deg P)), mcoeff m =
    ∑ (m ∈ filter f P), mcoeff m.
Proof.
intros * Hs.
induction P as [| ma la]; [ easy | cbn ].
assert (H : sorted rel la) by now apply sorted_cons in Hs.
specialize (IHla H); clear H.
rewrite fold_merge_same_deg.
unfold same_deg_sum_coeff.
remember (merge_same_deg la) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| mb]. {
  now cbn; apply eq_merge_same_deg_nil in Hlb; subst la.
}
rewrite if_eqb_eq_dec.
destruct (Nat.eq_dec _ _) as [Hdab| Hdab]. {
  cbn.
  unfold f at 3.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec _ _) as [Had| Had]. {
    do 2 rewrite rngl_summation_list_cons; cbn.
    rewrite <- rngl_add_assoc; f_equal.
    cbn in IHla.
    remember (f mb) as fb eqn:Hfb; symmetry in Hfb.
    destruct fb. {
      rewrite rngl_summation_list_cons in IHla.
      apply IHla.
    }
    unfold f in Hfb.
    apply Nat.eqb_neq in Hfb.
    now rewrite <- Hdab in Hfb.
  } {
    cbn in IHla.
    remember (f mb) as fb eqn:Hfb; symmetry in Hfb.
    destruct fb; [ | easy ].
    unfold f in Hfb.
    apply Nat.eqb_eq in Hfb.
    now rewrite <- Hdab in Hfb.
  }
}
rewrite <- Hlb; cbn; rewrite Hlb.
remember (f ma) as fa eqn:Hfa; symmetry in Hfa.
destruct fa; [ | easy ].
do 2 rewrite rngl_summation_list_cons.
now f_equal.
Qed.

Theorem summation_filter_merge_isort_coeff : ∀ (P : list (monom T)) d,
  let rel := λ ma mb, mdeg mb <=? mdeg ma in
  let f := λ m, mdeg m =? d in
  ∑ (m ∈ filter f (merge_same_deg (isort rel P))), mcoeff m =
  ∑ (m ∈ filter f P), mcoeff m.
Proof.
intros.
transitivity (∑ (m ∈ filter f (isort rel P)), mcoeff m). 2: {
  apply (rngl_summation_list_permut _ monom_eqb_eq).
  apply (permutation_filter monom_eqb_eq).
  apply (permutation_sym monom_eqb_eq).
  apply (permuted_isort _ monom_eqb_eq).
}
apply sorted_summation_filter_merge_coeff.
fold rel.
apply sorted_isort.
unfold rel; intros ma mb.
apply Nat_leb_total_relation.
Qed.

Theorem summation_filter_merge_isort_app : ∀ (P Q : list (monom T)) d,
  let rel := λ ma mb, mdeg mb <=? mdeg ma in
  let f := λ m, mdeg m =? d in
  ∑ (m ∈ filter f (merge_same_deg (isort rel (P ++ Q)))), mcoeff m =
  (∑ (m ∈ filter f P), mcoeff m + ∑ (m ∈ filter f Q), mcoeff m)%F.
Proof.
intros.
rewrite <- rngl_summation_list_app.
rewrite <- filter_app.
apply summation_filter_merge_isort_coeff.
Qed.

Theorem canon_polyn_merge_isort_merge_isort_swap : ∀ P Q R : list (monom T),
  is_canon_monl P = true
  → is_canon_monl Q = true
  → is_canon_monl R = true
  → let rel := λ ma mb, mdeg mb <=? mdeg ma in
    merge_same_deg (isort rel (merge_same_deg (isort rel (P ++ Q)) ++ R)) =
    merge_same_deg (isort rel (merge_same_deg (isort rel (P ++ R)) ++ Q)).
Proof.
intros * PP PQ PR.
set (rel := λ ma mb, mdeg mb <=? mdeg ma); cbn.
set (MS := λ l, merge_same_deg (isort rel l)).
fold (MS (P ++ Q)).
fold (MS (P ++ R)).
fold (MS (MS (P ++ Q) ++ R)).
fold (MS (MS (P ++ R) ++ Q)).
specialize summation_filter_merge_isort_app as H1.
cbn in H1.
fold rel in H1.
set (f := λ d (m : monom T), mdeg m =? d).
assert
  (H : ∀ P Q d,
     ∑ (m ∈ filter (f d) (MS (P ++ Q))), mcoeff m =
     (∑ (m ∈ filter (f d) P), mcoeff m +
      ∑ (m ∈ filter (f d) Q), mcoeff m)%F). {
  intros.
  apply H1.
}
clear H1; rename H into H1.
...

Theorem canon_polyn_add_add_swap :
  ∀ a b c : canon_polyn T, (a + b + c)%F = (a + c + b)%F.
Proof.
intros P Q R; cbn.
apply canon_polyn_eq_eq; cbn.
unfold polyn_norm; f_equal; cbn.
do 4 rewrite fold_merge_same_deg.
set (rel := λ ma mb : monom T, mdeg mb <=? mdeg ma).
set (f := λ ma, (mcoeff ma ≠? 0)%F).
assert (Htra : transitive rel). {
  unfold rel; intros a b c Hab Hbc.
  apply Nat.leb_le in Hab, Hbc.
  apply Nat.leb_le.
  now transitivity (mdeg b).
}
assert (Htot : total_relation rel). {
  unfold rel; intros ma mb.
  apply Nat_leb_total_relation.
}
destruct P as ((P), PP).
destruct Q as ((Q), PQ).
destruct R as ((R), PR); cbn.
move Q before P; move R before Q.
unfold is_canon_polyn in PP, PQ, PR.
cbn in PP, PQ, PR.
do 4 rewrite fold_merge_same_deg.
rewrite (canon_monl_is_filter_deg_non_zero R PR) at 1; symmetry.
rewrite (canon_monl_is_filter_deg_non_zero Q PQ) at 1; symmetry.
fold f.
do 2 rewrite <- filter_app.
do 2 rewrite (sorted_isort_filter Htra Htot).
rewrite filter_merge_filter; [ | now fold rel; apply sorted_isort ].
rewrite filter_merge_filter; [ | now fold rel; apply sorted_isort ].
f_equal; clear f.
... ...
now apply canon_polyn_merge_isort_merge_isort_swap.
...
apply List_eq_iff.
split. {
Search (length (merge_same_deg _)).
....
revert Q R PQ PR.
induction P as [| ma la]; intros; cbn. {
  do 4 rewrite fold_merge_same_deg.
  rewrite merge_same_deg_isort_app_comm.
  fold rel.
Search (isort _ (_ ++ _)).
...
Fixpoint merge_app_monl_loop it (P Q : list (monom T)) :=
  match it with
  | 0 => [Mon 0 99] (* algo error: not enough iterations *)
  | S it' =>
      match P with
      | [] => Q
      | ma :: la =>
          match Q with
          | [] => P
          | mb :: lb =>
              if mdeg mb <=? mdeg ma then ma :: merge_app_monl_loop it' la Q
              else mb :: merge_app_monl_loop it' P lb
          end
      end
  end.
Definition merge_app_monl_nb_iter (la lb : list (monom T)) :=
  S (length la + length lb).
Definition merge_app_monl la lb :=
  merge_app_monl_loop (merge_app_monl_nb_iter la lb) la lb.
Theorem isort_merge_app_monl : ∀ P Q : list (monom T),
  let rel := λ ma mb : monom T, mdeg mb <=? mdeg ma in
  is_canon_monl P = true
  → is_canon_monl Q = true
  → isort rel (P ++ Q) = merge_app_monl P Q.
Proof.
intros * HP HQ.
assert (Htra : transitive rel). {
  unfold rel; intros a b c Hab Hbc.
  apply Nat.leb_le in Hab, Hbc.
  apply Nat.leb_le.
  now transitivity (mdeg b).
}
assert (Htot : total_relation rel). {
  unfold rel; intros ma mb.
  apply Nat_leb_total_relation.
}
assert (Htral : transitive (λ x y : monom T, mdeg y <? mdeg x)). {
  intros a b c Hab Hbc.
  apply Nat.ltb_lt in Hab, Hbc.
  apply Nat.ltb_lt.
  now transitivity (mdeg b).
}
unfold merge_app_monl.
remember (merge_app_monl_nb_iter P Q) as it.
assert (Hit : merge_app_monl_nb_iter P Q ≤ it) by flia Heqit.
clear Heqit.
unfold merge_app_monl_nb_iter in Hit.
revert P Q HP HQ Hit.
induction it; intros; [ easy | cbn ].
destruct P as [| ma]. {
  cbn.
  unfold is_canon_monl in HQ.
  apply Bool.andb_true_iff in HQ.
  destruct HQ as (Hsq, Hcq).
  apply isort_when_sorted.
  rewrite fold_sorted in Hsq.
  now apply sorted_lt_sorted_le_mdeg.
}
cbn in Hit.
apply Nat.succ_le_mono in Hit.
destruct Q as [| mb]. {
  rewrite app_nil_r.
  unfold is_canon_monl in HP.
  apply Bool.andb_true_iff in HP.
  destruct HP as (Hsp, Hcp).
  destruct ma.
  apply isort_when_sorted.
  rewrite fold_sorted in Hsp.
  now apply sorted_lt_sorted_le_mdeg.
}
rewrite if_leb_le_dec.
cbn in Hit.
destruct (le_dec (mdeg mb) (mdeg ma)) as [Hba| Hba]. {
  rewrite <- IHit; [ | | easy | cbn; flia Hit ]. 2: {
    unfold is_canon_monl in HP |-*.
    apply Bool.andb_true_iff in HP.
    apply Bool.andb_true_iff.
    destruct HP as (Hsp, Hcp).
    split; [ now apply sorted_cons in Hsp | ].
    rewrite and_list_cons in Hcp.
    now apply Bool.andb_true_iff in Hcp.
  }
  cbn.
  remember (isort rel (P ++ mb :: Q)) as la eqn:Hla.
  assert (H1 : ∀ mx, mx ∈ la → mdeg mx ≤ mdeg ma). {
    intros mx Hmx.
    subst la.
    apply in_isort in Hmx.
    apply in_app_or in Hmx.
    destruct Hmx as [Hmx| [Hmx| Hmx]]. {
      unfold is_canon_monl in HP.
      apply Bool.andb_true_iff in HP.
      destruct HP as (Hs & Hap).
      apply (sorted_cons_iff Htral) in Hs.
      destruct Hs as (Hs & Hp).
      cbn in Hp.
      specialize (Hp _ Hmx) as H1.
      apply Nat.ltb_lt in H1.
      now apply Nat.lt_le_incl.
    } {
      now subst mx; cbn.
    } {
      unfold is_canon_monl in HQ.
      apply Bool.andb_true_iff in HQ.
      destruct HQ as (Hs & Hap).
      apply (sorted_cons_iff Htral) in Hs.
      destruct Hs as (Hs & Hp).
      cbn in Hp.
      specialize (Hp _ Hmx) as H2.
      apply Nat.ltb_lt in H2.
      transitivity (mdeg mb); [ | easy ].
      now apply Nat.lt_le_incl.
    }
  }
  destruct la as [| mc]; [ easy | cbn ].
  unfold rel at 1; cbn.
  specialize (H1 _ (or_introl eq_refl)) as H2.
  apply Nat.leb_le in H2.
  now rewrite H2.
} {
  apply Nat.nle_gt in Hba.
  rewrite <- IHit; [ | easy | | cbn; flia Hit ]. 2: {
    unfold is_canon_monl in HQ |-*.
    apply Bool.andb_true_iff in HQ.
    apply Bool.andb_true_iff.
    destruct HQ as (Hsp, Hcp).
    split; [ now apply sorted_cons in Hsp | ].
    rewrite and_list_cons in Hcp.
    now apply Bool.andb_true_iff in Hcp.
  }
  cbn.
  remember (isort rel (P ++ mb :: Q)) as la eqn:Hla.
  assert (H1 : ∀ mx, mx ∈ la → mdeg mx ≤ mdeg mb). {
    intros mx Hmx.
    subst la.
    apply in_isort in Hmx.
    apply in_app_or in Hmx.
    destruct Hmx as [Hmx| [Hmx| Hmx]]. {
      unfold is_canon_monl in HP.
      apply Bool.andb_true_iff in HP.
      destruct HP as (Hs & Hap).
      apply (sorted_cons_iff Htral) in Hs.
      destruct Hs as (Hs & Hp).
      cbn in Hp.
      specialize (Hp _ Hmx) as H1.
      apply Nat.ltb_lt in H1.
      apply Nat.lt_le_incl.
      now transitivity (mdeg ma).
    } {
      now subst mx; cbn.
    } {
      unfold is_canon_monl in HQ.
      apply Bool.andb_true_iff in HQ.
      destruct HQ as (Hs & Hap).
      apply (sorted_cons_iff Htral) in Hs.
      destruct Hs as (Hs & Hp).
      cbn in Hp.
      specialize (Hp _ Hmx) as H2.
      apply Nat.ltb_lt in H2.
      now apply Nat.lt_le_incl.
    }
  }
  destruct la as [| mc]. {
    symmetry in Hla; apply eq_isort_nil in Hla.
    now destruct P.
  }
  unfold rel at 1; cbn.
  specialize (H1 _ (or_introl eq_refl)) as H2.
  rewrite if_leb_le_dec.
  move mb before ma; move mc before mb.
  destruct (le_dec (mdeg mc) (mdeg ma)) as [Hca| Hca]. 2: {
    apply Nat.nle_gt in Hca.
    fold rel.
    destruct P as [| md]. {
      cbn - [ isort ] in Hla.
      rewrite isort_when_sorted in Hla. 2: {
        apply Bool.andb_true_iff in HQ.
        destruct HQ as (Hsq, Hcq).
        now apply sorted_lt_sorted_le_mdeg.
      }
      injection Hla; clear Hla; intros; subst mc la.
      f_equal; cbn.
      rewrite isort_when_sorted; [ easy | ].
      apply Bool.andb_true_iff in HQ.
      destruct HQ as (Hsq, Hcq).
      rewrite fold_sorted in Hsq.
      apply sorted_lt_sorted_le_mdeg in Hsq.
      fold rel in Hsq.
      now apply (sorted_cons_iff Htra) in Hsq.
    }
    assert (Hdb : mdeg md < mdeg mb). {
      apply (le_lt_trans _ (mdeg ma)); [ | easy ].
      apply Bool.andb_true_iff in HP.
      destruct HP as (Hsp, Hcp).
      cbn in Hsp.
      apply Nat.lt_le_incl, Nat.ltb_lt.
      now apply Bool.andb_true_iff in Hsp.
    }
    cbn in Hla.
    destruct P as [| me]. {
      cbn in Hla.
      do 2 rewrite fold_isort in Hla.
      cbn - [ isort ].
      rewrite fold_isort.
(* c'est pas clair, mon affaire *)
...
Theorem isort_cons_cons_swap : ∀ A (rel : A → _),
  antisymmetric rel →
  ∀ a b l,
  rel a b = true
  → isort rel (a :: b :: l) = isort rel (b :: a :: l).
Proof.
intros * Hant * Hab.
revert a b Hab.
induction l as [| c]; intros. {
  cbn; rewrite Hab.
  apply Hant in Hab.
  destruct (rel b a); [ | easy ].
  now rewrite Hab.
}
remember (rel b c) as bc eqn:Hbc; symmetry in Hbc.
destruct bc. {
  remember (b :: c :: l) as l'.
  remember (a :: c :: l) as l''; cbn; subst l' l''.
  rewrite IHl; [ symmetry | easy ].
  remember (rel a c) as ac eqn:Hac; symmetry in Hac.
  destruct ac. {
    rewrite IHl; [ | easy ].
Search (sorted _ _ → isort _ _ = _).
...
  rewrite IHl; [ symmetry | ].
  do 2 rewrite fold_isort.
...
rewrite <- isort_cons_cons_swap in Hla. 2: {
  now apply Nat.leb_le, Nat.lt_le_incl.
}
...
      clear Hit HQ.
      revert la Hla H1.
      induction Q as [| (cc, dc)]; intros. {
        cbn in Hla.
        injection Hla; clear Hla; intros; subst ma la.
        cbn in Haa.
        now apply Nat.nlt_ge in Haa.
      }
      cbn in Hla.
...
      destruct Q as [| (cc2, dc2)]. {
        cbn in Hla.
        rewrite if_leb_le_dec in Hla.
        destruct (le_dec dc db) as [Hcb| Hcb]. {
          injection Hla; clear Hla; intros; subst ma la.
          cbn in Haa.
          now apply Nat.nlt_ge in Haa.
        }
        apply Nat.nle_gt in Hcb.
        injection Hla; clear Hla; intros; subst ma la.
        cbn in H2.
        now apply Nat.nlt_ge in H2.
      }
      cbn in Hla.
...
  apply Nat.leb_le in H2.
  rewrite H2.
...
  destruct la as [| ma]; [ easy | cbn ].
  unfold rel at 1; cbn.
  specialize (H1 _ (or_introl eq_refl)) as H2.
  apply Nat.leb_le in H2.
  now rewrite H2.
...
  revert ca da cb db Q HP HQ Hit Hba.
  induction P as [| (ca', da')]; intros; cbn. {
    apply (sorted_cons_isort_insert Htra).
    apply (sorted_cons_iff Htra).
    split. {
      apply (sorted_isort_insert Htot).
      apply (sorted_isort Htot).
    }
    intros (cc, dc) Hc; cbn.
    apply Nat.leb_le.
    rewrite fold_isort in Hc.
    unfold is_canon_monl in HQ.
    apply Bool.andb_true_iff in HQ.
    destruct HQ as (Hsq, Hcq).
    rewrite fold_sorted in Hsq.
    generalize Hsq; intros Hsqi.
    apply sorted_lt_sorted_le_mdeg in Hsq.
    fold rel in Hsq.
    rewrite (isort_when_sorted Hsq) in Hc.
    destruct Hc as [Hc| Hc]. {
      now injection Hc; clear Hc; intros; subst.
    }
    apply (sorted_cons_iff Htra) in Hsq.
    destruct Hsq as (Hsq, Hrq).
    specialize (Hrq _ Hc).
    cbn in Hrq.
    apply Nat.leb_le in Hrq.
    now transitivity db.
  }
  cbn in Hit.
  destruct (le_dec db da') as [Hba'| Hba']. 2: {
    apply Nat.nle_gt in Hba'.
...
Theorem merge_same_deg_filter_isort : ∀ P,
  let rel := λ ma mb : monom T, mdeg mb <=? mdeg ma in
  let f := λ ma : monom T, (mcoeff ma ≠? 0)%F in
  filter f (merge_same_deg (filter f (isort rel P))) =
  filter f (merge_same_deg (isort rel P)).
Proof.
intros.
assert (Htot : total_relation rel). {
  unfold rel; intros ma mb.
  apply Nat_leb_total_relation.
}
specialize (sorted_isort Htot P) as Hs.
remember (isort rel P) as la eqn:Hla.
clear P Hla.
induction la as [| ma]; [ easy | cbn ].
rewrite fold_merge_same_deg.
assert (H : sorted rel la) by now apply sorted_cons in Hs.
specialize (IHla H); clear H.
remember (f ma) as fa eqn:Hfa; symmetry in Hfa.
destruct fa. {
  cbn; do 2 rewrite fold_merge_same_deg.
  unfold same_deg_sum_coeff.
  remember (merge_same_deg (filter f la)) as lb eqn:Hlb; symmetry in Hlb.
  remember (merge_same_deg la) as lc eqn:Hlc; symmetry in Hlc.
  destruct lb as [| mb]. {
    apply eq_merge_same_deg_nil in Hlb.
    specialize (proj1 (List_filter_nil_iff _ _) Hlb) as Ha; clear Hlb.
    unfold f in Ha; cbn in Ha.
    unfold f in Hfa.
    destruct lc as [| mc]; [ easy | ].
    symmetry in IHla.
    specialize (proj1 (List_filter_nil_iff _ _) IHla) as Hc.
    unfold f in Hc; cbn - [ In ] in Hc.
    unfold f; cbn; rewrite Hfa.
    rewrite if_eqb_eq_dec.
    specialize (Hc _ (or_introl eq_refl)) as H1.
    cbn in IHla.
    unfold f in IHla at 1.
    rewrite H1 in IHla.
    destruct (Nat.eq_dec _ _) as [Hac| Hac]. {
      cbn.
      apply Bool.negb_false_iff in H1.
      apply (rngl_eqb_eq Heq) in H1.
      rewrite H1, rngl_add_0_r.
      fold f.
      rewrite Hfa, IHla.
      now destruct ma.
    }
    cbn; fold f.
    now rewrite Hfa, IHla, H1.
  }
  destruct lc as [| mc]. {
    now apply eq_merge_same_deg_nil in Hlc; subst la.
  }
  unfold f in Hfa; cbn in Hfa.
  apply Bool.negb_true_iff in Hfa.
  apply (rngl_eqb_neq Heq) in Hfa.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (mdeg ma) (mdeg mb)) as [Hab| Hab]. {
    destruct (Nat.eq_dec (mdeg ma) (mdeg mc)) as [Hac| Hac]. {
      unfold f; cbn; fold f.
      cbn in IHla.
      remember (f mb) as fb eqn:Hfb; symmetry in Hfb.
      remember (f mc) as fc eqn:Hfc; symmetry in Hfc.
      destruct fb. {
        unfold f in Hfb.
        apply Bool.negb_true_iff in Hfb.
        apply (rngl_eqb_neq Heq) in Hfb.
        destruct fc. {
          now injection IHla; clear IHla; intros H1 H2; subst mc; rewrite H1.
        }
exfalso.
        unfold f in Hfc.
        apply Bool.negb_false_iff in Hfc.
        apply (rngl_eqb_eq Heq) in Hfc.
(*
        rewrite Hfc, rngl_add_0_r.
        apply (rngl_eqb_neq Heq) in Hfa; rewrite Hfa; cbn.
        apply (rngl_eqb_neq Heq) in Hfa.
*)
        move Hfa after Hfb.
(*
        exfalso.
*)
        apply eq_merge_same_deg_cons_iff in Hlb.
        destruct Hlb as (i & Hi & Hfi & Hms & Hmb & Hdib).
        rewrite Hmb in Hfb.
        apply eq_merge_same_deg_cons_iff in Hlc.
        destruct Hlc as (j & Hj & Hfj & Hmsf & Hmc & Hdic).
        rewrite Hmc in Hfc.
        move Hdib before Hdic.
        rewrite <- Hac, Hab in Hdic, Hfj.
        move j before i.
rewrite Hac in Hab.
apply sorted_cons in Hs.
clear ma Hfa Hac.
...
assert (H1 : ∑ (ma ∈ firstn j (filter g la)), mcoeff ma = 0%F). {
  rename ma into ma'.
  apply all_0_rngl_summation_list_0.
  intros ma Hma.
  apply (In_nth _ _ (Mon 0 0)) in Hma.
  rewrite firstn_length in Hma.
  destruct Hma as (n & Hn & Hma); subst ma.
  destruct (lt_dec n (length (firstn j (filter g la)))) as [Hnj| Hnj]. 2: {
    apply Nat.nlt_ge in Hnj.
    rewrite nth_overflow; [ easy | easy ].
  }
  unfold g.
  clear - Heq.
  revert j n.
  induction la as [| ma]; intros. {
    now cbn; rewrite firstn_nil, List_nth_nil.
  }
  cbn; rewrite if_bool_if_dec.
  destruct (bool_dec _) as [Hmaz| Hmaz]. {
    apply (rngl_eqb_eq Heq) in Hmaz.
    destruct j; [ cbn; now destruct n | ].
    cbn - [ nth ].
    destruct n; [ easy | ].
    apply IHla.
  }
  destruct j; [ cbn; now destruct n | ].
  apply IHla.
}
rewrite <- (rngl_add_0_l (iter_list _ _ _)) in Hfc.
rewrite <- H1 in Hfc at 1; clear H1.
rewrite <- rngl_summation_list_app in Hfc.
...
intros.
destruct P as [| ma la]; [ easy | ].
cbn; do 2 rewrite fold_merge_same_deg.
revert ma.
induction la as [| mb]; intros; cbn. {
  rewrite fold_merge_same_deg.
  rewrite if_bool_if_dec.
  destruct (bool_dec _) as [Hmaz| Hmaz]; [ | easy ].
  now cbn; rewrite Hmaz.
}
do 2 rewrite fold_merge_same_deg.
Print isort_insert.
(* bon, faut voir... *)
... ...
do 2 rewrite merge_same_deg_filter_isort.
fold rel.
...

Theorem canon_polyn_add_assoc :
  ∀ a b c : canon_polyn T, (a + (b + c))%F = (a + b + c)%F.
Proof.
intros P Q R.
symmetry.
rewrite (canon_polyn_add_comm P).
... ...
rewrite canon_polyn_add_add_swap.
now rewrite canon_polyn_add_comm.
...
intros P Q R; cbn.
apply canon_polyn_eq_eq; cbn.
unfold polyn_norm; f_equal; cbn.
do 4 rewrite fold_merge_same_deg.
set (rel := λ ma mb : monom T, mdeg mb <=? mdeg ma).
set (f := λ ma, (mcoeff ma ≠? 0)%F).
assert (Htra : transitive rel). {
  unfold rel; intros a b c Hab Hbc.
  apply Nat.leb_le in Hab, Hbc.
  apply Nat.leb_le.
  now transitivity (mdeg b).
}
assert (Htot : total_relation rel). {
  unfold rel; intros ma mb.
  apply Nat_leb_total_relation.
}
destruct P as ((P), PP).
destruct Q as ((Q), PQ).
destruct R as ((R), PR); cbn.
move Q before P; move R before Q.
unfold is_canon_polyn in PP, PQ, PR.
cbn in PP, PQ, PR.
do 4 rewrite fold_merge_same_deg.
rewrite (canon_monl_is_filter_deg_non_zero P PP) at 1; symmetry.
rewrite (canon_monl_is_filter_deg_non_zero R PR) at 1; symmetry.
fold f.
do 2 rewrite <- filter_app.
do 2 rewrite (sorted_isort_filter Htra Htot).
...
Theorem filter_deg_non_zero_merge_same_deg_filter : ∀ P,
  let f := λ ma : monom T, (mcoeff ma ≠? 0)%F in
  filter f (merge_same_deg (filter f P)) = filter f (merge_same_deg P).
Proof.
intros.
induction P as [| ma la]; [ easy | cbn ].
rewrite if_bool_if_dec.
destruct (bool_dec (f ma)) as [Hmaz| Hmaz]. {
  cbn; do 2 rewrite fold_merge_same_deg.
  unfold same_deg_sum_coeff.
  remember (merge_same_deg la) as lb eqn:Hlb; symmetry in Hlb.
  destruct lb as [| mb]. {
    apply eq_merge_same_deg_nil in Hlb; subst la.
    now cbn; rewrite Hmaz.
  }
  remember (merge_same_deg (filter f la)) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as [| mc]. {
    cbn in IHla; symmetry in IHla.
    remember (f mb) as fmb eqn:Hmbz; symmetry in Hmbz.
    destruct fmb; [ easy | ].
    cbn; rewrite Hmaz.
    rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec _ _) as [Hab| Hab]. {
      cbn.
      unfold f at 1; cbn.
      unfold f in Hmaz, Hmbz; cbn in Hmaz, Hmbz.
      apply Bool.negb_false_iff in Hmbz.
      apply (rngl_eqb_eq Heq) in Hmbz.
      rewrite Hmbz, rngl_add_0_r, Hmaz, IHla.
      now destruct ma.
    }
    now cbn; rewrite Hmaz, Hmbz, IHla.
  }
  cbn in IHla.
  do 2 rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec (mdeg ma) (mdeg mc)) as [Hac| Hac]. {
    destruct (Nat.eq_dec (mdeg ma) (mdeg mb)) as [Hab| Hab]. {
      cbn.
      unfold f at 1 4; cbn.
      remember (f mc) as fmc eqn:Hmcz; symmetry in Hmcz.
      remember (f mb) as fmb eqn:Hmbz; symmetry in Hmbz.
      destruct fmc. {
        destruct fmb. {
          now injection IHla; clear IHla; intros H1 H; subst mc; rewrite H1.
        }
        unfold f in Hmbz, Hmcz.
        apply Bool.negb_false_iff in Hmbz.
        apply (rngl_eqb_eq Heq) in Hmbz.
        rewrite Hmbz, rngl_add_0_r.
        unfold f in Hmaz; cbn in Hmaz.
exfalso.
apply Bool.negb_true_iff in Hmcz, Hmaz.
apply (rngl_eqb_neq Heq) in Hmcz, Hmaz.
symmetry in IHla.
rewrite Hab in Hac.
clear ma Hmaz Hab.
rename Hac into Hbc.
move lb before la; move lc before lb.
move mc before mb.
move IHla before Hlc.
...
apply eq_merge_same_deg_cons_iff in Hlb.
destruct Hlb as (i & Hi & Hfi & Hms & Hmb & Hdib).
rewrite Hmb in Hmbz.
apply eq_merge_same_deg_cons_iff in Hlc.
destruct Hlc as (j & Hj & Hfj & Hmsf & Hmc & Hdic).
rewrite Hmc in Hmcz.
move Hdib before Hdic.
rewrite <- Hbc in Hdic.
set (g := λ ma : monom T, (mcoeff ma =? 0)%F).
...
assert (H1 : ∑ (ma ∈ firstn j (filter g la)), mcoeff ma = 0%F). {
  apply all_0_rngl_summation_list_0.
  intros ma Hma.
  apply (In_nth _ _ (Mon 0 0)) in Hma.
  rewrite firstn_length in Hma.
  destruct Hma as (n & Hn & Hma); subst ma.
  destruct (lt_dec n (length (firstn j (filter g la)))) as [Hnj| Hnj]. 2: {
    apply Nat.nlt_ge in Hnj.
    rewrite nth_overflow; [ easy | easy ].
  }
  unfold g.
  clear - Heq.
  revert j n.
  induction la as [| ma]; intros. {
    now cbn; rewrite firstn_nil, List_nth_nil.
  }
  cbn; rewrite if_bool_if_dec.
  destruct (bool_dec _) as [Hmaz| Hmaz]. {
    apply (rngl_eqb_eq Heq) in Hmaz.
    destruct j; [ cbn; now destruct n | ].
    cbn - [ nth ].
    destruct n; [ easy | ].
    apply IHla.
  }
  destruct j; [ cbn; now destruct n | ].
  apply IHla.
}
rewrite <- (rngl_add_0_l (iter_list _ _ _)) in Hmcz.
rewrite <- H1 in Hmcz at 1; clear H1.
rewrite <- rngl_summation_list_app in Hmcz.
Search (firstn _ _ ++ firstn _ _).
...
specialize permutation_firstn as H1.
specialize (H1 _ monom_eqb (Mon 0 0) monom_eqb_eq).
specialize (H1 (λ _, True)).
eapply H1.
apply (permutation_firstn (Mon 0 0)).
Search (∑ (_ ∈ _), _ = ∑ (_ ∈ _), _)%F.
Search (∑ (_ ∈ _), _ + ∑ (_ ∈ _), _)%F.
...
  rewrite firstn_app.
  rewrite rngl_summation_list_app.
...
replace la with (filter f la
...
Search (∑ (_ ∈ _), _ + ∑ (_ ∈ _), _)%F.
assert (H1 : ∑ (ma ∈ firstn j (filter g la)), mcoeff ma = 0%F).
...
replace (∑ (_ ∈ _), _) with (α
rewrite rngl_summation_list_eq_compat with
  (h := λ firstn j (filter f la ++ filter g la)) in Hmbz.
...
destruct lb as [| md]; [ easy | ].
cbn in IHla.
remember (f md) as fd eqn:Hmdz; symmetry in Hmdz.
destruct fd. {
  injection IHla; clear IHla; intros H1 H; subst md.
  now apply eq_merge_same_deg_cons_cons in Hlb.
}
unfold f in Hmdz; cbn in Hmdz.
apply Bool.negb_false_iff in Hmdz.
apply (rngl_eqb_eq Heq) in Hmdz.
move Hmdz after Hmbz.
destruct lb as [| me]; [ easy | ].
cbn in IHla.
remember (f me) as fe eqn:Hmez; symmetry in Hmez.
destruct fe. {
  injection IHla; clear IHla; intros H1 H; subst me.
  apply eq_merge_same_deg_cons_iff in Hlb.
  destruct Hlb as (i & Hi & Hfi & Hms & Hmb & Hdi).
  clear Hmez.
...
generalize Hlb; intros H.
apply (f_equal (filter f)) in H.
cbn in H.
unfold f at 2 in H.
rewrite Hmbz in H.
rewrite if_bool_if_dec in H.
destruct (bool_dec _) as [H'| H']; [ | clear H' ]. {
  apply Bool.negb_true_iff in H'.
  now apply (rngl_eqb_neq Heq) in H'.
}
rewrite Hlb in H.
cbn in H.
unfold f in H at 1.
rewrite Hmbz in H.
rewrite if_bool_if_dec in H.
destruct (bool_dec _) as [H'| H']; [ | clear H' ]. {
  apply Bool.negb_true_iff in H'.
  now apply (rngl_eqb_neq Heq) in H'.
}
(* aucun intérêt *)
...
Search (merge_same_deg (filter _ _)).
(* cb=0 donc, par Hlb, les premiers éléments de "la" de degré "db"
   ont 0 pour somme de coefficients ;
   - s'il n'y en a qu'un seul, alors il est nul et "filter f la"
     a pour permier élément un monôme de degré ≠ mb donc mc a un
     degré différent de mb : contradiction
   - s'il y en a plusieurs, alors le coefficient de mc est 0 :
     contradiction
*)
apply eq_merge_same_deg_cons_iff in Hlb.
destruct Hlb as (i & Hil & Hffa & Hlb & Hcb & Hdb).
symmetry in Hcb; rewrite Hmbz in Hcb.
destruct la as [| md]; [ easy | ].
destruct i; [ easy | ].
cbn in Hcb.
destruct la as [| me]. {
  rewrite firstn_nil in Hcb.
  rewrite rngl_summation_list_only_one in Hcb.
  cbn in Hlb.
  now rewrite skipn_nil in Hlb; cbn in Hlb; subst lb.
}
cbn - [ merge_same_deg ] in Hlb.
rewrite List_nth_succ_cons in Hdb.
(**)
rewrite Hab in Hac.
clear ma Hmaz Hab.
rename Hac into Hbc.
clear Hil.
move lb before la; move lc before lb.
move mc before mb.
move Hmbz after Hmcz.
move IHla before Hlb.
subst lb.
...
destruct i. {
  cbn - [ In ] in Hcb, Hlb, Hdb, Hffa.
  rewrite rngl_summation_list_only_one in Hcb.
  rewrite fold_merge_same_deg in Hlb.
  specialize (Hffa _ (or_introl eq_refl)).
  cbn in Hlc.
  unfold f in Hlc at 1.
  rewrite Hcb in Hlc; cbn in Hlc.
  rewrite if_bool_if_dec in Hlc.
  destruct (bool_dec (0 ≠? 0)%F) as [H| H]; [ | clear H ]. {
    apply Bool.negb_true_iff in H.
    now apply (rngl_eqb_neq Heq) in H.
  }
  rewrite fold_merge_same_deg in Hlc.
  remember (f me) as fe eqn:Hmez; symmetry in Hmez.
  unfold f in Hmez; cbn in Hmez.
  destruct fe. {
    cbn in Hlc.
    rewrite fold_merge_same_deg in Hlc.
    rename Hdb into Heb; rename Hffa into Hdb.
    move Hdb at bottom; move Heb at bottom.
    apply Bool.negb_true_iff in Hmaz, Hmcz, Hmez.
    apply (rngl_eqb_neq Heq) in Hmaz, Hmcz, Hmez.
    move Hmbz after Hmaz.
    move Hmcz after Hmbz.
    move Hmez after Hmcz.
    rename Hcb into Hmdz.
    move Hmdz after Hmcz.
    clear Hil.
    move lb before la; move lc before lb.
    move mb before ma; move mc before mb.
...
    unfold same_deg_sum_coeff in Hlb, Hlc.
    remember (merge_same_deg la) as ld eqn:Hld; symmetry in Hld.
    destruct ld as [| mf]. {
      subst lb.
      apply eq_merge_same_deg_nil in Hld; subst la.
      cbn in Hlc.
      injection Hlc; clear Hlc; intros; subst me lc.
      congruence.
    }
    rewrite if_eqb_eq_dec in Hlb.
    destruct (Nat.eq_dec (mdeg me) (mdeg mf)) as [Hef| Hef]. {
      subst lb; unfold f in IHla.
      cbn in IHla; fold f in IHla.
      move Hef after Heb.
...
apply eq_merge_same_deg_cons_iff in Hlc.
destruct Hlc as (i & Hil & Hffa & Hlc & Hcc & Hdc).
...
(*
        rewrite Hmaz.
        rewrite if_bool_if_dec.
        destruct (bool_dec _) as [Hcac| Hcac]. {
*)
...
  destruct lb as [| mb]; [ now cbn; rewrite Hmaz | ].
  cbn.
  remember (f mb) as fmb eqn:Hmbz; symmetry in Hmbz.
  destruct fmb. {
    do 2 rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec (mdeg ma) (mdeg mb)) as [Hab| Hab]. {
      unfold f; cbn; fold f.
      rewrite if_bool_if_dec.
      destruct (bool_dec _) as [Habz| Habz]; [ easy | ].
*)
... ...
Search (isort _ (_ ++ _)).
Search (merge_same_deg (isort _ _)).
Search (merge_same_deg (_ ++ _)).
Search (merge_same_deg (filter _ _)).
Inspect 1.
do 2 rewrite filter_deg_non_zero_merge_same_deg_filter.
f_equal.
...
induction R as [| ma]; [ easy | cbn ].
remember (f ma) as b eqn:Hb; symmetry in Hb.
destruct b. {
  cbn; rewrite IHR.
  clear IHR.
  revert ma Hb.
  induction R as [| mb]; intros; cbn; [ now rewrite Hb | ].
  rewrite <- IHR.
...
intros * HPP.
induction P as [| ma]. {
  cbn.
  induction Q as [| mb]; [ easy | cbn ].
  remember (f mb) as b eqn:Hb; symmetry in Hb.
  destruct b. {
    cbn.
    rewrite IHQ.
    clear IHQ.
    remember (isort rel Q) as P; clear HeqP.
    revert mb Hb.
    induction P as [| mc]; intros; cbn; [ now rewrite Hb | ].
    remember (rel mb mc) as bc eqn:Hbc; symmetry in Hbc.
    destruct bc. {
      remember (f mc) as c eqn:Hc; symmetry in Hc.
      cbn.
      rewrite Hb, Hc.
      destruct c; [ now cbn; rewrite Hbc | ].
      rewrite IHP; [ | easy ].
... ...
rewrite glop.
...

Definition canon_polyn_ring_like_prop : ring_like_prop (canon_polyn T) :=
  {| rngl_mul_is_comm := false; (* à voir *)
     rngl_has_eqb := false; (* à voir *)
     rngl_has_dec_le := false; (* à voir *)
     rngl_has_1_neq_0 := false; (* à voir *)
     rngl_is_ordered := false; (* à voir *)
     rngl_is_integral := false; (* à voir *)
     rngl_characteristic := rngl_characteristic;
     rngl_add_comm := canon_polyn_add_comm;
     rngl_add_assoc := canon_polyn_add_assoc;
    rngl_add_0_l := ?rngl_add_0_l;
    rngl_mul_assoc := ?rngl_mul_assoc;
    rngl_mul_1_l := ?rngl_mul_1_l;
    rngl_mul_add_distr_l := ?rngl_mul_add_distr_l;
    rngl_opt_1_neq_0 := ?rngl_opt_1_neq_0;
    rngl_opt_mul_comm := ?rngl_opt_mul_comm;
    rngl_opt_mul_1_r := ?rngl_opt_mul_1_r;
    rngl_opt_mul_add_distr_r := ?rngl_opt_mul_add_distr_r;
    rngl_opt_add_opp_l := ?rngl_opt_add_opp_l;
    rngl_opt_add_sub := ?rngl_opt_add_sub;
    rngl_opt_sub_sub_sub_add := ?rngl_opt_sub_sub_sub_add;
    rngl_opt_mul_sub_distr_l := ?rngl_opt_mul_sub_distr_l;
    rngl_opt_mul_sub_distr_r := ?rngl_opt_mul_sub_distr_r;
    rngl_opt_mul_inv_l := ?rngl_opt_mul_inv_l;
    rngl_opt_mul_inv_r := ?rngl_opt_mul_inv_r;
    rngl_opt_mul_div := ?rngl_opt_mul_div;
    rngl_opt_mul_quot_r := ?rngl_opt_mul_quot_r;
    rngl_opt_eqb_eq := ?rngl_opt_eqb_eq;
    rngl_opt_le_dec := ?rngl_opt_le_dec;
    rngl_opt_integral := ?rngl_opt_integral;
    rngl_characteristic_prop := ?rngl_characteristic_prop;
    rngl_opt_le_refl := ?rngl_opt_le_refl;
    rngl_opt_le_antisymm := ?rngl_opt_le_antisymm;
    rngl_opt_le_trans := ?rngl_opt_le_trans;
    rngl_opt_add_le_compat := ?rngl_opt_add_le_compat;
    rngl_opt_mul_le_compat_nonneg := ?rngl_opt_mul_le_compat_nonneg;
    rngl_opt_mul_le_compat_nonpos := ?rngl_opt_mul_le_compat_nonpos;
    rngl_opt_mul_le_compat := ?rngl_opt_mul_le_compat;
    rngl_opt_not_le := ?rngl_opt_not_le
  |}.

...
(**)

(* old version *)

Record polyn T := mk_polyn { monl : list (monom T) }.

Arguments mk_polyn {T} monl%list.
Arguments polyn T%type.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).
Context {Heq : rngl_has_eqb = true}.
(*
Context {Hop : rngl_has_opp = true}.
*)
Context {H10 : rngl_has_1_neq_0 = true}.

(* if "pa" and "pb" are polynomials in canonical order,
   i.e.
   - degrees are in decreasing order
   - no coefficien is nul,
   then "polyn_add pa pb" is also in canonical order
   (this must be proven, if necessary) *)

Fixpoint monl_add_loop it la lb :=
  match it with
  | 0 => [Mon 0 99] (* algo error: not enough iterations *)
  | S it' =>
      match la with
      | [] => lb
      | Mon ca da :: la' =>
          match lb with
          | [] => la
          | Mon cb db :: lb' =>
              match Nat.compare da db with
              | Eq =>
                  let c := (ca + cb)%F in
                  if (c =? 0)%F then monl_add_loop it' la' lb'
                  else Mon c da :: monl_add_loop it' la' lb'
              | Lt => Mon cb db :: monl_add_loop it' la lb'
              | Gt => Mon ca da :: monl_add_loop it' la' lb
              end
          end
      end
  end.

Definition monl_add_nb_iter (la lb : list (monom T)) :=
  S (length la + length lb).
Definition monl_add la lb :=
  monl_add_loop (monl_add_nb_iter la lb) la lb.

Arguments monl_add_loop it%nat (la lb)%list.
Arguments monl_add (la lb)%list.

(*
End a.
Arguments monl_add {T ro} (la lb)%list.
Arguments is_canon_polyn {T ro} p.
Arguments monl {T} p.
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
Compute (is_canon_polyn «3*☓^5 + 5*☓^2 + 8*☓»).
Compute (is_canon_polyn «3*☓^5 + 5*☓^2 + 8*☓^7»).
Compute (monl_add (monl «3*☓^5 + 5*☓^2 + 8*☓») (monl «3*☓^5 + 5*☓^2 + 8*☓»)).
Compute (monl_add (monl «3*☓^5 + 5*☓^2 + 8*☓») (monl «3*☓^5 + (-5)*☓^2 + 8*☓»)).
Compute (monl_add (monl «3*☓^5 + 5*☓^2 + 8*☓») (monl « »)).
Compute (monl_add (monl « ») (monl «3*☓^5 + (-5)*☓^2 + 8*☓»)).
*)

Definition polyn_add (pa pb : polyn T) :=
  mk_polyn (monl_add (monl pa) (monl pb)).

(*
End a.
Arguments polyn_add {T ro} (pa pb).
Arguments is_canon_polyn {T ro} p.
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
Compute (polyn_add «3*☓^5 + 5*☓^2 + 8*☓» «3*☓^5 + 5*☓^2 + 8*☓»).
Compute (polyn_add «3*☓^5 + 5*☓^2 + 8*☓» «3*☓^5 + (-5)*☓^2 + 7·»).
Compute (is_canon_polyn (polyn_add «3*☓^5 + 5*☓^2 + 8*☓» «3*☓^5 + 5*☓^2 + 8*☓»)).
Compute (polyn_add «3*☓^5 + 5*☓^2 + 8*☓» «3*☓^5 + (-5)*☓^7 + 7·»).
Compute (is_canon_polyn (polyn_add «3*☓^5 + 5*☓^2 + 8*☓» «3*☓^5 + (-5)*☓^7 + 7·»)).
*)

(* multiplication *)

Fixpoint monl_mul_mon_l ma lb :=
  match lb with
  | [] => []
  | mb :: lb' =>
      let c := (mcoeff ma * mcoeff mb)%F in
      if (c =? 0)%F then monl_mul_mon_l ma lb'
      else Mon c (mdeg ma + mdeg mb) :: monl_mul_mon_l ma lb'
  end.

Fixpoint monl_mul la lb :=
  match la with
  | [] => []
  | ma :: la' => monl_add (monl_mul_mon_l ma lb) (monl_mul la' lb)
  end.

Definition polyn_mul pa pb := mk_polyn (monl_mul (monl pa) (monl pb)).

(*
End a.
Arguments polyn_mul {T ro} (pa pb).
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
Compute (polyn_mul «1*☓ + 1·» «1*☓ + (-1)·»).
Compute (polyn_mul «3*☓^5 + 1·» «1*☓ + (-1)·»).
Compute (polyn_mul «1*☓ + (-1)·» «3*☓^5 + 1·»).
*)

(* opposite *)

Definition monl_opp la := map (λ m, Mon (- mcoeff m)%F (mdeg m)) la.
Definition polyn_opp p := mk_polyn (monl_opp (monl p)).

(* subtraction *)

Definition monl_sub la lb := monl_add la (monl_opp lb).
Definition polyn_sub pa pb := mk_polyn (monl_sub (monl pa) (monl pb)).

(*
End a.
Arguments polyn_opp {T ro} p.
Arguments polyn_mul {T ro} (pa pb).
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
Compute (mk_polyn [Mon 1 2]).
Compute « 1*☓^2 ».
Compute (polyn_opp «1*☓»).
Compute (polyn_opp «1*☓ + 1·»).
Compute (polyn_opp «1*☓ + (-1)·»).
Compute (polyn_opp «3*☓^5 + 1·»).
Compute (polyn_opp «3*☓^5»).
Compute (polyn_mul «1*☓ + (-1)·» «3*☓^5 + 1·»).
Check (polyn_mul «1*☓ + (-1)·» «3*☓^5 + 1·»).
Compute (polyn_opp (polyn_mul «3*☓^5 + 1·» «1*☓ + (-1)·»)).
*)

(* euclidean division *)

Fixpoint monl_quot_rem_loop it la lb :=
  match it with
  | 0 => ([], [Mon (rngl_of_nat 99) 0]) (* algo err: not enough iterations *)
  | S it' =>
      match la with
      | [] => ([], [])
      | Mon ca da :: la' =>
          match lb with
          | [] => ([], []) (* division by zero *)
          | Mon cb db :: _ =>
            let c := (ca / cb)%F in
            if (c =? 0)%F then ([], la)
            else if da <? db then ([], la)
            else
              let mq := Mon c (da - db) in
              let lr := monl_sub la (monl_mul lb [mq]) in
              let (lq', lr') := monl_quot_rem_loop it' lr lb in
              (mq :: lq', lr')
          end
      end
  end.

Definition monl_quot_rem la lb := monl_quot_rem_loop (S (length la)) la lb.

Definition polyn_quot_rem pa pb :=
  let (lq, lr) := monl_quot_rem (monl pa) (monl pb) in
  (mk_polyn lq, mk_polyn lr).

Definition polyn_quot pa pb := fst (polyn_quot_rem pa pb).
Definition polyn_rem pa pb := snd (polyn_quot_rem pa pb).

Definition polyn_zero := mk_polyn [] : polyn T.
Definition polyn_one := mk_polyn [Mon 1 0] : polyn T.

(*
End a.
Arguments monl_quot_rem_loop {T ro} it%nat (la lb)%list.
Arguments monl_quot_rem {T ro} (la lb)%list.
Arguments polyn_quot_rem {T ro} (pa pb).
Arguments polyn_quot {T ro} (pa pb).
Arguments polyn_rem {T ro} (pa pb).
Arguments monl_mul {T ro} (la lb)%list.
Arguments monl_sub {T ro} (la lb)%list.
(*
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
*)
Require Import RnglAlg.Qrl.
Require Import RnglAlg.Rational.
Import Q.Notations.
Open Scope Q_scope.
Compute (polyn_quot_rem «1*☓^2 + (-1)·» «2·»).
Compute (polyn_quot_rem «4*☓^2 + (-1)·» «2·»).
Compute (polyn_quot_rem «1*☓^2 + (-1)·» «2*☓»).
Compute (polyn_quot_rem «1·» «2·»).
Compute (polyn_quot_rem «1*☓^2 + 3*☓ + 7·» «1*☓ + 1·»).
Compute (polyn_quot_rem «1*☓^2 + 3*☓ + 7·» «2*☓ + 1·»).
Compute (polyn_quot_rem «1*☓^2 + 3*☓ + 7·» «»).
Compute (polyn_quot_rem «» «1*☓^2 + 3*☓ + 7·»).
*)

End a.

(* polynomial notations *)

Declare Scope P_scope.
Delimit Scope P_scope with P.

Arguments monl_add {T ro} (la lb)%list.
Arguments monl_add_loop {T ro} it%nat (la lb)%list.
Arguments monl_opp {T ro} la%list.
Arguments polyn_add {T ro} (pa pb)%P.
Arguments polyn_mul {T ro} (pa pb)%P.
Arguments polyn_one {T ro}.
Arguments polyn_opp {T ro} p%P.
Arguments polyn_quot {T ro} (pa pb)%P.

Module polynomial_Notations.

Notation "pa + pb" := (polyn_add pa pb) : P_scope.

End polynomial_Notations.

Import polynomial_Notations.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).
Context {Heq : rngl_has_eqb = true}.
Context {Hop : rngl_has_opp = true}.

(* polynomial ring-like operators *)

Definition polyn_ring_like_op : ring_like_op (polyn T) :=
  {| rngl_zero := polyn_zero;
     rngl_one := polyn_one;
     rngl_add := polyn_add;
     rngl_mul := polyn_mul;
     rngl_opt_opp_or_sous := Some (inl polyn_opp);
     rngl_opt_inv_or_quot := Some (inr polyn_quot);
     rngl_opt_eqb := None;
     rngl_opt_le := None |}.

(* allows to use ring-like theorems on polynomials *)
Canonical Structure polyn_ring_like_op.

(* to search for ring-like polynomials operators in the context *)
Global Existing Instance polyn_ring_like_op.

(* polynomial ring-like properties *)

Theorem monl_opp_length : ∀ la : list (monom T),
  length (monl_opp la) = length la.
Proof.
now intros; unfold monl_opp; rewrite map_length.
Qed.

Theorem monl_opp_involutive : ∀ (la : list (monom T)),
  monl_opp (monl_opp la) = la.
Proof.
intros.
unfold monl_opp.
rewrite map_map.
erewrite map_ext_in. 2: {
  intros ma Hma; cbn.
  rewrite rngl_opp_involutive; [ | easy ].
  easy.
}
induction la as [| (ca, da)]; [ easy | cbn ].
now f_equal.
Qed.

Theorem monl_add_loop_comm : ∀ it (la lb : list (monom T)),
  monl_add_nb_iter la lb ≤ it
  → monl_add_loop it la lb = monl_add_loop it lb la.
Proof.
intros * Hit.
unfold monl_add_nb_iter in Hit.
revert la lb Hit.
induction it; intros; [ easy | cbn ].
destruct la as [| (ca, da)]. {
  now destruct lb as [| (cb, db) ].
}
destruct lb as [| (cb, db)]; [ easy | ].
cbn in Hit.
rewrite Nat.add_succ_r in Hit.
apply Nat.succ_le_mono in Hit.
move db before da; move cb before ca.
rewrite (Nat.compare_antisym da).
unfold CompOpp.
rewrite (rngl_add_comm cb).
remember (da ?= db) as c eqn:Hc; symmetry in Hc.
destruct c. {
  apply Nat.compare_eq in Hc; subst db.
  rewrite IHit; [ easy | now apply Nat.lt_le_incl ].
} {
  now f_equal; apply IHit.
} {
  f_equal; apply IHit; cbn.
  now rewrite Nat.add_succ_r.
}
Qed.

Theorem monl_add_nb_iter_comm : ∀ (la lb : list (monom T)),
  monl_add_nb_iter la lb = monl_add_nb_iter lb la.
Proof.
intros.
unfold monl_add_nb_iter.
now rewrite Nat.add_comm.
Qed.

Theorem monl_add_comm : ∀ (la lb : list (monom T)),
  monl_add la lb = monl_add lb la.
Proof.
intros.
unfold monl_add.
rewrite (monl_add_nb_iter_comm lb).
now apply monl_add_loop_comm.
Qed.

...

Theorem monl_add_loop_enough_iter : ∀ it1 it2 (la lb : list (monom T)),
  monl_add_nb_iter la lb ≤ it1
  → monl_add_nb_iter la lb ≤ it2
  → monl_add_loop it1 la lb = monl_add_loop it2 la lb.
Proof.
intros * Hit1 Hit2.
unfold monl_add_nb_iter in Hit1, Hit2.
revert it2 la lb Hit1 Hit2.
induction it1; intros; [ easy | cbn ].
apply Nat.succ_le_mono in Hit1.
destruct la as [| (ca, da)]; [ now destruct it2 | ].
destruct lb as [| (cb, db)]; [ now destruct it2 | ].
cbn in Hit1, Hit2.
destruct it2; [ easy | cbn ].
apply Nat.succ_le_mono in Hit2.
remember (da ?= db) as dab eqn:Hdab; symmetry in Hdab.
destruct dab. {
  destruct (ca + cb =? 0)%F; [ | f_equal ]. {
    apply IHit1; [ flia Hit1 | flia Hit2 ].
  } {
    apply IHit1; [ flia Hit1 | flia Hit2 ].
  }
} {
  f_equal.
  apply IHit1; cbn; [ flia Hit1 | flia Hit2 ].
} {
  f_equal.
  apply IHit1; cbn; [ flia Hit1 | flia Hit2 ].
}
Qed.

Theorem eq_monl_add_loop_nil : ∀ it (la lb : list (monom T)),
  monl_add_nb_iter la lb ≤ it
  → monl_add_loop it la lb = []
  → la = monl_opp lb.
Proof.
intros * Hit Hab.
unfold monl_add_nb_iter in Hit.
revert la lb Hab Hit.
induction it; intros; [ easy | ].
cbn in Hab.
destruct la as [| (ca, da)]; [ now subst lb | ].
destruct lb as [| (cb, db)]; [ easy | cbn ].
move cb before ca; move db before da.
remember (da ?= db) as dab eqn:Hdab; symmetry in Hdab.
cbn in Hit; apply Nat.succ_le_mono in Hit.
rewrite Nat.add_succ_r in Hit.
destruct dab; [ | easy | easy ].
apply Nat.compare_eq_iff in Hdab; subst db.
remember (ca + cb =? 0)%F as cab eqn:Hcab; symmetry in Hcab.
destruct cab; [ | easy ].
apply (rngl_eqb_eq Heq), (rngl_add_move_0_r Hop) in Hcab.
rewrite <- Hcab; f_equal.
apply IHit; [ easy | flia Hit ].
Qed.

Theorem monl_add_loop_assoc : ∀ it1 it2 it3 it4 (la lb lc : list (monom T)),
  monl_is_canon la = true
  → monl_is_canon lb = true
  → monl_is_canon lc = true
  → monl_add_nb_iter la (monl_add_loop (monl_add_nb_iter lb lc) lb lc) ≤ it1
  → monl_add_nb_iter lb lc ≤ it2
  → monl_add_nb_iter (monl_add_loop (monl_add_nb_iter la lb) la lb) lc ≤ it3
  → monl_add_nb_iter la lb ≤ it4
  → monl_add_loop it1 la (monl_add_loop it2 lb lc) =
    monl_add_loop it3 (monl_add_loop it4 la lb) lc.
Proof.
intros * Hcna Hcnb Hcnc Hit1 Hit2 Hit3 Hit4.
unfold monl_add_nb_iter in Hit1, Hit2, Hit3, Hit4.
revert la lb lc it2 it3 it4 Hit1 Hit2 Hit3 Hit4 Hcna Hcnb Hcnc.
induction it1; intros; [ easy | cbn ].
destruct la as [| (ca, da)]. {
  destruct it4; [ easy | cbn ].
  cbn in Hit3.
  now apply monl_add_loop_enough_iter.
}
destruct it2; [ easy | ].
destruct lb as [| (cb, db)]. {
  destruct lc as [| (cc, dc)]. {
    cbn in Hit1, Hit2, Hit3, Hit4; cbn.
    destruct it3; [ easy | cbn ].
    destruct it4; [ easy | easy ].
  } {
    cbn in Hit1, Hit2, Hit3, Hit4; cbn.
    destruct it3; [ easy | cbn ].
    destruct it4; [ easy | cbn ].
    remember (da ?= dc) as dac eqn:Hdac; symmetry in Hdac.
    destruct dac. {
      destruct (ca + cc =? 0)%F; [ | f_equal ]. {
        apply monl_add_loop_enough_iter.
        unfold monl_add_nb_iter; flia Hit1.
        unfold monl_add_nb_iter; flia Hit3.
      } {
        apply monl_add_loop_enough_iter.
        unfold monl_add_nb_iter; flia Hit1.
        unfold monl_add_nb_iter; flia Hit3.
      }
    } {
      f_equal.
      apply Nat.succ_le_mono in Hit1, Hit3.
      rewrite Nat.add_succ_r in Hit1, Hit3.
      now apply monl_add_loop_enough_iter.
    } {
      f_equal.
      apply Nat.succ_le_mono in Hit1, Hit3.
      apply monl_add_loop_enough_iter; [ easy | easy ].
    }
  }
}
move cb before ca.
move db before da.
cbn - [ monl_add_loop ] in Hit1, Hit2, Hit3, Hit4.
apply Nat.succ_le_mono in Hit1, Hit2.
destruct lc as [| (cc, dc)]. {
  cbn in Hit1.
  destruct it4; [ easy | cbn ].
  destruct it3; [ easy | ].
  remember (da ?= db) as dab eqn:Hdab; symmetry in Hdab.
  destruct dab. {
    apply Nat.compare_eq_iff in Hdab; subst db.
    destruct (ca + cb =? 0)%F. {
      remember (monl_add_loop it4 _ _) as ld eqn:Hld.
      symmetry in Hld.
      destruct ld as [| (cd, dd)]. {
        cbn; rewrite <- Hld.
        apply monl_add_loop_enough_iter.
        unfold monl_add_nb_iter; flia Hit1.
        unfold monl_add_nb_iter; flia Hit4.
      } {
        cbn; rewrite <- Hld.
        apply monl_add_loop_enough_iter.
        unfold monl_add_nb_iter; flia Hit1.
        unfold monl_add_nb_iter; flia Hit4.
      }
    } {
      cbn; f_equal.
      apply monl_add_loop_enough_iter.
      unfold monl_add_nb_iter; flia Hit1.
      unfold monl_add_nb_iter; flia Hit4.
    }
  } {
    cbn; f_equal.
    apply monl_add_loop_enough_iter.
    unfold monl_add_nb_iter; cbn; flia Hit1.
    unfold monl_add_nb_iter; cbn; flia Hit4.
  } {
    cbn; f_equal.
    apply monl_add_loop_enough_iter.
    unfold monl_add_nb_iter; cbn; flia Hit1.
    unfold monl_add_nb_iter; cbn; flia Hit4.
  }
}
move cc before cb; move dc before db.
cbn - [ monl_add_loop ] in Hit1, Hit2, Hit3, Hit4.
cbn.
destruct it3; [ easy | cbn ].
destruct it4; [ easy | cbn ].
cbn - [ monl_add_loop ] in Hit3.
apply Nat.succ_le_mono in Hit3, Hit4.
rewrite Nat.add_succ_r in Hit3.
remember (db ?= dc) as dbc eqn:Hdbc; symmetry in Hdbc.
remember (da ?= db) as dab eqn:Hdab; symmetry in Hdab.
destruct dbc. {
  apply Nat.compare_eq_iff in Hdbc; subst dc.
  destruct dab. {
    apply Nat.compare_eq_iff in Hdab; subst db.
    remember (cb + cc =? 0)%F as cbc eqn:Hcbc; symmetry in Hcbc.
    remember (monl_add_loop it2 lb lc) as mbc eqn:Hmbc; symmetry in Hmbc.
    rewrite rngl_add_comm in Hcbc.
    destruct cbc. {
      apply (rngl_eqb_eq Heq), (rngl_add_move_0_r Hop) in Hcbc.
      subst cc.
      destruct mbc as [| (cbc, dbc)]. {
        apply eq_monl_add_loop_nil in Hmbc. 2: {
          unfold monl_add_nb_iter; flia Hit2.
        }
        subst lb.
        remember (ca + cb =? 0)%F as cab eqn:Hcab; symmetry in Hcab.
        destruct cab. {
          apply (rngl_eqb_eq Heq), (rngl_add_move_0_r Hop) in Hcab.
          subst ca.
          remember (monl_add_loop it4 la (monl_opp lc)) as mac eqn:Hmac.
          symmetry in Hmac.
          destruct mac as [| (cac, dac)]. {
            f_equal.
            apply eq_monl_add_loop_nil in Hmac. 2: {
              unfold monl_add_nb_iter; flia Hit4.
            }
            subst la.
            apply monl_opp_involutive.
          }
          remember (dac ?= da) as daca eqn:Hdaca; symmetry in Hdaca.
          destruct daca. {
            apply Nat.compare_eq_iff in Hdaca; subst dac.
            rewrite (fold_rngl_sub Hop).
            remember (cac - cb =? 0)%F as cab eqn:Hcab.
            symmetry in Hcab.
            destruct cab. {
              apply (rngl_eqb_eq Heq) in Hcab.
              apply -> (rngl_sub_move_0_r Hop) in Hcab; subst cac.
              symmetry.
              remember (- cb)%F as ca eqn:Hca.
              apply (f_equal rngl_opp) in Hca.
              rewrite (rngl_opp_involutive Hop) in Hca.
              subst cb.
...
      move cab before cbc; move mab before mbc.
      destruct cab. {
        apply (rngl_eqb_eq Heq), (rngl_add_move_0_r Hop) in Hcab.
        rewrite <- Hcab in Hcbc; subst cc.
        destruct mbc as [| (cbc, dbc)]. {
          apply eq_monl_add_loop_nil in Hmbc. 2: {
            unfold monl_add_nb_iter; flia Hit2.
          }
          subst lb.
          rewrite monl_opp_length in Hit1, Hit2, Hit3, Hit4.
          destruct mab as [| (cab, dab)]. {
            f_equal.
            apply eq_monl_add_loop_nil in Hmab. 2: {
              unfold monl_add_nb_iter.
              rewrite monl_opp_length; flia Hit4.
            }
            now rewrite monl_opp_involutive in Hmab.
          }
          move cab before cb; move dab before da.
          remember (dab ?= da) as daba eqn:Hdaba; symmetry in Hdaba.
          destruct daba. {
            apply Nat.compare_eq_iff in Hdaba; subst dab.
            remember (cab + ca =? 0)%F as caba eqn:Hcaba.
            symmetry in Hcaba.
            destruct caba. {
              apply (rngl_eqb_eq Heq) in Hcaba.
              destruct lc as [| (cc, dc)]. {
                destruct it4; [ easy | cbn in Hmab ].
                destruct la as [| (ca', da')]; [ easy | ].
                injection Hmab; clear Hmab; intros; subst ca' da' mab.
                unfold monl_is_canon in Hcna.
                cbn in Hcna.
                now rewrite Nat.leb_refl in Hcna.
              }
              destruct it3; [ easy | cbn ].
              apply Nat.succ_le_mono in Hit3.
              destruct mab as [| (ca', da')]. {
                cbn in Hmab.
                destruct it4; [ easy | ].
                cbn in Hmab.
                destruct la as [| (ca', da')]. {
                  injection Hmab; clear Hmab; intros Hmab H H'; subst dc cab.
                  apply map_eq_nil in Hmab; subst lc; f_equal; f_equal.
                  rewrite rngl_add_comm in Hcaba.
                  rewrite (fold_rngl_sub Hop) in Hcaba.
                  now apply -> (rngl_sub_move_0_r Hop) in Hcaba.
                }
                cbn in Hcna, Hcnc, Hcnb.
                f_equal. {
                  f_equal. {
                    remember (da' ?= dc) as dac eqn:Hdac; symmetry in Hdac.
                    destruct dac. {
                      apply Nat.compare_eq_iff in Hdac; subst da'.
                      rewrite (fold_rngl_sub) in Hmab.
                      remember (ca' - cc =? 0)%F as cac eqn:Hcac.
                      symmetry in Hcac.
                      destruct cac. {
                        apply (rngl_eqb_eq Heq) in Hcac.
                        apply -> (rngl_sub_move_0_r Hop) in Hcac.
                        subst ca'.
                        cbn in Hit4.
                        apply Nat.succ_le_mono in Hit4.
                        destruct it4; [ easy | ].
                        apply Nat.succ_le_mono in Hit4.
                        cbn in Hmab.
                        destruct la as [|( ca', da')]. {
                          destruct lc as [| (cc', dc')]; [ easy | ].
                          destruct lc; [ | easy ].
                          cbn in Hmab.
                          injection Hmab; clear Hmab; intros; subst da cab.
                          unfold monl_is_canon in Hcnc.
                          apply Bool.andb_true_iff in Hcnc.
                          destruct Hcnc as (Hs, Hcnc).
                          cbn in Hs.
                          rewrite Bool.andb_true_r in Hs.
                          apply Bool.andb_true_iff in Hs.
                          destruct Hs as (H1, H2).
                          apply Bool.negb_true_iff in H1, H2.
                          apply leb_gt in H1, H2.
                          flia H1 H2.
                        }
                        destruct lc as [| (cc', dc')]. {
                          cbn in Hmab.
                          injection Hmab; clear Hmab; intros; subst la da' ca'.
                          unfold monl_is_canon in Hcna.
                          apply Bool.andb_true_iff in Hcna.
                          destruct Hcna as (Hs, Hcna).
                          cbn in Hs.
                          rewrite Bool.andb_true_r in Hs.
                          apply Bool.andb_true_iff in Hs.
                          destruct Hs as (H1, H2).
                          apply Bool.negb_true_iff in H1, H2.
                          apply leb_gt in H1, H2.
                          flia H1 H2.
                        }
                        cbn in Hmab.
                        remember (da' ?= dc') as dac eqn:Hdac; symmetry in Hdac.
                        destruct dac. {
                          apply Nat.compare_eq_iff in Hdac; subst dc'.
                          rewrite fold_rngl_sub in Hmab.
                          remember (ca' - cc' =? 0)%F as cac eqn:Hcac.
                          symmetry in Hcac.
                          destruct cac. {
                            apply (rngl_eqb_eq Heq) in Hcac.
                            apply -> (rngl_sub_move_0_r Hop) in Hcac.
                            subst cc'.
                            cbn in Hit4.
                            destruct it4; [ easy | ].
                            apply Nat.succ_le_mono in Hit4.
                            cbn in Hmab.
                            destruct la as [| (ca'', da'')]. {
                              destruct lc as [| (cc', dc')]; [ easy | ].
                              destruct lc; [ cbn in Hmab | easy ].
                              injection Hmab; clear Hmab; intros H Hmab; subst dc'.
                              cbn in Hcnb.
...
                              cbn - [ monl_add_loop ] in Hit1, Hit3.
                              cbn in Hit2, Hit4.
                              cbn in Hcnb.
...

(* *)

Theorem monl_add_assoc : ∀ (la lb lc : list (monom T)),
  monl_add la (monl_add lb lc) = monl_add (monl_add la lb) lc.
Proof.
intros.
unfold monl_add.
(*
remember (monl_add_nb_iter la lb) as it_ab eqn:Hit_ab in |-*.
remember (monl_add_nb_iter lb lc) as it_bc eqn:Hit_bc in |-*.
remember (monl_add_nb_iter la _) as it_a_bc eqn:Hit_a_bc in |-*.
remember (monl_add_nb_iter _ lc) as it_ab_c eqn:Hit_ab_c in |-*.
move it_bc before it_ab; move it_a_bc before it_bc.
move it_ab_c before it_a_bc.
*)
remember (monl_add_nb_iter _ _) as it1 eqn:Hit1.
remember (monl_add_nb_iter _ _) as it2 eqn:Hit2 in |-*.
remember (monl_add_nb_iter _ _) as it3 eqn:Hit3 in |-*.
remember (monl_add_nb_iter _ _) as it4 eqn:Hit4 in |-*.
move it2 before it1; move it3 before it2; move it4 before it3.
... ...
apply monl_add_loop_assoc.
...

(* *)

Theorem polyn_add_comm : ∀ a b, (a + b)%F = (b + a)%F.
Proof.
intros; cbn.
unfold polyn_add; f_equal.
destruct a as (la).
destruct b as (lb).
cbn - [ monl_add ].
apply monl_add_comm.
Qed.

Theorem polyn_add_assoc : ∀ a b c : polyn T, (a + (b + c))%F = (a + b + c)%F.
Proof.
intros; cbn.
unfold polyn_add; f_equal.
destruct a as (la).
destruct b as (lb).
destruct c as (lc).
cbn - [ monl_add ].
... ...
apply monl_add_assoc.
...

Definition polyn_ring_like_prop : ring_like_prop (polyn T) :=
  {| rngl_mul_is_comm := false; (* à voir *)
     rngl_has_eqb := false; (* à voir *)
     rngl_has_dec_le := false; (* à voir *)
     rngl_has_1_neq_0 := false; (* à voir *)
     rngl_is_ordered := false; (* à voir *)
     rngl_is_integral := false; (* à voir *)
     rngl_characteristic := rngl_characteristic;
     rngl_add_comm := polyn_add_comm;
     rngl_add_assoc := polyn_add_assoc;
    rngl_add_0_l := ?rngl_add_0_l;
    rngl_mul_assoc := ?rngl_mul_assoc;
    rngl_mul_1_l := ?rngl_mul_1_l;
    rngl_mul_add_distr_l := ?rngl_mul_add_distr_l;
    rngl_opt_1_neq_0 := ?rngl_opt_1_neq_0;
    rngl_opt_mul_comm := ?rngl_opt_mul_comm;
    rngl_opt_mul_1_r := ?rngl_opt_mul_1_r;
    rngl_opt_mul_add_distr_r := ?rngl_opt_mul_add_distr_r;
    rngl_opt_add_opp_l := ?rngl_opt_add_opp_l;
    rngl_opt_add_sub := ?rngl_opt_add_sub;
    rngl_opt_sub_sub_sub_add := ?rngl_opt_sub_sub_sub_add;
    rngl_opt_mul_sub_distr_l := ?rngl_opt_mul_sub_distr_l;
    rngl_opt_mul_sub_distr_r := ?rngl_opt_mul_sub_distr_r;
    rngl_opt_mul_inv_l := ?rngl_opt_mul_inv_l;
    rngl_opt_mul_inv_r := ?rngl_opt_mul_inv_r;
    rngl_opt_mul_div := ?rngl_opt_mul_div;
    rngl_opt_mul_quot_r := ?rngl_opt_mul_quot_r;
    rngl_opt_eqb_eq := ?rngl_opt_eqb_eq;
    rngl_opt_le_dec := ?rngl_opt_le_dec;
    rngl_opt_integral := ?rngl_opt_integral;
    rngl_characteristic_prop := ?rngl_characteristic_prop;
    rngl_opt_le_refl := ?rngl_opt_le_refl;
    rngl_opt_le_antisymm := ?rngl_opt_le_antisymm;
    rngl_opt_le_trans := ?rngl_opt_le_trans;
    rngl_opt_add_le_compat := ?rngl_opt_add_le_compat;
    rngl_opt_mul_le_compat_nonneg := ?rngl_opt_mul_le_compat_nonneg;
    rngl_opt_mul_le_compat_nonpos := ?rngl_opt_mul_le_compat_nonpos;
    rngl_opt_mul_le_compat := ?rngl_opt_mul_le_compat;
    rngl_opt_not_le := ?rngl_opt_not_le
  |}.

...

(* old version *)

Declare Scope polyn_scope.
Declare Scope mlist_scope.

Delimit Scope polyn_scope with P.
Delimit Scope mlist_scope with mlist.

(* definition of a monomial *)

Record monom T := Mon { mcoeff : T; mdeg : nat }.

(*
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
Compute (Mon (-3) 4).
*)

Notation "c ☓" := (Mon c 1) (at level 30, format "c ☓").
Notation "c ☓ a" := (Mon c a) (at level 30, format "c ☓ a").

(* definition of a list of monomials *)

Record mlist T := mk_mlist { m_list : list (monom T) }.

Definition monl_is_correct T {ro : ring_like_op T} (monl : mlist T) :=
  (is_sorted (λ x y, negb (mdeg x <=? mdeg y)) (m_list monl) &&
   ⋀ (x ∈ m_list monl), (mcoeff x ≠? 0)%F)%bool.

(* definition of a polynomial *)

Record polyn T (ro : ring_like_op T) := mk_polyn
  { monl : mlist T;
    monl_prop : monl_is_correct monl = true }.

Arguments m_list {T} m%mlist.
Arguments mk_polyn {T ro} monl%mlist_scope.
Arguments polyn T%type {ro}.
Arguments monl_is_correct {T ro} monl%mlist.

(*
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
Compute (mk_polyn (mk_mlist [Mon 3 5; Mon (-5) 2; Mon 8 0]) eq_refl).
Compute (mk_polyn (mk_mlist [3☓5; (-5)☓2; 8☓0]) eq_refl).
Compute (Mon 3 8).
Compute (mk_mlist [3☓5; (-5)☓2; 8☓0]).
Compute [3☓5; (-5)☓2; 8☓0].
*)

Module MlistNotations.
Notation "x + y + .. + z" :=
  (mk_mlist (cons x (cons y .. (cons z nil) ..)))
  (at level 50, y at next level, z at next level,
   format "x  +  y  +  ..  +  z")
  : mlist_scope.
(*
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
Compute (mk_polyn (mk_mlist [Mon 3 5; Mon (-5) 2; Mon 8 0]) eq_refl).
Compute (mk_polyn (mk_mlist [3☓5; (-5)☓2; 8☓0]) eq_refl).
Compute (Mon 3 8).
*)
End MlistNotations.

Import MlistNotations.

(*
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
Compute (3☓5 + (-5)☓2 + 8☓)%mlist.
Compute (3☓5 + (-5)☓2 + 8☓0)%mlist.
*)

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).
Context {Heb : rngl_has_eqb = true}.
(*
Context {H10 : rngl_has_1_neq_0 = true}.
*)

(* normalisation *)

Fixpoint monl_norm_loop it (la : list (monom T))  :=
  match it with
  | 0 => []
  | S it' =>
      match la with
      | [] | [_] => la
      | Mon c1 d1 :: Mon c2 d2 :: lb =>
          if Nat.eq_dec d1 d2 then
            let c := (c1 + c2)%F in
            if (c =? 0)%F then monl_norm_loop it' lb
            else monl_norm_loop it' (Mon c d1 :: lb)
          else
            Mon c1 d1 :: monl_norm_loop it' (Mon c2 d2 :: lb)
      end
  end.

Definition monl_norm (la : list (monom T)) :=
  monl_norm_loop (length la) la.

Arguments monl_norm_loop it%nat la%list.
Arguments monl_norm la%list.

(* addition *)

Fixpoint monl_add_loop it (al1 al2 : list (monom T))  :=
  match it with
  | 0 => []
  | S it' =>
      match al1 with
      | [] => al2
      | Mon c1 d1 :: bl1 =>
          match al2 with
          | [] => al1
          | Mon c2 d2 :: bl2 =>
              if le_dec d1 d2 then Mon c2 d2 :: monl_add_loop it' al1 bl2
              else Mon c1 d1 :: monl_add_loop it' bl1 al2
          end
      end
  end.

Definition monl_add (la lb : list (monom T)) :=
  monl_add_loop (length la + length lb) la lb.

Arguments monl_add_loop it%nat al1%list al2%list.
Arguments monl_add la%list lb%list.

(*
End a.
Arguments monl_add {T} la%list lb%list.
Arguments monl_is_correct {T ro} monl%mlist.
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
Compute (monl_is_correct (3☓5 + 5☓2 + 8☓)).
Compute (monl_is_correct (3☓5 + 5☓2 + 8☓7)).
Compute (mk_polyn (3☓5 + 5☓2 + 8☓) eq_refl).
Compute (monl_add (m_list (3☓5 + 5☓2 + 8☓)) (m_list (3☓5 + 5☓2 + 8☓))).
Compute (monl_add (m_list (3☓5 + 5☓2 + 8☓)) (m_list (3☓5 + (-5)☓2 + 8☓))).
*)

Definition deg_non_incr (ma mb : monom T) := (mdeg mb <=? mdeg ma).

Theorem monl_add_is_sorted : ∀ pa pb,
  sorted deg_non_incr (monl_add (m_list (monl pa)) (m_list (monl pb))).
Proof.
intros.
destruct pa as ((la), Hlac).
destruct pb as ((lb), Hlbc).
move lb before la; cbn.
unfold monl_is_correct in Hlac, Hlbc.
cbn in Hlac, Hlbc.
apply Bool.andb_true_iff in Hlac, Hlbc.
destruct Hlac as (Hsa, _).
destruct Hlbc as (Hsb, _).
rewrite fold_sorted in Hsa, Hsb.
remember (length la + length lb) as it eqn:Hit; symmetry in Hit.
apply Nat.eq_le_incl in Hit.
assert (Htr : transitive (λ x y : monom T, negb (mdeg x <=? mdeg y))). {
  intros a b c Hab Hbc.
  apply Bool.negb_true_iff in Hab, Hbc.
  apply Bool.negb_true_iff.
  apply Nat.leb_gt in Hab, Hbc.
  apply Nat.leb_gt.
  now transitivity (mdeg b).
}
assert (Htr' : transitive deg_non_incr). {
  unfold deg_non_incr.
  intros a b c Hab Hbc.
  apply Nat.leb_le in Hab, Hbc.
  apply Nat.leb_le.
  now transitivity (mdeg b).
}
revert la lb Hsa Hsb Hit.
induction it; intros; [ easy | cbn ].
destruct la as [| (mac, mad)]. {
  cbn in Hit; clear Hsa.
  destruct lb as [| mb]; [ easy | cbn ].
  apply sorted_cons_iff in Hsb; [ | easy ].
  apply sorted_cons_iff; [ easy | ].
  destruct Hsb as (Hs & Hmb).
  unfold deg_non_incr.
  split. {
    clear mb Hmb Hit.
    induction lb as [| mb]; [ easy | ].
    apply sorted_cons_iff in Hs; [ | easy ].
    apply sorted_cons_iff; [ easy | ].
    destruct Hs as (Hs & Hmb).
    specialize (IHlb Hs).
    split; [ easy | ].
    intros mc Hmc.
    specialize (Hmb _ Hmc).
    apply Bool.negb_true_iff in Hmb.
    apply Nat.leb_gt, Nat.lt_le_incl in Hmb.
    now apply Nat.leb_le.
  }
  intros mc Hmc.
  specialize (Hmb _ Hmc).
  apply Bool.negb_true_iff in Hmb.
  apply Nat.leb_gt, Nat.lt_le_incl in Hmb.
  now apply Nat.leb_le.
}
destruct lb as [| (mbc, mbd)]. {
  cbn in Hit; clear Hsb.
  apply sorted_cons_iff in Hsa; [ | easy ].
  apply sorted_cons_iff; [ easy | ].
  destruct Hsa as (Hsa & Hma).
  unfold deg_non_incr.
  cbn in Hma |-*.
  split. {
    clear Hma Hit.
    induction la as [| ma]; [ easy | ].
    apply sorted_cons_iff in Hsa; [ | easy ].
    apply sorted_cons_iff; [ easy | ].
    destruct Hsa as (Hsa & Hma).
    specialize (IHla Hsa).
    split; [ easy | ].
    intros mc Hmc.
    specialize (Hma _ Hmc).
    apply Bool.negb_true_iff in Hma.
    apply Nat.leb_gt, Nat.lt_le_incl in Hma.
    now apply Nat.leb_le.
  }
  intros mc Hmc.
  specialize (Hma _ Hmc).
  apply Bool.negb_true_iff in Hma.
  apply Nat.leb_gt, Nat.lt_le_incl in Hma.
  now apply Nat.leb_le.
}
destruct (le_dec mad mbd) as [Habd| Habd]. {
  apply sorted_cons_iff in Hsa; [ | easy ].
  apply sorted_cons_iff in Hsb; [ | easy ].
  apply sorted_cons_iff; [ easy | ].
  destruct Hsa as (Hsa & Hma).
  destruct Hsb as (Hsb & Hmb).
  move Hsb before Hsa.
  cbn in Hit.
  rewrite Nat.add_succ_r in Hit.
  apply Nat.succ_le_mono in Hit.
  split. {
    destruct it; [ easy | cbn ].
    destruct lb as [| (mbc2, mbd2)]. {
      apply sorted_cons_iff; [ easy | cbn ].
...

Theorem monl_norm_is_correct : ∀ s (ss : sorted deg_non_incr s),
  monl_is_correct (mk_mlist (monl_norm s)) = true.
...

Print polyn.

Definition polyn_add p1 p2 :=
  let s := monl_add (m_list (monl p1)) (m_list (monl p2)) in
  let ss := monl_add_is_sorted p1 p2 in
  mk_polyn (mk_mlist (monl_norm s)) (monl_norm_is_correct ss).

(*
End a.
Arguments monl_add {T} la%list lb%list.
Arguments monl_is_correct {T ro} monl%mlist.
About polyn_add.
Arguments polyn_add {T ro rp Heb} p1%P p2%P.
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
Compute (mk_polyn (3☓5 + 5☓2 + 8☓) eq_refl).
Compute
  (polyn_add
     (mk_polyn (3☓5 + 5☓2 + 8☓) eq_refl)
     (mk_polyn (3☓5 + 5☓2 + 8☓) eq_refl)).
Compute
  (polyn_add
     (mk_polyn (3☓5 + 5☓2 + 8☓) eq_refl)
     (mk_polyn (3☓5 + (-5)☓2 + 8☓) eq_refl)).
*)

...

(* old version *)

Fixpoint monl_add it al1 al2 :=
  match it with
  | 0 => []
  | S it' =>
      match al1 with
      | [] => al2
      | Mon c1 d1 :: bl1 =>
          match al2 with
          | [] => al1
          | Mon c2 d2 :: bl2 =>
              match Nat.compare d1 d2 with
              | Eq =>
                  let c := (c1 + c2)%F in
                  if (c =? 0)%F then monl_add it' bl1 bl2
                  else Mon c d1 :: monl_add it' bl1 bl2
              | Lt => Mon c2 d2 :: monl_add it' al1 bl2
              | Gt => Mon c1 d1 :: monl_add it' bl1 al2
              end
          end
      end
  end.

Definition monl_degree {T} (ml : list (monom T)) :=
  match ml with
  | m :: _ => mdeg m
  | [] => 0 (* should be -1 *)
  end.

Definition degree p := monl_degree (p_list (monl p)).

Arguments monl_add it%nat al1%list al2%list.

(*
End a.
Arguments monl_add {T ro} it%nat al1%list al2%list.
Arguments monl_is_correct {T ro} monl%plist.
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
Compute (monl_is_correct (3☓5 + 5☓2 + 8☓)).
Compute (monl_is_correct (3☓5 + 5☓2 + 8☓7)).
Compute (mk_polyn (3☓5 + 5☓2 + 8☓) eq_refl).
Compute (monl_add 50 (p_list (3☓5 + 5☓2 + 8☓)) (p_list (3☓5 + 5☓2 + 8☓))).
Compute (monl_add 50 (p_list (3☓5 + 5☓2 + 8☓)) (p_list (3☓5 + (-5)☓2 + 8☓))).
*)

Theorem polyn_add_is_correct : ∀ p1 p2,
  let it := max (degree p1) (degree p2) in
  monl_is_correct
    (mk_plist (monl_add it (p_list (monl p1)) (p_list (monl p2)))) = true.
Proof.
intros.
subst it.
unfold monl_is_correct; cbn.
apply Bool.andb_true_iff.
destruct p1 as ((l1), p1).
destruct p2 as ((l2), p2).
move l2 before l1.
unfold degree; cbn.
unfold monl_is_correct in p1, p2.
cbn in p1,p2.
apply Bool.andb_true_iff in p1, p2.
destruct p1 as (Hs1, Hc1).
destruct p2 as (Hs2, Hc2).
move Hs2 before Hs1.
remember (max (monl_degree l1) (monl_degree l2)) as it eqn:Hit.
symmetry in Hit.
rewrite fold_sorted in Hs1, Hs2 |-*.
assert (Htr : transitive (λ x y : monom T, negb (mdeg x <=? mdeg y))). {
  intros a b c Hab Hbc.
  apply Bool.negb_true_iff in Hab, Hbc.
  apply Bool.negb_true_iff.
  apply Nat.leb_gt in Hab, Hbc.
  apply Nat.leb_gt.
  now transitivity (mdeg b).
}
split. {
  apply Nat.eq_le_incl in Hit.
  clear Hc1 Hc2.
  revert l1 l2 Hs1 Hs2 Hit.
  induction it; intros; [ easy | cbn ].
  destruct l1 as [| (c1, d1)]; [ easy | ].
  destruct l2 as [| (c2, d2)]; [ easy | ].
  cbn in Hit.
  apply sorted_cons_iff in Hs1; [ | easy ].
  apply sorted_cons_iff in Hs2; [ | easy ].
  cbn in Hs1, Hs2.
  destruct Hs1 as (Hs1, Hm1).
  destruct Hs2 as (Hs2, Hm2).
  move Hs2 before Hs1.
  assert (Hm12 : max (monl_degree l1) (monl_degree l2) ≤ it). {
    destruct l1 as [| m1]; cbn. {
      destruct l2 as [| m2]; [ easy | cbn ].
      specialize (Hm2 _ (or_introl eq_refl)).
      apply Bool.negb_true_iff, Nat.leb_gt in Hm2.
      flia Hm2 Hit.
    }
    destruct l2 as [| m2]; cbn. {
      rewrite Nat.max_0_r.
      specialize (Hm1 _ (or_introl eq_refl)).
      apply Bool.negb_true_iff, Nat.leb_gt in Hm1.
      flia Hm1 Hit.
    }
    specialize (Hm1 _ (or_introl eq_refl)).
    specialize (Hm2 _ (or_introl eq_refl)).
    apply Bool.negb_true_iff, Nat.leb_gt in Hm1, Hm2.
    flia Hm1 Hm2 Hit.
  }
  move c2 before c1; move d2 before d1.
  remember (d1 ?= d2) as c eqn:Hc; symmetry in Hc.
  destruct c. {
    apply Nat.compare_eq_iff in Hc; subst d2.
    move Hm2 before Hm1.
    rewrite Nat.max_id in Hit.
    remember (c1 + c2 =? 0)%F as ccz eqn:Hccz; symmetry in Hccz.
    destruct ccz; [ now apply IHit | ].
    apply sorted_cons_iff; [ easy | ].
    split; [ now apply IHit | ].
    intros m Hm; cbn.
    apply Bool.negb_true_iff, Nat.leb_gt.
    destruct l1 as [| m1]. {
      destruct it; [ easy | cbn in Hm ].
      specialize (Hm2 _ Hm).
      now apply Bool.negb_true_iff, Nat.leb_gt in Hm2.
    }
    destruct l2 as [| m2]. {
      destruct it; [ easy | cbn in Hm ].
      destruct m1 as (c1', d1').
      specialize (Hm1 _ Hm).
      now apply Bool.negb_true_iff, Nat.leb_gt in Hm1.
    }
    destruct it; [ easy | ].
    cbn in Hm.
    destruct m1 as (c1', d1').
    destruct m2 as (c2', d2').
    cbn in Hm12.
    (* bon, preuve un peu trop longue, mais peut-être faisable quand
       même ; cependant, je vais essayer plutôt de programmer mon
       truc différemment en séparant l'addition de la normalisation *)
...
Print mdeg.
Print monl_degree.
Search (sorted _ (_ :: _)).
...
cbn in Hc1.
Search (is_sorted _ (_ :: _)).
Search (sorted _ (_ :: _)).
        cbn in Hs1.
...
Search ((_ =? _)%F = true).
specialize (@rngl_eqb_eq) as H1.
specialize (H1 T ro rp Heb).
apply H1 in Hccz.
      apply rngl_
...

Definition polyn_add p1 p2 :=
  let it := max (degree p1) (degree p2) in
  mk_polyn (mk_plist (monl_add it (p_list (monl p1)) (p_list (monl p2))))
    (polyn_add_is_correct p1 p2).

...

Compute
  (polyn_add
     (mk_polyn (3☓5 + 5☓2 + 8☓) eq_refl)
     (mk_polyn (3☓5 + 5☓2 + 8☓) eq_refl)).
Compute
  (polyn_add
     (mk_polyn (3☓5 + 5☓2 + 8☓) eq_refl)
     (mk_polyn (3☓5 + 5☓ + 8☓0) eq_refl)).

...

(* old version *)

Record polyn T {ro : ring_like_op T} := mk_polyn
  { lap : list (T * nat);
    lap_prop : last_lap_neq_0 lap }.
...

(*
Module ListNotations.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : list_scope.
End ListNotations.
*)

Print list.

(**)

Declare Scope plist_scope.
Inductive plist (A : Type) : Type :=  pnil : plist A | pcons : A → plist A → plist A.
Arguments pnil {A}%plist_scope.
Arguments pcons {A}%plist_scope a l%plist_scope.

Open Scope plist_scope.

Module PlistNotations.
Notation "'[:' ':]'" := pnil (format "[: :]") : plist_scope.
Notation "'[:' x ':]'" := (pcons x pnil) : plist_scope.
Notation "'[:' x ; y ; .. ; z ':]'" :=  (pcons x (pcons y .. (pcons z pnil) ..)) : plist_scope.
End PlistNotations.

Import PlistNotations.

Compute [].
Compute nil.
Compute [3].

Compute pnil.
Compute ([: :] ).

Compute (pcons 3 pnil).
Compute [: 3;4 :].

About list.
About plist.

...

Module MyListNotations.
Notation "'[' ']'" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : list_scope.
End MyListNotations.

Import MyListNotations.

Compute nil.
Compute ([])%list.

...

Pour la notation des polynômes, par exemple pour afficher 3x2-2x+5
comme, mettons 3ⓧ^2-2ⓧ+5, voir comment s'affichent les notations
des listes, par exemple [5;-2;3] dans la librairie de Coq.
ListNotations

...

(* old version *)

(* (lap : list as polynomial) *)
(* e.g. polynomial ax²+bx+c is implemented by the list [c;b;a] *)
Definition last_lap_neq_0 T {ro : ring_like_op T} (lap : list T) :=
  (last lap 1 ≠? 0)%F = true.

Record polyn T {ro : ring_like_op T} := mk_polyn
  { lap : list T;
    lap_prop : last_lap_neq_0 lap }.

Arguments polyn T {ro}.
Arguments mk_polyn {T ro} lap%list.
Arguments lap {T ro}.

Section a.

Context {T : Type}.
Context (ro : ring_like_op T).
Context (rp : ring_like_prop T).
Context {Heb : rngl_has_eqb = true}.
Context {H10 : rngl_has_1_neq_0 = true}.

Definition polyn_eqb (eqb : T → _) (P Q : polyn T) :=
  list_eqv eqb (lap P) (lap Q).

(* polyn_eqb is an equality *)

Theorem polyn_eqb_eq : ∀ (eqb : T → T → bool),
  equality eqb →
  ∀ (P Q : polyn T),
  polyn_eqb eqb P Q = true ↔ P = Q.
Proof.
intros * Heqb *.
split; intros Hpq. {
  unfold polyn_eqb in Hpq.
  apply list_eqb_eq in Hpq; [ | easy ].
  destruct P as (P, Pprop).
  destruct Q as (Q, Qprop).
  cbn in Hpq; cbn.
  destruct Hpq.
  f_equal.
  apply (Eqdep_dec.UIP_dec Bool.bool_dec).
} {
  subst Q.
  now apply list_eqb_eq.
}
Qed.

Theorem lap_1_0_prop : last_lap_neq_0 [].
Proof.
apply Bool.negb_true_iff.
apply (rngl_eqb_neq Heb).
apply (rngl_1_neq_0 H10).
Qed.

Definition polyn_zero := mk_polyn [] lap_1_0_prop.
Definition polyn_one := mk_polyn [1%F] lap_1_0_prop.

(* normalization *)

Fixpoint strip_0s la :=
  match la with
  | [] => []
  | a :: la' => if (a =? 0)%F then strip_0s la' else la
  end.

Lemma strip_0s_app : ∀ la lb,
  strip_0s (la ++ lb) =
  match strip_0s la with
  | [] => strip_0s lb
  | lc => lc ++ lb
  end.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct (a =? 0)%F; [ apply IHla | easy ].
Qed.

Definition lap_norm la := rev (strip_0s (rev la)).

Theorem polyn_norm_prop : ∀ la, last_lap_neq_0 (lap_norm la).
Proof.
intros.
unfold last_lap_neq_0, lap_norm.
induction la as [| a]; cbn. {
  apply Bool.negb_true_iff, (rngl_eqb_neq Heb).
  now apply rngl_1_neq_0.
}
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]; cbn. {
  remember (a =? 0)%F as az eqn:Haz; symmetry in Haz.
  destruct az; [ easy | cbn ].
  now apply Bool.negb_true_iff.
}
cbn in IHla.
now rewrite last_last in IHla |-*.
Qed.

Definition polyn_norm la :=
  mk_polyn (lap_norm la) (polyn_norm_prop la).

(* addition *)

Fixpoint lap_add al1 al2 :=
  match al1 with
  | [] => al2
  | a1 :: bl1 =>
      match al2 with
      | [] => al1
      | a2 :: bl2 => (a1 + a2)%F :: lap_add bl1 bl2
      end
  end.

Definition lap_opp la := List.map rngl_opp la.
Definition lap_sub la lb := lap_add la (lap_opp lb).

Definition polyn_add p1 p2 := polyn_norm (lap_add (lap p1) (lap p2)).
Definition polyn_opp pol := polyn_norm (lap_opp (lap pol)).
Definition polyn_sub p1 p2 := polyn_add p1 (polyn_opp p2).

(* multiplication *)

Fixpoint lap_convol_mul al1 al2 i len :=
  match len with
  | O => []
  | S len1 =>
      (∑ (j = 0, i), List.nth j al1 0 * List.nth (i - j) al2 0)%F ::
      lap_convol_mul al1 al2 (S i) len1
  end.

Definition lap_mul la lb :=
  match la with
  | [] => []
  | _ =>
      match lb with
      | [] => []
      | _ => lap_convol_mul la lb 0 (length la + length lb - 1)
      end
  end.

Definition polyn_mul p1 p2 := polyn_norm (lap_mul (lap p1) (lap p2)).

(* monomial a * x^i *)

Definition lap_monom a i := repeat 0%F i ++ [a].

Theorem monom_norm : ∀ a i, last_lap_neq_0 (lap_monom a i).
...

Definition monom a i := mk_polyn (lap_monom a i) 42.

...

(* monomial x^i (to be removed) *)

Theorem monom_norm : ∀ i, last_lap_neq_0 (repeat 0%F i ++ [1%F]).
Proof.
intros.
unfold last_lap_neq_0.
rewrite last_last.
apply Bool.negb_true_iff, (rngl_eqb_neq Heb).
now apply rngl_1_neq_0.
Qed.

Definition lap_monom i := repeat 0%F i ++ [1%F].
Definition monom i := mk_polyn (lap_monom i) (monom_norm i).

End a.

Arguments lap_add {T ro} (al1 al2)%list.
Arguments lap_monom {T ro} i%nat.
Arguments lap_mul {T ro} (la lb)%list.
Arguments monom {T ro rp Heb H10} i%nat.
Arguments monom_norm {T ro rp} {Heb H10 i}.
Arguments polyn_norm_prop {T ro rp} {Heb H10 la}.

(*
Require Import ZArith RnglAlg.Zrl.
Open Scope Z_scope.
Compute (lap_monom 1).
Compute (lap_monom 3).
Global Existing Instance Z_ring_like_prop.
Compute (monom 1).
Compute (monom 3).
*)
(*
Require Import NatRingLike.
Compute (lap_monom 1).
Compute (monom 1).
About monom_norm.
*)

Declare Scope lap_scope.
Delimit Scope lap_scope with lap.
(*
Notation "1" := [1%F] : lap_scope.
*)
Notation "- a" := (lap_opp a) : lap_scope.
Notation "a + b" := (lap_add a b) : lap_scope.
Notation "a - b" := (lap_sub a b) : lap_scope.
Notation "a * b" := (lap_mul a b) : lap_scope.
(*
Notation "a ^ b" := (lap_power a b) : lap_scope.
*)

Declare Scope poly_scope.
Delimit Scope poly_scope with pol.

Arguments polyn_add {T ro rp} {Heb H10} (p1 p2)%pol.
Arguments polyn_sub {T ro rp} {Heb H10} (p1 p2)%pol.

Notation "a + b" := (polyn_add a b) : poly_scope.
Notation "a - b" := (polyn_sub a b) : poly_scope.
Notation "a * b" := (polyn_mul a b) : poly_scope.
Notation "'ⓧ' ^ a" := (monom a) (at level 30, format "'ⓧ' ^ a") : poly_scope.
Notation "'ⓧ'" := (monom 1) (at level 30, format "'ⓧ'") : poly_scope.

Require Import ZArith RnglAlg.Zrl.
Global Existing Instance Z_ring_like_prop.
Open Scope Z_scope.
Compute (lap_add [1;2;3] [4;5;6]).
Check (lap_add [1;2;3] [4;5;6]).
Compute ([1;2;3] + [4;5;6])%lap.
(* (x-1)(x+1) *)
Compute ([1; 1] * [-1; 1])%lap.
Compute (monom 3).
Compute (ⓧ^4)%pol.
Compute (ⓧ^4+ⓧ)%pol.
Compute (ⓧ^4-ⓧ)%pol.
Compute (3*ⓧ^4)%pol.
...
Compute (ⓧ^4-ⓧ+2%F)%pol.
Compute (ⓧ)%pol.
(* ah bin zut, non seulement ça n'affiche pas la notation, mais
   ça affiche le long Z_ring_like_prop *)
(* peut-être que, finalement, faut que je laisse tomber ce champ
   "lap_prop" dans le type polyn ? *)

...

Definition list_nth_def_0 {α} {R : ring α} n l := List.nth n l 0%Rng.

Declare Scope poly_scope.
Delimit Scope poly_scope with pol.
Notation "0" := poly_zero : poly_scope.
Notation "1" := poly_one : poly_scope.
Notation "- a" := (poly_opp a) : poly_scope.
Notation "a + b" := (poly_add a b) : poly_scope.
Notation "a - b" := (poly_sub a b) : poly_scope.
Notation "a * b" := (poly_mul a b) : poly_scope.
Notation "'ⓧ' ^ a" := (xpow a) (at level 30, format "'ⓧ' ^ a") : poly_scope.
Notation "'ⓧ'" := (xpow 1) (at level 30, format "'ⓧ'") : poly_scope.

Check polyn_mul.

...

(* euclidean division *)

Definition polyn_div p1 p2 :=
...

(* ring-like *)

Definition polyn_ring_like_op : ring_like_op (polyn T) :=
  {| rngl_zero := polyn_zero;
     rngl_one := polyn_one;
     rngl_add := polyn_add;
     rngl_mul := polyn_mul;
     rngl_opt_opp := Some polyn_opp;
     rngl_opt_inv := None;
     rngl_opt_sous := Some polyn_sub;
     rngl_opt_quot := Some Nat.div;
     rngl_opt_eqb := Some Nat.eqb;
     rngl_le := Nat.le |}.

(* allows to use ring-like theorems on polynomials *)
Canonical Structure polyn_ring_like_op.

(*
Compute (@lap_norm Z Z_ring [3; 4; 0; 5; 0; 0; 0]%Z).
*)
(**)

(*
Compute (@poly_add Z Z_ring (poly_norm [3;4;5]%Z) (poly_norm [2;3;-4;5]%Z)).
Compute (@poly_add Z Z_ring (poly_norm [3;4;5]%Z) (poly_norm [2;3;-5]%Z)).
*)

...

(*
Compute (@lap_mul Z Z_ring [3;4;5]%Z [2;3;-4;5]%Z).
Compute (@poly_mul Z Z_ring (poly_norm [3;4;5]%Z) (poly_norm [2;3;-4;5]%Z)).
*)

(* power *)

Fixpoint lap_power {α} {r : ring α} la n :=
  match n with
  | O => [1%Rng]
  | S m => lap_mul la (lap_power la m)
  end.

Definition poly_power {A} {rng : ring A} pol n :=
  poly_norm (lap_power (lap pol) n).

(*
Compute (@poly_power Z Z_ring (poly_norm [1; -1]%Z) 4).
*)

(* composition *)

Definition lap_compose {α} {r : ring α} la lb :=
  List.fold_right (λ c accu, lap_add (lap_mul accu lb) [c]) [] la.

Definition lap_compose2 {α} {r : ring α} la lb :=
  List.fold_right
    (λ i accu,
     lap_add accu (lap_mul [List.nth i la 0] (lap_power lb i)))%Rng
    [] (List.seq 0 (length la)).

(* *)

Fixpoint list_pad {α} n (zero : α) rem :=
  match n with
  | O => rem
  | S n1 => zero :: list_pad n1 zero rem
  end.

Theorem xpow_norm {A} {rng : ring A} : ∀ i,
  rng_eqb (last (repeat 0%Rng i ++ [1%Rng]) 1%Rng) 0%Rng = false.
Proof.
intros.
rewrite List_last_app.
unfold rng_eqb.
destruct (rng_eq_dec 1 0) as [H| H]; [ | easy ].
now apply rng_1_neq_0 in H.
Qed.

Definition xpow {α} {r : ring α} i :=
  mkpoly (repeat 0%Rng i ++ [1%Rng]) (xpow_norm i).

Declare Scope lap_scope.
Delimit Scope lap_scope with lap.
Notation "1" := [1%Rng] : lap_scope.
Notation "- a" := (lap_opp a) : lap_scope.
Notation "a + b" := (lap_add a b) : lap_scope.
Notation "a - b" := (lap_sub a b) : lap_scope.
Notation "a * b" := (lap_mul a b) : lap_scope.
Notation "a ^ b" := (lap_power a b) : lap_scope.

Definition list_nth_def_0 {α} {R : ring α} n l := List.nth n l 0%Rng.

Declare Scope poly_scope.
Delimit Scope poly_scope with pol.
Notation "0" := poly_zero : poly_scope.
Notation "1" := poly_one : poly_scope.
Notation "- a" := (poly_opp a) : poly_scope.
Notation "a + b" := (poly_add a b) : poly_scope.
Notation "a - b" := (poly_sub a b) : poly_scope.
Notation "a * b" := (poly_mul a b) : poly_scope.
Notation "'ⓧ' ^ a" := (xpow a) (at level 30, format "'ⓧ' ^ a") : poly_scope.
Notation "'ⓧ'" := (xpow 1) (at level 30, format "'ⓧ'") : poly_scope.

(* *)

Theorem lap_convol_mul_comm : ∀ α (R : ring α) l1 l2 i len,
  lap_convol_mul l1 l2 i len = lap_convol_mul l2 l1 i len.
Proof.
intros α R l1 l2 i len.
revert i.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen; f_equal.
rewrite summation_rtl.
apply summation_compat; intros j (_, Hj).
rewrite Nat.add_0_r.
rewrite rng_mul_comm.
apply rng_mul_compat; [ idtac | reflexivity ].
rewrite Nat_sub_sub_distr; [ idtac | easy ].
rewrite Nat.sub_diag, Nat.add_0_l; reflexivity.
Qed.

Theorem lap_convol_mul_nil_l : ∀ α (R : ring α) l i len,
  lap_norm (lap_convol_mul [] l i len) = [].
Proof.
intros α R l i len.
unfold lap_norm.
revert i.
induction len; intros; [ reflexivity | ].
cbn - [ summation ].
rewrite all_0_summation_0. {
  rewrite strip_0s_app; cbn.
  specialize (IHlen (S i)).
  apply List_eq_rev_nil in IHlen.
  rewrite IHlen.
  now destruct (rng_eq_dec 0%Rng 0%Rng).
}
intros k (_, Hk).
now rewrite match_id, rng_mul_0_l.
Qed.

Theorem lap_convol_mul_nil_r : ∀ α (R : ring α) l i len,
  lap_norm (lap_convol_mul l [] i len) = [].
Proof.
intros α R l i len.
rewrite lap_convol_mul_comm.
apply lap_convol_mul_nil_l.
Qed.

Theorem list_nth_lap_eq : ∀ α (r : ring α) la lb,
  (∀ i, (List.nth i la 0 = List.nth i lb 0)%Rng)
  → lap_norm la = lap_norm lb.
Proof.
intros α r la lb Hi.
unfold lap_norm; f_equal.
revert lb Hi.
induction la as [| a]; intros. {
  induction lb as [| b]; [ reflexivity | ].
  specialize (Hi 0) as H; cbn in H.
  subst b; cbn.
  rewrite strip_0s_app; cbn.
  remember (strip_0s (rev lb)) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as [| c]; [ now destruct (rng_eq_dec _ _) | ].
  assert (H : lap_norm [] = lap_norm lb). {
    unfold lap_norm; cbn.
    cbn in IHlb.
    change (rev [] = rev (strip_0s (rev lb))).
    f_equal.
    rewrite Hlc.
    apply IHlb.
    intros i; cbn; rewrite match_id.
    now specialize (Hi (S i)); cbn in Hi.
  }
  cbn in H.
  unfold lap_norm in H.
  rewrite Hlc in H.
  symmetry in H.
  now apply List_eq_rev_nil in H.
} {
  cbn.
  rewrite strip_0s_app.
  remember (strip_0s (rev la)) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as [| c]. {
    assert (Hla : ∀ i, nth i la 0%Rng = 0%Rng). {
      intros i.
      clear - Hlc.
      revert i.
      induction la as [| a]; intros; [ now cbn; rewrite match_id | cbn ].
      destruct i. {
        cbn in Hlc.
        rewrite strip_0s_app in Hlc; cbn in Hlc.
        remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
        destruct lb as [| b]; [ now destruct (rng_eq_dec a 0%Rng) | easy ].
      }
      apply IHla.
      cbn in Hlc.
      rewrite strip_0s_app in Hlc; cbn in Hlc.
      remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
      destruct lb as [| b]; [ now destruct (rng_eq_dec a 0%Rng) | easy ].
    }
    cbn.
    destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]. {
      assert (Hlb : ∀ i, nth i lb 0%Rng = 0%Rng). {
        intros.
        rewrite <- Hi; cbn.
        destruct i; [ easy | ].
        apply Hla.
      }
      clear - Hlb.
      induction lb as [| b]; [ easy | cbn ].
      specialize (Hlb 0) as H1; cbn in H1; subst b.
      rewrite strip_0s_app; cbn.
      rewrite <- IHlb; [ now destruct (rng_eq_dec 0%Rng 0%Rng) | ].
      intros i.
      now specialize (Hlb (S i)).
    }
    destruct lb as [| b]; [ now specialize (Hi 0); cbn in Hi | cbn ].
    rewrite strip_0s_app; cbn.
    remember (strip_0s (rev lb)) as ld eqn:Hld; symmetry in Hld.
    destruct ld as [| d]. {
      destruct (rng_eq_dec b 0%Rng) as [Hbz| Hbz]. {
        subst b.
        now specialize (Hi 0).
      }
      f_equal.
      now specialize (Hi 0).
    }
    specialize (IHla lb).
    assert (H : ∀ i : nat, nth i la 0%Rng = nth i lb 0%Rng). {
      intros i.
      now specialize (Hi (S i)); cbn in Hi.
    }
    specialize (IHla H); clear H.
    now rewrite Hld in IHla.
  }
  destruct lb as [| b]. {
    specialize (IHla []).
    assert (H : ∀ i : nat, nth i la 0%Rng = nth i [] 0%Rng). {
      intros i; cbn; rewrite match_id.
      now specialize (Hi (S i)).
    }
    now specialize (IHla H).
  }
  cbn.
  rewrite strip_0s_app; cbn.
  remember (strip_0s (rev lb)) as ld eqn:Hld; symmetry in Hld.
  destruct ld as [| d]. {
    destruct (rng_eq_dec b 0%Rng) as [Hbz| Hbz]. {
      subst b.
      specialize (IHla lb).
      assert (H : ∀ i : nat, nth i la 0%Rng = nth i lb 0%Rng). {
        intros i.
        now specialize (Hi (S i)); cbn in Hi.
      }
      specialize (IHla H); clear H.
      now rewrite Hld in IHla.
    }
    specialize (IHla lb).
    assert (H : ∀ i : nat, nth i la 0%Rng = nth i lb 0%Rng). {
      intros i.
      now specialize (Hi (S i)); cbn in Hi.
    }
    specialize (IHla H); clear H.
    now rewrite Hld in IHla.
  }
  specialize (Hi 0) as H1; cbn in H1; subst b.
  do 2 rewrite app_comm_cons; f_equal.
  rewrite <- Hld.
  apply IHla.
  now intros i; specialize (Hi (S i)).
}
Qed.

Theorem fold_lap_norm {A} {rng : ring A} :
  ∀ la, rev (strip_0s (rev la)) = lap_norm la.
Proof. easy. Qed.

Theorem lap_add_0_l {α} {r : ring α} : ∀ la, lap_add [] la = la.
Proof. easy. Qed.

Theorem lap_add_0_r {α} {r : ring α} : ∀ la, lap_add la [] = la.
Proof. intros; now destruct la. Qed.

Theorem poly_add_0_l {α} {r : ring α} : ∀ p, (0 + p)%pol = p.
Proof.
intros (la, lapr).
apply eq_poly_eq; cbn.
apply eq_poly_prop in lapr.
induction la as [| a]; [ easy | cbn ].
rewrite strip_0s_app.
rewrite <- (rev_involutive (strip_0s _)).
rewrite IHla; cbn. {
  remember (rev la) as lb eqn:Hlb; symmetry in Hlb.
  destruct lb as [| b]. {
    apply List_eq_rev_nil in Hlb; subst la.
    now destruct (rng_eq_dec a 0).
  }
  cbn.
  rewrite rev_app_distr; cbn; f_equal.
  now rewrite <- rev_involutive, Hlb.
} {
  destruct la as [| a2]; [ | easy ].
  apply rng_1_neq_0.
}
Qed.

Theorem lap_mul_0_l {α} {r : ring α} : ∀ la, lap_norm (lap_mul [] la) = [].
Proof. easy. Qed.

Theorem lap_mul_0_r {α} {r : ring α} : ∀ la, lap_norm (lap_mul la []) = [].
Proof. now intros; destruct la. Qed.

Section lap.

Context {α : Type}.
Context {r : ring α}.

Theorem strip_0s_idemp : ∀ la, strip_0s (strip_0s la) = strip_0s la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]; [ easy | cbn ].
now destruct (rng_eq_dec a 0%Rng).
Qed.

Theorem lap_norm_idemp : ∀ la, lap_norm (lap_norm la) = lap_norm la.
Proof.
intros.
unfold lap_norm.
rewrite rev_involutive.
now rewrite strip_0s_idemp.
Qed.

Theorem eq_lap_convol_mul_nil : ∀ la lb i len,
  lap_convol_mul la lb i len = [] → len = 0.
Proof. now intros; induction len. Qed.

(* addition theorems *)

Theorem lap_add_comm : ∀ al1 al2,
  lap_add al1 al2 = lap_add al2 al1.
Proof.
intros al1 al2.
revert al2.
induction al1; intros; [ now destruct al2 | ].
destruct al2; [ easy | cbn ].
now rewrite rng_add_comm, IHal1.
Qed.

Theorem poly_add_comm : ∀ a b, (a + b)%pol = (b + a)%pol.
Proof.
intros.
unfold "+"%pol.
now rewrite lap_add_comm.
Qed.

Theorem lap_add_norm_idemp_l : ∀ la lb,
  lap_norm (lap_norm la + lb)%lap = lap_norm (la + lb)%lap.
Proof.
intros.
unfold lap_norm; f_equal.
revert la.
induction lb as [| b]; intros. {
  do 2 rewrite lap_add_0_r.
  now rewrite rev_involutive, strip_0s_idemp.
}
cbn.
destruct la as [| a]; [ easy | cbn ].
do 2 rewrite strip_0s_app; cbn.
rewrite <- IHlb.
remember (strip_0s (rev la)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  cbn.
  destruct (rng_eq_dec a 0) as [Haz| Haz]. {
    subst a; rewrite rng_add_0_l; cbn.
    now rewrite strip_0s_app.
  }
  cbn.
  now rewrite strip_0s_app.
}
cbn.
rewrite rev_app_distr; cbn.
now rewrite strip_0s_app.
Qed.

Theorem lap_add_norm_idemp_r : ∀ la lb,
  lap_norm (la + lap_norm lb)%lap = lap_norm (la + lb)%lap.
Proof.
intros.
rewrite lap_add_comm, lap_add_norm_idemp_l.
now rewrite lap_add_comm.
Qed.

Theorem lap_add_assoc : ∀ al1 al2 al3,
  lap_add al1 (lap_add al2 al3) = lap_add (lap_add al1 al2) al3.
Proof.
intros al1 al2 al3.
revert al2 al3.
induction al1; intros; [ easy | ].
destruct al2; [ easy | cbn ].
destruct al3; [ easy | cbn ].
rewrite rng_add_assoc.
now rewrite IHal1.
Qed.

Theorem lap_add_add_swap : ∀ la lb lc,
  lap_add (lap_add la lb) lc = lap_add (lap_add la lc) lb.
Proof.
intros la lb lc.
do 2 rewrite <- lap_add_assoc.
now rewrite (lap_add_comm lb).
Qed.

Theorem poly_add_assoc : ∀ pa pb pc,
  (pa + (pb + pc) = (pa + pb) + pc)%pol.
Proof.
intros (la, lapr) (lb, lbpr) (lc, lcpr).
apply eq_poly_eq.
cbn - [ lap_norm ].
rewrite lap_add_norm_idemp_l.
rewrite lap_add_norm_idemp_r.
now rewrite lap_add_assoc.
Qed.

(* multiplication theorems *)

Theorem lap_mul_comm : ∀ a b, lap_mul a b = lap_mul b a.
Proof.
intros la lb.
unfold lap_mul.
destruct la as [| a]; [ now destruct lb | cbn ].
rewrite <- Nat.add_succ_comm; cbn.
rewrite (Nat.add_comm (length lb)).
now rewrite lap_convol_mul_comm.
Qed.

Theorem poly_mul_comm : ∀ pa pb, (pa * pb)%pol = (pb * pa)%pol.
Proof.
intros.
apply eq_poly_eq; cbn.
now rewrite lap_mul_comm.
Qed.

Theorem list_nth_lap_convol_mul_aux : ∀ la lb n i len,
  List.length la + List.length lb - 1 = (i + len)%nat
  → (List.nth n (lap_convol_mul la lb i len) 0%Rng =
     Σ (j = 0, n + i),
     List.nth j la 0 * List.nth (n + i - j) lb 0)%Rng.
Proof.
intros la lb n i len Hlen.
revert la lb i n Hlen.
induction len; intros.
 simpl.
 rewrite Nat.add_0_r in Hlen.
 rewrite all_0_summation_0; [ destruct n; reflexivity | idtac ].
 intros j (_, Hj).
 destruct (le_dec (length la) j) as [H1| H1].
  rewrite List.nth_overflow; [ idtac | assumption ].
  rewrite rng_mul_0_l; reflexivity.

  destruct (le_dec (length lb) (n + i - j)) as [H2| H2].
   rewrite rng_mul_comm.
   rewrite List.nth_overflow; [ idtac | assumption ].
   rewrite rng_mul_0_l; reflexivity.

   exfalso; apply H2; clear Hj H2.
   apply Nat.nle_gt in H1; subst i.
   flia H1.

 simpl.
 destruct n; [ reflexivity | idtac ].
 rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hlen.
 rewrite IHlen; [ idtac | assumption ].
 rewrite Nat.add_succ_r, <- Nat.add_succ_l; reflexivity.
Qed.

(* to be unified perhaps with list_nth_convol_mul below *)
Theorem list_nth_lap_convol_mul : ∀ la lb i len,
  len = length la + length lb - 1
  → (List.nth i (lap_convol_mul la lb 0 len) 0 =
     Σ (j = 0, i), List.nth j la 0 * List.nth (i - j) lb 0)%Rng.
Proof.
intros la lb i len Hlen.
symmetry in Hlen.
rewrite list_nth_lap_convol_mul_aux; [ idtac | assumption ].
rewrite Nat.add_0_r; reflexivity.
Qed.

Theorem summation_mul_list_nth_lap_convol_mul : ∀ la lb lc k,
  (Σ (i = 0, k),
     List.nth i la 0 *
     List.nth (k - i)
       (lap_convol_mul lb lc 0 (length lb + length lc - 1))
       0 =
   Σ (i = 0, k),
     List.nth i la 0 *
     Σ (j = 0, k - i),
       List.nth j lb 0 * List.nth (k - i - j) lc 0)%Rng.
Proof.
intros la lb lc k.
apply summation_compat; intros i (_, Hi).
f_equal.
rewrite list_nth_lap_convol_mul; reflexivity.
Qed.

Theorem summation_mul_list_nth_lap_convol_mul_2 : ∀ la lb lc k,
   (Σ (i = 0, k),
      List.nth i lc 0 *
      List.nth (k - i)
        (lap_convol_mul la lb 0 (length la + length lb - 1))  0 =
    Σ (i = 0, k),
      List.nth (k - i) lc 0 *
      Σ (j = 0, i),
        List.nth j la 0 * List.nth (i - j) lb 0)%Rng.
Proof.
intros la lb lc k.
rewrite summation_rtl.
apply summation_compat; intros i (_, Hi).
rewrite Nat.add_0_r.
f_equal.
rewrite Nat_sub_sub_distr; [ idtac | easy ].
rewrite Nat.sub_diag.
apply list_nth_lap_convol_mul; reflexivity.
Qed.

Lemma lap_norm_mul_assoc : ∀ la lb lc,
  lap_norm (la * (lb * lc))%lap = lap_norm (la * lb * lc)%lap.
Proof.
intros la lb lc.
symmetry; rewrite lap_mul_comm.
unfold lap_mul.
destruct lc as [| c]. {
  destruct la as [| a]; [ easy | now destruct lb ].
}
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | ].
move b before a; move c before b.
remember (a :: la) as la' eqn:Hla'.
remember (b :: lb) as lb' eqn:Hlb'.
remember (c :: lc) as lc' eqn:Hlc'.
apply list_nth_lap_eq; intros k.
remember (lap_convol_mul la' lb' 0 (length la' + length lb' - 1)) as ld
  eqn:Hld.
remember (lap_convol_mul lb' lc' 0 (length lb' + length lc' - 1)) as le
  eqn:Hle.
symmetry in Hld, Hle.
destruct ld as [| d]. {
  destruct le as [| e]; [ easy | cbn ].
  rewrite match_id.
  move e before c.
  apply eq_lap_convol_mul_nil in Hld.
  apply Nat.sub_0_le in Hld.
  remember (length la' + length lb') as len eqn:Hlen.
  symmetry in Hlen.
  destruct len. {
    apply Nat.eq_add_0 in Hlen.
    now subst la'.
  }
  destruct len; [ clear Hld | flia Hld ].
  apply Nat.eq_add_1 in Hlen.
  destruct Hlen as [Hlen| Hlen]; [ now rewrite Hlb' in Hlen | ].
  now rewrite Hla' in Hlen.
}
destruct le as [| e]. {
  cbn; rewrite match_id.
  move d before c.
  apply eq_lap_convol_mul_nil in Hle.
  apply Nat.sub_0_le in Hle.
  remember (length lb' + length lc') as len eqn:Hlen.
  symmetry in Hlen.
  destruct len. {
    apply Nat.eq_add_0 in Hlen.
    now subst lb'.
  }
  destruct len; [ clear Hle | flia Hle ].
  apply Nat.eq_add_1 in Hlen.
  destruct Hlen as [Hlen| Hlen]; [ now rewrite Hlc' in Hlen | ].
  now rewrite Hlb' in Hlen.
}
rewrite list_nth_lap_convol_mul; [ idtac | reflexivity ].
rewrite list_nth_lap_convol_mul; [ idtac | reflexivity ].
rewrite <- Hld, <- Hle.
rewrite summation_mul_list_nth_lap_convol_mul_2; symmetry.
rewrite summation_mul_list_nth_lap_convol_mul; symmetry.
rewrite <- summation_summation_mul_swap.
rewrite <- summation_summation_mul_swap.
rewrite summation_summation_exch.
rewrite summation_summation_shift.
apply summation_compat; intros i Hi.
apply summation_compat; intros j Hj.
rewrite rng_mul_comm, rng_mul_assoc.
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_comm, Nat.sub_add_distr.
reflexivity.
Qed.

Theorem eq_lap_norm_eq_length : ∀ la lb,
  lap_norm la = lap_norm lb
  → length la = length lb
  → la = lb.
Proof.
intros * Hll Hlen.
unfold lap_norm in Hll.
apply (f_equal (@rev α)) in Hll.
do 2 rewrite rev_involutive in Hll.
setoid_rewrite <- rev_length in Hlen.
enough (H : rev la = rev lb). {
  apply (f_equal (@rev α)) in H.
  now do 2 rewrite rev_involutive in H.
}
remember (rev la) as l; clear la Heql; rename l into la.
remember (rev lb) as l; clear lb Heql; rename l into lb.
revert la Hll Hlen.
induction lb as [| b]; intros. {
  now apply length_zero_iff_nil in Hlen.
}
destruct la as [| a]; [ easy | ].
cbn in Hll, Hlen.
apply Nat.succ_inj in Hlen.
destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]. {
  destruct (rng_eq_dec b 0%Rng) as [Hbz| Hbz]. {
    subst a b; f_equal.
    now apply IHlb.
  }
  exfalso; clear - Hbz Hll Hlen.
  assert (H : length la ≤ length lb) by flia Hlen.
  clear Hlen; rename H into Hlen.
  induction la as [| a]; [ easy | ].
  cbn in Hll.
  destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]. {
    cbn in Hlen.
    clear a Haz.
    apply IHla; [ easy | flia Hlen ].
  }
  rewrite Hll in Hlen; cbn in Hlen.
  flia Hlen.
}
destruct (rng_eq_dec b 0%Rng) as [Hbz| Hbz]. {
  exfalso; clear b Hbz.
  clear - Haz Hll Hlen.
  assert (H : length lb ≤ length la) by flia Hlen.
  clear Hlen; rename H into Hlen.
  induction lb as [| b]; [ easy | ].
  cbn in Hll.
  destruct (rng_eq_dec b 0%Rng) as [Hbz| Hbz]. {
    cbn in Hlen.
    clear b Hbz.
    apply IHlb; [ easy | flia Hlen ].
  }
  rewrite <- Hll in Hlen; cbn in Hlen.
  flia Hlen.
}
easy.
Qed.

Theorem lap_convol_mul_length : ∀ la lb i len,
  length (lap_convol_mul la lb i len) = len.
Proof.
intros.
revert la lb i.
induction len; intros; [ easy | ].
cbn.
now rewrite IHlen.
Qed.

Theorem lap_mul_assoc : ∀ la lb lc,
  (la * (lb * lc))%lap = ((la * lb) * lc)%lap.
Proof.
intros.
apply eq_lap_norm_eq_length; [ apply lap_norm_mul_assoc | ].
unfold "*"%lap.
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | ].
destruct lc as [| c]. {
  now destruct (lap_convol_mul _ _ _ _).
}
cbn.
do 4 (rewrite Nat.add_succ_r; cbn); f_equal.
do 2 rewrite rng_add_0_r.
do 4 rewrite lap_convol_mul_length.
apply Nat.add_assoc.
Qed.

Theorem lap_convol_mul_0_l : ∀ la lb i len,
  (∀ i, nth i la 0%Rng = 0%Rng)
  → lap_norm (lap_convol_mul la lb i len) = [].
Proof.
intros * Ha.
revert i.
induction len; intros; [ easy | ].
cbn - [ summation ].
rewrite strip_0s_app.
remember (strip_0s (rev _)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  rewrite all_0_summation_0. 2: {
    intros j Hj.
    now rewrite Ha, rng_mul_0_l.
  }
  cbn.
  now destruct (rng_eq_dec 0%Rng 0%Rng).
}
unfold lap_norm in IHlen.
specialize (IHlen (S i)).
rewrite Hlc in IHlen.
now apply List_eq_rev_nil in IHlen.
Qed.

Theorem all_0_all_rev_0 : ∀ la,
  (∀ i, nth i la 0%Rng = 0%Rng)
  ↔ (∀ i, nth i (rev la) 0%Rng = 0%Rng).
Proof.
intros *.
split; intros H i. {
  destruct (lt_dec i (length la)) as [Hila| Hila]. {
    rewrite rev_nth; [ apply H | easy ].
  }
  apply nth_overflow; rewrite rev_length; flia Hila.
} {
  destruct (lt_dec i (length la)) as [Hila| Hila]. {
    rewrite <- (rev_involutive la).
    rewrite rev_nth; [ apply H | now rewrite rev_length ].
  }
  apply nth_overflow; flia Hila.
}
Qed.

Theorem eq_strip_0s_nil : ∀ la,
  strip_0s la = [] ↔ ∀ i, nth i la 0%Rng = 0%Rng.
Proof.
intros.
split. {
  intros Hla *.
  revert i.
  induction la as [| a]; intros; [ now destruct i | cbn ].
  cbn in Hla.
  destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]; [ | easy ].
  destruct i; [ easy | ].
  now apply IHla.
} {
  intros Hla.
  induction la as [| a]; [ easy | cbn ].
  destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]. {
    apply IHla.
    intros i.
    now specialize (Hla (S i)).
  }
  now specialize (Hla 0).
}
Qed.

Theorem eq_strip_0s_rev_nil : ∀ la,
  strip_0s (rev la) = [] ↔ ∀ i, nth i la 0%Rng = 0%Rng.
Proof.
intros.
split; intros Hla. {
  apply all_0_all_rev_0.
  now apply eq_strip_0s_nil.
} {
  apply eq_strip_0s_nil.
  apply all_0_all_rev_0.
  now rewrite rev_involutive.
}
Qed.

Lemma lap_convol_mul_cons_with_0_l : ∀ a la lb i len,
  (∀ i, nth i la 0%Rng = 0%Rng)
  → lap_convol_mul (a :: la) lb i len = lap_convol_mul [a] lb i len.
Proof.
intros * Hla.
revert i.
induction len; intros; [ easy | ].
cbn - [ summation ].
f_equal; [ | apply IHlen ].
apply summation_compat.
intros j Hj.
destruct j; [ easy | ].
rewrite match_id.
now rewrite Hla.
Qed.

Theorem lap_convol_mul_succ : ∀ la lb i len,
  lap_convol_mul la lb i (S len) =
  lap_convol_mul la lb i len ++
    [Σ (j = 0, i + len),
     List.nth j la 0 * List.nth (i + len - j) lb 0]%Rng.
Proof.
intros.
cbn - [ summation ].
revert i.
induction len; intros. {
  now rewrite Nat.add_0_r.
}
cbn - [ summation ].
f_equal.
specialize (IHlen (S i)).
cbn - [ summation ] in IHlen.
rewrite Nat.add_succ_r.
apply IHlen.
Qed.

Theorem lap_norm_app_0_r : ∀ la lb,
  (∀ i, nth i lb 0%Rng = 0%Rng)
  → lap_norm la = lap_norm (la ++ lb).
Proof.
intros * Hlb.
unfold lap_norm; f_equal.
induction la as [| a]. {
  cbn; symmetry.
  induction lb as [| b]; [ easy | cbn ].
  rewrite strip_0s_app.
  rewrite IHlb. 2: {
    intros i.
    now specialize (Hlb (S i)).
  }
  specialize (Hlb 0); cbn in Hlb; rewrite Hlb; cbn.
  now destruct (rng_eq_dec 0%Rng 0%Rng).
}
cbn.
do 2 rewrite strip_0s_app.
now rewrite IHla.
Qed.

Theorem lap_convol_mul_more : ∀ n la lb i len,
  length la + length lb - 1 ≤ i + len
  → lap_norm (lap_convol_mul la lb i len) =
    lap_norm (lap_convol_mul la lb i (len + n)).
Proof.
intros.
induction n; [ rewrite Nat.add_0_r; reflexivity | idtac ].
rewrite Nat.add_succ_r.
rewrite lap_convol_mul_succ.
rewrite IHn.
apply lap_norm_app_0_r.
intros j.
rewrite all_0_summation_0. {
  destruct j; [ easy | now destruct j ].
}
clear j.
intros j (_, Hj).
apply rng_mul_eq_0.
destruct (le_dec (length la) j) as [H1| H1]. {
  now left; rewrite List.nth_overflow.
} {
  apply Nat.nle_gt in H1.
  destruct (le_dec (length lb) (i + (len + n) - j)) as [H2| H2]. {
    now right; rewrite nth_overflow.
  } {
    exfalso; apply H2; clear H2.
    flia H H1.
  }
}
Qed.

Theorem all_0_lap_norm_nil : ∀ la,
  (∀ i, nth i la 0%Rng = 0%Rng)
  → lap_norm la = [].
Proof.
intros * Hla.
induction la as [| a]; [ easy | cbn ].
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]. {
  cbn.
  destruct (rng_eq_dec a 0%Rng) as [H1| H1]; [ easy | exfalso ].
  now specialize (Hla 0); cbn in Hla.
}
exfalso.
assert (H : strip_0s (rev la) = []). {
  clear - Hla.
  apply eq_strip_0s_nil.
  intros i.
  destruct (lt_dec i (length la)) as [Hila| Hila]. {
    rewrite rev_nth; [ | easy ].
    specialize (Hla (S (length la - S i))).
    now cbn in Hla.
  }
  apply Nat.nlt_ge in Hila.
  rewrite nth_overflow; [ easy | now rewrite rev_length ].
}
now rewrite Hlb in H.
Qed.

Theorem lap_norm_repeat_0 : ∀ la,
  la = lap_norm la ++ repeat 0%Rng (length la - length (lap_norm la)).
Proof.
intros.
induction la as [| a]; [ easy | ].
cbn.
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]. {
  cbn.
  destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]. {
    cbn; subst a; f_equal.
    assert (H : lap_norm la = []). {
      apply all_0_lap_norm_nil.
      intros i.
      specialize (proj1 (eq_strip_0s_nil _) Hlb) as H1.
      destruct (lt_dec i (length la)) as [Hila| Hila]. {
        replace la with (rev (rev la)) by apply rev_involutive.
        rewrite rev_nth; rewrite rev_length; [ | easy ].
        apply H1.
      }
      apply Nat.nlt_ge in Hila.
      now rewrite nth_overflow.
    }
    rewrite H in IHla; cbn in IHla.
    now rewrite Nat.sub_0_r in IHla.
  } {
    cbn; f_equal.
    assert (H : lap_norm la = []). {
      apply all_0_lap_norm_nil.
      intros i.
      specialize (proj1 (eq_strip_0s_nil _) Hlb) as H1.
      destruct (lt_dec i (length la)) as [Hila| Hila]. {
        replace la with (rev (rev la)) by apply rev_involutive.
        rewrite rev_nth; rewrite rev_length; [ | easy ].
        apply H1.
      }
      apply Nat.nlt_ge in Hila.
      now rewrite nth_overflow.
    }
    now rewrite H in IHla; cbn in IHla.
  }
} {
  cbn.
  rewrite rev_app_distr; cbn; f_equal.
  replace (rev lb ++ [b]) with (rev (b :: lb)) by easy.
  rewrite <- Hlb.
  now rewrite fold_lap_norm.
}
Qed.

Theorem lap_convol_mul_app_rep_0_l : ∀ la lb i len n,
  lap_norm (lap_convol_mul (la ++ repeat 0%Rng n) lb i len) =
  lap_norm (lap_convol_mul la lb i len).
Proof.
intros.
revert la i len.
induction n; intros. {
  now cbn; rewrite app_nil_r.
}
cbn.
replace (0%Rng :: repeat 0%Rng n) with ([0%Rng] ++ repeat 0%Rng n) by easy.
rewrite app_assoc.
rewrite IHn; clear n IHn.
revert la i.
induction len; intros; [ easy | ].
cbn - [ summation ].
do 2 rewrite strip_0s_app.
rewrite <- (rev_involutive (strip_0s _)).
rewrite fold_lap_norm.
rewrite <- (rev_involutive (strip_0s (rev _))).
rewrite fold_lap_norm.
rewrite IHlen.
remember (rev (lap_norm _)) as lc eqn:Hlc; symmetry in Hlc.
f_equal.
destruct lc as [| c]. {
  apply List_eq_rev_nil in Hlc.
  f_equal; f_equal.
  apply summation_compat.
  intros j Hj.
  f_equal; clear.
  destruct (lt_dec j (length la)) as [Hjla| Hjla]. {
    now rewrite app_nth1.
  }
  apply Nat.nlt_ge in Hjla.
  rewrite (nth_overflow la); [ | easy ].
  rewrite app_nth2; [ | easy ].
  destruct (Nat.eq_dec j (length la)) as [Hjla2| Hjla2]. {
    now rewrite Hjla2, Nat.sub_diag.
  }
  rewrite nth_overflow; [ easy | cbn; flia Hjla Hjla2 ].
} {
  f_equal; f_equal.
  apply summation_compat.
  intros j Hj.
  f_equal; clear.
  destruct (lt_dec j (length la)) as [Hjla| Hjla]. {
    now rewrite app_nth1.
  }
  apply Nat.nlt_ge in Hjla.
  rewrite (nth_overflow la); [ | easy ].
  rewrite app_nth2; [ | easy ].
  destruct (Nat.eq_dec j (length la)) as [Hjla2| Hjla2]. {
    now rewrite Hjla2, Nat.sub_diag.
  }
  rewrite nth_overflow; [ easy | cbn; flia Hjla Hjla2 ].
}
Qed.

Theorem lap_norm_cons_norm : ∀ a la lb i len,
  length (a :: la) + length lb - 1 ≤ i + len
  → lap_norm (lap_convol_mul (a :: lap_norm la) lb i len) =
    lap_norm (lap_convol_mul (a :: la) lb i len).
Proof.
intros * Hlen.
rewrite (lap_norm_repeat_0 la) at 2.
rewrite app_comm_cons.
now rewrite lap_convol_mul_app_rep_0_l.
Qed.

Theorem lap_norm_length_le : ∀ la, length (lap_norm la) ≤ length la.
Proof.
intros.
rewrite (lap_norm_repeat_0 la) at 2.
rewrite app_length; flia.
Qed.

Theorem nth_lap_add : ∀ i la lb,
  nth i (la + lb)%lap 0%Rng = (nth i la 0 + nth i lb 0)%Rng.
Proof.
intros.
revert i lb.
induction la as [| a]; intros; cbn. {
  now rewrite match_id, rng_add_0_l.
}
destruct lb as [| b]; cbn. {
  now rewrite match_id, rng_add_0_r.
}
destruct i; [ easy | ].
apply IHla.
Qed.

Theorem lap_mul_norm_idemp_l : ∀ la lb,
  lap_norm (lap_norm la * lb)%lap = lap_norm (la * lb)%lap.
Proof.
intros.
unfold "*"%lap; cbn.
destruct la as [| a]; [ easy | cbn ].
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  cbn.
  destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]. {
    cbn.
    destruct lb as [| b]; [ easy | cbn ].
    rewrite lap_convol_mul_0_l; [ easy | ].
    intros i; cbn.
    destruct i; [ easy | ].
    specialize (proj1 (eq_strip_0s_nil _) Hlc) as H1.
    destruct (lt_dec i (length la)) as [Hil| Hil]. {
      specialize (H1 (length la - S i)).
      rewrite <- rev_length in H1.
      rewrite <- rev_nth in H1. {
        now rewrite rev_involutive in H1.
      }
      now rewrite rev_length.
    }
    apply Nat.nlt_ge in Hil.
    now rewrite nth_overflow.
  }
  cbn.
  destruct lb as [| b]; [ easy | ].
  remember (b :: lb) as ld eqn:Hld; symmetry in Hld.
  do 2 rewrite Nat.sub_0_r.
  rewrite fold_lap_norm.
  rewrite (lap_convol_mul_cons_with_0_l _ la). 2: {
    intros i.
    specialize (proj1 (eq_strip_0s_nil _) Hlc) as H1.
    destruct (lt_dec i (length la)) as [Hil| Hil]. {
      specialize (H1 (length la - S i)).
      rewrite <- rev_length in H1.
      rewrite <- rev_nth in H1. {
        now rewrite rev_involutive in H1.
      }
      now rewrite rev_length.
    }
    apply Nat.nlt_ge in Hil.
    now rewrite nth_overflow.
  }
  rewrite Nat.add_comm.
  apply lap_convol_mul_more; cbn.
  now rewrite Nat.sub_0_r.
}
rewrite rev_app_distr; cbn.
rewrite fold_lap_norm.
destruct lb as [| b]; [ easy | ].
remember (b :: lb) as d eqn:Hd.
replace (rev lc ++ [c]) with (rev (c :: lc)) by easy.
rewrite <- Hlc.
rewrite fold_lap_norm.
do 2 rewrite Nat.sub_0_r.
clear c lc b lb Hlc Hd.
rename d into lb.
rewrite (lap_convol_mul_more (length la - length (lap_norm la))). 2: {
  now cbn; rewrite Nat.sub_0_r.
}
rewrite (Nat.add_comm _ (length lb)).
rewrite <- Nat.add_assoc.
rewrite Nat.add_sub_assoc; [ | apply lap_norm_length_le ].
rewrite (Nat.add_comm _ (length la)).
rewrite Nat.add_sub.
rewrite Nat.add_comm.
apply lap_norm_cons_norm.
now cbn; rewrite Nat.sub_0_r.
Qed.

Theorem lap_mul_norm_idemp_r : ∀ la lb,
  lap_norm (la * lap_norm lb)%lap = lap_norm (la * lb)%lap.
Proof.
intros.
setoid_rewrite lap_mul_comm.
apply lap_mul_norm_idemp_l.
Qed.

Theorem poly_mul_assoc : ∀ p1 p2 p3,
  (p1 * (p2 * p3))%pol = ((p1 * p2) * p3) %pol.
Proof.
intros.
unfold "*"%pol.
remember (lap p1) as la.
remember (lap p2) as lb.
remember (lap p3) as lc.
clear p1 Heqla.
clear p2 Heqlb.
clear p3 Heqlc.
unfold poly_norm at 1 3.
apply eq_poly_eq; cbn.
rewrite lap_mul_norm_idemp_l.
rewrite lap_mul_norm_idemp_r.
now rewrite lap_mul_assoc.
Qed.

Theorem lap_mul_mul_swap : ∀ la lb lc,
  lap_mul (lap_mul la lb) lc = lap_mul (lap_mul la lc) lb.
Proof.
intros la lb lc.
do 2 rewrite <- lap_mul_assoc.
now rewrite (lap_mul_comm lb).
Qed.

Fixpoint lap_convol_mul_add al1 al2 al3 i len :=
  match len with
  | O => []
  | S len1 =>
      (Σ (j = 0, i),
       List.nth j al1 0 *
       (List.nth (i - j) al2 0 + List.nth (i - j) al3 0))%Rng ::
       lap_convol_mul_add al1 al2 al3 (S i) len1
  end.

(* *)

Theorem list_nth_add : ∀ k la lb,
  (List.nth k (lap_add la lb) 0 =
   List.nth k la 0 + List.nth k lb 0)%Rng.
Proof.
intros k la lb.
revert la lb.
induction k; intros.
 destruct la as [| a]; simpl; [ rewrite rng_add_0_l; reflexivity | idtac ].
 destruct lb as [| b]; simpl; [ rewrite rng_add_0_r; reflexivity | idtac ].
 reflexivity.

 destruct la as [| a]; simpl; [ rewrite rng_add_0_l; reflexivity | idtac ].
 destruct lb as [| b]; simpl; [ rewrite rng_add_0_r; reflexivity | idtac ].
 apply IHk.
Qed.

Theorem lap_convol_mul_lap_add : ∀ la lb lc i len,
  eq
    (lap_convol_mul la (lap_add lb lc) i len)
    (lap_convol_mul_add la lb lc i len).
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen; f_equal.
apply summation_compat; intros j (_, Hj).
f_equal.
rewrite list_nth_add; reflexivity.
Qed.

Theorem lap_add_lap_convol_mul : ∀ la lb lc i len,
  eq
     (lap_add
        (lap_convol_mul la lb i len)
        (lap_convol_mul la lc i len))
     (lap_convol_mul_add la lb lc i len).
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen; f_equal.
rewrite <- summation_add_distr.
apply summation_compat; intros j (_, Hj).
rewrite rng_mul_add_distr_l; reflexivity.
Qed.

Lemma lap_norm_mul_add_distr_l : ∀ la lb lc,
  lap_norm (la * (lb + lc))%lap = lap_norm (la * lb + la * lc)%lap.
Proof.
intros la lb lc.
unfold lap_mul.
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | ].
destruct lc as [| c]; [ now cbn; rewrite lap_add_0_r | ].
move b before a; move c before b.
remember (a :: la) as la' eqn:Hla'.
remember (b :: lb) as lb' eqn:Hlb'.
remember (c :: lc) as lc' eqn:Hlc'.
remember (length la' + length (lap_add lb' lc') - 1) as labc.
remember (length la' + length lb' - 1) as lab.
remember (length la' + length lc' - 1) as lac.
rewrite Heqlabc.
remember (lb' + lc')%lap as lbc.
symmetry in Heqlbc.
destruct lbc as [| bc]. {
  cbn.
  now subst lb' lc'.
}
rewrite <- Heqlbc in Heqlabc |-*.
rewrite lap_convol_mul_more with (n := (lab + lac)%nat). 2: {
  subst; flia.
}
rewrite <- Heqlabc.
symmetry.
rewrite Heqlab.
rewrite <- lap_add_norm_idemp_l.
rewrite lap_convol_mul_more with (n := (labc + lac)%nat); [ | flia ].
rewrite <- Heqlab.
rewrite lap_add_norm_idemp_l.
rewrite lap_add_comm.
rewrite <- lap_add_norm_idemp_l.
rewrite Heqlac.
rewrite lap_convol_mul_more with (n := (labc + lab)%nat); [ | flia ].
rewrite lap_add_norm_idemp_l.
rewrite <- Heqlac.
rewrite Nat.add_comm.
rewrite lap_add_comm.
rewrite Nat.add_assoc, Nat.add_shuffle0, Nat.add_comm, Nat.add_assoc.
symmetry.
rewrite lap_convol_mul_lap_add.
rewrite lap_add_lap_convol_mul.
reflexivity.
Qed.

Theorem lap_add_length : ∀ la lb,
  length (la + lb)%lap = max (length la) (length lb).
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | ].
cbn.
destruct lb as [| b]; [ easy | cbn ].
now rewrite IHla.
Qed.

Lemma lap_mul_add_distr_l : ∀ la lb lc,
  (la * (lb + lc))%lap = (la * lb + la * lc)%lap.
Proof.
intros la lb lc.
apply eq_lap_norm_eq_length; [ apply lap_norm_mul_add_distr_l | ].
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | ].
destruct lc as [| c]. {
  now cbn; rewrite lap_add_0_r.
}
cbn.
do 3 (rewrite Nat.add_succ_r; cbn); f_equal.
rewrite lap_convol_mul_length.
do 2 rewrite lap_add_length; cbn.
do 2 rewrite lap_convol_mul_length.
now rewrite Nat.add_max_distr_l.
Qed.

Theorem poly_mul_add_distr_l : ∀ pa pb pc,
  (pa * (pb + pc))%pol = (pa * pb + pa * pc)%pol.
Proof.
intros.
apply eq_poly_eq; cbn.
rewrite fold_lap_norm.
rewrite lap_mul_norm_idemp_r.
rewrite lap_add_norm_idemp_l.
rewrite lap_add_norm_idemp_r.
now rewrite lap_mul_add_distr_l.
Qed.

Lemma lap_convol_mul_1_l : ∀ la i len,
  length la = i + len
  → lap_convol_mul [1%Rng] la i len = skipn i la.
Proof.
intros * Hlen.
revert i Hlen.
induction len; intros. {
  rewrite Nat.add_0_r in Hlen; rewrite <- Hlen.
  symmetry; apply skipn_all.
}
cbn - [ summation nth ].
rewrite summation_split_first; [ | flia ].
rewrite all_0_summation_0. 2: {
  intros j Hj.
  destruct j; [ flia Hj | cbn ].
  now rewrite match_id, rng_mul_0_l.
}
rewrite Nat.sub_0_r, rng_add_0_r; cbn.
rewrite rng_mul_1_l.
rewrite IHlen; [ | flia Hlen ].
clear - Hlen.
revert i Hlen.
induction la as [ | a]; intros. {
  cbn in Hlen; flia Hlen.
}
cbn.
destruct i; [ easy | ].
rewrite IHla; [ easy | ].
cbn in Hlen; flia Hlen.
Qed.

Theorem lap_mul_1_l : ∀ la, ([1%Rng] * la)%lap = la.
Proof.
intros la.
unfold lap_mul.
destruct la as [| a]; [ easy | cbn ].
rewrite rng_mul_1_l, rng_add_0_r; f_equal.
now rewrite lap_convol_mul_1_l.
Qed.

Theorem lap_mul_1_r : ∀ la, (la * [1%Rng])%lap = la.
Proof.
intros la.
rewrite lap_mul_comm.
apply lap_mul_1_l.
Qed.

Theorem poly_mul_1_l : ∀ p, (1 * p)%pol = p.
Proof.
intros (la, lapr).
unfold "*"%pol.
rewrite lap_mul_1_l; cbn.
apply eq_poly_eq; cbn.
unfold rng_eqb in lapr.
unfold lap_norm.
destruct (rng_eq_dec (last la 1%Rng) 0) as [Hlaz| Hlaz]; [ easy | ].
clear lapr.
induction la as [| a]; [ easy | cbn ].
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]. {
  specialize (proj1 (eq_strip_0s_rev_nil _) Hlb) as H1.
  cbn; clear Hlb.
  destruct (rng_eq_dec a 0) as [Haz| Haz]. {
    exfalso; subst a.
    cbn in IHla.
    destruct la as [| a]; [ easy | ].
    remember (a :: la) as lb; cbn in Hlaz; subst lb.
    now specialize (IHla Hlaz).
  }
  cbn in IHla |-*.
  rewrite <- IHla; [ easy | ].
  cbn in Hlaz.
  destruct la as [| a2]; [ | easy ].
  intros; apply rng_1_neq_0.
}
cbn.
rewrite rev_app_distr; cbn; f_equal.
apply IHla.
cbn in Hlaz.
now destruct la.
Qed.

End lap.

Lemma lap_add_opp_l {α} {r : ring α} : ∀ la, lap_norm (- la + la)%lap = [].
Proof.
intros.
unfold lap_norm.
apply List_eq_rev_nil.
rewrite rev_involutive.
induction la as [| a]; [ reflexivity | cbn ].
rewrite strip_0s_app.
remember (strip_0s _) as lb eqn:Hlb; symmetry in Hlb.
subst lb.
rewrite IHla; cbn.
rewrite rng_add_opp_l.
now destruct (rng_eq_dec 0 0).
Qed.

Theorem poly_add_opp_l {α} {r : ring α} : ∀ p, (- p + p)%pol = 0%pol.
Proof.
intros p.
unfold "+"%pol; cbn.
apply eq_poly_eq; cbn.
rewrite lap_add_norm_idemp_l.
apply lap_add_opp_l.
Qed.

Theorem poly_add_opp_r {α} {r : ring α} : ∀ p, (p - p)%pol = 0%pol.
Proof.
intros p.
unfold poly_sub.
rewrite poly_add_comm.
apply poly_add_opp_l.
Qed.

Theorem poly_1_neq_0 {A} {rng : ring A} : 1%pol ≠ 0%pol.
Proof. easy. Qed.

Fixpoint lap_eqb {A} {rng : ring A} la lb :=
  match la with
  | [] =>
      match lb with
      | [] => true
      | _ :: _ => false
      end
  | a :: la' =>
      match lb with
      | [] => false
      | b :: lb' => if rng_eq_dec a b then lap_eqb la' lb' else false
      end
  end.

Theorem lap_eqb_eq {A} {rng : ring A} : ∀ la lb,
  lap_eqb la lb = true ↔ la = lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ now destruct lb | ].
destruct lb as [| b]; [ easy | cbn ].
destruct (rng_eq_dec a b) as [Hab| Hab]. {
  subst b.
  split; intros Hll; [ now f_equal; apply IHla | ].
  injection Hll; clear Hll; intros; subst lb.
  now apply IHla.
} {
  split; intros Hll; [ easy | ].
  now injection Hll; intros.
}
Qed.

Theorem lap_eqb_neq {A} {rng : ring A} : ∀ la lb,
  lap_eqb la lb = false ↔ la ≠ lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ now destruct lb | ].
destruct lb as [| b]; [ easy | cbn ].
destruct (rng_eq_dec a b) as [Hab| Hab]. {
  subst b.
  split; intros Hll. {
    intros H.
    injection H; clear H; intros; subst lb.
    now apply IHla in Hll.
  } {
    apply IHla.
    intros H; apply Hll.
    now subst lb.
  }
} {
  split; intros Hll; [ | easy ].
  intros H; apply Hab.
  now injection H; intros.
}
Qed.

Lemma lap_eq_dec {A} {rng : ring A} : ∀ la lb : list A,
  {la = lb} + {la ≠ lb}.
Proof.
intros.
remember (lap_eqb la lb) as lab eqn:Hlab; symmetry in Hlab.
destruct lab. {
  now left; apply lap_eqb_eq.
} {
  now right; apply lap_eqb_neq.
}
Qed.

Theorem poly_eq_dec {A} {rng : ring A} : ∀ pa pb : poly _,
  {pa = pb} + {pa ≠ pb}.
Proof.
intros (la, lapr) (lb, lbpr).
destruct (lap_eq_dec la lb) as [Hll| Hll]. {
  left; subst lb.
  now apply eq_poly_eq.
} {
  right; intros H; apply Hll.
  now injection H.
}
Qed.

Definition polynomial_ring {α} {r : ring α} : ring (poly α) :=
  {| rng_zero := poly_zero;
     rng_one := poly_one;
     rng_add := poly_add;
     rng_mul := poly_mul;
     rng_opp := poly_opp;
     rng_1_neq_0 := poly_1_neq_0;
     rng_eq_dec := poly_eq_dec;
     rng_add_comm := poly_add_comm;
     rng_add_assoc := poly_add_assoc;
     rng_add_0_l := poly_add_0_l;
     rng_add_opp_l := poly_add_opp_l;
     rng_mul_comm := poly_mul_comm;
     rng_mul_assoc := poly_mul_assoc;
     rng_mul_1_l := poly_mul_1_l;
     rng_mul_add_distr_l := poly_mul_add_distr_l |}.

(* allows to use ring theorems on polynomials *)
Canonical Structure polynomial_ring.

(* *)

Definition eval_lap {α} {R : ring α} la x :=
  (List.fold_right (λ c accu, accu * x + c) 0 la)%Rng.

Definition eval_poly {α} {R : ring α} pol :=
  eval_lap (lap pol).
