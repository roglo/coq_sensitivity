(* attempt to define algebraic numbers *)
(* work was in progress; not included in present application *)

Set Nested Proofs Allowed.

Require Import Arith.
Import List.ListNotations Init.Nat.

Require Import RingLike.RingLike.
Require Import RingLike.IterAdd.
Require Import RingLike.IterAnd.
Require Import RingLike.IterMul.
Require Import Misc.
Require Import Polynomial Matrix Determinant Comatrix.
Require Import Signature PermutSeq MyVector.
Import matrix_Notations.

(* Sylvester matrix *)

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Definition rlap_sylvester_list_list (rla rlb : list T) : list (list T) :=
  let m := length rla - 1 in
  let n := length rlb - 1 in
  List.map (λ i, List.repeat 0%L i ++ rla ++ List.repeat 0%L (n - 1 - i))
    (List.seq 0 n) ++
  List.map (λ i, List.repeat 0%L i ++ rlb ++ List.repeat 0%L (m - 1 - i))
    (List.seq 0 m).
(* it is possible to define it as the transposition of the above
   definition; avoiding a transposition to express its properties,
   they say *)

Definition rlap_sylvester_mat (rla rlb : list T) : matrix T :=
  mk_mat (rlap_sylvester_list_list rla rlb).

Definition lap_resultant (p q : list T) :=
  det (rlap_sylvester_mat (List.rev p) (List.rev q)).

Definition polyn_sylvester_mat (p q : polyn T) : matrix T :=
  mk_mat (rlap_sylvester_list_list (List.rev (lap p)) (List.rev (lap q))).

Definition resultant (p q : polyn T) :=
  det (polyn_sylvester_mat p q).

(*
Definition rlap_sylvester_list_list' (rla rlb : list T) :=
  let n := length rla - 1 in
  let m := length rlb - 1 in
  let s := rlap_sylvester_list_list rla rlb in
  List.map
    (λ i,
       let a := List.repeat 0%L (m - 1 - i) ++ List.rev rla in
       List.map (λ a, [a]) (firstn (length s - 1) (nth i s [])) ++ [a])
    (List.seq 0 m) ++
  List.map
    (λ i,
       let a := List.repeat 0%L (m + n - 1 - i) ++ List.rev rlb in
       List.map (λ a, [a]) (firstn (length s - 1) (nth i s [])) ++ [a])
    (List.seq m n).

Definition rlap_sylvester_mat' (rla rlb : list T) : matrix (list T) :=
  mk_mat (rlap_sylvester_list_list' rla rlb).

Definition rlap_resultant' (rol : ring_like_op (list T)) (p q : list T) :=
  List.rev (det (rlap_sylvester_mat' (List.rev p) (List.rev q))).
*)

Theorem rlap_sylvester_list_list_length :
  ∀ rla rlb,
  length (rlap_sylvester_list_list rla rlb) =
    (length rla - 1) + (length rlb - 1).
intros.
unfold rlap_sylvester_list_list.
rewrite List.length_app.
do 2 rewrite List.length_map, List.length_seq.
apply Nat.add_comm.
Qed.

Theorem lap_x_power_add :
  rngl_has_opp_or_psub T = true →
  rngl_has_eq_dec T = true →
  ∀ a b, lap_x_power (a + b) = (lap_x_power a * lap_x_power b)%lap.
Proof.
intros Hos Hed *.
unfold lap_x_power.
rewrite List.repeat_app.
rewrite <- List.app_assoc.
remember (List.repeat 0%L b ++ [1%L]) as la eqn:Hla.
assert (Ha : la ≠ []). {
  intros H; subst la.
  now apply List.app_eq_nil in H.
}
clear Hla b.
revert la Ha.
induction a; intros; cbn - [ lap_mul ]. {
  rewrite (lap_mul_const_l Hos).
  erewrite List.map_ext_in; [ | intros; apply (rngl_mul_1_l) ].
  now rewrite List.map_id.
}
rewrite IHa; [ | easy ].
rename la into lb.
rename Ha into Hb.
remember (List.repeat 0%L a ++ [1%L]) as la eqn:Hla.
assert (Ha : la ≠ []). {
  intros H; subst la.
  now apply List.app_eq_nil in H.
}
clear a Hla IHa.
move Hb after Ha.
rewrite <- (lap_mul_x_l Hos). 2: {
  intros Hab.
  apply eq_lap_mul_0 in Hab.
  now destruct Hab.
}
symmetry.
rewrite <- (lap_mul_x_l Hos); [ | easy ].
symmetry.
apply (lap_mul_assoc Hed Hos).
Qed.

Theorem lap_x_power_has_polyn_prop :
  rngl_characteristic T ≠ 1 →
  rngl_has_eq_dec T = true →
  ∀ n, has_polyn_prop (lap_x_power n) = true.
Proof.
intros Hch Hed *.
apply Bool.orb_true_iff.
right.
destruct n; cbn. {
  apply (rngl_neqb_neq Hed).
  now apply rngl_1_neq_0_iff.
}
rewrite List.last_last.
remember (List.repeat 0%L n ++ [1%L]) as la eqn:Hla; symmetry in Hla.
destruct la as [| a]. {
  now apply List.app_eq_nil in Hla.
}
apply (rngl_neqb_neq Hed).
now apply rngl_1_neq_0_iff.
Qed.

Theorem lap_norm_x_power :
  rngl_characteristic T ≠ 1 →
  rngl_has_eq_dec T = true →
  ∀ n, lap_norm (lap_x_power n) = lap_x_power n.
Proof.
intros Hch Hed *.
apply (has_polyn_prop_lap_norm Hed).
apply (lap_x_power_has_polyn_prop Hch Hed).
Qed.

Theorem polyn_x_power_add :
  rngl_has_opp_or_psub T = true →
  rngl_has_eq_dec T = true →
  ∀ a b, polyn_x_power (a + b) = (polyn_x_power a * polyn_x_power b)%pol.
Proof.
intros Hos Hed *.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hch| Hch]. {
  specialize (rngl_characteristic_1 Hos Hch) as H1.
  apply eq_polyn_eq.
  apply (eq_list_eq 0%L). 2: {
    intros i Hi.
    rewrite H1; symmetry.
    now rewrite H1.
  }
  cbn.
  rewrite (lap_mul_norm_idemp_l Hos Hed).
  rewrite (lap_mul_norm_idemp_r Hos Hed).
  specialize (all_0_lap_norm_nil Hed) as H2.
  rewrite (proj1 (H2 _)); [ | intros; apply H1 ].
  rewrite (proj1 (H2 _)); [ | intros; apply H1 ].
  easy.
}
apply eq_polyn_eq; cbn.
f_equal.
rewrite (lap_x_power_add Hos Hed).
now do 2 rewrite (lap_norm_x_power Hch Hed).
Qed.

Theorem lap_norm_mul_x_power_r :
  rngl_has_opp_or_psub T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 1 →
  rngl_has_eq_dec T = true →
  ∀ la n,
  lap_norm (la * lap_x_power n) = (lap_norm la * lap_x_power n)%lap.
Proof.
intros Hos Hiv Hch Hed *.
rewrite <- (lap_mul_norm_idemp_l Hos Hed).
rewrite (lap_norm_mul Hos Hed Hiv); [ easy | | ]. {
  apply polyn_norm_prop.
}
apply (lap_x_power_has_polyn_prop Hch Hed).
Qed.

Theorem polyn_of_const_add :
  ∀ (Hos : rngl_has_opp_or_psub T = true),
  ∀ (Hed : rngl_has_eq_dec T = true),
  ∀ (rop := polyn_ring_like_op Hos Hed),
  ∀ a b,
  polyn_of_const (a + b) = (polyn_of_const a + polyn_of_const b)%L.
Proof.
intros.
apply eq_polyn_eq; cbn.
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Hab| Hab]. {
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Ha| Ha]. {
    apply (rngl_eqb_eq Hed) in Ha; subst a.
    now rewrite rngl_add_0_l in Hab; rewrite Hab.
  }
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Hb| Hb]. {
    apply (rngl_eqb_eq Hed) in Hb; subst b.
    now rewrite rngl_add_0_r, Ha in Hab.
  }
  cbn.
  now rewrite Hab.
} {
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Ha| Ha]. {
    apply (rngl_eqb_eq Hed) in Ha; subst a.
    rewrite rngl_add_0_l in Hab; rewrite Hab.
    now cbn; rewrite rngl_add_0_l; rewrite Hab.
  }
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Hb| Hb]. {
    apply (rngl_eqb_eq Hed) in Hb; subst b.
    now cbn; rewrite rngl_add_0_r; rewrite Ha.
  }
  now cbn; rewrite Hab.
}
Qed.

Theorem polyn_of_const_mul :
  (rngl_is_integral_domain T || rngl_has_inv_or_pdiv T)%bool = true →
  ∀ (Hos : rngl_has_opp_or_psub T = true),
  ∀ (Hed : rngl_has_eq_dec T = true),
  ∀ (rop := polyn_ring_like_op Hos Hed),
  ∀ a b,
  polyn_of_const (a * b) = (polyn_of_const a * polyn_of_const b)%L.
Proof.
intros Hii *.
apply eq_polyn_eq; cbn.
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Hab| Hab]. {
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Ha| Ha]; [ easy | ].
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Hb| Hb]; [ easy | ].
  apply (rngl_eqb_eq Hed) in Hab.
  apply (rngl_eqb_neq Hed) in Ha, Hb.
  now apply (rngl_eq_mul_0_r Hos) in Hab.
}
apply (rngl_eqb_neq Hed) in Hab.
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Ha| Ha]. {
  apply (rngl_eqb_eq Hed) in Ha; subst a.
  now rewrite (rngl_mul_0_l Hos) in Hab.
}
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Hb| Hb]. {
  apply (rngl_eqb_eq Hed) in Hb; subst b.
  now rewrite (rngl_mul_0_r Hos) in Hab.
}
cbn.
rewrite rngl_summation_only_one.
rewrite if_bool_if_dec.
apply (rngl_eqb_neq Hed) in Hab.
destruct (Sumbool.sumbool_of_bool _); [ | easy ].
congruence.
Qed.

Arguments charac_0_field T {ro rp}.
Arguments polyn_characteristic_prop T {ro rp} Hos Hed.
Arguments polyn_ring_like_op T {ro rp} Hos Hed.
Arguments polyn_ring_like_prop T {ro rp} Hos Hed.

Theorem polyn_of_const_rngl_summation :
  ∀ (Hos : rngl_has_opp_or_psub T = true),
  ∀ (Hed : rngl_has_eq_dec T = true),
  ∀ (rop := polyn_ring_like_op T Hos Hed),
  ∀ b e f,
  polyn_of_const (∑ (i = b, e), f i) = ∑ (i = b, e), polyn_of_const (f i).
Proof.
intros *.
unfold iter_seq.
remember (S e - b) as n eqn:Hn.
clear e Hn.
revert b.
induction n; intros. {
  rewrite rngl_summation_list_empty; [ | easy ].
  rewrite rngl_summation_list_empty; [ | easy ].
  apply eq_polyn_eq; cbn.
  now rewrite (rngl_eqb_refl Hed).
}
rewrite List.seq_S.
rewrite rngl_summation_list_app.
set (rpp := polyn_ring_like_prop T Hos Hed).
rewrite rngl_summation_list_app.
rewrite (polyn_of_const_add Hos Hed).
rewrite IHn.
f_equal.
now do 2 rewrite rngl_summation_list_only_one.
Qed.

Theorem polyn_of_const_opp :
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ a, polyn_of_const (- a) = (- polyn_of_const a)%pol.
Proof.
intros Hop Hed *.
apply eq_polyn_eq; cbn.
do 2 rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Ha| Ha]. {
  apply (rngl_eqb_eq Hed) in Ha.
  destruct (Sumbool.sumbool_of_bool _) as [Hb| Hb]; [ easy | ].
  apply (rngl_eqb_neq Hed) in Hb.
  apply (f_equal rngl_opp) in Ha.
  rewrite (rngl_opp_involutive Hop) in Ha.
  now rewrite (rngl_opp_0 Hop) in Ha.
} {
  apply (rngl_eqb_neq Hed) in Ha.
  destruct (Sumbool.sumbool_of_bool _) as [Hb| Hb]. {
    apply (rngl_eqb_eq Hed) in Hb.
    now rewrite Hb, (rngl_opp_0 Hop) in Ha.
  }
  cbn.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Hc| Hc]; [ | easy ].
  now apply (rngl_eqb_eq Hed) in Hc.
}
Qed.

Theorem polyn_has_opp_or_psub :
  ∀ (Hop : rngl_has_opp T = true),
  ∀ (Hed : rngl_has_eq_dec T = true),
  ∀ (Hos := rngl_has_opp_has_opp_or_psub Hop),
  ∀ (rop := polyn_ring_like_op T Hos Hed),
  rngl_has_opp_or_psub (polyn T) = true.
Proof.
intros.
subst rop Hos.
unfold rngl_has_opp in Hop.
unfold rngl_has_opp_or_psub; cbn.
unfold polyn_opt_opp_or_psub.
remember rngl_opt_opp_or_psub as os eqn:Hos; symmetry in Hos.
destruct os; [ | easy ].
now destruct s.
Qed.

Theorem lap_norm_opp :
  rngl_has_opp T = true →
  rngl_has_eq_dec T = true →
  ∀ la, lap_norm (- la) = (- lap_norm la)%lap.
Proof.
intros Hop Hed *.
unfold lap_norm, lap_opp.
rewrite List.map_rev; f_equal.
rewrite <- List.map_rev.
remember (List.rev la) as lb eqn:Hlb.
clear la Hlb; rename lb into la.
induction la as [| a]; [ easy | cbn ].
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Hoaz| Hoaz]. {
  apply (rngl_eqb_eq Hed) in Hoaz.
  apply (f_equal rngl_opp) in Hoaz.
  rewrite (rngl_opp_involutive Hop) in Hoaz.
  rewrite (rngl_opp_0 Hop) in Hoaz.
  apply (rngl_eqb_eq Hed) in Hoaz; rewrite Hoaz.
  apply IHla.
} {
  apply (rngl_eqb_neq Hed) in Hoaz.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
    apply (rngl_eqb_eq Hed) in Haz; subst a.
    now rewrite (rngl_opp_0 Hop) in Hoaz.
  }
  easy.
}
Qed.

Theorem rngl_has_opp_has_opp_or_psub :
  rngl_has_opp T = true → rngl_has_opp_or_psub T = true.
Proof.
intros Hop.
unfold rngl_has_opp in Hop.
unfold rngl_has_opp_or_psub.
now destruct rngl_opt_opp_or_psub.
Defined.

(*
Definition rngl_has_opp_has_opp_or_psub (Hop : rngl_has_opp = true) :=
  match rngl_has_opp_or_psub_iff with
  | conj x x0 => x0
  end (or_introl Hop).
*)

Theorem polyn_of_const_minus_one_pow :
  ∀ (Hop : rngl_has_opp T = true),
  ∀ (Hed : rngl_has_eq_dec T = true),
  ∀ (rop := polyn_ring_like_op T (rngl_has_opp_has_opp_or_psub Hop) Hed),
  ∀ n, polyn_of_const (minus_one_pow n) = minus_one_pow n.
Proof.
intros *.
assert (Honp : rngl_has_1 (polyn T) = true) by easy.
set (Hos := rngl_has_opp_has_opp_or_psub Hop) in rop.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hch| Hch]. {
  specialize (rngl_characteristic_1 Hos Hch) as H1.
  apply eq_polyn_eq; cbn.
  rewrite (H1 (minus_one_pow n)).
  rewrite (rngl_eqb_refl Hed); cbn.
  set (rpp := polyn_ring_like_prop T Hos Hed).
  specialize (polyn_characteristic_prop (polyn T)) as H2.
  assert (Hosp : rngl_has_opp_or_psub (polyn T) = true). {
    now specialize (polyn_has_opp_or_psub Hop Hed) as H3.
  }
  specialize (H2 Honp Hosp).
  assert (Hedp : rngl_has_eq_dec (polyn T) = true) by easy.
  specialize (H2 Hedp).
  cbn in H2.
  rewrite Hch in H2.
  cbn in H2.
  destruct H2 as (_, H2).
  (* faudrait un polyn_add_0_r *)
  rewrite polyn_add_comm in H2.
  rewrite polyn_add_0_l in H2; [ | easy ].
  unfold minus_one_pow.
  destruct (n mod 2); cbn. {
    now rewrite (H1 1%L), (rngl_eqb_refl Hed).
  }
  unfold polyn_one, polyn_of_const, polyn_of_norm_lap; cbn.
  clear - H1 Hed.
  rewrite (H1 1%L).
  unfold rngl_opp; cbn.
  unfold polyn_opt_opp_or_psub.
  subst Hos; cbn.
  specialize (proj2 rngl_has_opp_or_psub_iff (or_introl Hop)) as H2.
  unfold rngl_has_opp_or_psub in H2.
  destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
  destruct os as [opp| psub ]; [ | easy ].
  subst rop; cbn.
  now rewrite (rngl_eqb_refl Hed); cbn.
}
apply eq_polyn_eq; cbn.
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Hmz| Hmz]; cbn. {
  apply (rngl_eqb_eq Hed) in Hmz.
  subst rop; cbn.
  unfold polyn_ring_like_op; cbn.
  unfold Hos; cbn.
  unfold minus_one_pow in Hmz |-*.
  destruct (n mod 2); cbn. {
    now apply (rngl_eqb_eq Hed) in Hmz; rewrite Hmz.
  }
  apply (f_equal rngl_opp) in Hmz.
  rewrite (rngl_opp_involutive Hop) in Hmz.
  rewrite (rngl_opp_0 Hop) in Hmz.
  now apply rngl_1_neq_0_iff in Hch.
}
unfold minus_one_pow.
destruct (n mod 2) as [| m]; cbn. {
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [H10| H10]; [ | easy ].
  apply (rngl_eqb_eq Hed) in H10.
  now apply rngl_1_neq_0_iff in Hch.
}
unfold rngl_opp; cbn.
specialize (proj2 rngl_has_opp_or_psub_iff (or_introl Hop)) as H2.
unfold rngl_has_opp_or_psub in H2.
unfold polyn_opt_opp_or_psub; cbn.
remember (rngl_opt_opp_or_psub T) as os eqn:Hos'; symmetry in Hos'.
destruct os as [os| ]; [ | easy ].
subst rop; cbn.
destruct os as [opp| psub ]. {
  assert (Hoo : ∀ x, opp x = rngl_opp x). {
    intros.
    unfold rngl_opp.
    now rewrite Hos'.
  }
  cbn - [ lap_norm ].
  unfold rngl_opp.
  rewrite Hos'.
  unfold lap_norm at 2.
  cbn - [ lap_norm ].
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [H10| H10]. {
    apply (rngl_eqb_eq Hed) in H10.
    now apply rngl_1_neq_0_iff in Hch.
  }
  cbn.
  rewrite Hoo.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [H11| H11]; [ | easy ].
  apply (rngl_eqb_eq Hed) in H11.
  apply (f_equal rngl_opp) in H11.
  rewrite (rngl_opp_involutive Hop) in H11.
  rewrite (rngl_opp_0 Hop) in H11.
  now apply rngl_1_neq_0_iff in Hch.
}
generalize Hop; intros Hsu.
apply rngl_has_opp_has_no_psub in Hsu.
move Hsu before Hop.
unfold rngl_has_psub in Hsu.
now rewrite Hos' in Hsu.
Qed.

Theorem det_polyn_of_const :
  (rngl_is_integral_domain T || rngl_has_inv_or_pdiv T)%bool = true →
  rngl_characteristic T ≠ 1 →
  ∀ (Hop : rngl_has_opp T = true),
  ∀ (Hed : rngl_has_eq_dec T = true),
  ∀ (rop := polyn_ring_like_op T (rngl_has_opp_has_opp_or_psub Hop) Hed),
  ∀ (ll : list (list T)),
  det {| mat_list_list := List.map (λ l, List.map polyn_of_const l) ll |} =
  polyn_of_const (det {| mat_list_list := ll |}).
Proof.
intros Hii Hch *; cbn.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
replace rop with (polyn_ring_like_op T Hos Hed). 2: {
  subst rop.
  unfold polyn_ring_like_op; cbn.
  f_equal.
  unfold rngl_has_opp_has_opp_or_psub.
  unfold rngl_has_opp_or_psub in Hos.
  f_equal.
  apply (Eqdep_dec.UIP_dec Bool.bool_dec).
}
subst rop.
set (rop := polyn_ring_like_op T Hos Hed).
assert (Hosp : rngl_has_opp_or_psub (polyn T) = true). {
  unfold rngl_has_opp_or_psub; cbn.
  unfold polyn_opt_opp_or_psub.
  unfold rngl_has_opp in Hop.
  clear - Hop.
  destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
  now destruct os.
}
rewrite List.length_map.
remember (List.length ll) as len eqn:Hlen; symmetry in Hlen.
revert ll Hlen.
induction len; intros; [ easy | ].
cbn - [ rngl_zero rngl_add ].
rewrite (polyn_of_const_rngl_summation Hos Hed).
apply rngl_summation_eq_compat.
intros i Hi.
assert
  (Hi1 :
    (rngl_is_integral_domain T ||
       rngl_has_inv_or_pdiv T)%bool = true). {
  apply Bool.orb_true_iff in Hii.
  apply Bool.orb_true_iff.
  destruct Hii as [Hii | Hii]; [ now left | right ].
  apply rngl_has_inv_or_pdiv_iff in Hii.
  apply rngl_has_inv_or_pdiv_iff.
  now destruct Hii; [ left | right ].
}
rewrite (polyn_of_const_mul Hi1 Hos Hed).
rewrite (polyn_of_const_mul Hi1 Hos Hed).
rewrite (List_map_nth' []); [ | now rewrite Hlen ].
rewrite <- List_hd_nth_0; cbn.
do 2 rewrite <- (polyn_mul_assoc Hos Hed).
f_equal. {
  symmetry.
  apply (polyn_of_const_minus_one_pow Hop Hed).
}
f_equal. {
  destruct (lt_dec (i - 1) (List.length (List.hd [] ll))) as [Hil| Hil]. {
    now rewrite (List_map_nth' 0%L).
  }
  apply Nat.nlt_ge in Hil.
  rewrite List.nth_overflow; [ | now rewrite List.length_map ].
  rewrite List.nth_overflow; [ | easy ].
  symmetry.
  apply eq_polyn_eq; cbn.
  now rewrite (rngl_eqb_refl Hed).
}
destruct ll as [| la]; [ easy | cbn ].
cbn in Hlen; apply Nat.succ_inj in Hlen.
unfold subm; cbn.
rewrite List.map_map.
erewrite List.map_ext_in. 2: {
  intros lb Hlb.
  now rewrite <- List_map_butn.
}
rewrite <- List.map_map.
rewrite IHlen; [ easy | now rewrite List.length_map ].
Qed.

(* U and V such that PU+QV=res(P,Q) *)
(* see Serge Lang's book, "Algebra", section "the resultant" *)
Definition lap_bezout_resultant_coeff (P Q : list T) :=
  let rol := lap_ring_like_op in
  let n := List.length P - 1 in
  let m := List.length Q - 1 in
  let s := rlap_sylvester_list_list (List.rev P) (List.rev Q) in
  (∑ (i = 0, m - 1),
     let j := (m - 1 - i)%nat in
     let s' :=
       mk_mat
         (List.map (λ l, List.firstn (List.length l - 1) l) (List_butn i s))
     in
     (minus_one_pow (m + n - i + 1) * (List.repeat 0%L j ++ [det s']))%lap,
   ∑ (i = m, m + n - 1),
     let j := (m + n - 1 - i)%nat in
     let s' :=
       mk_mat
         (List.map (λ l, List.firstn (List.length l - 1) l) (List_butn i s))
     in
     (minus_one_pow (m + n + i + 1) * (List.repeat 0%L j ++ [det s']))%lap).

(* to be completed
Theorem lap_bezout_is_resultant :
  charac_0_field T →
  ∀ (P Q U V : list T),
  2 ≤ List.length P
  → 2 ≤ List.length Q
  → lap_bezout_resultant_coeff P Q = (U, V)
  → lap_norm (U * P + V * Q)%lap = lap_norm [lap_resultant P Q].
Proof.
intros Hif * H2p H2q Hbr.
unfold lap_bezout_resultant_coeff in Hbr.
remember lap_ring_like_op as rol eqn:Hrol.
injection Hbr; clear Hbr; intros HV HU.
symmetry in HU, HV.
subst rol.
remember (List.length P - 1) as n eqn:Hn.
remember (List.length Q - 1) as m eqn:Hm.
remember (rlap_sylvester_list_list (List.rev P) (List.rev Q)) as ll eqn:Hll.
move m before n.
unfold lap_resultant.
unfold rlap_sylvester_mat.
rewrite <- Hll.
specialize (@cramer's_rule_by_mul (polyn T)) as Hcr.
assert (Hos : rngl_has_opp_or_psub T = true). {
  apply rngl_has_opp_or_psub_iff; left.
  apply (cf_has_opp Hif).
}
assert (Hon : rngl_has_1 T = true) by apply (cf_has_1 Hif).
assert (Hed : rngl_has_eq_dec T = true) by apply (cf_has_eq_dec Hif).
set (rop := polyn_ring_like_op T Hos Hed).
set (rpp := polyn_ring_like_prop T Hos Hed).
specialize (Hcr rop rpp).
cbn - [ det ] in Hcr.
generalize Hif; intros H.
destruct H as (_, Hic, Hop, Hin, _, Hch).
assert (Hopp : rngl_has_opp (polyn T) = true). {
  unfold rngl_has_opp; cbn.
  unfold polyn_opt_opp_or_psub.
  unfold rngl_has_opp in Hop.
  destruct rngl_opt_opp_or_psub as [s| ]; [ | easy ].
  now destruct s.
}
specialize (Hcr eq_refl Hopp Hic Hch).
assert (Hiq : rngl_has_inv_or_pdiv T = true). {
  apply rngl_has_inv_or_pdiv_iff.
  now rewrite Hin; left.
}
assert (Hiqp : rngl_has_inv_or_pdiv (polyn T) = true). {
  apply rngl_has_inv_or_pdiv_iff.
  unfold rngl_has_inv, rngl_has_pdiv; cbn.
  unfold polyn_opt_inv_or_pdiv.
  rewrite Hic, Hop, Hin; cbn.
  unfold rngl_has_inv in Hin.
  destruct rngl_opt_inv_or_pdiv; [ now right | easy ].
}
rewrite Hiqp, Bool.orb_comm in Hcr.
specialize (Hcr eq_refl).
assert
  (H : ∀ A (ro : ring_like_op A) (p q : list A),
     polyn_of_norm_lap p = polyn_of_norm_lap q → lap_norm p = lap_norm q). {
  intros * H.
  now apply eq_polyn_eq in H.
}
apply H; clear H.
remember (mk_mat (List.map (λ l, List.map polyn_of_const l) ll))
  as sm eqn:Hsm.
specialize (Hcr sm).
(* u is the vector [X^(n+m-1) X^(n+m-2) ... X 1] *)
remember
  (mk_vect (List.map (@polyn_x_power _ ro) (List.rev (List.seq 0 (n + m)))))
  as u eqn:Hu.
specialize (Hcr u).
(* v is the vector [X^(m-1)P X^(m-2)P ... XP P X^(n-1)Q X^(n-2)Q ... XQ Q] *)
remember
  (mk_vect
     (List.map (λ i, polyn_of_norm_lap (lap_x_power i * P)%lap)
        (List.rev (List.seq 0 m)) ++
     (List.map (λ i, polyn_of_norm_lap (lap_x_power i * Q)%lap)
        (List.rev (List.seq 0 n)))))
  as v eqn:Hv.
specialize (Hcr v).
assert (H : is_square_matrix sm = true). {
  clear - H2p H2q Hll Hsm.
  rewrite Hsm.
  apply Bool.andb_true_iff.
  split. {
    apply Bool.orb_true_iff.
    unfold mat_nrows, mat_ncols; cbn.
    rewrite List.length_map.
    destruct (Nat.eq_dec (List.length ll) 0) as [Hllz| Hllz]. {
      now right; rewrite Hllz.
    }
    left.
    destruct ll as [| la]; [ easy | clear Hllz; cbn ].
    rewrite List.length_map.
    apply Bool.negb_true_iff.
    apply Nat.eqb_neq.
    intros H; apply List.length_zero_iff_nil in H; subst la.
    move Hll at bottom.
    destruct P as [| a1]; [ easy | ].
    cbn in H2p; apply Nat.succ_le_mono in H2p.
    destruct P as [| a2]; [ easy | clear H2p ].
    destruct Q as [| b1]; [ easy | ].
    cbn in H2q; apply Nat.succ_le_mono in H2q.
    destruct Q as [| b2]; [ easy | clear H2q ].
    cbn in Hll.
    do 4 rewrite List.length_app in Hll.
    do 2 rewrite List.length_rev in Hll.
    cbn in Hll.
    do 4 rewrite Nat.add_sub in Hll.
    do 2 rewrite Nat.add_1_r in Hll.
    cbn in Hll.
    injection Hll; clear Hll; intros H1 H2.
    now destruct (List.rev P).
  } {
    move Hll at bottom.
    cbn; rewrite List.length_map.
    unfold iter_list.
    rewrite List_fold_left_map.
    specialize iter_list_eq_compat as H1.
    unfold iter_list in H1.
    erewrite H1; [ | now intros; rewrite List.length_map ].
    clear H1.
    rewrite fold_iter_list.
    apply all_true_and_list_true_iff.
    intros la Hla.
    apply Nat.eqb_eq.
    rewrite Hll in Hla |-*.
    rewrite rlap_sylvester_list_list_length.
    do 2 rewrite List.length_rev.
    apply List.in_app_or in Hla.
    do 2 rewrite List.length_rev in Hla.
    destruct Hla as [Hla| Hla]. {
      apply List.in_map_iff in Hla.
      destruct Hla as (i & Hi & His); subst la.
      do 2 rewrite List.length_app.
      rewrite List.length_rev.
      do 2 rewrite List.repeat_length.
      apply List.in_seq in His.
      flia H2p His.
    } {
      apply List.in_map_iff in Hla.
      destruct Hla as (i & Hi & His); subst la.
      do 2 rewrite List.length_app.
      rewrite List.length_rev.
      do 2 rewrite List.repeat_length.
      apply List.in_seq in His.
      flia H2q His.
    }
  }
}
specialize (Hcr H); clear H.
assert (H : vect_size u = mat_nrows sm). {
  rewrite Hu, Hsm; cbn.
  do 2 rewrite List.length_map.
  rewrite List.length_rev, List.length_seq.
  symmetry.
  rewrite Hll.
  rewrite rlap_sylvester_list_list_length.
  rewrite Hn, Hm.
  now do 2 rewrite List.length_rev.
}
specialize (Hcr H); clear H.
assert (H : (sm • u)%V = v). {
  clear - rpp Hsm Hu Hv Hll Hn Hm H2p H2q Hic Hed Hop.
  rewrite Hsm, Hu, Hv.
  unfold mat_mul_vect_r; f_equal; cbn.
  rewrite List.map_map.
  unfold vect_dot_mul.
  cbn - [ rngl_add rngl_zero ].
  rewrite Hll.
  unfold rlap_sylvester_list_list.
  rewrite List.map_app.
  do 2 rewrite List.map_map.
  do 2 rewrite List.length_rev.
  rewrite <- Hn, <- Hm.
  assert (H :
    ∀ (P Q : list T) n m,
    2 ≤ List.length P
    → 2 ≤ List.length Q
    → n = List.length P - 1
    → m = List.length Q - 1 →
      List.map
        (λ i,
           ∑ (t ∈
              List_map2 polyn_mul
                (List.map polyn_of_const
                   (List.repeat 0%L i ++ List.rev P ++
                      List.repeat 0%L (m - 1 - i)))
                (List.map polyn_x_power (List.rev (List.seq 0 (n + m))))),
             t) (List.seq 0 m) =
      List.map (λ i, polyn_of_norm_lap (lap_x_power i * P))
        (List.rev (List.seq 0 m))). {
    clear P Q n m H2p H2q Hn Hm Hll Hv (*HU HV*) Hu.
    intros * H2p H2q Hn Hm.
    erewrite List.map_ext_in. 2: {
      intros i Hi.
      apply List.in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
      erewrite List_map_map_seq with (d := 0%L).
      do 2 rewrite List.length_app.
      do 2 rewrite List.repeat_length.
      rewrite List.length_rev.
      replace (i + (List.length P + (m - 1 - i))) with (n + m) by
        flia Hi H2p Hn.
      rewrite List_map2_map_l.
      rewrite List_map2_map_r.
      rewrite List_map2_rev_seq_r.
      rewrite List_map2_diag.
      cbn - [ rngl_add rngl_zero ].
      rewrite rngl_summation_list_map.
      rewrite rngl_summation_seq_summation; [ | flia H2p H2q Hn ].
      rewrite Nat.add_0_l.
      rewrite rngl_summation_rshift.
      rewrite <- Nat.sub_succ_l; [ | flia H2p H2q Hn ].
      rewrite Nat_sub_succ_1.
      erewrite rngl_summation_eq_compat. 2: {
        intros j Hj.
        replace (n + m - 1 - (j - 1)) with (n + m - j) by flia Hj.
        easy.
      }
      remember (∑ (j = _, _), _) as x in |-*; subst x.
      easy.
    }
    rewrite List_map_rev_seq.
    apply List.map_ext_in.
    intros i Hi.
    apply List.in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
    rewrite Nat.mul_0_r, Nat.add_0_l.
    unfold polyn_of_norm_lap.
    rewrite rngl_summation_split with (j := i); [ | flia Hi ].
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite List.app_nth1; [ | rewrite List.repeat_length; flia Hj ].
      rewrite List.nth_repeat; cbn.
      unfold polyn_of_const; cbn.
      unfold polyn_of_norm_lap; cbn.
      apply eq_polyn_eq; cbn.
      now rewrite (rngl_eqb_refl Hed).
    }
    rewrite rngl_add_0_l.
    rewrite rngl_summation_shift with (s := i); [ | flia Hi ].
    rewrite Nat.add_comm, Nat.add_sub.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite List.app_nth2; [ | rewrite List.repeat_length; flia Hj ].
      rewrite List.repeat_length.
      rewrite Nat_sub_sub_swap, Nat.add_comm, Nat.add_sub.
      easy.
    }
    remember (∑ (j = _, _), _) as x in |-*; subst x.
    rewrite rngl_summation_split with (j := List.length P). 2: {
      rewrite Hn; flia Hi.
    }
    rewrite all_0_rngl_summation_0 with (b := List.length P + 1). 2: {
      intros j Hj.
      rewrite List.app_nth2; [ | rewrite List.length_rev; flia Hj ].
      rewrite List.nth_repeat; cbn.
      unfold polyn_of_const; cbn.
      unfold polyn_of_norm_lap; cbn.
      apply eq_polyn_eq; cbn.
      now rewrite (rngl_eqb_refl Hed).
    }
    rewrite rngl_add_0_r.
    remember (∑ (j = _, _), _) as x in |-*; subst x.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite List.app_nth1; [ | rewrite List.length_rev; flia Hj ].
      easy.
    }
    remember (∑ (j = _, _), _) as x in |-*; subst x.
    rewrite Hn, Hm.
    remember (List.length P) as n' eqn:Hn'.
    remember (List.length Q) as m' eqn:Hm'.
    move m' before n'; move n before m'; move m before n.
    subst n m.
    rename n' into n; rename m' into m.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      replace (n - 1 + (m - 1) - (j + i)) with
        (m - 2 - i + (n - j)) by flia Hi Hj.
      easy.
    }
    replace (m - 1 - 1) with (m - 2) by flia.
    remember (m - 2 - i) as a eqn:Ha.
    remember (∑ (j = _, _), _) as x in |-*; subst x.
    rewrite rngl_summation_rtl.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite Nat_sub_sub_swap, Nat.add_sub.
      replace (n - (n + 1 - j)) with (j - 1) by flia Hj.
      rewrite List.rev_nth; [ | rewrite <- Hn'; flia Hj ].
      rewrite <- Hn'.
      replace (n - S (n - j)) with (j - 1) by flia Hj.
      rewrite (polyn_mul_comm Hic).
      rewrite (polyn_x_power_add Hos Hed).
      replace polyn_mul with rngl_mul by easy.
      rewrite <- rngl_mul_assoc.
      easy.
    }
    remember (∑ (j = _, _), _) as x in |-*; subst x.
    rewrite <- rngl_mul_summation_distr_l. 2: {
      clear - Hop.
      unfold rngl_has_opp_or_psub in Hos |-*; cbn.
      unfold rngl_has_opp in Hop.
      subst rop.
      unfold polyn_opt_opp_or_psub.
      remember (rngl_opt_opp_or_psub T) as x eqn:Hx.
      destruct x as [x| ]; [ | easy ].
      now destruct x.
    }
    apply eq_polyn_eq.
    cbn - [ rngl_zero rngl_add ].
    rewrite (lap_mul_norm_idemp_l Hos Hed).
    rewrite <- (lap_mul_norm_idemp_r Hos Hed _ P).
    rewrite <- (lap_mul_norm_idemp_r Hos Hed).
    f_equal; f_equal; symmetry.
    remember (∑ (j = _, _), _) as x in |-*; subst x.
    clear a Ha.
    clear u v (*Hcr*).
    clear sm Hsm.
(*
    clear U V.
*)
    clear ll.
    clear i Hi.
    clear m Q Hm' H2q.
    rename Hn' into Hn.
    subst n.
    set
      (f :=
         λ (P : list T) i,
         (polyn_x_power (i - 1) *
            polyn_of_const (List.nth (i - 1) P 0%L))%pol).
    erewrite rngl_summation_eq_compat. 2: {
      intros i Hi.
      fold (f P i).
      easy.
    }
    specialize (lap_norm_lap_rngl_summation Hos Hed) as H1.
    specialize (H1 1 (List.length P) (f P)).
    remember (@lap T ro (∑ (i = 1, @List.length T P), f P i)) as x eqn:Hx.
    rewrite H1; subst x; clear H1.
    subst f.
    cbn - [ rngl_zero rngl_add polyn_of_const ].
    erewrite rngl_summation_eq_compat. 2: {
      intros i Hi.
      rewrite (lap_mul_norm_idemp_l Hos Hed).
      easy.
    }
    cbn - [ rngl_zero rngl_add polyn_of_const ].
    rewrite (lap_norm_rngl_summation_idemp Hed).
    erewrite rngl_summation_eq_compat. 2: {
      intros i Hi.
      unfold polyn_of_const.
      unfold polyn_of_norm_lap.
      cbn - [ lap_norm ].
      easy.
    }
    cbn - [ rngl_zero rngl_add lap_norm ].
    clear H2p.
(**)
    clear - rp Hos Hed.
    induction P as [| a la ]; [ easy | ].
    cbn - [ rngl_zero rngl_add lap_norm List.nth ].
    rewrite rngl_summation_shift with (s := 1); [ | cbn; flia ].
    rewrite Nat.sub_diag, Nat_sub_succ_1.
    (* it is so sad that I cannot apply rngl_summation_split_first
       because it requires that lap be a fully ring_like with all
       properties of ring_like_prop are set; however add_0_l, add_0_r
       and add_assoc work! *)
    rewrite iter_seq_split_first; [ | | | | easy ]; cycle 1. {
      apply lap_add_0_l.
    } {
      apply lap_add_0_r.
    } {
      apply lap_add_assoc.
    }
    rewrite Nat.add_0_r, Nat.sub_diag.
    unfold lap_x_power at 1.
    rewrite List_nth_0_cons.
    erewrite rngl_summation_eq_compat. 2: {
      intros i Hi.
      rewrite <- Nat.add_sub_assoc; [ | easy ].
      rewrite List_nth_succ_cons.
      rewrite (lap_x_power_add Hos Hed).
      unfold lap_x_power at 1.
      cbn - [ rngl_zero rngl_add lap_norm List.nth lap_mul ].
      rewrite <- (lap_mul_assoc Hed Hos).
      easy.
    }
    remember (λ j, _) as x in |-*; subst x.
    cbn - [ rngl_zero rngl_add lap_norm List.nth lap_mul ].
    rewrite (lap_mul_const_l Hos).
    erewrite List.map_ext_in; [ | now intros; rewrite (rngl_mul_1_l) ].
    rewrite List.map_id.
    (* cannot apply rngl_mul_summation_list_distr because it requires
       rngl_has_opp_or_psub, which is false on laps *)
    (* mul_iter_list_distr_l_test is more general, does not requires
       that, but I must decompose the whole processus ; I should make
       a lemma *)
    replace (@lap_mul T ro) with (@rngl_mul (list T) (@lap_ring_like_op T ro))
      by easy.
    set (rpl := @lap_ring_like_prop T ro rp Hed Hos).
    specialize mul_iter_list_distr_l_test as H1.
    specialize (H1 (list T) nat).
    specialize (H1 (@rngl_zero _ lap_ring_like_op)).
    specialize (H1 (@rngl_add _ lap_ring_like_op)).
    specialize (H1 (@rngl_mul _ lap_ring_like_op)).
    specialize (H1 lap_add_0_l (lap_mul_add_distr_l Hed Hos)).
    specialize (H1 [0; 1]%L (List.seq 1 (List.length la))).
    rewrite List.length_seq in H1.
    set (rol := lap_ring_like_op).
    specialize
      (H1 (λ i, (lap_x_power (i - 1) * lap_norm [List.nth (i - 1) la 0]))%L).
    rewrite if_bool_if_dec in H1.
    destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
      apply Nat.eqb_eq, List.length_zero_iff_nil in Haz; subst la.
      unfold iter_seq, iter_list; cbn - [ lap_norm ].
      rewrite lap_add_0_r.
      symmetry; apply lap_norm_idemp.
    }
    apply Nat.eqb_neq in Haz.
    rewrite (rngl_summation_seq_summation 1 (List.length la)) in H1;
      [ | easy ].
    rewrite (rngl_summation_seq_summation 1 (List.length la)) in H1;
      [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub in H1.
    fold rol rpl in H1.
    rewrite <- H1; clear H1.
    (* end of processus *)
    replace (@rngl_add _ rol) with (@lap_add _ ro) by easy.
    rewrite <- (lap_add_norm_idemp_r Hed).
    replace (@lap_add _ ro) with (@rngl_add _ rol) by easy.
    (**)
    replace (@rngl_mul _ rol) with (@lap_mul _ ro) by easy.
    rewrite <- (lap_mul_norm_idemp_r Hos Hed).
    (**)
    remember (lap_norm (∑ (i = _, _), _)) as x eqn:Hx.
    rewrite <- IHla.
    (**)
    rewrite (lap_mul_norm_idemp_r Hos Hed).
    replace (@rngl_add _ rol) with (@lap_add _ ro) by easy.
    rewrite (lap_add_norm_idemp_r Hed).
    rewrite (lap_add_norm_idemp_l Hed).
    (**)
    f_equal.
    apply (lap_cons Hos).
  }
  f_equal; [ now apply (H P Q) | now rewrite Nat.add_comm; apply (H Q P) ].
}
unfold polyn_of_norm_lap.
apply eq_polyn_eq; cbn - [ det lap_norm ].
specialize (Hcr H); clear H.
move Hcr at bottom.
replace (mat_nrows sm) with (n + m) in Hcr. 2: {
  rewrite Hsm, Hll; cbn.
  rewrite List.length_map.
  rewrite rlap_sylvester_list_list_length.
  do 2 rewrite List.length_rev.
  now rewrite <- Hn, <- Hm.
}
subst u.
cbn - [ det ] in Hcr.
assert
  (H : ∀ i, 1 ≤ i ≤ n + m →
    (det sm * polyn_of_norm_lap (lap_x_power (n + m - i)))%pol =
    det (mat_repl_vect i sm v)). {
  intros i Hi.
  rewrite <- Hcr; [ | easy ]; f_equal.
  rewrite (List_map_nth' 0). 2: {
    rewrite List.length_rev, List.length_seq.
    flia Hi.
  }
  unfold polyn_x_power.
  rewrite List_rev_seq_nth; [ | flia Hi ].
  rewrite <- Nat.sub_succ_l; [ | easy ].
  now rewrite Nat_sub_succ_1, Nat.add_0_l.
}
clear Hcr; rename H into Hcr.
assert
  (H : ∀ i, 1 ≤ i ≤ n + m →
    polyn_norm (lap (det sm) * lap_x_power (n + m - i)) =
    det (mat_repl_vect i sm v)). {
  intros i Hi.
  rewrite <- Hcr; [ | easy ].
  unfold polyn_mul; cbn.
  rewrite lap_norm_x_power; [ easy | easy | now rewrite Hch | easy ].
}
clear Hcr; rename H into Hcr.
assert
  (H : ∀ i, 1 ≤ i ≤ n + m →
     lap (det (mat_repl_vect i sm v)) =
     (lap_norm (lap (det sm)) * lap_x_power (n + m - i))%lap). {
  intros i Hi.
  specialize (Hcr i Hi).
  unfold polyn_norm in Hcr.
  apply (f_equal (λ p, lap p)) in Hcr.
  cbn - [ det ] in Hcr.
  rewrite (lap_norm_mul_x_power_r Hos Hin) in Hcr; [ | | easy ]. 2: {
    now rewrite Hch.
  }
  easy.
}
clear Hcr; rename H into Hcr.
assert (Hdm : det sm = polyn_of_const (det (mk_mat ll))). {
  rewrite Hsm.
  specialize det_polyn_of_const as H1.
  rewrite Hiq, Bool.orb_comm in H1.
  specialize (H1 eq_refl).
  rewrite Hch in H1.
  specialize (H1 (Nat.neq_0_succ _) Hop Hed).
  cbn - [ det ] in H1.
  apply H1.
}
unfold polyn_of_const in Hdm.
unfold polyn_of_norm_lap in Hdm.
apply (f_equal lap) in Hdm.
cbn - [ det ] in Hdm.
rewrite if_bool_if_dec in Hdm.
destruct (Sumbool.sumbool_of_bool _) as [Hdz| Hdz]. {
  cbn in Hdm.
  apply (rngl_eqb_eq Hed) in Hdz.
  rewrite Hdz.
  specialize (lap_norm_repeat_0 Hed 1) as H1.
  cbn - [ lap_norm ] in H1.
  rewrite H1; clear H1.
  rewrite Hdm in Hcr.
  cbn - [ det ] in Hcr.
...
}
... ...
apply (f_equal (λ l, List.rev l)) in H.
rewrite List.rev_involutive in H.
rewrite <- H.
cbn.
...
Search polyn_of_const.
...
(*
destruct (Nat.eq_dec (List.length ll) 0) as [Hlz| Hlz]. {
  apply List.length_zero_iff_nil in Hlz; subst ll.
  do 2 rewrite List_nth_nil.
  cbn.
  replace (@polyn_zero T ro) with (@rngl_zero _ rop) by easy.
  replace polyn_mul with rngl_mul by easy.
  set (rpp := polyn_ring_like_prop Hos Hed).
  rewrite rngl_mul_0_r; [ | easy ].
  rewrite rngl_mul_0_l; [ | easy ].
  (**)
  unfold polyn_of_const.
  remember (polyn_of_norm_lap [@rngl_zero _ ro]) as x eqn:Hx.
  unfold polyn_of_norm_lap in Hx; cbn in Hx.
  apply (f_equal lap) in Hx; cbn in Hx.
  rewrite (rngl_eqb_refl Hed) in Hx; cbn in Hx.
  destruct x as (x, y).
  cbn in Hx; subst x; cbn.
  (**)
  replace (@mk_polyn T ro (@nil T) y) with (@rngl_zero _ rop). 2: {
    now apply eq_polyn_eq.
  }
  replace polyn_mul with rngl_mul by easy.
  rewrite (rngl_mul_0_r Hosp).
  rewrite (rngl_mul_0_l Hosp).
  easy.
}
*)
rewrite (List_map_nth' []); [ | apply Nat.neq_0_lt_0 ].
  rewrite <- List_hd_nth_0.
  rewrite (List_map_nth' 0%L). 2: {
...
remember (lap_norm [_]) as x eqn:Hx.
    cbn - [ lap_norm ].
    replace (@polyn_zero T ro) with (@rngl_zero _ rop) by easy.
    replace polyn_mul with rngl_mul by easy.
    rewrite rngl_mul_0_r.
...
      rewrite Hos.
...
rewrite polyn_mul_0_r.
...
    set (rol := polyn_ring_like_op Hos Hed).
rewrite rngl_mul_0_r.
...
    unfold polyn_of_const.
    unfold polyn_of_norm_lap.
...
remember (List.nth 0 (List.map _ _) _) as x eqn:Hx.
rewrite (List_map_nth' []) in Hx.
  cbn.
  rewrite (List_map_nth' []).
...
induction ll as [| la]. {
  apply eq_polyn_eq; cbn.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [H1| H1]; [ | easy ].
  apply (rngl_eqb_eq Hed) in H1.
  now apply rngl_1_neq_0_iff in Hch.
}
cbn.
rewrite List.length_map.
... ...
apply det_polyn_of_const.
...

End a.

(*
Require Import RnglAlg.Qrl.
Require Import RnglAlg.Rational.
Import Q.Notations.
*)
Open Scope Q_scope.
Definition lap_compose_y_minus_x A {ro : ring_like_op A}
    {rol : ring_like_op _} (l : list A) :=
  lap_compose (List.map (λ i, [i]) l) [[0; 1]; [-1]]%L.
Definition lap_compose_y_div_x A {ro : ring_like_op A} (l : list A) :=
  List.map
    (λ i,
      List.repeat 0%L (List.length l - 1 - i) ++
        [List.nth (List.length l - 1 - i) l 0%L])
    (List.seq 0 (List.length l)).
Compute (
  let qro := Q_ring_like_op in
  let rla := [1;0;1] in
  let rlb := [1;0;-2] in
  let (U, V) := lap_bezout_resultant_coeff (List.rev rla) (List.rev rlb) in
  ((U * List.rev rla + V * List.rev rlb)%lap, lap_resultant rla rlb)).
(* oui *)
Compute (
  let qro := Q_ring_like_op in
  let lro := lap_ring_like_op in
  let rla := [1;0;1] in
  let rlb := [1;0;-2] in
  let p := List.map (λ i, [i]) (List.rev rla) in
  let q := lap_compose_y_minus_x (List.rev rlb) in
  let (U, V) := lap_bezout_resultant_coeff p q in
  ((U * p + V * q)%lap, lap_resultant p q)).
(* oui !!! *)
Compute (
  let qro := Q_ring_like_op in
  let lro := lap_ring_like_op in
  let rla := [1;0;1] in
  let rlb := [1;0;-2] in
  let p := List.map (λ i, [i]) (List.rev rla) in
  let q := lap_compose_y_div_x (List.rev rlb) in
  let (U, V) := lap_bezout_resultant_coeff p q in
  ((U * p + V * q)%lap, lap_resultant p q)).
Compute (
  let qro := Q_ring_like_op in
  let lro := lap_ring_like_op in
  let rla := [1;0;1] in
  let rlb := [1;0;0;-2] in
  let p := List.map (λ i, [i]) (List.rev rla) in
  let q := lap_compose_y_minus_x (List.rev rlb) in
  let (U, V) := lap_bezout_resultant_coeff p q in
  ((U * p + V * q)%lap, lap_resultant p q)).
(* oui *)
Compute (
  let qro := Q_ring_like_op in
  let lro := lap_ring_like_op in
  let rla := [1;0;1] in
  let rlb := [1;0;0;-2] in
  let p := List.map (λ i, [i]) (List.rev rla) in
  let q := lap_compose_y_div_x (List.rev rlb) in
  let (U, V) := lap_bezout_resultant_coeff p q in
  ((U * p + V * q)%lap, lap_resultant p q)).
Compute (
  let qro := Q_ring_like_op in
  let lro := lap_ring_like_op in
  let rla := [1;-4] in
  let rlb := [1;0;0;0;-3] in
  let p := List.map (λ i, [i]) (List.rev rla) in
  let q := lap_compose_y_minus_x (List.rev rlb) in
  let (U, V) := lap_bezout_resultant_coeff p q in
  ((U * p + V * q)%lap, lap_resultant p q)).
(* oui *)
Compute (
  let qro := Q_ring_like_op in
  let lro := lap_ring_like_op in
  let rla := [1;-4] in
  let rlb := [1;0;0;0;-3] in
  let p := List.map (λ i, [i]) (List.rev rla) in
  let q := lap_compose_y_div_x (List.rev rlb) in
  let (U, V) := lap_bezout_resultant_coeff p q in
  ((U * p + V * q)%lap, lap_resultant p q)).
Compute (
  let qro := Q_ring_like_op in
  let lro := lap_ring_like_op in
  let rla := [1;-2] in
  let rlb := [1;-3] in
  let p := List.map (λ i, [i]) (List.rev rla) in
  let q := lap_compose_y_minus_x (List.rev rlb) in
  let (U, V) := lap_bezout_resultant_coeff p q in
  ((U * p + V * q)%lap, lap_resultant p q)).
(* oui *)
Compute (
  let qro := Q_ring_like_op in
  let lro := lap_ring_like_op in
  let rla := [1;0;0;-2] in
  let rlb := [1;0;0;-3] in
  let p := List.map (λ i, [i]) (List.rev rla) in
  let q := lap_compose_y_minus_x (List.rev rlb) in
  let (U, V) := lap_bezout_resultant_coeff p q in
  ((U * p + V * q)%lap, lap_resultant p q)).
(* oui *)
Definition Q_list_ring_like_op : ring_like_op (list (list Q)) :=
  @lap_ring_like_op (list Q) (@lap_ring_like_op Q Q_ring_like_op).
Compute (
  let qro := Q_ring_like_op in
  let qlro := Q_list_ring_like_op in
  ([[1];[];[1]] * [[3;0;3];[0;-2]] +
     [[-2;0;1];[0;-2];[1]] * [[-3;0;1];[0;2]])%L).
(* same, with powers in decreasing order, for testing and readability *)
Definition r_algeb_add A (ro : ring_like_op A) (rol : ring_like_op (list A))
    rp rq :=
  List.rev (algeb_add (List.rev rp) (List.rev rq)).

Definition r_algeb_mul A (ro : ring_like_op A) (rol : ring_like_op (list A))
    rp rq :=
  List.rev (algeb_mul (List.rev rp) (List.rev rq)).

(* from Cyril Cohen's Phd thesis :
Since R is in the ideal generated by P(X+Y) and Q(X), there exist
U and V such that R(Y) = U(X,Y)P(X+Y) + V(X,Y)Q(X).
*)

(* test *)
(*
Require Import RnglAlg.Zrl.
Require Import ZArith.
Open Scope Z_scope.

Compute (
  let zro := Z_ring_like_op in
  rlap_pdiv_rem _ [4; 0; 6] [2; 1]).
(*
     = ([2; -1], [7])
     : list Z * list Z
*)
Compute (
  let zro := Z_ring_like_op in
  rlap_pdiv_rem _ [1; 0; 1] [1; 0; -2]).
(*
     = ([1], [0; 3])
     : list Z * list Z
*)
*)

Definition Q_r_algeb_add :=
  let qro := Q_ring_like_op in
  let qrp := Q_ring_like_prop in
  let lro := lap_ring_like_op in
  r_algeb_add qro lro.

Definition Q_r_algeb_mul :=
  let qro := Q_ring_like_op in
  let qrp := Q_ring_like_prop in
  let lro := lap_ring_like_op in
  r_algeb_mul qro lro.

Compute (
  let qro := Q_ring_like_op in
  rlap_pdiv_rem _ [4; 0; 6] [2; 1]).
(*
     = ([〈2〉; 〈-1〉], [〈7〉])
     : list Q * list Q
*)

Compute (
  let qro := Q_ring_like_op in
  rlap_pdiv_rem _ [1; 0; 1] [1; 0; -2]).
(*
     = ([〈1〉], [0; 〈3〉])
     : list Q * list Q
*)

(*
Compute (
  let qro := Q_ring_like_op in
  let qrp := Q_ring_like_prop in
  let lro := lap_ring_like_op in
  let p := [1; 0; 1] in
  let q := [-2; 0; 1] in
  let p' := List.map (λ i, [i]) p in
  let q' := List.map (λ i, [i]) q in
  List.rev
    (lap_resultant
       (lap_compose p' [[0; 1]; [1]])%L
       q')).
...
*)

Compute (Q_r_algeb_add [1;-1] [1;-2]).
(*
     = [〈1〉; 〈-3〉]
*)
Compute (Q_r_algeb_add [1;1] [1;-2]).
(*
     = [〈1〉; 〈-1〉]
*)
Compute (Q_r_algeb_add [1;0;1] [1;0;-2]).
(*
     = [〈1〉; 0; 〈-2〉; 0; 〈9〉]
*)
Compute (Q_r_algeb_add [1;0;1] [1;0;-3]).
(*
     = [〈1〉; 0; 〈-4〉; 0; 〈16〉]
(i+√3)=x
√3=x-i
3=x²-2ix-1
2ix=x²-4
-4x²=x⁴-8x²+16
x⁴-4x²+16=0
c'est bon
*)
Compute (Q_r_algeb_add [1;0;-2] [1;0;0;-2]).
(*
     = [〈1〉; 0; 〈-6〉; 〈-4〉; 〈12〉; 〈-24〉; 〈-4〉]
x⁶-6x⁴-4x³+12x²-24x-4
√2+∛2=x
∛2=x-√2
2=x³-3x²√2+6x-2√2
√2(3x²+2)=x³+6x-2
2(9x⁴+12x²+4)=x⁶+2x³(6x-2)+(6x-2)²
18x⁴+24x²+8=x⁶+12x⁴-4x³+36x²-24x+4
x⁶-6x⁴-4x³+12x²-24x-4
yeah !
*)

Compute (
  let _ := Q_ring_like_op in
  let _ := lap_ring_like_op in
  lap_compose_y_div_x [0;1;2;3]).

Compute (Q_r_algeb_mul [1;-1] [1;-2]).
(*
     = [〈1〉; 〈-2〉]
*)
Compute (Q_r_algeb_mul [1;1] [1;-2]).
(*
     = [〈1〉; 〈2〉]
*)
Compute (Q_r_algeb_mul [1;0;1] [1;0;-2]).
(*
     = [〈1〉; 0; 〈4〉; 0; 〈4〉]
*)
Compute (Q_r_algeb_mul [1;0;1] [1;0;-3]).
(*
     = [〈1〉; 0; 〈6〉; 0; 〈9〉]
*)
Compute (Q_r_algeb_mul [1;0;-2] [1;0;0;-2]).
(*
     = [〈1〉; 0; 0; 0; 0; 0; 〈-32〉]
*)

(*
  x = t²
  y = t²(t+1)

  t²-x = 0
  t³+t-y = 0
*)
Check
  (@lap_resultant (list (list Q)) lap_ring_like_op).
Check (mk_polyn [[[];[1]]; []; [[1]]]).
Print Q_r_algeb_add.
(* example taken from YouTube video
     https://www.youtube.com/watch?v=pjnq5LP1ESY
   a way to eliminate the variable t from a parametric function
     x = t²
     y = t²(t+1)
 *)
Compute
  (let T := Q in
   let roq := Q_ring_like_op in
   let rol := lap_ring_like_op in
   @lap_resultant (list (list Q)) lap_ring_like_op
     [[[];[-1]]; []; [[1]]]            (* t²-x *)
     [[[0; -1]]; []; [[1]]; [[1]]]).   (* t³+t²-y *)
(*
     = [[0; 0; 〈1〉]; [0; 〈-2〉]; [〈1〉]; [〈-1〉]]
     : list (list Q)
*)
(* -x³+x²-2yx+y² *)

Definition glop_add A (ro : ring_like_op A) (rol : ring_like_op (list A))
    p q :=
  let p' := List.map (λ i, [i]) p in
  let q' := List.map (λ i, [i]) q in
  lap_resultant
    (lap_compose p' [[0; 1]; [1]])%L
    (lap_compose q' [[0; 1]; [1]])%L.
Definition glip A (ro : ring_like_op A) (rol : ring_like_op (list A)) p :=
  let p' := List.map (λ i, [i]) p in
  @lap_compose (list A) rol p' [[0; 1]; [1]]%L.
Definition r_glop_add A (ro : ring_like_op A) (rol : ring_like_op (list A))
    rp rq :=
  List.rev (glop_add ro rol (List.rev rp) (List.rev rq)).
Definition Q_r_glop_add :=
  let qro := Q_ring_like_op in
  let qrp := Q_ring_like_prop in
  let lro := lap_ring_like_op in
  r_glop_add qro lro.
Compute (Q_r_glop_add [1;0;1] [1;0;-2]).
Compute (
  let qro := Q_ring_like_op in
  let qrp := Q_ring_like_prop in
  let lro := lap_ring_like_op in
  let rp := [[1]; [0; 2]; [1;0;1]] in
  let rq := [[1]; [0; 2]; [-2;0;1]] in
  List.rev (lap_resultant (List.rev rp) (List.rev rq))).
(* From Cyril Cohen's Phd Thesis, page 27
  properties of the resultant
    ResX(P(X,Y), Q(X,Y)) ∈ R[Y]
  of polynomials P,Q ∈ R[X,Y] where F is a field:
    ∃U,V ∈ R[X,Y], ResX(P,Q) = UP + VQ
  and
    ResX(P,Q)=0 ⇔ P and Q are not coprime as polynomials in X
*)
Compute (
  let qro := Q_ring_like_op in
  let qrp := Q_ring_like_prop in
  let lro := lap_ring_like_op in
  let rp := [[1]; [0; 2]; [1;0;1]] in
  let rq := [[1]; []; [-2]] in
  List.rev (lap_resultant (List.rev rp) (List.rev rq))).
(* example in video https://www.youtube.com/watch?v=WvbAfhOH4ik *)
Compute (
  let qro := Q_ring_like_op in
  rlap_pdiv_rem _ [1;0;0;-2;8;1;0;-16;-2] [1;0;0;0;8;1]).

(*
Compute (
  let qro := Q_ring_like_op in
  let qrp := Q_ring_like_prop in
  let lro := lap_ring_like_op in
  let rla := [1;2] in
  let rlb := [3;4;5] in
  mk_mat (rlap_sylvester_list_list' rla rlb)).
Compute (
  let qro := Q_ring_like_op in
  let qrp := Q_ring_like_prop in
  let lro := lap_ring_like_op in
  let rla := [1;0;1] in
  let rlb := [1;0;-2] in
  mk_mat (rlap_sylvester_list_list' rla rlb)).
Compute (
  let qro := Q_ring_like_op in
  let qrp := Q_ring_like_prop in
  let lro := lap_ring_like_op in
  let rla := [1;0;1] in
  let rlb := [1;0;-2] in
  (rlap_resultant' lro rla rlb, lap_resultant rla rlb)).
Compute (
  let qro := Q_ring_like_op in
  let qrp := Q_ring_like_prop in
  let lro := lap_ring_like_op in
  let rla := [1;2;3] in
  let rlb := [4;5;6;7] in
  (rlap_resultant' lro rla rlb, lap_resultant rla rlb)).
*)
Compute (
  let qro := Q_ring_like_op in
  let qrp := Q_ring_like_prop in
  let lro := lap_ring_like_op in
  let rla := [1;0;1] in
  let rlb := [1;0;-2] in
  let p := List.map (λ i, [i]) (List.rev rla) in
  let q := lap_compose (List.map (λ i, [i]) (List.rev rlb)) [[0; 1]; [-1]] in
  List.rev (lap_resultant p q)).
(*
Compute (
  let qro := Q_ring_like_op in
  let qrp := Q_ring_like_prop in
  let lro := lap_ring_like_op in
  let qlro := Q_list_ring_like_op in
  let rla := [1;0;1] in
  let rlb := [1;0;-2] in
  let p := List.map (λ i, [i]) (List.rev rla) in
  let q := lap_compose (List.map (λ i, [i]) (List.rev rlb)) [[0; 1]; [-1]] in
  lap_norm (List.rev (List.map (λ i, List.rev i) (rlap_resultant' _ p q)))).
Compute (
  let qro := Q_ring_like_op in
  let qrp := Q_ring_like_prop in
  let lro := lap_ring_like_op in
  let rla := [1;0;1] in
  let rlb := [1;0;-2] in
  mk_mat (rlap_sylvester_list_list' rla rlb)).
*)
(*
     = {|
         mat_list_list :=
           [[[〈1〉]; [0]; [〈1〉]; [0; 〈1〉; 0; 〈1〉]];
           [[0]; [〈1〉]; [0]; [〈1〉; 0; 〈1〉]];
           [[〈1〉]; [0]; [〈-2〉]; [0; 〈-2〉; 0; 〈1〉]];
           [[0]; [〈1〉]; [0]; [〈-2〉; 0; 〈1〉]]]
       |}
*)
Compute (
  let qro := Q_ring_like_op in
  let qrp := Q_ring_like_prop in
  let lro := lap_ring_like_op in
  let qlro := Q_list_ring_like_op in
  let rla := [1;0;1] in
  let rlb := [1;0;-2] in
  lap_resultant (List.rev rla) (List.rev rlb)).
(*
  x²+1            -2yx+3y²+3
     x²-2yx+y²-2             2y+y²-3
*)
Compute (
  let qro := Q_ring_like_op in
  let qlro := Q_list_ring_like_op in
  @lap_norm _ lap_ring_like_op
    ([[1];[];[1]] * [[3;0;3];[0;-2]] +
     [[-2;0;1];[0;-2];[1]] * [[-3;0;1];[0;2]])%L).
(*
Time Compute (
  let qro := Q_ring_like_op in
  let qrp := Q_ring_like_prop in
  let lro := lap_ring_like_op in
  lap_resultant (List.rev [5;0;0;-7;5;-3]) (List.rev [1;0;0;0;-4;0;0;6])).
...
*)

Compute (Q_r_algeb_add [1;0;1] [1;0;-2]).
Compute (Q_r_algeb_mul [1;0;1] [1;0;-2]).
Compute (Q_r_algeb_add [1;0;1] [1;0;1]).
Compute (Q_r_algeb_mul [1;0;1] [1;0;1]).
Compute (Q_r_algeb_add [1;0;-2] [1;0;-2]).
Compute (Q_r_algeb_mul [1;0;-2] [1;0;-2]).
Compute (Q_r_algeb_add [1;0;-2] [1;0;-3]).
Compute (Q_r_algeb_mul [1;0;-2] [1;0;-3]).
Compute (Q_r_algeb_add [1;0;1] [1;1;1]).
Compute (Q_r_algeb_mul [1;0;1] [1;1;1]).
Compute (Q_r_algeb_add [1;1;1] [1;0;1]).
Compute (Q_r_algeb_mul [1;1;1] [1;0;1]).
Compute (Q_r_algeb_add [1;2;3;4;5] [1;1;1]).
Compute (Q_r_algeb_add [1;0;0;-2] [1;0;1]).

(*
résultant (selon le X) des polynomes Q et P(Y-X)
*)

(*
Time Compute (
  let _ := Q_ring_like_op in
  let la := [7;5;3;2] in
  let lb := [11;13] in
  List.last (lap_compose la lb) 0).
(*
2*13³
(2.5 s)
*)
*)
(*
Compute (lap_compose Q_ring_like_op [-1;1] [1;0;1]).
Compute (lap_compose Q_ring_like_op [1;0;1] [-1;1]).
*)

Definition Q_polyn_ring_like_op : ring_like_op (polyn Q) :=
  @polyn_ring_like_op _ Q_ring_like_op Q_ring_like_prop
    eq_refl eq_refl.
Definition Q_polyn_ring_like_prop : ring_like_prop (polyn Q) :=
  @polyn_ring_like_prop _ Q_ring_like_op Q_ring_like_prop
    eq_refl eq_refl.

(*
Definition polyn_Q_ring_like_op :=
  @polyn_ring_like_op Q Q_ring_like_op Q_ring_like_prop eq_refl eq_refl
    (n_Sn _).
*)

Check
  (let roq := Q_ring_like_op in
   [mk_polyn [1;0;1] eq_refl]). (* x²+1 *)
Check
  (let roq := Q_ring_like_op in
   [mk_polyn [-2;0;1] eq_refl]). (* x²-2 *)

Check (@polyn_sylvester_mat _ Q_polyn_ring_like_op).

Search polyn.
Print polyn_of_norm_lap.

Compute (
   let roq := Q_ring_like_op in
   let rpq := Q_ring_like_prop in
   lap_norm [3]).
Compute (
   let roq := Q_ring_like_op in
   let rpq := Q_ring_like_prop in
   mk_polyn [3]).

Theorem single_has_polyn_prop :
  ∀ T op (rp : ring_like_prop T),
  rngl_has_eq_dec T = true →
  ∀ c, c ≠ 0%L → @has_polyn_prop T op [c] = true.
Proof.
intros T op rp Hed * Hcz; cbn.
apply Bool.negb_true_iff.
now apply rngl_eqb_neq.
Qed.

Definition polyn_of_const {T} (ro : ring_like_op T) rp
    (Hed : rngl_has_eq_dec T = true) (c : T) :=
  match rngl_eq_dec Hed c 0 with
  | left _ => 0%pol
  | right Hcz => mk_polyn [c] (single_has_polyn_prop rp Hed Hcz)
  end.

Theorem Q_single_has_polyn_prop :
  ∀ c, c ≠ 0%Q → @has_polyn_prop Q Q_ring_like_op [c] = true.
Proof.
intros * Hcz; cbn.
now destruct c.
Qed.

Definition polyn_of_Q_const c :=
  match Q.eq_dec c 0 with
  | left _ => 0%pol
  | right Haz => mk_polyn [c] (Q_single_has_polyn_prop Haz)
  end.

Theorem has_polyn_prop_map_polyn_of_Q_const :
  let roq := Q_ring_like_op in
  let roqp := Q_polyn_ring_like_op in
  ∀ la,
  has_polyn_prop la = true
  → has_polyn_prop (List.map polyn_of_Q_const la) = true.
Proof.
intros * Hla.
destruct la as [| a] using List.rev_ind; [ easy | clear IHla ].
apply Bool.orb_true_iff in Hla.
destruct Hla as [Hla| Hla]; [ now destruct la | ].
rewrite List.last_last in Hla.
rewrite List.map_app; cbn.
apply Bool.orb_true_iff; right.
rewrite List.last_last; cbn.
unfold polyn_eqb; cbn.
unfold polyn_of_Q_const.
destruct (Q.eq_dec a 0) as [Haz| Haz]; [ now subst a | easy ].
Qed.

Compute (
   let roq := Q_ring_like_op in
   let rpq := Q_ring_like_prop in
   @polyn_of_Q_const 3).
Compute
  (let roqp := Q_polyn_ring_like_op in
   let rpqp := Q_polyn_ring_like_prop in
   let roq := Q_ring_like_op in
   let rpq := Q_ring_like_prop in
   List.map polyn_of_Q_const [1;0;1]).
Compute
  (let roqp := Q_polyn_ring_like_op in
   let rpqp := Q_polyn_ring_like_prop in
   let roq := Q_ring_like_op in
   let rpq := Q_ring_like_prop in
   let la := [1;0;1] in
   mk_polyn (List.map polyn_of_Q_const la)
     (has_polyn_prop_map_polyn_of_Q_const la eq_refl)).
Compute
  (let roqp := Q_polyn_ring_like_op in
   let rpqp := Q_polyn_ring_like_prop in
   let roq := Q_ring_like_op in
   let rpq := Q_ring_like_prop in
   List.map polyn_of_Q_const [-2;0;1]).
Compute
  (let roqp := Q_polyn_ring_like_op in
   let roq := Q_ring_like_op in
   @mk_polyn (polyn Q) roqp [mk_polyn [1;0;1] eq_refl] eq_refl).
    (* x²+1 = p *)
Compute
  (let roqp := Q_polyn_ring_like_op in
   let roq := Q_ring_like_op in
   @mk_polyn (polyn Q) roqp [mk_polyn [-2;0;1] eq_refl] eq_refl).
     (* x²-2 = q *)
Compute
  (let roqp := Q_polyn_ring_like_op in
   let roq := Q_ring_like_op in
   @mk_polyn (polyn Q) roqp [polyn_zero; mk_polyn [1] eq_refl] eq_refl).
     (* z *)
Compute
  (let roqp := Q_polyn_ring_like_op in
   let roq := Q_ring_like_op in
   @mk_polyn (polyn Q) roqp [mk_polyn [0;-1] eq_refl] eq_refl). (* -x *)
Compute
  (let roqp := Q_polyn_ring_like_op in
   let roq := Q_ring_like_op in
   @mk_polyn (polyn Q) roqp [mk_polyn [0;-1] eq_refl; mk_polyn [1] eq_refl]
     eq_refl). (* z-x *)

Compute
  (let roqp := Q_polyn_ring_like_op in
   let roq := Q_ring_like_op in
   @mk_polyn (polyn Q) roqp [mk_polyn [-2;0;1] eq_refl] eq_refl).
     (* x²-2 = q *)
Compute
  (let roqp := Q_polyn_ring_like_op in
   let roq := Q_ring_like_op in
   @mk_polyn (polyn Q) roqp [mk_polyn [0;-1] eq_refl; mk_polyn [1] eq_refl]
     eq_refl). (* z-x *)

Check @polyn_compose.
Check
  (let T := polyn Q in
   let ro := Q_polyn_ring_like_op in
   let rp := Q_polyn_ring_like_prop in
   @lap_compose T ro).
Print polyn_compose.
Print polyn_of_norm_lap.
Compute
  (let q :=
     let roqp := Q_polyn_ring_like_op in
     let roq := Q_ring_like_op in
     @mk_polyn (polyn Q) roqp [mk_polyn [-2;0;1] eq_refl] eq_refl (* x²-2 *)
   in
   let roqp := Q_polyn_ring_like_op in
   lap_norm (lap q)).
Compute
  (let z_x :=
     let roqp := Q_polyn_ring_like_op in
     let roq := Q_ring_like_op in
     @mk_polyn (polyn Q) roqp
       [mk_polyn [0;-1] eq_refl; mk_polyn [1] eq_refl] eq_refl
   in
   let roqp := Q_polyn_ring_like_op in
   lap_norm (lap z_x)).

Compute
  (let q :=
     let roqp := Q_polyn_ring_like_op in
     let roq := Q_ring_like_op in
     @mk_polyn (polyn Q) roqp [mk_polyn [-2;0;1] eq_refl] eq_refl (* x²-2 *)
   in
   let z_x :=
     let roqp := Q_polyn_ring_like_op in
     let roq := Q_ring_like_op in
     @mk_polyn (polyn Q) roqp
       [mk_polyn [0;-1] eq_refl; mk_polyn [1] eq_refl] eq_refl
   in
   lap_compose (lap q) (lap z_x)).

Check
  (let q :=
     let roqp := Q_polyn_ring_like_op in
     let roq := Q_ring_like_op in
     @mk_polyn (polyn Q) roqp [mk_polyn [-2;0;1] eq_refl] eq_refl (* x²-2 *)
   in
   let z_x :=
     let roqp := Q_polyn_ring_like_op in
     let roq := Q_ring_like_op in
     @mk_polyn (polyn Q) roqp
       [mk_polyn [0;-1] eq_refl; mk_polyn [1] eq_refl] eq_refl
   in
   let rpqp := Q_polyn_ring_like_op in
   polyn_norm_prop (lap_compose (lap q) (lap z_x))).

Check
  (let q :=
     let roqp := Q_polyn_ring_like_op in
     let roq := Q_ring_like_op in
     @mk_polyn (polyn Q) roqp [mk_polyn [-2;0;1] eq_refl] eq_refl (* x²-2 *)
   in
   let z_x :=
     let roqp := Q_polyn_ring_like_op in
     let roq := Q_ring_like_op in
     @mk_polyn (polyn Q) roqp
       [mk_polyn [0;-1] eq_refl; mk_polyn [1] eq_refl] eq_refl
   in
   (*mk_polyn*) (lap_compose (lap q) (lap z_x))).

(*
Theorem Q_polyn_norm_prop :
  let ro := Q_polyn_ring_like_op in
  ∀ la : list (polyn Q), has_polyn_prop (@lap_norm _ ro la) = true.
Proof.
intros.
unfold has_polyn_prop, lap_norm.
induction la as [| a]; [ easy | cbn ].
rewrite strip_0s_app.
remember (strip_0s (List.rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]; cbn. {
  rewrite if_bool_if_dec.
  destruct (Bool.bool_dec _) as [Haz| Haz]; [ easy | cbn ].
  now apply Bool.negb_true_iff.
}
cbn in IHla.
rewrite List.last_last in IHla.
apply Bool.orb_true_iff in IHla.
apply Bool.orb_true_iff; right.
rewrite List.last_last.
destruct IHla as [H1| H1]; [ | easy ].
apply is_empty_list_empty in H1.
now apply List.app_eq_nil in H1.
Qed.
*)

Theorem Q_has_eqb : @rngl_has_eq_dec Q Q_ring_like_op = true.
Proof. easy. Qed.

Theorem Q_polyn_has_eqb :
  @rngl_has_eq_dec (polyn Q) Q_polyn_ring_like_op = true.
Proof. easy. Qed.

Time Compute (
  let p :=
    let roqp := Q_polyn_ring_like_op in
    let roq := Q_ring_like_op in
    let p :=
      [mk_polyn [1] eq_refl; mk_polyn [] eq_refl; mk_polyn [1] eq_refl]
    in
    mk_polyn p (polyn_norm_prop p)
  in
  let q' :=
    let roq := Q_ring_like_op in
    let q :=
      [mk_polyn [-2;0;1] eq_refl; mk_polyn [0;-2] eq_refl;
       mk_polyn [1] eq_refl]
    in
    let roqp := Q_polyn_ring_like_op in
    mk_polyn q (polyn_norm_prop q)
  in
  resultant p q').
(*
     = mkp [〈9〉; 0; 〈-2〉; 0; 〈1〉]%pol
     : polyn Q
ok
*)

Definition r_algeb_sum_cancel_lap T
    (ro : ring_like_op T) (rol : ring_like_op (list T)) rp rq :=
  let p' := List.map (λ i, [i]) (List.rev rp) in
  let q' := List.map (λ i, [i]) (List.rev rq) in
  List.rev (lap_resultant p' (lap_compose q' [[0; -1]; [1]])%L).

Definition Q_r_algeb_sum_cancel_lap :=
  let qro := Q_ring_like_op in
  let qrp := Q_ring_like_prop in
  let lro := lap_ring_like_op in
  r_algeb_sum_cancel_lap qro lro.

Compute (Q_r_algeb_sum_cancel_lap [1;0;1] [1;0;-2]).
Compute (Q_r_algeb_sum_cancel_lap [1;0;1] [1;0;1]).
Compute (Q_r_algeb_sum_cancel_lap [1;0;-2] [1;0;-2]).
Compute (Q_r_algeb_sum_cancel_lap [1;0;-2] [1;0;-3]).
Compute (Q_r_algeb_sum_cancel_lap [1;0;1] [1;1;1]).

(* bon, ci-dessous, ça prend toujours plein de temps à calculer
   par Compute, même si tous les implicites sont donnés implicitement ;
   je croyais que c'était à cause d'implicites non explicites que
   ça prenait du temps mais non *)
Set Printing All.
Time Check
  (let q :=
     let roqp := Q_polyn_ring_like_op in
     let roq := Q_ring_like_op in
     @mk_polyn (polyn Q) roqp [mk_polyn [-2;0;1] eq_refl] eq_refl (* x²-2 *)
   in
   let z_x :=
     let roqp := Q_polyn_ring_like_op in
     let roq := Q_ring_like_op in
     @mk_polyn (polyn Q) roqp
       [mk_polyn [0;-1] eq_refl; mk_polyn [1] eq_refl] eq_refl
   in
(*
   let r := (lap q ° lap z_x)%lap in
*)
   let r := @lap_compose (polyn Q) Q_polyn_ring_like_op (lap q) (lap z_x) in
(**)
   let qpro := Q_polyn_ring_like_op in
   mk_polyn (@lap_norm (polyn Q) qpro r) (polyn_norm_prop r)).
(* 32 s *)
(*
   mk_polyn r (Q_polyn_norm_prop r)).
*)
(* 0.007 s *)
(*
Time Compute (
  let p :=
    let roqp := Q_polyn_ring_like_op in
    let roq := Q_ring_like_op in
    let p :=
      [mk_polyn [1] eq_refl; mk_polyn [] eq_refl; mk_polyn [1] eq_refl]
    in
    mk_polyn p (polyn_norm_prop _ p)
  in
  let q' :=
    let roqp := Q_polyn_ring_like_op in
    let roq := Q_ring_like_op in
    let q :=
      [mk_polyn [-2;0;1] eq_refl; mk_polyn [0;-2] eq_refl;
       mk_polyn [1] eq_refl]
    in
    mk_polyn q (polyn_norm_prop _ q)
  in
  polyn_sylvester_mat p q').
*)
Check rngl_eqb.
Check polyn_of_const.
Check (polyn_of_const Q_ring_like_prop).
Search (@rngl_has_eq_dec Q).
Check polyn_norm_prop.

(*
Theorem toto :
  let roqp := Q_polyn_ring_like_op in
  ∀ la,
  has_polyn_prop (List.map (polyn_of_const Q_ring_like_prop Q_has_eqb) la) =
    true.
Proof.
intros.
apply Bool.orb_true_iff.
...
*)

Print polyn_of_const.
Check rngl_eq_dec.
Print rngl_eq_dec.
Definition rngl_eq_dec' T (ro : ring_like_op T) (rp : ring_like_prop T)
    (Heq : rngl_has_eq_dec T = true) (a b : T) :=
  (if (a =? b)%L as b0 return ((a =? b)%L = b0 → {a = b} + {a ≠ b}) then
     λ Hab1, left (match rngl_eqb_eq Heq a b with conj x _ => x Hab1 end)
   else
     λ Hab1, right (match rngl_eqb_neq Heq a b with conj x _ => x Hab1 end)
  ) eq_refl.
(*
Time Compute (
  rngl_eq_dec' _ Q_has_eqb 1 0).
Time Compute (
  rngl_eq_dec' Q_ring_like_prop Q_has_eqb 1 0).
(* 14 s *)
...
     = right
         match rngl_eqb_neq Q_has_eqb 〈1〉 0 with
         | conj x _ => x eq_refl
         end
     : {1 = 0} + {1 ≠ 0}
Time Compute (
    let rpq := Q_ring_like_prop in
  rngl_eq_dec Q_has_eqb 1 0).
(* 14 s *)
Print polyn_of_const.
...
*)
(*
Time Compute (
(*
  let p :=
    let roqp := Q_polyn_ring_like_op in
    let roq := Q_ring_like_op in
    let p :=
      [mk_polyn [1] eq_refl; mk_polyn [] eq_refl; mk_polyn [1] eq_refl]
    in
    mk_polyn p (polyn_norm_prop _ p)
  in
*)
  (* essai d'être plus général *)
  let p :=
    let roqp := Q_polyn_ring_like_op in
    let rpqp := Q_polyn_ring_like_prop in
    let roq := Q_ring_like_op in
    let rpq := Q_ring_like_prop in
    let p := List.map (polyn_of_const rpq Q_has_eqb) [1;0;1] in
p
in p).
*)
(*
    mk_polyn p (glop roqp p)
in p).
    mk_polyn (lap_norm p) (@polyn_norm_prop (polyn Q) roqp p)
(rend le truc interminable en temps)
  in
  let q' :=
    let roq := Q_ring_like_op in
    let q :=
      [mk_polyn [-2;0;1] eq_refl; mk_polyn [0;-2] eq_refl;
       mk_polyn [1] eq_refl]
    in
    mk_polyn q (polyn_norm_prop Q_polyn_ring_like_op q)
  in
  resultant p q').
...
*)
(* avec la Notation, ça répond vite, ce qui prouve que l'affichage
   qui prend du temps ; d'un autre côté, il y a un exemple plus
   haut où ça a pas l'air d'être ça *)
(* résultat
     = mkp [〈9〉; 0; 〈-2〉; 0; 〈1〉]%pol
     : polyn Q
   ce qui est correct !!! Super !
 *)
Print fold_right.

(* p sur K[x], p' sur L[x]
   calculer p (p') dans L[x]
ah non : tous les polynômes dans L[x]
voir lap_compose.
...
   Q[x] inclus dans Q[Q[x]].
*)

(*
Check [mk_polyn [1;0;1] eq_refl]. (* x²+1) *)
Check [mk_polyn [-2;0;1] eq_refl]. (* x²-2) *)
Check (@mk_polyn (polyn Q)).
*)
(*
Theorem glop :
  (@rngl_characteristic Q Q_ring_like_op Q_ring_like_prop) ≠ 1%nat.
Proof. easy. Show Proof.
...

Check (polyn_ring_like_op Q_ring_like_prop (n_Sn _)).
Check
  (@polyn_ring_like_op Q Q_ring_like_op Q_ring_like_prop eq_refl eq_refl
     (n_Sn _)).
Search rngl_characteristic.

Check mk_polyn.
Search has_polyn_prop.
*)

(*
Compute (polyn_sylvester_mat (mk_polyn (List.rev [1;2;3;4;5]) eq_refl)
  (mk_polyn (List.rev [6;7;8;9]) eq_refl)).
Compute
  (mat_nrows (polyn_sylvester_mat (mk_polyn (List.rev [1;2;3;4;5])
     eq_refl)
  (mk_polyn (List.rev [6;7;8;9]) eq_refl))).
Time Compute (det (polyn_sylvester_mat (mk_polyn (List.rev [1;2;3;4]) eq_refl)
  (mk_polyn (List.rev [6;7;8;9]) eq_refl))).
...
Compute (det (polyn_sylvester_mat (mk_polyn (List.rev [1;2;3;4;5]) eq_refl)
  (mk_polyn (List.rev [6;7;8;9]) eq_refl))).
...
Compute (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9]).
Compute (mat_nrows (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9])).
Compute (mat_ncols (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9])).
Compute (is_square_matrix (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9])).
Compute
  (let m := rlap_sylvester_mat [1;2;3;4] [6;7;8] in
   (mat_nrows m, mat_ncols m, m, is_square_matrix m)).
Compute
  (let m := rlap_sylvester_mat [1;2;3] [6;7] in
   (mat_nrows m, mat_ncols m, m, is_square_matrix m)).
Compute
  (let m := rlap_sylvester_mat [2] [6;7] in
   (mat_nrows m, mat_ncols m, m, is_square_matrix m)).
Compute
  (let m := rlap_sylvester_mat [2;3] [6] in
   (mat_nrows m, mat_ncols m, m, is_square_matrix m)).
*)
*)
