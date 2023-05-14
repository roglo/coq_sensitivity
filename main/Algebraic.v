(* attempt to define algebraic numbers *)

Set Nested Proofs Allowed.

Require Import Utf8 Arith.
Import List ListNotations Init.Nat.

Require Import Misc RingLike IterAdd IterMul IterAnd.
Require Import LapPolyn Polynomial Matrix Determinant Comatrix.
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
  map (λ i, repeat 0%L i ++ rla ++ repeat 0%L (n - 1 - i)) (seq 0 n) ++
  map (λ i, repeat 0%L i ++ rlb ++ repeat 0%L (m - 1 - i)) (seq 0 m).
(* it is possible to define it as the transposition of the above
   definition; avoiding a transposition to express its properties,
   they say *)

Definition rlap_sylvester_mat (rla rlb : list T) : matrix T :=
  mk_mat (rlap_sylvester_list_list rla rlb).

Definition lap_resultant (p q : list T) :=
  det (rlap_sylvester_mat (rev p) (rev q)).

Definition polyn_sylvester_mat (p q : polyn T) : matrix T :=
  mk_mat (rlap_sylvester_list_list (rev (lap p)) (rev (lap q))).

Definition resultant (p q : polyn T) :=
  det (polyn_sylvester_mat p q).

(*
Definition rlap_sylvester_list_list' (rla rlb : list T) :=
  let n := length rla - 1 in
  let m := length rlb - 1 in
  let s := rlap_sylvester_list_list rla rlb in
  map
    (λ i,
       let a := repeat 0%L (m - 1 - i) ++ rev rla in
       map (λ a, [a]) (firstn (length s - 1) (nth i s [])) ++ [a])
    (seq 0 m) ++
  map
    (λ i,
       let a := repeat 0%L (m + n - 1 - i) ++ rev rlb in
       map (λ a, [a]) (firstn (length s - 1) (nth i s [])) ++ [a])
    (seq m n).

Definition rlap_sylvester_mat' (rla rlb : list T) : matrix (list T) :=
  mk_mat (rlap_sylvester_list_list' rla rlb).

Definition rlap_resultant' (rol : ring_like_op (list T)) (p q : list T) :=
  rev (det (rlap_sylvester_mat' (rev p) (rev q))).
*)

Theorem rlap_sylvester_list_list_length :
  ∀ rla rlb,
  length (rlap_sylvester_list_list rla rlb) =
    (length rla - 1) + (length rlb - 1).
intros.
unfold rlap_sylvester_list_list.
rewrite app_length.
do 2 rewrite List_map_seq_length.
apply Nat.add_comm.
Qed.

Theorem lap_x_power_add :
  rngl_has_opp_or_subt = true →
  rngl_has_eqb = true →
  ∀ a b, lap_x_power (a + b) = (lap_x_power a * lap_x_power b)%lap.
Proof.
intros Hos Heb *.
unfold lap_x_power.
rewrite repeat_app.
rewrite <- app_assoc.
remember (repeat 0%L b ++ [1%L]) as la eqn:Hla.
assert (Ha : la ≠ []). {
  intros H; subst la.
  now apply app_eq_nil in H.
}
clear Hla b.
revert la Ha.
induction a; intros; cbn - [ lap_mul ]. {
  rewrite (lap_mul_const_l Hos).
  erewrite map_ext_in; [ | intros; apply rngl_mul_1_l ].
  now rewrite map_id.
}
rewrite IHa; [ | easy ].
rename la into lb.
rename Ha into Hb.
remember (repeat 0%L a ++ [1%L]) as la eqn:Hla.
assert (Ha : la ≠ []). {
  intros H; subst la.
  now apply app_eq_nil in H.
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
apply (lap_mul_assoc Heb Hos).
Qed.

Theorem lap_x_power_has_polyn_prop :
  rngl_characteristic ≠ 1 →
  rngl_has_eqb = true →
  ∀ n, has_polyn_prop (lap_x_power n) = true.
Proof.
intros Hch Heb *.
apply Bool.orb_true_iff.
right.
destruct n; cbn. {
  apply (rngl_neqb_neq Heb).
  now apply rngl_1_neq_0_iff.
}
rewrite last_last.
remember (repeat 0%L n ++ [1%L]) as la eqn:Hla; symmetry in Hla.
destruct la as [| a]. {
  now apply app_eq_nil in Hla.
}
apply (rngl_neqb_neq Heb).
now apply rngl_1_neq_0_iff.
Qed.

Theorem lap_norm_x_power :
  rngl_characteristic ≠ 1 →
  rngl_has_eqb = true →
  ∀ n, lap_norm (lap_x_power n) = lap_x_power n.
Proof.
intros Hch Heb *.
apply (has_polyn_prop_lap_norm Heb).
apply (lap_x_power_has_polyn_prop Hch Heb).
Qed.

Theorem polyn_x_power_add :
  rngl_has_opp_or_subt = true →
  rngl_has_eqb = true →
  ∀ a b, polyn_x_power (a + b) = (polyn_x_power a * polyn_x_power b)%pol.
Proof.
intros Hos Heb *.
destruct (Nat.eq_dec rngl_characteristic 1) as [Hch| Hch]. {
  specialize (rngl_characteristic_1 Hos Hch) as H1.
  apply eq_polyn_eq.
  apply (eq_list_eq 0%L). 2: {
    intros i Hi.
    rewrite H1; symmetry.
    now rewrite H1.
  }
  cbn.
  rewrite (lap_mul_norm_idemp_l Hos Heb).
  rewrite (lap_mul_norm_idemp_r Hos Heb).
  specialize (all_0_lap_norm_nil Heb) as H2.
  rewrite (proj1 (H2 _)); [ | intros; apply H1 ].
  rewrite (proj1 (H2 _)); [ | intros; apply H1 ].
  easy.
}
apply eq_polyn_eq; cbn.
f_equal.
rewrite (lap_x_power_add Hos Heb).
now do 2 rewrite (lap_norm_x_power Hch Heb).
Qed.

Theorem lap_norm_mul_x_power_r :
  rngl_has_opp_or_subt = true →
  rngl_has_inv = true →
  rngl_characteristic ≠ 1 →
  rngl_has_eqb = true →
  ∀ la n,
  lap_norm (la * lap_x_power n) = (lap_norm la * lap_x_power n)%lap.
Proof.
intros Hos Hiv Hch Heb *.
rewrite <- (lap_mul_norm_idemp_l Hos Heb).
rewrite (lap_norm_mul Hos Heb Hiv); [ easy | | ]. {
  apply polyn_norm_prop.
}
apply (lap_x_power_has_polyn_prop Hch Heb).
Qed.

Theorem polyn_of_const_add :
  ∀ (Hos : rngl_has_opp_or_subt = true),
  ∀ (Heb : rngl_has_eqb = true),
  ∀ (rop := polyn_ring_like_op Hos Heb),
  ∀ a b,
  polyn_of_const (a + b) = (polyn_of_const a + polyn_of_const b)%L.
Proof.
intros.
apply eq_polyn_eq; cbn.
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Hab| Hab]. {
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Ha| Ha]. {
    apply (rngl_eqb_eq Heb) in Ha; subst a.
    now rewrite rngl_add_0_l in Hab; rewrite Hab.
  }
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Hb| Hb]. {
    apply (rngl_eqb_eq Heb) in Hb; subst b.
    now rewrite rngl_add_0_r, Ha in Hab.
  }
  cbn.
  now rewrite Hab.
} {
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Ha| Ha]. {
    apply (rngl_eqb_eq Heb) in Ha; subst a.
    rewrite rngl_add_0_l in Hab; rewrite Hab.
    now cbn; rewrite rngl_add_0_l; rewrite Hab.
  }
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Hb| Hb]. {
    apply (rngl_eqb_eq Heb) in Hb; subst b.
    now cbn; rewrite rngl_add_0_r; rewrite Ha.
  }
  now cbn; rewrite Hab.
}
Qed.

Theorem polyn_of_const_mul :
  (rngl_is_integral || rngl_has_inv_or_quot)%bool = true →
  ∀ (Hos : rngl_has_opp_or_subt = true),
  ∀ (Heb : rngl_has_eqb = true),
  ∀ (rop := polyn_ring_like_op Hos Heb),
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
  apply (rngl_eqb_eq Heb) in Hab.
  apply (rngl_eqb_neq Heb) in Ha, Hb.
  now apply (rngl_eq_mul_0_r Hos) in Hab.
}
apply (rngl_eqb_neq Heb) in Hab.
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Ha| Ha]. {
  apply (rngl_eqb_eq Heb) in Ha; subst a.
  now rewrite (rngl_mul_0_l Hos) in Hab.
}
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Hb| Hb]. {
  apply (rngl_eqb_eq Heb) in Hb; subst b.
  now rewrite (rngl_mul_0_r Hos) in Hab.
}
cbn.
rewrite rngl_summation_only_one.
rewrite if_bool_if_dec.
apply (rngl_eqb_neq Heb) in Hab.
destruct (Sumbool.sumbool_of_bool _); [ | easy ].
congruence.
Qed.

Theorem polyn_of_const_rngl_summation :
  ∀ (Hos : rngl_has_opp_or_subt = true),
  ∀ (Heb : rngl_has_eqb = true),
  ∀ (rop := polyn_ring_like_op Hos Heb),
  ∀ b e f,
  polyn_of_const (∑ (i = b, e), f i) = ∑ (i = b, e), polyn_of_const (f i).
Proof.
intros.
unfold iter_seq.
remember (S e - b) as n eqn:Hn.
clear e Hn.
revert b.
induction n; intros. {
  rewrite rngl_summation_list_empty; [ | easy ].
  rewrite rngl_summation_list_empty; [ | easy ].
  apply eq_polyn_eq; cbn.
  now rewrite (rngl_eqb_refl Heb).
}
rewrite seq_S.
rewrite rngl_summation_list_app.
set (rpp := @polyn_ring_like_prop T ro rp Hos Heb).
rewrite rngl_summation_list_app.
rewrite (polyn_of_const_add Hos Heb).
rewrite IHn.
f_equal.
now do 2 rewrite rngl_summation_list_only_one.
Qed.

Theorem polyn_of_const_opp :
  rngl_has_opp = true →
  rngl_has_eqb = true →
  ∀ a, polyn_of_const (- a) = (- polyn_of_const a)%pol.
Proof.
intros Hop Heb *.
apply eq_polyn_eq; cbn.
do 2 rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Ha| Ha]. {
  apply (rngl_eqb_eq Heb) in Ha.
  destruct (Sumbool.sumbool_of_bool _) as [Hb| Hb]; [ easy | ].
  apply (rngl_eqb_neq Heb) in Hb.
  apply (f_equal rngl_opp) in Ha.
  rewrite (rngl_opp_involutive Hop) in Ha.
  now rewrite (rngl_opp_0 Hop) in Ha.
} {
  apply (rngl_eqb_neq Heb) in Ha.
  destruct (Sumbool.sumbool_of_bool _) as [Hb| Hb]. {
    apply (rngl_eqb_eq Heb) in Hb.
    now rewrite Hb, (rngl_opp_0 Hop) in Ha.
  }
  cbn.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Hc| Hc]; [ | easy ].
  now apply (rngl_eqb_eq Heb) in Hc.
}
Qed.

Theorem polyn_has_opp_or_subt :
  ∀ (Hop : rngl_has_opp = true),
  ∀ (Heb : rngl_has_eqb = true),
  ∀ (Hos := rngl_has_opp_has_opp_or_subt Hop),
  ∀ (rop := polyn_ring_like_op Hos Heb),
  @rngl_has_opp_or_subt (polyn T) rop = true.
Proof.
intros.
subst rop Hos.
unfold rngl_has_opp in Hop.
unfold rngl_has_opp_or_subt; cbn.
unfold polyn_opt_opp_or_subt.
remember rngl_opt_opp_or_subt as os eqn:Hos; symmetry in Hos.
destruct os; [ | easy ].
now destruct s.
Qed.

Theorem lap_norm_opp :
  rngl_has_opp = true →
  rngl_has_eqb = true →
  ∀ la, lap_norm (- la) = (- lap_norm la)%lap.
Proof.
intros Hop Heb *.
unfold lap_norm, lap_opp.
rewrite map_rev; f_equal.
rewrite <- map_rev.
remember (rev la) as lb eqn:Hlb.
clear la Hlb; rename lb into la.
induction la as [| a]; [ easy | cbn ].
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Hoaz| Hoaz]. {
  apply (rngl_eqb_eq Heb) in Hoaz.
  apply (f_equal rngl_opp) in Hoaz.
  rewrite (rngl_opp_involutive Hop) in Hoaz.
  rewrite (rngl_opp_0 Hop) in Hoaz.
  apply (rngl_eqb_eq Heb) in Hoaz; rewrite Hoaz.
  apply IHla.
} {
  apply (rngl_eqb_neq Heb) in Hoaz.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
    apply (rngl_eqb_eq Heb) in Haz; subst a.
    now rewrite (rngl_opp_0 Hop) in Hoaz.
  }
  easy.
}
Qed.

Definition rngl_has_opp_has_opp_or_subt (Hop : rngl_has_opp = true) :=
  match rngl_has_opp_or_subt_iff with
  | conj x x0 => x0
  end (or_introl Hop).

Theorem polyn_of_const_minus_one_pow :
  ∀ (Hop : rngl_has_opp = true),
  ∀ (Heb : rngl_has_eqb = true),
  ∀ (rop := polyn_ring_like_op (rngl_has_opp_has_opp_or_subt Hop) Heb),
  ∀ n, polyn_of_const (minus_one_pow n) = minus_one_pow n.
Proof.
intros.
set (Hos := rngl_has_opp_has_opp_or_subt Hop) in rop.
destruct (Nat.eq_dec rngl_characteristic 1) as [Hch| Hch]. {
  specialize (rngl_characteristic_1 Hos Hch) as H1.
  apply eq_polyn_eq; cbn.
  rewrite (H1 (minus_one_pow n)).
  rewrite (rngl_eqb_refl Heb); cbn.
  specialize @polyn_characteristic_prop as H2.
  set (rpp := @polyn_ring_like_prop T ro rp Hos Heb).
  specialize (H2 (polyn T) rop rpp).
  assert (Hosp : @rngl_has_opp_or_subt (polyn T) rop = true). {
    now specialize (polyn_has_opp_or_subt Hop Heb) as H3.
  }
  specialize (H2 Hosp).
  assert (Hebp : @rngl_has_eqb (polyn T) rop = true) by easy.
  specialize (H2 Hebp).
  cbn in H2.
  rewrite Hch in H2.
  cbn in H2.
  destruct H2 as (_, H2).
  (* faudrait un polyn_add_0_r *)
  rewrite polyn_add_comm in H2.
  rewrite polyn_add_0_l in H2; [ | easy ].
  unfold minus_one_pow.
  destruct (n mod 2); cbn. {
    now rewrite (H1 1%L), (rngl_eqb_refl Heb).
  }
  unfold polyn_one, polyn_of_const, polyn_of_norm_lap; cbn.
  clear - H1 Heb.
  rewrite (H1 1%L).
  unfold rngl_opp; cbn.
  unfold polyn_opt_opp_or_subt.
  subst Hos; cbn.
  specialize (proj2 rngl_has_opp_or_subt_iff (or_introl Hop)) as H2.
  unfold rngl_has_opp_or_subt in H2.
  destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
  destruct os as [opp| subt ]; [ | easy ].
  subst rop; cbn.
  now rewrite (rngl_eqb_refl Heb); cbn.
}
apply eq_polyn_eq; cbn.
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Hmz| Hmz]; cbn. {
  apply (rngl_eqb_eq Heb) in Hmz.
  subst rop; cbn.
  unfold polyn_ring_like_op; cbn.
  unfold Hos; cbn.
  unfold minus_one_pow in Hmz |-*.
  destruct (n mod 2); cbn. {
    now apply (rngl_eqb_eq Heb) in Hmz; rewrite Hmz.
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
  apply (rngl_eqb_eq Heb) in H10.
  now apply rngl_1_neq_0_iff in Hch.
}
unfold rngl_opp; cbn.
specialize (proj2 rngl_has_opp_or_subt_iff (or_introl Hop)) as H2.
unfold rngl_has_opp_or_subt in H2.
unfold polyn_opt_opp_or_subt; cbn.
remember rngl_opt_opp_or_subt as os eqn:Hos'; symmetry in Hos'.
destruct os as [os| ]; [ | easy ].
subst rop; cbn.
destruct os as [opp| subt ]. {
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
    apply (rngl_eqb_eq Heb) in H10.
    now apply rngl_1_neq_0_iff in Hch.
  }
  cbn.
  rewrite Hoo.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [H11| H11]; [ | easy ].
  apply (rngl_eqb_eq Heb) in H11.
  apply (f_equal rngl_opp) in H11.
  rewrite (rngl_opp_involutive Hop) in H11.
  rewrite (rngl_opp_0 Hop) in H11.
  now apply rngl_1_neq_0_iff in Hch.
}
generalize Hop; intros Hsu.
apply rngl_has_opp_has_no_subt in Hsu.
move Hsu before Hop.
unfold rngl_has_subt in Hsu.
now rewrite Hos' in Hsu.
Qed.

(* U and V such that PU+QV=res(P,Q) *)
(* see Serge Lang's book, "Algebra", section "the resultant" *)
Definition lap_bezout_resultant_coeff (P Q : list T) :=
  let rol := lap_ring_like_op in
  let n := length P - 1 in
  let m := length Q - 1 in
  let s := rlap_sylvester_list_list (rev P) (rev Q) in
  (∑ (i = 0, m - 1),
     let j := (m - 1 - i)%nat in
     let s' := mk_mat (map (λ l, firstn (length l - 1) l) (butn i s)) in
     (minus_one_pow (m + n - i + 1) * (repeat 0%L j ++ [det s']))%lap,
   ∑ (i = m, m + n - 1),
     let j := (m + n - 1 - i)%nat in
     let s' := mk_mat (map (λ l, firstn (length l - 1) l) (butn i s)) in
     (minus_one_pow (m + n + i + 1) * (repeat 0%L j ++ [det s']))%lap).

Theorem lap_bezout_is_resultant : in_charac_0_field →
  ∀ (P Q U V : list T),
  2 ≤ length P
  → 2 ≤ length Q
  → lap_bezout_resultant_coeff P Q = (U, V)
  → lap_norm (U * P + V * Q)%lap = lap_norm [lap_resultant P Q].
Proof.
intros Hif * H2p H2q Hbr.
unfold lap_bezout_resultant_coeff in Hbr.
remember lap_ring_like_op as rol eqn:Hrol.
injection Hbr; clear Hbr; intros HV HU.
subst rol.
remember (length P - 1) as n eqn:Hn.
remember (length Q - 1) as m eqn:Hm.
remember (rlap_sylvester_list_list (rev P) (rev Q)) as ll eqn:Hll.
move m before n.
unfold lap_resultant.
unfold rlap_sylvester_mat.
rewrite <- Hll.
specialize @cramer's_rule_by_mul as Hcr.
specialize (Hcr (polyn T)).
assert (Hos : rngl_has_opp_or_subt = true). {
  apply rngl_has_opp_or_subt_iff; left.
  apply (cf_has_opp Hif).
}
set (rop := polyn_ring_like_op Hos (cf_has_eqb Hif)).
set (rpp := @polyn_ring_like_prop T ro rp Hos (cf_has_eqb Hif)).
specialize (Hcr rop rpp).
cbn - [ det ] in Hcr.
generalize Hif; intros H.
destruct H as (Hic, Hop, Hin, Hit, Heb, Hch).
assert (Hopp : @rngl_has_opp (@polyn T ro) rop = true). {
  unfold rngl_has_opp; cbn.
  unfold polyn_opt_opp_or_subt.
  unfold rngl_has_opp in Hop.
  destruct rngl_opt_opp_or_subt as [s| ]; [ | easy ].
  now destruct s.
}
specialize (Hcr Hopp Hic Hch).
assert (H : (@rngl_is_integral T ro rp || rngl_has_inv_or_quot)%bool = true). {
  apply Bool.orb_true_iff; right.
  apply rngl_has_inv_or_quot_iff.
  unfold rngl_has_inv, rngl_has_quot; cbn.
  unfold polyn_opt_inv_or_quot.
  rewrite Hic, Hop, Hin; cbn.
  unfold rngl_has_inv in Hin.
  destruct rngl_opt_inv_or_quot; [ now right | easy ].
}
specialize (Hcr H); clear H.
assert
  (H : ∀ A (ro : ring_like_op A) (p q : list A),
     polyn_of_norm_lap p = polyn_of_norm_lap q → lap_norm p = lap_norm q). {
  intros * H.
  now apply eq_polyn_eq in H.
}
apply H; clear H.
remember (mk_mat (map (λ l, map polyn_of_const l) ll)) as sm eqn:Hsm.
specialize (Hcr sm).
(* u is the vector [X^(n+m-1) X^(n+m-2) ... X 1] *)
remember (mk_vect (map (@polyn_x_power _ ro) (rev (seq 0 (n + m)))))
  as u eqn:Hu.
specialize (Hcr u).
(* v is the vector [X^(m-1)P X^(m-2)P ... XP P X^(n-1)Q X^(n-2)Q ... XQ Q] *)
remember
  (mk_vect
     (map (λ i, polyn_of_norm_lap (lap_x_power i * P)%lap) (rev (seq 0 m)) ++
     (map (λ i, polyn_of_norm_lap (lap_x_power i * Q)%lap) (rev (seq 0 n)))))
  as v eqn:Hv.
specialize (Hcr v).
assert (H : is_square_matrix sm = true). {
  clear - H2p H2q Hll Hsm.
  rewrite Hsm.
  apply Bool.andb_true_iff.
  split. {
    apply Bool.orb_true_iff.
    unfold mat_nrows, mat_ncols; cbn.
    rewrite map_length.
    destruct (Nat.eq_dec (length ll) 0) as [Hllz| Hllz]; [ right | left ]. {
      now rewrite Hllz.
    }
    destruct ll as [| la]; [ easy | clear Hllz; cbn ].
    rewrite map_length.
    apply Bool.negb_true_iff.
    apply Nat.eqb_neq.
    intros H; apply length_zero_iff_nil in H; subst la.
    move Hll at bottom.
    destruct P as [| a1]; [ easy | ].
    cbn in H2p; apply Nat.succ_le_mono in H2p.
    destruct P as [| a2]; [ easy | clear H2p ].
    destruct Q as [| b1]; [ easy | ].
    cbn in H2q; apply Nat.succ_le_mono in H2q.
    destruct Q as [| b2]; [ easy | clear H2q ].
    cbn in Hll.
    do 4 rewrite app_length in Hll.
    do 2 rewrite rev_length in Hll.
    cbn in Hll.
    do 4 rewrite Nat.add_sub in Hll.
    do 2 rewrite Nat.add_1_r in Hll.
    cbn in Hll.
    injection Hll; clear Hll; intros H1 H2.
    now destruct (rev P).
  } {
    move Hll at bottom.
    cbn; rewrite map_length.
    unfold iter_list.
    rewrite List_fold_left_map.
    specialize iter_list_eq_compat as H1.
    unfold iter_list in H1.
    erewrite H1; [ | now intros; rewrite map_length ].
    clear H1.
    rewrite fold_iter_list.
    apply all_true_and_list_true_iff.
    intros la Hla.
    apply Nat.eqb_eq.
    rewrite Hll in Hla |-*.
    rewrite rlap_sylvester_list_list_length.
    do 2 rewrite rev_length.
    apply in_app_or in Hla.
    do 2 rewrite rev_length in Hla.
    destruct Hla as [Hla| Hla]. {
      apply in_map_iff in Hla.
      destruct Hla as (i & Hi & His); subst la.
      do 2 rewrite app_length.
      rewrite rev_length.
      do 2 rewrite repeat_length.
      apply in_seq in His.
      flia H2p His.
    } {
      apply in_map_iff in Hla.
      destruct Hla as (i & Hi & His); subst la.
      do 2 rewrite app_length.
      rewrite rev_length.
      do 2 rewrite repeat_length.
      apply in_seq in His.
      flia H2q His.
    }
  }
}
specialize (Hcr H); clear H.
assert (H : vect_size u = mat_nrows sm). {
  rewrite Hu, Hsm; cbn.
  do 2 rewrite map_length.
  rewrite rev_length, seq_length.
  symmetry.
  rewrite Hll.
  rewrite rlap_sylvester_list_list_length.
  rewrite Hn, Hm.
  now do 2 rewrite rev_length.
}
specialize (Hcr H); clear H.
assert (H : (sm • u)%V = v). {
  clear - rpp Hsm Hu Hv Hll Hn Hm H2p H2q Hic Heb Hop.
  rewrite Hsm, Hu, Hv.
  unfold mat_mul_vect_r; f_equal; cbn.
  rewrite map_map.
  unfold vect_dot_mul.
  cbn - [ rngl_add rngl_zero ].
  rewrite Hll.
  unfold rlap_sylvester_list_list.
  rewrite map_app.
  do 2 rewrite map_map.
  do 2 rewrite rev_length.
  rewrite <- Hn, <- Hm.
  assert (H :
    ∀ (P Q : list T) n m,
    2 ≤ length P
    → 2 ≤ length Q
    → n = length P - 1
    → m = length Q - 1 →
      map
        (λ i,
           ∑ (t ∈
              map2 polyn_mul
                (map polyn_of_const
                   (repeat 0%L i ++ rev P ++ repeat 0%L (m - 1 - i)))
                (map polyn_x_power (rev (seq 0 (n + m))))),
             t) (seq 0 m) =
      map (λ i, polyn_of_norm_lap (lap_x_power i * P)) (rev (seq 0 m))). {
    clear P Q n m H2p H2q Hn Hm Hll Hv (*HU HV*) Hu.
    intros * H2p H2q Hn Hm.
    erewrite map_ext_in. 2: {
      intros i Hi.
      apply in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
      erewrite List_map_map_seq with (d := 0%L).
      do 2 rewrite app_length.
      do 2 rewrite repeat_length.
      rewrite rev_length.
      replace (i + (length P + (m - 1 - i))) with (n + m) by flia Hi H2p Hn.
      rewrite map2_map_l.
      rewrite map2_map_r.
      rewrite map2_rev_seq_r.
      rewrite map2_diag.
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
    apply map_ext_in.
    intros i Hi.
    apply in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
    rewrite Nat.mul_0_r, Nat.add_0_l.
    unfold polyn_of_norm_lap.
    rewrite rngl_summation_split with (j := i); [ | flia Hi ].
    rewrite all_0_rngl_summation_0. 2: {
      intros j Hj.
      rewrite app_nth1; [ | rewrite repeat_length; flia Hj ].
      rewrite nth_repeat; cbn.
      unfold polyn_of_const; cbn.
      unfold polyn_of_norm_lap; cbn.
      apply eq_polyn_eq; cbn.
      now rewrite (rngl_eqb_refl Heb).
    }
    rewrite rngl_add_0_l.
    rewrite rngl_summation_shift with (s := i); [ | flia Hi ].
    rewrite Nat.add_comm, Nat.add_sub.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite app_nth2; [ | rewrite repeat_length; flia Hj ].
      rewrite repeat_length.
      rewrite Nat_sub_sub_swap, Nat.add_comm, Nat.add_sub.
      easy.
    }
    remember (∑ (j = _, _), _) as x in |-*; subst x.
    rewrite rngl_summation_split with (j := length P). 2: {
      rewrite Hn; flia Hi.
    }
    rewrite all_0_rngl_summation_0 with (b := length P + 1). 2: {
      intros j Hj.
      rewrite app_nth2; [ | rewrite rev_length; flia Hj ].
      rewrite nth_repeat; cbn.
      unfold polyn_of_const; cbn.
      unfold polyn_of_norm_lap; cbn.
      apply eq_polyn_eq; cbn.
      now rewrite (rngl_eqb_refl Heb).
    }
    rewrite rngl_add_0_r.
    remember (∑ (j = _, _), _) as x in |-*; subst x.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      rewrite app_nth1; [ | rewrite rev_length; flia Hj ].
      easy.
    }
    remember (∑ (j = _, _), _) as x in |-*; subst x.
    rewrite Hn, Hm.
    remember (length P) as n' eqn:Hn'.
    remember (length Q) as m' eqn:Hm'.
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
      rewrite rev_nth; [ | rewrite <- Hn'; flia Hj ].
      rewrite <- Hn'.
      replace (n - S (n - j)) with (j - 1) by flia Hj.
      rewrite (polyn_mul_comm Hic).
      rewrite (polyn_x_power_add Hos Heb).
      replace polyn_mul with rngl_mul by easy.
      rewrite <- rngl_mul_assoc.
      easy.
    }
    remember (∑ (j = _, _), _) as x in |-*; subst x.
    rewrite <- rngl_mul_summation_distr_l. 2: {
      clear - Hop.
      unfold rngl_has_opp_or_subt in Hos |-*; cbn.
      unfold rngl_has_opp in Hop.
      subst rop.
      unfold polyn_opt_opp_or_subt.
      remember rngl_opt_opp_or_subt as x eqn:Hx.
      destruct x as [x| ]; [ | easy ].
      now destruct x.
    }
    apply eq_polyn_eq.
    cbn - [ rngl_zero rngl_add ].
    rewrite (lap_mul_norm_idemp_l Hos Heb).
    rewrite <- (lap_mul_norm_idemp_r Hos Heb _ P).
    rewrite <- (lap_mul_norm_idemp_r Hos Heb).
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
         (polyn_x_power (i - 1) * polyn_of_const (nth (i - 1) P 0%L))%pol).
    erewrite rngl_summation_eq_compat. 2: {
      intros i Hi.
      fold (f P i).
      easy.
    }
    specialize (lap_norm_lap_rngl_summation Hos Heb) as H1.
    specialize (H1 1 (length P) (f P)).
    remember (@lap T ro (∑ (i = 1, @length T P), f P i)) as x eqn:Hx.
    rewrite H1; subst x; clear H1.
    subst f.
    cbn - [ rngl_zero rngl_add polyn_of_const ].
    erewrite rngl_summation_eq_compat. 2: {
      intros i Hi.
      rewrite (lap_mul_norm_idemp_l Hos Heb).
      easy.
    }
    cbn - [ rngl_zero rngl_add polyn_of_const ].
    rewrite (lap_norm_rngl_summation_idemp Heb).
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
    clear - rp Hos Heb.
    induction P as [| a la ]; [ easy | ].
    cbn - [ rngl_zero rngl_add lap_norm nth ].
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
      rewrite (lap_x_power_add Hos Heb).
      unfold lap_x_power at 1.
      cbn - [ rngl_zero rngl_add lap_norm nth lap_mul ].
      rewrite <- (lap_mul_assoc Heb Hos).
      easy.
    }
    remember (λ j, _) as x in |-*; subst x.
    cbn - [ rngl_zero rngl_add lap_norm nth lap_mul ].
    rewrite (lap_mul_const_l Hos).
    erewrite map_ext_in; [ | now intros; rewrite rngl_mul_1_l ].
    rewrite map_id.
    replace (@lap_mul T ro) with (@rngl_mul (list T) (@lap_ring_like_op T ro)) by easy.
    set (rpl := @lap_ring_like_prop T ro rp Heb Hos).
    rewrite <- (rngl_mul_summation_distr_l). 2: {
Print lap_ring_like_op.
Print lap_opt_opp_or_subt.
...
      cbn.
(* chiasse *)
...
(**)
specialize (@rngl_mul_summation_distr_l (list T)) as H1.
specialize (H1 lap_ring_like_op (lap_ring_like_prop Heb Hos)).
assert (H : @rngl_has_opp_or_subt (list T) lap_ring_like_op = true).
...
specialize (H1 H); clear H.
specialize (H1 [0%L; 1%L] 1 (length la)).
specialize (H1 (λ i, (lap_x_power (i - 1) * lap_norm [nth (i - 1) la 0%L]))%lap).
remember [0;1]%L as x in H1; subst x.
cbn - [ lap_norm rngl_zero rngl_add lap_mul ].
...
rewrite <- H1.
remember
         (@iter_seq (list T) (S O) (@length T la)
            (fun (c : list T) (i : nat) =>
             @rngl_add (list T) (@lap_ring_like_op T ro) c
               (@rngl_mul (list T) (@lap_ring_like_op T ro)
                  (@cons T (@rngl_zero T ro)
                     (@cons T (@rngl_one T ro) (@nil T)))
                  (@lap_mul T ro (@lap_x_power T ro (sub i (S O)))
                     (@lap_norm T ro
                        (@cons T (@nth T (sub i (S O)) la (@rngl_zero T ro))
                           (@nil T))))))
            (@rngl_zero (list T) (@lap_ring_like_op T ro)))
as x eqn:Hx.
remember
(@iter_seq (list T) (S O) (@length T la)
             (fun (j : list T) (i : nat) =>
              @rngl_add (list T) (@lap_ring_like_op T ro) j
                (@lap_mul T ro
                   (@cons T (@rngl_zero T ro)
                      (@cons T (@rngl_one T ro) (@nil T)))
                   (@lap_mul T ro (@lap_x_power T ro (Nat.sub i (S O)))
                      (@lap_norm T ro
                         (@cons T
                            (@nth T (Nat.sub i (S O)) la (@rngl_zero T ro))
                            (@nil T))))))
             (@rngl_zero (list T) (@lap_ring_like_op T ro)))
as y eqn:Hy.
move y before x.
move Hy before Hx.
unfold lap_ring_like_op in Hy.
cbn - [ lap_norm rngl_zero rngl_add lap_mul ] in Hy.
rewrite <- H1.
...
cbn - [ lap_norm rngl_zero rngl_add lap_mul ].
...
rewrite <- rngl_mul_summation_distr_l.
...
    (* all these complications to rewrite with rngl_mul_summation_distr_l
       on "lap" that is not a ring like *)
    specialize mul_iter_list_distr_l as H1.
    specialize (H1 (list T) nat [0; 1]%L (seq 1 (S (length la) - 1))).
    specialize
      (H1 (λ i, (lap_x_power (i - 1) * lap_norm [nth (i - 1) la 0%L])%lap)).
    specialize (H1 lap_add lap_mul).
    specialize (H1 []).
    rewrite lap_mul_0_r in H1.
    cbn - [ lap_add lap_mul lap_x_power lap_norm seq minus ] in H1.
    unfold iter_seq.
    unfold iter_list in H1 |-*.
    cbn - [ lap_add lap_mul lap_x_power lap_norm seq minus ].
...
    rewrite <- H1; clear H1. 2: {
      intros y z.
     apply lap_mul_add_distr_l; [ easy | easy | easy ].
    }
    rewrite fold_iter_list.
    rewrite fold_iter_seq.
    replace (@nil T) with (@rngl_zero (list T) lap_ring_like_op) at 3 by easy.
    replace lap_add with (@rngl_add (list T) lap_ring_like_op) by easy.
...
    unfold rngl_add at 1.
    cbn - [ rngl_zero rngl_add lap_x_power lap_norm lap_mul ].
    rewrite (lap_add_norm_idemp_l Heb).
    remember (∑ (i = _, _), _) as x eqn:Hx in |-*.
    rewrite (lap_cons Hos).
    rewrite <- (lap_add_norm_idemp_r Heb); symmetry.
    rewrite <- (lap_add_norm_idemp_r Heb); symmetry.
    f_equal; f_equal.
    rewrite <- (lap_mul_norm_idemp_r Hos Heb); symmetry.
    rewrite <- (lap_mul_norm_idemp_r Hos Heb); symmetry.
    f_equal; f_equal.
    subst x.
    apply IHla.
  }
  f_equal; [ now apply (H P Q) | now rewrite Nat.add_comm; apply (H Q P) ].
}
unfold polyn_of_norm_lap.
apply eq_polyn_eq; cbn - [ det lap_norm ].
specialize (Hcr H); clear H.
move Hcr at bottom.
replace (mat_nrows sm) with (n + m) in Hcr. 2: {
  rewrite Hsm, Hll; cbn.
  rewrite map_length.
  rewrite rlap_sylvester_list_list_length.
  do 2 rewrite rev_length.
  now rewrite <- Hn, <- Hm.
}
rewrite Hu in Hcr.
cbn - [ det ] in Hcr.
assert
  (H : ∀ i, 1 ≤ i ≤ n + m →
    (det sm * polyn_of_norm_lap (lap_x_power (n + m - i)))%pol =
    det (mat_repl_vect i sm v)). {
  intros i Hi.
  rewrite <- Hcr; [ | easy ]; f_equal.
  rewrite (List_map_nth' 0). 2: {
    rewrite rev_length, seq_length.
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
  rewrite lap_norm_x_power; [ easy | now rewrite Hch | easy ].
}
clear Hcr; rename H into Hcr.
assert
  (H : ∀ i, 1 ≤ i ≤ n + m →
     (lap_norm (lap (det sm)) * lap_x_power (n + m - i))%lap =
     lap (det (mat_repl_vect i sm v))). {
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
assert (H : det sm = polyn_of_const (det (mk_mat ll))). {
  rewrite Hsm.
Theorem det_polyn_of_const :
  (rngl_is_integral || rngl_has_inv_or_quot)%bool = true →
  rngl_characteristic ≠ 1 →
  ∀ (Hos : rngl_has_opp_or_subt = true),
  ∀ (Heb : rngl_has_eqb = true),
  ∀ (rop := polyn_ring_like_op Hos Heb),
  ∀ (ll : list (list T)),
  det {| mat_list_list := map (λ l, map polyn_of_const l) ll |} =
  polyn_of_const (det {| mat_list_list := ll |}).
Proof.
intros Hii Hch *.
cbn.
rewrite map_length.
assert
  (H :
     ∀ len,
     determinant_loop len
        {| mat_list_list := map (λ l : list T, map polyn_of_const l) ll |} =
     polyn_of_const (determinant_loop len {| mat_list_list := ll |})). {
  intros.
  revert ll.
  induction len; intros; [ easy | ].
  cbn - [ rngl_zero rngl_add ].
  rewrite (polyn_of_const_rngl_summation Hos Heb).
  apply rngl_summation_eq_compat.
  intros i Hi.
  rewrite (polyn_of_const_mul Hii Hos Heb).
  rewrite (polyn_of_const_mul Hii Hos Heb).
...
  rewrite (List_map_nth' []).
...
induction ll as [| la]. {
  apply eq_polyn_eq; cbn.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [H1| H1]; [ | easy ].
  apply (rngl_eqb_eq Heb) in H1.
  now apply rngl_1_neq_0_iff in Hch.
}
cbn.
rewrite map_length.
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
  lap_compose (map (λ i, [i]) l) [[0; 1]; [-1]]%L.
Definition lap_compose_y_div_x A {ro : ring_like_op A} (l : list A) :=
  map (λ i, repeat 0%L (length l - 1 - i) ++ [nth (length l - 1 - i) l 0%L])
    (seq 0 (length l)).
Compute (
  let qro := Q_ring_like_op in
  let rla := [1;0;1] in
  let rlb := [1;0;-2] in
  let (U, V) := lap_bezout_resultant_coeff (rev rla) (rev rlb) in
  ((U * rev rla + V * rev rlb)%lap, lap_resultant rla rlb)).
(* oui *)
Compute (
  let qro := Q_ring_like_op in
  let lro := lap_ring_like_op in
  let rla := [1;0;1] in
  let rlb := [1;0;-2] in
  let p := map (λ i, [i]) (rev rla) in
  let q := lap_compose_y_minus_x (rev rlb) in
  let (U, V) := lap_bezout_resultant_coeff p q in
  ((U * p + V * q)%lap, lap_resultant p q)).
(* oui !!! *)
Compute (
  let qro := Q_ring_like_op in
  let lro := lap_ring_like_op in
  let rla := [1;0;1] in
  let rlb := [1;0;-2] in
  let p := map (λ i, [i]) (rev rla) in
  let q := lap_compose_y_div_x (rev rlb) in
  let (U, V) := lap_bezout_resultant_coeff p q in
  ((U * p + V * q)%lap, lap_resultant p q)).
Compute (
  let qro := Q_ring_like_op in
  let lro := lap_ring_like_op in
  let rla := [1;0;1] in
  let rlb := [1;0;0;-2] in
  let p := map (λ i, [i]) (rev rla) in
  let q := lap_compose_y_minus_x (rev rlb) in
  let (U, V) := lap_bezout_resultant_coeff p q in
  ((U * p + V * q)%lap, lap_resultant p q)).
(* oui *)
Compute (
  let qro := Q_ring_like_op in
  let lro := lap_ring_like_op in
  let rla := [1;0;1] in
  let rlb := [1;0;0;-2] in
  let p := map (λ i, [i]) (rev rla) in
  let q := lap_compose_y_div_x (rev rlb) in
  let (U, V) := lap_bezout_resultant_coeff p q in
  ((U * p + V * q)%lap, lap_resultant p q)).
Compute (
  let qro := Q_ring_like_op in
  let lro := lap_ring_like_op in
  let rla := [1;-4] in
  let rlb := [1;0;0;0;-3] in
  let p := map (λ i, [i]) (rev rla) in
  let q := lap_compose_y_minus_x (rev rlb) in
  let (U, V) := lap_bezout_resultant_coeff p q in
  ((U * p + V * q)%lap, lap_resultant p q)).
(* oui *)
Compute (
  let qro := Q_ring_like_op in
  let lro := lap_ring_like_op in
  let rla := [1;-4] in
  let rlb := [1;0;0;0;-3] in
  let p := map (λ i, [i]) (rev rla) in
  let q := lap_compose_y_div_x (rev rlb) in
  let (U, V) := lap_bezout_resultant_coeff p q in
  ((U * p + V * q)%lap, lap_resultant p q)).
Compute (
  let qro := Q_ring_like_op in
  let lro := lap_ring_like_op in
  let rla := [1;-2] in
  let rlb := [1;-3] in
  let p := map (λ i, [i]) (rev rla) in
  let q := lap_compose_y_minus_x (rev rlb) in
  let (U, V) := lap_bezout_resultant_coeff p q in
  ((U * p + V * q)%lap, lap_resultant p q)).
(* oui *)
Compute (
  let qro := Q_ring_like_op in
  let lro := lap_ring_like_op in
  let rla := [1;0;0;-2] in
  let rlb := [1;0;0;-3] in
  let p := map (λ i, [i]) (rev rla) in
  let q := lap_compose_y_minus_x (rev rlb) in
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
...

(*
(* polynomial cancelling the sum of zeros of two polynomials p and q *)
(* e.g. if p=x²+1 and q=x²-2 whose zeros are, resp. i and √2, return
   a polynomial cancelling i+√2 (namely x⁴-2x²+9) *)
Definition algeb_add A {ro : ring_like_op A} {rol : ring_like_op _} p q :=
  lap_resultant (map (λ i, [i]) p) (lap_compose_y_minus_x q).

(* polynomial cancelling the product of zeros of two polynomials p and q *)
Definition algeb_mul A {ro : ring_like_op A} {rol : ring_like_op _} p q :=
  lap_resultant (map (λ i, [i]) p) (lap_compose_y_div_x q).

(*
Theorem algeb_add_cancelling :
  ∀ A (ro : ring_like_op A) (rol : ring_like_op (list A)) p q α β,
  eval_lap p α = 0%L
  → eval_lap q β = 0%L
  → eval_lap (algeb_add p q) (α + β)%L = 0%L.
Proof.
intros * Hp Hq.
remember (bezout_resultant_coeff (map (λ i, [i]) p) (lap_compose_y_minus_x q))
  as UV eqn:HUV.
symmetry in HUV.
destruct UV as (U, V).
...
intros * Hp Hq.
unfold lap_resultant.
unfold eval_lap in Hp, Hq.
rewrite <- map_rev.
unfold lap_compose.
rewrite <- map_rev.
cbn - [ det ].
remember (rev p) as rp eqn:Hrp.
remember (rev q) as rq eqn:Hrq.
clear p q Hrp Hrq.
move rq before rp.
...
unfold rlap_sylvester_mat.
unfold rlap_sylvester_list_list.
rewrite rev_length.
rewrite map_length.
...
*)

(* same, with powers in decreasing order, for testing and readability *)
Definition r_algeb_add A (ro : ring_like_op A) (rol : ring_like_op (list A))
    rp rq :=
  rev (algeb_add (rev rp) (rev rq)).

Definition r_algeb_mul A (ro : ring_like_op A) (rol : ring_like_op (list A))
    rp rq :=
  rev (algeb_mul (rev rp) (rev rq)).

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
  rlap_quot_rem _ [4; 0; 6] [2; 1]).
(*
     = ([2; -1], [7])
     : list Z * list Z
*)
Compute (
  let zro := Z_ring_like_op in
  rlap_quot_rem _ [1; 0; 1] [1; 0; -2]).
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
  rlap_quot_rem _ [4; 0; 6] [2; 1]).
(*
     = ([〈2〉; 〈-1〉], [〈7〉])
     : list Q * list Q
*)

Compute (
  let qro := Q_ring_like_op in
  rlap_quot_rem _ [1; 0; 1] [1; 0; -2]).
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
  let p' := map (λ i, [i]) p in
  let q' := map (λ i, [i]) q in
  rev
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
  let p' := map (λ i, [i]) p in
  let q' := map (λ i, [i]) q in
  lap_resultant
    (lap_compose p' [[0; 1]; [1]])%L
    (lap_compose q' [[0; 1]; [1]])%L.
Definition glip A (ro : ring_like_op A) (rol : ring_like_op (list A)) p :=
  let p' := map (λ i, [i]) p in
  @lap_compose (list A) rol p' [[0; 1]; [1]]%L.
Definition r_glop_add A (ro : ring_like_op A) (rol : ring_like_op (list A))
    rp rq :=
  rev (glop_add ro rol (rev rp) (rev rq)).
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
  rev (lap_resultant (rev rp) (rev rq))).
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
  rev (lap_resultant (rev rp) (rev rq))).
(* example in video https://www.youtube.com/watch?v=WvbAfhOH4ik *)
Compute (
  let qro := Q_ring_like_op in
  rlap_quot_rem _ [1;0;0;-2;8;1;0;-16;-2] [1;0;0;0;8;1]).

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
  let p := map (λ i, [i]) (rev rla) in
  let q := lap_compose (map (λ i, [i]) (rev rlb)) [[0; 1]; [-1]] in
  rev (lap_resultant p q)).
(*
Compute (
  let qro := Q_ring_like_op in
  let qrp := Q_ring_like_prop in
  let lro := lap_ring_like_op in
  let qlro := Q_list_ring_like_op in
  let rla := [1;0;1] in
  let rlb := [1;0;-2] in
  let p := map (λ i, [i]) (rev rla) in
  let q := lap_compose (map (λ i, [i]) (rev rlb)) [[0; 1]; [-1]] in
  lap_norm (rev (map (λ i, rev i) (rlap_resultant' _ p q)))).
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
  lap_resultant (rev rla) (rev rlb)).
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
  lap_resultant (rev [5;0;0;-7;5;-3]) (rev [1;0;0;0;-4;0;0;6])).
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

(* faudrait le prouver, que ce polynôme résultant (c'est le cas de
   le dire, puisqu'il faut passer par le "résultant") annule bien
   la somme des zéros des deux polynômes.
     À partir de ça, on pourrait définir un nombre algébrique comme
   étant le couple formé d'un polynôme et d'un entier "i" entre 1 et
   le degré dudit polynôme, représentant le i-ième zéro de ce polynôme.
     L'ennui, c'est comment ranger ces zéros ? dans quel ordre ? comment
   les identifier ? et si (P,i) et (Q,j) sont deux algébriques, leur
   somme serait le nombre algébrique (R,k). Pour R, on calcule le
   résultant, comme ci-dessus, mais comment déterminer k ? fonction de
   i et j, j'imagine, mais aussi peut-être de P et Q ? chais pas.
*)

(*
Theorem last_fold_left_lap_mul_const_add_const : ∀ la b c,
  last (fold_left (λ accu a, (accu * [b] + [a])%lap) la [c]) 0%L =
  fold_left (λ x y, (x * b + y)%L) la c.
Proof.
intros.
revert c.
induction la as [| a]; intros; [ easy | cbn ].
rewrite rngl_summation_only_one.
apply IHla.
Qed.

Theorem last_lap_add : ∀ la lb,
  last (la + lb)%lap 0%L =
    if length la <? length lb then last lb 0%L
    else if length lb <? length la then last la 0%L
    else (last la 0 + last lb 0)%L.
Proof.
intros.
rewrite if_bool_if_dec.
destruct (bool_dec _) as [Hab| Hab]. {
  apply Nat.ltb_lt in Hab.
  revert lb Hab.
  induction la as [| a]; intros; [ easy | cbn ].
  destruct lb as [| b]; [ cbn in Hab; flia Hab | ].
  cbn in Hab.
  apply Nat.succ_lt_mono in Hab.
  specialize (IHla _ Hab).
  destruct lb as [| b1]; [ easy | ].
  rewrite List_last_cons_cons.
  destruct la as [| a1]; [ | easy ].
  cbn - [ last ].
  now rewrite List_last_cons_cons.
}
rewrite if_bool_if_dec.
destruct (bool_dec _) as [Hba| Hba]. {
  clear Hab.
  apply Nat.ltb_lt in Hba.
  revert la Hba.
  induction lb as [| b]; intros; [ now rewrite lap_add_0_r | ].
  destruct la as [| a]; [ cbn in Hba; flia Hba | ].
  cbn in Hba.
  apply Nat.succ_lt_mono in Hba.
  specialize (IHlb _ Hba).
  destruct la as [| a1]; [ easy | ].
  rewrite List_last_cons_cons.
  destruct lb as [| b1]; [ | easy ].
  cbn - [ last ].
  now rewrite List_last_cons_cons.
}
apply Nat.ltb_ge in Hab, Hba.
apply Nat.le_antisymm in Hab; [ clear Hba | easy ].
remember (length la) as len eqn:Ha.
rename Hab into Hb.
symmetry in Ha, Hb.
revert la lb Ha Hb.
induction len; intros; cbn. {
  apply length_zero_iff_nil in Ha, Hb; subst la lb.
  cbn; symmetry; apply rngl_add_0_l.
}
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | ].
cbn in Ha, Hb.
apply Nat.succ_inj in Ha, Hb.
cbn - [ last ].
destruct la as [| a1]. {
  subst len.
  now apply length_zero_iff_nil in Hb; subst lb.
}
destruct lb as [| b1]; [ now rewrite <- Hb in Ha | ].
cbn - [ last ].
do 3 rewrite List_last_cons_cons.
now rewrite <- IHlen.
Qed.
*)

Theorem List_last_map : ∀ A B a b (f : A → B) la,
  f a = b → last (map f la) b = f (last la a).
Proof.
intros * Hab.
induction la as [| a1]; [ easy | ].
cbn - [ last ].
destruct la as [| a2]; [ easy | ].
cbn - [ last ].
do 2 rewrite List_last_cons_cons.
apply IHla.
Qed.

(*
Theorem last_lap_mul_const_l_add_const_r :
  rngl_has_opp_or_subt = true →
  ∀ a b la,
  last ([a] * la + [b])%lap 0%L =
    match length la with
    | 0 => b
    | 1 => (a * hd 0 la + b)%L
    | _ => last (map (λ b, (a * b)%L) (tl la)) 0%L
    end.
Proof.
intros Hos *.
induction la as [| a0]; [ easy | ].
destruct la as [| a1]. {
  cbn; unfold iter_seq, iter_list; cbn.
  now rewrite rngl_add_0_l.
}
cbn - [ lap_mul ].
rewrite last_lap_add.
cbn - [ last lap_mul ].
rewrite lap_mul_length.
rewrite app_length.
cbn - [ last lap_mul ].
rewrite if_bool_if_dec.
destruct (bool_dec _) as [H| H]; [ apply Nat.leb_le in H; flia H | clear H ].
rewrite if_bool_if_dec.
destruct (bool_dec _) as [H| H]; [ clear H | apply Nat.ltb_ge in H; flia H ].
cbn - [ last lap_mul ] in IHla.
rewrite last_lap_add in IHla.
cbn - [ last lap_mul ] in IHla.
rewrite if_bool_if_dec in IHla.
destruct (bool_dec _) as [H| H]. {
  cbn in H; apply Nat.leb_le in H; flia H.
}
clear H.
rewrite if_bool_if_dec in IHla.
destruct (bool_dec _) as [H| H]. 2: {
  cbn in H; apply Nat.leb_gt in H.
  rewrite lap_convol_mul_length in H.
  apply Nat.succ_lt_mono, Nat.lt_1_r in H.
  apply length_zero_iff_nil in H; subst la.
  cbn; unfold iter_seq, iter_list; cbn.
  now rewrite rngl_add_0_l, (rngl_mul_0_l Hos), rngl_add_0_r.
}
apply Nat.ltb_lt in H; cbn in H.
rewrite lap_convol_mul_length in H.
apply Nat.succ_lt_mono in H.
destruct la as [| a2]; [ easy | clear H ].
rewrite lap_mul_const_l; [ | easy | easy ].
rewrite (List_last_map 0%L); [ | apply (rngl_mul_0_r Hos) ].
rewrite (List_last_map 0%L); [ | apply (rngl_mul_0_r Hos) ].
now do 2 rewrite List_last_cons_cons.
Qed.
*)

(* to be completed
Theorem glop :
  rngl_has_eqb = true →
  ∀ p q,
  lap q ≠ []
  → has_polyn_prop (lap p ° lap q) = true.
Proof.
intros Heb * Hq.
destruct p as (la, pa).
destruct q as (lb, pb).
move lb before la.
cbn in Hq.
cbn - [ lap_compose ].
apply Bool.orb_true_iff in pa, pb.
apply Bool.orb_true_iff.
destruct pa as [pa| pa]. {
  now apply is_empty_list_empty in pa; subst la; left.
}
destruct pb as [pb| pb]. {
  now apply is_empty_list_empty in pb; subst lb.
}
right.
apply (rngl_neqb_neq Heb) in pa, pb.
Theorem last_lap_compose :
  rngl_has_opp_or_subt = true →
  ∀ la lb,
  last (la ° lb)%lap 0%L =
    match length lb with
    | 0 => hd 0%L la
    | 1 => eval_lap la (hd 0%L lb)
    | _ => (last la 0 * last lb 0 ^ (length la - 1))%L
    end.
Proof.
intros Hos *.
(* vérifier le cas "> 1" *)
(**)
destruct lb as [| b0]. {
  cbn; unfold lap_compose, rlap_compose; cbn.
  unfold rlap_horner, iter_list; cbn.
  erewrite List_fold_left_ext_in. 2: {
    intros b lb Hb.
    now rewrite lap_mul_0_r, lap_add_0_l.
  }
  destruct la as [| a]; [ easy | cbn ].
  now rewrite map_app, fold_left_app.
}
cbn - [ last ].
destruct lb as [| b1]. {
  cbn; unfold lap_compose, rlap_compose; cbn.
  unfold rlap_horner, iter_list; cbn.
  erewrite List_fold_left_ext_in. 2: {
    intros b lb Hb.
    rewrite lap_mul_const_r; [ | easy | easy ].
    easy.
  }
  destruct la as [| a]; [ easy | cbn ].
  rewrite map_app, fold_left_app; cbn.
  rewrite last_lap_add.
  rewrite map_length.
  remember (fold_left _ _ _) as lb eqn:Hlb.
  rewrite if_bool_if_dec.
  destruct (bool_dec _) as [H1| H1]. {
    subst lb.
    apply Nat.ltb_lt in H1; cbn in H1 |-*.
    apply Nat.lt_1_r, length_zero_iff_nil in H1.
    unfold eval_lap, eval_rlap, rlap_horner, iter_list; cbn.
    rewrite fold_left_app; cbn.
    destruct la as [| a0]; cbn. {
      now rewrite rngl_mul_0_l, rngl_add_0_l.
    }
    cbn in H1.
    rewrite map_app in H1; cbn in H1.
    rewrite fold_left_app in H1; cbn in H1.
    now apply eq_lap_add_nil in H1.
  }
  rewrite if_bool_if_dec.
  destruct (bool_dec _) as [H2| H2]. 2: {
    apply Nat.ltb_ge in H1, H2; cbn in H1, H2 |-*.
    apply Nat.le_antisymm in H1; [ clear H2 | easy ].
    destruct lb as [| b1]; [ easy | ].
    destruct lb; [ clear H1 | easy ].
    symmetry in Hlb; cbn.
    destruct la as [| a0]; [ easy | ].
    unfold eval_lap, eval_rlap, rlap_horner, iter_list; cbn.
    rewrite fold_left_app; cbn; f_equal; symmetry.
    rewrite fold_left_app; cbn.
    destruct la as [| a1]; cbn. {
      rewrite rngl_mul_0_l; [ | easy ].
      rewrite rngl_add_0_l.
      cbn in Hlb.
      now injection Hlb; clear Hlb; intros; subst a0.
    }
    cbn in Hlb.
...
}
cbn - [ last ].
...
unfold lap_compose.
remember (length lb) as blen eqn:Hbl; symmetry in Hbl.
destruct blen. {
  apply length_zero_iff_nil in Hbl; subst lb.
  unfold rlap_compose, rlap_horner, iter_list; cbn.
  erewrite List_fold_left_ext_in. 2: {
    intros b lb Hb.
    now rewrite lap_mul_0_r, lap_add_0_l.
  }
  destruct la as [| a]; [ easy | cbn ].
  now rewrite map_app, fold_left_app.
}
destruct blen. {
  unfold eval_lap, eval_rlap, rlap_horner, iter_list.
  remember (rev la) as rla; clear la Heqrla.
  destruct lb as [| b]; [ easy | ].
  destruct lb; [ cbn; clear Hbl | easy ].
  destruct rla as [| a2]; intros; [ easy | cbn ].
  rewrite (rngl_mul_0_l Hos), rngl_add_0_l.
  unfold rlap_compose, rlap_horner, iter_list; cbn.
  rewrite List_fold_left_map.
  apply last_fold_left_lap_mul_const_add_const.
}
unfold rlap_compose, rlap_horner, iter_list.
rewrite rev_involutive.
rewrite List_fold_left_map.
remember (rev la) as rla eqn:Hrla.
rewrite <- (rev_involutive la).
rewrite <- Hrla.
rewrite List_last_rev.
rewrite rev_length.
clear la Hrla.
destruct lb as [| b0]; [ easy | ].
cbn in Hbl.
apply Nat.succ_inj in Hbl.
destruct lb as [| b1]; intros; [ easy | ].
cbn in Hbl; apply Nat.succ_inj in Hbl.
destruct rla as [| a]. {
  now cbn; rewrite (rngl_mul_0_l Hos).
}
cbn - [ last ].
Theorem last_fold_left_lap_mul_cons_cons_add_const :
  ∀ (la lb lc : list T) (b0 b1 : T),
  last (fold_left (λ accu a, (accu * (b0 :: b1 :: lb) + [a])%lap) la lc)
    0%L =
  last (fold_left (λ accu a, (accu * (b1 :: lb) + [a])%lap) la lc) 0%L.
Admitted.
rewrite last_fold_left_lap_mul_cons_cons_add_const.
rewrite List_last_cons_cons.
clear b0 blen Hbl.
rewrite Nat.sub_0_r.
revert b1.
induction lb as [| b2]; intros. {
  cbn.
  rewrite last_fold_left_lap_mul_const_add_const.
  (* bin non *)
...
}
rewrite last_fold_left_lap_mul_cons_cons_add_const.
apply IHlb.
...
last_fold_left_lap_mul_add:
  ∀ (la : list T) (b c : T),
    last (fold_left (λ (accu : list T) (a : T), (accu * [b] + [a])%lap) la [c])
      0%L = fold_left (λ x y : T, (x * b + y)%L) la c
...
...
revert lb Hbl.
induction la as [| a]; intros; cbn. {
  symmetry; apply rngl_mul_1_r.
}
rewrite fold_left_app; cbn.
destruct la as [| a1]; [ now cbn; rewrite rngl_mul_1_r | cbn ].
rewrite List_cons_length in IHla.
rewrite Nat_sub_succ_1 in IHla.
destruct la as [| a2]. {
  rewrite app_nil_l, rngl_pow_0_r, rngl_mul_1_r.
  cbn - [ lap_mul ].
  rewrite lap_mul_0_l, lap_add_0_l.
  rewrite (last_lap_mul_const_l_add_const_r Hos).
  destruct lb as [| b0]; [ easy | ].
  destruct lb as [| b1]; [ easy | ].
  rewrite List_last_cons_cons.
  cbn - [ last ].
  clear Hbl.
  revert b1.
  induction lb as [| b2]; intros; [ easy | ].
  cbn - [ last ].
  do 2 rewrite List_last_cons_cons.
  apply IHlb.
}
specialize (IHla _ Hbl) as H1.
rewrite List_last_cons_cons in H1.
rewrite last_lap_add.
cbn - [ last ].
rewrite if_bool_if_dec.
destruct (bool_dec _) as [H2| H2]. {
  apply Nat.ltb_lt, Nat.lt_1_r, length_zero_iff_nil in H2.
  rewrite fold_left_app in H2.
  rewrite fold_left_app in H2.
  cbn in H2.
...
remember (a2 :: la) as l; cbn - [ last ] in H1; subst l.
...
  destruct lb as [| b1]; [ easy | ].
  rewrite List_last_cons_cons.
  cbn - [ last ].
  do 2 rewrite List_last_cons_cons.
  unfold iter_seq, iter_list.
  cbn - [ last ].
  rewrite rngl_add_0_l.
...
  rewrite lap_mul_const_l; [ | easy | easy ].
  rewrite lap_add_const_r; [ | easy ].
  rewrite List_map_tl.
...
rewrite map_tl.
Search ((_ + [_])%lap).
Search ((_ * [_])%lap).
...
Theorem List_last_map : ∀ A B (f : A → B) l d e,
  f e = d → last (map f l) d = f (last l e).
...
rewrite List_last_map.
...
  cbn.
  destruct lb as [| b0]; [ easy | ].
  cbn in Hbl; apply Nat.succ_inj in Hbl.
  destruct lb as [| b1]; [ easy | ].
  cbn in Hbl; apply Nat.succ_inj in Hbl.
  rewrite Nat.sub_0_r, rngl_mul_1_r.
  rewrite lap_convol_mul_const_l; [ | easy | easy | easy ].
  cbn - [ last ].
  do 2 rewrite List_last_cons_cons.
  clear Hbl.
  revert b1.
  induction lb as [| b2]; intros; [ easy | ].
  cbn - [ last ].
  do 2 rewrite List_last_cons_cons.
  apply IHlb.
}
rewrite fold_left_app; cbn.
rewrite List_last_cons_cons in IHla.
rewrite List_cons_length in IHla.
destruct la as [| a3]. {
  rewrite app_nil_l, rngl_pow_0_r, rngl_mul_1_r.
  cbn - [ lap_mul ].
  rewrite lap_mul_0_l, lap_add_0_l.
...
  cbn.
  destruct lb as [| b0]; [ easy | ].
  cbn in Hbl; apply Nat.succ_inj in Hbl.
  destruct lb as [| b1]; [ easy | ].
  cbn in Hbl; apply Nat.succ_inj in Hbl.
  rewrite Nat.sub_0_r, rngl_mul_1_r.
  rewrite List_last_cons_cons.
  do 2 rewrite List_cons_length.
  rewrite lap_convol_mul_const_l; [ | easy | easy | easy ].
  rewrite skipn_O.
  cbn - [ last ].
  rewrite Nat.add_succ_r.
  cbn - [ last ].
  rewrite List_last_cons_cons.
  rewrite Nat.add_succ_r.
  cbn - [ last ].
  rewrite List_last_cons_cons.
  unfold iter_seq, iter_list.
  cbn - [ last ].
  rewrite rngl_add_0_l, map_length.
  destruct lb as [| b2]. {
    cbn.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    symmetry; apply rngl_mul_assoc.
  }
  cbn - [ last ].
  do 2 rewrite List_last_cons_cons.
  unfold iter_seq, iter_list.
  cbn - [ last ].
  rewrite rngl_add_0_l, Nat.add_succ_r.
  cbn - [ last ].
  rewrite List_last_cons_cons.
  unfold iter_seq, iter_list.
  cbn - [ last ].
  rewrite rngl_add_0_l.
  destruct lb as [| b3]. {
    cbn.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    symmetry; apply rngl_mul_assoc.
  }
  cbn - [ last ].
  do 2 rewrite List_last_cons_cons.
  unfold iter_seq, iter_list.
  cbn - [ last ].
  rewrite rngl_add_0_l.
  destruct lb as [| b4]. {
    cbn.
    unfold iter_seq, iter_list; cbn.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    rewrite rngl_add_0_l.
    symmetry; apply rngl_mul_assoc.
  }
  cbn - [ last ].
  do 2 rewrite List_last_cons_cons.
  unfold iter_seq, iter_list.
  cbn - [ last ].
  rewrite rngl_add_0_l.
  destruct lb as [| b5]. {
    cbn.
    unfold iter_seq, iter_list; cbn.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
    rewrite rngl_add_0_l, rngl_add_0_r.
    rewrite rngl_add_0_l.
    symmetry; apply rngl_mul_assoc.
  }
  cbn - [ last ].
  do 2 rewrite List_last_cons_cons.
  unfold iter_seq, iter_list.
  cbn - [ last ].
  rewrite rngl_add_0_l.
  rewrite Nat.add_succ_r; cbn - [ last ]; rewrite List_last_cons_cons.
  rewrite Nat.add_succ_r; cbn - [ last ]; rewrite List_last_cons_cons.
  rewrite Nat.add_succ_r; cbn - [ last ]; rewrite List_last_cons_cons.
  unfold iter_seq, iter_list; cbn - [ last ].
...
  ============================
  last
    ((0 + (a2 * b0 + a1) * nth 4 lb 0 + a2 * b1 * nth 3 lb 0 +
      a2 * b2 * nth 2 lb 0 + a2 * b3 * nth 1 lb 0 + 
      a2 * b4 * nth 0 lb 0 + a2 * b5 * b5 +
      nth 0 (map (λ b : A, a2 * b) lb) 0 * b4 +
      nth 1 (map (λ b : A, a2 * b) lb) 0 * b3 +
      nth 2 (map (λ b : A, a2 * b) lb) 0 * b2 +
      nth 3 (map (λ b : A, a2 * b) lb) 0 * b1 +
      nth 4 (map (λ b : A, a2 * b) lb) 0 * b0)%L
     :: lap_convol_mul
          ((a2 * b0 + a1)%L
           :: (a2 * b1)%L
              :: (a2 * b2)%L
                 :: (a2 * b3)%L
                    :: (a2 * b4)%L
                       :: (a2 * b5)%L :: map (λ b : A, (a2 * b)%L) lb)
          (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: lb) 11 
          (length lb + length lb)) 0%L =
  (a2 * (last (b5 :: lb) 0 * last (b5 :: lb) 0))%L
...
*)

(*
résultant (selon le X) des polynomes Q et P(Y-X)
*)

(*
Time Compute (
  let _ := Q_ring_like_op in
  let la := [7;5;3;2] in
  let lb := [11;13] in
  last (lap_compose la lb) 0).
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
  rngl_has_eqb = true →
  ∀ c, c ≠ 0%L → @has_polyn_prop T op [c] = true.
Proof.
intros T op rp Heb * Hcz; cbn.
apply Bool.negb_true_iff.
now apply rngl_eqb_neq.
Qed.

Definition polyn_of_const {T} (ro : ring_like_op T) rp
    (Heb : rngl_has_eqb = true) (c : T) :=
  match rngl_eq_dec Heb c 0 with
  | left _ => 0%pol
  | right Hcz => mk_polyn [c] (single_has_polyn_prop rp Heb Hcz)
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
  → has_polyn_prop (map polyn_of_Q_const la) = true.
Proof.
intros * Hla.
destruct la as [| a] using rev_ind; [ easy | clear IHla ].
apply Bool.orb_true_iff in Hla.
destruct Hla as [Hla| Hla]; [ now destruct la | ].
rewrite last_last in Hla.
rewrite map_app; cbn.
apply Bool.orb_true_iff; right.
rewrite last_last; cbn.
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
   map polyn_of_Q_const [1;0;1]).
Compute
  (let roqp := Q_polyn_ring_like_op in
   let rpqp := Q_polyn_ring_like_prop in
   let roq := Q_ring_like_op in
   let rpq := Q_ring_like_prop in
   let la := [1;0;1] in
   mk_polyn (map polyn_of_Q_const la)
     (has_polyn_prop_map_polyn_of_Q_const la eq_refl)).
Compute
  (let roqp := Q_polyn_ring_like_op in
   let rpqp := Q_polyn_ring_like_prop in
   let roq := Q_ring_like_op in
   let rpq := Q_ring_like_prop in
   map polyn_of_Q_const [-2;0;1]).
Compute
  (let roqp := Q_polyn_ring_like_op in
   let roq := Q_ring_like_op in
   @mk_polyn (polyn Q) roqp [mk_polyn [1;0;1] eq_refl] eq_refl). (* x²+1 = p *)
Compute
  (let roqp := Q_polyn_ring_like_op in
   let roq := Q_ring_like_op in
   @mk_polyn (polyn Q) roqp [mk_polyn [-2;0;1] eq_refl] eq_refl). (* x²-2 = q *)
Compute
  (let roqp := Q_polyn_ring_like_op in
   let roq := Q_ring_like_op in
   @mk_polyn (polyn Q) roqp [polyn_zero; mk_polyn [1] eq_refl] eq_refl). (* z *)
Compute
  (let roqp := Q_polyn_ring_like_op in
   let roq := Q_ring_like_op in
   @mk_polyn (polyn Q) roqp [mk_polyn [0;-1] eq_refl] eq_refl). (* -x *)
Compute
  (let roqp := Q_polyn_ring_like_op in
   let roq := Q_ring_like_op in
   @mk_polyn (polyn Q) roqp [mk_polyn [0;-1] eq_refl; mk_polyn [1] eq_refl] eq_refl). (* z-x *)

Compute
  (let roqp := Q_polyn_ring_like_op in
   let roq := Q_ring_like_op in
   @mk_polyn (polyn Q) roqp [mk_polyn [-2;0;1] eq_refl] eq_refl). (* x²-2 = q *)
Compute
  (let roqp := Q_polyn_ring_like_op in
   let roq := Q_ring_like_op in
   @mk_polyn (polyn Q) roqp [mk_polyn [0;-1] eq_refl; mk_polyn [1] eq_refl] eq_refl). (* z-x *)

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
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]; cbn. {
  rewrite if_bool_if_dec.
  destruct (Bool.bool_dec _) as [Haz| Haz]; [ easy | cbn ].
  now apply Bool.negb_true_iff.
}
cbn in IHla.
rewrite last_last in IHla.
apply Bool.orb_true_iff in IHla.
apply Bool.orb_true_iff; right.
rewrite last_last.
destruct IHla as [H1| H1]; [ | easy ].
apply is_empty_list_empty in H1.
now apply app_eq_nil in H1.
Qed.
*)

Theorem Q_has_eqb : @rngl_has_eqb Q Q_ring_like_op = true.
Proof. easy. Qed.

Theorem Q_polyn_has_eqb : @rngl_has_eqb (polyn Q) Q_polyn_ring_like_op = true.
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
  let p' := map (λ i, [i]) (rev rp) in
  let q' := map (λ i, [i]) (rev rq) in
  rev (lap_resultant p' (lap_compose q' [[0; -1]; [1]])%L).

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
Search (@rngl_has_eqb Q).
Check polyn_norm_prop.

(*
Theorem toto :
  let roqp := Q_polyn_ring_like_op in
  ∀ la,
  has_polyn_prop (map (polyn_of_const Q_ring_like_prop Q_has_eqb) la) = true.
Proof.
intros.
apply Bool.orb_true_iff.
...
*)

Print polyn_of_const.
Check rngl_eq_dec.
Print rngl_eq_dec.
Definition rngl_eq_dec' T (ro : ring_like_op T) (rp : ring_like_prop T)
    (Heq : rngl_has_eqb = true) (a b : T) :=
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
    let p := map (polyn_of_const rpq Q_has_eqb) [1;0;1] in
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
(*
Theorem last_list_fold_right : ∀ A B (f : B → list A → list A) a l,
  last (fold_right f a l) = a.
...
erewrite List_fold_right_ext_in. 2: {
  intros c lc Hc.
  rewrite (lap_add_comm rp); cbn.
  easy.
}
...
  destruct la as [| a] using rev_ind; [ now left | right; cbn ].
  rewrite fold_right_app; cbn.
  rewrite last_last in pa.
  cbn.
...
}
...
Definition polyn_compose {A} {ro} (p q : polyn A) :=
  mk_polyn (lap_compose ro (lap p) (lap q)) (glop p q).

Print polyn_compose.
*)

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
  (@polyn_ring_like_op Q Q_ring_like_op Q_ring_like_prop eq_refl eq_refl (n_Sn _)).
Search rngl_characteristic.

Check mk_polyn.
Search has_polyn_prop.
*)

(*
Compute (polyn_sylvester_mat (mk_polyn (rev [1;2;3;4;5]) eq_refl) (mk_polyn (rev [6;7;8;9]) eq_refl)).
Compute (mat_nrows (polyn_sylvester_mat (mk_polyn (rev [1;2;3;4;5]) eq_refl) (mk_polyn (rev [6;7;8;9]) eq_refl))).
Time Compute (det (polyn_sylvester_mat (mk_polyn (rev [1;2;3;4]) eq_refl) (mk_polyn (rev [6;7;8;9]) eq_refl))).
...
Compute (det (polyn_sylvester_mat (mk_polyn (rev [1;2;3;4;5]) eq_refl) (mk_polyn (rev [6;7;8;9]) eq_refl))).
...
Compute (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9]).
Compute (mat_nrows (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9])).
Compute (mat_ncols (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9])).
Compute (is_square_matrix (rlap_sylvester_mat [1;2;3;4;5] [6;7;8;9])).
Compute (let m := rlap_sylvester_mat [1;2;3;4] [6;7;8] in (mat_nrows m, mat_ncols m, m, is_square_matrix m)).
Compute (let m := rlap_sylvester_mat [1;2;3] [6;7] in (mat_nrows m, mat_ncols m, m, is_square_matrix m)).
Compute (let m := rlap_sylvester_mat [2] [6;7] in (mat_nrows m, mat_ncols m, m, is_square_matrix m)).
Compute (let m := rlap_sylvester_mat [2;3] [6] in (mat_nrows m, mat_ncols m, m, is_square_matrix m)).
*)
*)
