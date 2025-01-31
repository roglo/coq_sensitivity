(* attempt to implement projective geometry *)

Require Import Utf8.

Require Import Main.RingLike.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Definition proj_point_prop x y := (x² + y² =? 1)%L = true.

(* proj_point is a triplet (ppx, ppy, pp_prop)
   - either a point (pp_x, pp_y) when pp_prop is None
   - or a point at the infinite whose direction is from the
     segment (0, 0) to (pp_x, pp_y) and, in that case, the 3rd
     component is Some (the proof that (pp_x, pp_y) is in the unit
     circle) *)

Record proj_point := mk_pp
  { pp_x : T;
    pp_y : T;
    pp_prop : option (proj_point_prop pp_x pp_y) }.

(* hyperbolic angle using projective geometry *)
(* I don't know if it works *)

Definition pp_cosh2_sinh2_prop pp :=
  let x := pp_x pp in
  let y := pp_y pp in
  match (pp_prop pp : option (proj_point_prop x y)) with
  | None => (x² - y² =? 1)%L = true
  | Some P => (rngl_abs x =? rngl_abs y)%L = true
  end.

Record pph_angle := mk_pp_hangle
  { pph_coord : proj_point;
    pph_angle_prop : pp_cosh2_sinh2_prop pph_coord }.

Class pph_angle_ctx :=
  { pphc_ic : rngl_mul_is_comm T = true;
    pphc_on : rngl_has_1 T = true;
    pphc_op : rngl_has_opp T = true;
    pphc_ed : rngl_has_eq_dec T = true;
(*
    hc_iv : rngl_has_inv T = true;
    hc_c2 : rngl_characteristic T ≠ 2;
    pphc_or : rngl_is_ordered T = true
*)
  }.

End a.

Arguments pph_angle_ctx T {ro rp}.

Ltac destruct_pphc :=
  set (Hic := pphc_ic);
  set (Hop := pphc_op);
  set (Hed := pphc_ed);
(*
  set (Hor := hc_or);
*)
  specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos;
  specialize pphc_on as Hon.
(*
  specialize hc_iv as Hiv;
  specialize hc_c2 as Hc2
*)

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {pphc : pph_angle_ctx T}.
(*
Context {rl : real_like_prop T}.
*)

(* equality equivalent of equality between components *)

Theorem eq_pp_eq : ∀ p1 p2,
  (pp_x p1, pp_y p1) = (pp_x p2, pp_y p2) ∧
  match (pp_prop p1, pp_prop p2) with
  | (None, None) | (Some _, Some _) => True
  | _ => False
  end ↔ p1 = p2.
Proof.
intros.
split; intros H12. {
  destruct H12 as (H12, Hp12).
  injection H12; clear H12; intros Hy Hx.
  destruct p1 as (p1x, p1y, H1p).
  destruct p2 as (p2x, p2y, H2p).
  cbn in Hp12, Hy, Hx.
  subst p2x p2y.
  progress f_equal.
  destruct H1p as [pp1| ]; [ | now destruct H2p ].
  destruct H2p as [pp2| ]; [ | easy ].
  progress f_equal.
  apply (Eqdep_dec.UIP_dec Bool.bool_dec).
} {
  subst p2.
  split; [ easy | ].
  destruct p1 as (p1x, p1y, H1p).
  now destruct H1p.
}
Qed.

Theorem eq_pph_eq : ∀ θ1 θ2,
  pph_coord θ1 = pph_coord θ2 ↔ θ1 = θ2.
Proof.
intros.
split; intros H12; [ | now subst θ2 ].
apply eq_pp_eq in H12.
destruct H12 as (H12, Hp12).
injection H12; clear H12; intros Hy Hx.
destruct θ1 as ((x1, y1, p1) & pp1).
destruct θ2 as ((x2, y2, p2) & pp2).
cbn in Hp12, Hx, Hy.
subst x2 y2.
destruct p1 as [p1| ]. {
  destruct p2 as [p2| ]; [ | easy ].
  assert (p1 = p2) by apply (Eqdep_dec.UIP_dec Bool.bool_dec).
  assert (pp1 = pp2) by apply (Eqdep_dec.UIP_dec Bool.bool_dec).
  now subst p2 pp2.
} {
  destruct p2 as [p2| ]; [ easy | ].
  progress f_equal.
  apply (Eqdep_dec.UIP_dec Bool.bool_dec).
}
Qed.

(* *)

Definition pp_cosh θ := pp_x (pph_coord θ).
Definition pp_sinh θ := pp_y (pph_coord θ).

(* hyperbolic angle zero *)

Theorem pph_zero_angle_prop :
  pp_cosh2_sinh2_prop {| pp_x := 1; pp_y := 0; pp_prop := None |}%L.
Proof.
destruct_pphc.
cbn.
rewrite (rngl_squ_0 Hos).
rewrite (rngl_sub_0_r Hos).
rewrite (rngl_squ_1 Hon).
apply (rngl_eqb_refl Hed).
Qed.

Definition pph_zero :=
  {| pph_coord := {| pp_x := 1; pp_y := 0; pp_prop := None |}%L;
     pph_angle_prop := pph_zero_angle_prop |}.

(* sum of hyperbolic angles *)

Theorem pph_angle_add_prop :
  ∀ p1 p2
    (H1 : bool_of_option (pp_prop p1) = false)
    (H2 : bool_of_option (pp_prop p2) = false),
  pp_cosh2_sinh2_prop
    {|
      pp_x := (pp_x p1 * pp_x p2 + pp_y p1 * pp_y p2)%L;
      pp_y := (pp_y p1 * pp_x p2 + pp_x p1 * pp_y p2)%L;
      pp_prop := None
    |}.
Proof.
destruct_pphc.
intros.
destruct p1 as (x1, y1, p1).
destruct p2 as (x2, y2, p2).
move x2 before x1; move y2 before y1.
move p2 before p1.
cbn.
progress unfold proj_point_prop in p1.
progress unfold proj_point_prop in p2.
destruct p1 as [p1| ]; [ easy | ].
destruct p2 as [p2| ]; [ easy | ].
clear H1 H2.
(*
...
  apply (rngl_eqb_eq Hed) in p1.
  destruct p2 as [p2| ]. {
    apply (rngl_eqb_eq Hed) in p2.
    apply (rngl_eqb_eq Hed).
(*
  Hxy : (x² - y² =? 1)%L = true
  Hxy' : (x'² - y'² =? 1)%L = true
  Hzx : (0 ≤? x)%L = true
  Hzx' : (0 ≤? x')%L = true
  ============================
  ((x * x' + y * y')² - (x * y' + y * x')² =? 1)%L = true
*)
rewrite (rngl_add_comm (y1 * x2)).
(*
  ((x1 * x2 + y1 * y2)² - (x1 * y2 + y1 * x2)²)%L = 1%L
*)
    do 2 rewrite (rngl_squ_add Hic Hon).
    rewrite rngl_add_add_swap.
    do 2 rewrite (rngl_sub_add_distr Hos).
    rewrite (rngl_sub_sub_swap Hop (_ + _ + _))%L.
    do 4 rewrite rngl_mul_assoc.
    rewrite (rngl_mul_mul_swap Hic (2 * x1 * y2)%L).
    rewrite (rngl_mul_mul_swap Hic (2 * x1) y2)%L.
    rewrite (rngl_mul_mul_swap Hic (2 * x1 * x2) y2 y1)%L.
    rewrite (rngl_add_sub Hos).
    do 4 rewrite (rngl_squ_mul Hic).
    do 2 rewrite (rngl_add_sub_swap Hop).
    rewrite <- (rngl_sub_sub_distr Hop).
    do 2 rewrite <- (rngl_mul_sub_distr_l Hop).
(* ah oui, mais ça déconne, là : mes hypothèses p1 et p2
   contiennent des + alors que ça devait être des - *)
...
    apply (rngl_eqb_eq Hed) in Hxy'.
  rewrite Hxy'.
  now do 2 rewrite (rngl_mul_1_r Hon).
...
    (* du coup, on en déduit par p1 et pp1 que 2x₁² = 1 *)
    apply (rngl_eqb_eq Hed) in p1, p2, pp1, pp2.
    apply (rngl_eqb_eq Hed).
(* faut voir sur papier *)
...
*)
...

Definition pph_angle_add θ1 θ2 :=
  let b1 := bool_of_option (pp_prop (pph_coord θ1)) in
  let b2 := bool_of_option (pp_prop (pph_coord θ2)) in
  match (Bool.bool_dec b1 false, Bool.bool_dec b2 false) with
  | (left H1, left H2) =>
      {| pph_coord :=
           {| pp_x := (pp_cosh θ1 * pp_cosh θ2 + pp_sinh θ1 * pp_sinh θ2)%L;
              pp_y := (pp_sinh θ1 * pp_cosh θ2 + pp_cosh θ1 * pp_sinh θ2)%L;
              pp_prop := None |};
         pph_angle_prop :=
           pph_angle_add_prop (pph_coord θ1) (pph_coord θ2) H1 H2 |}
  | _ =>
      pph_zero
  end.

...

Definition pph_angle_add θ1 θ2 :=
  match (pp_prop (pph_coord θ1), pp_prop (pph_coord θ2)) with
  | (None, None) =>
      {| pph_coord :=
           {| pp_x := (pp_cosh θ1 * pp_cosh θ2 + pp_sinh θ1 * pp_sinh θ2)%L;
              pp_y := (pp_sinh θ1 * pp_cosh θ2 + pp_cosh θ1 * pp_sinh θ2)%L;
              pp_prop := None |};
         pph_angle_prop := pph_angle_add_prop (pph_coord θ1) (pph_coord θ2) |}
  | _ =>
      pph_zero
  end.
