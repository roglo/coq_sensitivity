(* attempt to implement projective geometry *)

Require Import Utf8.

Require Import Main.RingLike.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.

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
  {
(*
    hc_ic : rngl_mul_is_comm T = true;
    hc_on : rngl_has_1 T = true;
    hc_op : rngl_has_opp T = true;
*)
    pphc_ed : rngl_has_eq_dec T = true;
(*
    hc_iv : rngl_has_inv T = true;
    hc_c2 : rngl_characteristic T ≠ 2;
    pphc_or : rngl_is_ordered T = true
*)
  }.

End a.

Arguments pph_angle_ctx T {ro}.

Ltac destruct_pphc :=
(*
  set (Hic := hc_ic);
  set (Hop := hc_op);
*)
  set (Hed := pphc_ed).
(*
  set (Hor := hc_or);
  specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos;
  specialize hc_on as Hon;
  specialize hc_iv as Hiv;
  specialize hc_c2 as Hc2
*)

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {pphc : pph_angle_ctx T}.
(*
Context {rp : ring_like_prop T}.
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

Theorem pph_angle_add_pp_prop :
  ∀ θ1 θ2,
  option
    (proj_point_prop
       (pp_cosh θ1 * pp_cosh θ2 + pp_sinh θ1 * pp_sinh θ2)%L
       (pp_sinh θ1 * pp_cosh θ2 + pp_cosh θ1 * pp_sinh θ2)%L).
Proof.
destruct_pphc.
intros.
destruct θ1 as ((x1, y1, p1) & pp1).
destruct θ2 as ((x2, y2, p2) & pp2).
cbn.
move x2 before x1; move y2 before y1.
move p2 before p1.
progress unfold proj_point_prop.
progress unfold pp_cosh2_sinh2_prop in pp1.
progress unfold pp_cosh2_sinh2_prop in pp2.
progress unfold proj_point_prop in p1.
progress unfold proj_point_prop in p2.
cbn in pp1, pp2.
destruct p1 as [p1| ]. {
  destruct p2 as [p2| ]. {
    apply (rngl_eqb_eq Hed) in p1, p2, pp1, pp2.
    apply Some.
    apply (rngl_eqb_eq Hed).
(* j'ai des doutes... faut voir sur papier *)
...
    progress unfold rngl_abs in pp1.
    progress unfold rngl_abs in pp2.
    remember (x1 ≤?
...

Theorem pph_angle_add_prop :
  ∀ θ1 θ2,
  pp_cosh2_sinh2_prop
    {|
      pp_x := (pp_cosh θ1 * pp_cosh θ2 + pp_sinh θ1 * pp_sinh θ2)%L;
      pp_y := (pp_sinh θ1 * pp_cosh θ2 + pp_cosh θ1 * pp_sinh θ2)%L;
      pp_prop := pph_angle_add_pp_prop θ1 θ2
    |}.
...

Definition pph_angle_add θ1 θ2 :=
  {| pph_coord :=
       {| pp_x := (pp_cosh θ1 * pp_cosh θ2 + pp_sinh θ1 * pp_sinh θ2)%L;
          pp_y := (pp_sinh θ1 * pp_cosh θ2 + pp_cosh θ1 * pp_sinh θ2)%L;
          pp_prop := pph_angle_add_pp_prop θ1 θ2 |};
     pph_angle_prop := pph_angle_add_prop θ1 θ2 |}.
