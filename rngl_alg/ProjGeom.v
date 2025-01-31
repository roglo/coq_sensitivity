(* attempt to implement projective geometry *)

Require Import Utf8.

Require Import Main.RingLike.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
(*
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
*)

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
