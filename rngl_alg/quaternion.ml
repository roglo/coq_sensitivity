let rec seq start len =
  match len with
  | 0 -> []
  | _ -> let len0 = len - 1 in start :: seq (start + 1) len0
;;

type 'a vector = { vect_list : 'a list };;
let mk_vect l = { vect_list = l };;
let vect_list v = v.vect_list;;
let vect_size v = List.length v.vect_list;;

let vect_el (v : int vector) i =
  List.nth (vect_list v) (i - 1);;

let vect_dot_mul (u : 'a vector) (v : 'a vector) =
  List.fold_left (fun a b -> a + b) 0
    (List.map2 (fun a b -> a * b) (vect_list u) (vect_list v));;

let vect_add (u : 'a vector) (v : 'a vector) =
  mk_vect (List.map2 (fun a b -> a + b) (vect_list u) (vect_list v));;

let vect_mul_scal_l s (v : 'a vector) =
  mk_vect (List.map (fun x -> s * x) (vect_list v));;

let vect_comm (u : int vector) (v : int vector) i j =
  let i = (i - 1) mod vect_size u + 1 in
  let j = (j - 1) mod vect_size u + 1 in
  vect_el u i * vect_el v j - vect_el u j * vect_el v i;;

let vect_cross_mul (u : 'a vector) (v : 'a vector) =
  let n = vect_size u in
  let f i =
    List.fold_left (fun a j -> a + vect_comm u v (i + j) (i + n - j)) 0
      (seq 1 (n / 2))
  in
  mk_vect (List.map f (seq 1 n));;

type 'a nion = { qre : 'a; qim : 'a vector };;
let mk_nion r i = { qre = r; qim = i };;

let nion_add {qre = a1; qim = v1} {qre = a2; qim = v2} =
  mk_nion (a1 + a2) (vect_add v1 v2);;

let nion_mul {qre = a1; qim = v1} {qre = a2; qim = v2} =
  mk_nion (a1 * a2 - vect_dot_mul v1 v2)
    (vect_add
      (vect_add (vect_mul_scal_l a1 v2) (vect_mul_scal_l a2 v1))
      (vect_cross_mul v1 v2));;

let _e1 = mk_nion 0 (mk_vect [1;0;0;0;0;0;0]) in
let _e2 = mk_nion 0 (mk_vect [0;1;0;0;0;0;0]) in
let _e3 = mk_nion 0 (mk_vect [0;0;1;0;0;0;0]) in
let _e4 = mk_nion 0 (mk_vect [0;0;0;1;0;0;0]) in
let _e5 = mk_nion 0 (mk_vect [0;0;0;0;1;0;0]) in
let _e6 = mk_nion 0 (mk_vect [0;0;0;0;0;1;0]) in
let _e7 = mk_nion 0 (mk_vect [0;0;0;0;0;0;1]) in
(List.map (fun e -> nion_mul _e1 e) [_e1;_e2;_e3;_e4;_e5;_e6;_e7],
 List.map (fun e -> nion_mul _e3 e) [_e1;_e2;_e3;_e4;_e5;_e6;_e7]);;

