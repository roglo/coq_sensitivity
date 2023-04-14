(* ocaml -I +camlp5 camlp5r.cma *)

value rec seq start len =
  if len < 0 then failwith "seq"
  else if len = 0 then []
  else
    let len0 = len - 1 in
    [start :: seq (start + 1) len0]
;

value repeat (x : α) (n : int) = List.map (fun _ → x) (seq 0 n);

value vect_el (v : list _) i =
  if i < 1 || i > List.length v then failwith "vect_el"
  else List.nth v (i - 1)
;

value vect_dot_mul (u : list α) (v : list α) =
  List.fold_left (fun a b → a + b) 0
    (List.map2 (fun a b → a * b) u v)
;

value vect_add (u : list α) (v : list α) =
  List.map2 (fun a b → a + b) u v
;

value vect_mul_scal_l s (v : list α) =
  List.map (fun x → s * x) v
;

value vect_comm (u : list int) (v : list int) i j =
  let i = (i - 1) mod List.length u + 1 in
  let j = (j - 1) mod List.length u + 1 in
  vect_el u i * vect_el v j - vect_el u j * vect_el v i
;

value vect_cross_mul (u : list α) (v : list α) =
  let n = List.length u in
  let f i =
    List.fold_left (fun a j → a + vect_comm u v (i + j) (i + n - j)) 0
      (seq 1 (n / 2))
  in
  List.map f (seq 1 n)
;

type nion α = { qre : α; qim : list α };
value mk_nion r i = {qre = r; qim = i};
value qim n = n.qim;

value nion_add {qre = a1; qim = v1} {qre = a2; qim = v2} =
  mk_nion (a1 + a2) (vect_add v1 v2)
;

value nion_mul {qre = a1; qim = v1} {qre = a2; qim = v2} =
  mk_nion (a1 * a2 - vect_dot_mul v1 v2)
    (vect_add (vect_add (vect_mul_scal_l a1 v2) (vect_mul_scal_l a2 v1))
       (vect_cross_mul v1 v2))
;

let _e1 = mk_nion 0 [1; 0; 0; 0; 0; 0; 0] in
let _e2 = mk_nion 0 [0; 1; 0; 0; 0; 0; 0] in
let _e3 = mk_nion 0 [0; 0; 1; 0; 0; 0; 0] in
let _e4 = mk_nion 0 [0; 0; 0; 1; 0; 0; 0] in
let _e5 = mk_nion 0 [0; 0; 0; 0; 1; 0; 0] in
let _e6 = mk_nion 0 [0; 0; 0; 0; 0; 1; 0] in
let _e7 = mk_nion 0 [0; 0; 0; 0; 0; 0; 1] in
(List.map (fun e → nion_mul _e1 e) [_e1; _e2; _e3; _e4; _e5; _e6; _e7],
 List.map (fun e → nion_mul _e3 e) [_e1; _e2; _e3; _e4; _e5; _e6; _e7]);

value r _ = Random.int 10 - 5;
value mk_nth n = mk_nion (r ()) (List.map r (seq 1 n));
value mk_octo () = mk_nion (r ()) (List.map r (seq 1 7));

let (a, b, c) = (mk_octo (), mk_octo (), mk_octo ()) in
(a, b, c, nion_mul (nion_mul a b) c, nion_mul a (nion_mul b c));

let (a, b) = (mk_octo (), mk_octo ()) in
(a, b, nion_mul (nion_mul a b) b, nion_mul a (nion_mul b b));

(* pas alternatifs ! mon truc marche pas ! *)

(* essai comme celui de wikipedia *)

"***** celui de wikipedia...";

value vect_cross_mul_2 (u : list α) (v : list α) =
  if List.length u <> 7 || List.length v <> 7 then failwith "vect_cross_mul_2"
  else
    let c i j = vect_comm u v i j in
    [c 2 4 + c 3 7 + c 5 6;
     c 3 5 + c 4 1 + c 6 7;
     c 4 6 + c 5 2 + c 7 1;
     c 5 7 + c 6 3 + c 1 2;
     c 6 1 + c 7 4 + c 2 3;
     c 7 2 + c 1 5 + c 3 4;
     c 1 3 + c 2 6 + c 4 5]
;

vect_cross_mul_2 (qim (mk_octo ())) (qim (mk_octo ()));

value nion_mul_2 {qre = a1; qim = v1} {qre = a2; qim = v2} =
  mk_nion (a1 * a2 - vect_dot_mul v1 v2)
    (vect_add (vect_add (vect_mul_scal_l a1 v2) (vect_mul_scal_l a2 v1))
       (vect_cross_mul_2 v1 v2))
;

let (a, b, c) = (mk_octo (), mk_octo (), mk_octo ()) in
(a, b, c, nion_mul_2 (nion_mul_2 a b) c, nion_mul_2 a (nion_mul_2 b c));

let (a, b) = (mk_octo (), mk_octo ()) in
(a, b, nion_mul_2 (nion_mul_2 a b) b, nion_mul_2 a (nion_mul_2 b b));

value e n i =
  mk_nion 0 (repeat 0 (i - 1) @ [1 :: repeat 0 (n - i)]);

let a = e 7 1 in nion_mul_2 a a;

(* essai du mien à la main *)

"***** let's test that...";

value n = 7;

value my_vect_cross_mul (u : list α) (v : list α) =
  if List.length u <> n || List.length v <> n then failwith "my_vect_cross_mul"
  else
    let c i j = vect_comm u v i j in
(* essai avec n = 8
    [c 2 4 + c 3 7 + c 5 6;
     c 3 5 + c 4 8 + c 6 7;
     c 4 6 + c 5 1 + c 7 8;
     c 5 7 + c 6 2 + c 8 1;
     c 6 8 + c 7 3 + c 1 2;
     c 7 1 + c 8 4 + c 2 3;
     c 8 2 + c 1 5 + c 3 4;
     c 1 3 + c 2 6 + c 4 5]
*)
    [c 2 6 + c 3 4 + c 5 7;
     c 3 7 + c 4 5 + c 6 1;
     c 4 1 + c 5 6 + c 7 2;
     c 5 2 + c 6 7 + c 1 3;
     c 6 3 + c 7 1 + c 2 4;
     c 7 4 + c 1 2 + c 3 5;
     c 1 5 + c 2 3 + c 4 6]
(**)
;

my_vect_cross_mul (qim (mk_nth n)) (qim (mk_nth n));

value nion_mul_3 {qre = a1; qim = v1} {qre = a2; qim = v2} =
  mk_nion (a1 * a2 - vect_dot_mul v1 v2)
    (vect_add (vect_add (vect_mul_scal_l a1 v2) (vect_mul_scal_l a2 v1))
       (my_vect_cross_mul v1 v2))
;

"*** my alternativity ?";

let (a, b) = (mk_nth n, mk_nth n) in
(a, b, nion_mul_3 (nion_mul_3 a b) b, nion_mul_3 a (nion_mul_3 b b));

"*** end my alternativity";

let a = e n 1 in nion_mul_3 a a;

(* *)

nion_mul_2 (e 7 1) (e 7 2);
(* ah, tiens, ça colle pas avec celui de wikipedia *)
(* ah si, faut regarder la section "Expression à l'aide des coordonnées" *)

(* *)

(* chez moi, e2 e7 = e1 *)
"*** e2 e7 = e1";
nion_mul_3 (e n 2) (e n 7);
nion_mul (e 7 2) (e 7 7);

(* mais j'ai aussi e1 e7 = - e4 *)
"*** e1 e7 = - e4";
nion_mul (e 7 1) (e 7 7);

(* du coup, (e2 e7) e7 = e1 e7 = - e4 *)
"*** (e2 e7) e7 = - e4";
nion_mul_3 (nion_mul_3 (e 7 2) (e 7 7)) (e 7 7);

(* cependant, e2 (e7 e7) = - e2 *)
"*** e2 (e7 e7) = - e2";
nion_mul_3 (e 7 2) (nion_mul_3 (e 7 7) (e 7 7));
