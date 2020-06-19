type nat = int;
value rec firstn n l =
  match n with
  | 0 -> []
  | _ ->
      let n0 = n - 1 in
      match l with
      | [] -> []
      | [a :: l0] -> [a :: firstn n0 l0]
      end
  end.
value length = List.length;
value hd d l = try List.hd l with [ Failure _ → d ];
value rec repeat x n =
  match n with
  | 0 -> []
  | _ -> [x :: repeat x (n - 1)]
  end.

type matrix 'a =
  { mat_list : list (list 'a);
    mat_nrows : nat;
    mat_ncols : nat }.

value list_list_nrows (ll  : list (list 'a)) =
  length ll.

value list_list_ncols (ll  : list (list 'a)) =
  length (hd [] ll).

value mat_of_list (ll : list (list 'a)) : matrix 'a =
  { mat_list = ll;
    mat_nrows = list_list_nrows ll;
    mat_ncols = list_list_ncols ll }.

(*
type mmatrix 'a =
  [ MM_1 of matrix 'a
  | MM_M of vector nat and vector nat and matrix (mmatrix 'a) ].

value rec mmat_opp mm =
  match mm with
  | MM_1 m → MM_1 (mat_opp m)
  | MM_M vr vc mm -> MM_M vr vc { matel i j = mmat_opp (matel mm i j) }
  end.

value mmat_of_list d (ll : list (list (mmatrix 'a))) :
    matrix (mmatrix 'a) =
  { matel i j = nth i (nth j ll []) (MM_1 { matel i j = d }) }.

value rec mA n =
  match n with
  | 0 → MM_1 (mat_of_list 0 [])
  | 1 → MM_1 (mat_of_list 0 [[0; 1]; [1; 0]])
  | _ →
       let n' = n - 1 in
       MM_M {vecel _ = 2} {vecel _ = 2}
         (mmat_of_list 0
            [[mA n'; MM_1 mI];
             [MM_1 mI; mmat_opp (mA n')]])
  end.

value rec mmat_nb_of_rows_ub vlen (mm : mmatrix 'a) =
  match mm with
  | MM_1 _ -> vlen
  | MM_M vr _ mmm ->
      List.fold_left
        (fun accu i ->
           accu + vecel vr i +
	     mmat_nb_of_rows_ub (vecel vr i) (matel mmm i 0))
	0 (seq 0 vlen)
  end.

let n = 0 in mmat_nb_of_rows_ub 2 (mA n).
let n = 1 in mmat_nb_of_rows_ub 2 (mA n).
let n = 2 in mmat_nb_of_rows_ub 2 (mA n).
let n = 3 in mmat_nb_of_rows_ub 2 (mA n).
let n = 4 in mmat_nb_of_rows_ub 2 (mA n).

(**)
value rec mmat_nb_of_rows vlen (mm : mmatrix 'a) =
  match mm with
  | MM_1 _ -> vlen
  | MM_M vr _ mmm ->
      List.fold_left
        (fun accu i ->
           accu + mmat_nb_of_rows (vecel vr i) (matel mmm i 0))
        0 (seq 0 vlen)
  end.

mmat_nb_of_rows 2 (mA 1).
(* 2 *)

value rec mmat_number_of_rows (mm : mmatrix 'a) =
  match mm with
  | MM_1 r _ _ -> r
  | MM_M r _ mm ->
      List.fold_left
        (fun acc i -> acc + mmat_number_of_rows (matel mm i 0)) 0 (seq 0 r)
  end.

value mat_horiz_concat (r1, c1, m1) (r2, c2, m2) =
  (max r1 r2, c1 + c2,
   { matel i j =
       if j < c1 then matel m1 i j else matel m2 i (j - c1) }).

value mat_vertic_concat (r1, c1, m1) (r2, c2, m2) =
  (r1 + r2, max c1 c2,
   { matel i j =
       if i < r1 then matel m1 i j else matel m2 (i - r1) j }).

value rec mat_of_mmat mm =
  match mm with
  | MM_1 r c m -> (r, c, m)
  | MM_M nr nc mm ->
      List.fold_left
        (fun acc r ->
	   mat_vertic_concat acc
             (List.fold_left
                 (fun acc c ->
                    mat_horiz_concat acc (mat_of_mmat (matel mm r c)))
                 (0, 0, {matel _ _ = 0}) (seq 0 nc)))
        (0, 0, {matel _ _ = 0}) (seq 0 nr)
  end.

value list_of_mat nrow ncol m =
  List.map
    (fun row ->
       List.map (fun col -> matel m row col) (seq 0 ncol)) (seq 0 nrow).

value list_of_mat2 (n, c, m) = list_of_mat n c m;

mat_of_mmat (mA 2);
list_of_mat2 (mat_of_mmat (mA 2));
*)
