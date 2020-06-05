type nat = int;
value nth i l d =
  try List.nth l i with [ Failure _ → d ].
value rec seq start len =
  if len ≤ 0 then [] else [start :: seq (start + 1) (len - 1)].
value rec pow a b =
  if b ≤ 0 then 1 else a * pow a (b - 1).

type matrix 'a = { matel : nat → nat → 'a };
type vector 'a = { vecel : nat → 'a }.

value matel m = m.matel.
value vecel v = v.vecel.

value mat_of_list d ll =
  { matel i j = nth i (nth j ll []) d }.

value mat_opp m = { matel i j = - (matel m i j) }.

value mI = { matel i j = if i = j then 1 else 0 }.

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
  | _ →
       let n' = n - 1 in
       MM_M {vecel _ = 2} {vecel _ = 2}
         (mmat_of_list 0
            [[mA n'; MM_1 mI];
             [MM_1 mI; mmat_opp (mA n')]])
  end.

value rec mmat_nb_of_rows vlen (mm : mmatrix 'a) =
  match mm with
  | MM_1 _ -> vlen
  | MM_M vr _ mmm ->
      List.fold_left
        (fun accu i ->
           accu + mmat_nb_of_rows (vecel vr i) (matel mmm i 0))
        0 (seq 0 vlen)
  end.

(*
value rec mmat_number_of_rows (mm : mmatrix 'a) =
  match mm with
  | MM_1 r _ _ -> r
  | MM_M r _ mm ->
      List.fold_left
        (fun acc i -> acc + mmat_number_of_rows (matel mm i 0)) 0 (seq 0 r)
  end.

mmat_number_of_rows (mA 3).
(* 8 *)

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
