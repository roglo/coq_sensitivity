type nat = int;

type vector 'a = { vecel : nat → 'a }.
type matrix 'a = { matel : nat → nat → 'a };

value vecel m = m.vecel.
value matel m = m.matel.

value nth i l d =
  try List.nth l i with [ Failure _ → d ].

value rec seq start len =
  if len ≤ 0 then [] else [start :: seq (start + 1) (len - 1)].

type mmatrix 'a =
  [ MM_1 of matrix 'a
  | MM_M of vector nat and vector nat and matrix (mmatrix 'a) ].

value mat_of_list d ll =
  { matel i j = nth i (nth j ll []) d }.

value mmat_of_list d (ll : list (list (mmatrix 'a))) :
    matrix (mmatrix 'a) =
  { matel i j = nth i (nth j ll []) (MM_1 { matel i j = d }) }.

value mI = { matel i j = if i = j then 1 else 0 }.

value mat_opp m = { matel i j = - (matel m i j) }.

value rec mmat_opp mm =
  match mm with
  | MM_1 m → MM_1 (mat_opp m)
  | MM_M r c mm -> MM_M r c { matel i j = mmat_opp (matel mm i j) }
  end.

value rec aM' n =
  match n with
  | 0 → MM_1 (mat_of_list 0 [])
  | 1 → MM_1 (mat_of_list 0 [[0; 1]; [1; 0]])
  | _ →
       let n' = n - 1 in
       MM_M {vecel _ = 2 } {vecel _ = 2}
         (mmat_of_list 0
            [[aM' n'; MM_1 mI];
             [MM_1 mI; mmat_opp (aM' n')]])
  end.

value rec mmat_number_of_rows nrow (mm : mmatrix 'a) =
let _ = Printf.printf "mmat_number_of_rows %d\n%!" nrow in
  match mm with
  | MM_1 _ -> nrow
  | MM_M vnrow vncol mm ->
      List.fold_left
        (fun acc i ->
let _ = Printf.printf "acc %d\n%!" acc in
           acc + mmat_number_of_rows (vecel vnrow i) (matel mm i 0))
        0 (seq 0 nrow)
  end.

let nrow = 2 in mmat_number_of_rows nrow (aM' 3).
(* should be 8 *)