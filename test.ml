type nat = int;

type vector 'a = { vecel : nat → 'a }.
type matrix 'a = { matel : nat → nat → 'a };

value matel m = m.matel.

type mmatrix 'a =
  [ MM_1 of matrix 'a
  | MM_M of vector nat and vector nat and (mmatrix 'a) ].

value nth i l d =
  try List.nth l i with [ Failure _ → d ].

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
  | MM_M r c mm → MM_M r c { matel i j = mmat_opp (matel mm i j) }
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
