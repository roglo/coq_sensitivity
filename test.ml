type nat = int;

type vector 'a = { vecel : nat → 'a }.
type matrix 'a = { matel : nat → nat → 'a };

type mmatrix 'a =
  [ MM_1 of matrix 'a
  | MM_M of vector nat and vector nat and (mmatrix 'a) ].

value rec aM' n =
  match n with
  | 0 → MM_1 (mat_of_list 0 [])
  | 1 → MM_1 (mat_of_list 0 [[0; 1]; [1; 0]])
  | _ →
       let n' = n - 1 in
       MM_M {vecel _ = 2 } {vecel _ = 2}
         (mmat_of_list 0
            [[aM' n'; MM_1 I];
             [MM_1 I; mmat_opp (aM' n')]])
  end.
