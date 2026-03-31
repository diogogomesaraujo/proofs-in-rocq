Module BinaryNum.
    Inductive digit : Type :=
        | zero
        | one.
    
    Inductive num : Type := 
        | a (n : num) (dig : digit)
        | no.

    Notation "0" := zero.
    Notation "1" := one.

    Notation " d || n " := (a (n: num) (d: digit) ).

    Example example_zero:
        a no zero =  0 || no.
    Proof. reflexivity. Qed.

    Example example_three:
        a (a no one) one = 1 || (1 || no).
    Proof. reflexivity. Qed.

    Example example_five:
        a (a (a no one) zero ) one = 1 || (0 || (1 || no)).
    Proof. reflexivity. Qed.

    Definition sum_digit (a b r: digit) : digit * digit :=
        match (a, b, r) with
        | (1, 1, 1) => (1, 1)
        | (1, 0, 1) | (1, 1, 0) | (0, 1, 1) => (0, 1)
        | _ => (1, 0)
        end.

    Fixpoint sum_single (y : num) (r : digit) {struct y} : num :=
        match y, r with
        | a y' 1, 0 | a y' 0, 1 =>
            a (sum_single y' 0) 1
        | a y' 1, 1 =>
            a (sum_single y' 1) 1
        | a y' 0, 0 =>
            a (sum_single y' 0) 0
        | no, 0 => no
        | no, 1 => a no 1
        end.

    Fixpoint sum_rec (x y : num) (r : digit) {struct x} : num := 
        match x, y with
        | a x' dx, no => 
            let (s, r') := sum_digit 0 dx r in
            a (sum_rec x' no r') s
        | a x' dx, a y' dy =>
            let (s, r') := sum_digit dx dy r in
            a (sum_rec x' y' r') s (*structurally smaller argument on the left*)
        | no, _ =>
            sum_single y r
        end.

    Definition sum (x y: num) : num :=
        sum_rec x y 0.
    
    Compute sum (0 || (0 || (1 || no))) (1 || (1 || (0 || no))).

    Example sum_1_4: sum (1|| (1 || no)) (1 || (0 || (0 || no))) =
            (1 || (1|| (1 || no))).
    Proof. simpl. compute. reflexivity. Qed.

    Compute sum (1 || (0 || (1 || no))) (1 || (0 || (0 || no))).
End BinaryNum.
