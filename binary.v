Module BinaryNum.
    Inductive digit : Type :=
        | zero
        | one.
    
    Inductive num : Type := 
        | a (dig : digit) (n : num)
        | no.

    Notation "0" := zero.
    Notation "1" := one.

    Notation " d || n " := (a (d: digit) (n: num)).


    Example example_zero:
        a zero no =  0 || no.
    Proof. reflexivity. Qed.

    Example example_three:
        a one (a one no) = 1 || (1 || no).
    Proof. reflexivity. Qed.

    Example example_five:
        a one (a zero (a one no)) = 1 || (0 || (1 || no)).
    Proof. reflexivity. Qed.

    Definition sum_digit (a b r: digit) : digit * digit :=
        match (a, b, r) with
        | (1, 1, 1) => (1, 1)
        | (1, 0, 1) | (1, 1, 0) | (0, 1, 1) => (0, 1)
        | _ => (1, 0)
        end.

    Fixpoint sum_single (y : num) (r : digit) {struct y} : num :=
        match y, r with
        | a 1 y', 0 | a 0 y', 1 =>
            a 1 (sum_single y' 0)
        | a 1 y', 1 =>
            a 1 (sum_single y' 1)
        | a 0 y', 0 =>
            a 0 (sum_single y' 0)
        | no, 0 => no
        | no, 1 => a 1 no
        end.

    Fixpoint sum_rec (x y : num) (r : digit) {struct x} : num := 
        match x, y with
        | a dx x', no => 
            let (s, r') := sum_digit dx 0 r in
            a s (sum_rec x' no r') 
        | a dx x', a dy y' =>
            let (s, r') := sum_digit dx dy r in
            a s (sum_rec x' y' r')  (*structurally smaller argument on the left*)
        | no, _ =>
            sum_single y r
        end.

    Definition sum (x y: num) : num :=
        sum_rec x y 0.
    
    Compute sum (0 || (0 || (1 || no))) (1 || (1 || (0 || no))).
    Compute sum (1 || (0 || (1 || no))) (1 || (1 || (0 || no))).
End BinaryNum.
