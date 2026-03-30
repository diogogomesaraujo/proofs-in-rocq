Module BinaryNum.
    Inductive digit : Type :=
        | zero
        | one.
    
    Inductive num : Type := 
        a (dig : digit) (other : option num).

    Notation "0" := zero.
    Notation "1" := one.

    Notation "&0 ()" := (a zero None).
    Notation "&1 ()" := (a one None).

    Notation "&0 ( n )" := (a zero (Some (n: num))).
    Notation "&1 ( n )" := (a one (Some (n: num))).


    Example example_zero:
        a zero None = &0 ().
    Proof. reflexivity. Qed.

    Example example_three:
        a one (Some (a one None)) = &1 (&1 ()).
    Proof. reflexivity. Qed.

    Definition sum_digit (a b r: digit) : digit * digit :=
        match (a, b, r) with
        | (1, 1, 1) => (1, 1)
        | (1, 0, 1) | (1, 1, 0) | (0, 1, 1) => (0, 1)
        | _ => (1, 0)
        end.

    Fixpoint sum (a b : option num) (r : digit) : num := 
        match (a, b) with
        | Some (cont da a'), Some (cont db b') => 
            let (s, r') := sum_digit da db r in
            cont s (sum a' b' r')
        | Some (cont da a'), Some (cont db b') => 
            let (s, r') := sum_digit da db r in
            cont s (sum a' b' r')
End Num.
