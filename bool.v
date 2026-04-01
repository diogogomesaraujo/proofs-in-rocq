Module Bool.
    Inductive bool : Type :=
        | true
        | false.

    Definition not (b : bool) : bool :=
        match b with
        | true => false
        | false => true
        end.

    Definition and (b1 b2: bool) : bool :=
        match (b1, b2) with
        | (true, true) => true
        | _ => false
        end.

    Definition or (b1 b2: bool) : bool :=
        match (b1, b2) with
        | (true, true) => true
        | (true, false) => true
        | (false, true) => true
        | _ => false
        end.

    Notation "x && y" := (and x y).
    Notation "x || y" := (or x y).

    Example or_true_false:
        or true false = true.
    Proof. reflexivity. Qed.

    Example or_true_true:
        true || false = true.
    Proof. reflexivity. Qed.

    Definition nand (b1 b2 : bool) : bool :=
        not (b1 && b2).

    Example nand_true_false:
        nand true false = true.
    Proof. simpl. reflexivity. Qed.

    Theorem and_commutitive : forall b c : bool, 
        b && c = c && b.
    Proof. 
        intros proof_b.
        intros proof_c.
        destruct proof_b.
            + destruct proof_c.
                reflexivity.
                reflexivity.
            + destruct proof_c.
                reflexivity.
                reflexivity.
    Qed.

End Bool.
