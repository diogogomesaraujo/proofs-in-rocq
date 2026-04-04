Theorem plus_id : forall n m : nat,
    n = m -> n + n = n + m.
Proof.
    intros proof_n.
    intros proof_m.
    intros n_equal_m.
    rewrite n_equal_m.
    reflexivity.
Qed.

Theorem identity : forall n : nat,
    n + 0 = n.
Proof.
    intros proof_n.
    induction proof_n.
        + compute.
          reflexivity.
        + simpl.
          rewrite IHproof_n.
          reflexivity.
Qed.

Theorem sum_zero : forall n m : nat, n = 0 ->
    m + n = m.
Proof.
    intros n.
    intros m.
    intros H.
    rewrite H.
    apply identity.
Qed.

Theorem sum_minus : forall n m : nat, 
    n >= m -> n - m >= 0.
Proof.
    intros proof_n. 
    intros proof_m.
    intros n_bigger_equal_m.
    induction proof_n.
        + simpl. apply le_n. 
        + simpl. destruct proof_m.
            - assumption.
            - apply le_0_n.
Qed.