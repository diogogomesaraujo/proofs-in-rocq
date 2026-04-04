Require Import Arith.

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

Theorem sub_ge_0 : forall n m : nat, 
    n >= m -> n - m >= 0.
Proof.
    intros proof_n. 
    intros proof_m.
    intros n_bigger_equal_m.
    induction proof_n.
        + simpl. apply le_0_n. 
        + simpl. destruct proof_m.
            - assumption.
            - apply le_0_n.
Qed.

Theorem ge_n_m: forall k n m : nat,
    n <= m -> k * n <= k * m. 
Proof.
    intros proof_k.
    intros proof_n.
    intros proof_m.
    intros n_le_m.
    induction proof_k.
        + simpl. apply le_n.
        + simpl. apply Nat.add_le_mono.
            - assumption.
            - assumption.
Qed.            