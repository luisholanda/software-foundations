From LF Require Export Basics.

Theorem add_0_r: forall n : nat,
    n + 0 = n.
Proof.
    intros n. induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_n_n: forall n : nat, 
    n - n = 0.
Proof.
    intros n. induction n as [|n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mul_0_r : forall n:nat, 
    n * 0 = 0.
Proof.
    intros n. induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, 
    S (n + m) = n + (S m).
Proof.
    intros n m. induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comm : forall n m : nat, 
    n + m = m + n.
Proof.
    intros n m. induction n as [| n' IHn'].
    - simpl. rewrite -> add_0_r. reflexivity.
    - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
    intros n m p. induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (n : nat) : nat :=
    match n with
    | 0 => 0
    | S n' => S (S (double n'))
    end.

Lemma double_plus: forall n, 
    double n = n + n.
Proof.
    intros n. induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite <- plus_n_Sm. rewrite -> IHn'. reflexivity.
Qed.

Theorem even_S: forall n : nat, 
    even (S n) = negb (even n).
Proof.
    intros n. induction n as [| n' IHn'].
    - reflexivity.
    - rewrite -> IHn'. rewrite -> negb_involutive. reflexivity.
Qed.


Theorem add_shuffle3: forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
    intros n m p.
    rewrite -> add_assoc.
    rewrite -> add_assoc.
    assert (H: n + m = m + n). {
        rewrite -> add_comm.
        reflexivity.
    }
    rewrite -> H.
    reflexivity.
Qed.

Theorem S_add: forall n m : nat,
    n = m -> S n = S m.
Proof.
    intros n m. induction n as [| n IHn'].
    - intros H. rewrite <- H. reflexivity.
    - intros H. rewrite -> H. reflexivity.
Qed.


Theorem mul_n_Sm: forall n m : nat,
    n + n * m = n * (S m).
Proof.
    intros n m. induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite -> add_shuffle3. rewrite -> IHn'. reflexivity.
Qed.


Theorem mul_comm : forall m n : nat,
    m * n = n * m.
Proof.
    intros m n. induction m as [| m' IHm'].
    - rewrite -> mul_0_r. reflexivity. 
    - simpl. 
        rewrite -> IHm'.
        rewrite -> mul_n_Sm.
        reflexivity.
Qed.

(* Exercise: 2 stars, standard, optional (eqb_refl) *)
Theorem eqb_refl : forall n : nat,
    (n =? n) = true.
Proof.
    intros n. induction n as [|n' IHn'].
    - reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.


Theorem add_shuffle3': forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
    intros n m p.
    rewrite -> add_assoc.
    rewrite -> add_assoc.
    replace (n + m) with (m + n).
    - reflexivity.
    - rewrite -> add_comm. reflexivity.
Qed.

Theorem bin_to_nat_pres_incr: forall b : bin,
    bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
    intros b. induction b as [| b0 IHb0| b1 IHb1].
    - reflexivity.
    - simpl. reflexivity.
    - simpl. 
        rewrite -> IHb1.
        rewrite -> add_0_r.
        rewrite -> add_0_r.
        rewrite <- plus_1_l.
        rewrite -> add_shuffle3.
        reflexivity.
Qed.

Fixpoint nat_to_bin (n : nat) : bin :=
    match n with
    | 0 => Z
    | S n' => incr (nat_to_bin n')
    end.

Theorem nat_bin_nat: forall n : nat,
    bin_to_nat (nat_to_bin n) = n.
Proof.
    intros n. induction n as [| n' IHn'].
    - reflexivity.
    - simpl. 
        rewrite -> bin_to_nat_pres_incr. 
        rewrite -> IHn'. 
        reflexivity.
Qed.

(* No idea what is going on here. :(

Theorem bin_nat_bin: forall b : bin,
    nat_to_bin (bin_to_nat b) = b.
Proof.
    intros b. induction b as [| b0 IHb0 | b1 IHb1].
    - reflexivity.
    - simpl. rewrite -> add_0_r.
Qed.


Fixpoint normalize (b : bin) : bin :=
    match b with
    | Z => .
*)