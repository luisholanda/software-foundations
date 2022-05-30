From LF.Volume1 Require Export Poly.

(* Exercise: 2 stars, standard, optional (silly_ex)

Complete the following proof using only intros and apply. 
*)

Theorem silly_ex : forall p : nat,
    (forall n : nat, even n = true -> even (S n) = false) ->
    (forall n : nat, even n = false -> odd n = true) ->
    even p = true ->
    odd (S p) = true.
Proof.
    intros p H1 H2 H3.
    apply H2.
    apply H1.
    apply H3.
Qed.

(* Exercise: 3 stars, standard (apply_exercise1)

Hint: You can also use apply with previously defined lemmas, not just
hypotheses in the context. You may find earlier lemmas like app_nil_r, 
app_assoc, rev_app_distr, rev_involutive, etc. helpful. Also, remember 
that Search is your friend (though it may not find earlier lemmas if they
were posed as optional problems and you chose not to finish the proofs). 
*)

Theorem rev_exercise1: forall l l' : list nat, 
    l = rev l' -> l' = rev l.
Proof.
    intros l l' H.
    rewrite -> H.
    symmetry.
    apply rev_involutive.
Qed.

(* Exercise: 3 stars, standard, optional (trans_eq_exercise) *)

Example trans_eq_exercise : forall (n m o p : nat),
    m = (minustwo o) ->
    (n + p) = m ->
    (n + p) = (minustwo o).
Proof.
    intros n m o p H1 H2.
    transitivity m.
    apply H2. apply H1.
Qed.

Example injection_ex3: forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j -> j = z :: l -> x = y.
Proof.
    intros X x y z l j H1.
    injection H1 as H3 H4.
    rewrite <- H4.
    intros H2.
    injection H2 as H5.
    transitivity z.
    apply H3. symmetry. apply H5.
Qed.

(* Exercise: 1 star, standard (discriminate_ex3) *)

Example discriminate_ex3 : forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] -> x = z.
Proof.
    intros X x y z l j H. discriminate H.
Qed.

Theorem eq_implies_succ_equal: forall n m : nat,
    n = m -> S n = S m.
Proof.
    intros n m H. f_equal. apply H.
Qed.

Theorem silly4: forall n m p q : nat,
    (n = m -> p = q) -> m = n -> q = p.
Proof.
    intros n m p q EQ H.
    symmetry in H. apply EQ in H. symmetry in H.
    apply H.
Qed.

(* Exercise: 2 stars, standard (eqb_true) *)

Theorem eqb_true: forall n m : nat,
    n =? m = true -> n = m.
Proof.
    intros n. induction n as [|n' IHn'].
    - intros m EQ. destruct m as [| m'] eqn:E.
        + reflexivity.
        + discriminate EQ.
    - intros m EQ. destruct m as [| m'] eqn:E.
        + discriminate EQ.
        + simpl in EQ. apply IHn' in EQ. f_equal. apply EQ.
Qed.

(* Exercise: 3 stars, standard, especially useful (plus_n_n_injective)

In addition to being careful about how you use intros, practice using "in" variants
in this proof. (Hint: use plus_n_Sm.)  *)

Theorem plus_n_n_injective: forall n m : nat,
    n + n = m + m -> n = m.
Proof.
    intros n. induction n as [|n' IHn'].
    - intros m EQ. simpl in EQ. destruct m as [|m'] eqn:E.
        + reflexivity.
        + discriminate EQ.
    - intros m EQ. destruct m as [|m'] eqn:E.
        + discriminate EQ.
        + 
            f_equal.
            apply IHn'.
            simpl in EQ.
            rewrite <- plus_n_Sm in EQ.
            rewrite <- plus_n_Sm in EQ.
            injection EQ as goal.
            apply goal.
Qed.

(* Exercise: 3 stars, standard, especially useful (gen_dep_practice)

Prove this by induction on l.  *)

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
    length l = n -> nth_error l n = None.
Proof.
    intros n X l.
    generalize dependent n.
    induction l as [|h' t' IHl'].
    - reflexivity.
    - intros n eq. destruct n as [|n'] eqn:E.
        + discriminate eq.
        + simpl. apply IHl'. simpl in eq. injection eq as goal. apply goal.
Qed.

(* Exrcise: 3 stars standard (commbine_split) 

Prove that split and combine are inverses in the following sense: 
*)

Theorem combine_split: forall (X Y : Type) (l : list (X * Y)) l1 l2,
    split l = (l1, l2) -> combine l1 l2 = l.
Proof.
    intros X Y l.
    induction l as [|h t IHl'].
    - (* l = nil *)
        simpl. intros l1 l2 eq.
        symmetry in eq.
        injection eq as eq1 eq2.
        rewrite eq1. rewrite eq2.
        reflexivity.
    - (* l = cons h t *)
        simpl. intros l1 l2 eq.
        destruct h.
        symmetry in eq.
        destruct (split t).
        injection eq as eq1 eq2.
        rewrite eq1. rewrite eq2. simpl.
        f_equal.
        apply IHl'.
        reflexivity.
Qed.

(* Exercise: 2 stars, standard (destruct_eqn_practice) *)

Theorem bool_fn_applied_thrice: forall (f : bool -> bool) (b : bool),
    f (f (f b)) = f b.
Proof.
    intros f.
    f_equal.
    destruct (f true) eqn:ft.
    - destruct (f false) eqn:ff.
        + destruct b eqn:eqb.
            * f_equal. rewrite ft. apply ft.
            * rewrite ff. rewrite ft. apply ft.
        + destruct b eqn:eqb.
            * f_equal. rewrite ft. apply ft.
            * f_equal. rewrite ff. apply ff.
    - destruct (f false) eqn:ff.
        + destruct b eqn:eqb.
            * f_equal. rewrite ft. apply ff.
            * f_equal. rewrite ff. apply ft.
        + destruct b eqn:eqb.
            * rewrite ft. rewrite ff. apply ff.
            * f_equal. rewrite ff. apply ff.
Qed.

(* Exercise: 3 stars, standard (eqb_sym) *)

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
    intros n. induction n as [|n' IHn'].
    - intros m. destruct m as [|m'].
        + reflexivity.
        + reflexivity.
    - intros m. destruct m as [|m'].
        + reflexivity.
        + simpl. apply IHn'.
Qed.

(* Exercise: 3 stars, standard, optional (eqb_trans) *)

Theorem eqb_trans : forall n m p,
    n =? m = true ->
    m =? p = true ->
    n =? p = true.
Proof.
    intros n m p eqnm eqmp.
    rewrite <- eqmp.
    f_equal.
    apply eqb_true in eqnm.
    apply eqnm.
Qed.


(* Exercise: 3 stars, advanced (split_combine)

We proved, in an exercise above, that for all lists of pairs, combine is 
the inverse of split. How would you formalize the statement that split is 
the inverse of combine? When is this property true?
    
Complete the definition of split_combine_statement below with a property 
that states that split is the inverse of combine. Then, prove that the 
property holds. (Be sure to leave your induction hypothesis general by 
not doing intros on more things than necessary. Hint: what property do you 
need of l1 and l2 for split (combine l1 l2) = (l1,l2) to be true?)

*)

Definition split_combine_statement : Prop :=
  (* (": Prop" means that we are giving a name to a
     logical proposition here.) *)
  forall (X Y : Type) 
         (l1 : list X) 
         (l2 : list Y), 
  length l1 = length l2 -> split (combine l1 l2) = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
    intros X Y l1. induction l1 as [|h1 t1 IHl1'].
    - simpl. intros l2 eq. destruct l2.
        + reflexivity.
        + discriminate eq.
    - intros l2 eq. destruct l2 eqn:eql2.
        + discriminate eq.
        + injection eq as eq. simpl. rewrite IHl1'.
            * reflexivity.
            * apply eq.
Qed.

(* Exercise: 3 stars, advanced (filter_exercise)

This one is a bit challenging. Pay attention to the form of your induction hypothesis.
*)

Theorem filter_exercise : forall (X : Type) 
                                 (test : X -> bool)
                                 (x : X) 
                                 (l lf : list X),
  filter test l = x :: lf -> test x = true.
Proof.
  intros X test x l. induction l as [|h t IHl'].
  - intros lf eq. discriminate eq.
  - destruct (test h) eqn:eqh.
    + (* test h = true *) 
        simpl. rewrite eqh.
        intros lf eq.
        injection eq as eq1 eq2.
        rewrite <- eq1. apply eqh.
    + (* test h = false *)
        simpl. rewrite eqh.
        apply IHl'.
Qed.

(* Exercise: 4 stars, advanced, especially useful (forall_exists_challenge)

Define two recursive Fixpoints, forallb and existsb. The first checks whether every element
in a list satisfies a given predicate:

      forallb odd [1;3;5;7;9] = true
      forallb negb [false;false] = true
      forallb even [0;2;4;5] = false
      forallb (eqb 5) [] = true

The second checks whether there exists an element in the list that satisfies a given predicate:

      existsb (eqb 5) [0;2;3;6] = false
      existsb (andb true) [true;true;false] = true
      existsb odd [1;0;0;0;0;3] = true
      existsb even [] = false

Next, define a nonrecursive version of existsb -- call it existsb' -- using forallb and negb.
Finally, prove a theorem existsb_existsb' stating that existsb' and existsb have the same behavior.
*)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
    match l with
    | nil => true
    | h :: t => (test h) && (forallb test t)
    end.

Example test_forallb_1 : forallb odd [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb even [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
    match l with
    | nil => false
    | h :: t => (test h) || (existsb test t)
    end.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb even [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
    fold (fun x e => test x || e) l false.

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
    existsb test l = existsb' test l.
Proof.
    intros X test l. induction l as [|h t IHl].
    - reflexivity.
    - unfold existsb'. simpl. destruct (test h).
        + reflexivity.
        + simpl. unfold existsb' in IHl. apply IHl.
Qed.