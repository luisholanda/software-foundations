Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF.Volume1 Require Export Tactics.

(* Exercise: 2 stars, standard (and_exercise) *)

Example and_exercise : forall n m : nat,
    n + m = 0 -> n = 0 /\ m = 0.
Proof.
    intros n m eq. split.
    - destruct n.
        + reflexivity.
        + discriminate eq.
    - destruct m.
        + reflexivity.
        + rewrite <- plus_n_Sm in eq. discriminate eq.
Qed.

(* Exercise: 1 star, standard, optional (proj2) *)

Lemma proj2 : forall P Q : Prop,
    P /\ Q -> Q.
Proof.
    intros P Q [_ HQ]. apply HQ.
Qed.

(* Finally, we sometimes need to rearrange the order of conjunctions and/or 
the grouping of multi-way conjunctions. The following commutativity and associativity
theorems are handy in such cases. *)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
    intros P Q [HP HQ].
    split.
        - (* left *) apply HQ.
        - (* right *) apply HP. 
Qed.

(* Exercise: 2 stars, standard (and_assoc)

(In the following proof of associativity, notice how the nested intros pattern breaks
the hypothesis H : P ∧ (Q ∧ R) down into HP : P, HQ : Q, and HR : R. Finish the proof
from there.) *)

Theorem and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
    intros P Q R [HP [HQ HR]].
    split. split. apply HP. apply HQ. apply HR.
Qed.

Theorem ex_falso_quodlibet : forall (P : Prop),
    False -> P.
Proof.
    (* WORKED IN CLASS *)
    intros P contra.
    destruct contra. 
Qed.

(* Exercise: 2 stars, standard, optional (not_implies_our_not)

Show that Coq's definition of negation implies the intuitive one mentioned above: *)

Fact not_implies_our_not : forall P : Prop,
    ~ P -> (forall Q : Prop, P -> Q).
Proof.
    intros P nP Q HP.
    destruct nP. apply HP.
Qed.

(* Exercise: 2 stars, standard, especially useful (contrapositive) *)

Theorem contrapositive: forall P Q : Prop,
    (P -> Q) -> ~Q -> ~P.
Proof.
    intros P Q imp nQ.
    unfold not.
    intros contra.
    apply nQ in imp.
    - destruct imp.
    - apply contra.
Qed.

(* Exercise: 1 star, standard (not_both_true_and_false) *)

Theorem not_both_true_and_false: forall P : Prop,
    ~ (P /\ ~P).
Proof.
    intros P.
    unfold not.
    intros [hP nP].
    apply nP. apply hP.
Qed.

Theorem not_true_is_false: forall b  : bool,
    b <> true -> b = false.
Proof.
    intros b H.
    destruct b eqn:HE.
    - (* b = true *)
        unfold not in H.
        apply ex_falso_quodlibet.
        apply H. reflexivity.
    - reflexivity.
Qed.

Theorem iff_sym: forall P Q : Prop,
    (P <-> Q) -> (Q <-> P).
Proof.
    intros P Q [hPQ hQP].
    split.
    - (* -> *) apply hQP.
    - (* <- *) apply hPQ.
Qed.

Lemma not_true_iff_false: forall b : bool,
    b <> true <-> b = false.
Proof.
    intros b. split.
    - (* -> *) apply not_true_is_false.
    - (* <- *)
        intros H.
        rewrite H.
        intros H'.
        discriminate H'.
Qed.

(* Exercise: 3 stars, standard (or_distributes_over_and) *)

Theorem or_distributes_over_and: forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
    intros P Q R. split.
    - (* -> *)
        intros [hP | [hQ hR]].
        + split.
            * left. apply hP.
            * left. apply hP.
        + split.
            * right. apply hQ.
            * right. apply hR.
    - (* <- *)
        intros [[hP | hQ] [hP' | hR]].
        + left. apply hP.
        + left. apply hP.
        + left. apply hP'.
        + right. split. apply hQ. apply hR.
Qed.

From Coq Require Import Setoids.Setoid.

Theorem or_assoc: forall P Q R : Prop,
    P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
    intros P Q R. split.
    - intros [H | [H | H]].
        + left. left. apply H.
        + left. right. apply H.
        + right. apply H.
    - intros [[H | H] | H].
        + left. apply H.
        + right. left. apply H.
        + right. right. apply H.
Qed.

Definition Even (x : nat) := exists n : nat, x = double n.

(* Exercise: 1 star, standard, especially useful (dist_not_exists)

Prove that "P holds for all x" implies "there is no x for which P does not hold." 
(Hint: destruct H as [x E] works on existential assumptions!) *)

Theorem dist_not_exists: forall (X : Type) (P : X -> Prop),
    (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
    intros X P allX.
    unfold not.
    intros [x hEPx].
    apply hEPx.
    apply allX.
Qed.

(* Exercise: 2 stars, standard (dist_exists_or)

Prove that existential quantification distributes over disjunction. *)

Theorem dist_exists_or: forall (X : Type) (P Q : X -> Prop),
    (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
    intros X P Q. split.
    - intros [x [hEPx | hEQx]].
        + left. exists x. apply hEPx.
        + right. exists x. apply hEQx.
    - intros [[x hEPx] | [x' hEQx]].
        + exists x. left. apply hEPx.
        + exists x'. right. apply hEQx.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
    match l with
    | [] => False
    | x' :: l' => x' = x \/ In x l'
    end.

Theorem In_map: forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l -> In (f x) (map f l).
Proof.
    intros A B f l x. induction l as [|x' l' IHl'].
    - (* l = nil, contradiction *)
        simpl. intros H. apply H.
    - (* l = x' :: l' *)
        simpl. intros [H | H].
        + rewrite H. left. reflexivity.
        + right. apply IHl'. apply H.
Qed.

(* Exercise: 3 stars, standard (In_map_iff) *)

Theorem In_map_iff: forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
    intros A B f l y. split.
    - (* ->  *)
        induction l as [|h t IHl].
        + simpl. intros H. destruct H.
        + simpl. intros [hFhy | hInymapft].
            * exists h. split.
                -- apply hFhy.
                -- simpl. left. apply eq_refl.
            * (* In y (map f t) *) 
                apply IHl in hInymapft. 
                destruct hInymapft as [x [hFxy hInxt]].
                exists x. split.
                    -- apply hFxy.
                    -- right. apply hInxt.
    - (* <- *)
        induction l as [|h t IHl].
        + simpl. intros [x [_ contra]]. destruct contra.
        + simpl. intros [x [hFxy [hhx | hInxt]]].
            * left. rewrite hhx. apply hFxy.
            * right. apply IHl. exists x. split. apply hFxy. apply hInxt.
Qed.

(*  Exercise: 2 stars, standard (In_app_iff) *)

Theorem In_app_iff: forall (A: Type) (l l': list A) (a : A),
    In a (l ++ l') <-> In a l \/ In a l'.
Proof.
    intros A l. induction l as [|a' l' IH].
    - simpl. intros l' a. split.
        + right. apply H.
        + intros [H | H].
            * destruct H.
            * apply H.
    - intros t b. simpl. split.
        + intros [haeqb | hInblt].
            * left. left. apply haeqb.
            * apply IH in hInblt. destruct hInblt as [hInbl | hInbt].
                -- left. right. apply hInbl.
                -- right. apply hInbt.
        + intros [[haeqb | hInbl] | hInbt].
            * left. apply haeqb.
            * right. apply IH. left. apply hInbl.
            * right. apply IH. right. apply hInbt.
Qed.

(* Exercise: 3 stars, standard, especially useful (All)

Recall that functions returning propositions can be seen as properties of their
arguments. For instance, if P has type nat → Prop, then P n states that property
P holds of n.

Drawing inspiration from In, write a recursive function All stating that some
property P holds of all elements of a list l. To make sure your definition is
correct, prove the All_In lemma below. (Of course, your definition should not
just restate the left-hand side of All_In.)  *)

Fixpoint All {T: Type} (P : T -> Prop) (l : list T) : Prop :=
    match l with
    | nil => True
    | h :: t => (P h) /\ (All P t)
    end.

Theorem All_In: forall (T: Type) (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <-> All P l.
Proof.
    intros T P l. split.
    - (* -> *)
        intros H. induction l as [|h t IH].
        + reflexivity.
        + split.
            * apply H. simpl. left. apply eq_refl.
            * apply IH. intros x H'. apply H. right. apply H'.
    - (* <- *)
        intros hAll. induction l as [|h t IH].
        + intros x contra. destruct contra.
        + intros x hInxht. destruct hAll as [hPh hAllt]. destruct hInxht as [hheqx | hInxt].
            * rewrite <- hheqx. apply hPh.
            * apply IH.
                -- apply hAllt.
                -- apply hInxt.
Qed.

(* Exercise: 2 stars, standard, optional (combine_odd_even)

Complete the definition of the combine_odd_even function below. It takes as arguments 
two properties of numbers, Podd and Peven, and it should return a property P such that
P n is equivalent to Podd n when n is odd and equivalent to Peven n otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) (n: nat): Prop :=
    if odd n then Podd n else Peven n.

Theorem combine_odd_even_intro : forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) -> (odd n = false -> Peven n) -> combine_odd_even Podd Peven n.
Proof.
    intros Podd Peven n hOdd hEven.
    unfold combine_odd_even.
    destruct (odd n).
    - apply hOdd. reflexivity.
    - apply hEven. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd : forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n -> odd n = true -> Podd n.
Proof.
    intros Podd Peven n H hOdd.
    unfold combine_odd_even in H. 
    rewrite hOdd in H. 
    apply H.
Qed.

Theorem combine_odd_even_elim_even : forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n -> odd n = false -> Peven n.
Proof.
    intros Podd Peven n H hEven.
    unfold combine_odd_even in H.
    rewrite hEven in H.
    apply H.
Qed.

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
  (forall (x : X), f x = g x) -> f = g.

(* Exercise: 4 stars, standard (tr_rev_correct)

One problem with the definition of the list-reversing function rev that we have 
is that it performs a call to app on each step; running app takes time asymptotically
linear in the size of the list, which means that rev is asymptotically quadratic. We 
can improve this with the following definitions: *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
    match l1 with
    | [] => l2
    | x :: l1' => rev_append l1' (x :: l2)
    end.

Definition tr_rev {X} (l : list X) : list X := rev_append l [].

(* This version of rev is said to be tail-recursive, because the recursive call to
the function is the last operation that needs to be performed (i.e., we don't have 
to execute ++ after the recursive call); a decent compiler will generate very efficient
code in this case.

Prove that the two definitions are indeed equivalent. *)

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
(* No idea how to prove this, get stuck in some cases :( *)
Proof. Admitted.

Lemma even_double: forall k, even (double k) = true.
Proof.
    intros  k. induction k as [|k' IHk'].
    - reflexivity.
    - simpl. apply IHk'.
Qed.

(* Exercise: 3 stars, standard (even_double_conv) *)

Lemma even_double_conv: forall n, exists k,
    n = if even n then double k else S (double k).
Proof.
    intros n. induction n as [|n' [k' IHk']].
    - exists 0. reflexivity.
    - rewrite even_S. destruct (even n').
        + simpl. exists k'. f_equal. apply IHk'.
        + simpl. rewrite IHk'. exists (S k'). reflexivity.
Qed.

Theorem even_bool_prop: forall n, 
    even n = true <-> Even n.
Proof.
    intros n. split.
    - (* -> *)
        intros H. 
        destruct (even_double_conv n) as [k Hk].
        rewrite Hk. rewrite H. 
        exists k. reflexivity.
    - (* <- *)
        intros [k Hk]. rewrite Hk. apply even_double.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
    n1 =? n2 = true <-> n1 = n2.
Proof.
    intros n1 n2. split.
    - apply eqb_true.
    - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.


(* Exercise: 2 stars, standard (logical_connectives)

The following theorems relate the propositional connectives studied in this 
chapter to the corresponding boolean operations. *)

Theorem andb_true_iff : forall b1 b2:bool,
    b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
    intros b1 b2. split.
    - (* -> *)
        intros H. split.
        + (* b1 *)
            rewrite andb_commutative in H.
            apply andb_true_elim2 in H.
            apply H.
        + (* b2 *)
            apply andb_true_elim2 in H.
            apply H.
    - (* <- *)
        intros H. destruct H as [H1 H2].
        rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem orb_true_iff : forall b1 b2,
    b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
    intros b1 b2. split.
    - (* -> *)
        intros H. destruct b1.
        + left. reflexivity.
        + right. simpl in H. apply H.
    - (* <- *)
        intros H. destruct H as [H1 | H2].
        + rewrite H1. reflexivity.
        + rewrite H2. destruct b1.
            * reflexivity.
            * reflexivity.
Qed.

(* Exercise: 1 star, standard (eqb_neq)

The following theorem is an alternate "negative" formulation of eqb_eq that
is more convenient in certain situations. (We'll see examples in later chapters.)
Hint: not_true_iff_false. *)

Theorem eqb_neq : forall x y : nat,
    x =? y = false <-> x <> y.
Proof.
    intros x y. unfold not. split.
    - (* -> *)
        intros H1 H2.
        rewrite H2 in H1.
        rewrite NatList.eq_refl in H1.
        discriminate H1.
    - (* <- *)
        intros H.
        rewrite <- not_true_iff_false.
        unfold not.
        intros H1.
        apply H.
        apply eqb_eq in H1.
        apply H1.
Qed.

(* Exercise: 3 stars, standard (eqb_list)

Given a boolean operator eqb for testing equality of elements of some type A,
we can define a function eqb_list for testing equality of lists with elements
in A. Complete the definition of the eqb_list function below. To make sure
that your definition is correct, prove the lemma eqb_list_true_iff. *)

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  match l1, l2 with
  | nil, nil => true
  | h1 :: t1, h2 :: t2 => (eqb h1 h2) && (eqb_list eqb t1 t2)
  | _, _ => false
  end.

Theorem eqb_list_true_iff : forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
    intros A eqb Heqb l1. split.
    - (* -> *)
        generalize dependent l2.
        induction l1 as [|h1 t1 IHt1].
        + destruct l2.
            * reflexivity.
            * intros H. discriminate H.
        + destruct l2 as [|h2 t2].
            * intros H. discriminate H.
            * destruct (eqb h1 h2) eqn:E.
                --  simpl. rewrite E. simpl. 
                    destruct (Heqb h1 h2) as [H1 H2].
                    apply H1 in E. rewrite E. 
                    intros H. f_equal. 
                    apply (IHt1 t2).
                    apply H.
                -- simpl. rewrite E. simpl.
                    intros H. discriminate H.
    - (* <- *)
        generalize dependent l2.
        induction l1 as [|h1 t1 IHt1].
        + destruct l2.
            * reflexivity.
            * intros H. discriminate H.
        + destruct l2.
            * intros H. discriminate H.
            * intros H. injection H as H1 H2. simpl. destruct (Heqb h1 x) as [H3 H4].
                -- apply H4 in H1. rewrite H1. simpl. apply (IHt1 l2). apply H2.
Qed.

(* Exercise: 2 stars, standard, especially useful (All_forallb)

Recall the function forallb, from the exercise forall_exists_challenge in chapter Tactics:

Fixpoint forallb {X : Type} (test : X → bool) (l : list X) : bool :=
  match l with
  | [] ⇒ true
  | x :: l' ⇒ andb (test x) (forallb test l')
  end.

Prove the theorem below, which relates forallb to the All property defined above.
*)

Theorem forallb_true_iff : forall X test (l : list X),
    forallb test l = true <-> All (fun x => test x = true) l.
Proof.
    intros X test l. split.
    - (* -> *)
        induction l as [|h t IHt].
        + reflexivity.
        + destruct (test h) eqn:E.
            * simpl. rewrite E. simpl. split.
                -- reflexivity.
                -- apply IHt. apply H.
            * simpl. rewrite E. simpl. intros H. discriminate H.
    - (* <- *)
        induction l as [|h t IHt].
        + reflexivity.
        + destruct (test h) eqn:E.
            * simpl. rewrite E. simpl. intros [_ A]. apply IHt. apply A.
            * simpl. rewrite E. simpl. intros [F _]. apply F.
Qed.

Definition excluded_middle := forall P : Prop, P \/ ~ P.

(* Exercise: 3 stars, standard (excluded_middle_irrefutable)

Proving the consistency of Coq with the general excluded middle axiom requires complicated 
reasoning that cannot be carried out within Coq itself. However, the following theorem implies 
that it is always safe to assume a decidability axiom (i.e., an instance of excluded middle) 
for any particular Prop P. Why? Because we cannot prove the negation of such an axiom. If we 
could, we would have both ¬ (P ∨ ¬P) and ¬ ¬ (P ∨ ¬P) (since P implies ¬ ¬ P, by lemma double_neg, 
which we proved above), which would be a contradiction. But since we can't, it is safe to add 
P ∨ ¬P as an axiom.

Succinctly: for any proposition P, Coq is consistent ==> (Coq + P ∨ ¬P) is consistent.
(Hint: You may need to come up with a clever assertion as the next step in the proof.) *)

(* Mechanical proof, not pretty :( *)
Theorem excluded_middle_irrefutable_uggly: forall (P : Prop),
    ~ ~ (P \/ ~ P).
Proof.
    unfold not. intros P H.
    apply H.
    right.
    intros p.
    apply H.
    left. 
    apply p.
Qed.

(* We will ignore the starting `unfold not`... 

First, we will need seconds De Morgan's Law:
*)

Theorem de_morgan_neg_of_disj: forall (P Q : Prop),
    ~(P \/ Q) -> (~P /\ ~Q).
Proof.
    unfold not.
    intros P Q.
    intros H. split.
    - intros P'. apply H. left. apply P'.
    - intros Q'. apply H. right. apply Q'.
Qed.

(* Now, we can prove this in a pretty way :D *)
Theorem excluded_middle_irrefutable: forall (P : Prop),
    ~ ~ (P \/ ~P).
Proof.
    intros P H.
    apply de_morgan_neg_of_disj in H.
    apply not_both_true_and_false in H.
    apply H.
Qed.

(* Exercise: 3 stars, advanced (not_exists_dist)

It is a theorem of classical logic that the following two assertions are equivalent:

    ¬(∃ x, ¬P x)
    ∀ x, P x

The dist_not_exists theorem above proves one side of this equivalence. Interestingly,
the other direction cannot be proved in constructive logic. Your job is to show that
it is implied by the excluded middle. *)

Theorem not_exists_dist : excluded_middle -> forall (X : Type) (P : X -> Prop), 
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
    intros EM X P H x.
    destruct (EM (P x)).
    - apply H0.
    - destruct H. exists x. apply H0.
Qed.

(* Exercise: 5 stars, standard, optional (classical_axioms)

For those who like a challenge, here is an exercise taken from the Coq'Art book by Bertot 
and Casteran (p. 123). Each of the following four statements, together with excluded_middle, 
can be considered as characterizing classical logic. We can't prove any of them in Coq, but
we can consistently add any one of them as an axiom if we wish to work in classical logic.

Prove that all five propositions (these four plus excluded_middle) are equivalent.

Hint: Rather than considering all pairs of statements pairwise, prove a single circular 
chain of implications that connects them all. *)

Definition peirce := forall P Q : Prop,
    ((P -> Q) -> P) -> P.

Definition double_negation_elimination := forall P : Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q : Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q : Prop,
  (P -> Q) -> (~P \/ Q).

Theorem peirce_iff_double_negation_elimination: 
    peirce <-> double_negation_elimination.
Proof.
    split.
    - (* -> *)
        intros Peirce P DoubleNegation.
        apply Peirce with (Q := False).
        intros P_False.
        apply DoubleNegation in P_False.
        inversion P_False.
    - (* <- *)
        intros DoubleNegation P Q P_Q_P.
        assert (~~P) as P_DoubleNeg.
            intros P_False.
            assert (P -> Q) as P_Q.
                intros p.
                apply P_False in p.
                inversion p.
            apply P_Q_P in P_Q.
            apply P_False in P_Q.
            apply P_Q.
        apply DoubleNegation in P_DoubleNeg.
        apply P_DoubleNeg.
Qed.

Theorem double_negation_elimination_de_morgan_not_and_not:
    double_negation_elimination <-> de_morgan_not_and_not.
Proof.
    split.
    - (* -> *)
        intros DoubleNegation P Q N_N_P_A_N_Q.
        unfold not in N_N_P_A_N_Q.
        apply DoubleNegation.
        unfold not.
        intros P_Or_Q_false.
        assert ((P -> False) /\ (Q -> False)) as P_F_A_Q_F.
            split.
            (* P -> False *)
            intros.
                apply or_introl with (B := Q) in H.
                apply P_Or_Q_false in H. apply H.
            (* Q -> False *)
            intros.
                apply or_intror with (A := P) in H.
                apply P_Or_Q_false in H. apply H.
        apply N_N_P_A_N_Q in P_F_A_Q_F. apply P_F_A_Q_F.
    - (* <- *)
        intros DeMorgan P P_DoubleNeg.
        assert (~(~P /\ ~P)) as N_N_P_A_N_P.
            unfold not.
            intros.
            inversion H.
            apply P_DoubleNeg in H0. apply H0.
        apply DeMorgan in N_N_P_A_N_P.
        destruct N_N_P_A_N_P.
        apply H. apply H.
Qed.

Theorem de_morgan_not_and_not_implies_to_or: 
    de_morgan_not_and_not <-> implies_to_or.
Proof.
    split.
    - (* -> *)
        intros DeMorgan P Q P_Q.
        apply DeMorgan.
        unfold not.
        intros P_F_F_A_Q_F.
        destruct P_F_F_A_Q_F as [P_F_F Q_False].
        apply P_F_F.
        intros p.
        apply P_Q in p.
        apply Q_False in p.
        apply p.
    - (* <- *)
        intros ImpliesToOr P Q N_N_P_A_N_Q.
Admitted.

Theorem implies_to_or_excluded_middle: 
    implies_to_or <-> excluded_middle.
Proof.
Admitted.


