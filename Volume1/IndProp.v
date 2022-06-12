Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.
From Coq Require Import Lia.

Inductive ev : nat -> Prop :=
    | ev_0 : ev 0
    | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(* Exercise: 1 star, standard (ev_double) *)

Theorem ev_double : forall (n : nat),
    ev (double n).
Proof.
    intros n. induction n as [|n' IHn'].
    - simpl. apply ev_0.
    - simpl. apply ev_SS. apply IHn'.
Qed.

Theorem ev_inversion : forall (n : nat), 
    ev n -> (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
    intros n E.
    destruct E as [ | n' E'] eqn:EE.
    - (* E = ev_0 : ev 0 *)
        left. reflexivity.
    - (* E = ev_SS n' E' : ev (S (S n')) *)
        right. exists n'. split. reflexivity. apply E'.
Qed.

Theorem evSS_ev': forall (n: nat),
    ev (S (S n)) -> ev n.
Proof.
    intros n E.
    inversion E as [|n' E' Heq].
    apply E'.
Qed.

(* Exercise: 1 star, standard (inversion_practice)

Prove the following result using inversion. (For extra practice, you 
can also prove it using the inversion lemma.) *)

Theorem SSSSev__even : forall n : nat,
    ev (S (S (S (S n)))) -> ev n.
Proof.
    intros n E.
    inversion E as [|n' E' Heq].
    inversion E' as [|n'' E'' Heq'].
    apply E''.
Qed.

(* Exercise: 1 star, standard (ev5_nonsense)

Prove the following result using inversion. *)

Theorem ev5_nonsense :
    ev 5 -> 2 + 2 = 9.
Proof.
    intros E.
    inversion E.
    inversion H0.
    inversion H2.
Qed.

Lemma ev_Even: forall n : nat,
    ev n -> Even n.
Proof.
    intros n E. induction E as [|n' E' IH].
    - (* E = ev 0 *)
        exists 0. reflexivity.
    - (* E = ev_SS n' E', IH: Even E' *)
        destruct IH as [k Hk].
        rewrite Hk.
        exists (S k).
        reflexivity.
Qed.

Theorem ev_Even_iff: forall n : nat,
    ev n <-> Even n.
Proof.
    intros n. split.
    - (* -> *) apply ev_Even.
    - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(* Exercise: 2 stars, standard (ev_sum) *)

Theorem ev_sum : forall n m : nat, 
    ev n -> ev m -> ev (n + m).
Proof.
    intros n m En Em. induction En as [|n' En' IH].
    - simpl. apply Em.
    - simpl. apply ev_SS. apply IH.
Qed.

(* Exercise: 4 stars, advanced, optional (ev'_ev)

In general, there may be multiple ways of defining a property inductively. 
For example, here's a (slightly contrived) alternative definition for ev: *)

Inductive ev' : nat -> Prop :=
    | ev'_0 : ev' 0
    | ev'_2 : ev' 2
    | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

(* Prove that this definition is logically equivalent to the old one. To streamline
the proof, use the technique (from Logic) of applying theorems to arguments, and 
note that the same technique works with constructors of inductively defined propositions. *)

Theorem ev'_ev : forall n : nat, 
    ev' n <-> ev n.
Proof.
    intros n. split.
    - (* -> *)
        intros E'n. induction E'n as [| |n' m' E'n' En E'm IH].
        + apply ev_0.
        + apply ev_SS. apply ev_0.
        + apply (ev_sum n' m'). apply En. apply IH.
    - (* <- *)
        intros En. induction En as [|n' En' IH].
        + apply ev'_0.
        + inversion IH.
            * apply ev'_2.
            * apply (ev'_sum 2 2 ev'_2 ev'_2).
            * (* n' = n + m *)
                assert (ev' (S (S n))) as Ev'SSn.
                    apply (ev'_sum 2 n ev'_2 Hn).
                apply (ev'_sum (S (S n)) m Ev'SSn Hm).
Qed.

(* Exercise: 3 stars, advanced, especially useful (ev_ev__ev)

There are two pieces of evidence you could attempt to induct upon here. If one doesn't
 work, try the other. *)

Theorem ev_ev__ev : forall n m : nat,
    ev (n+m) -> ev n -> ev m.
Proof.
    intros n m Enm En.
    generalize dependent Enm.
    induction En as [|n' En' IH].
    - simpl. intros. apply Enm.
    - simpl. intros. inversion Enm as [|n En'm H]. apply IH in En'm. apply En'm.
Qed.

(* Exercise: 3 stars, standard, optional (ev_plus_plus)

This exercise can be completed without induction or case analysis. But, you will need a
clever assertion and some tedious rewriting. Hint: is (n+m) + (n+p) even? *)

Theorem ev_plus_plus : forall n m p : nat,
    ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
    intros n m p Enm Enp.
    assert (ev (n + n + (m + p))) as Ennmp.
        assert (ev ((n + m) + (n + p))) as Enmnp.
            apply (ev_sum (n + m) (n + p)). apply Enm. apply Enp.
        rewrite <- add_assoc in Enmnp.
        rewrite (add_shuffle3 m n p) in Enmnp.
        rewrite add_assoc in Enmnp.
        apply Enmnp.
    apply (ev_ev__ev (n+n) (m+p)) in Ennmp. apply Ennmp.
    rewrite <- double_plus.
    apply ev_double.
Qed.

Module Playground.
    Inductive le : nat -> nat -> Prop :=
        | le_n (n : nat) : le n n
        | le_S (n m : nat) (H : le n m) : le n (S m).

    Notation "n <= m" := (le n m).
    
    Example test_le1: 3 <= 3.
    Proof. apply le_n. Qed.

    Example test_le2: 3 <= 6.
    Proof. apply le_S. apply le_S. apply le_S. apply le_n. Qed.

    Example test_le3: (2 <= 1) -> 2 + 2 = 5.
    Proof. intros H. inversion H. inversion H2. Qed.

    Definition lt (n m : nat) := le (S n) m.

    Notation "m < n" := (lt m n).
End Playground.

Inductive square_of : nat -> nat -> Prop :=
    | sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
    | nn n : next_nat n (S n).

Inductive next_ev : nat -> nat -> Prop :=
    | ne1 n (H: ev (S n)) : next_ev n (S n)
    | ne2 n (H: ev (S (S n))) : next_ev n (S (S n)).

(* Exercise: 2 stars, standard, optional (total_relation)

Define an inductive binary relation total_relation that holds between every pair of natural numbers. *)

Inductive total_relation : nat -> nat -> Prop :=
    | tr n m : total_relation n m.

Theorem total_relation_is_total: forall (n m : nat),
    total_relation n m.
Proof.
    apply tr.
Qed.


(* Exercise: 2 stars, standard, optional (empty_relation)

Define an inductive binary relation empty_relation (on numbers) that never holds. *)

Inductive empty_relation : nat -> nat -> Prop :=
    | er n m  (H: False) : empty_relation n m.

Theorem empty_relation_never_holds: forall (n m : nat),
    ~(empty_relation n m).
Proof.
    intros n m H.
    inversion H.
    apply H0.
Qed.


(* Exercise: 3 stars, standard, optional (le_exercises)

Here are a number of facts about the ≤ and < relations that we are going to need later in 
the course. The proofs make good practice exercises. *)

Lemma le_trans : forall m n o, 
    m <= n -> n <= o -> m <= o.
Proof.
    intros m n o Hmn Hno.
    transitivity n. 
    apply Hmn. apply Hno.
Qed.

Theorem O_le_n : forall n,
    0 <= n.
Proof.
    intros n. induction n as [|n IHn].
        apply le_n.
    apply le_S.
    apply IHn.
Qed.

Theorem le_succ: forall n,
    n <= S n.
Proof.
    intros n. apply le_S. apply le_n.
Qed.


Theorem n_le_m__Sn_le_Sm : forall n m,
    n <= m -> S n <= S m.
Proof.
    intros n m Hnm. induction n as [|n' IHn'].
    - induction m as [|m' IHm']. apply le_n.
        inversion Hnm.
        apply IHm' in H0.
        apply le_S.
        apply H0.
    - induction m as [|m' IHm'].
        all: (inversion Hnm).
        apply le_n.
        apply IHm' in H0.
            apply le_S in H0. apply H0.
        intros HEqnm.
        apply Hnm.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
    S n <= S m -> n <= m.
Proof.
    intros n m HSnSm.
    inversion HSnSm. apply le_n.
    apply (le_trans n (S n) m (le_succ n) H0).
Qed.

Theorem ge__eq_gt: forall n m,
    n >= m -> n = m \/ n > m.
Proof.
    intros n. 
    induction n as [|n' IHn'].
    + intros m Hnm. inversion Hnm. left. reflexivity.
    + intros m Hnm. 
        inversion Hnm.
            left. reflexivity.
        inversion H0.
            right. apply le_n.
        right.
        apply n_le_m__Sn_le_Sm.
        apply (le_trans m m1 (S m1)).
        apply H1.
        apply le_succ.
Qed.


Theorem lt_ge_cases : forall n m,
    n < m \/ n >= m.
Proof.
    intros n m.
    induction m as [|m' IHm'].
    - right. apply O_le_n.
    - destruct (IHm') as [Ltnm' | Lenm'].
        + left. 
            apply n_le_m__Sn_le_Sm.
            apply le_S in Ltnm'.
            apply Sn_le_Sm__n_le_m in Ltnm'.
            apply Ltnm'.
        + induction n as [|n' IHn'].
            left. apply n_le_m__Sn_le_Sm. apply O_le_n.
            inversion Lenm'.
                left. apply n_le_m__Sn_le_Sm. apply le_n.
            right. apply n_le_m__Sn_le_Sm. apply H0.
Qed.


Theorem le_plus_l : forall a b,
    a <= a + b.
Proof.
    intros a b. induction a as [|a' IHa'].
    - rewrite plus_0_n. apply O_le_n.
    - simpl. apply n_le_m__Sn_le_Sm. apply IHa'.
Qed.

Theorem le_plus_r : forall a b,
    b <= a + b.
Proof.
    intros a b. induction a as [|a' IHa'].
    - rewrite plus_0_n. apply le_n.
    - simpl. apply le_S. apply IHa'.
Qed.

Theorem plus_le : forall n1 n2 m,
    n1 + n2 <= m ->
    n1 <= m /\ n2 <= m.
Proof.
    intros n1 n2 m H. split.
    - apply (le_trans n1 (n1 + n2) m (le_plus_l n1 n2) H).
    - apply (le_trans n2 (n1 + n2) m (le_plus_r n1 n2) H).
Qed.

(* Hint: the next one may be easiest to prove by induction on n. *)

Theorem add_le_cases : forall n m p q,
    n + m <= p + q -> n <= p \/ m <= q.
Proof.
    (* FILL IN HERE *)
Admitted.

Theorem plus_le_compat_l : forall n m p,
    n <= m -> p + n <= p + m.
Proof.
    intros n m p. induction p as [|p' IHp'].
    - repeat rewrite plus_0_n. intros H. apply H.
    - intros H. 
        simpl. 
        apply n_le_m__Sn_le_Sm.
        apply IHp' in H.
        apply H.
Qed.


Theorem plus_le_compat_r : forall n m p,
    n <= m -> n + p <= m + p.
Proof.
    intros n m p H.
    rewrite (add_comm n p).
    rewrite (add_comm m p).
    apply (plus_le_compat_l _ _ _ H).
Qed.

Theorem le_plus_trans : forall n m p,
    n <= m -> n <= m + p.
Proof.
    intros n m p H.
    apply (plus_le_compat_r _ _ p) in H.
    apply (le_trans n (n + p) (m + p) (le_plus_l n p) H).
Qed.

Theorem n_lt_m__n_le_m : forall n m,
    n < m -> n <= m.
Proof.
    intros n m H.
    apply le_S in H.
    apply Sn_le_Sm__n_le_m in H.
    apply H.
Qed.

Theorem plus_lt : forall n1 n2 m,
    n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
    intros n1 n2 m H. split.
    - apply (le_trans (S n1) (S (n1 + n2)) m (le_plus_l (S n1) n2) H).
    - rewrite add_comm in H.
        apply (le_trans (S n2) (S (n2 + n1)) m (le_plus_l (S n2) n1) H).
Qed.

Theorem leb_complete : forall n m,
    n <=? m = true -> n <= m.
Proof.
    intros n. induction n as [|n' IHn'].
    - intros m _. apply O_le_n.
    - intros m H. 
        destruct m.
            discriminate H.
        simpl in H.
        apply IHn' in H.
        apply n_le_m__Sn_le_Sm.
        apply H.
Qed.

(* Hint: The next one may be easiest to prove by induction on m. *)

Theorem leb_correct : forall n m,
    n <= m -> n <=? m = true.
Proof.
    intros n. induction n as [|n' IHn'].
        reflexivity.
    intros m H.
    destruct m as [|m'].
        inversion H.
    simpl.
    apply Sn_le_Sm__n_le_m in H.
    apply IHn' in H.
    apply H.
Qed.
    

(* Hint: The next one can easily be proved without using induction. *)

Theorem leb_true_trans : forall n m o,
    n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
    intros n m o Leb_nm Leb_mo.
    apply leb_complete in Leb_nm as Le_nm.
    apply leb_complete in Leb_mo as Le_mo.
    apply (le_trans _ _ _ Le_nm) in Le_mo as Le_no.
    apply leb_correct in Le_no as Leb_no.
    apply Leb_no.
Qed.

(* Exercise: 2 stars, standard, optional (leb_iff) *)

Theorem leb_iff : forall n m,
    n <=? m = true <-> n <= m.
Proof.
    intros n m. split.
    apply leb_complete.
    apply leb_correct.
Qed.

(* Exercise: 2 stars, advanced (subsequence)

A list is a subsequence of another list if all of the elements in the first list
occur in the same order in the second list, possibly with some extra elements in
between. For example,

      [1;2;3]

is a subsequence of each of the lists

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

but it is not a subsequence of any of the lists

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

Define an inductive proposition subseq on list nat that captures what it means to be
a subsequence. (Hint: You'll need three cases.)
Prove subseq_refl that subsequence is reflexive, that is, any list is a subsequence of itself.
Prove subseq_app that for any lists l1, l2, and l3, if l1 is a subsequence of l2, then l1 
is also a subsequence of l2 ++ l3.
(Optional, harder) Prove subseq_trans that subsequence is transitive -- that is, if l1 is 
a subsequence of l2 and l2 is a subsequence of l3, then l1 is a subsequence of l3. Hint: choose
your induction carefully!

*)

Inductive subseq : list nat -> list nat -> Prop :=
    | SubseqNil l: subseq [] l
    | SubseqHead n l : subseq [n] (n :: l)
    | SubseqApp l1 l2 l3 l4 (E1 : subseq l1 l2) (E2 : subseq l3 l4) : subseq (l1 ++ l3) (l2 ++ l4)
    . 

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
    intro l. induction l as [|h t IHt].
        apply SubseqNil.
    remember (SubseqHead h []) as sseq_hh.
    apply (SubseqApp [h] [h] t t sseq_hh IHt).
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
    subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
    intros l1 l2 l3 Hl1l2.
    rewrite <- (app_nil_r nat l1).
    apply (SubseqApp l1 l2 [] l3 Hl1l2 (SubseqNil l3)).
Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
    subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
    (* FILL IN HERE *)
Admitted.

Inductive reg_exp (T : Type) : Type :=
    | EmptySet
    | EmptyStr
    | Char (t : T)
    | App (r1 r2 : reg_exp T)
    | Union (r1 r2 : reg_exp T)
    | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
    | MEmpty : [] =~ EmptyStr
    | MChar x : [x] =~ (Char x)
    | MApp s1 re1 s2 re2
                (H1 : s1 =~ re1)
                (H2 : s2 =~ re2)
            : (s1 ++ s2) =~ (App re1 re2)
    | MUnionL s1 re1 re2 (H1 : s1 =~ re1) : s1 =~ (Union re1 re2)
    | MUnionR re1 s2 re2 (H2 : s2 =~ re2) : s2 =~ (Union re1 re2)
    | MStar0 re : [] =~ (Star re)
    | MStarApp s1 s2 re
                (H1 : s1 =~ re)
                (H2 : s2 =~ (Star re))
            : (s1 ++ s2) =~ (Star re)
    where "s =~ re" := (exp_match s re).

Fixpoint reg_exp_of_list {T} (l : list T) :=
    match l with
    | [] => EmptyStr
    | x :: l' => App (Char x) (reg_exp_of_list l')
    end.

Lemma MStar1: forall T s (re : reg_exp T),
    s =~ re -> s =~ Star re.
Proof.
    intros T s re H.
    rewrite <- (app_nil_r _ s).
    apply MStarApp.
        apply H.
    apply MStar0.
Qed.

(* Exercise: 3 stars, standard (exp_match_ex1)

The following lemmas show that the informal matching rules given at the beginning
of the chapter can be obtained from the formal inductive definition. *)

Lemma empty_is_empty : forall T (s : list T),
    ~(s =~ EmptySet).
Proof.
    intros T s H. inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
    s =~ re1 \/ s =~ re2 -> s =~ Union re1 re2.
Proof.
    intros T s re1 re2 [Hre1 | Hre2].
        apply (MUnionL s re1 re2 Hre1).
    apply (MUnionR re1 s re2 Hre2).
Qed.

(* The next lemma is stated in terms of the fold function from the Poly chapter: 

If ss : list (list T) represents a sequence of strings s1, ..., sn, then fold app ss [] 
is the result of concatenating them all together. *)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
    (forall s, In s ss -> s =~ re) -> fold app ss [] =~ Star re.
Proof.
    intros T ss re. induction ss as [|s ss' IHss'].
        intros H. apply MStar0.
    simpl.
    intros H.

    (* First, prove that the first element matches the regex. *)
    assert (s =~ re) as s_re.
        pose (seqs_sinss_s_re := (H s)).
        simpl in seqs_sinss_s_re.
        assert (s = s) as s_eq_s. reflexivity.
        apply (or_introl) with (B := (In s ss')) in s_eq_s.
        apply seqs_sinss_s_re in s_eq_s as s_re.
        apply s_re.
    
    (* Now, prove that the remaining elements matches the regex. *)
    assert (fold app ss' [] =~ Star re) as ss'_re.
        assert (forall k, In k ss' -> k =~ re) as IHss_hip.
            intros k Inkss'.
            apply (or_intror) with (A := (s = k)) in Inkss'.
            apply H in Inkss'.
            apply Inkss'.
        apply IHss' in IHss_hip as goal.
        apply goal.
    
    apply (MStarApp s (fold app ss' []) re s_re ss'_re).
Qed.

(* Exercise: 4 stars, standard, optional (reg_exp_of_list_spec)

Prove that reg_exp_of_list satisfies the following specification: *)

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
    s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
    intros T s1 s2. split.
    
    (* -> *)
    generalize dependent s1.
    induction s2 as [|h t IHt].
        intros s1 s1_matches_list_s2. 
        inversion s1_matches_list_s2. 
        reflexivity.
    intros m s1_matches_list_ht.
    inversion s1_matches_list_ht.
    inversion H0.
    apply IHt in H3.
    rewrite H3.
    reflexivity.

    (* <- *)
    generalize dependent s1.
    induction s2 as [|h t IHt].
        intros s1 H. rewrite H. apply MEmpty.
    intros s1 s1_eq_ht. rewrite s1_eq_ht.
    assert (t =~ reg_exp_of_list t) as t_matches_list_t.
        apply (IHt t). reflexivity.
    simpl.
    apply (MApp [h] (Char h) 
                t (reg_exp_of_list t)
                (MChar h)
                t_matches_list_t).
Qed.

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
    s1 =~ Star re ->  s2 =~ Star re -> s1 ++ s2 =~ Star re.
Proof.
    intros T s1 s2 re H1.
    remember (Star re) as re'.
    generalize dependent s2.
    induction H1
      as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
          |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
          |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
    - (* MEmpty *) discriminate.
    - (* MChar *) discriminate.
    - (* MApp *) discriminate.
    - (* MUnionL *) discriminate.
    - (* MUnionR *) discriminate.
    - (* MStar0 *)
        injection Heqre' as Heqre''. intros s H. apply H.
    - (* MStarApp *)
        injection Heqre' as Heqre''.
        intros s2 H1. rewrite <- app_assoc.
        apply MStarApp.
        + apply Hmatch1.
        + apply IH2.
            * rewrite Heqre''. reflexivity.
            * apply H1.
Qed.

(* Exercise: 4 stars, standard (re_not_empty)

Write a recursive function re_not_empty that tests whether a regular 
expression matches some string. Prove that your function is correct. *)

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
    match re with
    | EmptySet => false
    | EmptyStr => true
    | Char _ => true
    | Star r => true
    | App r1 r2 => re_not_empty r1 && re_not_empty r2
    | Union r1 r2 => re_not_empty r1 || re_not_empty r2
    end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
    (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
    intros T re. split.

    - (* -> *)
    intros exists_match.
    inversion exists_match.
    induction H
        as [| x
            | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
            | s1 re1 re2 Hmatch IH
            | re1 s2 re2 Hmatch IH
            | re
            | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
        all: try reflexivity.
        + (* MApp *)
            assert (re_not_empty re1 = true) as re1_not_empty.
                apply IH1. exists s1. apply Hmatch1.
            assert (re_not_empty re2 = true) as re2_not_empty.
                apply IH2. exists s2. apply Hmatch2.
            simpl.
            rewrite re1_not_empty, re2_not_empty.
            reflexivity.
        + (* MUnionL *)
            assert (re_not_empty re1 = true) as re1_not_empty.
                apply IH. exists s1. apply Hmatch.
            simpl.
            rewrite re1_not_empty.
            reflexivity.
        + (* MUnionR *)
            assert (re_not_empty re2 = true) as re2_not_empty.
                apply IH. exists s2. apply Hmatch.
            simpl.
            rewrite re2_not_empty.
            apply orb_true_iff.
            right. reflexivity.

    - (* <- *)
        intros re_not_empty'.
        induction re
            as [|
                | x
                | re1 IH1 re2 IH2
                | re1 IH1 re2 IH2
                | re IH].
            + (* EmptySet *)
                discriminate.
            + (* EmptyStr *)
                exists []. apply MEmpty.
            + (* Char *)
                exists [x]. apply (MChar x).
            + (* App *)
                inversion re_not_empty'.
                apply andb_true_iff in H0.
                destruct H0 as [re1_not_empty re2_not_empty].
                apply IH1 in re1_not_empty as H1.
                apply IH2 in re2_not_empty as H2.
                destruct H1 as [s1 H1].
                destruct H2 as [s2 H2].
                exists (s1 ++ s2).
                apply (MApp s1 re1 s2 re2 H1 H2).
            + (* Union *)
                inversion re_not_empty'.
                apply orb_true_iff in H0.
                destruct H0 as [H1|H2].
                * apply IH1 in H1.
                    destruct H1 as [s1 H1].
                    exists s1.
                    apply (MUnionL s1 re1 re2 H1).
                * apply IH2 in H2.
                    destruct H2 as [s2 H2].
                    exists s2.
                    apply (MUnionR re1 s2 re2 H2).
            + (* Star *)
                exists [].
                apply MStar0.
Qed.

(* Exercise: 4 stars, standard, optional (exp_match_ex2)

The MStar'' lemma below (combined with its converse, the MStar' 
exercise above), shows that our definition of exp_match for Star
is equivalent to the informal one given previously. *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
    s =~ Star re ->
    exists ss : list (list T),
        s = fold app ss []
        /\ forall s', In s' ss -> s' =~ re.
Proof.
    intros T s re s_matches_star_re.
    remember (Star re) as re''.
    induction s_matches_star_re
        as [| x
            | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
            | s1 re1 re2 Hmatch IH
            | re1 s2 re2 Hmatch IH
            | re'
            | s1 s2 re'' Hmatch1 IH1 Hmatch2 IH2].
    all: inversion Heqre''.
    - exists []. simpl. split. reflexivity.
        intros s H. contradiction.
    - admit.
Admitted.

(* Exercise: 5 stars, advanced (weak_pumping)

One of the first really interesting theorems in the theory of regular expressions 
is the so-called pumping lemma, which states, informally, that any sufficiently 
long string s matching a regular expression re can be "pumped" by repeating some 
middle section of s an arbitrary number of times to produce a new string also matching
re. (For the sake of simplicity in this exercise, we consider a slightly weaker theorem 
than is usually stated in courses on automata theory.)

To get started, we need to define "sufficiently long." Since we are working in a constructive
logic, we actually need to be able to calculate, for each regular expression re, the minimum 
length for strings s to guarantee "pumpability." *)

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
    match re with
    | EmptySet => 1
    | EmptyStr => 1
    | Char _ => 2
    | App re1 re2 =>
        pumping_constant re1 + pumping_constant re2
    | Union re1 re2 =>
        pumping_constant re1 + pumping_constant re2
    | Star r => pumping_constant r
    end.

(* You may find these lemmas about the pumping constant useful when proving the pumping lemma below. *)

Lemma pumping_constant_ge_1 : forall T (re : reg_exp T),
    pumping_constant re >= 1.
Proof.
    intros T re. induction re.
    - (* EmptySet *)
        apply le_n.
    - (* EmptyStr *)
        apply le_n.
    - (* Char *)
        apply le_S. apply le_n.
    - (* App *)
        simpl.
        apply le_trans with (n:=pumping_constant re1).
        apply IHre1. apply le_plus_l.
    - (* Union *)
        simpl.
        apply le_trans with (n:=pumping_constant re1).
        apply IHre1. apply le_plus_l.
    - (* Star *)
        simpl. apply IHre.
Qed.
    

Lemma pumping_constant_0_false : forall T (re : reg_exp T),
    pumping_constant re = 0 -> False.
Proof.
    intros T re H.
    assert (Hp1 : pumping_constant re >= 1).
    { apply pumping_constant_ge_1. }
    inversion Hp1 as [Hp1'| p Hp1' Hp1''].
    - rewrite H in Hp1'. discriminate Hp1'.
    - rewrite H in Hp1''. discriminate Hp1''.
Qed.

(* Next, it is useful to define an auxiliary function that repeats a string (appends it to itself) 
some number of times. *)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
    match n with
    | 0 => []
    | S n' => l ++ napp n' l
    end.

(* This auxiliary lemma might also be useful in your proof of the pumping lemma. *)

Lemma napp_plus: forall T (n m : nat) (l : list T),
    napp (n + m) l = napp n l ++ napp m l.
Proof.
    intros T n m l.
    induction n as [|n IHn].
    - reflexivity.
    - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma napp_star : forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re -> napp m s1 ++ s2 =~ Star re.
Proof.
    intros T m s1 s2 re Hs1 Hs2.
    induction m.
    - simpl. apply Hs2.
    - simpl. rewrite <- app_assoc.
        apply MStarApp.
        + apply Hs1.
        + apply IHm.
Qed.

(* The (weak) pumping lemma itself says that, if s =~ re and if the length of s is at least the 
pumping constant of re, then s can be split into three substrings s1 ++ s2 ++ s3 in such a way 
that s2 can be repeated any number of times and the result, when combined with s1 and s3 will 
still match re. Since s2 is also guaranteed not to be the empty string, this gives us a 
(constructive!) way to generate strings matching re that are as long as we like. *)

Lemma weak_pumping : forall T (re : reg_exp T) s,
    s =~ re ->
    pumping_constant re <= length s ->
    exists s1 s2 s3,
        s = s1 ++ s2 ++ s3 /\
        s2 <> [] /\
        forall m, s1 ++ napp m s2 ++ s3 =~ re.

(* You are to fill in the proof. Several of the lemmas about le that were in an optional exercise
earlier in this chapter may be useful. *)

Proof.
    intros T re s Hmatch.
    induction Hmatch
        as [| x 
            | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
            | s1 re1 re2 Hmatch IH 
            | re1 s2 re2 Hmatch IH
            | re 
            | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
    - (* MEmpty *)
        simpl. intros contra. inversion contra.
    - (* MChar *) 
        simpl. intros contra. apply Sn_le_Sm__n_le_m in contra. inversion contra.
    - (* MApp *)
        simpl. intros H.
        rewrite app_length in H.
        apply add_le_cases in H as [H1 | H2].
        
        (* H1 *)
        apply IH1 in H1 as [s2' [s3 [s4 [s1_eq_s2_s3_s4 [s3_ne_nil forall_m]]]]].
        exists s2', s3, (s4 ++ s2).
        rewrite s1_eq_s2_s3_s4.

        split. do 3 rewrite app_assoc. reflexivity.
        split. apply s3_ne_nil.

        intros m.
        rewrite app_assoc.
        rewrite (app_assoc _ (s2' ++ napp m s3) s4 s2).
        rewrite <- (app_assoc _ s2' (napp m s3) s4).
        apply (MApp (s2' ++ napp m s3 ++ s4) re1 
                    s2 re2
                    (forall_m m)
                    Hmatch2).

        (* H2 *)
        apply IH2 in H2 as [s1' [s3 [s4 [s2_eq_s1_s3_s4 [s3_ne_nil forall_m]]]]].
        exists (s1 ++ s1'), s3, s4.
        rewrite s2_eq_s1_s3_s4.
       
        split. rewrite <- app_assoc. reflexivity.
        split. apply s3_ne_nil.

        intros m.
        rewrite <- app_assoc.
        apply (MApp s1 re1
                    (s1' ++ napp m s3 ++ s4) re2
                    Hmatch1
                    (forall_m m)).
    - (* MUnionL *)
        simpl. intros H.
        apply plus_le in H as [H1 H2].
        apply IH in H1 as [s2 [s3 [s4 [s1_eq_s2_s3_s4 [s3_ne_nil forall_m]]]]].
        exists s2, s3, s4.

        split. apply s1_eq_s2_s3_s4.
        split. apply s3_ne_nil.
        
        intros m.
        apply (MUnionL (s2 ++ napp m s3 ++ s4) re1 re2 (forall_m m)).
    - (* MUnionR *)
        simpl. intros H.
        apply plus_le in H as [H1 H2].
        apply IH in H2 as [s1 [s3 [s4 [s2_eq_s1_s3_s4 [s3_ne_nil forall_m]]]]].
        exists s1, s3, s4.

        split. apply s2_eq_s1_s3_s4.
        split. apply s3_ne_nil.

        intros m.
        apply (MUnionR re1 (s1 ++ napp m s3 ++ s4) re2 (forall_m m)).
    - (* MStar0 *)
        simpl. intros H. inversion H. 
        apply pumping_constant_0_false in H1.
        contradiction.
    - (* MStarApp *)
        simpl. intros H. rewrite app_length in H.
        induction re
            as [|
                | x
                | re1 IHre1 re2 IHre2
                | re1 IHre1 re2 IHre2
                | re IHre].
        + (* EmptySet *)
            apply empty_is_empty in Hmatch1.
            contradiction.
        + (* EmptyStr *)
            inversion Hmatch1.

            assert (@pumping_constant T (Star EmptyStr) <= length s2) as pc_length_s2.
                rewrite <- H0 in H. simpl in H.
                simpl. apply H.

            apply IH2 in pc_length_s2
                as [s1' [s3 [s4 [s2_eq_s1_s3_s4 [s3_ne_nil forall_m]]]]].
            exists s1', s3, s4.

            split. apply s2_eq_s1_s3_s4.
            split. apply s3_ne_nil.
            apply forall_m.
        + (* Char *)
            inversion Hmatch1.
            
            assert (s2 <> []) as s2_ne_nil.
                rewrite <- H0 in H. simpl in H. apply Sn_le_Sm__n_le_m in H.
                destruct s2.
                    apply leb_iff in H. discriminate H.
                unfold not. intros contra. discriminate contra.

            exists [x], s2, []. simpl.

            split. rewrite app_nil_r. reflexivity.
            split. apply s2_ne_nil.

            intros m.
            admit.
        + (* App *)
            admit.
        + (* Union *)
            admit.
        + (* Star *)
            admit.
Admitted.

End Pumping.

(* We've seen in the Logic chapter that we often need to relate boolean computations to statements
 in Prop. But performing this conversion as we did it there can result in tedious proof scripts.
 Consider the proof of the following theorem: *)

Theorem filter_not_empty_In : forall n l,
    filter (fun x => n =? x) l <> [] -> In n l.
Proof.
    intros n l. induction l as [|m l' IHl'].
    - (* l =  *)
        simpl. intros H. apply H. reflexivity.
    - (* l = m :: l' *)
        simpl. destruct (n =? m) eqn:H.
        + (* n =? m = true *)
        intros _. rewrite eqb_eq in H. rewrite H.
        left. reflexivity.
        + (* n =? m = false *)
        intros H'. right. apply IHl'. apply H'.
Qed.

(* In the first branch after destruct, we explicitly apply the eqb_eq lemma to the equation
generated by destructing n =? m, to convert the assumption n =? m = true into the assumption n = m;
then we had to rewrite using this assumption to complete the case.

We can streamline this by defining an inductive proposition that yields a better case-analysis 
principle for n =? m. Instead of generating an equation such as (n =? m) = true, which is generally
not directly useful, this principle gives us right away the assumption we really need: n = m.

Following the terminology introduced in Logic, we call this the "reflection principle for equality
(between numbers)," and we say that the boolean n =? m is reflected in the proposition n = m. *)

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H : P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.

(* The reflect property takes two arguments: a proposition P and a boolean b. Intuitively, it states
that the property P is reflected in (i.e., equivalent to) the boolean b: that is, P holds if and only
if b = true. To see this, notice that, by definition, the only way we can produce evidence for reflect
P true is by showing P and then using the ReflectT constructor. If we invert this statement, this means
that it should be possible to extract evidence for P from a proof of reflect P true. Similarly, the only
way to show reflect P false is by combining evidence for ¬ P with the ReflectF constructor.

To put this observation to work, we first prove that the statements P ↔ b = true and reflect P b are 
indeed equivalent. First, the left-to-right implication: *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
    (* WORKED IN CLASS *)
    intros P b H. destruct b eqn:Eb.
    - apply ReflectT. rewrite H. reflexivity.
    - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

(* Now you prove the right-to-left implication: *)

(* Exercise: 2 stars, standard, especially useful (reflect_iff) *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
    intros P b [PTrue | PFalse].
    - split. intros _. reflexivity. intros _. apply PTrue.
    - split. 
        intros p. apply PFalse in p. contradiction.
        intros contra. discriminate contra.
Qed.

(* The advantage of reflect over the normal "if and only if" connective is that, by destructing a
hypothesis or lemma of the form reflect P b, we can perform case analysis on b while at the same
time generating appropriate hypothesis in the two branches (P in the first subgoal and ¬ P in the
second). *)

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
    intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

(* A smoother proof of filter_not_empty_In now goes as follows. Notice how the calls to destruct
and rewrite are combined into a single call to destruct.

(To see this clearly, look at the two proofs of filter_not_empty_In with Coq and observe the
differences in proof state at the beginning of the first case of the destruct.) *)

Theorem filter_not_empty_In' : forall n l,
    filter (fun x => n =? x) l <> [] -> In n l.
Proof.
    intros n l. induction l as [|m l' IHl'].
    - (* l =  *)
        simpl. intros H. apply H. reflexivity.
    - (* l = m :: l' *)
        simpl. destruct (eqbP n m) as [H | H].
        + (* n = m *)
        intros _. rewrite H. left. reflexivity.
        + (* n <> m *)
        intros H'. right. apply IHl'. apply H'.
Qed.

(* Exercise: 3 stars, standard, especially useful (eqbP_practice)

Use eqbP as above to prove the following: *)

Fixpoint count n l :=
    match l with
    | [] => 0
    | m :: l' => (if n =? m then 1 else 0) + count n l'
    end.

Theorem eqbP_practice : forall n l,
    count n l = 0 -> ~(In n l).
Proof.
    intros n l count_n_l_zero.
    induction l as [|h t IHt].
    - (* l = [] *) 
        simpl. intros False. apply False.
    - (* l = h :: t*) 
        simpl. destruct (eqbP h n) as [h_eq_n | h_ne_n].
        + (* h = n *) 
            rewrite h_eq_n in count_n_l_zero. simpl in count_n_l_zero.
            rewrite eqb_refl in count_n_l_zero.
            discriminate count_n_l_zero.
        + (* h <> n *)
            apply eqb_neq in h_ne_n. rewrite eqb_sym in h_ne_n.
            simpl in count_n_l_zero. rewrite h_ne_n in count_n_l_zero. simpl in count_n_l_zero.
            apply IHt in count_n_l_zero as n_not_in_t.
            intros [h_eq_n | n_in_t ].
                rewrite h_eq_n in h_ne_n. rewrite eqb_refl in h_ne_n. discriminate h_ne_n.
             apply n_not_in_t in n_in_t. contradiction.
Qed.


(* This small example shows reflection giving us a small gain in convenience; in larger developments,
using reflect consistently can often lead to noticeably shorter and clearer proof scripts. We'll see
many more examples in later chapters and in Programming Language Foundations.

The use of the reflect property has been popularized by SSReflect, a Coq library that has been used to
formalize important results in mathematics, including as the 4-color theorem and the Feit-Thompson
theorem. The name SSReflect stands for small-scale reflection, i.e., the pervasive use of reflection
to simplify small proof steps with boolean computations. *)

(* Exercise: 3 stars, standard, especially useful (nostutter_defn)

Formulating inductive definitions of properties is an important skill you'll need in this course. Try
to solve this exercise without any help at all.

We say that a list "stutters" if it repeats the same element consecutively. (This is different from
not containing duplicates: the sequence [1;4;1] repeats the element 1 but does not stutter.) The
property "nostutter mylist" means that mylist does not stutter. Formulate an inductive definition
for nostutter. *)

Inductive nostutter {X:Type} : list X -> Prop :=
    | NoStutterNil : nostutter []
    | NoStutterHead h : nostutter [h]
    | NoStutterCons x h l (H1 : x <> h) (H2 : nostutter (h :: l)) : nostutter (x :: h :: l).

(* Make sure each of these tests succeeds, but feel free to change the suggested proof (in comments)
if the given one doesn't work for you. Your definition might be different from ours and still be
correct, in which case the examples might need a different proof. (You'll notice that the suggested
proofs use a number of tactics we haven't talked about, to make them more robust to different possible
ways of defining nostutter. You can probably just uncomment and use them as-is, but you can also prove
each example with more basic tactics.) *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. repeat constructor; apply eqb_neq; auto.
Qed.

Example test_nostutter_2: nostutter (@nil nat).
Proof. repeat constructor; apply eqb_neq; auto.
Qed.

Example test_nostutter_3: nostutter [5].
Proof. repeat constructor; auto. Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof. 
    intro.
    repeat match goal with
        h: nostutter _ |- _ => inversion h; clear h; subst
    end.
    contradiction; auto. 
Qed.


(* Exercise: 4 stars, advanced (filter_challenge)

Let's prove that our definition of filter from the Poly chapter matches an abstract specification.
Here is the specification, written out informally in English:

A list l is an "in-order merge" of l1 and l2 if it contains all the same elements as l1 and l2, in
the same order as l1 and l2, but possibly interleaved. For example,

    [1;4;6;2;3]

is an in-order merge of

    [1;6;2]

and

    [4;3].

Now, suppose we have a set X, a function test: X→bool, and a list l of type list X. Suppose further
that l is an in-order merge of two lists, l1 and l2, such that every item in l1 satisfies test and no
item in l2 satisfies test. Then filter test l = l1.

Translate this specification into a Coq theorem and prove it. (You'll need to begin by defining what 
it means for one list to be a merge of two others. Do this with an inductive relation, not a Fixpoint.) *)

Inductive in_order_merge {T : Type} : list T -> list T -> list T -> Prop :=
    | IOMNil : in_order_merge [] [] []
    | IOMConsL x l1 l2 l3 (H : in_order_merge l1 l2 l3)
        : in_order_merge (x :: l1) l2 (x :: l3)
    | IOMConsR l1 x l2 l3 (H : in_order_merge l1 l2 l3)
        : in_order_merge l1 (x :: l2) (x :: l3).

Theorem filter_challenge: forall X (test : X -> bool) (l l1 l2: list X),
    in_order_merge l1 l2 l ->
    (forall x, In x l1 -> test x = true) ->
    (forall y, In y l2 -> test y = false) ->
    filter test l = l1.
Proof.
    intros X test l. induction l as [|x l' IHl'].
    - (* l = [] *)
        intros l1 l2 H. inversion H.
        intros _ _. reflexivity.
    - (* l = x :: l' *)
        intros l1 l2 H all_l1_test none_l2_test. inversion H. all: subst.
        + (* x in l1 *)
            assert (test x = true) as x_test.
                apply all_l1_test. simpl. left. reflexivity.

            assert (filter test l' = l0) as l'_test_l0.
                apply (IHl' l0 l2 H3).
                intros x0 x0_in_l0.
                apply (all_l1_test x0).
                simpl. right.
                apply x0_in_l0.
                apply none_l2_test.

            simpl. 
            rewrite x_test, l'_test_l0.
            reflexivity.
        + (* x in l2 *)
            assert (test x = false) as x_test.
                apply none_l2_test. simpl. left. reflexivity.
            
            assert (filter test l' = l1) as l'_test_l1.
                apply (IHl' l1 l3 H3 all_l1_test).
                intros y y_in_l3.
                apply (none_l2_test y).
                simpl. right.
                apply y_in_l3.

            simpl.
            rewrite x_test, l'_test_l1.
            reflexivity.
Qed.

(* Exercise: 5 stars, advanced, optional (filter_challenge_2)

A different way to characterize the behavior of filter goes like this: Among all subsequences of l with
the property that test evaluates to true on all their members, filter test l is the longest. Formalize 
this claim and prove it. *)

(* FILL ME HERE *)

(* Exercise: 4 stars, standard, optional (palindromes)

A palindrome is a sequence that reads the same backwards as forwards.

    Define an inductive proposition pal on list X that captures what it means to be a palindrome. (Hint:
    You'll need three cases. Your definition should be based on the structure of the list; just having a
    single constructor like

         c : ∀ l, l = rev l → pal l
    
    may seem obvious, but will not work very well.)

    Prove (pal_app_rev) that

           ∀ l, pal (l ++ rev l).

    Prove (pal_rev that)

           ∀ l, pal l → l = rev l.
*)

Inductive palindrome {X : Type} : list X -> Prop :=
    | PNil : palindrome []
    | PElem x : palindrome [x]
    | PAdd x l (H : l = rev l) : palindrome (x :: l ++ [x])
    .

Theorem pal_app_rev: forall X (l : list X),
    palindrome (l ++ rev l).
Proof.
    intros X l. induction l as [|h t IHt].
    - (* l = [] *)
        simpl. apply PNil.
    - (* l = h :: t *)
        simpl. 
        inversion IHt.
        all: (
            rewrite app_assoc;
            apply (PAdd h (t ++ rev t));
            simpl;
            rewrite rev_app_distr;
            rewrite rev_involutive;
            reflexivity
        ).
Qed.


Theorem pal_rev: forall X (l : list X),
    palindrome l -> l = rev l.
Proof.
    intros X l l_palindrome. 
    inversion l_palindrome.
    all: reflexivity || simpl.
    rewrite rev_app_distr. simpl.
    rewrite <- H.
    reflexivity.
Qed.


(* Exercise: 5 stars, standard, optional (palindrome_converse)

Again, the converse direction is significantly more difficult, due to the lack of evidence. Using your
definition of pal from the previous exercise, prove that

     ∀ l, l = rev l → pal l.

*)

Theorem palindrome_converse: forall X (l : list X),
    l = rev l -> palindrome l.
Proof.
Admitted.


(* Exercise: 4 stars, advanced, optional (NoDup)

Recall the definition of the In property from the Logic chapter, which asserts that a value x appears
at least once in a list l:

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   |  => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

Your first task is to use In to define a proposition disjoint X l1 l2, which should be provable exactly 
when l1 and l2 are lists (with elements of type X) that have no elements in common. *)

Definition disjoint {X : Type} (l1 l2 : list X): Prop := 
    (forall x, In x l1 -> ~(In x l2)) /\ (forall x, In x l2 -> ~(In x l1)).

(* Next, use In to define an inductive proposition NoDup X l, which should be provable exactly when l is
a list (with elements of type X) where every member is different from every other. For example, 
NoDup nat [1;2;3;4] and NoDup bool [] should be provable, while NoDup nat [1;2;1] and 
NoDup bool [true;true] should not be. *)

Inductive NoDup {X : Type} : list X -> Prop :=
    | NDNil : NoDup []
    | NDCons x l (H1 : NoDup l) (H2 : ~(In x l)) : NoDup (x :: l).

(* Finally, state and prove one or more interesting theorems relating disjoint, 
NoDup and ++ (list append). *)

Theorem app_disjoint_nodup: forall X (l1 l2 : list X),
    NoDup l1 -> NoDup l2 -> disjoint l1 l2 -> NoDup (l1 ++ l2).
Proof.
    intros X l1 l2 nodup_l1 nodup_l2 [not_in_l2 not_in_l1].
    induction l1.
    + simpl. apply nodup_l2.
    + (* l1 = x :: l1 *)
        inversion nodup_l1. subst.

        assert (forall x0, In x0 l1 -> ~(In x0 l2)) as not_in_l2'.
            simpl in not_in_l2.
            intros x0 not_in_l1'.
            apply not_in_l2.
            right. 
            apply not_in_l1'.

        assert (forall x0, In x0 l2 -> ~(In x0 l1)) as not_in_l1'.
            simpl in not_in_l1.
            intros x0 not_in_l2''.
            apply not_in_l1 in not_in_l2''.
            apply de_morgan_neg_of_disj in not_in_l2'' as [x_ne_x0 not_in_l1'].
            assumption.

        assert (NoDup (l1 ++ l2)) as nodup_l1_app_l2.
            apply (IHl1 H2 not_in_l2' not_in_l1').
        
        assert (~(In x (l1 ++ l2))) as not_in_l1_app_l2.
            admit.

        simpl.
        apply (NDCons x (l1 ++ l2) nodup_l1_app_l2 not_in_l1_app_l2).
Admitted.


(* Exercise: 4 stars, advanced, optional (pigeonhole_principle)

The pigeonhole principle states a basic fact about counting: if we distribute more than n items into n 
pigeonholes, some pigeonhole must contain at least two items. As often happens, this apparently trivial 
fact about numbers requires non-trivial machinery to prove, but we now have enough...

First prove an easy and useful lemma. *)

Lemma in_split : forall (X : Type) (x : X) (l : list X),
    In x l -> exists l1 l2, l = l1 ++ x :: l2.
Proof.
    intros X x l x_in_l.
    induction l.
        contradiction. 
    simpl in x_in_l. 
    destruct x_in_l as [x_eq_x0 | x_in_l].
        exists [], l. rewrite x_eq_x0. reflexivity.
    apply IHl in x_in_l as [l1 [l2 l_eq_l1_x_l2]].
    exists (x0 :: l1), l2. simpl.
    rewrite l_eq_l1_x_l2.
    reflexivity.
Qed.


(* Now define a property repeats such that repeats X l asserts that l contains at least one repeated
element (of type X). *)

Fixpoint repeats {X : Type} (l : list X): Prop :=
    match l with
    | [] => False
    | x :: l' => In x l' \/ repeats l'
    end.

(* Now, here's a way to formalize the pigeonhole principle. Suppose list l2 represents a list of
pigeonhole labels, and list l1 represents the labels assigned to a list of items. If there are more
items than labels, at least two items must have the same label -- i.e., list l1 must contain repeats.

This proof is much easier if you use the excluded_middle hypothesis to show that In is decidable, 
i.e., ∀ x l, (In x l) ∨ ¬ (In x l). However, it is also possible to make the proof go through without
assuming that In is decidable; if you manage to do this, you will not need the excluded_middle hypothesis.
*)

Theorem pigeonhole_principle: excluded_middle -> forall (X : Type) (l1 l2 : list X),
    (forall x, In x l1 -> In x l2) -> length l2 < length l1 -> repeats l1.
Proof.
    intros EM X l1. induction l1 as [|x l1' IHl1'].
    + (* l1 = [] *)
        intros l2 x_in_l2 len_l2_le_zero.
        simpl in len_l2_le_zero.
        inversion len_l2_le_zero.
    + (* l1 = x :: l1' *)
        intros l2 x_in_l2 len_l2_le_len_l1.
        admit.
Admitted.

(* ================================================================= *)
(** ** Extended Exercise: A Verified Regular-Expression Matcher *)

(** We have now defined a match relation over regular expressions and
    polymorphic lists. We can use such a definition to manually prove that
    a given regex matches a given string, but it does not give us a
    program that we can run to determine a match automatically.

    It would be reasonable to hope that we can translate the definitions
    of the inductive rules for constructing evidence of the match relation
    into cases of a recursive function that reflects the relation by recursing
    on a given regex. However, it does not seem straightforward to define
    such a function in which the given regex is a recursion variable
    recognized by Coq. As a result, Coq will not accept that the function
    always terminates.

    Heavily-optimized regex matchers match a regex by translating a given
    regex into a state machine and determining if the state machine
    accepts a given string. However, regex matching can also be
    implemented using an algorithm that operates purely on strings and
    regexes without defining and maintaining additional datatypes, such as
    state machines. We'll implement such an algorithm, and verify that
    its value reflects the match relation. *)

(** We will implement a regex matcher that matches strings represented
    as lists of ASCII characters: *)
Require Import Coq.Strings.Ascii.

Definition string := list ascii.

(** The Coq standard library contains a distinct inductive definition
    of strings of ASCII characters. However, we will use the above
    definition of strings as lists as ASCII characters in order to apply
    the existing definition of the match relation.

    We could also define a regex matcher over polymorphic lists, not lists
    of ASCII characters specifically. The matching algorithm that we will
    implement needs to be able to test equality of elements in a given
    list, and thus needs to be given an equality-testing
    function. Generalizing the definitions, theorems, and proofs that we
    define for such a setting is a bit tedious, but workable. *)

(** The proof of correctness of the regex matcher will combine
    properties of the regex-matching function with properties of the
    [match] relation that do not depend on the matching function. We'll go
    ahead and prove the latter class of properties now. Most of them have
    straightforward proofs, which have been given to you, although there
    are a few key lemmas that are left for you to prove. *)

(** Each provable [Prop] is equivalent to [True]. *)
Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
    intros.
    split.
    - intros. constructor.
    - intros _. apply H.
Qed.

(** Each [Prop] whose negation is provable is equivalent to [False]. *)
Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
    intros.
    split.
    - apply H.
    - intros. destruct H0.
Qed.

(** [EmptySet] matches no string. *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
    intros.
    apply not_equiv_false.
    unfold not. intros. inversion H.
Qed.

(** [EmptyStr] only matches the empty string. *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [].
Proof.
    split.
    - intros. inversion H. reflexivity.
    - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] matches no non-empty string. *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
    intros.
    apply not_equiv_false.
    unfold not. intros. inversion H.
Qed.

(** [Char a] matches no string that starts with a non-[a] character. *)
Lemma char_nomatch_char :
    forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
    intros.
    apply not_equiv_false.
    unfold not.
    intros.
    apply H.
    inversion H0.
    reflexivity.
Qed.

(** If [Char a] matches a non-empty string, then the string's tail is empty. *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [].
Proof.
    split.
    - intros. inversion H. reflexivity.
    - intros. rewrite H. apply MChar.
Qed.

(** [App re0 re1] matches string [s] iff [s = s0 ++ s1], where [s0]
    matches [re0] and [s1] matches [re1]. *)
Lemma app_exists : forall (s : string) re0 re1,
    s =~ App re0 re1 <->
    exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
    intros.
    split.
    - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
    - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(** **** Exercise: 3 stars, standard, optional (app_ne)

    [App re0 re1] matches [a::s] iff [re0] matches the empty string
    and [a::s] matches [re1] or [s=s0++s1], where [a::s0] matches [re0]
    and [s1] matches [re1].

    Even though this is a property of purely the match relation, it is a
    critical observation behind the design of our regex matcher. So (1)
    take time to understand it, (2) prove it, and (3) look for how you'll
    use it later. *)
Lemma app_ne : forall (a : ascii) s re0 re1,
    a :: s =~ (App re0 re1) <->
    ([] =~ re0 /\ a :: s =~ re1) \/
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
    (* FILL IN HERE *) Admitted.
(** [] *)

(** [s] matches [Union re0 re1] iff [s] matches [re0] or [s] matches [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
    s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
    intros. split.
    - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
    - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

(** **** Exercise: 3 stars, standard, optional (star_ne)

    [a::s] matches [Star re] iff [s = s0 ++ s1], where [a::s0] matches
    [re] and [s1] matches [Star re]. Like [app_ne], this observation is
    critical, so understand it, prove it, and keep it in mind.

    Hint: you'll need to perform induction. There are quite a few
    reasonable candidates for [Prop]'s to prove by induction. The only one
    that will work is splitting the [iff] into two implications and
    proving one by induction on the evidence for [a :: s =~ Star re]. The
    other implication can be proved without induction.

    In order to prove the right property by induction, you'll need to
    rephrase [a :: s =~ Star re] to be a [Prop] over general variables,
    using the [remember] tactic.  *)

Lemma star_ne : forall (a : ascii) s re,
    a :: s =~ Star re <->
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
    (* FILL IN HERE *) Admitted.
(** [] *)

(** The definition of our regex matcher will include two fixpoint
    functions. The first function, given regex [re], will evaluate to a
    value that reflects whether [re] matches the empty string. The
    function will satisfy the following property: *)
Definition refl_matches_eps m :=
    forall re : reg_exp ascii, reflect ([] =~ re) (m re).

(** **** Exercise: 2 stars, standard, optional (match_eps)

    Complete the definition of [match_eps] so that it tests if a given
    regex matches the empty string: *)
Fixpoint match_eps (re: reg_exp ascii) : bool
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (match_eps_refl)

    Now, prove that [match_eps] indeed tests if a given regex matches
    the empty string.  (Hint: You'll want to use the reflection lemmas
    [ReflectT] and [ReflectF].) *)
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
    (* FILL IN HERE *) Admitted.
(** [] *)

(** We'll define other functions that use [match_eps]. However, the
    only property of [match_eps] that you'll need to use in all proofs
    over these functions is [match_eps_refl]. *)

(** The key operation that will be performed by our regex matcher will
    be to iteratively construct a sequence of regex derivatives. For each
    character [a] and regex [re], the derivative of [re] on [a] is a regex
    that matches all suffixes of strings matched by [re] that start with
    [a]. I.e., [re'] is a derivative of [re] on [a] if they satisfy the
    following relation: *)

Definition is_der re (a : ascii) re' :=
    forall s, a :: s =~ re <-> s =~ re'.

(** A function [d] derives strings if, given character [a] and regex
    [re], it evaluates to the derivative of [re] on [a]. I.e., [d]
    satisfies the following property: *)
Definition derives d := forall a re, is_der re a (d a re).

(** **** Exercise: 3 stars, standard, optional (derive)

    Define [derive] so that it derives strings. One natural
    implementation uses [match_eps] in some cases to determine if key
    regex's match the empty string. *)
Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** The [derive] function should pass the following tests. Each test
    establishes an equality between an expression that will be
    evaluated by our regex matcher and the final value that must be
    returned by the regex matcher. Each test is annotated with the
    match fact that it reflects. *)
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(** "c" =~ EmptySet: *)
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof.
    (* FILL IN HERE *) Admitted.

(** "c" =~ Char c: *)
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof.
    (* FILL IN HERE *) Admitted.

(** "c" =~ Char d: *)
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof.
    (* FILL IN HERE *) Admitted.

(** "c" =~ App (Char c) EmptyStr: *)
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof.
    (* FILL IN HERE *) Admitted.

(** "c" =~ App EmptyStr (Char c): *)
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof.
    (* FILL IN HERE *) Admitted.

(** "c" =~ Star c: *)
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof.
    (* FILL IN HERE *) Admitted.

(** "cd" =~ App (Char c) (Char d): *)
Example test_der6 :
    match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof.
    (* FILL IN HERE *) Admitted.

(** "cd" =~ App (Char d) (Char c): *)
Example test_der7 :
    match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof.
    (* FILL IN HERE *) Admitted.

(** **** Exercise: 4 stars, standard, optional (derive_corr)

    Prove that [derive] in fact always derives strings.

    Hint: one proof performs induction on [re], although you'll need
    to carefully choose the property that you prove by induction by
    generalizing the appropriate terms.

    Hint: if your definition of [derive] applies [match_eps] to a
    particular regex [re], then a natural proof will apply
    [match_eps_refl] to [re] and destruct the result to generate cases
    with assumptions that the [re] does or does not match the empty
    string.

    Hint: You can save quite a bit of work by using lemmas proved
    above. In particular, to prove many cases of the induction, you
    can rewrite a [Prop] over a complicated regex (e.g., [s =~ Union
    re0 re1]) to a Boolean combination of [Prop]'s over simple
    regex's (e.g., [s =~ re0 \/ s =~ re1]) using lemmas given above
    that are logical equivalences. You can then reason about these
    [Prop]'s naturally using [intro] and [destruct]. *)
Lemma derive_corr : derives derive.
Proof.
    (* FILL IN HERE *) Admitted.
(** [] *)

(** We'll define the regex matcher using [derive]. However, the only
    property of [derive] that you'll need to use in all proofs of
    properties of the matcher is [derive_corr]. *)

(** A function [m] matches regexes if, given string [s] and regex [re],
    it evaluates to a value that reflects whether [s] is matched by
    [re]. I.e., [m] holds the following property: *)
Definition matches_regex m : Prop :=
    forall (s : string) re, reflect (s =~ re) (m s re).

(** **** Exercise: 2 stars, standard, optional (regex_match)

    Complete the definition of [regex_match] so that it matches
    regexes. *)
Fixpoint regex_match (s : string) (re : reg_exp ascii) : bool
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (regex_refl)

    Finally, prove that [regex_match] in fact matches regexes.

    Hint: if your definition of [regex_match] applies [match_eps] to
    regex [re], then a natural proof applies [match_eps_refl] to [re]
    and destructs the result to generate cases in which you may assume
    that [re] does or does not match the empty string.

    Hint: if your definition of [regex_match] applies [derive] to
    character [x] and regex [re], then a natural proof applies
    [derive_corr] to [x] and [re] to prove that [x :: s =~ re] given
    [s =~ derive x re], and vice versa. *)
Theorem regex_refl : matches_regex regex_match.
Proof.
    (* FILL IN HERE *) Admitted.
(** [] *)

    (* 2021-08-11 15:08 *)