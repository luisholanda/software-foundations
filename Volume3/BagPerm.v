(** * BagPerm:  Insertion Sort With Bags *)

(** We have seen how to specify algorithms on "collections", such as
    sorting algorithms, using [Permutation]s.  Instead of using
    permutations, another way to specify these algorithms is to use
    _bags_ (also called _multisets_), which we introduced in [Lists].
    A _set_ of values is like a list with no repeats where
    the order does not matter.  A _multiset_ is like a list, possibly
    with repeats, where the order does not matter.  Whereas the principal
    query on a set is whether a given element appears in it, the
    principal query on a bag is _how many_ times a given element appears 
    in it. *)

From Coq Require Import Strings.String. (* for manual grading *)
From Coq Require Import Setoid Morphisms.
From VFA Require Import Perm.
From VFA Require Import Sort.

(** To keep this chapter more self-contained, 
we restate the critical definitions from [Lists].  *)
Definition bag := list nat.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t =>
      (if h =? v then 1 else 0) + count v t
  end.

(** We will say two bags are _equivalent_ if they have the same number
    of copies of every possible element. *)

Definition bag_eqv (b1 b2: bag) : Prop :=
  forall n, count n b1 = count n b2. 

(** **** Exercise: 2 stars, standard (bag_eqv_properties) *)

(* It is easy to prove [bag_eqv] is an equivalence relation. *)

Lemma bag_eqv_refl : forall b, bag_eqv b b.
Proof.
  unfold bag_eqv. intros. reflexivity.
Qed.

Lemma bag_eqv_sym: forall b1 b2, bag_eqv b1 b2 -> bag_eqv b2 b1. 
Proof.
  unfold bag_eqv. intros.
  specialize H with n.
  symmetry.
  assumption.
Qed.

Lemma bag_eqv_trans: forall b1 b2 b3,
  bag_eqv b1 b2 -> bag_eqv b2 b3 -> bag_eqv b1 b3.
Proof.
  unfold bag_eqv. intros.
  specialize H with n.
  specialize H0 with n.
  transitivity (count n b2);
  assumption.
Qed.

(** The following little lemma is handy in a couple of places. *)

Lemma bag_eqv_cons : forall x b1 b2,
  bag_eqv b1 b2 -> bag_eqv (x::b1) (x::b2).
Proof.
  unfold bag_eqv. intros.
  specialize H with n.
  simpl. rewrite H.
  reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Correctness *)

(** A sorting algorithm must rearrange the elements into a list that
    is totally ordered.  But let's say that a different way: the
    algorithm must produce a list _with the same multiset of values_,
    and this list must be totally ordered. *)

Definition is_a_sorting_algorithm' (f: list nat -> list nat) :=
  forall al, bag_eqv al (f al) /\ sorted (f al).

(** **** Exercise: 3 stars, standard (insert_bag)

    First, prove the auxiliary lemma [insert_bag], which will be
    useful for proving [sort_bag] below.  Your proof will be by
    induction.  *)

Lemma insert_bag: forall x l, bag_eqv (x::l) (insert x l).
Proof.
  intros. induction l.
  (* nil *) simpl. apply bag_eqv_refl.
  (* l = a :: l *)
  simpl.
  bdestruct (a >=? x).
  (* a >= x *) apply bag_eqv_refl.
  (* a < x *)
  assert (H0: bag_eqv (a :: x :: l) (a :: insert x l))
    by (apply bag_eqv_cons; assumption).
  apply bag_eqv_trans with (b2 := a :: x :: l).
  unfold bag_eqv. intro. simpl. lia.
  assumption.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (sort_bag)

    Now prove that sort preserves bag contents. *)
Theorem sort_bag: forall l, bag_eqv l (sort l).
Proof.
  intro. induction l. unfold bag_eqv. reflexivity.
  simpl.
  assert (H1: bag_eqv (a :: (sort l)) (insert a (sort l)))
    by apply insert_bag.
  apply bag_eqv_trans with (b2 := a :: (sort l));
  try apply bag_eqv_cons; assumption.
Qed.

(** [] *)

(** Now we wrap it all up.  *)

Theorem insertion_sort_correct:
  is_a_sorting_algorithm' sort.
Proof.
  split. apply sort_bag. apply sort_sorted.
Qed.

(** **** Exercise: 1 star, standard (permutations_vs_multiset)

    Compare your proofs of [insert_perm, sort_perm] with your proofs
    of [insert_bag, sort_bag].  Which proofs are simpler?

      - [ ] easier with permutations,
      - [ ] easier with multisets
      - [ ] about the same.

   Regardless of "difficulty", which do you prefer / find easier to
   think about?
      - [ ] permutations or
      - [ ] multisets

   Put an X in one box in each list. *)
(* Do not modify the following line: *)
Definition manual_grade_for_permutations_vs_multiset : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Permutations and Multisets *)

(** The two specifications of insertion sort are equivalent.  One
    reason is that permutations and multisets are closely related.
    We're going to prove:

       [Permutation al bl <-> bag_eqv al bl.] *)

(** **** Exercise: 3 stars, standard (perm_bag)

    The forward direction is straighforward, by induction on the evidence for
    [Permutation]: *)
Lemma perm_bag:
  forall al bl : list nat,
   Permutation al bl -> bag_eqv al bl. 
Proof.
  intros. induction H.
  - (* nil *) apply bag_eqv_refl.
  - (* skip *) apply bag_eqv_cons. assumption.
  - (* swap *)
    unfold bag_eqv. intro. simpl.
    destruct (y =? n); destruct (x =? n); reflexivity.
  - (* trans *) apply bag_eqv_trans with (b2 := l'); assumption.
Qed.
(** [] *)

(** The other direction,
    [bag_eqv al bl -> Permutation al bl],
    is surprisingly difficult.  
    This proof approach is due to Zhong Sheng Hu.
    The first three lemmas are used to prove the fourth one. *)

(** **** Exercise: 2 stars, advanced (bag_nil_inv) *)
Lemma bag_nil_inv : forall b, bag_eqv [] b -> b = []. 
Proof.
  unfold bag_eqv. intros. induction b.
  reflexivity.
  specialize H with a.
  simpl in H.
  rewrite Nat.eqb_refl in H.
  inversion H.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (bag_cons_inv) *)
Lemma bag_cons_inv : forall l x n,
    S n = count x l ->
    exists l1 l2,
      l = l1 ++ x :: l2
      /\ count x (l1 ++ l2) = n.
Proof.
  intros. induction l.
  - (* nil - contradiction *) inv H.
  - (* a :: l *)
    destruct (a =? x) eqn:E; simpl in H.
    + (* a = x *)
      rewrite E in H.
      inv H.
      exists [], l.
      apply beq_nat_true in E.
      subst.
      auto.
    + (* a <> x *)
      rewrite E in H.
      simpl in H.
      apply IHl in H as [l1 [l2 [Hl Hc]]].
      subst.
      exists (a :: l1), l2.
      simpl. rewrite E.
      auto.
Qed.

(** [] *)

(** **** Exercise: 2 stars, advanced (count_insert_other) *)
Lemma count_insert_other : forall l1 l2 x y,
  y <> x -> count y (l1 ++ x :: l2) = count y (l1 ++ l2).
Proof.
  intro. induction l1; intros.
  - (* l1 = nil *)
    apply Nat.neq_sym in H.
    apply Nat.eqb_neq in H.
    simpl.
    rewrite H.
    auto.
  - (* l1 = a :: l1 *)
    bdestruct (a =? y).
    + subst.
      apply (IHl1 l2 x y) in H.
      simpl.
      rewrite Nat.eqb_refl.
      auto.
    + apply Nat.eqb_neq in H0.
      simpl.
      rewrite H0.
      simpl.
      apply (IHl1 l2 x y) in H.
      assumption.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (bag_perm) *)
Lemma bag_perm:
  forall al bl, bag_eqv al bl -> Permutation al bl.
Proof.
  intro.
  induction al.
  - intros.
    apply bag_nil_inv in H.
    subst.
    constructor.
  - intros. induction bl as [| b bl].
    + apply bag_eqv_sym in H.
      apply bag_nil_inv in H.
      discriminate.
    + bdestruct (a =? b).
      * subst.
        assert (H0: bag_eqv al bl). {
          unfold bag_eqv. intro.
          unfold bag_eqv in H.
          specialize H with n.
          simpl in H.
          bdestruct (b =? n);
          subst; inv H;
          reflexivity.
        }
        apply IHal in H0.
        constructor.
        assumption.
      * assert (exists l1 l2, al = l1 ++ b :: l2 /\ count b (l1 ++ l2) = count b bl)
         as [al1 [al2 [Ha Hcb]]].
       {
        assert (S (count b bl) = count b al) as Ha. {
          unfold bag_eqv in H.
          specialize H with b.
          simpl in H.
          rewrite Nat.eqb_refl in H.
          apply Nat.eqb_neq in H0 as H1.
          rewrite H1 in H.
          simpl in H.
          auto.
                 }
        apply bag_cons_inv in Ha.
        assumption.
          }

       assert (exists l1 l2, bl = l1 ++ a :: l2 /\ count a (l1 ++ l2) = count a al)
         as [bl1 [bl2 [Hb Hca]]].
       {
        assert (S (count a al) = count a bl) as Hb. {
          unfold bag_eqv in H.
          specialize H with a.
          simpl in H.
          rewrite Nat.eqb_refl in H.
          apply Nat.neq_sym in H0.
          apply Nat.eqb_neq in H0 as H2.
          rewrite H2 in H.
          simpl in H.
          auto.
        }
        apply bag_cons_inv in Hb.
        assumption.
                    }

       assert (forall n, n <> b -> n <> a -> count n al = count n bl) as Hcab.
       {
         unfold bag_eqv in H.
         intros.
         specialize H with n.
         simpl in H.
         bdestruct (b =? n);
         bdestruct (a =? n);
         subst;
         try contradiction.
         (* b <> a <> n *)
         simpl in H.
         assumption.
       }

       subst.

       assert (count a (al1 ++ al2) = count a (bl1 ++ bl2)). {
         apply (count_insert_other al1 al2) in H0.
         rewrite H0 in Hca.
         symmetry. assumption.
       }

       assert (count b (al1 ++ al2) = count b (bl1 ++ bl2)). {
         apply not_eq_sym in H0.
         apply (count_insert_other bl1 bl2) in H0.
         rewrite H0 in Hcb.
         assumption.
       }



       (*
       do 2 rewrite app_comm_cons.
       apply Permutation_app.
       *)



Admitted.
(** [] *)

(* ################################################################# *)
(** * The Main Theorem: Equivalence of Multisets and Permutations *)
Theorem bag_eqv_iff_perm:
  forall al bl, bag_eqv al bl <-> Permutation al bl.
Proof.
  intros. split. apply bag_perm. apply perm_bag.
Qed.

(** Therefore, it doesn't matter whether you prove your sorting
    algorithm using the Permutations method or the multiset method. *)

Corollary sort_specifications_equivalent:
    forall sort, is_a_sorting_algorithm sort <->  is_a_sorting_algorithm' sort.
Proof.
  unfold is_a_sorting_algorithm, is_a_sorting_algorithm'.
  split; intros;
  destruct (H al); split; auto;
  apply bag_eqv_iff_perm; auto.
Qed.

(** $Date$ *)

(* 2021-08-11 15:15 *)
