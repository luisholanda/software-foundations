From LF.Volume1 Require Export Lists.

Inductive list (X : Type) : Type :=
    | nil
    | cons (x : X) (l : list X).

Arguments nil {X}.
Arguments cons {X}.

Fixpoint repeat {X : Type} (x : X) (count : nat) : list X :=
    match count with
    | 0 => nil
    | S count' => cons x (repeat x count')
    end.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
    match l1 with
    | nil => l2
    | cons h t => cons h (app t l2)
    end.

Fixpoint rev {X : Type} (l : list X) : list X :=
    match l with
    | nil =>  nil
    | cons h t => app (rev t) (cons h nil)
    end.

Fixpoint length {X : Type} (l : list X) : nat :=
    match l with
    | nil => 0
    | cons _ l' => S (length l')
    end.

Notation "x :: y" :=
    (cons x y)
    (at level 60, right associativity).

Notation "[]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" :=
    (app x y)
    (at level 60, right associativity).

(* Exercise: 2 stars, standard, optional (poly_exercises) 

Here are a few simple exercises, just like ones in the Lists chapter,
for practice with polymorphism. Complete the proofs below. 
*)

Theorem app_nil_r: forall X : Type, forall l : list X,
    l ++ [] = l.
Proof.
    intros X l. induction l as [|h t IHl].
    - reflexivity.
    - simpl. rewrite -> IHl. reflexivity.
Qed.

Theorem app_assoc: forall (A : Type) (l m n: list A),
    l ++ m ++ n = (l ++ m) ++ n.
Proof.
    intros A l m n. induction l as [|h t IHl].
    - reflexivity.
    - simpl. rewrite -> IHl. reflexivity.
Qed.

Lemma app_length: forall (X: Type) (l1 l2: list X),
    length (l1 ++ l2) = length l1 + length l2.
Proof.
    intros X l1 l2. induction l1 as [|h1 t1 IHl1].
    - reflexivity.
    - simpl. rewrite -> IHl1. reflexivity.
Qed.

(* Exercise: 2 stars, standard, optional (more_poly_exercises)

Here are some slightly more interesting ones... 
*)

Theorem rev_app_distr: forall (X: Type) (l1 l2 : list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
    intros X l1 l2. induction l1 as [|h1 t1 IHl1].
    - simpl. rewrite -> app_nil_r. reflexivity.
    - simpl. rewrite -> IHl1. rewrite -> app_assoc. reflexivity.
Qed.

Theorem rev_involutive: forall (X : Type) (l : list X),
    rev (rev l) = l.
Proof.
    intros X l. induction l as [|h t IHl].
    - reflexivity.
    - simpl. rewrite -> rev_app_distr. rewrite -> IHl. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type := pair (x : X) (y: Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).
Notation "X * Y":= (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y): X := 
    match p with
    | (x, y) => x
    end.

Definition snd {X Y : Type} (p : X * Y): Y := 
    match p with
    | (x, y) => y
    end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
    match lx, ly with
    | [], _ => []
    | _, [] => []
    | x :: tx, y :: ty => (x, y) :: (combine tx ty)
    end.

(* Exercise: 2 stars, standard, especially useful (split)

The function split is the right inverse of combine: it takes a list of pairs and
returns a pair of lists. In many functional languages, it is called unzip.

Fill in the definition of split below. Make sure it passes the given unit test. 
*)

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t => let (xs, ys) := split t in (x :: xs, y :: ys)
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Fixpoint nth_error {X : Type} (l: list X) (n : nat) : option X :=
    match l, n with
    | nil, _ => None
    | a :: _, 0 => Some a
    | _ :: l', S n' => nth_error l' n'
    end.

(* Exercise: 1 star, standard, optional (hd_error_poly)

Complete the definition of a polymorphic version of the hd_error function from the 
last chapter. Be sure that it passes the unit tests below. 
*)

Definition hd_error {X : Type} (l : list X) : option X :=
    match l with
    | nil => None
    | h :: _ => Some h
    end.

(*  Once again, to force the implicit arguments to be explicit, we can use @ 
before the name of the function.  *)

Check @hd_error : forall X : Type, list X -> option X.
Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

Fixpoint filter { X : Type } (test: X -> bool) (l : list X) : list X :=
    match l with
    | [] => []
    | h :: t =>
        if test h then h :: (filter test t)
        else filter test t
    end.

(* Exercise: 2 stars, standard (filter_even_gt7) *)

Definition filter_even_gt7 (l : list nat) : list nat :=
    filter (fun n => even n && (7 <=? n) ) l.

Example test_filter_even_gt7_1 : filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 : filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

(* Exercise: 3 stars, standard (partition)

Use filter to write a Coq function partition:
      partition : ∀ X : Type,
                  (X → bool) → list X → list X × list X

Given a set X, a predicate of type X → bool and a list X, partition should return
a pair of lists. The first member of the pair is the sublist of the original list
containing the elements that satisfy the test, and the second is the sublist containing
those that fail the test. The order of elements in the two sublists should be the same
as their order in the original list. 
*)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
    (filter test l, filter (fun x => negb (test x)) l).

Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
    match l with
    | [] => []
    | h :: t => (f h) :: (map f t)
    end.

(* Exercise: 3 stars, standard (map_rev)

Show that map and rev commute. You may need to define an auxiliary lemma. 
*)

Lemma map_linear: forall (X Y : Type) (f : X -> Y) (l1 l2: list X),
    map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
    intros X Y f l1 l2. induction l1 as [|h1 t1 IHl1].
    - reflexivity.
    - simpl. rewrite <- IHl1. reflexivity.
Qed.

Theorem map_rev: forall (X Y : Type) (f : X -> Y) (l : list X),
    map f (rev l) = rev (map f l).
Proof.
    intros X Y f l. induction l as [|h t IHl].
    - reflexivity.
    - simpl. rewrite -> map_linear. rewrite -> IHl. reflexivity.
Qed.

(* Exercise: 2 stars, standard, especially useful (flat_map)

The function map maps a list X to a list Y using a function of type X → Y. 

We can define a similar function, flat_map, which maps a list X to a list Y 
using a function f of type X → list Y. Your definition should work by 'flattening'
the results of f, like so:
        flat_map (fun n ⇒ [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].
*)

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : list Y :=
    match l with
    | [] => []
    | h :: t => (f h) ++ flat_map f t
    end.

Example test_flat_map1: flat_map (fun n => [n;n;n]) [1;5;4] = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
    match l with
    | nil => b
    | h :: t => f h (fold f t b)
    end.

Module Exercises.
    (* Exercise: 2 stars, standard (fold_length)

    Many common functions on lists can be implemented in terms of fold. For
    example, here is an alternative definition of length: 
    *)

    Definition fold_length {X : Type} (l : list X) : nat := fold (fun _ n => S n) l 0.
    Example test_fold_length1 : fold_length [4;7;0] = 3.
    Proof. reflexivity. Qed.

    (* 
    Prove the correctness of fold_length. (Hint: It may help to know that reflexivity
    simplifies expressions a bit more aggressively than simpl does -- i.e., you may find 
    yourself in a situation where simpl does nothing but reflexivity solves the goal.)
    *)

    Theorem fold_length_correct: forall (X : Type) (l : list X),
        fold_length l = length l.
    Proof.
        intros X l. induction l as [|h t IHl].
        - reflexivity.
        - simpl. rewrite <- IHl. reflexivity.
    Qed.
    
    (* Exercise: 3 stars, standard (fold_map)

    We can also define map in terms of fold. Finish fold_map below. 
    *)

    Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
        fold (fun x r => (f x) :: r) l [].

    (* 
    Write down a theorem fold_map_correct in Coq stating that fold_map is correct, 
    and prove it. (Hint: again, remember that reflexivity simplifies expressions a bit 
    more aggressively than simpl.) 
    *)

    Theorem fold_map_correct: forall {X Y : Type} (f : X -> Y) (l : list X),
        fold_map f l = map f l.
    Proof.
        intros X Y f l. induction l as [|h t IHl].
        - reflexivity.
        - simpl. rewrite <- IHl. reflexivity.
    Qed.
End Exercises.
