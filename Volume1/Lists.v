From LF Require Export Induction.
Module NatList.
    Inductive natprod : Type :=
        | pair (n1 n2 : nat).

    Check (pair 3 5) : natprod.

    Definition fst (p: natprod) : nat :=
        match p with
        | pair x _ => x
        end.

    Definition snd (p: natprod) : nat :=
        match p with
        | pair _ y => y
        end.
    
    Compute (fst (pair 3 5)).

    Notation "( x , y )" := (pair x y).
    
    Compute (fst (3, 5)).

    Definition fst' (p : natprod) : nat :=
        match p with
        | (x, _) => x
        end.

    Definition snd' (p : natprod) : nat := 
        match p with
        | (_, y) => y
        end.

    Definition swap_pair (p : natprod) : natprod :=
        match p with
        | (x, y) => (y, x)
        end.
    
    Theorem surjective_pairing' : forall n m : nat,
        (n, m) = (fst (n, m), snd (n, m)).
    Proof.
        reflexivity.
    Qed.

    Theorem surjective_pairing : forall p : natprod,
        p = (fst p, snd p).
    Proof.
        intros p. destruct p as [n m]. reflexivity.
    Qed.

    Theorem snd_fst_is_swap: forall p : natprod,
        (snd p, fst p) = swap_pair p.
    Proof.
        intros p. destruct p as [n m]. reflexivity.
    Qed.
    
    Theorem fst_swap_is_snd: forall p : natprod,
        fst (swap_pair p) = snd p.
    Proof.
        intros p. destruct p as [n m]. reflexivity.
    Qed.
    
    Inductive natlist : Type :=
        | nil
        | cons (n : nat) ( l :  natlist).
    
    Notation "x :: l" :=
        (cons x l)
        (at level 60, right associativity).
    
    Notation "[ ]" := nil.
    Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

    Fixpoint repeat (n count : nat) : natlist :=
        match count with
        | 0 => nil
        | S count' => n :: (repeat n count')
    end.

    Fixpoint length (l: natlist) : nat :=
        match l with
        | nil => 0
        | h :: t => S (length t)
        end.

    Fixpoint app (l1 l2 : natlist) : natlist :=
        match l1 with
        | nil => l2
        | h :: t => h :: (app t l2)
        end.

    Notation "x ++ y" :=
        (app x y)
        (at level 60, right associativity).
    
    Definition hd (default : nat) (l : natlist) : nat := 
        match l with
        | nil => default
        | h :: _ => h
        end.
    
    Definition tl (l : natlist) : natlist := 
        match l with
        | nil => nil
        | h :: t => t
        end.
    
    Fixpoint nonzeros (l : natlist) : natlist :=
        match l with
        | nil => nil
        | 0 :: t => nonzeros t
        | h :: t => h :: (nonzeros t)
        end.
    
    Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
    Proof. reflexivity. Qed.


    Fixpoint oddmembers (l:natlist) : natlist :=
        match l with
        | nil => nil
        | h :: t => let 
            t' := oddmembers t 
            in if odd h then h :: t' else t'
        end.
    
    Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
    Proof. reflexivity. Qed.

    Definition countoddmembers (l:natlist) : nat := length (oddmembers l).

    Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
    Proof. reflexivity. Qed.
    Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
    Proof. reflexivity. Qed.
    Example test_countoddmembers3: countoddmembers nil = 0.
    Proof. reflexivity. Qed.

    Fixpoint alternate (l1 l2 : natlist) : natlist :=
        match l1, l2 with
        | nil, l2' => l2'
        | l1', nil => l1'
        | h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
        end.
    
    Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
    Proof. reflexivity. Qed.
    Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
    Proof. reflexivity. Qed.
    Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
    Proof. reflexivity. Qed.
    Example test_alternate4: alternate [] [20;30] = [20;30].
    Proof. reflexivity. Qed.

    Definition bag := natlist.

    Fixpoint count (v : nat) (s : bag) : nat :=
        match s with
        | nil => 0
        | h :: t => let tc := count v t in if h =? v then 1 + tc else tc
        end.

    Example test_count1: count 1 [1;2;3;1;4;1] = 3.
    Proof. reflexivity. Qed.
    Example test_count2: count 6 [1;2;3;1;4;1] = 0.
    Proof. reflexivity. Qed.

    Definition sum : bag -> bag -> bag := app.
    
    Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
    Proof. reflexivity. Qed.

    Definition add : nat -> bag -> bag := cons.

    Example test_add1: count 1 (add 1 [1;4;1]) = 3.
    Proof. reflexivity. Qed.
    Example test_add2: count 5 (add 1 [1;4;1]) = 0.
    Proof. reflexivity. Qed.

    Definition member (v : nat) (s : bag) : bool := negb ((count v s) =? 0).

    Example test_member1: member 1 [1;4;1] = true.
    Proof. reflexivity. Qed.
    Example test_member2: member 2 [1;4;1] = false.
    Proof.  reflexivity. Qed.

    (* Exercise: 3starts, standard, optional (bag_more_functions) 

    Here are some more bag functions for you to practice with.

    When remove_one is applied to a bag without the number to remove, it should 
    return the same bag unchanged. (This exercise is optional, but students 
    following the advanced track will need to fill in the definition of remove_one
    for a later exercise.) 

    *)

    Fixpoint remove_one (v : nat) (s : bag) : bag :=
        match s with
        | nil => nil
        | h :: t => if h =? v then t else h :: (remove_one v t)
        end.

    Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
    Proof. reflexivity. Qed.
    Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
    Proof. reflexivity. Qed.
    Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
    Proof. reflexivity. Qed.
    Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
    Proof. reflexivity. Qed.

    Fixpoint remove_all (v:nat) (s:bag) : bag :=
        match s with
        | nil => nil
        | h :: t => let rem := remove_all v t in if h =? v then rem else h :: rem
        end.

    Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
    Proof. reflexivity. Qed.
    Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
    Proof. reflexivity. Qed.
    Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
    Proof. reflexivity. Qed.
    Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
    Proof. reflexivity. Qed.

    Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
        match s1, s2 with
        | nil, _ => true
        | _, nil => false
        | h :: t, s2' => (member h s2') && subset t (remove_one h s2')
        end.

    Example test_subset1: subset [1;2] [2;1;4;1] = true.
    Proof. reflexivity. Qed.
    Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
    Proof. reflexivity. Qed.

    (* Exercise: 2 stars, standard especially useful (add_inc_count) 
    
    Adding a value to a bag should increase the value's count by one. 
    State that as a theorem and prove it. 
    *)

    Theorem eq_refl: forall n : nat,
        n =? n = true.
    Proof.
        intros n. induction n as [|n' IHn'].
        - reflexivity.
        - simpl. rewrite -> IHn'. reflexivity.
    Qed.
    

    Theorem bag_add_inc_count : forall v : nat, forall b : bag,
        count v (add v b) = S (count v b).
    Proof.
        intros v b. 
        destruct b as [|bh' bt'].
        - simpl. rewrite -> eq_refl. reflexivity.
        - simpl. rewrite -> eq_refl. reflexivity.
    Qed.

    Fixpoint rev (l:natlist) : natlist :=
        match l with
        | nil => nil
        | h :: t => rev t ++ [h]
        end.

    Example test_rev1: rev [1;2;3] = [3;2;1].
    Proof. reflexivity. Qed.
    Example test_rev2: rev nil = nil.
    Proof. reflexivity. Qed.

    Theorem app_length : forall l1 l2 : natlist,
        length (l1 ++ l2) = (length l1) + (length l2).
    Proof.
        (* WORKED IN CLASS *)
        intros l1 l2. induction l1 as [| n l1' IHl1'].
        - (* l1 = nil *)
          reflexivity.
        - (* l1 = cons *)
          simpl. rewrite -> IHl1'. reflexivity. 
    Qed.

    Theorem rev_length : forall l : natlist,
        length (rev l) = length l.
    Proof.
        intros l. induction l as [| n l' IHl'].
        - (* l = nil *)
            reflexivity.
        - (* l = cons *)
            simpl. rewrite -> app_length.
            simpl. rewrite -> IHl'. rewrite add_comm.
            reflexivity.
    Qed.
  

    (* Exercise: 3 stars, standard (list_exercises) 
    
    More practice with lists:
    *)

    Theorem app_nil_r : forall l : natlist,
        l ++ [] = l.
    Proof.
        intros l. induction l as [|lh' lt' IHl'].
        - reflexivity.
        - simpl. rewrite -> IHl'. reflexivity.
    Qed.

    Theorem app_assoc: forall l1 l2 l3 : natlist,
        l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
    Proof.
        intros l1 l2 l3. induction l1 as [|l1h l1t IHl1'].
        - (* l1 = nil *)
            reflexivity.
        - (* l1 = cons l1h l1t *)
            simpl. rewrite -> IHl1'. reflexivity.
    Qed.
    
    Theorem rev_app_distr: forall l1 l2 : natlist,
        rev (l1 ++ l2) = rev l2 ++ rev l1.
    Proof.
        intros l1 l2. induction l1 as [|l1h l1t IHl1'].
        - (* l1 = nil *)
            simpl. rewrite -> app_nil_r. reflexivity.
        - (* l1 = cons l1h l1t *)
            simpl. 
            rewrite -> IHl1'. 
            rewrite -> app_assoc. 
            reflexivity.
    Qed.

    Theorem rev_involutive : forall l : natlist,
        rev (rev l) = l.
    Proof.
        intros l. induction l as [|lh lt IHl'].
        - reflexivity.
        - (* l = cons lh lt *)
            simpl. 
            rewrite -> rev_app_distr.
            rewrite -> IHl'.
            reflexivity.
    Qed.

    (* There is a short solution to the next one. If you find yourself 
       getting tangled up, step back and try to look for a simpler way. 
    *)

    Theorem app_assoc4: forall l1 l2 l3 l4 : natlist,
        l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
    Proof.
        intros l1 l2 l3 l4.
        rewrite -> app_assoc.
        rewrite -> app_assoc.
        reflexivity.
    Qed.
    
    (* An exercise about your implementation of nonzeros: *)

    Lemma nonzeros_app: forall l1 l2 : natlist,
        nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
    Proof.
        intros l1 l2. induction l1 as [|l1h l1t IHl1'].
        - reflexivity.
        - induction l1h as [|l1h' IHl1h'].
            -- simpl. rewrite -> IHl1'. reflexivity.
            -- simpl. rewrite -> IHl1'. reflexivity.
    Qed.
    
    (* Exercise: 2 stars, standard (eqblist) 
    
    Fill in the definition of eqblist, which compares lists of numbers
    for equality. Prove that eqblist l l yields true for every list l. 

    *)
 
    Fixpoint eqblist (l1 l2 : natlist) : bool :=
        match l1, l2 with
        | nil, nil => true
        | h1 :: t1, h2 :: t2 => (h1 =? h2) && eqblist t1 t2
        | _, _ => false
        end.  
  
    Example test_eqblist1 : (eqblist nil nil = true).
    Proof. reflexivity. Qed.
    Example test_eqblist2 : eqblist [1;2;3] [1;2;3] = true.
    Proof. reflexivity. Qed.
    Example test_eqblist3 : eqblist [1;2;3] [1;2;4] = false.
    Proof. reflexivity. Qed.
  
    Theorem eqblist_refl : forall l:natlist,
        eqblist l l = true.
    Proof.
        intros l. induction l as [|h t IHl'].
        - reflexivity.
        - simpl. rewrite -> IHl'. rewrite -> eq_refl. reflexivity.
    Qed.

    (* Exercise: 1 star, standard (count_member_nonzero) *)

    Theorem count_member_nonzero: forall s : bag,
        1 <=? (count 1 (1 :: s)) = true.
    Proof.
        intros s. induction s as [|h t IHs'].
        - reflexivity.
        - simpl. reflexivity.
    Qed.

    Theorem leb_n_Sn: forall n : nat,
        n <=? (S n) = true.
    Proof.
        intros n. induction n as [| n' IHn'].
        - reflexivity.
        - simpl. rewrite -> IHn'. reflexivity.
    Qed.
    
    (* Exercise: 3 stars, advanced (remove_does_not_increase_count) *)

    Theorem remove_does_not_increase_count: forall s : bag,
       (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
    Proof.
        intros s. induction s as [|h t IHs'].
        - reflexivity.
        - simpl. induction h as [|h' IHh'].
            -- simpl. rewrite -> leb_n_Sn. reflexivity.
            -- simpl. rewrite -> IHs'. reflexivity. 
    Qed.
    
    (* Exercise: 3 stars, standard, optional (bag_count_sum)
    
    Write down an interesting theorem bag_count_sum about bags involving
    the functions count and sum, and prove it using Coq. (You may find that
    the difficulty of the proof depends on how you defined count! Hint: If
    you defined count using =? you may find it useful to know that destruct
    works on arbitrary expressions, not just simple identifiers.)
    *)

    Theorem bag_count_sum: forall n : nat, forall b1 b2: bag,
        count n b1 + count n b2 = count n (sum b1 b2).
    Proof.
        intros n b1 b2. induction b1 as [|b1h b1t IHb1].
        - reflexivity.
        - simpl. destruct (b1h =? n) as [].
            -- simpl. rewrite -> IHb1. reflexivity.
            -- rewrite -> IHb1. reflexivity.
    Qed.
    
    (* Exercise: 4 stars, advanced (rev_injective) 
    
    Prove that the rev function is injective. There is a hard way and an easy
    way to do this. 
    *)

    Theorem rev_injective: forall l1 l2 : natlist,
        rev l1 = rev l2 -> l1 = l2.
    Proof.
        intros l1 l2.
        intros H.
        rewrite <- rev_involutive.
        rewrite <- H.
        rewrite -> rev_involutive.
        reflexivity.
    Qed.
    
    Inductive natoption : Type :=
        | Some (n : nat)
        | None.

    Fixpoint nth_error (l : natlist) (n : nat) : natoption :=
        match l, n with
        | nil, _ => None
        | a :: _, 0 => Some a
        | _ :: l', S n' => nth_error l' n'
        end.

    Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
    Proof. reflexivity. Qed.
    Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
    Proof. reflexivity. Qed.
    Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
    Proof. reflexivity. Qed.

    Definition option_elim (d : nat) (o : natoption) : nat := 
        match o with
        | Some n' => n'
        | None => d
        end.
    
    (* Exercise: 2 stars, standard (hd_error)
    
    Using the same idea, fix the hd function from earlier so we
    don't have to pass a default element for the nil case. 
    *)
    
    Definition hd_error (l : natlist) : natoption := 
        match l with
        | nil => None
        | h :: _ => Some h
        end.
    
    Example test_hd_error1 : hd_error [] = None.
    Proof. reflexivity. Qed.
    Example test_hd_error2 : hd_error [1] = Some 1.
    Proof. reflexivity. Qed.
    Example test_hd_error3 : hd_error [5;6] = Some 5.
    Proof. reflexivity. Qed.

    (* Exercise: 1 star, standard, optional (option_elim_hd) 
    
    This exercise relates your new hd_error to the old hd.
    *)

    Theorem option_elim_hd: forall (l : natlist) (default : nat),
        hd default l = option_elim default (hd_error l).
    Proof.
        intros l d. destruct l as [].
        - reflexivity.
        - reflexivity.
    Qed.
End NatList.

Inductive id : Type := Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
    match x1, x2 with
    | Id n1, Id n2 => n1 =? n2
    end.

(* Exercise: 1 star standard (eqb_id_refl) *)

Theorem eqb_id_refl: forall x: id,
    eqb_id x x = true.
Proof.
    intros x. destruct x. simpl. rewrite -> NatList.eq_refl. reflexivity.
Qed.

Module PartialMap.
    Export NatList.

    Inductive partial_map : Type :=
        | empty
        | record (i: id) (v : nat) (m : partial_map).

    Definition update (d : partial_map) (x : id) (value : nat) : partial_map := 
        record x value d.
    
    Fixpoint find (x : id) (d : partial_map) : natoption :=
        match d with
        | empty => None
        | record y v d' => if eqb_id x y
                           then Some v
                           else find x d'
        end.

    (* Exercise: 1 star, standard (update_eq) *)

    Theorem update_eq: forall (d: partial_map) (x : id) (v : nat),
        find x (update d x v) = Some v.
    Proof.
        intros d x v. destruct d as [].
        - simpl. rewrite -> eqb_id_refl. reflexivity.
        - simpl. rewrite -> eqb_id_refl. reflexivity.
    Qed.
    
    (* Exercise: 1 star, standard (update-neq) *)

    Theorem update_neq: forall (d : partial_map) (x y : id) (o : nat),
        eqb_id x y = false -> find x (update d y o) = find x d.
    Proof.
        intros d x y o H. destruct d as [].
        - simpl. rewrite -> H. reflexivity.
        - simpl.  rewrite -> H. reflexivity.
    Qed.
End PartialMap.
