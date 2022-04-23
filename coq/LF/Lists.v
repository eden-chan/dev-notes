From LF Require Export Induction.
(* From LF Require Export Basics. *)

Module NatList.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Definition fst (p : natprod) : nat :=
    match p with
        | pair x y => x 
    end. 

Definition snd (p: natprod) : nat := 
    match p with 
        | pair x y => y 
    end. 

Notation "( x , y )" := (pair x y).
Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p: natprod) : natprod :=
    match p with
        | (x, y) => (y, x)
    end. 
Example swap_pair_test : swap_pair (1, 2) = (2, 1). Proof. reflexivity. Qed. 

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.


Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
    intros p. 
    rewrite surjective_pairing.
    destruct p as [n m].
    simpl.  (* have to expose the structure of p for simpl to perform the pattern match *)
    reflexivity.
Qed. 

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p as [m n].
  rewrite <- snd_fst_is_swap.
  simpl. 
  reflexivity.
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
    | O => nil 
    | S count' => n :: repeat n count'
  end.

Example test_repeat0: repeat 1 0 = []. Proof. reflexivity. Qed.
Example test_repeat1: repeat 1 1 = [1]. Proof. reflexivity. Qed.
Example test_repeat2: repeat 1 3 = [1;1;1]. Proof. reflexivity. Qed.

Fixpoint length (lst : natlist) : nat :=
    match lst with 
        | nil => 0
        | cons x y => 1 + length y
    end.   
Example test_length0: length [] = 0. Proof. reflexivity. Qed.
Example test_length1: length [1] = 1. Proof. reflexivity. Qed.
Example test_length2: length [1;1;1] = 3. Proof. reflexivity. Qed.


Fixpoint append' (lst1 lst2 : natlist) : natlist :=
  match lst1, lst2 with 
    | nil, nil => nil 
    | _, nil =>  lst1 
    | nil, _ => lst2 
    | cons x lst1', lst2 => cons x (append' lst1' lst2)
  end. 

  (* h = head, t = tail *)
Fixpoint append (lst1 lst2 : natlist) : natlist :=
  match lst1 with 
    | nil => lst2 
    | h :: t => h :: (append t lst2)
  end. 
Notation "lst1 ++ lst2" := (append lst1 lst2).
Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5]. Proof. reflexivity. Qed.
Example test_app2:             nil ++ [4;5] = [4;5]. Proof. reflexivity. Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3]. Proof. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat := 
  match l with 
    | nil => default 
    | h :: t => h 
  end. 
Definition tl (l : natlist) : natlist := 
  match l with 
    | [ ] => [ ]
    | h :: t => t 
  end. 

Example test_hd1:             hd 0 [1;2;3] = 1. Proof. reflexivity. Qed.
Example test_hd2:             hd 0 [] = 0. Proof. reflexivity. Qed.
Example test_tl1:              tl [1;2;3] = [2;3]. Proof. reflexivity. Qed.
Example test_tl2:              tl [] = []. Proof. reflexivity. Qed.


  (* USEFUL *)

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with 
    | [] => [] 
    | h :: t => match h with 
                  | O => nonzeros t 
                  | _ => h :: nonzeros t 
                end 
  end.  
Example test_nonzeros0: nonzeros [0;1;0;2;3;0;0] = [1;2;3]. Proof. reflexivity. Qed.
Example test_nonzeros1: nonzeros [0;0;0] = []. Proof. reflexivity. Qed.
Example test_nonzeros2: nonzeros [1;2;3] = [1;2;3]. Proof. reflexivity. Qed.
Example test_nonzeros3: nonzeros [] = []. Proof. reflexivity. Qed.



Definition odd (n : nat) : bool :=
  negb (even n).

(* if then else is a two way constructor for bools *)
Fixpoint oddmembers' (l:natlist) : natlist :=
  match l with 
    | [] => []
    | h :: t => match (odd h) with 
                  | true => h :: (oddmembers' t)
                  | _ => (oddmembers' t)
                  end
  end. 
Fixpoint oddmembers (l:natlist) : natlist :=
  match l with 
    | [] => []
    | h :: t => if (odd h) then h :: (oddmembers t) else (oddmembers t)
  end. 
Example test_oddmembers0: oddmembers [0;1;0;2;3;0;0] = [1;3].  Proof. reflexivity. Qed.
Example test_oddmembers1: oddmembers [1;3;5] = [1;3;5].  Proof. reflexivity. Qed.
Example test_oddmembers2: oddmembers [0;2;4] = [].  Proof. reflexivity. Qed.
Example test_oddmembers3: oddmembers [] = [].  Proof. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l). 
Example test_countoddmembers0: countoddmembers [0;1;0;2;3;0;0] = 2.  Proof. reflexivity. Qed.
Example test_countoddmembers1: countoddmembers [1;3;5] = 3.  Proof. reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [0;2;4] = 0.  Proof. reflexivity. Qed.
Example test_countoddmembers3: countoddmembers [] = 0.  Proof. reflexivity. Qed.

  (* 
Note: one natural and elegant way of writing alternate will fail to 
satisfy Coq's requirement that all Fixpoint definitions be 
"obviously terminating." 
If you find yourself in this rut, look for a slightly more verbose 
solution that considers elements of both lists at the same time.
One possible solution involves defining a new kind of pairs, 
but this is not the only way.
*)
Fixpoint alternate' (l1 l2 : natlist) : natlist :=
  match l1 with 
    | [] => l2 
    | h1 :: t1 => match l2 with 
                  | [] => l1 
                  | h2 :: t2 => h1 :: h2 :: (alternate' t1 t2)
                  end 
    end. 
Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with 
    | [], [] => [] 
    | _, [] => l1  
    | [], _ => l2
    | h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
  end. 
Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].  Proof. reflexivity. Qed.
Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].  Proof. reflexivity. Qed.
Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].  Proof. reflexivity. Qed.
Example test_alternate4: alternate [] [1;2;3] = [1;2;3].  Proof. reflexivity. Qed.
Example test_alternate5: alternate [1;2;3] [] = [1;2;3].  Proof. reflexivity. Qed.
Example test_alternate6: alternate [1;3] [2;4;5;6] = [1;2;3;4;5;6].  Proof. reflexivity. Qed.
Example test_alternate7: alternate [1;3;5;6] [2;4] = [1;2;3;4;5;6].  Proof. reflexivity. Qed.
Example test_alternate8: alternate [] [] = [].  Proof. reflexivity. Qed.


  (* 
 A bag (or multiset) is like a set, except that each element can 
 appear multiple times rather than just once. 
 One possible representation for a bag of numbers is as a list. 
  *)
Definition bag := natlist.
Compute eqb 1 2. 
(* TODO: length of filter *)
Fixpoint count (v : nat) (s : bag) : nat :=
  match s with 
    | [] => 0
    | h :: t => if (h =? v) then 1 + (count v t) else (count v t)
  end. 
Example test_count0: count 1 [1;2;3;1;4;1] = 3. Proof. reflexivity. Qed. 
Example test_count1: count 1 [1;1;1] = 3. Proof. reflexivity. Qed. 
Example test_count2: count 1 [2;3;4] = 0. Proof. reflexivity. Qed. 
Example test_count3: count 1 [] = 0. Proof. reflexivity. Qed. 

(* 
Multiset sum is similar to set union: sum a b contains all the elements of a and of b.
(Mathematicians usually define union on multisets a little bit differently -- 
  using max instead of sum -- which is why we don't call this operation union.)
*)
Definition sum (a b : bag) : bag :=
  (append a b).
Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3. Proof. reflexivity. Qed. 

Definition add (v : nat) (s : bag) : bag := v :: s.
Example test_add1:                count 1 (add 1 [1;4;1]) = 3. Proof. reflexivity. Qed. 
Example test_add2:                count 5 (add 1 [1;4;1]) = 0. Proof. reflexivity. Qed. 

Fixpoint member (v : nat) (s : bag) : bool := 
  match s with 
    | [] => false 
    | h :: t => if (eqb h v) then true else (member v t)
  end. 

(* Fixpoint member (v : nat) (s : bag) : bool :=  *)
  (* ((count v s) >=? 1). *)
Example test_member1:             member 1 [1;4;1] = true. Proof. reflexivity. Qed.
Example test_member2:             member 2 [1;4;1] = false. Proof. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with 
    | [] => []
    | h :: t => if (eqb h v) then t else (h :: (remove_one v t))
  end.  
Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0. Proof. reflexivity. Qed.
Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0. Proof. reflexivity. Qed.
Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2. Proof. reflexivity. Qed.
Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1. Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with 
    | [] => []
    | h :: t => if (eqb h v) then (remove_all v t) else (h :: (remove_all v t))
  end. 
Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0. Proof. reflexivity. Qed.
Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0. Proof. reflexivity. Qed.
Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2. Proof. reflexivity. Qed.
Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0. Proof. reflexivity. Qed.
Example test_remove_all5:  count 5 (remove_all 5 [5;5;2;1;4;1;5;5]) = 0. Proof. reflexivity. Qed.

Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
  match s1, s2 with 
    | [], [] => true 
    | [], _ => true 
    | _, [] => false 
    | h::t, _ =>  if (member h s2) 
                  then (subset t (remove_one h s2)) 
                  else false
  end.  
Example test_subset1:              subset [1;2] [2;1;4;1] = true. Proof. reflexivity. Qed.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false. Proof. reflexivity. Qed.
Example test_subset3:              subset [1;2;3] [1;2;3] = true. Proof. reflexivity. Qed.
Example test_subset4:              subset [] [1;2;3] = true. Proof. reflexivity. Qed.
Example test_subset5:              subset [] [] = true. Proof. reflexivity. Qed.
Example test_subset6:              subset [1] [] = false. Proof. reflexivity. Qed.


(* Adding a value to a bag should increase the value's count by one. 
State this as a theorem and prove it.
*)

(* Lemma ternary : forall cond : bool, forall a, forall b,
  if cond then (eqb a a) else (eqb b b). 
Proof. 
  intros cond a b. 
  simpl. 
  destruct cond as [| t f].
 - reflexivity.
  - reflexivity.
Qed.  *)

(* 
Require and Import are used often together
But they do different things. 
Require loads the file. 
Import manages the name space. 

When coq files (DIR/File.vo) are loaded with Require,
 the contents of File.vo is wrapped in 
 Module DIR.FILE 
 ... 
 End 
Everything defined in the file is then accessed with 
      DIR.FILE.SOME_DEF
      
The file can itself have modules M (MODULE) inside of it.
To access contents of M, type 
    DIR.File.MODULE_M.SOME_DEF_IN_MODULE_M

    Import gets all definitions to the top level.
Import DIR.FILE.MODULE_M gets SOME_DEF_IN_MODULE_M to the top level, 
so now it can be referenced without DIR.FILE.MODULE_M path
https://stackoverflow.com/questions/36621752/how-to-import-the-library-coq-arith-peanonat-in-coq/36647535#36647535
*)
(* Require Import Coq.Arith.EqNat. *)

(* Check beq_nat_refl. 
Check (eqb 1 2). 
Check true. 
Check Datatypes.true.
It's fine to use Admitted. to avoid type issues from the stdlib *)
Lemma eqbnat_refl': forall v : nat, v =? v = true. Proof. Admitted. 

Theorem bag_theorem: forall v n : nat, forall b : bag, 
  (count v (add v b)) = S (count v b).
Proof.
  intros v n b. 
  simpl.
  rewrite eqbnat_refl'. 
  reflexivity.
Qed. 

(* As with numbers, simple facts about list-processing functions can sometimes be proved entirely by simplification.  
  *)
Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.

(* interesting theorems about lists require induction for their proofs.   *)

(* Since larger lists can always be broken down into smaller ones, eventually reaching nil *)
Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.
(* Coq proof is not especially illuminating as a static document 
-- it is easy to see what's going on if you are reading the proof
   in an interactive Coq session and you can see the current goal 
   and context at each point, but this state is not visible in the
   written-down parts of the Coq proof. So a natural-language proof 
-- one written for human readers -- will need to include more explicit
   signposts; in particular, it will help the reader stay oriented 
   if we remind them exactly what the induction hypothesis is in the
   second case. 
   
Theorem: For all lists l1, l2, and l3, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof: By induction on l1.
Suppose l1 = []. 
Then ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3), by definition of ++.

Otherwise, suppose l1 = n::l1', with
    (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)
as the induction hypothesis. 
Now ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3). by definition of ++.
Finally,
    n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),
which is immediate from the induction hypothesis. ☐   
   
*)
Fixpoint rev (l:natlist) : natlist :=
  match l with 
    | [] => []
    | h :: t => (rev t) ++ [h]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1]. Proof. reflexivity. Qed.
Example test_rev2: rev [] = []. Proof. reflexivity. Qed.


Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = n :: l' *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving ++, but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

(* 
Theorem app_length: For all lists l1 and l2, we have 
  length (l1 ++ l2) = length l1 + length l2 
Proof. By induction on l1.

Base case: l1 = []
We have     
  length ([] ++ l2) = length [] + length l2 
Which follows directly from definition of ++ and plus  

  --

Inductive step: l1 = n :: l1' where
  length (l1 ++ l2) = length l1 + length l2 
We show 
    length ((n :: l1') ++ l2) = length (n :: l1') + length l2 
which follows directly from definition of length and ++ together with
the inductive hypothesis.  ☐
*)
Theorem rev_length : forall  l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = n l' *)
    simpl. rewrite app_length. 
    simpl. rewrite IHl'.
    rewrite add_comm.
    simpl. reflexivity.
 Qed. 
(* 
Theorem rev_length: For all lists l, we have 
      length (rev l) = length l.

Proof. By induction on l.

Base case: l = []
We have     
  length (rev []) = length [] 
Which follows directly from definition of rev, length, and plus.

  --

Inductive step: l1 = n :: l1' where the IH is 
    length (rev l') = length l'.
We must show 
    length (rev (n :: l1')) = length (n :: l1')  
By definition of rev, app_length, we get 
    length (rev l' ++ [n]) = length (n :: l1')        (rev)
    length (rev l') + length [n] = length (n :: l1')  (app_length)
    length l' + length [n] = length (n :: l1')  (IH)
which follows directly from definition of length and plus.  ☐

Theorem: For all lists l, length (rev l) = length l.
Proof: First, observe that 
    length (l ++ [n]) = S (length l)
 for any l, by induction on l.
The main property again follows by induction on l,
using the observation together with the induction hypothesis 
in the case where l = n'::l'. ☐ ** too big brain for me. readability is more important. 


*)
(* Search rev.
Search (_ + _ = _ + _).
Search (_ + _ = _ + _) inside Induction.
Search (?x + ?y = ?y + ?x). *)


Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof. 
  intros l. induction l as [| n l' IHl'].
  - (* l = [] *) 
    reflexivity.
  - (* l = n l' *)
    simpl. 
  rewrite IHl'. 
  reflexivity. 
Qed.


Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = [] *)
    simpl. 
    rewrite app_nil_r.
    reflexivity.
  - (* l1 = n l1' *)
    simpl. 
    rewrite IHl1'. 
    rewrite app_assoc.
    reflexivity.
Qed. 

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = [] *)
    reflexivity.
  - (* l = n l' *)
    simpl. 
    rewrite rev_app_distr. 
    rewrite IHl'. 
    simpl. 
    reflexivity.
Qed. 

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. induction l1 as [| n l1' IHl1'].
  - (* l1 = [] *)
    simpl. rewrite app_assoc. reflexivity.
  - (* l1 = n l1' *)
    simpl. rewrite <- IHl1'. reflexivity.
Qed. 

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = [] *)
    simpl. reflexivity.
  - (* l1 = n l1' *)
    induction n as [| n' IHn'].
    + (* n = O *) 
      simpl. rewrite IHl1'. reflexivity.
    + (* n = S n' *)
      simpl. rewrite IHl1'. reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool := 
  match l1 with 
    | [] => match l2 with 
              | [] => true 
              | _ => false 
              end 
    | h1 :: t1 => match l2 with 
              | [] => false 
              | h2 :: t2 => if (eqb h1 h2) then (eqblist t1 t2) else false 
              end 
end. 


Example test_eqblist1 : (eqblist nil nil = true). Proof. reflexivity. Qed.
Example test_eqblist2 : eqblist [1;2;3] [1;2;3] = true. Proof. reflexivity. Qed.
Example test_eqblist3 : eqblist [1;2;3] [1;2;4] = false. Proof. reflexivity. Qed.
Example test_eqblist4 : eqblist [1] [1;2;4] = false. Proof. reflexivity. Qed.
Example test_eqblist5 : eqblist [1;2;3] [1] = false. Proof. reflexivity. Qed.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = [] *)
    reflexivity.
  - (* l = n l' *)
    simpl. rewrite eqbnat_refl'. 
    rewrite <- IHl'. 
    reflexivity.
Qed. 

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros s. simpl. reflexivity.
Qed. 


(* USEFUL for later *)
Theorem leb_n_Sn : forall  n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.
 

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s. induction s as [| n s' IHs'].
  - (* s = [] *)
    simpl. reflexivity.
  - (* s = n s' *)
  induction n as [| n' IHn' ].
    + (* n = O *)
      simpl. rewrite leb_n_Sn. reflexivity. 
    + (* n = S n' *) 
      simpl. 
      rewrite IHs'. 
      reflexivity.
Qed. 


(* Write down an interesting theorem bag_count_sum 
about bags involving the functions count and sum, 
and prove it using Coq. 
(You may find that the difficulty of the proof depends
 on how you defined count! 
 Hint: If you defined count using =? you may find it
 useful to know that destruct works on arbitrary
 expressions, not just simple identifiers.) *)

Theorem bag_count_sum: forall n: nat, forall b1 b2: bag, 
      (count n b1) + (count n b2) = (count n (sum b1 b2)).
Proof. 
  intros n b1 b2. 
Admitted. 

Lemma rev_n : forall n:nat, 
  rev ([n]) = [n].
Proof. simpl. reflexivity. Qed. 

Lemma rev_empty : rev [] = []. Proof. reflexivity. Qed. 


Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2. 
  intros H. 
  induction l1 as [| n1 l1' IHl1' ].
  - (* l1 = [] *)
    rewrite <- rev_involutive. 
    rewrite <- H. 
    reflexivity. 
  - (* l1 = n1 l1' *)
    rewrite <- rev_involutive. 
    rewrite <- H.
    rewrite rev_involutive. 
    reflexivity.
Qed. 

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42 (* can't tell if 42 is the input or error *)
  | a :: l' => match n with
               | 0 => a
               | S n' => nth_bad l' n'
               end
  end.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | [] => None
  | h :: t => match n with
               | O => Some h
               | S n' => nth_error t n'
               end
  end.
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4. Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7. Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None. Proof. reflexivity. Qed.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(* Fix the hd function from earlier so the default value is not hard-coded. *)
Definition hd_error (l : natlist) : natoption := 
  match l with 
    | [] => None 
    | h :: t => Some h 
  end. 
Example test_hd_error1 : hd_error [] = None. Proof. reflexivity. Qed. 
Example test_hd_error2 : hd_error [1] = Some 1. Proof. reflexivity. Qed. 
Example test_hd_error3 : hd_error [5;6] = Some 5. Proof. reflexivity. Qed. 

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = [] *)
    simpl. reflexivity. 
  - (* l = n l' *)
    simpl.  reflexivity. 
Qed. 

End NatList.

Module PartialMap.
Export NatList. (* make the definitions from NatList available here *)

(* Partial Maps *)
(* Internally, an id is just a number.
Introducing a separate type by wrapping each nat with
the tag Id makes definitions more readable and gives 
us flexibility to change representations later if we want to. *)
Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.
Theorem eqb_id_refl : forall x : id, eqb_id x x = true.
Proof.
  intros x. 
  destruct x as [x'].
  simpl. 
  rewrite eqbnat_refl'. 
  reflexivity.
Qed. 

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).
Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (k : id) (m : partial_map) : natoption := 
  match m with 
    | empty => None 
    | record k' v m' => if (eqb_id k k') then Some v else find k m'
  end.

Definition map0 := 
  (record (Id 0) 0 (record (Id 1) 1 (record (Id 2) 2 empty))).
Example test_find0: find (Id 0) map0 = Some 0. Proof. reflexivity. Qed. 
Example test_find1: find (Id 1) map0 = Some 1. Proof. reflexivity. Qed. 
Example test_find2: find (Id 2) map0 = Some 2. Proof. reflexivity. Qed. 
Example test_find3: find (Id 3) map0 = None. Proof. reflexivity. Qed. 
Example test_find4: find (Id 3) empty = None. Proof. reflexivity. Qed. 

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v. 
  simpl. rewrite eqb_id_refl. reflexivity. 
Qed. 

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o. 
  intro H. 
  simpl. rewrite H. reflexivity. 
Qed.

End PartialMap. 

