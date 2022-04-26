Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
 
From LF Require Export Poly.

Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.
  apply eq. (* alternatively "rewrite → eq. reflexivity."*)
Qed.

(* 
The apply tactic also works with conditional 
hypotheses and lemmas: if the statement being applied
 is an implication, then the premises of this implication
will be added to the list of subgoals needing to be proved.
*)
Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.


(* 
Typically, when we use apply H, the statement H
 will begin with a ∀ that introduces some universally 
 quantified variables. When Coq matches the current goal
 against the conclusion of H, it will try to find appropriate
 values for these variables. For example, when we do apply 
 eq2 in the following proof, the universal variable q in 
 eq2 gets instantiated with n, and r gets instantiated with m.

*)
Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m)  ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.


Definition odd := fun n => negb (even n).
Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
    intros p eq1 eq2 eq3.  

    assert (H: forall p, odd (S p) = negb (even (S p))).
    { reflexivity. } 
    rewrite  H. 
    apply eq2.
    apply eq1.
    apply eq3. 
Qed. 
(* 
To use the apply tactic, the (conclusion of the) 
fact being applied must match the goal exactly 
(perhaps after simplification) -- for example,
apply will not work if the left and right sides of the equality are swapped. 

In this case, use symmetry tactic.
*)

Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H.
  (* Fail apply H. *)
    symmetry. apply H. Qed.

Search app.
Search rev. 
Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
    intros l l' H. 
    rewrite H. 
    rewrite rev_involutive.  
    reflexivity.
Qed. 

(* 
apply and rewrite + reflex do the same thing. 
but apply is shorthand, conventional notation for rewrite then reflex
where the goal is the exact result of some previous lemma or hypothesis in context.
*)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.
(* 
two rewrites in a row are used 
this is a common pattern, we might like to
pull it out as a lemma that records,
once and for all, the fact that equality is 
transitive. 
*)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. 
  rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].


    (* 
    If we simply tell Coq apply trans_eq at this 
    point, it can tell (by matching the goal 
    against the conclusion of the lemma) that it 
    should instantiate X with [nat], n with [a,b], 
    and o with [e,f]. However, the matching process doesn't determine an instantiation for m: we have to supply one explicitly by adding "with (m:=[c,d])" to the invocation of apply.
     *)
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2. Qed.

Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2. 
  transitivity [c;d]. (* built-in tactic*)
  apply eq1. apply eq2. Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
    intros n m o p eq1 eq2. 
    transitivity m. 
    apply eq2. apply eq1. 
Qed.


(*
Recall the definition of natural numbers:
     Inductive nat : Type :=
       | O
       | S (n : nat).

Implicit in the definition are two additional facts: 

The constructor S is injective (or one-to-one). 
    That is, if S n = S m, it must be that n = m.
The constructors O and S are disjoint. 
    That is, O is not equal to S n for any n. 

Similar principles apply to every inductively 
defined type: all constructors are injective, 
and the values built from distinct constructors 
are never equal. For lists, the cons constructor 
is injective and nil is different from every 
non-empty list. For booleans, true and false 
are different. (Since true and false take no 
arguments, their injectivity is neither here nor 
there.) And so on.

*)
Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. simpl. reflexivity.
Qed.
(* 
This technique can be generalized to any 
constructor by writing the equivalent of pred -- 
i.e., writing a function that "undoes" one application of the constructor.
As a more convenient alternative, Coq provides a
tactic called injection that allows us to exploit 
the injectivity of any constructor. Here is an 
alternate proof of the above theorem using injection:
*)

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  (* asking Coq to generate all equations 
  that it can infer from H using the injectivity 
  of constructors*)
  injection H as Hnm. 
  apply Hnm. 
Qed. 
Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
    intros X x y z l j. 
    intros eq1.
    injection eq1 as H1 H2. 
    intros H3. 

    assert (H4 : y :: l = z :: l).
    { transitivity j. apply H2. apply H3. }

    injection H4 as H4'. 
    transitivity z. 
    apply H1. 
    rewrite H4'. reflexivity. 
Qed. 


(*  False => Vacuously True  

The principle of disjointness says that two terms beginning with different constructors (like O and S, or true and false) can never be equal. This means that, any time we find ourselves in a context where we've assumed that two such terms are equal, we are justified in concluding anything we want, since the assumption is nonsensical.
The discriminate tactic embodies this principle: It is used on a hypothesis involving an equality between different constructors (e.g., false = true), and it solves the current goal immediately. 

*)
Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
  intros n m contra. discriminate contra. Qed.
Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.

  (* These examples are instances of a 
  logical principle known as the principle of explosion, 
  which asserts that a contradictory hypothesis entails 
  anything (even manifestly false things!).
   *)


Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
    intros X x y z l j. 
    intros H_contra. 
    discriminate H_contra.
Qed. 

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.
  - (* n = S n'*)
    intros H. discriminate H. 
    (* If we use discriminate on this hypothesis, 
    Coq confirms that the subgoal we are working on is 
    impossible and removes it from further consideration. *)
Qed.


Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.
Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof. 
    intros n m H. 
    apply f_equal. (* there is a built-in tactic f_equal *)
    apply H. Qed.
(* Given a goal of the form f a1 ... an = g b1 ... bn, 
the tactic f_equal will produce subgoals of the form 
f = g, a1 = b1, ..., an = bn. At the same time, 
any of these subgoals that are simple enough 
(e.g., immediately provable by reflexivity) will be 
automatically discharged by f_equal *)

Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b  ->
  (n =? m) = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.


Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H. apply EQ in H. symmetry in H.
  apply H. Qed.

Theorem double_injective_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) apply f_equal.
Abort.
(* be careful, when using induction, that you are not trying 
to prove something too specific: When proving a property 
involving two variables n and m by induction on n, it is 
sometimes crucial to leave m generic. *)
Theorem double_injective : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *)  intros m eq. destruct m as [| m'] eqn:E. 
    + (* m = 0 *)
      discriminate eq. 
    + (* m = S m' *)
      apply f_equal.
      apply IHn'. 
      simpl in eq. injection eq as goal. apply goal. Qed.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - (* n = 0 *) destruct m as [| m'] eqn:E. 
      + (* m = 0 *) reflexivity.
      + (* m = S m' *) discriminate.
  - (* n = S n' *) destruct m as [| m'] eqn:E. 
      + (* m = 0 *) discriminate. 
      + (* m = S m' *) 
        intros H. simpl in H.  apply IHn' in H. 
        apply f_equal. apply H. 
Qed. 



Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n. 
  induction n as [| n' IHn'].
  - (* n = 0 *) destruct m as [| m'].
    + (* m = 0 *) reflexivity.
    + (* m = S m' *) simpl. intros H. discriminate H. 
  - (* n = S n' *) destruct m as [| m']. 
    + (* m = 0 *) intros H. discriminate H. 
    + (* m = S m' *) intros H. simpl in H. 
      assert (H' : m' + S m' = S m' + m' ).
        { apply add_comm. }
      rewrite add_comm in H. simpl in H. 
      rewrite H' in H. simpl in H. 
      injection H as goal. 
      apply IHn' in goal. 
      apply f_equal. 
      apply goal. 
Qed. 

Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. injection eq as goal. apply goal. 
Qed. 
(* 
Theorem: For any nats n and m, if double n = double m, then n = m.
Proof: 
Let m be a nat. We prove by induction on m that, for any n, 
  if double n = double m then n = m.
First, suppose m = 0, and suppose n is a number 
  such that double n = double m. We must show that n = 0.
Since m = 0, by the definition of double we have double n = 0. 
There are two cases to consider for n.
 If n = 0 we are done, since m = 0 = n, as required. 
 Otherwise, if n = S n' for some n', we derive a contradiction: 
  by the definition of double, we can calculate double n = S (S (double n')), 
  but this contradicts the assumption that double n = 0.
Second, suppose m = S m' and that n 
  is again a number such that double n = double m. 
  We must show that n = S m', with the induction hypothesis
  that for every number s, if double s = double m' then s = m'.
  By the fact that m = S m' and the definition of double, 
  we have double n = S (S (double m')). 
  There are two cases to consider for n.
    If n = 0, then by definition double n = 0, a contradiction.
Thus, we may assume that n = S n' for some n', and again by the definition of 
double we have S (S (double n')) = S (S (double m')), which implies by injectivity 
that double n' = double m'. Instantiating the induction hypothesis with n' thus allows 
us to conclude that n' = m', and it follows immediately that S n' = S m'. 
Since S n' = n and S m' = m, this is just what we wanted to show. ☐
*)


Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros n X l. 
  generalize dependent n. 
  induction l as [| x l' IHl']. 
  - (* l = [] *) destruct n as [| n'] eqn:E. 
      + (* n = 0 *) reflexivity.
      + (* n = S n' *)intros H. discriminate H. 
  - (* l = x l' *) destruct n as [| n'] eqn:E. 
    + (* n = 0 *)intros H. discriminate H. 
    + (* l = x l' *) intros H. simpl in H. injection H as H'. apply IHl' in H'. 
      simpl. apply H'. 
Qed. 

(* It sometimes happens that we need to manually unfold a name that has been introduced by a
 Definition so that we can manipulate the expression it denotes. *)
Definition square n := n * n.
Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mul_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.


Definition foo (x: nat) := 5.
Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

  Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.
Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.


Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.
Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity. Qed.
 
        Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
  (* stuck... *)
Abort.

(* don't subsitute all existing occurences of n. use eqn to keep track of n *)

Theorem sillyfun1_odd : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
      - (* e3 = true *) apply eqb_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *) destruct (n =? 5) eqn:Heqe5.
        + (* e5 = true *)
          apply eqb_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) discriminate eq. Qed.


(* Fixpoint combine {X Y : Type} (l1 : list X) (l2 : list Y) : list (X * Y) :=
  match (l1, l2) with
    | ([], _) => []
    | (_, []) => []
    | (h1 :: t1, h2 :: t2) => (h1, h2) :: (combine t1 t2)
  end.

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
    | [] => ([], [])
    | (x, y)::t =>  let t' := split t in (x::(fst t'), (y::(snd t')))
  end. *)



Theorem surjective_pairing:  forall X Y (p : X * Y), 
          p = ((fst p), (snd p)).
Proof. 
  intros. destruct p as [ x y]. reflexivity. Qed. 


Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros. generalize dependent l2. generalize dependent l1.  generalize dependent l.
  induction l as [| [x y]].
    -  (* l = [] *) intros. inversion H. simpl. reflexivity.
    - (* l = (x,y) *) 
          intros. simpl in H. 
          injection H as h1 h2. 
          rewrite <- h1. rewrite <- h2. 
          simpl. 
          apply f_equal. 
          apply IHl. 
          apply surjective_pairing.
Qed. 

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros. destruct (f b) eqn:Eqb. 
  - destruct b eqn:Eqb2.
    + rewrite Eqb. apply Eqb. 
    + rewrite <- Eqb2 in Eqb. destruct (f (f b)) eqn:Eqb3. 
      * rewrite <- Eqb.
        assert (H:  f (f b)  =  f b).
        { transitivity true. apply Eqb3. symmetry. apply Eqb. }
        rewrite H. apply H. 
      * rewrite <- Eqb. rewrite Eqb3. rewrite <- Eqb2. reflexivity.
  -  destruct b eqn: Eqb2. 
    + rewrite <- Eqb. rewrite <- Eqb2. destruct (f (f b)) eqn:Eqb3.
      * transitivity false. apply Eqb. symmetry. rewrite Eqb2.  apply Eqb. 
      * rewrite <- Eqb. rewrite <- Eqb2. transitivity false. apply Eqb3. rewrite Eqb2. symmetry. apply Eqb.
    + rewrite Eqb. apply Eqb.
Qed. 
  
Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n. induction n as [| n' IHn' ].  
  - destruct m as [| m'] eqn:Eqm. 
    + reflexivity.
    + reflexivity.
  - destruct m as [| m'] eqn:Eqm. 
    + reflexivity.
    + simpl. apply IHn'. 
Qed. 
      (* destruct (n' =? m) eqn: Eqb. 
       assert (H: n' = m).
       { apply eqb_true. }
        assert (H2: forall b:bool, ((S n') =? (S m)) = b  ->
  (n' =? m) = b).
      { apply S_inj. }
          rewrite Eqb in H2.  symmetry in H2. 
          
        simpl. apply IHn'.
        simpl.  apply IHn'.
Qed.  *)


Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros. 
  assert (H2:  n = m).
  { apply eqb_true. apply H. }
  rewrite H2. apply H0. 
Qed. 


(* 
Hint: what property do you need of l1 and l2 for split 
(combine l1 l2) = (l1,l2) to be true?) length l1 = length l2 *)
Definition split_combine_statement {X Y : Type} (l1 : list X) (l2: list Y): Prop := 
  length l1 = length l2 -> split (combine l1 l2 ) = (l1, l2).
(* (": Prop" means that we are giving a name to a
     logical proposition here.) *)

Theorem split_combine : forall {X Y : Type} (l1 : list X) (l2: list Y),
  split_combine_statement l1 l2.
Proof.
  intros. 
  generalize dependent l2. 
  unfold split_combine_statement.

  induction l1 as [| n l1' IHl1'].
  - simpl. destruct l2 as [| x l2'] eqn:Eqn.
    + simpl. reflexivity.
    + simpl. discriminate. 
  - destruct l2 as [| x l2'] eqn:Eqn.
    + simpl. discriminate. 
    + intros H. 
      simpl in H. 
      injection H as H'.
      apply IHl1' in H'. 
      simpl. 
     rewrite H'. 
     simpl. 
      reflexivity. 
Qed. 

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                                 (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof.
  intros. 
  generalize dependent lf. 
  generalize dependent x. 
  induction l as [| n l' IHl'].
  - simpl. discriminate. 
  -  destruct (test n) eqn:eqtest.
    + simpl. rewrite eqtest. Admitted.
(* TODO LATER *)

