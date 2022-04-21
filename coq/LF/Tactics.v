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