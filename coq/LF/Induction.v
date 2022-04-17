(* 
coq_makefile -f _CoqProject *.v -o Makefile
make <file.vo>
*)
From LF Require Export Basics.

Check day.
Check NatPlayground.factorial.


Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.

Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

Theorem add_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl. (* ...but here we are stuck again *)
Abort.

 (* 
the principle of induction over natural numbers: 
If P(n) is some proposition involving a natural number n 
and we want to show that P holds for all numbers n,
we can reason like this:
show that P(O) holds;
show that, for any n', if P(n') holds, then so does P(S n');
conclude that P(n) holds for all n. 
*)

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem add_0_l : forall n:nat, 0 + n = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. reflexivity. Qed.


Theorem add_1_Sn: forall n:nat, S n = n + 1. 
Proof. 
    induction n as [| n' IHn'].
    - (* n = 0 *) simpl. reflexivity.
    - (* n = S n' *)  simpl. rewrite <- IHn'. reflexivity.
Qed. 

Theorem add_1_Sn_l: forall n:nat, S n = 1 + n. 
Proof. 
    induction n as [| n' IHn'].
    - (* n = 0 *) simpl. reflexivity.
    - (* n = S n' *)  simpl. reflexivity.
Qed. 

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
    induction n as [| n' IHn']. (* induction moves quantified variables to context automatically, so intros is redundant for n in this case*)
    - (* n = 0 *) simpl. reflexivity.
    - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.
Qed.


(* two stars my ass *)
Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
    induction n as [| n' IHn']. 
    - (* n = 0 *) simpl. reflexivity.
    - (* n = S n' *) simpl. rewrite IHn'. reflexivity.
Qed.  
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
    induction n as [| n' IHn'].
    - (* n = 0 *) induction m as [| m' IHm'].
        + (* m = 0 *) simpl. reflexivity.
        + (* m = S m' *) simpl. reflexivity.
    - (* n = S n' *) induction m as [| m' IHm'].
        + (* m = 0 *) rewrite add_0_r. simpl. rewrite <- add_1_Sn. reflexivity.
        + (* m = S m' *) simpl.  rewrite <- IHn'. rewrite <- IHn'. rewrite <- IHn'. reflexivity.  
Qed. 

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
    induction n as [| n' IHn'].
    - (* n = 0 *) induction m as [| m' IHm'].
        + (* m = 0 *) simpl. reflexivity.
        + (* m = S m' *) rewrite add_0_l. rewrite add_0_r. simpl. reflexivity. 
    - (* n = S n' *) induction m as [| m' IHm'].
        + (* m = 0 *) rewrite add_0_l. rewrite add_0_r. simpl. reflexivity.
        + (* m = S m' *) simpl. rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. rewrite IHn'. reflexivity.
Qed.

Theorem plus_n_Sm_r : forall n m : nat,
  S (n + m) = (S m) + n.
Proof.
    induction n as [| n' IHn'].
    - (* n = 0 *) induction m as [| m' IHm'].
        + (* m = 0 *) simpl. reflexivity.
        + (* m = S m' *) simpl. rewrite add_0_r. reflexivity.
    - (* n = S n' *) induction m as [| m' IHm'].
        + (* m = 0 *) rewrite add_0_r. simpl. reflexivity.
        + (* m = S m' *) simpl. rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. rewrite add_comm. reflexivity. 
Qed. 

            (* TODO SOLVE THIS LEMMA THEN PROVE BIG BOY LEMMA ADD_ASSOC *)

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
    induction n as [| n' IHn'].
    - (* n = 0 *) induction m as [| m' IHm'].
        + (* m = 0 *) induction p as [| p' IHp'].
            * (* p = 0 *) simpl. reflexivity.
            * (* p = S p' *)simpl. reflexivity.
        + (* m = S m' *) induction p as [| p' IHp'].
            * (* p = 0 *) simpl. reflexivity.
            * (* p = S p' *) simpl.  reflexivity.
    - (* n = S n' *) induction m as [| m' IHm'].
        + (* m = 0 *) induction p as [| p' IHp'].
            * (* p = 0 *) rewrite add_0_r. rewrite add_0_r. rewrite add_0_r. reflexivity.
            * (* p = S p' *) rewrite add_0_l. rewrite add_0_r. reflexivity.
        + (* m = S m' *) induction p as [| p' IHp'].
            * (* p = 0 *) rewrite add_0_r. rewrite add_0_r. reflexivity.
            * (* p = S p' *) simpl. rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. rewrite <- plus_n_Sm.
                rewrite IHn'.
                rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. simpl.  reflexivity.
Qed.

(* 2 stars *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  induction n as [| n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = S n' *) simpl. rewrite <- plus_n_Sm.  rewrite <- IHn'. reflexivity.
Qed. 

(* One inconvenient aspect of our definition of even n is the recursive call on n - 2. This makes proofs about even n harder when done by induction on n, since we may need an induction hypothesis about n - 2.
   The following lemma gives an alternative characterization of even *)

Fixpoint even (n:nat) :=
  match n with 
    | O => true 
    | S O => false 
    | S (S n') => even n' 
  end.   

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  induction n as [| n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = S n' *) rewrite IHn'. simpl. rewrite negb_involutive. reflexivity. 
Qed.

(* destruct and induction are different

induction is powerful for proving facts about inductively defined sets. 
destruct is simple, but does not work for arbitrary unknown numbers, since an arbirtary number  like n' cannot be simplified any further.  

*)


(* Proofs within proofs, subtheorems === inline proofs *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite H.
  reflexivity. Qed.

(*  assert introduces two sub-goals
  1. assertion itself.
  2. same goal before the assertion, with the added context of the subtheorem added 

  So assert generates one subgoal where we prove the asserted fact, and a second
  subgoal where we use the asserted fact to make progress on whatever we 
  were trying to prove in the first place. 
*)

  (* rewrite tactic is not very smart about where it applies the rewrite. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n). (* introduce a local lemma for the particular m and n values *)
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity. Qed.
  
(*"Informal proofs are algorithms; formal proofs are code."

What constitutes a successful proof of a mathematical claim? 
The question has challenged philosophers for millennia, 
but a rough and ready definition could be this: 
A proof of a mathematical proposition P is a written 
(or spoken) text that instills in the reader or hearer the 
certainty that P is true -- an unassailable argument for the 
truth of P. That is, a proof is an act of communication.

Acts of communication may involve different sorts of readers. On one hand, the "reader" can be a program like Coq, in which case the "belief" that is instilled is that P can be mechanically derived from a certain set of formal logical rules, and the proof is a recipe that guides the program in checking this fact. Such recipes are formal proofs.

Formal proofs are useful in many ways, but they are not very efficient ways of communicating ideas between human beings.


*)

  (* 3 stars *)

  Check add_assoc. 
  Check add_comm. 
Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. 
  rewrite add_assoc. 
  assert (H: m + (n + p) = m + n + p). 
    { rewrite add_assoc. reflexivity. }
  rewrite H. 
  assert (H2: m + n = n + m). 
    { rewrite add_comm. reflexivity. }
  rewrite H2. 
  reflexivity.
Qed. 

(* 
  n * (S m)

  hint: what's n * (1 + m) equal to? n + n * m
    add_com to get n * (m + 1) = n * m + n
*)

Theorem mul_1_plus : forall m n : nat, 
  (1 + n) * m = m + n * m. 
Proof. 
  intros m n. 
  simpl.  
  reflexivity.
Qed.   

Lemma mul_1 : forall n : nat, 
  n * 1 = n.
Proof. 
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.  
Qed. 

Check mult_n_Sm.
Check mul_0_r.
Check mul_1.
Theorem my_mult_n_Sm: forall (n m : nat),
    n * (S m) = n + n * m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  { reflexivity. }
  { simpl.
    rewrite -> IHn'.
    assert (swap: m + (n' + n' * m) = n' + (m + n' * m)).
      { rewrite -> add_shuffle3. reflexivity. }
    rewrite -> swap. 
    reflexivity.   
    }
Qed.

(* Theorem my_mult_n_Sm_2: forall (n m: nat), 
  n * m + n = n * S m. 
Proof. 
  intros n m. 
  assert (swap: n * m + n )
  rewrite add_comm. 

       *)
    
Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros n m. 
  induction n as [| n' IHn'].
  - (* n = 0 *) simpl. rewrite mul_0_r. reflexivity.
  - (* n = S n' *) rewrite my_mult_n_Sm. simpl. 

  (* FILL IN HERE *) Admitted.
