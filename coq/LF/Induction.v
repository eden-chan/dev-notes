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
        + (* m = S m' *) simpl.  rewrite <- IHn'. \rewrite <- IHn'. rewrite <- IHn'. reflexivity.  
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
        + (* m = S m' *)  Abort.

            (* TODO SOLVE THIS LEMMA THEN PROVE BIG BOY LEMMA ADD_ASSOC *)


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
                rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. 