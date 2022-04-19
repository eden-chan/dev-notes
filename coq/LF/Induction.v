(* 
coq_makefile -f _CoqProject *.v -o Makefile
make <file.vo>
*)
From LF Require Export Basics.

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

Theorem add_assoc_abc : forall a b c: nat, 
  a + b + c = a + (b + c). 
Proof. 
  intros a b c.
  rewrite add_assoc. 
  reflexivity.
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

Theorem add_shuffle_bac : forall n m p : nat,
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

Theorem add_shuffle_acb: forall a b c : nat, 
  a + (b + c) = a + (c + b).
Proof.
  intros a b c. 
  assert (H: b + c = c + b).
  { rewrite add_comm. reflexivity. }
  rewrite H. 
  reflexivity.
Qed.

Theorem add_shuffle_cba: forall a b c : nat, 
  a + (b + c) = c + (b + a).
Proof.
  intros a b c. 
  rewrite add_shuffle_acb. 
  rewrite add_shuffle_bac. 
  rewrite add_shuffle_acb. 
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


Theorem my_mult_n_Sm: forall (n m : nat),
    n * (S m) = n + n * m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  { reflexivity. }
  { simpl.
    rewrite -> IHn'.
    assert (swap: m + (n' + n' * m) = n' + (m + n' * m)).
      { rewrite -> add_shuffle_bac. reflexivity. }
    rewrite -> swap. 
    reflexivity.   
    }
Qed.

    
Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros n m. 
  induction n as [| n' IHn'].
  - (* n = 0 *) simpl. rewrite mul_0_r. reflexivity.
  - (* n = S n' *) simpl. rewrite my_mult_n_Sm.  rewrite IHn'. reflexivity.
Qed. 



Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed. 

Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  intros n.  simpl. reflexivity. Qed. 

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b. destruct b. 
  - reflexivity.
  - reflexivity.
Qed. 
Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p. 
  intros H. 
  induction p as [| p' IHp'].
  - simpl. rewrite H. reflexivity.
  - simpl. rewrite IHp'. reflexivity. 
Qed. 
Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  reflexivity. Qed. 
Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite add_0_r. reflexivity.
Qed. 
Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros [] [].
  - reflexivity.  
  - reflexivity.  
  - reflexivity.  
  - reflexivity.  
Qed. 



Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
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
            * (* p = 0 *) rewrite add_0_r. rewrite mul_0_r. reflexivity.
            * (* p = S p' *) rewrite add_0_r. rewrite mult_0_l. rewrite add_0_r. reflexivity.
        + (* m = S m' *) induction p as [| p' IHp'].
          * (* p = 0 *) rewrite mul_0_r. rewrite mul_0_r. rewrite mul_0_r. reflexivity. 
          * (* p = S p' *) rewrite <- mult_n_Sm. rewrite IHp'. 
              (* move terms to match n * m + n = n * Sm *)
             rewrite add_shuffle_acb.
             rewrite add_assoc. 
             rewrite  add_comm. 
            rewrite <- mult_n_Sm.
              rewrite <- mult_n_Sm.
                rewrite add_assoc. 
                rewrite add_assoc. 
                rewrite add_assoc.
                assert (swap: S n' + S n' * p' = S n' * p' + S n').
                { rewrite add_comm. reflexivity. } 
                rewrite swap. 
                  reflexivity.
Qed. 

Theorem mult_plus_distr_l : forall n m p: nat, 
  p * (n + m) = (n * p) + (m * p).
Proof. 
  intros n m p.
  rewrite mul_comm. 
  rewrite mult_plus_distr_r.  
  reflexivity.
Qed. 

Theorem mult_n_Sm_l: forall n m : nat,
  m * n + n = n * S m.
Proof. 
  intros n m.
  rewrite mul_comm. 
  rewrite mult_n_Sm. 
  reflexivity.
Qed. 

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
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
              * (* p = 0 *) simpl. rewrite mul_0_r. reflexivity.
              * (* p = S p' *) simpl. rewrite mul_0_r. simpl. reflexivity. 
          + (* m = S m' *) induction p as [| p' IHp'].
            * (* p = 0 *) rewrite mul_0_r. rewrite mul_0_r. rewrite mul_0_r. reflexivity. 
            * (* p = S p' *)  
              rewrite <- mult_n_Sm. rewrite mult_plus_distr_l. 
              rewrite mul_comm. 
              rewrite IHp'. 
              rewrite mul_comm. 
              assert (swap: S m' * S n' = S n' * S m').
              { rewrite mul_comm. reflexivity. }
              rewrite swap. 
              rewrite <- mult_n_Sm. 
              rewrite mult_n_Sm_l.
              reflexivity. 
Qed.


(* 3 stars *)
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m:bin) : bin := 
  match m with 
    | Z => B1 Z 
    | B1 m' => B0 (incr m')
    | B0 m' => B1 m' 
  end. 

Fixpoint bin_to_nat (m:bin) : nat := 
  match m with 
    | Z => 0
    | B1 m' => 1 + (2 * bin_to_nat m') 
    | B0 m' => (2 * bin_to_nat m') 
  end. 


(* 3 stars USEFUL  *)
(* 
Prove that the following diagram commutes:
                        incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S

*)


Lemma S_S: forall a b: nat, 
   S (a + S b) = S (S (a + b)).
Proof.
  intros a b. 
  rewrite add_comm.
  simpl.  
  rewrite add_comm.
  reflexivity.
Qed.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  induction b as [| b1 IHb1 | b1 IHb1].
  - simpl. reflexivity.
  - simpl. rewrite add_0_r. reflexivity.
  - simpl. rewrite add_0_r. rewrite add_0_r. rewrite IHb1. simpl. rewrite S_S.  reflexivity.
Qed. 

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with 
    | O => Z 
    | S n' => incr (nat_to_bin n')
  end. 
  

Example test_nat_to_bin0 : nat_to_bin 0 = Z. Proof. reflexivity. Qed. 
Example test_nat_to_bin1 : nat_to_bin 1 = B1 Z. Proof. reflexivity. Qed. 
Example test_nat_to_bin2 : nat_to_bin 2 = B0 (B1 Z). Proof. reflexivity. Qed. 
Example test_nat_to_bin3 : nat_to_bin 3 = B1 (B1 Z). Proof. reflexivity. Qed. 

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  induction n as [| n' IHn']. 
  - simpl. reflexivity. 
  - simpl. rewrite bin_to_nat_pres_incr. simpl. rewrite IHn'. reflexivity.
Qed. 


(* Bin to Nat and Back to Bin (Advanced) *)
Lemma double_incr : forall n : nat, 
  double (S n) = S (S (double n)).
Proof.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed. 

(* prolly wrong, use Definition one liner instead. *)
Fixpoint double_bin (b:bin) : bin:= 
  match b with 
  | Z => Z 
  | B1 b' =>  (B0 (double_bin b'))
  | B0 b' =>  double_bin b'
end. 

(* Example double_bin_zero : double_bin Z = Z. Proof. reflexivity. Qed. 
Example double_bin_1 : double_bin (B1 Z) = (B0 (B1 Z)). Proof. reflexivity. Qed. 
Example double_bin_2 : double_bin (B0 (B1 Z)) = (B0 (B0 (B1 Z))). Proof. reflexivity. Qed. 
Example double_bin_3 : double_bin (B1 (B1 Z)) = (B0 (B1 (B1 Z))). Proof. reflexivity. Qed. 
Example double_bin_4 : double_bin (B0 (B0 (B1 Z))) = (B0 (B0 (B0 (B1 Z)))). Proof. reflexivity. Qed. 
 *)


Lemma double_incr_bin : forall b:bin,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  Abort.
