Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.
  
Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

Compute (next_weekday friday).
(* ==> monday : day *)
Compute (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.


Example test_next_two_weekday: 
  (next_weekday (next_weekday monday)) =  wednesday .
Proof. simpl. reflexivity. Qed.

From Coq Require Export String.


(* Booleans *)

Inductive bool : Type := 
  | true
  | false. 

Definition negb (b:bool) : bool := 
  match b with 
  | true => false 
  | false => true
  end.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with 
  | true => b2 
  | false => false 
  end. 

Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with 
  | true => true 
  | false => b2 
  end. 

Example test_orb1: (orb true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (b:bool) : bool :=
  if b then false
  else true.
Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.
Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.