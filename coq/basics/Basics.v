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

(* Compute (next_weekday friday). *)
(* ==> monday : day *)
(* Compute (next_weekday (next_weekday saturday)). *)
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


(* Infix syntax for boolean operators *)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.


(* If then else syntax *)
Definition negb' (b:bool) : bool :=
  if b then false
  else true.
Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.
Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.

Example test_andb1: (andb true true) = true. 
Proof. simpl. reflexivity. Qed.  
Example test_andb2: (andb true false) = false. 
Proof. simpl. reflexivity. Qed.  
Example test_andb3: (andb false true) = false. 
Proof. simpl. reflexivity. Qed.  
Example test_andb4: (andb false false) = false. 
Proof. simpl. reflexivity. Qed.  


(*  exercise 1 star *)
Definition nandb (b1 : bool) (b2 : bool) : bool := 
  (negb (andb b1 b2)). 
Example test_nandb1:               (nandb true false) = true.
Proof. simpl. reflexivity. Qed.  
Example test_nandb2:               (nandb false false) = true.
Proof. simpl. reflexivity. Qed.  
Example test_nandb3:               (nandb false true) = true.
Proof. simpl. reflexivity. Qed.  
Example test_nandb4:               (nandb true true) = false.
Proof. simpl. reflexivity. Qed.  

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  (andb b1 (andb b2 b3)).
Example test_andb31:                 (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed. 
Example test_andb32:                 (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed. 
Example test_andb33:                 (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed. 
Example test_andb34:                 (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed. 

(* Types *)

Check true.
(* ===> true : bool *)

(* If followed by colon and a type, Coq will verify match, and halt with error if not *)
Check true
  : bool.
Check (negb true)
  : bool.
(* Check (negb true)  *)
  (* : day.  *)
(* ==> The term "negb true" has type "bool" while it is expected to have type "day". *)

Check negb 
 : bool -> bool. 
Check andb 
  : bool -> bool -> bool. 
Check andb3 
  : bool -> bool -> bool -> bool. 



(* 
An Inductive definition does two things:
It defines a set of new constructors. E.g., red, primary, true, false, monday, etc. are constructors.
It groups them into a new named type, like bool, rgb, or color.
 
Constructor expressions are formed by applying a constructor 
to zero or more other constructors or constructor expressions
matching the structure of the definition


red, green, and blue belong to the set rgb;
black and white belong to the set color;
if p is a constructor expression belonging to the set rgb, 
then primary p (pronounced "the constructor primary applied to the argument p")
is a constructor expression belonging to the set color; and
constructor expressions formed in these ways are the only ones belonging
to the sets rgb and color.
*)
Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.
Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.
(* 
Modules

Coq provides a module system to aid in organizing large developments.
We won't need most of its features, but one is useful: 
If we enclose a collection of declarations between Module X and End X markers, 
then, in the remainder of the file after the End, these definitions are referred
to by names like X.foo instead of just foo. 
We will use this feature to limit the scope of definitions, 
so that we are free to reuse names.
*)

Module Playground.
  Definition b : rgb := blue.
End Playground.
Definition b : bool := true.
Check Playground.b : rgb.
Check b : bool.
