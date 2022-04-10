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

Module TuplePlayground.

Inductive bit : Type :=
  | B0
  | B1.
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).
Check (bits B1 B0 B1 B0)
  : nybble.

(*
the bits constructor is a wrapper for its contents
unwrapping can be done by pattern-matching
Use underscore ( _ ) as a wildcard  pattern to avoid inventing variable 
names that aren't used. 
*)
Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.
Example all_zero_test1: (all_zero (bits B1 B0 B1 B0)) = false.
Proof. simpl. reflexivity. Qed.
Example all_zero_test2: (all_zero (bits B0 B0 B0 B0)) = true.
Proof. simpl. reflexivity. Qed.
End TuplePlayground.

(* Use module so it doesn't conflict with later usages of Nats from stdlib *)
Module NatPlayground.


(* 
there is a representation of numbers that is even simpler than binary, namely unary (base 1)
 *)

 Inductive nat : Type :=
  | O            (* capital letter O stands for zero *)
  | S (n : nat). (* S stands for successor *)


(* This is just a representation of numbers: a way of writing them down
The names S and O are arbitrary, and at this point they have no special meaning
-- they are just two different marks that we can use to write down numbers (together with a rule that says any nat will be written as some string of S marks followed by an O).
If we like, we can write essentially the same definition this way: *)
Inductive nat' : Type :=
  | stop
  | tick (foo : nat').

(*
The interpretation of these marks comes from how we use them to compute.
*)

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

(* Since natural numbers are such a pervasive form of data, 
Coq has built-in parser and printer for them, 
printing numbers in decimal by default.  *)
Check (S (S (S (S O)))).
(* ===> 4 : nat *)
Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.
Example minus_two_test: (minustwo (S (S (S (S O))))) = (S (S O)).
Proof. simpl. reflexivity. Qed.

Check S        : nat -> nat.
Check pred     : nat -> nat.
Check minustwo : nat -> nat.

(* 
However, there is a fundamental difference between S and the other two: 
functions like pred and minustwo are defined by giving computation rules 
-- e.g., the definition of pred says that pred 2 can be simplified to 1 --
while the definition of S has no such behavior attached. 
Although it is like a function in the sense that it can be applied to 
an argument, it does not do anything at all! It is just a way
of writing down numbers. *)

(* 
For most interesting computations involving numbers, 
simple pattern matching is not enough: we also need recursion.  
Such functions are introduced using the keyword Fixpoint instead of Definition. 
*)

Fixpoint even (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => even n'
  end.
(* We can define odd in a similar way, but basing it off even is simpler *)
Definition odd (n:nat) : bool :=
  negb (even n).

Example test_odd1:    odd (S O) = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2:    odd (S (S (S (S O)))) = false.
Proof. simpl. reflexivity. Qed.

(* Multi-argument functions by recursion *)
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m) (* Predicate (S n' => n') *)
  end.

Example test_add1: (plus (S (S (S O))) (S (S O))) = (S (S (S (S (S O))))).
Proof. simpl. reflexivity. Qed.

(* ===> 5 : nat *)
(*      plus 3 2
   i.e. plus (S (S (S O))) (S (S O))
    ==> S (plus (S (S O)) (S (S O)))
          by the second clause of the match
    ==> S (S (plus (S O) (S (S O))))
          by the second clause of the match
    ==> S (S (S (plus O (S (S O)))))
          by the second clause of the match
    ==> S (S (S (S (S O))))
          by the first clause of the match
   i.e. 5  *)

(* 
As a notational convenience, if two or more arguments have the same type, 
they can be written together. In the following definition, (n m : nat)
means just the same as if we had written (n : nat) (m : nat).
*)
Fixpoint mult (n m : nat) : nat := 
    match n with 
      | O => O 
      | S n' => (plus m (mult n' m))
    end.

Example test_mult1: (mult (S (S O)) (S (S O))) = (S (S (S (S O)))).
Proof. simpl. reflexivity. Qed.

(* Match two expressions at once with a comma between them *)
Fixpoint minus (n m : nat) : nat :=
  match n, m with 
    | O, _ => O 
    | S _, O => O
    | S n', S m' => minus n' m'
  end.
  
Example test_minus1: (minus O O) = O.
Proof. simpl. reflexivity. Qed.
Example test_minus2: (minus (S O) O) = O.
Proof. simpl. reflexivity. Qed.
Example test_minus3: (minus (S O) (S O)) = O.
Proof. simpl. reflexivity. Qed.

Fixpoint exp (base power : nat) : nat :=
  match base, power with 
    | _, O => S O 
    | O, _ => O 
    | base, S power' => mult base (exp base power') 
  end. 

Example test_exp0: exp O (S O) = O.
Proof. simpl. reflexivity. Qed.
Example test_exp1: exp O O = S O.
Proof. simpl. reflexivity. Qed.
Example test_exp2: exp (S O) O = S O.
Proof. simpl. reflexivity. Qed.
Example test_exp3: exp (S (S O)) (S (S (S O))) = (S (S (S (S (S (S (S (S O)))))))).
Proof. simpl. reflexivity. Qed.

Fixpoint factorial (n : nat) : nat :=
  match n with 
    | O => S O 
    | S n' => mult n (factorial n')
  end. 

Example test_factorial0: factorial O = S O. 
Proof. simpl. reflexivity. Qed.
Example test_factorial1: factorial( S O) = S O. 
Proof. simpl. reflexivity. Qed.
Example test_factorial2: factorial (S (S O)) = S (S O). 
Proof. simpl. reflexivity. Qed.
Example test_factorial3: factorial (S (S (S O))) = S (S (S (S (S (S O))))). 
Proof. simpl. reflexivity. Qed.

Check factorial.
End NatPlayground.

(* Note the use of nested matches (we could also have used a simultaneous match, as we did in minus.) *)
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.
