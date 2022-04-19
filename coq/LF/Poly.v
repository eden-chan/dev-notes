From LF Require Export Lists.
(* 
polymorphism (abstracting functions over the types of the data they manipulate) 
higher-order functions (treating functions as data).  
*)

(* Coq supports polymorphic inductive types *)
Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

(* list is a function from Types to Inductive definitions; 
or, to put it more concisely, list is a function from Types to Types. 
For any particular type X, the type list X is the Inductively defined 
set of lists whose elements are of type X. *)

Check list : Type -> Type. 
Check (nil nat) : list nat.
Check (cons nat 3 (nil nat)) : list nat.

(* What is nil's type? 
Intuitively, it is (X : Type) → list X. 
But Coq notation is represents it as follows. *)
Check nil : forall X : Type, list X.

Check cons : forall X : Type, X -> list X -> list X.
Check (cons nat 2 (cons nat 1 (nil nat)))
    : list nat. 

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.
Example test_repeat1 : repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)). Proof. reflexivity. Qed.
Example test_repeat2 : repeat bool false 1 = cons bool false (nil bool). Proof. reflexivity. Qed.

Module MumbleGrumble.
Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.
Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).

(* 
TODO: 
Which of the following are well-typed elements of grumble X for some type X? (Add YES or NO to each line.)
d (b a 5)           NO since it has to use the mumble constructor 
d mumble (b a 5)    YES. type grumble mumble. Uses mumble constructor, where (b a 5) is type mumble because (1 2 3) in the mumble constructor, b=1 matches, a=2 matches since a is a mumble type, and 5=3 matches since 5 is nat
d bool (b a 5)      NO, because (b a 5) expects to be a bool
e bool true         YES, type grumble bool
e mumble (b c 0)    YES, type grumble mumble
e bool (b c 0)      NO because it expocts (b c 0) to be bool
c                   YES, type mumble

*)
Check (grumble nat ).
Check (d nat).
Check (e nat).

Check (d mumble (b a 5)).
Check (e bool true).
Check (e mumble (b c 0)).
Check d mumble (b a 5). 

Check list nat. 
End MumbleGrumble.