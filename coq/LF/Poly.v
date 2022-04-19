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

(* Type Annotation Inference *)
Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.
Check repeat'
  : forall X : Type, X -> nat -> list X.
Check repeat
  : forall X : Type, X -> nat -> list X.

(* when Coq encounters a "hole" represented by underscore character _, 
it will attempt to unify all locally available information
 -- the type of the function being applied, the types of the other arguments, 
and the type expected by the context in which the application appears -- to determine 
    what concrete type should replace the _.
     *)
Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* Implicit Arguments *)

(* The Arguments directive specifies the name of the function (or constructor) 
and then lists the (leading) argument names to be treated as implicit, each surrounded by curly braces. *)
Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

(* No need to supply type arg since it's explicitly told to be treated implict with Arguments declaration *)
Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

(* But don't make everything implicit. Consider the following list'  *)
Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').
(* Because X is declared as implicit for the entire 
inductive definition including list' itself, we now 
have to write just list' whether we are talking about 
lists of numbers or booleans or anything else, rather than 
list' nat or list' bool or whatever; this is a step too far. *)

(* So let's stick with our original implementation of list but with 
the Arguments for nil, cons defined to treat their leading terms as implicit *)

(* So we explicitly supply the generic type arg X for the list constructor, but not for the function type arg *)
Fixpoint app {X : Type} (l1 l2 : list X) : list X  := 
    match l1 with 
    | nil => l2 
        | cons h t => cons h (app t l2)
    end.  
Fixpoint rev {X : Type} (l : list X) : list X := 
    match l with 
        | nil => nil 
        | cons h t => app (rev t ) (cons h nil)
    end. 
Fixpoint length {X : Type} (l : list X) : nat :=
    match l with 
        | nil => 0
        | cons _ t => 1 + length t 
    end. 

Example test_rev1 : rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)). Proof. reflexivity. Qed.
Example test_rev2: rev (cons true nil) = cons true nil. Proof. reflexivity. Qed.
Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3. Proof. reflexivity. Qed.
