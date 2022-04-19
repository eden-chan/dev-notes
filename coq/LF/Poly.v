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

    (* Supplying Type Arguments Explicitly *)
Definition mynil : list nat := nil.

(* Alternatively, we can force the implicit arguments to
 be explicit by prefixing the function name with @. *)
Check nil. 
Check @nil : forall X : Type, list X.
Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123''' := [1; 2; 3].

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
 intros X l.
 induction l as [| n l' IHl']. 
 - (* l = [] *)
    reflexivity.
 - (* l = n :: l' *)
    simpl. rewrite IHl'. reflexivity.
Qed.  

Theorem app_assoc : forall (X: Type), forall (l m n: list X),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
    intros X l m n. 
    induction l as [| x l' IHl'].
    - (* l = [] *)
        simpl. reflexivity.
    - (* l = n :: l'*)
        simpl. rewrite <- IHl'. reflexivity.
Qed. 

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
    intros X l1 l2.
    induction l1 as [| n l1' IHl1'].
    - (* l1 = [] *)
        reflexivity.
    - (* l1 = n :: l1' *)
        simpl. rewrite IHl1'. reflexivity. 
Qed. 

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
    intros X l1 l2. 
    induction l1 as [| n l1' IHl1' ].
    - (* l1 = [] *)
        simpl. rewrite app_nil_r. reflexivity.
    - (* l1 = n :: l1' *)
        simpl. rewrite IHl1'. rewrite <- app_assoc. reflexivity.
Qed. 

Theorem rev_involutive : forall (X : Type), forall (l : list X),
  rev (rev l) = l.
Proof.
    intros X l. 
    induction l as [| n l' IHl'].
    - (* l = [] *)
        reflexivity.
    - (* l = n :: l' *)
        simpl. rewrite rev_app_distr. rewrite IHl'. simpl. reflexivity.
Qed. 

(*  Polymorphic Pairs  *)
Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).
Arguments pair {X} {Y}.
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.
(* type_scope tells Coq that this abbreviation should only be used when parsing types, not when parsing expressions.  *)

(* 
It is easy at first to get (x,y) and X * Y confused. Remember that (x,y) is a value built from two other values, while X * Y is a type built from two other types. If x has type X and y has type Y, then (x,y) has type X * Y. 
*)
Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.
Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.    

(* often called zip, but calling it combine to be consistent with coq's stdlib  *)
Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
        : list (X*Y) :=
match lx, ly with
    | [], _ => []
    | _, [] => []
    | x :: tx, y :: ty => (x, y) :: (combine tx ty)
end.
Compute (combine [1;2] [false;false;true;true]).
(* [(1, false);(2, false)] *)


(* USEFUL *)
(* also known as unzip  *)
Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y):=
    match l with 
        | [] => ([],[])
        | (x, y) :: t => let t' := split t in (x::(fst t'), (y::(snd t')))
    end. 

Example test_split0: split [(1,false);(2,false)] = ([1;2],[false;false]). Proof. reflexivity. Qed.
Example test_split2: let t' := split [(1,false);(2,false)] in combine (fst t') (snd t') = [(1,false);(2,false)]. Proof. reflexivity. Qed.

Module OptionPlayground.
Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.
Arguments Some {X}.
Arguments None {X}.
End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4. Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2]. Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None. Proof. reflexivity. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
    match l with 
        | [] => None 
        | h::t => Some h 
    end. 

    (* Force implicit arguments to be explicit *)
Check @hd_error : forall X : Type, list X -> option X.
Example test_hd_error1 : hd_error [1;2] = Some 1. Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1]. Proof. reflexivity. Qed.
