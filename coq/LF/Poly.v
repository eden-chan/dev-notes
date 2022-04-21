From LF Require Export Lists.
(* 
polymorphism (abstracting functions over the types of the data they manipulate) 
higher-order functions (treating functions as data).  
*)
Definition odd (n:nat) :=
  (negb (even n)).
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


    (* Higher Order Functions *)

Definition doit3times {X : Type} (f : X->X) (n : X) : X :=
  f (f (f n)).
Check @doit3times : forall X : Type, (X -> X) -> X -> X.

Definition minustwo (n : nat) : nat :=
    (minus n 2).

Example test_doit3times: doit3times  minustwo 9 = 3. Proof. reflexivity. Qed.
Example test_doit3times': doit3times negb true = false. Proof. reflexivity. Qed.

Fixpoint filter {X : Type} (pred : X -> bool) (l : list X) : list X :=
    match l with 
        | [] => []
        | h :: t => match (pred h) with
                        | true => h :: (filter pred t) 
                        | false =>  (filter pred t)
                    end 
    end. 
Example test_filter1: filter even [1;2;3;4] = [2;4]. Proof. reflexivity. Qed.
Example test_filter2: filter negb [true;false;true] = [false]. Proof. reflexivity. Qed.
Example test_filter3: filter even [2;4;6] = [2;4;6]. Proof. reflexivity. Qed.
Example test_filter4: filter even [1;3;5] = []. Proof. reflexivity. Qed.
Example test_filter5: filter even [] = []. Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.
Example test_filter6:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ]. Proof. reflexivity. Qed.

    (* use lambda *)
Definition countoddmembers' (l:list nat) : nat :=
  length (filter (fun n => negb (even n)) l).
Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4. Proof. reflexivity. Qed.
Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0. Proof. reflexivity. Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0. Proof. reflexivity. Qed.
Example test_anon_fun': doit3times (fun n => n * n) 2 = 256. Proof. reflexivity. Qed.

Example test_filter6':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

    Definition filter_even_gt7 (l : list nat) : list nat:=
        filter (fun n => (andb (even n) (geb n 7))) l.
Example test_filter_even_gt7_1 : filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8]. Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 : filter_even_gt7 [5;2;6;19;129] = []. Proof. reflexivity. Qed.


Fixpoint partition' {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
    match l with 
      | [] => ([], [])
      | h::t => let t' := (partition' test t) in match (test h) with 
                                | true => (h::(fst t'), (snd t'))
                                | false => ((fst t'), h::(snd t'))
                                end
    end. 
Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X := ((filter test l),(filter (fun n => (negb (test n))) l)).

Example test_partition1: partition even [1;2;3;4;5] = ([2;4], [1;3;5] ).  Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).  Proof. reflexivity. Qed.

Fixpoint map { X Y : Type }  (f : X -> Y) (l : list X) : list Y :=
    match l with 
        | [] => []
        | h :: t => (f h) :: (map f t) 
    end. 
Definition mapf := fun n => (geb n 2). 
Example test_map0: (map mapf [1;2;3]) = [false;true;true].  Proof. reflexivity. Qed.
Example test_map3:
    map (fun n => [even n; (negb (even n))]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]]. Proof. reflexivity. Qed.


Lemma map_assoc : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X) ,
    (map f (l1 ++ l2)) = (map f l1) ++ (map f l2).
Proof. 
    intros X Y f l1 l2.
    induction l1 as [| n l1' IHl1'].
    - (* l1 = [] *)
        reflexivity.
    - (* l1 = n :: l1' *)
        simpl. rewrite IHl1'. reflexivity.
Qed. 


Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l. 
  induction l as [| n l' IHl'].
  - (* l = [] *)
    reflexivity.
  - (* l = n :: l' *)
    simpl. rewrite <- IHl'.  rewrite map_assoc. simpl. reflexivity.
Qed. 

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : list Y := 
match l with 
    | [] => []
    | h :: t => (f h) ++ flat_map f t
    end.  

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4]. Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

  (* 
  Intuitively, the behavior of the fold operation is to insert a given binary operator f between every pair of elements in a given list. For example, fold plus [1;2;3;4] intuitively means 1+2+3+4. To make this precise, we also need a "starting element" that serves as the initial second input to f. So, for example,
       fold plus [1;2;3;4] 0
yields
       1 + (2 + (3 + (4 + 0))).
  *)
Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Example fold_example1 : fold mult [1;2;3;4] 1 = 24. Proof. reflexivity. Qed. 
    (* FOLD LEFT
    1 * (2 * (3 * (4 * 1)))
    *)
Example fold_example2 :fold andb [true;true;false;true] true = false. Proof. reflexivity. Qed.
Example fold_example3 :fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4]. Proof. reflexivity. Qed.

Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k:nat) => x.
Definition ftrue := constfun true.
Example constfun_example1 : ftrue 0 = true. Proof. reflexivity. Qed.
Example constfun_example2 : (constfun 5) 99 = 5. Proof. reflexivity. Qed.
(* "plus is a one-argument function that takes a nat and returns a one-argument function that takes another nat and returns a nat."
  RIGHT ASSOCIATIVE / PARTIAL APPLICATION *)

Definition plus3 := plus 3.
Check plus3 : nat -> nat.
Example test_plus3 :    plus3 4 = 7. Proof. reflexivity. Qed.
Example test_plus3' :   doit3times plus3 0 = 9. Proof. reflexivity. Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9. Proof. reflexivity. Qed.

Module Exercises.
Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3. Proof. reflexivity. Qed.

Lemma fold_length_Sn : forall X (l : list X) (n : X),
  fold_length (n :: l) = S (fold_length l).
Proof. 
  (* intros X l n. *)
  reflexivity.
  (* induction l as [| n' l' IHl'].
  - (* l = [] *)
    reflexivity.
  - (* l = n' :: l' *)
    simpl. reflexivity. *)
Qed. 
Lemma fold_length_assoc : forall X (l1 l2 : list X),
  fold_length (l1 ++ l2) = fold_length l1 + fold_length l2.
Proof. 
  intros X l1 l2. 
  induction l1 as [| n l1' IHl1'].
  - (* l1 = [] *)
    reflexivity.
  - (* l1 = n :: l1' *)
    assert (H: (n :: l1') ++ l2 = n :: (l1' ++ l2)). 
      { reflexivity.  }
    rewrite H. 
    rewrite fold_length_Sn. 
    rewrite fold_length_Sn. 
    rewrite IHl1'. 
    reflexivity.
Qed. 

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l. 
  induction l as [| n l' IHl'].
  - (* l = [] *)
    reflexivity.
  - (* l = n :: l' *)
    simpl. rewrite <- IHl'. 
    rewrite fold_length_Sn. reflexivity.
Qed. 
Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold (fun a b => f a :: b) l []. 

Example test_map0: map mapf [1;2;3] = fold_map mapf [1;2;3].  Proof. reflexivity. Qed.
  (* [false;true;true] *)
Example test_map3:
    map (fun n => [even n; (negb (even n))]) [2;1;2;5]
  = fold_map (fun n => [even n; (negb (even n))]) [2;1;2;5]. Proof. reflexivity. Qed.
(*   [[true;false];[false;true];[true;false];[false;true]] *)

Theorem fold_map_correct: forall X Y (f : X -> Y) (l : list X), 
  fold_map f l = map f l. 
Proof. 
  intros X Y f l. 
  induction l as [| n l' IHl'].
  - (* l = [] *)
    reflexivity.
  - (* l = n :: l' *)
    simpl. 
    assert (H : fold_map f (n :: l') = f n :: fold_map f l' ).
    { reflexivity. } 
    rewrite H. 
    rewrite IHl'. 
    reflexivity.
Qed. 
(* f h (fold f t b) *)

(* In Coq, a function f : A → B → C really has the 
type A → (B → C). That is, if you give f a value of type A,
 it will give you function f' : B → C. If you then give 
 f' a value of type B, it will return a value of type C. 
 This allows for partial application, as in plus3. 
 Processing a list of arguments with functions that 
 return functions is called currying, in honor of the 
 logician Haskell Curry.
Conversely, we can reinterpret the type A → B → C as 
(A * B) → C. This is called uncurrying. With an uncurried 
binary function, both arguments must be given at once as 
a pair; there is no partial application.
 *)
Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).
Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

(* Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5]. Proof. reflexivity. Qed. *)
Example test_map1': map (plus 3) [2;0;2] = [5;3;5]. Proof. reflexivity. Qed.
Example test_curry_inverse :  prod_curry (prod_uncurry plus) 1 2 = plus 1 2. Proof. reflexivity. Qed.
Check @prod_curry.
(* forall X Y Z : Type, (X * Y -> Z) -> X -> Y -> Z *)
Check @prod_uncurry.
(* forall X Y Z : Type, (X -> Y -> Z) -> X * Y -> Z  *)
Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  reflexivity. 
Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p. 
  destruct p as [x y].
  reflexivity. 
Qed. 

Module Church.
(* 
Church numerals, named after mathematician Alonzo Church, are 
an alternate way of defining natural number n as a function 
that takes a function f as a parameter and returns f iterated n times.
*)
Definition cnat := forall X : Type, (X -> X) -> X -> X.
Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.
Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).
Definition three : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f (f x)).
(*
Defining zero is somewhat trickier: 
how can we "apply a function zero times"? 
The answer is actually simple: just return the argument untouched.
*)
Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.
Definition succ (n : cnat) : cnat :=
    fun (X : Type) (f : X -> X) (x : X) => f (n _ f x).

Example succ_1 : succ zero = one. Proof. reflexivity. Qed.
Example succ_2 : succ one = two. Proof. reflexivity. Qed.
Example succ_3 : succ two = three. Proof. reflexivity. Qed.

(* 
TODO
Definition pred (n : cnat) : cnat :=
    match n with 
      | zero => zero 
      | one => one
    end. 
    
    fun X f x => f (n _ f x).

Example pred_1 : pred zero = zero. Proof. reflexivity. Qed.
Example pred_2 : pred one = zero. Proof. reflexivity. Qed.
Example pred_3 : pred two = one. Proof. reflexivity. Qed.       *)
  
Definition plus (n m : cnat) : cnat :=
  fun X f x => n _ f (m _ f x).

Example plus_1 : plus zero one = one. Proof. reflexivity. Qed. 
Example plus_2 : plus two three = plus three two. Proof. reflexivity. Qed.
Example plus_3 :
  plus (plus two two) three = plus one (plus three three). Proof. reflexivity. Qed.

Check plus one. 
Check succ. 
Check cnat.

Definition mult (n m : cnat) : cnat :=
    fun _ f x => n _ (m _ f) x.

Example mult_1 : mult one one = one. Proof. reflexivity. Qed.
Example mult_2 : mult zero (plus three three) = zero. Proof. reflexivity. Qed.
Example mult_3 : mult two three = plus three three. Proof. reflexivity. Qed.

Definition exp (n m : cnat) : cnat :=
  (* fun _ f => m _ ((n _ f)) .  *)
  fun X => m (X -> X) (n X).
 


Example exp_1 : exp two two = plus two two. Proof. reflexivity. Qed.
Example exp_2 : exp three zero = one. Proof. reflexivity. Qed.
Example exp_3 : exp three two = plus (mult two (mult two two)) one. Proof. reflexivity. Qed.
End Church. 
End Exercises. 
