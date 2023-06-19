Set Implicit Arguments.

Require Import Setoid.
Require Import Omega.
Require Import List.
Import ListNotations.
Require Import Ring.
Import Arith.

Inductive A : Type :=
  | O : A
  | I : A.

Definition And (x y : A) : A :=
match x with
  | O => O
  | I => y
end.

Definition Or (x y : A) : A :=
match x with
  | O => y
  | I => I
end.

Definition Not (x : A) : A :=
match x with
  | O => I
  | I => O
end.

(* -------------------------------------------------------- *)
  
Fixpoint andL (X Y: list A): list A := 
  match X, Y with
    | [ ], _ => [ ]
    | _, [ ] => [ ]
    | x :: tailX, y :: tailY => And x y :: andL tailX tailY
end.

Compute andL [I;O;I] [I;I;O].

Fixpoint orL (X Y: list A): list A :=
  match X, Y with
    | [ ], _ => [ ]
    | _, [ ] => [ ]
    | x :: X', y :: Y' => Or x y :: orL X' Y'
end.

Fixpoint notL (X: list A): list A :=
  match X with
    | [ ] => [ ]
    | x :: X' => Not x :: notL X' 
end.


Fixpoint repeat (X: Type)(x : X)(n : nat):list X:=
  match n with
    | 0 => []
    | S n' => [x] ++ repeat x n'
end.
Compute repeat 2 5.

Fixpoint myRev (X : Type)(A: list X): list X :=
  match A with
    | [] => []
    | x :: A' => myRev A' ++ [x]
end.

(* Compute rev [1;2;3]. *)

(* -------------- C) -------------- *)
Lemma pomoc (X : Type)(b: list X)(n :nat):
  repeat b n ++ [ b ] = b :: repeat b n.
Proof. 
  induction n; simpl.
    - reflexivity.
    - rewrite IHn. reflexivity.
Qed.

Lemma L1 (X : Type)(n: nat)(b : list X):
  rev(repeat b n) = repeat b n.
Proof. induction n; simpl. 
  -  reflexivity.
  - rewrite IHn. rewrite pomoc. reflexivity.
Qed.

(* -------------- D) -------------- *)

Notation "| A |" := (length A)(at level 70).

Lemma pomoc1 (a: A)(u : list A): 
  And a I :: u = a :: u.
Proof. induction a; simpl; reflexivity. Qed.

Goal forall (u : list A), andL u (repeat (I) (| u |)) = u.
Proof. induction u; simpl.
  - reflexivity.
  - rewrite IHu. rewrite pomoc1. reflexivity. 
Qed.
(* -------------- E) -------------- *)

Goal forall (n : nat), notL (repeat O n) = repeat I n. 
Proof. induction n; simpl.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

(* -------------- F) -------------- *)

Lemma deM x y: Not (And x y) = Or (Not x) (Not y) . 
Proof. destruct x, y; simpl; reflexivity. Qed.


Goal forall (n v: list A), notL (andL v n) = orL (notL v)(notL n).
Proof. induction n; simpl.
  - induction v; simpl; reflexivity.
  - induction v. simpl.
    + reflexivity.
    + simpl. rewrite IHn. rewrite deM. reflexivity. 
Qed.

(* -------------- G) -------------- *)


Lemma pomoc2 (u : A):
  Not(Not u) = u.
Proof. destruct u; reflexivity. Qed.


Goal forall u: list A, notL(notL u) = u.
Proof. induction u; simpl.
 - reflexivity.
  - rewrite IHu. rewrite pomoc2. reflexivity.
Qed.

(* -------------- 2. Zadatak -------------- *)

Fixpoint map (X Y: Type)(f: X -> Y)(L: list X): list Y :=
  match L with
    | [] => []
    | x :: xs => f x :: map f xs
end.

(* -------------- C) -------------- *)
Fixpoint djeljiv_3 (n: nat) : bool :=
  match n with
    | 0 => true
    | 1 => false
    | 2 => false 
    | S( S (S n')) => djeljiv_3 (n') 
end.

Compute djeljiv_3 31.

Definition map_i2b (l: list nat): list bool:=
  map djeljiv_3 l.


Lemma mapF (X Y: Type)(f: X -> Y)(p q : list X): 
  map f (p ++ q) = map f p ++ map f q.
Proof. induction p as [| x xs]. simpl.
    - reflexivity.
    - simpl. rewrite IHxs. reflexivity.
Qed. 

(* -------------- 3. Zadatak -------------- *)
Fixpoint foldr (X Y: Type)(f: X -> Y -> Y)(y : Y)(l : list X): Y :=
match l with 
  | [] => y
  | x :: xs => f x (foldr f y xs)
end.



















