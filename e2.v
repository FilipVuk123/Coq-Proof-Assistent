Require Import Setoid.


Fixpoint plus (x y: nat): nat :=
  match x with
    | O => y
    | S x' => S (plus x' y)
end.

(* Compute plus 5 1. *)

Fixpoint mult (x y:nat):nat :=
  match x with
    | O => O
    | S x' => plus y (mult x' y)
end.

(* Compute mult 3 2. *)

Fixpoint pow (x n:nat):nat :=
  match n with
    | O => S O
    | S n' => mult x (pow x n')
end.

Lemma plus_O (x y:nat) :  plus x O = x.
Proof. induction x; simpl. 
  - reflexivity. 
  - rewrite IHx. reflexivity. 
Qed.
(* Compute pow 10 2. *)

Lemma plus_S (x y:nat) :  plus x (S y) = S (plus x y).
Proof. induction x; simpl. 
  - reflexivity.
  - rewrite IHx. reflexivity. 
Qed.

(* a) *)
Lemma plus_asso (x y z: nat) : plus (plus x y) z = plus x (plus y z).
Proof. 
  - induction x; simpl. reflexivity. rewrite IHx. reflexivity. Qed.

Lemma plus_com (x y: nat) : plus x y = plus y x.
Proof.
  induction x; simpl.
  rewrite plus_O. reflexivity. exact y.
  rewrite plus_S. rewrite IHx. reflexivity.
Qed.


Lemma mult_dist (x y z: nat) :
  mult (plus x y) z = plus (mult x z) (mult y z).
Proof.
  induction x; simpl.
    - reflexivity.
    - rewrite plus_asso. rewrite IHx. reflexivity.
Qed.

Lemma mult_O (x:nat) : mult x O = O.
  Proof.
     induction x; simpl.
      - reflexivity.
      - rewrite IHx. reflexivity.
Qed.

Lemma mult_S (x y:nat) : mult x (S y) = plus (mult x y) x.
  Proof.
     induction x; simpl.
      - reflexivity.
      - rewrite plus_S. rewrite IHx. rewrite plus_asso. reflexivity.
Qed.

Lemma mult_asso (x y z: nat): 
 mult (mult x y) z = mult x (mult y z).
Proof. 
  induction x; simpl. 
    - reflexivity.
    - rewrite mult_dist. rewrite IHx. reflexivity.
Qed.

Lemma plus_O' x:
  plus O x = x.
Proof.
  auto.
Qed.

Lemma mult_com (x y : nat) :
  mult x y = mult y x.
Proof. induction x;simpl.
  - rewrite mult_O. reflexivity.
  - rewrite mult_S. setoid_rewrite <- IHx. setoid_rewrite plus_com at 2. reflexivity.
Qed.

Lemma mult_1 (x:nat): mult x 1 = x.
Proof. induction x;  simpl.
  -  reflexivity.
  - auto. 
Qed.

Lemma pote (x m n: nat) : 
  pow x (plus m n)= mult (pow x n)(pow x m).
Proof. induction m; simpl.
   - rewrite mult_1. reflexivity.
   - setoid_rewrite mult_com at 2. rewrite mult_asso. rewrite IHm. setoid_rewrite mult_com at 2. reflexivity.
Qed.


Lemma mult_X (x:nat) :
   mult (mult x x) x = mult x (mult x x).
Proof. induction x. simpl.
  - reflexivity.
  - rewrite mult_com. reflexivity.
Qed.

(* 2. Zadatak *)
Set Implicit Arguments.
Definition car (A B C :Type) (f: A -> B -> C)(p: prod A B) : C :=
match p with (x,y) => f x y end.

Lemma L3 (A B C :Type) (f: A -> B -> C) x y:
  car f (x, y) = f x y.
Proof.
  simpl. reflexivity.
Qed.

Definition cas (A B C :Type) (f: prod A B -> C) x y : C :=
match x,y with x,y => f (x,y) 
end.

Lemma L4 (X Y Z: Type) (f: prod X Y -> Z)  x y :
 cas f x y = f (x, y).
Proof.
  simpl. reflexivity.
Qed.
(* High lvl! *)
Fixpoint iter (n : nat) (X: Type) (f: X -> X) x : X := 
  match n with 
    | O => x
    | S n' => f(iter n' f x)
end.

Fixpoint fact (n : nat) :nat :=
  match n with
    | O => (S O)
    | S n => mult (S n)(fact n)
end.









 