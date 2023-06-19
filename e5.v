Require Import Omega.
Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Setoid.

(* A *)
Goal forall (X Y: Prop), X -> Y -> X.
Proof.  intros X Y x y. exact x. Qed.
(* B *)
Goal forall (X Y Z:Prop), (X -> Y -> Z) -> (X -> Y) -> X -> Z.
Proof. intros X Y Z x y z. apply x. apply z. apply (y z). Qed.
(* C *)
Goal forall (X Y: Prop),(forall Z: Prop, (X -> Y -> Z)-> Z)-> X.
Proof. intros X Y x. apply x. intros a b. exact a. Qed.
(* D *)
Goal forall X: Prop, ~~~X -> ~X.
Proof. intros X x a. apply x. intros c. apply c. exact a. Qed.

(* E *)
Goal forall (X Y: Prop), (X -> Y) -> ~Y -> ~X.
Proof. intros X Y a b x. apply b. apply (a x). Qed. 

(* F *)
Goal forall (X: Prop),(X -> False)-> (~X -> False) -> False.
Proof. intros X a b. apply b. intros C. apply a. apply C. Qed.

(* G *)
Goal forall (X Y: Prop), (forall Z: Prop, (X -> Y -> Z) -> Z) -> Y.
Proof. intros X Y a. apply a. intros Z x. exact x. Qed. 

(* H *)
Goal forall (X Y Z: Prop), X /\ (Y \/ Z) -> X /\ Y \/ X /\ Z.
Proof. intros X Y Z a. destruct a. destruct H0. left. split. 
  exact H. exact H0. right. split.
 exact H. exact H0. Qed.

(* I *)
Goal forall(X Y Z: Prop), X \/ (Y /\ Z) -> (X \/ Y) /\ (X \/ Z).
Proof. intros X Y Z a. destruct a. split; left; exact H. split; destruct H; right. exact H. exact H0.
Qed.

(* J *)
Goal forall (X Y : Prop),X \/ (X /\ Y) <-> X.
Proof. intros X Y. split. intros x. destruct x. exact H. destruct H.  exact H.
  intros a. left. exact a. Qed.

(* K *)
Goal forall (X Y: Prop), X /\ (X \/ Y) <-> X.
Proof. intros X Y. split. intros x. destruct x. exact H.
  split. exact H. left. exact H. Qed.

(* --------------- 2. Zadatak ------------ *)

Goal forall (X: Type)(x y: X), (forall p:X -> Prop, p x -> p y) -> (forall p:X -> Prop, p y-> p x).
Proof. intros X Y x y a. apply y. intros c. exact c. Qed.

(* --------------- 3. Zadatak -------------- *)

Goal False <-> forall (Z:Prop), Z.
Proof. split. intros A. destruct A. intros Z. apply Z. Qed.

Goal forall X Y:Prop, X /\ Y <-> forall Z:Prop, (X -> Y -> Z) -> Z.
Proof. intros X Y. split. intros Z a b. destruct Z. apply b. exact H. exact H0.
  intros p. apply p. split. exact H. exact H0. Qed.

Goal forall (X Y:Prop), X \/ Y <-> forall Z:Prop, (X -> Z) -> (Y -> Z) -> Z.
Proof. intros X Y. split.
  - intros Z a b c. destruct Z. apply b. exact H. apply c. exact H.
  - intros Z. apply Z. intros x. left. exact x. intros y. right. exact y. Qed.


(* --------------- 4. Zadatak -------------- *)

Goal forall X:Prop, ~~(X \/ ~X).
Proof. intros. intros a. apply a. right. intros x. apply a. left. exact x. Qed.


(* Goal forall X Y:Prop, ~~(~(X /\ Y) <-> ~X \/ ~Y). *)
(* Proof. intros X Y a. apply a. split.  *)
(*   - intros x. left. intros c. apply x. split. exact c. exfalso.  apply a. split. intros s...... *)










