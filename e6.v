Require Import Omega.
Require Import Arith.
Require Import Setoid.
Require Import List.
Import ListNotations.



Goal forall (X Y:Prop) (p: X -> Y -> Prop), (exists y x, p x y) -> exists x y, p y x.
Proof. intros. apply H. Qed. 

Goal forall x y, andb x y = true -> x = true.
Proof. intros. destruct x. reflexivity. destruct H. trivial. Qed.

Goal forall (X Y: Prop)(p: X -> Prop),(forall x, p x -> Y) <-> ((exists x, p x)-> Y).
Proof. intros. split.
  -  intros. destruct H0. apply (H x). exact H0.
  -  intros. apply H. exists x. exact H0.
Qed.

Goal forall(X Y:Prop), (X -> Y) <-> ((exists x : X, True) -> Y).
Proof. intros. split.
  -  intros x y. destruct y. apply (x x0).
  -  intros. apply H. exists H0. trivial. (* true -> trivial*)
Qed.


Goal forall (X : Type) (p : X -> Prop), (exists x, p x) <-> forall Z : Prop, (forall x, p x -> Z) -> Z.
Proof. intros. split.
  -  intros. destruct H. apply (H0 x). exact H.
  -  intros. apply H. intros. exists x. exact H0. 
Qed.


(* ----------------- 2. Zadatak---------------- *)

Goal forall (X :Type) (p: X -> Prop), ~(exists x, p x) <-> forall x, ~p x.
Proof. intros A B. split.
  -  intros x y z. apply x. exists y. exact z.
  -  intros H G. destruct G. apply (H x). exact H0.
Qed.

Goal forall (X: Type) (p: X -> Prop), (exists x, ~p x) <-> ~(forall x, p x).
Proof. intros. split.
  -  intros. intros b. destruct H. apply H. apply (b x).
  -  intros. exfalso. apply H. intros. exfalso. apply H. intros a.
 Abort.

(* ----------------- 3. Zadatak---------------- *)

(* a i b *)
Goal (forall (X : Prop), X \/ ~X) <-> (forall (X:Prop), ~~X -> X).
Proof. split.
  - intros. destruct (H X). apply H1. exfalso. apply H0. apply H1.
  - intros. apply H. intros A. apply A. right.  intros B. apply A. left. exact B.
Qed.



(* ----------------- 4. Zadatak---------------- *)

Lemma L1: false <> true.
Proof. intuition.  Qed.

Lemma L2: true <> false.
Proof. intuition. Qed.



Goal forall x y: bool, x = y \/ x <> y.
Proof. intros. destruct x,y.
  - left. trivial.
  - right. discriminate.
  - right. discriminate.
   - left. trivial.
Qed.


Goal forall X : Type, forall (x y : X), x <> y <-> exists R : X -> X -> Prop, ~R x y /\ forall z, R z z.
Proof. split. 
  -  intros. exists eq. split.
    + apply H.
    + intros. reflexivity.
  - intros. destruct H. destruct H. intros a. apply H. rewrite a. apply H0.
Qed.

(* ----------------- 5. Zadatak---------------- *)


Definition XM := forall X : Prop, X \/ ~ X.

Goal forall (X : Type)(d : X -> Prop), XM -> (exists x : X, True) -> exists x, d x -> forall x, d x.
Proof. unfold XM.  intros. destruct H0. exists x. intros. exfalso. Abort.

















