Set Implicit Arguments.
Require Import Setoid.
Require Import Omega.
Require Import Arith.
Require Import List.
Import ListNotations.

Fixpoint iter (n : nat)(X:Type)(f:X->X) x: X:=
  match n with
    |O => x
    |S n' => f (iter n' f x)
end.



Fixpoint foldr (X Y:Type)(f: X -> Y -> Y)(l:list X)(y: Y) :  Y :=
  match l with
    | [] => y
    | x :: xs => f x (foldr f xs y)
end.

Lemma kom (a b:nat): mult a b = mult b a.
Proof. Search mult. rewrite Nat.mul_comm. reflexivity. Qed.

Goal forall (X:Type)(x:X)(p: X -> Prop),exists q : X -> Prop,
   q x /\ (forall y, p y -> q y) /\ forall y, q y -> p y \/ x = y.
Proof. intros. exists ( fun y => p y \/ x = y). split.
  - right. reflexivity.
  - split.
    -- intros. left. exact H.
    -- intros. exact H.
Qed.

Lemma L1: false <> true.
Proof.  exact (fun H : false = true => Bool.diff_false_true H). Qed.
