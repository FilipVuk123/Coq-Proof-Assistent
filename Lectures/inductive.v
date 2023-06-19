Require Import Omega.

Inductive zero: nat->Prop:=
  |zeroI : zero 0.

Lemma zero_iff x:
  zero x <-> x = 0.
Proof.
 split. intros A.
  -destruct A. reflexivity.
  - intros B. subst x. apply zeroI.
Qed.

Goal ~ zero 2.
Proof.
 intros A. remember 2 as x. destruct A. discriminate Heqx.
Qed.

Inductive paran : nat -> Prop :=
  | paranO : paran 0
  | paranS x : paran x -> paran (S (S x)).


Lemma neind_karak_parnosti x:
  paran x <-> exists k, x = 2*k.
Proof.
  split; intros A.
  - induction A.
    +exists 0. reflexivity.
    +destruct IHA as [k IHa]. subst x. exists (S k). omega.
  - destruct A as [k A]. subst x. induction k; simpl.
    +constructor. (*prolazi i exact paranO*)  
    + replace ((S (k + S (k + 0)))) with (S(S(2*k))) by omega. constructor. exact IHk.
Qed.


Lemma prethodnik_parnog x:
  paran (S(S x)) -> paran x.
Proof.
  intros A. remember (S(S x)) as y. destruct A as [ | y A].
  - discriminate Heqy.
  - congruence. (*koristi injektivnost sljedbenika iz Heqy izvukao da je y = x. *)
Qed.


Inductive le (x : nat): nat -> Prop :=
  | le_n : le x x  (*x manjejedn od x*)
  | le_S y : le x y -> le x (S y). (*ako je x manjjedn od y onda je manji jedn od y+1*)

Notation "x <= y" := (le x y)(at level 70).

Lemma le_iff x y:
   x <= y <-> exists k, x + k = y.
Proof.
  split; intros A.
  - induction A as [|y A].
      +exists 0. omega.
      + destruct IHA as [k IHA]. exists (S k). rewrite <- IHA. omega.
  - destruct A as [k A]. subst y. (*rewrite <- A.*) induction k; simpl.
    + rewrite plus_0_r. constructor.
    + replace (x + S k) with (S(x + k)) by omega. constructor. exact IHk.
Qed.

Lemma le_Stran x y : S x <= y -> x <= y.
Proof.
  intros A. induction A.
  - constructor. constructor.
  - constructor. exact IHA.
Qed.


Lemma le_SS x y : x<= y -> S x <= S y.
Proof.
  intros A. induction A.
  -constructor.
  -constructor. exact IHA.
Qed.

Lemma le_SS' x y : S x <= S y -> x <= y.
Proof.
  intros A. remember (S y) as y'. induction A as [|y' A].
  - injection Heqy'. intros A. subst x. (* rewrite A *) constructor.
  - injection Heqy'. intros B. subst y. apply le_Stran. exact A.
Qed.


(* Egzistencijalni kvantifikatori *)

(*Goal forall (X : Type) (p q : X -> Prop),
(exists x,)*)

(*Googlaj Touringov stroj..*)
(*dijagonalni zakon*)
Definition diagonal : Prop:= forall (X : Type) (p : X -> X -> Prop), 
~ exists x, forall y, p x y <-> ~p y y.

Lemma circuit (X : Prop) : ~ (X <-> ~X).
Proof. tauto. Qed. (*Tauto radi dost dobro sa negacijama, mijenja applyeve i sve te sheme*)

Set Implicit Arguments.
Unset Strict Implicit.

(*Goal diagonal*)
(*Valjda vjezbe iz skripte 
  .
  .
  .
*)