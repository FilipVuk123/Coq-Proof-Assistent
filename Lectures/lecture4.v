Set Implicit Arguments.
Require Import Omega.

Fixpoint iteracija (n : nat)(X:Type)(f:X->X)(x : X): X:=
 match n with 
  |O => x
  |S n' =>  f (iteracija n' f x)
 end.

Lemma iteracija_zbrajanje x y:
 x + y = iteracija x S y.
Proof.
 induction x; simpl.  (*probaj induction x; simpl; congruendce. Show Proof.*)
  -reflexivity.               (*Qed.*)
  -rewrite IHx. reflexivity.
Qed.



Lemma iteracija_oduzimanje x y:
 x - S y = iteracija y S x.
Proof.
 induction x; simpl.
  -
Abort. (*to be cont..*)


Inductive PrazanSkup :Type:=.

Definition negacija(x : bool): bool:=
match x with
  | true => false
  | false => true
end.

Lemma tvrdnja_s_dokazom(x: bool):
  negacija(negacija x)  = x.
Proof.
  destruct x; reflexivity.
Qed. (*Dokaz je koristio definiciju, tj. kod razlaganja slucajeva otisao u definiciju i vidio da moze bit ili true ili false*)

Lemma tvrdnja_s_dokazom2 (x:PrazanSkup):
 negacija true = true.
Proof.
  destruct x.
Qed. (*Ovaj isto ide u definiciju, a u definiciji Praznog skupa ne postoji nista tj. nema konstruktora*)

Lemma jedan_jednako_dva(x:PrazanSkup):
 1 = 2.
Proof.
 destruct x.
Qed. (*so called "Prazna istina"*)


Inductive opcija(X:Type): Type:=
 | Stari : X -> opcija X
 | Novi : opcija X.

Arguments Stari{X}.
Arguments Novi{X}.

Definition konacan (n:nat): Type:=
  iteracija n opcija PrazanSkup.

Definition a11 : konacan 1 := @Novi PrazanSkup. (*Ekpslicitno dao novi na prazan skup?!?*)
Definition a21 : konacan 2 := Stari a11.   (*Eksplicitno vec prepostavio?!?*)
Definition a22 : konacan 2 := @Novi (konacan 1).
Definition a31 : konacan 3 := Stari a21.
Definition a32 : konacan 3 := @Novi (konacan 2).
  
Goal forall(X: Type)(x y: X), x = y -> y = x.
Proof.
  intros X x y A. rewrite A. reflexivity. Show Proof. (*A je premisa, lijeva strana implikacije... A ce bit tu x = y,*)
Qed.

(*Googleaj Modus Ponens(to je ovo dolje)*)

Goal forall X Y:Prop,X -> (X -> Y) -> Y. (*kod propa x i y predstavljaju logicku tvrdnju*)
Proof.
 intros X Y x A. exact(A x). Show Proof. (*za dokaz za y si presliko zapravo samo A na malo x (gledaj desno sta su i kako su)*)