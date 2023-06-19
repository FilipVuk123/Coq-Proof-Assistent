Inductive lista(X : Type):Type:=
 | prazna : lista X
 | dodaj : X -> lista X -> lista X.
(*dodaj uzmina x, uzima listu tipa x i vraca listu tipa x*)

Arguments prazna {X}.
Arguments dodaj {X}.
(*kad imas arguments onda ti ne prolazi Check nat 0 prazna.*)

Set Printing All.
Check dodaj 0 prazna.
Check @dodaj nat 0 prazna.
Unset Printing All.

Notation "x :: y" := (dodaj x y)(at level 60,right associativity). (*Prvi komentar..*)
Notation "[]" := prazna.
Notation "[ x ]" := (dodaj x prazna). (*Mora bit [ x ] tako sa razmacima*)
Notation "[ x ; .. ; y ]" := (dodaj x .. (dodaj y prazna) ..).

Check [1;2;3].

Set Implicit Arguments. (*ukljucivanje impl argumenata*)
Unset Strict Implicit.

(*BEZ OVIH SET IMPL.... U DOLJE U KONSTRUKTORU | _ :: A' => S (duljina X A') izlgeda ovako jer je taj x
implicitno proslijeden i guess*)

Fixpoint duljina (X:Type) (A:lista X) : nat:=
 match A with
  | prazna => 0
  | _ :: A' => S ( duljina A') (*_ :: A je isto kao dodaj x A'*)
 end.

Notation "| A |" :=(duljina A) (at level 70).
(*ide level 70 da ga napravi nakon onih konstrukcija koje su level 60*)

Fixpoint konkatenacija (X:Type) (A B: lista X): lista X:=
 match A with
  |[] => B
  | x :: A' => x :: konkatenacija A' B
 end.


  
Notation " A +++ B " :=(konkatenacija A B) (at level 60).

Fixpoint obrni(X: Type) (A :lista X): lista X:=
 match A with
  | [] => []
  | x :: A => obrni A +++ [x]
 end.


Lemma neutral_za_konkat (X: Type) (A : lista X):
  A +++ [] = A.
 Proof.
  induction A as [| x A']. (*oznake koje koristi u indukciji, lijevo od | su pretpostavke, desno od | su koraci*)
  -simpl. reflexivity.
  -simpl. rewrite IHA'. reflexivity.
Qed.

Lemma asoc_za_konkat (X: Type) (A B C : lista X):
  (A +++ B) +++ C = A +++ (B +++ C).
Proof.
 induction A as [| x A']. 
  -simpl. reflexivity.
  -simpl. rewrite IHA'. reflexivity.
Qed.

Lemma obrni_konkat (X : Type) (A B: lista X):
 obrni(A +++ B) = (obrni B) +++ (obrni A).
Proof.
 induction A as [| x A']. 
  -simpl. rewrite neutral_za_konkat. reflexivity.
  -simpl. rewrite IHA'. rewrite asoc_za_konkat. reflexivity.
Qed.


Lemma obrni2 (X : Type)(A :lista X):
  obrni(obrni A) =  A.
Proof.
 induction A as [| x A'].
  -simpl. reflexivity.
  -simpl. rewrite obrni_konkat. rewrite IHA'. simpl. reflexivity.
Qed. (*To be continued*) 

Fixpoint obrni_repna (X:Type) (A B: lista X) : lista X:=
 match A with
  | prazna => B
  | x :: A' => obrni_repna A' (x :: B)
 end.

Lemma obrni_repna_obrni (X : Type) (A B: lista X):
 obrni_repna A B = obrni(A) +++ B.
Proof.
 revert B. induction A as[| x A]; simpl.    (* REVERT = za svaki b koji je tipa x vrijedi ta tvrdnja..*) 
  -reflexivity.
  -intros B. rewrite IHA. rewrite asoc_za_konkat. reflexivity. (*INTROS = Suprotno od reverta, UVODI B actually*)  
Qed.
