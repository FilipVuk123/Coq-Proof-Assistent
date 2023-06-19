Require Import Omega.

(* 1.1 booleans *)

Inductive bool : Type :=
 | true : bool
 | false : bool.

Definition negb (x: bool): bool := 
  match x with
    | true => false
    | false => true
end.

Check negb.

Compute negb(negb true).

Lemma L1 : 
  negb true = false.
Proof. simpl. reflexivity. Qed.

Lemma negb_negb (x :bool) : negb(negb x) = x.
Proof. destruct x; reflexivity. Qed.

Definition andb (x y : bool): bool :=
 match x with
    | true => y
    | false => false
end.

Definition orb (x y : bool): bool :=
  match x with
    | true => true
    | false => y
end.

Lemma andb_com (x y :bool): andb x y = andb y x.
Proof. destruct x, y;reflexivity. Qed.

Check andb.
Check orb.

Lemma orb_com (x y : bool): orb x y = orb y x.
Proof. destruct x, y; reflexivity. Qed.

Theorem DeM_law (x y :bool): negb(orb x y) = andb(negb x) (negb y).
Proof. destruct x, y; reflexivity. Qed.

(* 1.2 Cascade functions *)
Check fun x: bool => x.

Compute (fun x:bool => x) true.

Compute andb true.
Print negb.

(* 1.3 Natural numbers *)
Inductive nat : Type :=
 | O :nat
 | S :nat -> nat.

Definition pred (x : nat): nat := 
 match x with
    | O => O
    | S x' => x'
 end.

Compute pred (S(S(S O))).

Fixpoint plus (x y : nat) : nat :=
   match x with
      | O => y
      | S x' => S (plus x' y)
end.
Compute plus (S(S O)) (S O).

Fixpoint mult (x y : nat): nat :=
  match x with
    | O => O
    | S x' => plus (y) ( mult x' y)
end.
Compute mult (S(S O)) (S(S(S O))).

Fixpoint firstLess (x y: nat): bool :=
  match x, y with
    | O, _ => true
    | _, O => false
    | S x', S y' => firstLess x' y'
end.
Compute firstLess (S O) (S(S(S(S O)))).

Fixpoint pow (x y : nat): nat :=
   match y with 
    | O => S O
    | S y' => mult x (pow x y')
end.
Compute pow (S(S O)) (S(S(S O))).

Fixpoint fact (x : nat) :nat :=
  match x with
    | O => S O
    | S x => mult (S x) (fact x)
end.
Compute fact (S(S(S O))).

Fixpoint is_even (x : nat) :bool :=
 match x with 
    | O => true
    | S O => false
    | S (S x') => is_even x'
end.
Compute is_even (S(S(S(S(S O))))).


Fixpoint equal (x y : nat):bool :=
 match x, y with
    | O, O => true
    | _, O => false
    | O, _ => false
    | S x' , S y' => equal x' y'
end.
Compute equal (S(S(S(S O)))) (S(S(S O))).

Fixpoint minus (x y : nat) : nat :=
  match x, y with 
    | _, O => x
    | O, _ => O (* nije bas kako treba ali sta je tu je!*)
    | S x', S y' => minus x' y'
end.
Compute minus (S(S(S(S(S(S O)))))) (S(S O)).

Fixpoint mod2 (x : nat) :nat :=
  match x with
    | O => O
    | S O => S O
    | S (S x') => mod2 x'
end.
Compute mod2 (S(S(S(S O)))).

(* Induction and rewriting *)

Lemma plus_O x: plus x O = x.
Proof. induction x; simpl.
  - reflexivity.
  - rewrite IHx. reflexivity.
Qed.

Lemma plus_S x y: plus x (S y) = S (plus x y).
Proof. induction x; simpl.
  - reflexivity.
  - rewrite IHx. reflexivity.
Qed.

Lemma plus_com x y: plus x y = plus y x.
Proof. induction x; simpl.
  - rewrite plus_O. reflexivity.
  - rewrite plus_S. rewrite IHx. reflexivity.
Qed.

Lemma plus_asso x y z: plus (plus x y) z = plus x (plus y z).
Proof. induction x; simpl.
  - reflexivity.
  - rewrite IHx. reflexivity.
Qed.



Lemma plus_AC (x y z : nat): plus(plus(mult x y) (mult x z))(plus y z) = plus(plus(mult x y)y)(plus(mult x z)z).
Proof. 
   rewrite plus_asso. rewrite plus_asso. f_equal.
   setoid_rewrite plus_com at 1. rewrite plus_asso. f_equal. (* f_equal "smanjuje" jednadybu*)
   apply plus_com.
Qed.

Lemma mult_O (x:nat) : mult x O = O.
Proof. induction x; simpl.
 - reflexivity.
 - rewrite IHx. reflexivity.
Qed.

Lemma mult_S (x y: nat): mult x (S y) = plus (mult x y) x.
Proof. induction x; simpl. reflexivity.
 - rewrite plus_S. f_equal. rewrite IHx. rewrite plus_asso. f_equal.
Qed.

Lemma mult_com (x y: nat): mult x y = mult y x.
Proof. induction x; simpl. 
 - rewrite mult_O. reflexivity.
 - rewrite IHx. rewrite mult_S. rewrite plus_com. reflexivity.
Qed.
Lemma mult_dis x y z: (x + y) * z = x*z + y*z.
Proof. induction x; simpl; omega.
Qed.

Lemma mult_asso x y z: (x * y) * z = x * (y * z).
Proof. induction x; simpl.
 - reflexivity.
 - rewrite mult_dis. omega. 
Qed.


Lemma plus_AC2 (x y z: nat) : plus y (plus x z) = plus (plus z y) x.
Proof. setoid_rewrite plus_com at 1 2.  apply plus_asso. Qed.


Goal forall x y, 2 * (x + y) = (y + x) * 2.
Proof. intros x y. omega. Qed.


Notation "x + y" := (plus x y) (at level 50, left associativity).
Notation "x * y" := (mult x y) (at level 40, left associativity).

Lemma lema1(x : nat) : (x + x) + x = x + (x + x).
Proof. rewrite plus_asso.  f_equal. Qed.

Inductive prod (X Y: Type): Type :=
 | pair : X -> Y -> prod X Y.

Arguments pair [X] [Y] _ _.

Check pair 0 true.

About pair.

Definition fst (X Y: Type) (p: prod X Y): X :=
 match p with pair X _ => X end.

Definition snd (X Y: Type) (p: prod X Y): Y :=
 match p with pair _ Y => Y end.

(* Lists *)

Inductive lista(X : Type):Type:=
 | prazna : lista X
 | dodaj : X -> lista X -> lista X.
(*dodaj uzmina x, uzima listu tipa x i vraca listu tipa x*)
Arguments prazna {X}.
Arguments dodaj {X}.
(*kad imas arguments onda ti ne prolazi Check nat 0 prazna.*)
Set Printing All.
Check dodaj 0 prazna.
Check @dodaj nat O prazna.
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
  | prazna => O
  | _ :: A' => S (duljina A') (*_ :: A je isto kao dodaj x A'*)
 end.

Fixpoint app (X : Type) (A B : lista X) : lista X := 
 match A with
    | prazna => B
    | x :: A' => x :: app A' B
end.

Notation "A ++ B" := (app A B)(at level 60, right associativity).

Fixpoint rev (X :Type) (A : lista X) : lista X :=
 match A with
    | prazna => prazna
    | x :: A' => rev A' ++ [x]
end.

Compute (rev [1;2;3]).

Lemma app_nul (X :Type)(A : lista X): A ++ prazna = A.
Proof. induction A as [|x A].
 - reflexivity.
 -simpl. rewrite IHA. reflexivity.
Qed.

Require Import List.
Import ListNotations.
Notation "| A |" := (length A) (at level 90).

(* Excercise *)

Lemma app_assoc (X: Type)(A B C : list X): 
   A ++ (B ++ C) = (A ++ B) ++ C.
Proof. induction A  as [| x y]. 
  -simpl. reflexivity.
  -simpl. rewrite IHy. reflexivity.
Qed. 


