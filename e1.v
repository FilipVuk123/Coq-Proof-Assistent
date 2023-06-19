Definition orb (x y: bool) := 
 match y with
  | true => true
  | false => x
end.

Lemma orb_com (x y: bool): orb x y = orb y x.
Proof.
  - destruct x,y; reflexivity.
Qed.

Definition andb (x y: bool) :=
  match x with
    | true => y
    | false => false
end.

Definition not (x: bool) :=
  match x with
    | false => true
    | true => false
end.

Lemma deM1 (x y: bool): not(orb x y) = andb (not x)(not y).
Proof. destruct x;destruct y; reflexivity. Qed.

Lemma deM2 (x y: bool): not(andb x y) = orb (not x)(not y).
Proof. destruct x.
  - destruct y; reflexivity.
  - destruct y; reflexivity.
Qed.


Definition sop (x y:bool) :=
  match x, y with
    | true, true => false
    | _, _ => true
end.

Definition luk (x y:bool) :=
  match x, y with
    | false, false => true
    | _, _ => false
end.

Lemma sop_com (x y: bool): sop x y = sop y x.
Proof. destruct x.
  - destruct y; reflexivity.
  - destruct y; reflexivity.
Qed.


Lemma luk_com (x y: bool): luk x y = luk y x.
Proof. destruct x.
  - destruct y; reflexivity.
  - destruct y; reflexivity.
Qed.



Definition ekviv (x y: bool) :=
  match x,y with
    | true, true => true
    | false, false => true
    | _,_ => false
end.

Goal forall (x y: bool), ekviv (andb x y)(sop(sop x y)(sop x y)) = true.
Proof. destruct x; destruct y; reflexivity. Qed. 


Fixpoint mult (x y : nat): nat :=
   match x with
    | O => O
    | S x' => plus y (mult x' y)
end.


Fixpoint pow (x n : nat): nat :=
   match n with
    | O => S O
    | S n' => mult x (pow x n')
end.

Fixpoint isEven (x: nat): bool :=
  match x with
    | O => true
    | S O => false
    | S (S x') => (isEven x')
end.

Compute isEven 5.


Fixpoint minus (x y: nat): nat :=
  match x, y with
    | _, O => x
    | O, _ => O
    | S x', S y' => minus x' y'
end.

Compute minus 5 7.







