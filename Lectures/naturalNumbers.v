(*Commented because of naming conflicts with the Standard library: *)
Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Definition pred (x : nat) : nat :=
  match x with
    | O => O
    | S x' => x'
  end.

Print nat.

Compute pred (S(S O)).

(* Commented because of naming conflicts with the Standard library: *)
Fixpoint plus (x y : nat) : nat :=
  match x with
    | O => y
    | S x' => S (plus x' y)
  end.

Print plus.

Compute plus (S O) ( S O).

Fixpoint leb (x y: nat) : bool :=
  match x with
    | O => true
    | S x' => match y with
                | O => false
                | S y' => leb x' y'
              end
  end.

Fixpoint leb' (x y: nat) : bool :=
  match x, y with
    | O, _ => true
    | _, O => false
    | S x', S y' => leb' x' y'
  end.

Print leb'.

Fixpoint addtail (x y : nat) : nat :=
  match x with
    | O => y
    | S x' => addtail x' (S y)
  end.


Lemma addtail_prop (x y : nat):
  addtail x y = plus y x.
Proof.
induction x ; simpl.
  - reflexivity.
  - reflexivity.
Qed.
(* Exercise 1.3.1 *)   

(* Definition mult (x y: nat) : nat := 
 (* ... *) *)