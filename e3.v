Set Implicit Arguments.
Require Import Setoid.
Require Import Omega.

Notation "x + y" := (plus x y)  (at level 50 , left associativity).
Notation "x * y" := (mult x y) (at level 40, left associativity).

Lemma plus_O x:
  plus x O = x.
Proof.
  auto.
Qed.

Lemma mult_dist' x y z :  
  x * (y + z) = x*y + x*z.
Proof. induction x; simpl. reflexivity. omega.
Qed.

Goal forall (a b c d: nat), (a + b) * (c + d) = a*c + b*c + a*d + b*d.
Proof. 
 intros. induction a; simpl.
  - rewrite mult_dist'. rewrite plus_O. reflexivity.
  - omega.
Qed.

(* 2. Zadatak *)

Fixpoint sum_n_ones (n: nat) :=
  match n with
    | O => O
    | S n' => plus (S O) (sum_n_ones n')
end.

Compute sum_n_ones 5.

Lemma L1 n: sum_n_ones n = n.
Proof. 
  induction n; simpl.
    - reflexivity.
    - rewrite IHn. reflexivity.
Qed.


Fixpoint sum_n_ms (n m: nat) :=
  match n with
    | O => O
    | S n' => plus m (sum_n_ms n' m)
end.

Compute sum_n_ms 4 3.

Lemma L2 (n m: nat): sum_n_ms n O = O.
Proof. induction n. 
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.


Lemma L3 (n m: nat): sum_n_ms n m = mult n m.
Proof. induction n; simpl. 
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

Lemma L4 (n m: nat): sum_n_ms (sum_n_ones n) (sum_n_ones m) = n * m.
Proof. induction n. 
  - simpl. reflexivity.
  - simpl. rewrite IHn. rewrite L1. reflexivity.
Qed.

Fixpoint suma_prvih_n n :=
  match n with
    | O => O
    | S n' => plus n (suma_prvih_n n')
end.

Compute suma_prvih_n 3.

Lemma plus_S x y:
  plus x (S y) = S (plus x y).
Proof.
  auto.
Qed.

Lemma plus_asso x y z :
plus (plus x y) z = plus x (plus y z).
Proof.
induction x ; simpl.
  - reflexivity.
  - rewrite IHx. reflexivity.
Qed.

Lemma mult_S (x y : nat) :
  mult x (S y) = plus (mult x y) x.
Proof.
  induction x; simpl.
    - reflexivity.
    - rewrite plus_S. rewrite IHx. rewrite plus_asso. reflexivity.
Qed.

Lemma mult_dist (x y z: nat) :
  mult (plus x y) z = plus (mult x z) (mult y z).
Proof.
  induction x; simpl.
    - reflexivity.
    - rewrite plus_asso. rewrite IHx. reflexivity.
Qed.


Lemma zbrojPrvihN (n: nat): (suma_prvih_n n) * 2= (n*n + n).
Proof. induction n.
  - simpl. reflexivity.
  - simpl. rewrite mult_dist. rewrite IHn. repeat rewrite mult_S. omega.
Qed.

Fixpoint sumaNkvad n :=
   match n with
    | O => O
    | S n' => plus (n*n)(sumaNkvad n')
end.

Compute sumaNkvad 2.

Lemma pomocna n:
  sumaNkvad (S n) = (S n)*(S n) + (sumaNkvad n).
Proof.
  induction n; simpl; omega.
Qed.

Lemma pomocna_2 n:
  S n = plus n 1.
Proof.
  omega.
Qed.

Lemma mult_O' x:
  mult x O = O.
Proof.
  induction x; simpl.
  - reflexivity.
  - rewrite IHx. reflexivity.
Qed.

(*
Lemma zbrojPrvihNkvad n : (sumaNkvad n) * 6 = n*(n + 1)*(2*n + 2).
Proof. induction n; simpl.
  - reflexivity.
  - repeat rewrite plus_S. repeat rewrite plus_O.
repeat rewrite mult_S. simpl. repeat rewrite mult_dist. repeat rewrite mult_O'.  repeat rewrite plus_S.
repeat rewrite plus_O. simpl. repeat rewrite plus_asso. omega.
*)








