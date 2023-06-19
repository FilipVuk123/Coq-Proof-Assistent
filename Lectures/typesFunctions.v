
Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (x : bool) : bool :=
  match x with
    | true => false
    | false => true
  end.

Check negb.
Check negb (negb true).
Compute negb (negb true).

Lemma L1 :
  negb true = false.
Proof. simpl. reflexivity. Qed.

Lemma negb_negb (x : bool) :
  negb (negb x) = x.
Proof.
  destruct x.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
      
Goal forall (x: bool), negb (negb x) = x.
Proof.
  destruct x; reflexivity.
Qed.

(* Commented because of naming conflicts with the Standard library: *)
Definition andb (x y : bool) : bool :=
  match x with
    | true => y
    | false => false
  end. 

Print andb.

Lemma andb_com x y :
  andb x y = andb y x.
Proof.
  destruct x.
  - destruct y.
      + simpl. reflexivity.
      + simpl. reflexivity.
  - destruct y.
      + simpl. reflexivity.
      + simpl. reflexivity.
Qed.

Goal forall x y: bool,
       andb x y = andb y x.
Proof. destruct x, y; reflexivity. Qed.

(* Exercise 1.1.1 *)

(* Definition orb (x y: bool) :=
  (* ... *) *)

(* Goal forall x y: bool,
       orb x y = orb y x.
Abort.*)

(* Formulate and prove the De Morgan Law. *)