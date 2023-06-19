Goal forall X Y : Prop, 
  X -> (X -> Y) -> Y.
Proof. intros X Y x A. exact (A x). Show Proof. Qed.

Goal forall X Y : Prop, 
   X -> (X -> Y) -> Y.
Proof. intros X Y x A. Show Proof. apply A. exact x. Show Proof. Qed.

Goal forall X Y Z : Prop, 
  (X -> Y) -> (Y -> Z) -> X -> Z.
Proof. intros X Y Z A B x. apply B. apply A. exact x. Show Proof. Qed.

(* Predikati *)
(* Za svake dvije fje koje nat broju pridruzuju propoziciju*)

Goal forall p q : nat -> Prop,
  p 7 -> (forall x, p x -> q x) -> q 7.
Proof. 
  intros p q A B. apply B. exact A. Qed. (* ili -> intros p q A B. exact (B 7 A). Qed.*)

Goal forall (X :Type) (x y: X), (forall p : X -> Prop, p x -> p y) -> x = y.
Proof. 
  intros X x y A. apply A. reflexivity. 
Qed.

Goal forall (X :Type) (x y: X), (forall p : X -> Prop, p x -> p y) -> x = y.
Proof. 
  intros X x y A. apply (A (fun z => x = z)). reflexivity. 
Qed.

Goal False -> 2 = 3.
Proof.  intros A. destruct A. (* ili contradicton A*)
Qed.

Goal forall X : Prop, X -> ~~X.
Proof. intros X x A. apply A. exact x. 
Qed.

Goal forall X : Prop,
  ~~ X -> (X -> ~X) -> X.
Proof.
  intros X A B. exfalso. apply A. intros x. apply (B x). exact x.
Qed.

Goal forall X Y : Prop,
 X /\ Y -> Y /\ X.
Proof. intros X Y A. destruct A as [x y]. split. 
 - exact y.
 - exact x.
Qed.

Goal forall X Y: Prop,
  X \/ Y -> Y \/ X.
Proof. 
    intros X Y [x | y].
      - right. exact x.
      - left. exact y.
Qed.  

