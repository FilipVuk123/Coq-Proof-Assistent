Lemma and_com: forall X Y : Prop, X /\ Y <-> Y /\ X.
Proof.
  intros X Y. split.
   - intros [x y]. split.
    + exact y.
    + exact x.
  - intros [y x]. split.
    + exact x.
    + exact y.
Qed.

Lemma deMorgan : forall X Y : Prop, ~(X \/ Y) <-> ~X /\ ~Y.
Proof.
 intros X Y. split.
  -intros A. split.
    +intros x. apply A. left. exact x.
    +intros y. apply A. right. exact y.
  -intros [A B] [x|y].
    +exact (A x). (*exact ce primjenit A na x. mogao si i apply a pa exact x*)
    +exact (B y).
Qed.
(*Googlaj DeMorgana u teoriji skupova*)

Goal forall X Y Z W : Prop, (X <-> Y) -> (Z <-> W) -> (X /\ Z <-> Y /\ W).
Proof.
 intros X Y Z W A B. split.
  -intros [C D]. split.
    +apply -> A. exact C.  (*Apply A sa lijeva ce primjenit ako X onda Y*)
    +apply -> B. exact D.
  -intros [C D]. split.
    +apply <- A. exact C. (*Sad kad trebas Ako Y onda X, onda primjenis zdesna apply A.*)
    +apply <- B. exact D.
Qed.




  Set Implicit Arguments.
(*SKRIPTA, ALFA I BETA KONVERZIJA*)
Goal ~~True.
Proof.
  change (~True -> False).
  change (~(True -> False)).
  change (~~True).
  hnf.
  change (~~True).
  cbv.
  simpl.
  pattern True.  (*Uzet ce proizvoljnu propozicijju P i radi beta redux, 'nesto zamjeni/iskoristi sa true'.*)
  change (~~True).
  hnf.
  exact (fun f => f I).
Qed.

Goal ~~True.
Proof.
  exact (fun f => f I).
Qed.


(*HeadNormalForm primjenjuje nesto samo jednom, npr kod ~~True, primjenit c
ce negaciju samo jednom. CBV ce napravit sve. 
Pattern ce  iskoristit te neke alfa i beta konverzije*)


Inductive demo (X : Type) (x : X) : Prop:=
  | demoI : demo x.

Goal demo plus.
Proof.
  unfold plus.
  fold plus.     (*Unfold ubacuje definiciju izraza u treutno stanje,fold radi obrnuto*)
  apply demoI.
Qed.

Goal false <> true.
Proof.
  intros A.
  change(if false then True else False). (*false bool, True i False propozicije*)
  rewrite A.
  exact I.
Qed.


Lemma disjoint_O_S n:
  0 <> S n.
Proof.
  intros A.
  change (match 0 with 0 => False | _ => True end).
  rewrite A.
  exact I.
Qed.



Lemma injective_S x y:
  S x = S y -> x = y.
Proof.
  intros A.
  change (pred (S x) = pred (S y)).
  rewrite A.
  reflexivity.
Qed.


Goal forall x, S x <> 0.
Proof.
  intros x y. discriminate.
Qed. 
 
Goal forall x, S x <> 0.
Proof.
  congruence.
Qed.


(*3 poznate tvrdnje u mat.logici*)

(*eXcludedMiddle*)
Definition XM : Prop := forall X : Prop, (X \/ ~X).
(*DoubleNegativity*)
Definition DN : Prop := forall X : Prop, (~~X -> X).
(*ContraPozicija*)
Definition CP : Prop := forall X Y : Prop, (~Y -> ~X) -> X -> Y.


Lemma XMimpDN : forall X : Prop,
XM -> (~~X -> X).
Proof.
  unfold XM.
    intros X[A | B]; intros C.
      + exact A.
      + exfalso. apply C. exact B.
Qed.

(*Lemma DNimCP : forall X Y : Prop,
DN (~Y -> ~X) -> X -> Y.
  intros X Y A B C.
*)