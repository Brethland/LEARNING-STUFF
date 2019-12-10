Record IsMagic (A : Set) (f : A -> A -> A) : Prop :=
  is_magic {
    left  : forall x y, f (f x y) y = x;
    right : forall x y, f y (f y x) = x
  }.
Arguments IsMagic {_} f.

Record IsComm (A : Set) (f : A -> A -> A) : Prop :=
  is_comm {
    comm : forall x y, f x y = f y x
  }.
Arguments IsComm {_} f.

Lemma silly : forall (A : Set) (a b c : A), a = c -> b = c -> a = b.
Proof.
  intros. rewrite H.
  auto.
Qed.

Lemma equality__leibniz_equality : forall (X : Type) (x y: X),   x = y -> forall P: X -> Prop, P x -> P y. 
Proof.
  intros.
  rewrite <- H.
  auto.
Qed.

Lemma leibniz_equality__equality : forall (X : Type) (x y: X),   (forall P: X -> Prop, P x -> P y) -> x = y. 
Proof.
  intros.
  apply (H (fun y => x = y)). auto.
Qed.

Inductive eq_leibniz {A : Type} (x y : A): Type :=
  eql : forall (P : A -> Type), P x -> P y -> eq_leibniz x y.

Lemma silly_1 : forall {A : Type} (f : A -> A) (x y : A),
    f x = f y -> x = y.
Proof.
  intros. assert (W : f x = f x). { auto. }
   Abort.
Theorem magic_is_comm : forall (A : Set) (f : A -> A -> A), IsMagic f -> IsComm f.
Proof.
  intros. inversion H.
  constructor. intros.
  remember (left0 x y) as H1.
  remember (right0 x y) as H2.
  clear HeqH1. clear HeqH2.
  remember (silly _ _ _ _ H1 H2) as Heqn.
  clear HeqHeqn.
Abort.
Lemma lemma:forall b,negb(negb b)=b. apply negb_elim. Qed.
