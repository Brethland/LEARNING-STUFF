CoInductive stream (A : Set) : Set :=
  | cons : A -> stream A -> stream A.
Arguments cons {_} hd tl.

Notation "x :: y" := (cons x y) (at level 60, right associativity).

Definition head {A} (x : stream A) := match x with
  hd :: _ => hd end.
Definition tail {A} (x : stream A) := match x with
  _ :: tl => tl end.

CoInductive bisim {A : Set} (x y : stream A) : Set :=
  | bisim_eq : head x = head y -> bisim (tail x) (tail y) -> bisim x y.
Notation "x == y" := (bisim x y) (at level 70).

Module Introduction.

  (* Infinite sequence of ones. (not tested) *)
  CoFixpoint ones : stream nat := 1 :: ones.
  
  (* Infinite sequence of given value. *)
  CoFixpoint repeat {A : Set} (a : A) : stream A := a :: (repeat a).
  
  (* Elements at even and odd indexes, respectively. *)
  CoFixpoint even {A : Set} (x : stream A) : stream A := head x :: (even (tail (tail x))).
  Definition odd {A : Set} (x : stream A) : stream A := even (tail x).
  
  (* A stream equals its head plus its tail. (not tested) *)
  Lemma stream_unfold : forall {A : Set} (a : stream A), a = head a :: tail a.
  Proof. intros A a. destruct a. reflexivity. Qed.

End Introduction.

Module Bisimulation.
  
  Export Introduction.
  
  (* Bisimulation is reflexive. *)
  Theorem bisim_refl : forall {A : Set} (a : stream A), a == a.
  Proof.
  cofix CIH. intros. constructor. reflexivity. apply CIH.
  Qed.
  
  (* Odd is tail of Even. *)
  (* Hint: Do you really need cofix? It may depend on your own definition of odd and even. *)
  Theorem odd_even : forall {A : Set} (a : stream A), odd a == even (tail a).
  Proof. unfold odd. intros. apply bisim_refl. Qed.
  
End Bisimulation.

Module Merge.

  Export Bisimulation.
  
  (* Interleave two streams, starting with the left one. *)
  CoFixpoint merge {A : Set} (x y : stream A) : stream A := (head x) :: (merge y (tail x)).
  
  (* Main task: Merge even and odd, and get the original. *)
  Theorem moe : forall {A : Set} (a : stream A), merge (even a) (odd a) == a.
  Proof. 
    cofix CIH. intros. constructor. simpl. reflexivity.
    simpl. constructor. simpl. reflexivity.
    simpl. apply CIH.
  Qed. 
End Merge.