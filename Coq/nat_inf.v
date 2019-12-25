CoInductive conat : Set := O' | S' (n : conat).

CoFixpoint inf : conat := S' inf.

Fixpoint toCo (n : nat) : conat := match n with
  | O => O'
  | S n' => S' (toCo n') end.

CoInductive bisim : conat -> conat -> Prop :=
  | OO : bisim O' O'
  | SS : forall n m : conat, bisim n m -> bisim (S' n) (S' m).

Notation "x == y" := (bisim x y) (at level 70).

Definition conat_u (n : conat) : conat := match n with
  | O' => O'
  | S' n' => S' n' end.

Lemma conat_unfold : forall n : conat, n = conat_u n.
Proof. destruct n; auto. Qed.

Theorem not_fin_then_inf : forall n : conat, ~ (exists m : nat, toCo m == n) -> (n == inf).
Proof.
  cofix CIH. intros. destruct n.
  - destruct H. exists 0. simpl. constructor.
  - rewrite (conat_unfold inf). simpl. constructor.
    apply CIH. intros [m contra]. apply H. exists (S m). simpl.
    constructor. apply contra.
Qed. 