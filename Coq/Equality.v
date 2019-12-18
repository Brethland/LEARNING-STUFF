(** Can you write down three "different" proofs of transitivity (they should all be judgmentally different; [refl] should not prove any two of them the same. *)

Definition trans1
: forall A (x y z : A),
    x = y -> y = z -> x = z.
intros. rewrite <- H in H0. apply H0. Defined.
Definition trans2
: forall A (x y z : A),
    x = y -> y = z -> x = z.
intros. transitivity y. auto. auto. Defined.
Definition trans3
: forall A (x y z : A),
    x = y -> y = z -> x = z.
intros. rewrite H. rewrite H0. auto. Defined.
(** Now we have Coq check that they are not the same; these lines should compile unmodified. *)

Fail Check eq_refl : trans1 = trans2.

Fail Check eq_refl : trans2 = trans3.

Fail Check eq_refl : trans1 = trans3.


(** Now prove that these are all equal (propositionally, but not judgmentally. *)

Definition trans_12
: forall A (x y z : A) (H0 : x = y) (H1 : y = z),
    trans1 A x y z H0 H1 = trans2 A x y z H0 H1.
Proof.
  unfold trans1. unfold trans2. intros.
  subst. auto.
Qed.
Definition trans_23
: forall A (x y z : A) (H0 : x = y) (H1 : y = z),
    trans2 A x y z H0 H1 = trans3 A x y z H0 H1.
Proof.
  unfold trans2. unfold trans3. intros.
  subst. auto.
Qed.

(** We can also prove associativity. *)

Definition trans_assoc
: forall A (x y z w : A) (H0 : x = y) (H1 : y = z) (H2 : z = w),
    eq_trans H0 (eq_trans H1 H2) = eq_trans (eq_trans H0 H1) H2.
Proof. intros. subst. auto. Qed.

Definition trans_Vp
: forall A (x y : A) (H : x = y),
    eq_trans (eq_sym H) H = eq_refl.
Proof. intros. subst. auto. Qed.
  
Definition trans_pV
: forall A (x y : A) (H : x = y),
    eq_trans H (eq_sym H) = eq_refl.
Proof. intros. subst. auto. Qed.
  
Definition trans_1p
: forall A (x y : A) (H : x = y),
    eq_trans eq_refl H = H.
Proof. intros. subst. auto. Qed.

Definition trans_p1
: forall A (x y : A) (H : x = y),
    eq_trans H eq_refl = H.
Proof. intros. subst. auto. Qed.

Definition trans_sym
: forall A (x y z : A) (H0 : x = y) (H1 : y = z),
    eq_sym (eq_trans H0 H1) = eq_trans (eq_sym H1) (eq_sym H0).
Proof. intros. subst. auto. Qed.
