(*
  Exercises for <Software Foundations> V2 CH4.
  Arthur : Brethland, Late 2019.
 *)

Set Warnings "-notation-overridden,-parsing".
Add LoadPath "C:\Users\ycy12\Documents\Workspace\LEARNING-STUFF\Coq".
Load Coq24.

Inductive hoare_proof : Assertion → com → Assertion → Type :=
  | H_Skip : ∀P,
      hoare_proof P (SKIP) P
  | H_Asgn : ∀Q V a,
      hoare_proof (assn_sub V a Q) (V ::= a) Q
  | H_Seq : ∀P c Q d R,
      hoare_proof P c Q → hoare_proof Q d R → hoare_proof P (c;;d) R
  | H_If : ∀P Q b c1 c2,
    hoare_proof (fun st => P st ∧ bassn b st) c1 Q →
    hoare_proof (fun st => P st ∧ ~(bassn b st)) c2 Q →
    hoare_proof P (IFB b THEN c1 ELSE c2 FI) Q
  | H_While : ∀P b c,
    hoare_proof (fun st => P st ∧ bassn b st) c P →
    hoare_proof P (WHILE b DO c END) (fun st => P st ∧ ¬(bassn b st))
  | H_Consequence : ∀(P Q P' Q' : Assertion) c,
    hoare_proof P' c Q' →
    (∀st, P st → P' st) →
    (∀st, Q' st → Q st) →
    hoare_proof P c Q.

Lemma H_Consequence_pre : ∀(P Q P': Assertion) c,
    hoare_proof P' c Q →
    (∀st, P st → P' st) →
    hoare_proof P c Q.
Proof.
  intros. eapply H_Consequence.
    apply X0. apply H. intros. apply H0. Qed.

Lemma H_Consequence_post : ∀(P Q Q' : Assertion) c,
    hoare_proof P c Q' →
    (∀st, Q' st → Q st) →
    hoare_proof P c Q.
Proof.
  intros. eapply H_Consequence.
  apply X0. auto. auto.
Qed.

Theorem hoare_proof_sound : ∀P c Q,
  hoare_proof P c Q → {{P}} c {{Q}}.
Proof.
  intros. induction X0 eqn:He.
  - apply hoare_skip.
  - apply hoare_asgn.
  - eapply hoare_seq. apply IHh2 with h2. auto.
    apply IHh1 with h1. auto.
  - subst. eapply hoare_if. apply IHh1 with h1. auto.
    apply IHh2 with h2. auto.
  - subst. eapply hoare_while. apply IHh with h. auto.
  - subst. eapply hoare_consequence_pre. eapply hoare_consequence_post.
    apply IHh with h. auto. unfold assert_implies;auto.
    unfold assert_implies;auto.
Qed.

Definition wp (c:com) (Q:Assertion) : Assertion :=
  fun s => ∀s', s =[ c ]⇒ s' → Q s'.

Lemma wp_is_precondition: ∀c Q,
  {{wp c Q}} c {{Q}}.
Proof.
  intros. unfold wp. unfold hoare_triple.
  intros. apply H0 in H. auto.
Qed.

Lemma bassn_eval_false : ∀b st, ¬bassn b st → beval st b = false.
Proof.
  intros b st H. unfold bassn in H. destruct (beval st b).
    exfalso. apply H. reflexivity.
    reflexivity.
Qed.

Lemma wp_is_weakest: ∀c Q P',
   {{P'}} c {{Q}} → ∀st, P' st → wp c Q st.
Proof.
  intros. unfold wp. intros.
  unfold hoare_triple in H. apply H in H1. auto. auto.
Qed.

Theorem hoare_proof_complete: ∀P c Q,
  {{P}} c {{Q}} → hoare_proof P c Q.
Proof.
  intros P c. generalize dependent P.
  induction c; intros P Q HT.
  - (* SKIP *)
    eapply H_Consequence.
     eapply H_Skip.
      intros. eassumption.
      intro st. apply HT. apply E_Skip.
  - (* ::= *)
    eapply H_Consequence.
      eapply H_Asgn.
      intro st. apply HT. econstructor. reflexivity.
      intros; assumption.
  - (* ;; *)
    apply H_Seq with (wp c2 Q).
     eapply IHc1.
       intros st st' E1 H. unfold wp. intros st'' E2.
         eapply HT. econstructor; eassumption. assumption.
     eapply IHc2. intros st st' E1 H. apply H; assumption.
  - (* IF *)
    Admitted.

