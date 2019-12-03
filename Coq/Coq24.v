(*
  Exercises for <Software Foundations> V2 CH2.
  Arthur : Brethland, Late 2019.
 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
Add LoadPath "C:\Users\ycy12\Documents\Workspace\LEARNING-STUFF\Coq".
Load Coq19.

Definition Assertion := state -> Prop.
Definition assert_implies (P Q : Assertion) : Prop :=
  ∀st, P st → Q st.
Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q ∧ Q ->> P) (at level 80) : hoare_spec_scope.

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  ∀st st',
     st =[ c ]⇒ st' →
     P st →
     Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Theorem hoare_post_true : ∀(P Q : Assertion) c,
  (∀st, Q st) →
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H. Qed.

Theorem hoare_pre_false : ∀(P Q : Assertion) c,
  (∀st, ¬(P st)) →
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP. Qed.

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).
Notation "P [ X ⊢> a ]" := (assn_sub X a P)
                             (at level 10, X at next level).

Theorem hoare_asgn : ∀Q X a,
  {{Q [X ⊢> a]}} X ::= a {{Q}}.
Proof.
  intros Q X a.
  unfold assn_sub. unfold hoare_triple.
  intros. inversion H;subst. apply H0.
Qed.

Lemma assn_sub_ex1 : {{(fun st => st X <= 10) [X ⊢> 2 * X] }}
                       X ::= 2 * X
                     {{fun st => st X <= 10}}.
Proof.
  apply hoare_asgn.
Qed.

Lemma assn_sub_ex2 : {{(fun st => st X >= 0 /\ st X <= 5) [X ⊢> 3]}}
                       X ::= 3
                     {{fun st => st X >= 0 /\ st X <= 5}}.
Proof.
  apply hoare_asgn.
Qed.
Axiom functional_extensionality : ∀ {X Y: Type} {f g : X → Y}, (∀ (x:X), f x = g x) → f = g.

Lemma beq_stringP : ∀ x y, reflect (x = y) (beq_string x y).
Proof.
  intros. destruct (beq_string x y) eqn:HS.
  - apply ReflectT. apply beq_string_true_iff. auto.
  - apply ReflectF. apply beq_string_false_iff. auto.
Qed.

Theorem t_update_same : ∀(A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros. apply functional_extensionality.
  intros. unfold t_update.
  destruct (beq_stringP x x0).
  - rewrite e. auto.
  - auto.
Qed.

Lemma t_update_shadow : ∀(A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros.
  apply functional_extensionality.
  intros. unfold t_update.
  destruct (beq_string x x0) eqn:HE.
  - auto.
  - auto.
Qed.

Theorem hoare_asgn_fwd :
  ∀m a P,
  {{fun st => P st ∧ st X = m}}
    X ::= a
  {{fun st => P (X !-> m ; st)
           ∧ st X = aeval (X !-> m ; st) a }}.
Proof.
  intros. unfold hoare_triple. intros.
  inversion H. subst. destruct H0.
  subst. rewrite t_update_shadow. rewrite t_update_same. split.
  - auto.
  - rewrite t_update_eq. auto.
Qed.

Theorem hoare_asgn_fwd_exists :
  ∀a P,
  {{fun st => P st}}
    X ::= a
  {{fun st => ∃m, P (X !-> m ; st) ∧
                st X = aeval (X !-> m ; st) a }}.
Proof.
  intros a P.
  unfold hoare_triple. intros.
  inversion H;subst. exists (st X).
  rewrite t_update_shadow. rewrite t_update_same. split.
  auto. rewrite t_update_eq. auto.
Qed.

Theorem hoare_consequence_pre : ∀(P P' Q : Assertion) c,
  {{P'}} c {{Q}} →
  P ->> P' →
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : ∀(P Q Q' : Assertion) c,
  {{P}} c {{Q'}} →
  Q' ->> Q →
  {{P}} c {{Q}}.
Proof.
  intros. intros st st' Hc HP.
  apply H0. apply (H st st').
  auto. auto.
Qed.

Example hoare_asgn_example1 :
  {{fun st => True}} X ::= 1 {{fun st => st X = 1}}.
Proof.
  apply hoare_consequence_pre
    with (P' := (fun st => st X = 1) [X ⊢> 1]).
  apply hoare_asgn.
  intros st H. unfold assn_sub, t_update. simpl. reflexivity.
Qed.

Example assn_sub_example2 :
  {{(fun st => st X < 4)}}
  X ::= X + 1
  {{fun st => st X < 5}}.
Proof.
  apply hoare_consequence_pre
    with (P' := (fun st => st X < 5) [X ⊢> X + 1]).
  apply hoare_asgn.
  intros st H. unfold assn_sub, t_update. simpl. omega.
Qed.

Theorem hoare_consequence : ∀(P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} →
  P ->> P' →
  Q' ->> Q →
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption. Qed.

Lemma assn_sub_ex1' : {{ fun st =>  st X + 1 <= 5 }} X ::= X + 1 {{ fun st => st X <= 5 }}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H. unfold assn_sub, t_update. simpl.
  auto.
Qed.

Lemma assn_sub_ex2' : {{ fun st => 0 <= 3 /\ 3 <= 5 }} X ::= 3 {{ fun st => 0 <= st X /\ st X <= 5}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn. intros st H.
  unfold assn_sub, t_update.   simpl. auto.
Qed.

Theorem hoare_skip : ∀P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption. Qed.

Theorem hoare_seq : ∀P Q R c1 c2,
     {{Q}} c2 {{R}} →
     {{P}} c1 {{Q}} →
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

Example hoare_asgn_example3 : ∀a n,
  {{fun st => aeval st a = n}}
  X ::= a;; SKIP
  {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  - apply hoare_skip.
  - eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. subst. reflexivity.
Qed.

Example hoare_asgn_example4 :
  {{fun st => True}}
  X ::= 1;; Y ::= 2
  {{fun st => st X = 1 ∧ st Y = 2}}.
Proof.
  eapply hoare_seq.
  - apply hoare_asgn.
  - eapply hoare_consequence_pre.
    apply hoare_asgn.
    unfold assn_sub, t_update. simpl.
    intros st H. auto.
Qed.

Definition swap_program : com :=
  Z ::= X ;; X ::= Y ;; Y ::= Z.

Theorem swap_exercise :
  {{fun st => st X ≤ st Y}}
  swap_program
  {{fun st => st Y ≤ st X}}.
Proof.
  unfold swap_program.
  eapply hoare_seq.
  - eapply hoare_seq.
    apply hoare_asgn.
    apply hoare_asgn.
  - eapply hoare_consequence_pre.
    apply hoare_asgn.
    unfold assn_sub, t_update.
    simpl.
    intros st H. auto.
Qed.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : ∀b st,
  beval st b = true → (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption. Qed.

Lemma bexp_eval_false : ∀b st,
  beval st b = false → ¬((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe. Qed.

Theorem hoare_if : ∀P Q b c1 c2,
  {{fun st => P st ∧ bassn b st}} c1 {{Q}} →
  {{fun st => P st ∧ ¬(bassn b st)}} c2 {{Q}} →
  {{P}} IFB b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - apply (HTrue st st').
    auto. split. auto. apply bexp_eval_true. auto.
  - apply (HFalse st st').
    auto. split. auto. apply bexp_eval_false. auto.
Qed.

Theorem if_minus_plus :
  {{fun st => True}}
  IFB X ≤ Y
    THEN Z ::= Y - X
    ELSE Y ::= X + Z
  FI
  {{fun st => st Y = st X + st Z}}.
Proof.
  eapply hoare_if.
  - eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, t_update. simpl.
    intros st [_ H]. apply leb_le in H. omega.
  - eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, t_update. simpl.
    intros st H. auto.
Qed.

Module If1.
Inductive com : Type :=
  | CSkip : com
  | CAss : string → aexp → com
  | CSeq : com → com → com
  | CIf : bexp → com → com → com
  | CWhile : bexp → com → com
  | CIf1 : bexp → com → com.
Notation "'SKIP'" :=
  CSkip : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "X '::=' a" :=
  (CAss X a) (at level 60) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity) : imp_scope.
Notation "'IF1' b 'THEN' c 'FI'" :=
  (CIf1 b c) (at level 80, right associativity) : imp_scope.

Reserved Notation "st '=[' c ']⇒' st'" (at level 40).
Open Scope imp_scope.
Inductive ceval : com → state → state → Prop :=
  | E_Skip : ∀st,
      st =[ SKIP ]⇒ st
  | E_Ass : ∀st a1 n x,
      aeval st a1 = n →
      st =[ x ::= a1 ]⇒ (x !-> n ; st)
  | E_Seq : ∀c1 c2 st st' st'',
      st =[ c1 ]⇒ st' →
      st' =[ c2 ]⇒ st'' →
      st =[ c1 ;; c2 ]⇒ st''
  | E_IfTrue : ∀st st' b c1 c2,
      beval st b = true →
      st =[ c1 ]⇒ st' →
      st =[ TEST b THEN c1 ELSE c2 FI ]⇒ st'
  | E_IfFalse : ∀st st' b c1 c2,
      beval st b = false →
      st =[ c2 ]⇒ st' →
      st =[ TEST b THEN c1 ELSE c2 FI ]⇒ st'
  | E_WhileFalse : ∀b st c,
      beval st b = false →
      st =[ WHILE b DO c END ]⇒ st
  | E_WhileTrue : ∀st st' st'' b c,
      beval st b = true →
      st =[ c ]⇒ st' →
      st' =[ WHILE b DO c END ]⇒ st'' →
      st =[ WHILE b DO c END ]⇒ st''
  | E_IF1Ture : forall st st' b c,
      beval st b = true ->
      st =[ c ]⇒ st' ->
      st =[ IF1 b THEN c FI ]⇒ st'
  | E_IF1False : forall st b c,
      beval st b = false ->
      st =[ IF1 b THEN c FI ]⇒ st
  where "st '=[' c ']⇒' st'" := (ceval c st st').
Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  ∀st st',
       st =[ c ]⇒ st' →
       P st →
       Q st'.
Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c at next level)
                                : hoare_spec_scope.
Lemma hoare_if1 : forall P Q b c,
    {{ fun st =>  P st /\ bassn b st }} c {{ Q }} -> {{ P }} (IF1 b THEN c FI) {{ fun st => P st \/ Q st}}.
Proof.
  intros P Q b c HTrue st st' HE HP.
  inversion HE; subst.
  - right. apply (HTrue st st'). auto.
    split. auto. apply bexp_eval_true. auto.
  - left. auto.
Qed.
End If1.

Theorem hoare_while : ∀P b c,
  {{fun st => P st ∧ bassn b st}} c {{P}} →
  {{P}} WHILE b DO c END {{fun st => P st ∧ ¬(bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember (WHILE b DO c END)%imp as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *)
    split. assumption. apply bexp_eval_false. assumption.
  - (* E_WhileTrue *)
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

Example while_example :
    {{fun st => st X ≤ 3}}
  WHILE X ≤ 2
  DO X ::= X + 1 END
    {{fun st => st X = 3}}.
Proof.
  eapply hoare_consequence_post.
  apply hoare_while.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold bassn, assn_sub, assert_implies, t_update. simpl.
    intros st [H1 H2]. apply leb_complete in H2. omega.
  unfold bassn, assert_implies. intros st [Hle Hb].
    simpl in Hb. destruct ((st X) <=? 2) eqn : Heqle.
    exfalso. apply Hb; reflexivity.
    apply leb_iff_conv in Heqle. omega.
Qed.

Theorem always_loop_hoare : ∀P Q,
  {{P}} WHILE true DO SKIP END {{Q}}.
Proof.
  intros P Q.
  apply hoare_consequence_pre with (P' := fun st : state => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  - apply hoare_post_true. intros. apply I.
  - simpl. intros st [Hinv Hguard].
    exfalso. apply Hguard. reflexivity.
  - intros st H. constructor. Qed.

Module RepeatExercise.
Inductive com : Type :=
  | CSkip : com
  | CAsgn : string → aexp → com
  | CSeq : com → com → com
  | CIf : bexp → com → com → com
  | CWhile : bexp → com → com
  | CRepeat : com → bexp → com.

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
  (CRepeat e1 b2) (at level 80, right associativity).

Reserved Notation "st '=[' c ']⇒' st'" (at level 40).
Inductive ceval : state → com → state → Prop :=
  | E_Skip : ∀st,
      st =[ SKIP ]⇒ st
  | E_Ass : ∀st a1 n x,
      aeval st a1 = n →
      st =[ x ::= a1 ]⇒ (x !-> n ; st)
  | E_Seq : ∀c1 c2 st st' st'',
      st =[ c1 ]⇒ st' →
      st' =[ c2 ]⇒ st'' →
      st =[ c1 ;; c2 ]⇒ st''
  | E_IfTrue : ∀st st' b c1 c2,
      beval st b = true →
      st =[ c1 ]⇒ st' →
      st =[ TEST b THEN c1 ELSE c2 FI ]⇒ st'
  | E_IfFalse : ∀st st' b c1 c2,
      beval st b = false →
      st =[ c2 ]⇒ st' →
      st =[ TEST b THEN c1 ELSE c2 FI ]⇒ st'
  | E_WhileFalse : ∀b st c,
      beval st b = false →
      st =[ WHILE b DO c END ]⇒ st
  | E_WhileTrue : ∀st st' st'' b c,
      beval st b = true →
      st =[ c ]⇒ st' →
      st' =[ WHILE b DO c END ]⇒ st'' →
      st =[ WHILE b DO c END ]⇒ st''
  | E_RepeatTrue : forall b st st' c,
      st =[ c ]⇒ st' ->
      beval st' b = true ->
      st =[ REPEAT c UNTIL b END ]⇒ st'
  | E_RepeatFalse : forall st st' st'' b c,
      st =[ c ]⇒ st' ->
      beval st' b = false ->
      st' =[ REPEAT c UNTIL b END ]⇒ st'' ->
      st =[ REPEAT c UNTIL b END ]⇒ st''

where "st '=[' c ']⇒' st'" := (ceval st c st').

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion)
                        : Prop :=
  ∀st st', st =[ c ]⇒ st' → P st → Q st'.
Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

Definition ex1_repeat :=
  REPEAT
    X ::= 1;;
    Y ::= Y + 1
  UNTIL X = 1 END.
Theorem ex1_repeat_works :
  empty_st =[ ex1_repeat ]⇒ (Y !-> 1 ; X !-> 1).
Proof.
  unfold ex1_repeat. apply E_RepeatTrue.
  - apply E_Seq with (X !-> 1). apply E_Ass. auto.
    apply E_Ass. auto.
  - simpl. auto.
Qed.

Lemma hoare_repeat : forall P b c, {{ P }} c {{ P }} ->
                                   {{ P }} (REPEAT c UNTIL b END) {{ fun st => P st /\ bassn b st}}.
Proof.
    intros P b c Hhoare st st' He HP.
  remember (REPEAT c UNTIL b END)%imp as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
    - split. apply (Hhoare st st'). auto. auto.
      apply bexp_eval_true. auto.
    - apply IHHe2. auto. apply (Hhoare st st'). auto. auto.
Qed.

(* LEAVING Additional Exercises. *)
