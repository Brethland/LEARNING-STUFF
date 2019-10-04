(*
  Exercises for <Software Foundations> CH7.
  Regular Expressions Case.
  Author : Brethland Late 2019
*)

Require Import List.
Require Import Nat.
Require Import PeanoNat.
Require Import Unicode.Utf8.
Require Export Logic. 

Inductive reg_exp {T : Type} : Type :=
  | EmptySet
  | EmptyStr
  | Char : T -> reg_exp
  | App : reg_exp -> reg_exp -> reg_exp
  | Union : reg_exp -> reg_exp -> reg_exp
  | Star : reg_exp -> reg_exp.

Notation "x :: l" := (cons x l)
                      (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar : forall x, exp_match [x] (Char x)
  | MApp : forall s1 re1 s2 re2, exp_match s1 re1 -> exp_match s2 re2 -> exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL : forall s re1 re2, exp_match s re1 -> exp_match s (Union re1 re2)
  | MUnionR : forall s re1 re2, exp_match s re2 -> exp_match s (Union re1 re2)
  | MStar0 : forall re, exp_match [] (Star re)
  | MStarApp : forall s1 s2 re, exp_match s1 re -> exp_match s2 (Star re) -> exp_match (s1 ++ s2) (Star re).
(*   | MStarApp_silly : forall s1 s2 re, exp_match s1 re -> exp_match s2 (Star re) -> exp_match (app s1 s2) (Star re). *)
(* for silly usage *)

Notation "s =~ re" := (exp_match s re) (at level 80).

Example reg_exp_ex3 : ¬ ([1; 2] =~ Char 1). Proof.   intros H. inversion H. Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=   
  match l with   
  | [] => EmptyStr 
  | x :: l' => App (Char x) (reg_exp_of_list l')   
  end.

Lemma MStar1 : ∀ T s (re : @reg_exp T) ,
   s =~ re → s =~ Star re. 
Proof.   
  intros T s re H.
  rewrite <- (@app_nil_r T s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0. 
Qed.

Lemma empty_is_empty : forall T (s : list T), ~ (s =~ EmptySet).
Proof.
  intros.
  unfold not.
  intros.
  inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 -> s =~ (Union re1 re2).
Proof.
  intros T s re1 re2 [HA | HB].
  - apply MUnionL. auto.
  - apply MUnionR. auto.
Qed.

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) :=
  match l with
  | [] => b
  | x :: s => f x (fold f s b)
  end.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
  (forall s, In s ss -> s =~ re) -> (@fold (list T) (list T) (@app T) ss []) =~ (Star re).
Proof.
  intros. generalize dependent H.
  induction ss. intros.
  - simpl. apply MStar0.
  - simpl. intros. apply MStarApp.
    + apply H. simpl. left. auto.
    + apply IHss. intros. apply H.
      right. auto.
Qed.

Lemma silly : forall T (l : list T) (a : T), a :: l = [a] ++ l.
Proof.
  intros. simpl. auto.
Qed.

Lemma reg_exp_of_list_spec : ∀ T (s1 s2 : list T),   
  s1 =~ reg_exp_of_list s2 ↔ s1 = s2.
Proof.
  intros. generalize dependent s1.
  induction s2.
  - split.
    + intros. inversion H. auto.
    + intros. rewrite H. simpl. apply MEmpty.
  - split.
    + intros. inversion H.
      inversion H3. simpl. apply IHs2 in H4. rewrite H4. auto.
    + intros. rewrite H. rewrite silly. apply MApp.
      ++ apply MChar.
      ++ apply IHs2. auto.
Qed.

Fixpoint re_chars {T} (re : reg_exp) : list T :=   
  match re with   
  | EmptySet => []   
  | EmptyStr => []   
  | Char x => [x]   
  | App re1 re2 => re_chars re1 ++ re_chars re2   
  | Union re1 re2 => re_chars re1 ++ re_chars re2   
  | Star re => re_chars re   
  end.

Lemma In_app_iff : forall X l1 l2 (x : X),
  In x (l1 ++ l2) <-> In x l1 \/ In x l2.
Proof.
  intros.
  split.
  induction l1.
  - intros. simpl in H. right. auto.
  - simpl. intros [HA | HB].
    + left. left. auto.
    + apply IHl1 in HB. (* or_assoc *)
      destruct HB.
      ++ left. right. auto.
      ++ right. auto.
  - apply in_or_app.
Qed.

Theorem in_re_match : ∀ T (s : list T) (re : reg_exp) (x : T),   
  s =~ re → In x s → In x (re_chars re).
Proof.
  intros.
  induction H.
  - inversion H0.
  - apply H0.
  - simpl. rewrite In_app_iff in *.
    destruct H0.
    + left. auto.
    + right. auto.
  - simpl. rewrite In_app_iff. left. auto.
  - simpl. rewrite In_app_iff. right. auto.
  - inversion H0.
  - rewrite In_app_iff in H0.
    destruct H0.
    + auto.
    + auto.
Qed.


Fixpoint re_not_empty {T} (re : @reg_exp T) : bool :=   
  match re with   
  | EmptySet => false
  | EmptyStr => true
  | Char x => true
  | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)   
  | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)   
  | Star re => true  
  end.

Lemma silly_orb: forall (a : bool) ,orb a true = true.
Proof.
  intros. destruct a. auto. auto.
Qed.

Lemma silly_andb : forall a b, andb a b = true -> (a = true) /\ (b = true).
Proof.
  intros.
  split.
  - destruct a. auto. inversion H.
  - destruct b. auto. destruct a. inversion H. inversion H.
Qed.

Lemma silly_orb2 : forall a b, orb a b = true -> (a = true) \/ (b = true).
Proof.
  intros.
  destruct a.
  - left. auto.
  - destruct b. right. auto. inversion H.
Qed.

Lemma re_not_empty_correct : ∀ T (re : @reg_exp T), (∃ s, s =~ re) ↔ re_not_empty re = true. 
Proof.
  split.
  - intros. destruct H. generalize dependent x. induction re.
    + intros. inversion H.
    + intros. inversion H. auto.
    + auto.
    + intros. simpl. inversion H. apply IHre1 in H3.
      apply IHre2 in H4. rewrite H3, H4. auto.
    + intros. simpl. inversion H.
      ++ apply IHre1 in H2. rewrite H2. auto.
      ++ apply IHre2 in H2. rewrite H2. apply silly_orb.
    + intros. auto.
  - intros.
    induction re.
    + inversion H.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar.
    + inversion H. apply silly_andb in H1. destruct H1.
      apply IHre1 in H0. apply IHre2 in H1. destruct H0, H1.
      exists (x ++ x0). apply MApp. auto. auto.
    + inversion H. apply silly_orb2 in H1. destruct H1.
      ++ apply IHre1 in H0. destruct H0. exists x. apply MUnionL. auto.
      ++ apply IHre2 in H0. destruct H0. exists x. apply MUnionR. auto.
    + exists []. apply MStar0.
Qed.

Lemma star_app: ∀ T (s1 s2 : list T) (re : reg_exp), s1 =~ Star re → s2 =~ Star re → s1 ++ s2 =~ Star re. 
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'. intros. simpl. auto.
  - inversion Heqre'. intros. rewrite H0 in IHexp_match2, H1_. 
    rewrite <- (app_assoc). apply MStarApp.
    + auto.
    + apply IHexp_match2. auto. auto.
Qed.

Lemma MStar'' : ∀ T (s : list T) (re : reg_exp), s =~ Star re → 
  ∃ ss : list (list T), s = (@fold (list T) (list T) (@app T) ss []) ∧ ∀ s', In s' ss → s' =~ re.
Proof.
  intros.
  remember (Star re) as re'.
  induction H.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'. exists []. simpl.
    split. auto. intros. inversion H.
  - inversion Heqre'.
    apply IHexp_match2 in Heqre'. destruct Heqre'.
    exists ([s1] ++ x).
    destruct H1. simpl. rewrite H1. split.
    auto. intros.
    destruct H4.
    + rewrite <- H4. rewrite H2 in H. auto.
    + apply H3. auto.
Qed.

Module Pumping. 
Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=   
  match re with   
  | EmptySet => 0   
  | EmptyStr => 1   
  | Char _ => 2   
  | App re1 re2 => pumping_constant re1 + pumping_constant re2   
  | Union re1 re2 => pumping_constant re1 + pumping_constant re2   
  | Star _ => 1   
  end.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=   
  match n with   
  | 0 => []   
  | S n' => l ++ napp n' l   
  end. 

Lemma napp_plus: ∀ T (n m : nat) (l : list T), napp (n + m) l = napp n l ++ napp m l. 
Proof.   
  intros T n m l.
  induction n as [|n IHn]. 
  - reflexivity. 
  - simpl. rewrite IHn, app_assoc. reflexivity. 
Qed.

Require Import Coq.omega.Omega.

Lemma n_le_m__Sn_le_Sm : forall n m, n <= m -> S n <= S m.
Proof.
  intros. omega.
Qed.

Lemma le_add: forall (a b c: nat), b <= c -> (a + b <= a + c).
Proof. intros. omega. Qed.

Lemma app_length' : forall T (l1 l2 : list T) (a b : nat), 
  (a <= length l1) -> (b <= length l2) -> (a + b <= length (l1 ++ l2)).
Proof.
  intros.
  generalize dependent l2.
  induction l1.
  - intros. simpl. inversion H. simpl in H1. simpl. auto.
  - intros. simpl. simpl in H. inversion H.
    + rewrite (plus_Sn_m (length l1) b). apply n_le_m__Sn_le_Sm.
      rewrite app_length. apply le_add. auto.
    + apply le_S. apply IHl1.
      auto. auto.
Qed.

Lemma le_orb_plus : forall a b c d, a + b <= c + d -> (a <= c) \/ (b <= d).
Proof.
  intros. omega.
Qed.

Lemma app_length_inj : forall T (l1 l2 l3 : list T), l2 = l3 -> l2 ++ l1 = l3 ++ l1.
Proof.
  intros. rewrite H. auto.
Qed.

Lemma app_length_inj' : forall T (l1 l2 l3 : list T), l2 = l3 -> l1 ++ l2 = l1 ++ l3.
Proof.
  intros. rewrite H. auto.
Qed.

Lemma app_length_nil : forall T (l1 l2 : list T), 1 <= length l1 + length l2 -> (l1 <> []) \/ (l2 <> []).
Proof. 
  intros. destruct l1, l2.
  - inversion H.
  - right. unfold not. intros. inversion H0.
  - left. unfold not. intros. inversion H0.
  - left. unfold not. intros. inversion H0.
Qed.

Lemma not_nil_ge_0 : forall T (l : list T), l <> [] -> 1 <= length l.
Proof.
  intros. destruct l.
  - unfold not in H. destruct H. auto.
  - simpl. omega.
Qed.

Lemma pumping : ∀ T (re : @reg_exp T) s, 
  s =~ re → pumping_constant re ≤ length s → 
  ∃ s1 s2 s3, s = s1 ++ s2 ++ s3 ∧ s2 ≠ [] ∧ ∀ m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
                        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
                        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - simpl. omega.
  - simpl. omega.
  - simpl. intros. 
    rewrite app_length in H.
    apply le_orb_plus in H. destruct H.
    + apply IH1 in H.
      destruct H as [x1 [x2 [x3 [H1 [H2 H3]]]]].
      exists x1, x2, (x3 ++ s2). split. 
      rewrite (app_assoc x1 x2 (x3 ++ s2)).
      rewrite (app_assoc (x1 ++ x2) x3 s2). rewrite <- (app_assoc x1 x2 x3).
      apply (app_length_inj T s2 s1 (x1 ++ x2 ++ x3)). auto. split.
      auto. intros. rewrite (app_assoc x1 (napp m x2) (x3 ++ s2)).
      rewrite (app_assoc (x1 ++ napp m x2) x3 s2). rewrite <- (app_assoc x1 (napp m x2) x3).
      apply (MApp (x1 ++ napp m x2 ++ x3) re1 s2 re2). auto. auto.
    + apply IH2 in H.
      destruct H as [x1 [x2 [x3 [H1 [H2 H3]]]]].
      exists (s1 ++ x1), x2, x3. split.
      rewrite <- (app_assoc s1 x1 (x2 ++ x3)).
      apply (app_length_inj' T s1 s2 (x1 ++ x2 ++ x3)). auto. split. auto.
      intros. 
      rewrite <- (app_assoc s1 x1 (napp m x2 ++ x3)). apply MApp. auto. auto.
  - simpl. intros.
    assert (H1 : pumping_constant re1 + pumping_constant re2 ≤ length s1 -> 
                pumping_constant re1 <= length s1). omega. apply H1, IH in H.
    destruct H as [x1 [x2 [x3 [H2 [H3 H4]]]]].
    exists x1, x2, x3. split. auto. split. auto.
    intros. apply MUnionL. auto.
  - simpl. intros. 
    assert (H1 : pumping_constant s2 + pumping_constant re2 ≤ length re1 -> 
                pumping_constant re2 <= length re1). omega. apply H1, IH in H.
    destruct H as [x1 [x2 [x3 [H2 [H3 H4]]]]].
    exists x1, x2, x3. split. auto. split. auto.
    intros. apply MUnionR. auto.
  - simpl. omega.
  - simpl. intros.
    simpl in IH2. rewrite app_length in H.
    apply app_length_nil in H.
    destruct H.
    + exists [], s1, s2.
      simpl. split. auto.
      split. auto. intros. induction m.
      ++ simpl. auto.
      ++ simpl. rewrite <- app_assoc. apply MStarApp. auto. auto.
    + apply not_nil_ge_0, IH2 in H.
      destruct H as [x1 [x2 [x3 [H1 [H2 H3]]]]].
      exists (s1 ++ x1), x2, x3. split.
      rewrite <- (app_assoc s1 x1 (x2 ++ x3)).
      apply (app_length_inj' T s1 s2 (x1 ++ x2 ++ x3)). auto. split. auto.
      intros. rewrite <- (app_assoc s1 x1 (napp m x2 ++ x3)). apply MStarApp. auto. auto.
Qed.


