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
  | EmptyStr => false
  | Char x => true
  | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)   
  | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)   
  | Star re => re_not_empty re   
  end.

