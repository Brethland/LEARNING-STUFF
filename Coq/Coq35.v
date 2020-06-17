(*
  This is the exercise for <Software Foundations> V2 CH11.
  Author: Brethland, Early 2020.
*)

Require Import Strings.String.
Add LoadPath "C:\Users\ycy12\Documents\Workspace\LEARNING-STUFF\Coq".
Load Coq32.

Import STLC.

Fixpoint eqb_ty (T1 T2:ty) : bool :=
  match T1,T2 with
  | Bool, Bool =>
      true
  | Arrow T11 T12, Arrow T21 T22 =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | _,_ =>
      false
  end.

Lemma eqb_ty_refl : forall T1, eqb_ty T1 T1 = true.
Proof.
  intros. induction T1;simpl;auto.
  rewrite IHT1_1, IHT1_2. auto.
Qed.

Lemma eqb_ty_eq: forall T1 T2, eqb_ty T1 T2 = true -> T1 = T2.
Proof.
  intros T1. induction T1;intros;simpl in *;destruct T2;auto.
  1 - 2: inversion H.
  rewrite andb_true_iff in H;destruct H. apply (IHT1_1 T2_1) in H.
  apply (IHT1_2 T2_2) in H0. subst;auto.
Qed.

Module STLCChecker.
  Import STLC.

  Notation " x <- e1 <| e2" := (match e1 with
                              | Some x => e2
                              | None => None
                              end)
         (right associativity, at level 60).

Notation " 'return' e "
  := (Some e) (at level 70).
Notation " 'fail' "
  := None.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | var x =>
      match Gamma x with
      | Some T => return T
      | None => fail
      end
  | abs x T11 t12 =>
      T12 <- type_check (update Gamma x T11) t12 <|
      return (Arrow T11 T12)
  | app t1 t2 =>
      T1 <- type_check Gamma t1 <|
      T2 <- type_check Gamma t2 <|
      (match T1 with
      | Arrow T11 T12 =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end)
  | tru =>
      return Bool
  | fls =>
      return Bool
  | test guard t1 t2 =>
      Tguard <- type_check Gamma guard <|
      T1 <- type_check Gamma t1 <|
      T2 <- type_check Gamma t2 <|
      match Tguard with
      | Bool =>
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  end.

Theorem type_checking_sound : ÅÕGamma t T,
  type_check Gamma t = Some T Å® has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma. induction t;intros;simpl in *...

  destruct (Gamma s) eqn: Hn.  inversion H. subst. eauto.
  inversion H.
Abort.

Theorem type_checking_complete : ÅÕGamma t T,
  has_type Gamma t T Å® type_check Gamma t = Some T.
Proof with auto.
  intros;induction H;simpl in *.

  destruct (Gamma x0) eqn:H0; assumption.
  rewrite IHhas_type...

  rewrite IHhas_type1, IHhas_type2. rewrite (eqb_ty_refl T11)...

  1 - 2 : auto.

  rewrite IHhas_type1, IHhas_type2, IHhas_type3, (eqb_ty_refl T)...
Qed.

(* Leaving Exercises *)
