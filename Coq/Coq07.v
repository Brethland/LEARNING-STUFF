(*
  Some exercises come from Software Foundations Book1 CH3.
  Author : Brethland.
*)

From Coq Require Import Setoid.

Fixpoint evenb(n : nat) :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair n m => n
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair n m => m
  end.

Notation "( x , y )" := (pair x y).

Definition swap (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Lemma snd_fst_is_swap : forall p : natprod, (snd p, fst p) = swap p.
Proof.
  intros.
  destruct p as [n m].
  simpl.
  auto.
Qed.

Lemma fst_swap_is_snd : forall p : natprod, fst (swap p) = snd p.
Proof.
  intros.
  destruct p as [n m].
  simpl.
  auto.
Qed.

Inductive natlist: Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l)
                      (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

Fixpoint repeat (n count : nat) :natlist :=
  match count with
  | O => nil
  | S count' => cons n (repeat n count')
  end.

Fixpoint length (p : natlist) : nat :=
  match p with
  | nil => O
  | x :: l => S (length l)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | x :: y => x :: (app y l2)
  end.

Notation "x ++ y" := (app x y)
                      (right associativity , at level 60).

Definition hd(default : nat) (l : natlist) :=
  match l with
  | nil => default
  | x :: y => x
  end.

Definition tl(l : natlist) := 
  match l with
  | nil => nil
  | x :: y => y
  end.

Fixpoint beq_n (n m :nat) :=
  match n , m with
  | O, O => true
  | O, S m' => false
  | S n', O => false
  | S n', S m' => beq_n n' m'
  end.

Lemma beq_n_refl : forall n : nat, beq_n n n = true.
Proof.
  intros.
  induction n.
  - auto.
  - trivial.
Qed.

Fixpoint nonzero (l : natlist) :=
  match l with
  | nil => nil
  | x :: y => if beq_n x O then nonzero y
                            else x :: nonzero y
  end.

Fixpoint oddnumbers (l : natlist) :=
  match l with 
  | nil => nil
  | x :: y => match evenb x with 
                    | true => oddnumbers y
                    | false => x :: oddnumbers y
                    end
  end.

Definition conutoddnumbers (l : natlist) :=
  length (oddnumbers l).

Inductive tree a :=
  | leaf
  | node : tree a -> a -> tree a -> tree a.

Check nat_rect.
Check nat_ind.
Check nat_rec.


Check tree_ind.

Fixpoint alternative (l1 l2 : natlist ) :natlist :=
  match l1,l2 with
  | nil,_ => l2
  | _,nil => l1
  | x :: y , z :: p => x :: z :: (alternative y p)
  end.

Definition bag := natlist.

Fixpoint count (ele: nat) (s : bag) :=
  match s with
  | nil => O
  | x :: y => match beq_n ele x with
              | true => S (count ele y)
              | false => count ele y
            end
  end.

Definition sum : bag -> bag -> bag := app.

Definition add (v : nat) (s : bag) :=
  v :: s.

Definition member(v : nat) (s : bag) :=
  match count v s with
  | O => false
  | _ => true
  end.

Fixpoint remove_one (v : nat) (s : bag) :=
  match s with
  | nil => nil
  | x :: y => match beq_n v x with
              | true => y
              | false => x :: (remove_one v y)
             end
  end.

Fixpoint remove_all (v : nat) (s : bag) :=
  match s with
  | nil => nil
  | x :: y => match beq_n v x with
              | true => (remove_all v y)
              | false => x :: (remove_all v y)
             end
  end.

Fixpoint subset (s1 s2 :bag) :=
  match s1 with
  | nil => true
  | x :: y => if member x s2 then subset y (remove_one x s2)
                              else false
  end.

Lemma add_and_cons: forall (x : nat) (s : bag), add x s = x :: s.
Proof.
  auto.
Qed.

(* Lemma add_1_for_count: forall (b : nat) (s : bag), count b s = 0 -> count b (add b s) = 1.
Proof.
  intros.
  destruct s.
  - simpl. rewrite <- H. simpl.
    induction b.
    + auto.
    + apply IHb. simpl. auto.
  - rewrite -> add_and_cons.

    induction b.
    + rewrite <- H. auto.
Abort. *)

Lemma silly_lemma_that_you_dont_need_if_you_use_std_lib : forall p : nat,
  beq_n p p = true.
Proof.
  intro.
  induction p.
  - trivial.
  - simpl.
    rewrite IHp.
    reflexivity.
Qed.

Lemma add_1_for_count: forall (b : nat) (s : bag),
  count b s = 0 -> count b (b :: s) = 1.
Proof.
  intros.
  unfold count.
  rewrite silly_lemma_that_you_dont_need_if_you_use_std_lib.
  fold count.
  rewrite H.
  auto.
Qed.

Fixpoint rev (l : natlist) :=
  match l with
  | nil => nil
  | x :: s => rev s ++ [x]
  end.

Compute (rev [1;2;3]).

Lemma app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros.
  induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl.
    auto.
Qed.

Lemma silly_pred : forall n : nat, n + 1 = S n.
Proof.
  intros.
  induction n.
  - auto.
  - simpl.
    rewrite <- IHn.
    auto.
Qed.


Lemma rev_length : forall l : natlist,
  length l = length (rev l).
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    rewrite -> app_length,silly_pred.
    rewrite <- IHl.
    auto.
Qed.

Lemma app_nil_r : forall l : natlist, l ++ [] = l.
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    rewrite -> IHl.
    auto.
Qed.

Lemma app_assoc : forall l1 l2 l3 : natlist,
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
  intros.
  induction l1.
  - auto.
  - simpl.
    rewrite <- IHl1.
    auto.
Qed.


Lemma rev_app_distr : forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1.
  - simpl. 
    rewrite -> app_nil_r.
    auto.
  - simpl.
    rewrite -> IHl1.
    rewrite <- app_assoc.
    auto.
Qed.

Lemma rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    rewrite -> rev_app_distr.
    rewrite -> IHl.
    auto.
Qed.

(* Lemma app_assoc4: forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = (l1 ++ (l2 ++ l3)) ++ l4.
Proof.
  intros.
  induction l1.
  - rewrite -> app_assoc.
    simpl.
    rewrite -> app_assoc.
    auto.
  - simpl.
    rewrite -> IHl1.
    auto.
Qed. *)

Lemma app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = (l1 ++ (l2 ++ l3)) ++ l4.
Proof.
  intros.
  rewrite 3 app_assoc.
  auto.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzero (l1 ++ l2) = (nonzero l1) ++ (nonzero l2).
Proof.
  intros.
  induction l1.
  - auto.
  - destruct n.
    + auto.
    + simpl.
      rewrite -> IHl1.
      auto.
Qed.

Fixpoint beq_natlist (l1 l2 : natlist) :=
  match l1 with
  | nil => match l2 with
           | nil => true
           | x :: s => false
          end
  | x :: s => match l2 with
            | nil => false
            | y :: t => if beq_n x y then beq_natlist s t
                                    else false
          end
  end.

Compute (beq_natlist [1;2;3] [1;2;4]).

Lemma beq_natlist_refl : forall l : natlist,
  beq_natlist l l = true.
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    rewrite -> beq_n_refl.
    trivial.
Qed.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Lemma count_member_nonzero : 
  forall (s : bag), leb 1 (count 1 (1 :: s)) = true.
Proof.
  intros.
  induction s.
  - auto.
  - trivial.
Qed.

Lemma ble_n_Sn : forall n : nat,
  leb n (S n) = true.
Proof.
  intros.
  induction n.
  - auto.
  - simpl. rewrite -> IHn.
    auto.
Qed.

Lemma remove_does_not_increase_count :
  forall (s : bag), leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros.
  induction s.
  - auto.
  - destruct n.
    + simpl. rewrite -> ble_n_Sn.
      auto.
    + simpl.
      trivial.
Qed.

Lemma rev_app : forall (n : nat) (l : natlist),
  rev (n :: l) = rev l ++ [n].
Proof.
  intros.
  induction l.
  - auto.
  - auto.
Qed.

Check f_equal.

Lemma rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros. rewrite <- rev_involutive. 
  rewrite <- H.
  rewrite  rev_involutive. auto.
Qed. 

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Definition hd_error (l : natlist) :=
  match l with
  | nil => None
  | x :: s => Some x
  end.

Definition option_elim (n : natoption) (d : nat) :=
  match n with
  | Some n' => n'
  | None => d
  end.

Lemma option_elim_hd : forall (l : natlist) (d : nat),
  hd d l = option_elim (hd_error l) d.
Proof.
  intros.
  induction l.
  - auto.
  - auto.
Qed.

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id (a b : id) :=
  match a,b with
  | Id a', Id b' => beq_n a' b'
  end.

Lemma beq_id_refl : forall x : id, beq_id x x = true.
Proof.
  intros.
  destruct x.
  - simpl.
    apply beq_n_refl.
Qed.

Inductive partial_map : Type :=
  | empty : partial_map
  | record : id -> nat -> partial_map -> partial_map.

Definition update (d : partial_map) (x : id) (value : nat) :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) :=
  match d with
  | empty => None
  | record y v d' => if beq_id x y then Some v
                                else find x d'
  end.

Lemma update_eq : forall (d : partial_map) (x : id) (o : nat),
  find x (update d x o) = Some o.
Proof.
  intros.
  simpl.
  rewrite -> beq_id_refl.
  auto.
Qed.

Lemma update_neq : forall (d : partial_map) (x y : id) (o : nat),
  beq_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros.
  simpl.
  rewrite -> H.
  auto.
Qed.

Inductive baz : Type :=
  | Baz1 : baz -> baz
  | Baz2 : baz -> bool -> baz.

Definition bazp (b : baz) := Baz2 b true.

Definition baz_elim (b : baz) :=
  match b with
  | Baz1 b' => b'
  | Baz2 b' _ => b'
  end.

Lemma baz_exp : forall b : baz, baz_elim (bazp b) = b.
Proof.
  intros.
  destruct b.
  - auto.
  - auto.
Qed.

 


