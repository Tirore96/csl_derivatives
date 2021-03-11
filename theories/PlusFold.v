Require Import Lists.List.
Require Import Program.
Import ListNotations.
Require Import CSL.Contract.

Set Implicit Arguments.

Hint Constructors matches_comp : core.

(*plus_fold is useful in ContractEquations so has been extracted
  from ParallelContract to a separate file*)

Fixpoint plus_fold (l : list Contract) : Contract :=
match l with
| [] => Failure
| c ::l => c _+_ (plus_fold l)
end.


Lemma plus_fold_app : forall (s:Trace)(l1 l2 : list Contract), 
s ==~ plus_fold (l1 ++ l2) <-> s ==~ (plus_fold l1) _+_ (plus_fold l2).
Proof.
intro. induction l1.
- intros. split.
  * intros. simpl in H. auto.
  * intros. simpl. simpl in H. inversion H. {  inversion H2. } assumption.
- intros. split.
  * intros. simpl in *. apply plus_or in H as [H | H] ; auto.
    specialize IHl1 with l2. apply IHl1 in H. apply plus_assoc. auto.
  * intros. simpl in *. apply plus_assoc in H. apply plus_or in H as [H | H].
    ** auto.
    ** apply MPlusR. apply IHl1. assumption.
Qed.


Lemma in_plus_fold : forall (s : Trace)(l : list Contract), s ==~ plus_fold l <-> 
(exists c, In c l /\ s ==~ c).
Proof.
intros. split.
- induction l.
  * intros. simpl in H. inversion H.
  * intros. simpl in H. apply plus_or in H as [H | H].
    ** exists a. split. apply in_eq. assumption.
    ** apply IHl in H as [c' [P1 P2]]. exists c'. split ; auto using  in_cons.
- intros. destruct H as [ c' [P1 P2]]. induction l.
  * destruct P1.
  * apply in_inv in P1 as [P1 | P1].
    ** simpl. rewrite P1. auto.
    ** simpl. auto.
Qed.






Fixpoint seq_fold (l : list Contract) :=
match l with
| [] => Success
| a::l' => a _;_ (seq_fold l')
end.



Lemma seq_fold_map : forall (s:Trace), s ==~ seq_fold (map Event s).
Proof.
induction s.
- simpl. auto.
- simpl. assert (HA: a::s = [a]++s). { reflexivity. } rewrite HA. constructor; auto.
Qed.


