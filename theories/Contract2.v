Require Import Lists.List.
Require Import FunInd.
Require Import Bool.Bool.
Require Import Bool.Sumbool.
Require Import Structures.GenericMinMax.
From Equations Require Import Equations.
Import ListNotations.
Require Import micromega.Lia.
Require Import Setoid.
Require Import Init.Tauto btauto.Btauto.
Require Import Logic.ClassicalFacts.

(** printing =~ %$=\sim$% *)

(* Set Implicit Arguments. *)




Inductive EventType : Type :=
| Transfer : EventType
| Notify : EventType.

Scheme Equality for EventType.


Definition Trace := List.list EventType % type.

Inductive Contract : Set :=
| Success : Contract
| Failure : Contract
| Event : EventType -> Contract
| CPlus : Contract -> Contract -> Contract
| CSeq : Contract -> Contract -> Contract.

Notation "e _._ c" := (CSeq (Event e) c)
                    (at level 51, right associativity).

Notation "c0 _;_ c1"  := (CSeq c0 c1)
                         (at level 52, left associativity).

Notation "c0 _+_ c1"  := (CPlus c0 c1)
                         (at level 53, left associativity).

Scheme Equality for Contract.


Fixpoint nu(c:Contract):bool :=
match c with
| Success => true
| Failure => false
| Event e => false
| c0 _;_ c1 => nu c0 && nu c1
| c0 _+_ c1 => nu c0 || nu c1
end.

Definition o (c : Contract) := if nu c then Success else Failure.
Hint Unfold o : core.

Lemma o_Failure : o Failure = Failure.
Proof. reflexivity.
Qed.

Lemma o_Success : o Success = Success.
Proof. reflexivity.
Qed.


Lemma o_or : forall (c : Contract), o c = Success /\ nu c = true \/ o c = Failure /\ nu c = false.
Proof.
intros. unfold o. destruct (nu c) eqn:Heqn; intuition.
Qed.

Lemma o_idempotent : forall (c : Contract), o (o c) = o c.
Proof.
intros. destruct (o_or c). destruct H. rewrite H;auto. destruct H. now rewrite H. 
Qed.

Hint Rewrite o_Failure o_Success o_idempotent : cDB.

Reserved Notation "e \ c" (at level 40, left associativity).
Fixpoint derive (e:EventType) (c:Contract) :Contract :=
match c with
| Success => Failure
| Failure => Failure
| Event e' => if (EventType_eq_dec e' e) then Success else Failure
| c0 _;_ c1 => o c0 _;_ e \ c1 _+_ e \ c0 _;_ c1
| c0 _+_ c1 => e \ c0 _+_ e \ c1
end
where "e \ c" := (derive e c).

Ltac destruct_ctx :=
  repeat match goal with
         | [ H: ?H0 /\ ?H1 |- _ ] => destruct H
         | [ H: exists _, _  |- _ ] => destruct H
         end.

Ltac o_destruct :=
  match goal with
         | [ |- context[(o ?c)] ] => destruct (o_or c);destruct_ctx
         | [ _ : context[ (o ?c)] |- _ ] => let H := fresh "H" in 
                                            let H1 := fresh "H1" in 
                                            destruct (o_or c) as [[H H1] | [H H1]];
                                            rewrite H in*;clear H
         end.

Lemma o_derive : forall c e, e \ (o c) = Failure.
Proof.
intros. o_destruct. unfold o. rewrite H0. now simpl. unfold o. rewrite H0. now simpl.
Qed.

Hint Rewrite o_idempotent o_derive : cDB.
Ltac autoIC := auto with cDB.


(*Removed because it is not needed in this file*)
(*
Inductive Trace_Derive : Contract -> Trace -> Contract -> Prop :=
| Trace_Derive_Nil c : Trace_Derive c [] c
| Trace_Derive_Cons c s c' e (H: Trace_Derive (c/e) s c') : Trace_Derive c (e::s) c'. (*rule motivated by constructor being analgous to cons on lists*)
Hint Constructors Trace_Derive : cDB.


Lemma Trace_Derive_trans : forall s s' c0 c1 c2 , Trace_Derive c0 s c1 -> Trace_Derive c1 s' c2 -> Trace_Derive c0 (s++s') c2.
Proof.
intros. induction H;simpl;autoIC.
Qed.*)


Reserved Notation "s \\ c" (at level 42, no associativity).
Fixpoint trace_derive (s : Trace) (c : Contract)  : Contract :=
match s with
| [] => c
| e::s' => s' \\ (e \ c)
end
where "s \\ c" := (trace_derive s c).

(*
Lemma trace_derive_spec : forall (c c' : Contract)(s : Trace), c // s = c' <-> Trace_Derive c s c'.
Proof.
split;intros.
- funelim (trace_derive c s);simpl;autoIC.
- induction H;auto. 
Qed.

Lemma trace_derive_spec2 : forall (c : Contract)(s : Trace), Trace_Derive c s (c // s).
Proof.
intros. remember (c//s). symmetry in Heqc0. now rewrite <- trace_derive_spec.
Qed.*)


Definition matchesb (c : Contract)(s : Trace) := nu (s\\c).


Reserved Notation "s =~ re" (at level 63).

Inductive Matches_Comp : Trace -> Contract -> Prop :=
  | MSuccess : [] =~ Success
  | MEvent x : [x] =~ (Event x)
  | MSeq s1 c1 s2 c2
             (H1 : s1 =~ c1)
             (H2 : s2 =~ c2)
           : (s1 ++ s2) =~ (c1 _;_ c2)
  | MPlusL s1 c1 c2
                (H1 : s1 =~ c1)
              : s1 =~ (c1 _+_ c2)
  | MPlusR c1 s2 c2
                (H2 : s2 =~ c2)
              : s2 =~ (c1 _+_ c2)
 (* | MStar0 c 
              : [] =~ Star c
  | MStarSeq c s1 s2 (H1: s1 =~ c) 
                     (H2: s2 =~ Star c) 
              : s1 ++ s2 =~ Star c*)
  where "s =~ c" := (Matches_Comp s c).

(*Derive Signature for Matches_Comp.*)

Hint Constructors Matches_Comp : cDB.

Ltac eq_event_destruct :=
  repeat match goal with
         | [ |- context[EventType_eq_dec ?e ?e0] ] => destruct (EventType_eq_dec e e0);try contradiction
         | [ _ : context[EventType_eq_dec ?e ?e0]  |- _ ] => destruct (EventType_eq_dec e e0);try contradiction
         end.

Lemma seq_Success : forall c s, s =~ Success _;_ c <-> s =~ c.
Proof.
split;intros. inversion H. inversion H3. subst. now simpl.
rewrite <- (app_nil_l s). autoIC.
Qed. 

Lemma seq_Failure : forall c s, s =~ Failure _;_ c <-> s =~ Failure.
Proof.
split;intros. inversion H. inversion H3. inversion H.
Qed.

Hint Resolve seq_Success seq_Failure : cDB.

(*
Lemma o_or : forall (c0 c1 : Contract)(s : Trace), s =~ o c0 _;_ c1 -> nu c0 = true /\ s =~ c1 \/ nu c0 = false /\ s =~ Failure.
Proof.
intros. o_destruct. unfold o in H. destruct (nu c0). funelim (o c0).
- rewrite <- Heqcall in H. rewrite seq_Success in H. now left.
- rewrite <- Heqcall in H. rewrite seq_Failure in H. now right.
Qed.*)

Lemma derive_distr_plus : forall (s : Trace)(c0 c1 : Contract), s \\ (c0 _+_ c1) = s \\ c0 _+_ s \\ c1.
Proof.
induction s;intros;simpl;auto.
Qed. 
Check existsb.
(*Lemma nu_derive_disjuncts_seq : forall s c0 c1, nu (s \\ (c0 _;_ c1)) = existsb (fun ss => nu ((fst ss) \\ c0) && nu (snd ss) \\ c1)*)

Lemma o_true : forall (c: Contract), nu c = true -> o c = Success.
Proof.
intros. o_destruct;auto with cDB. rewrite H in H1. discriminate. 
Qed.

Lemma o_false : forall (c: Contract), nu c = false -> o c = Failure.
Proof.
intros. o_destruct. rewrite H in H1. discriminate. auto. 
Qed.

Hint Rewrite derive_distr_plus : cDB.

Lemma nu_seq_derive : forall (e : EventType)(c0 c1 : Contract), 
nu c0 = true -> nu (e \ c1) = true -> nu (e \ (c0 _;_ c1)) = true.
Proof.
intros. simpl. rewrite orb_true_iff. left. rewrite o_true;auto.
Qed.

(*Not needed*)
(*
Lemma nu_plus : forall c0 c1, nu (c0 _+_ c1) = true <-> nu c0 = true \/ nu c1 = true.
Proof.
intros. simpl. now rewrite orb_true_iff.
Qed.*)

Lemma nu_Failure : forall (s : Trace)(c : Contract), nu (s \\ (Failure _;_ c)) = false.
Proof.
induction s;intros. now simpl. simpl. rewrite o_false;auto.
rewrite derive_distr_plus. simpl. now repeat rewrite IHs.
Qed.

Hint Rewrite nu_Failure : cDB.

Lemma nu_Success : forall (s : Trace)(c : Contract), nu (s \\ (Success _;_ c)) = nu (s \\ c).
Proof.
induction s;intros;simpl;auto. 
autorewrite with cDB using simpl;auto. rewrite orb_false_r. auto. 
Qed.

Hint Rewrite nu_Failure nu_Success : cDB.

Lemma nu_seq_trace_derive : forall (s : Trace)(c0 c1 : Contract), 
nu c0 = true -> nu (s \\ c1) = true -> nu (s \\ (c0 _;_ c1)) = true.
Proof.
induction s;intros;simpl in *. intuition.
rewrite o_true;auto. rewrite derive_distr_plus. simpl. autorewrite with cDB.
rewrite H0. btauto.
Qed.

Lemma matchesb_seq : forall (s0 s1 : Trace)(c0 c1 : Contract), nu (s0\\c0) = true -> nu (s1\\c1) = true -> nu ((s0++s1)\\(c0 _;_c1)) = true.
Proof.
induction s0;intros;simpl in *.
- rewrite nu_seq_trace_derive; auto. 
- autorewrite with cDB. simpl. rewrite orb_true_iff. right. 
  rewrite IHs0;auto.
Qed.

Hint Rewrite matchesb_seq : cDB.

Print HintDb cDB.

Lemma Matches_Comp_i_matchesb : forall (c : Contract)(s : Trace), s =~ c -> nu (s\\c) = true.
Proof.
intros; induction H; 
solve [ autorewrite with cDB; simpl; auto with bool 
      | simpl;eq_event_destruct;auto ].
Qed.

Lemma Matches_Comp_nil_nu : forall (c : Contract), nu c = true -> [] =~ c.
Proof.
intros;induction c; simpl in H ; try discriminate; autoIC. apply orb_prop in H. destruct H; autoIC.
rewrite <- (app_nil_l []); autoIC.
Qed.



(*This direction with longer trace on the right because of induction step on trace*)
Lemma Matches_Comp_derive : forall (c : Contract)(e : EventType)(s : Trace), s =~ e \ c-> (e::s) =~ c.
Proof.
induction c;intros; simpl in*; try solve [inversion H].
- eq_event_destruct. inversion H. subst. autoIC. inversion H.
- inversion H; autoIC. (*apply IH directly*) 
- inversion H.
  * inversion H2. subst. o_destruct. 
    inversion H7. simpl. 
    rewrite <- (app_nil_l (e::s2)). constructor.
    all: auto using Matches_Comp_nil_nu. 
    inversion H7.
  * inversion H1. subst. rewrite app_comm_cons. 
    auto with cDB.
Qed.




Lemma Matches_Comp_iff_matchesb : forall (c : Contract)(s : Trace), s =~ c <-> nu (s \\ c) = true.
Proof.
split;intros.
- auto using Matches_Comp_i_matchesb.
- generalize dependent c. induction s;intros. 
  simpl in H. auto using Matches_Comp_nil_nu.
  auto using Matches_Comp_derive.
Qed.


Lemma derive_spec_comp : forall (c : Contract)(e : EventType)(s : Trace), e::s =~ c <-> s =~ e \ c.
Proof.
intros. repeat rewrite Matches_Comp_iff_matchesb.  reflexivity.
Qed.


(*
Lemma Matches_Comp_nil : forall (c : Contract), nu c = true <-> [] =~ c.
Proof.
split;intros.
- induction c; simpl in H ; try discriminate; autoIC. apply orb_prop in H. destruct H; autoIC.
  rewrite <- (app_nil_l []); autoIC.
- induction c;autoIC; inversion H; simpl; intuition. 
  apply app_eq_nil in H1 as [H1 H1']. subst. intuition. 
Qed.

*)

Fixpoint plus_fold (l : list Contract) : Contract :=
match l with
| [] => Failure
| c ::l => c _+_ (plus_fold l)
end.

Lemma plus_assoc : forall (c1 c2 c3 : Contract), (forall s, s=~((c1 _+_ c2) _+_ c3) <-> s =~ (c1 _+_ (c2 _+_ c3))).
Proof.
split;intros. inversion H;autoIC. inversion H2;autoIC. inversion H;autoIC. inversion H1;autoIC.
Qed.

Lemma plus_fold_app : forall (s:Trace)(l1 l2 : list Contract), 
s =~ plus_fold (l1 ++ l2) <-> s =~ (plus_fold l1) _+_ (plus_fold l2).
Proof.
intro. induction l1.
- intros. split.
  * intros. simpl in H. autoIC.
  * intros. simpl. simpl in H. inversion H. {  inversion H2. } assumption.
- intros. split.
  * intros. simpl in *. inversion H ; autoIC. subst.
    rewrite IHl1 in H1. rewrite plus_assoc. apply MPlusR;autoIC. 
  * intros. simpl in *. apply plus_assoc in H. inversion H;autoIC.
    apply MPlusR. rewrite IHl1. autoIC. 
Qed.


Lemma in_plus_fold : forall (s : Trace)(l : list Contract), s =~ plus_fold l <-> 
(exists c, In c l /\ s =~ c).
Proof.
intros. split.
- induction l.
  * intros. simpl in H. inversion H.
  * intros. simpl in H. inversion H;autoIC. 
    ** exists a. split. apply in_eq. assumption.
    ** apply IHl in H1 as [c' [P1 P2]]. exists c'. split ; auto using  in_cons.
- intros. destruct H as [ c' [P1 P2]]. induction l.
  * destruct P1.
  * simpl in P1. destruct P1.
    ** subst. simpl. autoIC.
    ** simpl. autoIC.
Qed.

Lemma plus_fold_derive : forall (l : list Contract) (e : EventType), e \ (plus_fold l) = plus_fold (map (fun c => e \ c) l).
Proof.
induction l;intros;simpl;auto;f_equal;auto.
Qed.

