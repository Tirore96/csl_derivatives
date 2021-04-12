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
| CSeq : Contract -> Contract -> Contract
| Star : Contract -> Contract.

Notation "e _._ c" := (CSeq (Event e) c)
                    (at level 51, right associativity).

Notation "c0 _;_ c1"  := (CSeq c0 c1)
                         (at level 52, left associativity).

Notation "c0 _+_ c1"  := (CPlus c0 c1)
                         (at level 53, left associativity).

Scheme Equality for Contract.


(*For a nullary contract c, nu c = true*)
Fixpoint nu(c:Contract):bool :=
match c with
| Success => true
| Failure => false
| Event e => false
| c0 _;_ c1 => nu c0 && nu c1
| c0 _+_ c1 => nu c0 || nu c1
| Star c => true
end.

Definition o (c : Contract) := if nu c then Success else Failure.
Hint Unfold o : core.


(*Derivative of contract with respect to an event*)
Equations derive (c:Contract) (e:EventType) :Contract :=
derive Success e := Failure;
derive Failure e := Failure;
derive (Event e') e := if (EventType_eq_dec e' e) then Success else Failure;
derive (c0 _;_ c1) e := (derive c0 e) _;_ c1 _+_ (o c0) _;_ (derive c1 e);
derive (c0 _+_ c1) e := (derive c0 e) _+_ (derive c1 e);
derive (Star c) e := derive c e _;_ (Star c).

Global Transparent derive.

Notation "c / e" := (derive c e)(at level 40, left associativity).

Inductive Trace_Derive : Contract -> Trace -> Contract -> Prop :=
| Trace_Derive_Nil c : Trace_Derive c [] c
| Trace_Derive_Cons c s c' e (H: Trace_Derive (c/e) s c') : Trace_Derive c (e::s) c'. (*rule motivated by constructor being analgous to cons on lists*)
Hint Constructors Trace_Derive : MatchDB.

Ltac autoM := auto with MatchDB.

Lemma Trace_Derive_trans : forall s s' c0 c1 c2 , Trace_Derive c0 s c1 -> Trace_Derive c1 s' c2 -> Trace_Derive c0 (s++s') c2.
Proof.
intros. induction H;simpl;autoM.
Qed.



Equations trace_derive (c : Contract) (s : Trace) : Contract :=
trace_derive c [] := c;
trace_derive c (e::s') := trace_derive (c/e) s'.
Global Transparent trace_derive.

Notation "c // s" := (trace_derive c s)(at level 42, left associativity).

Lemma trace_derive_spec : forall (c c' : Contract)(s : Trace), c // s = c' <-> Trace_Derive c s c'.
Proof.
split;intros.
- funelim (trace_derive c s);simpl;autoM.
- induction H;auto. 
Qed.

Lemma trace_derive_spec2 : forall (c : Contract)(s : Trace), Trace_Derive c s (c // s).
Proof.
intros. remember (c//s). symmetry in Heqc0. now rewrite <- trace_derive_spec.
Qed.


Definition matchesb (c : Contract)(s : Trace) := nu (c//s).


Reserved Notation "s ==~ re" (at level 63).

Inductive Matches_Comp : Trace -> Contract -> Prop :=
  | MSuccess : [] ==~ Success
  | MEvent x : [x] ==~ (Event x)
  | MSeq s1 c1 s2 c2
             (H1 : s1 ==~ c1)
             (H2 : s2 ==~ c2)
           : (s1 ++ s2) ==~ (c1 _;_ c2)
  | MPlusL s1 c1 c2
                (H1 : s1 ==~ c1)
              : s1 ==~ (c1 _+_ c2)
  | MPlusR c1 s2 c2
                (H2 : s2 ==~ c2)
              : s2 ==~ (c1 _+_ c2)
  | MStar0 c 
              : [] ==~ Star c
  | MStarSeq c s1 s2 (H1: s1 ==~ c) 
                     (H2: s2 ==~ Star c) 
              : s1 ++ s2 ==~ Star c
  where "s ==~ c" := (Matches_Comp s c).

Derive Signature for Matches_Comp.

Hint Constructors Matches_Comp : MatchDB.

Ltac eq_event_destruct :=
  repeat match goal with
         | [ |- context[if EventType_eq_dec ?e ?e then _ else _] ] => destruct (EventType_eq_dec e e);try contradiction
         | [ |- context[if EventType_eq_dec ?e ?e0 then _ else _] ] => destruct (EventType_eq_dec e e0)
         | [ _ : context[if EventType_eq_dec ?e ?e then _ else _]  |- _ ] => destruct (EventType_eq_dec e e);try contradiction
         | [ _ : context[if EventType_eq_dec ?e ?e0 then _ else _] |- _ ] => destruct (EventType_eq_dec e e0)
         end.

Lemma o_or : forall (c : Contract), o c = Success /\ nu c = true \/ o c = Failure /\ nu c = false.
Proof.
intros. unfold o. destruct (nu c) eqn:Heqn; intuition.
Qed.

Ltac destruct_ctx :=
  repeat match goal with
         | [ H: ?H0 /\ ?H1 |- _ ] => destruct H
         | [ H: exists _, _  |- _ ] => destruct H
         end.

Ltac o_destruct :=
  match goal with
         | [ |- context[(o ?c)] ] => destruct (o_or c);destruct_ctx
         | [ _ : context[ (o ?c)] |- _ ] => destruct (o_or c);destruct_ctx
         end.

Lemma seq_Success : forall c s, s ==~ Success _;_ c <-> s ==~ c.
Proof.
split;intros. inversion H. inversion H3. subst. now simpl.
rewrite <- (app_nil_l s). autoM.
Qed. 

Lemma seq_Failure : forall c s, s ==~ Failure _;_ c <-> s ==~ Failure.
Proof.
split;intros. inversion H. inversion H3. inversion H.
Qed.

(*
Lemma o_or : forall (c0 c1 : Contract)(s : Trace), s ==~ o c0 _;_ c1 -> nu c0 = true /\ s ==~ c1 \/ nu c0 = false /\ s ==~ Failure.
Proof.
intros. o_destruct. unfold o in H. destruct (nu c0). funelim (o c0).
- rewrite <- Heqcall in H. rewrite seq_Success in H. now left.
- rewrite <- Heqcall in H. rewrite seq_Failure in H. now right.
Qed.*)

Lemma derive_plus : forall (s : Trace)(c0 c1 : Contract), (c0 _+_ c1) // s = c0//s _+_ c1//s.
Proof.
induction s;intros;simpl;auto.
Qed. 

Lemma o_true : forall (c: Contract), nu c = true -> o c = Success.
Proof.
intros. o_destruct;auto with MatchDB. rewrite H in H1. discriminate. 
Qed.

Lemma o_false : forall (c: Contract), nu c = false -> o c = Failure.
Proof.
intros. o_destruct. rewrite H in H1. discriminate. auto. 
Qed.

Hint Rewrite derive_plus  : MatchDB.

Lemma nu_seq_derive : forall (e : EventType)(c0 c1 : Contract), 
nu c0 = true -> nu (c1 / e) = true -> nu ((c0 _;_ c1) / e) = true.
Proof.
intros. simpl. rewrite orb_true_iff. right. rewrite o_true;auto.
Qed.

Lemma nu_plus : forall c0 c1, nu (c0 _+_ c1) = true <-> nu c0 = true \/ nu c1 = true.
Proof.
intros. simpl. now rewrite orb_true_iff.
Qed.

Lemma nu_Failure : forall (s : Trace)(c : Contract), nu ((Failure _;_ c)//s) = false.
Proof.
induction s;intros. now simpl. simpl. rewrite o_false;auto.
rewrite derive_plus. simpl. now repeat rewrite IHs.
Qed.

Lemma nu_Success : forall (s : Trace)(c : Contract), nu ((Success _;_ c)//s) = nu (c//s).
Proof.
induction s;intros;simpl;auto. simp o. rewrite derive_plus.
simpl. rewrite nu_Failure. simpl. now rewrite IHs.
Qed.

Hint Rewrite nu_Failure nu_Success : MatchDB.

Lemma nu_seq_trace_derive : forall (s1 : Trace)(c0 c1 : Contract), 
nu c0 = true -> nu (c1 // s1) = true -> nu ((c0 _;_ c1) // s1) = true.
Proof.
induction s1;intros;simpl in *. intuition.
rewrite o_true;auto. rewrite derive_plus. simpl. autorewrite with MatchDB.
rewrite H0. now rewrite orb_comm.
Qed.

Lemma matchesb_seq : forall (s0 s1 : Trace)(c0 c1 : Contract), nu (c0//s0) = true -> nu (c1//s1) = true -> nu ((c0 _;_c1) // (s0++s1)) = true.
Proof.
induction s0;intros;simpl in *.
- rewrite nu_seq_trace_derive; auto. 
- autorewrite with MatchDB. simpl. rewrite orb_true_iff. left.
  rewrite IHs0;auto.
Qed.

Lemma Matches_Comp_i_matchesb : forall (c : Contract)(s : Trace), s ==~ c -> nu (c//s) = true.
Proof.
intros. induction H;auto.
- simpl. eq_event_destruct. reflexivity.
- rewrite matchesb_seq;auto.
- autorewrite with MatchDB. simpl. intuition.
- autorewrite with MatchDB. simpl. intuition.
- destruct s1. now simpl. simpl. rewrite matchesb_seq;auto.
Qed.


Lemma Matches_Comp_nil : forall (c : Contract), nu c = true <-> [] ==~ c.
Proof.
split;intros.
- induction c; simpl in H ; try discriminate; autoM. apply orb_prop in H. destruct H; autoM.
  rewrite <- (app_nil_l []); autoM.
- induction c;autoM; inversion H; simpl; intuition. 
  apply app_eq_nil in H1 as [H1 H1']. subst. intuition. 
Qed.

Lemma Matches_Comp_derive : forall (c : Contract)(e : EventType)(s : Trace), s ==~ c / e -> (e::s) ==~ c.
Proof.
induction c;intros; try solve [simpl in H; inversion H].
- simpl in H. eq_event_destruct. inversion H. subst. autoM. inversion H.
- simpl in H. inversion H; autoM. 
- simpl in H. inversion H. inversion H2. subst. rewrite app_comm_cons. autoM.
  subst. o_destruct.  
  * rewrite H0 in H1. rewrite <- (app_nil_l (e::s)). constructor. now rewrite Matches_Comp_nil in H2.
    rewrite seq_Success in H1. auto. 
  * rewrite H0 in H1. inversion H1. inversion H6.
- inversion H. rewrite app_comm_cons. autoM.
Qed.




Lemma Matches_Comp_iff_matchesb : forall (c : Contract)(s : Trace), s ==~ c <-> matchesb c s = true.
Proof.
split;intros.
- unfold matchesb. auto using Matches_Comp_i_matchesb.
- generalize dependent c. induction s;intros. unfold matchesb in H.
  simpl in H. now rewrite <- Matches_Comp_nil.
  auto using Matches_Comp_derive.
Qed.


Lemma derive_spec_comp : forall (c : Contract)(e : EventType)(s : Trace), e::s ==~ c <-> s ==~ c / e.
Proof.
intros. repeat rewrite Matches_Comp_iff_matchesb.  reflexivity.
Qed.

