(** printing "_;_" %;% *)
(** printing "_+_" %+% *)


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
| CSeq : Contract -> Contract -> Contract.

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

Hint Rewrite o_Failure o_Success o_idempotent : icDB.

Reserved Notation "e \ c" (at level 40, left associativity).
(*Derivative of contract with respect to an event*)
Equations derive (e:EventType) (c:Contract) :Contract := {
e \ Success := Failure;
e \ Failure := Failure;
e \ (Event e') := if (EventType_eq_dec e' e) then Success else Failure;
e \ (c0 _;_ c1) := o c0 _;_ e \ c1 _+_ e \ c0 _;_ c1;
e \ (c0 _+_ c1) := e \ c0 _+_ e \ c1}
where "e \ c" := (derive e c).

Global Transparent derive.

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

Lemma o_derive : forall c e, (o c)/e = Failure.
Proof.
intros. o_destruct. unfold o. rewrite H0. now simpl. unfold o. rewrite H0. now simpl.
Qed.

Hint Rewrite o_idempotent o_derive : icDB.
Ltac autoM := auto with icDB.

Inductive Trace_Derive : Contract -> Trace -> Contract -> Prop :=
| Trace_Derive_Nil c : Trace_Derive c [] c
| Trace_Derive_Cons c s c' e (H: Trace_Derive (c/e) s c') : Trace_Derive c (e::s) c'. (*rule motivated by constructor being analgous to cons on lists*)
Hint Constructors Trace_Derive : icDB.


Lemma Trace_Derive_trans : forall s s' c0 c1 c2 , Trace_Derive c0 s c1 -> Trace_Derive c1 s' c2 -> Trace_Derive c0 (s++s') c2.
Proof.
intros. induction H;simpl;autoM.
Qed.



Equations trace_derive (c : Contract) (s : Trace) : Contract :=
trace_derive c [] := c;
trace_derive c (e::s') := trace_derive (c/e) s'.
Global Transparent trace_derive.

Notation "c // s" := (trace_derive c s)(at level 42, left associativity).

(*
Lemma trace_derive_spec : forall (c c' : Contract)(s : Trace), c // s = c' <-> Trace_Derive c s c'.
Proof.
split;intros.
- funelim (trace_derive c s);simpl;autoM.
- induction H;auto. 
Qed.

Lemma trace_derive_spec2 : forall (c : Contract)(s : Trace), Trace_Derive c s (c // s).
Proof.
intros. remember (c//s). symmetry in Heqc0. now rewrite <- trace_derive_spec.
Qed.*)


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
 (* | MStar0 c 
              : [] ==~ Star c
  | MStarSeq c s1 s2 (H1: s1 ==~ c) 
                     (H2: s2 ==~ Star c) 
              : s1 ++ s2 ==~ Star c*)
  where "s ==~ c" := (Matches_Comp s c).

Derive Signature for Matches_Comp.

Hint Constructors Matches_Comp : icDB.

Ltac eq_event_destruct :=
  repeat match goal with
         | [ |- context[if EventType_eq_dec ?e ?e then _ else _] ] => destruct (EventType_eq_dec e e);try contradiction
         | [ |- context[if EventType_eq_dec ?e ?e0 then _ else _] ] => destruct (EventType_eq_dec e e0)
         | [ _ : context[if EventType_eq_dec ?e ?e then _ else _]  |- _ ] => destruct (EventType_eq_dec e e);try contradiction
         | [ _ : context[if EventType_eq_dec ?e ?e0 then _ else _] |- _ ] => destruct (EventType_eq_dec e e0)
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

Hint Resolve seq_Success seq_Failure : icDB.

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
intros. o_destruct;auto with icDB. rewrite H in H1. discriminate. 
Qed.

Lemma o_false : forall (c: Contract), nu c = false -> o c = Failure.
Proof.
intros. o_destruct. rewrite H in H1. discriminate. auto. 
Qed.

Hint Rewrite derive_plus : icDB.

Lemma nu_seq_derive : forall (e : EventType)(c0 c1 : Contract), 
nu c0 = true -> nu (c1 / e) = true -> nu ((c0 _;_ c1) / e) = true.
Proof.
intros. simpl. rewrite orb_true_iff. left. rewrite o_true;auto.
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

Hint Rewrite nu_Failure : icDB.

Lemma nu_Success : forall (s : Trace)(c : Contract), nu ((Success _;_ c)//s) = nu (c//s).
Proof.
induction s;intros;simpl;auto. 
autorewrite with icDB using simpl;auto. rewrite orb_false_r. auto. 
Qed.

Hint Rewrite nu_Failure nu_Success : icDB.

Lemma nu_seq_trace_derive : forall (s1 : Trace)(c0 c1 : Contract), 
nu c0 = true -> nu (c1 // s1) = true -> nu ((c0 _;_ c1) // s1) = true.
Proof.
induction s1;intros;simpl in *. intuition.
rewrite o_true;auto. rewrite derive_plus. simpl. autorewrite with icDB.
rewrite H0. btauto.
Qed.

Lemma matchesb_seq : forall (s0 s1 : Trace)(c0 c1 : Contract), nu (c0//s0) = true -> nu (c1//s1) = true -> nu ((c0 _;_c1) // (s0++s1)) = true.
Proof.
induction s0;intros;simpl in *.
- rewrite nu_seq_trace_derive; auto. 
- autorewrite with icDB. simpl. rewrite orb_true_iff. right. 
  rewrite IHs0;auto.
Qed.

Lemma Matches_Comp_i_matchesb : forall (c : Contract)(s : Trace), s ==~ c -> nu (c//s) = true.
Proof.
intros. induction H;auto.
- simpl. eq_event_destruct. reflexivity.
- rewrite matchesb_seq;auto.
- autorewrite with icDB. simpl. intuition.
- autorewrite with icDB. simpl. intuition.
(* - destruct s1. now simpl. simpl. rewrite matchesb_seq;auto. *)
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
- simpl in H. inversion H.
  * inversion H2. subst. o_destruct. rewrite H0 in *.
    inversion H7. simpl. 
    rewrite <- (app_nil_l (e::s2)). subst. constructor.
     now rewrite <- Matches_Comp_nil. auto. rewrite H0 in *.
     inversion H7.
  * inversion H1. subst. rewrite app_comm_cons. 
    auto with icDB.
(* - inversion H. rewrite app_comm_cons. autoM. *)
Qed.




Lemma Matches_Comp_iff_matchesb : forall (c : Contract)(s : Trace), s ==~ c <-> nu (c // s) = true.
Proof.
split;intros.
- unfold matchesb. auto using Matches_Comp_i_matchesb.
- generalize dependent c. induction s;intros. 
  simpl in H. now rewrite <- Matches_Comp_nil.
  auto using Matches_Comp_derive.
Qed.


Lemma derive_spec_comp : forall (c : Contract)(e : EventType)(s : Trace), e::s ==~ c <-> s ==~ c / e.
Proof.
intros. repeat rewrite Matches_Comp_iff_matchesb.  reflexivity.
Qed.

Fixpoint plus_fold (l : list Contract) : Contract :=
match l with
| [] => Failure
| c ::l => c _+_ (plus_fold l)
end.

Lemma plus_assoc : forall (c1 c2 c3 : Contract), (forall s, s==~((c1 _+_ c2) _+_ c3) <-> s ==~ (c1 _+_ (c2 _+_ c3))).
Proof.
split;intros. inversion H;autoM. inversion H2;autoM. inversion H;autoM. inversion H1;autoM.
Qed.

Lemma plus_fold_app : forall (s:Trace)(l1 l2 : list Contract), 
s ==~ plus_fold (l1 ++ l2) <-> s ==~ (plus_fold l1) _+_ (plus_fold l2).
Proof.
intro. induction l1.
- intros. split.
  * intros. simpl in H. autoM.
  * intros. simpl. simpl in H. inversion H. {  inversion H2. } assumption.
- intros. split.
  * intros. simpl in *. inversion H ; autoM. subst.
    rewrite IHl1 in H1. rewrite plus_assoc. apply MPlusR;autoM. 
  * intros. simpl in *. apply plus_assoc in H. inversion H;autoM.
    apply MPlusR. rewrite IHl1. autoM. 
Qed.


Lemma in_plus_fold : forall (s : Trace)(l : list Contract), s ==~ plus_fold l <-> 
(exists c, In c l /\ s ==~ c).
Proof.
intros. split.
- induction l.
  * intros. simpl in H. inversion H.
  * intros. simpl in H. inversion H;autoM. 
    ** exists a. split. apply in_eq. assumption.
    ** apply IHl in H1 as [c' [P1 P2]]. exists c'. split ; auto using  in_cons.
- intros. destruct H as [ c' [P1 P2]]. induction l.
  * destruct P1.
  * simpl in P1. destruct P1.
    ** subst. simpl. autoM.
    ** simpl. autoM.
Qed.

Lemma plus_fold_derive : forall (l : list Contract) (e : EventType), (plus_fold l) / e = plus_fold (map (fun c => c/e) l).
Proof.
induction l;intros;simpl;auto;f_equal;auto.
Qed.

