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

Inductive EventType : Type :=
| Transfer : EventType
| Notify : EventType.

Scheme Equality for EventType.

Definition Trace := List.list EventType % type.

Lemma plus_minus2 : forall (n0 n1 : nat), n0 + n1 = n1 + n0.
Proof.
induction n0;intros;simpl.
- induction n1; [ | simpl; rewrite <- IHn1]; reflexivity. 
- rewrite IHn0. rewrite plus_n_Sm. reflexivity. 
Qed.

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


Reserved Notation "e \ c" (at level 40, left associativity).
Fixpoint derive (e:EventType) (c:Contract) :Contract :=
match c with
| Success => Failure
| Failure => Failure
| Event e' => if (EventType_eq_dec e' e) then Success else Failure
| c0 _;_ c1 => if nu c0 then
                 ((derive e c0) _;_ c1) _+_ (derive e c1)
                 else (derive e c0) _;_ c1
| c0 _+_ c1 => e \ c0 _+_ e \ c1
end
where "e \ c" := (derive e c).

Ltac destruct_ctx :=
  repeat match goal with
         | [ H: ?H0 /\ ?H1 |- _ ] => destruct H
         | [ H: exists _, _  |- _ ] => destruct H
         end.

Ltac autoIC := auto with cDB.


Reserved Notation "s \\ c" (at level 42, no associativity).
Fixpoint trace_derive (s : Trace) (c : Contract)  : Contract :=
match s with
| [] => c
| e::s' => s' \\ (e \ c)
end
where "s \\ c" := (trace_derive s c).

Definition matchesb (c : Contract)(s : Trace) := nu (s\\c).


Reserved Notation "s (:) re" (at level 63).

Inductive Matches_Comp : Trace -> Contract -> Prop :=
  | MSuccess : Matches_Comp [] Success
  | MEvent x : Matches_Comp [x] (Event x)
  | MSeq s1 c1 s2 c2
             (H1 : Matches_Comp s1 c1)
             (H2 : Matches_Comp s2 c2)
           : Matches_Comp (s1 ++ s2) (c1 _;_ c2)
  | MPlusL s1 c1 c2
                (H1 : Matches_Comp s1 c1)
              : Matches_Comp s1 (c1 _+_ c2)
  | MPlusR c1 s2 c2
                (H2 : Matches_Comp s2 c2)
              : Matches_Comp s2 (c1 _+_ c2).

Notation "s (:) c" := (Matches_Comp s c)(at level 63).


Hint Constructors Matches_Comp : cDB.

Ltac eq_event_destruct :=
  repeat match goal with
         | [ |- context[EventType_eq_dec ?e ?e0] ] 
                => destruct (EventType_eq_dec e e0);try contradiction
         | [ _ : context[EventType_eq_dec ?e ?e0]  |- _ ] 
                => destruct (EventType_eq_dec e e0);try contradiction
         end.

Lemma seq_Success : forall c s, s (:) Success _;_ c <-> s (:) c.
Proof.
split;intros. inversion H. inversion H3. subst. now simpl.
rewrite <- (app_nil_l s). autoIC.
Qed. 

Lemma seq_Failure : forall c s, s (:) Failure _;_ c <-> s (:) Failure.
Proof.
split;intros. inversion H. inversion H3. inversion H.
Qed.

Hint Resolve seq_Success seq_Failure : cDB.

Lemma derive_distr_plus : forall (s : Trace)(c0 c1 : Contract), 
s \\ (c0 _+_ c1) = s \\ c0 _+_ s \\ c1.
Proof.
induction s;intros;simpl;auto.
Qed. 

Hint Rewrite derive_distr_plus : cDB.

Lemma nu_seq_derive : forall (e : EventType)(c0 c1 : Contract), 
nu c0 = true -> nu (e \ c1) = true -> nu (e \ (c0 _;_ c1)) = true.
Proof.
intros. simpl. destruct (nu c0). simpl. auto with bool. discriminate.
Qed.


Lemma nu_Failure : forall (s : Trace)(c : Contract), 
nu (s \\ (Failure _;_ c)) = false.
Proof.
induction s;intros. now simpl. simpl. auto.
Qed.

Hint Rewrite nu_Failure : cDB.

Lemma nu_Success : forall (s : Trace)(c : Contract), 
nu (s \\ (Success _;_ c)) = nu (s \\ c).
Proof.
induction s;intros;simpl;auto. 
autorewrite with cDB using simpl;auto.
Qed.

Hint Rewrite nu_Failure nu_Success : cDB.

Lemma nu_seq_trace_derive : forall (s : Trace)(c0 c1 : Contract), 
nu c0 = true -> nu (s \\ c1) = true -> nu (s \\ (c0 _;_ c1)) = true.
Proof.
induction s;intros;simpl in *. intuition. destruct (nu c0).
rewrite derive_distr_plus. simpl. auto with bool. discriminate.
Qed.

Lemma matchesb_seq : forall (s0 s1 : Trace)(c0 c1 : Contract), 
nu (s0\\c0) = true -> nu (s1\\c1) = true -> nu ((s0++s1)\\(c0 _;_c1)) = true.
Proof.
induction s0;intros;simpl in *.
- rewrite nu_seq_trace_derive; auto. 
- destruct (nu c0); autorewrite with cDB; simpl; auto with bool.
Qed.

Hint Rewrite matchesb_seq : cDB.

Lemma Matches_Comp_i_matchesb : forall (c : Contract)(s : Trace), 
s (:) c -> nu (s\\c) = true.
Proof.
intros; induction H; 
solve [ autorewrite with cDB; simpl; auto with bool 
      | simpl;eq_event_destruct;auto ].
Qed.

Lemma Matches_Comp_nil_nu : forall (c : Contract), nu c = true -> [] (:) c.
Proof.
intros;induction c; simpl in H ; try discriminate; autoIC. 
apply orb_prop in H. destruct H; autoIC.
rewrite <- (app_nil_l []); autoIC.
Qed.


Lemma Matches_Comp_derive : forall (c : Contract)(e : EventType)(s : Trace), 
s (:) e \ c-> (e::s) (:) c.
Proof.
induction c;intros; simpl in*; try solve [inversion H].
- eq_event_destruct. inversion H. subst. autoIC. inversion H.
- inversion H; autoIC.
- destruct (nu c1) eqn:Heqn.
  * inversion H.
    ** inversion H2. subst. rewrite app_comm_cons. auto with cDB.
    ** subst. rewrite <- (app_nil_l (e::s)).
       auto using Matches_Comp_nil_nu with cDB.
  * inversion H. subst. rewrite app_comm_cons. auto with cDB.
Qed.


Theorem Matches_Comp_iff_matchesb : forall (c : Contract)(s : Trace), 
s (:) c <-> nu (s \\ c) = true.
Proof.
split;intros.
- auto using Matches_Comp_i_matchesb.
- generalize dependent c. induction s;intros. 
  simpl in H. auto using Matches_Comp_nil_nu.
  auto using Matches_Comp_derive.
Qed.