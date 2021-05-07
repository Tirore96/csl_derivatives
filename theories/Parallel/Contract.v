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

Set Implicit Arguments.

Require CSL.Core.Contract.

Module CSLC := CSL.Core.Contract.
Definition Trace := CSLC.Trace.
Definition EventType := CSLC.EventType.
Definition EventType_eq_dec := CSLC.EventType_eq_dec.
Definition Transfer := CSLC.Transfer.
Definition Notify := CSLC.Notify.

Inductive Contract : Set :=
| Success : Contract
| Failure : Contract
| Event : EventType -> Contract
| CPlus : Contract -> Contract -> Contract
| CSeq : Contract -> Contract -> Contract
| Par : Contract -> Contract -> Contract.



Notation "c0 _;_ c1"  := (CSeq c0 c1)
                         (at level 50, left associativity).

Notation "c0 _*_ c1"  := (Par c0 c1)
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
| c0 _*_ c1 => nu c0 && nu c1
end.
(*
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
Qed.*)


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
| c0 _*_ c1 => (derive e c0) _*_ c1 _+_ c0 _*_ (derive e c1)
end
where "e \ c" := (derive e c).

Ltac destruct_ctx :=
  repeat match goal with
         | [ H: ?H0 /\ ?H1 |- _ ] => destruct H
         | [ H: exists _, _  |- _ ] => destruct H
         end.



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


Inductive interleave (A : Set) : list A -> list A -> list A -> Prop :=
| IntLeftNil t : interleave nil t t
| IntRightNil t : interleave t nil t
| IntLeftCons t1 t2 t3 e (H: interleave t1 t2 t3) : interleave (e :: t1) t2 (e :: t3)
| IntRightCons t1 t2 t3 e (H: interleave t1 t2 t3) : interleave t1 (e :: t2) (e :: t3).
Hint Constructors interleave : cDB.





Fixpoint interleave_fun (A : Set) (l0 l1 l2 : list A ) : Prop :=
match l2 with
| [] => l0 = [] /\ l1 = []
| a2::l2' => match l0 with
            | [] => l1 = l2
            | a0::l0' => a2=a0 /\ interleave_fun l0' l1 l2' \/ match l1 with
                                                           | [] => l0 = l2
                                                           | a1::l1' => a2=a1 /\ interleave_fun l0 l1' l2'
                                                           end
            end
end.

Lemma interl_fun_nil : forall (A:Set), @interleave_fun A [] [] [].
Proof. intros. unfold interleave_fun. split;auto. Qed.

Hint Resolve interl_fun_nil : cDB.

Lemma interl_fun_l : forall (A:Set) (l : list A), interleave_fun l [] l.
Proof.
induction l;intros; auto with cDB. simpl. now right.
Qed.

Lemma interl_fun_r : forall (A:Set) (l : list A), interleave_fun [] l  l.
Proof.
induction l;intros; auto with cDB. now simpl. 
Qed.

Hint Resolve interl_fun_l interl_fun_r : cDB.



Lemma interl_eq_l : forall (A: Set) (l0 l1 : list A), interleave [] l0 l1 -> l0 = l1.
Proof.
induction l0;intros;simpl.
- inversion H;auto.
- inversion H; subst; auto. f_equal. auto. 
Qed.

Lemma interl_comm : forall (A: Set) (l0 l1 l2 : list A), interleave l0 l1 l2 -> interleave l1 l0 l2.
Proof.
intros. induction H;auto with cDB.
Qed.

Lemma interl_eq_r : forall (A: Set) (l0 l1 : list A), interleave  l0 [] l1 -> l0 = l1.
Proof. auto using interl_eq_l,interl_comm.
Qed.

Lemma interl_nil : forall (A: Set) (l0 l1 : list A), interleave  l0 l1 [] -> l0 = [] /\ l1 = [].
Proof.
intros. inversion H;subst; split;auto.
Qed.

Lemma interl_or : forall (A:Set)(l2 l0 l1 :list A)(a0 a1 a2:A), interleave (a0::l0) (a1::l1) (a2 :: l2) -> a0 = a2 \/ a1 = a2.
Proof.
intros. inversion H;subst; auto||auto.
Qed.

Lemma interl_i_fun : forall (A:Set)(l0 l1 l2 : list A), interleave l0 l1 l2 -> interleave_fun l0 l1 l2.
Proof.
intros. induction H;auto with cDB.
- simpl. left. split;auto.
- simpl. destruct t1. apply interl_eq_l in H. now subst. right. split;auto.
Qed.

Lemma fun_i_interl : forall (A:Set)(l2 l0 l1 : list A), interleave_fun l0 l1 l2 -> interleave l0 l1 l2.
Proof.
induction l2;intros.
- simpl in*. destruct H. subst. constructor.
- simpl in H. destruct l0. subst. auto with cDB.
  destruct H.
  * destruct H. subst. auto with cDB.
  * destruct l1.
    ** inversion H. auto with cDB.
    ** destruct H. subst. auto with cDB.
Qed.

Theorem interl_iff_fun : forall (A:Set)(l2 l0 l1 : list A), interleave l0 l1 l2 <-> interleave_fun l0 l1 l2.
Proof. split;auto using interl_i_fun,fun_i_interl.
Qed.

Lemma interl_eq_r_fun : forall (A: Set) (l0 l1 : list A), interleave_fun  l0 [] l1 -> l0 = l1.
Proof. intros. rewrite <- interl_iff_fun in H. auto using interl_eq_r.
Qed.

Lemma interl_eq_l_fun : forall (A: Set) (l0 l1 : list A), interleave_fun  [] l0 l1 -> l0 = l1.
Proof. intros. rewrite <- interl_iff_fun in H. auto using interl_eq_l.
Qed.

Lemma interl_fun_cons_l : forall (A: Set) (a:A) (l0 l1 l2 : list A), interleave_fun l0 l1 l2 ->
interleave_fun (a::l0) l1 (a::l2).
Proof. intros. rewrite <- interl_iff_fun in *. auto with cDB. 
Qed.

Lemma interl_fun_cons_r : forall (A: Set) (a:A) (l0 l1 l2 : list A), interleave_fun l0 l1 l2 ->
interleave_fun l0 (a::l1) (a::l2).
Proof. intros. rewrite <- interl_iff_fun in *. auto with cDB. 
Qed.

Hint Rewrite interl_eq_r interl_eq_l interl_eq_r_fun interl_eq_l_fun : cDB.

Hint Resolve interl_fun_cons_l interl_fun_cons_r : cDB.

Ltac interl_tac := 
        (repeat match goal with
         | [ H: _::_ = [] |- _ ] => discriminate
         | [ H: _ /\ _ |- _ ] => destruct H
         | [ H: _ \/ _ |- _ ] => destruct H
         | [ H: interleave_fun _ _ [] |- _ ] => simpl in H
         | [ H: interleave_fun _ _ (?e::?s) |- _ ] => simpl in H
         | [ H: interleave_fun _ _ ?s |- _ ] => destruct s;simpl in H
         | [ H: interleave _ _ _ |- _ ] => rewrite interl_iff_fun in H
         end);subst.

Lemma interl_fun_app : forall (l l0 l1 l_interl l2  : Trace),
interleave_fun l0 l1 l_interl -> interleave_fun l_interl l2 l -> 
exists l_interl', interleave_fun l1 l2 l_interl' /\ interleave_fun l0 l_interl' l.
Proof.
induction l;intros.
- simpl in H0. destruct H0. subst. simpl in H. destruct H.
  subst.  exists []. split;auto with cDB.
- simpl in H0. destruct l_interl. simpl in H. destruct H. subst.
  exists (a::l). split;auto with cDB.
  destruct H0.
  * destruct H0. subst. simpl in H. destruct l0.
    ** subst. exists (e::l). split;auto with cDB.
    ** destruct H. destruct H. subst.
      *** eapply IHl in H1;eauto. destruct_ctx.
          exists x. split;auto with cDB.
      *** destruct l1.
        **** inversion H. subst. exists l2.
             split;auto with cDB.
        **** destruct H. subst. eapply IHl in H1;eauto. destruct_ctx.
             exists (e1::x). split;auto with cDB;
             apply interl_iff_fun; constructor;
         now rewrite interl_iff_fun.
  * destruct l2.
    ** inversion H0. subst. exists l1. split; auto with cDB.
    ** destruct H0. subst. eapply IHl in H1;eauto. destruct H1.
       exists (e0::x). split; apply interl_iff_fun; constructor;
       destruct H0; now rewrite interl_iff_fun.
Qed.

Lemma interl_app : forall (l l0 l1 l_interl l2  : Trace),
interleave l0 l1 l_interl -> interleave l_interl l2 l -> 
exists l_interl', interleave l1 l2 l_interl' /\ interleave l0 l_interl' l.
Proof.
intros. rewrite interl_iff_fun in *.
eapply interl_fun_app in H0;eauto. destruct_ctx. exists x.
repeat rewrite interl_iff_fun. split;auto.
Qed.



Lemma event_interl : forall s (e0 e1 : EventType), interleave_fun [e0] [e1] s -> s = [e0]++[e1] \/ s = [e1]++[e0].
Proof.
induction s;intros. simpl in H. destruct H. discriminate.
simpl in H. destruct H.
- destruct H. subst. apply interl_eq_l_fun in H0. subst.
  now left.
- destruct H. subst. apply interl_eq_r_fun in H0. subst.
  now right.
Qed.

Lemma interleave_app : forall (A:Set) (s0 s1: list A), interleave s0 s1 (s0++s1).
Proof.
induction s0;intros;simpl;auto with cDB.
Qed.

Hint Resolve interleave_app : cDB.

Lemma interleave_app2 : forall (A:Set) (s1 s0: list A), interleave s0 s1 (s1++s0).
Proof.
induction s1;intros;simpl;auto with cDB.
Qed.

Hint Resolve interleave_app interleave_app2 : cDB.

Lemma interl_extend_r : forall (l0 l1 l2 l3 : Trace),
interleave l0 l1 l2 -> interleave l0 (l1++l3) (l2++l3). 
Proof.
intros. generalize dependent l3. induction H;intros;simpl;auto with cDB.
Qed.

Lemma interl_extend_l : forall (l0 l1 l2 l3 : Trace),
interleave l0 l1 l2 -> interleave (l0++l3) l1 (l2++l3). 
Proof.
intros. generalize dependent l3. induction H;intros;simpl;auto with cDB.
Qed.


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
  | MPar s1 c1 s2 c2 s
             (H1 : s1 =~ c1)
             (H2 : s2 =~ c2)
             (H3 : interleave s1 s2 s)
           : s =~ (c1 _*_ c2)
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

Hint Rewrite derive_distr_plus : cDB.

Lemma nu_seq_derive : forall (e : EventType)(c0 c1 : Contract), 
nu c0 = true -> nu (e \ c1) = true -> nu (e \ (c0 _;_ c1)) = true.
Proof.
intros. simpl. destruct (nu c0). simpl. auto with bool. discriminate.
Qed.

(*Not needed*)
(*
Lemma nu_plus : forall c0 c1, nu (c0 _+_ c1) = true <-> nu c0 = true \/ nu c1 = true.
Proof.
intros. simpl. now rewrite orb_true_iff.
Qed.*)

Lemma nu_Failure : forall (s : Trace)(c : Contract), nu (s \\ (Failure _;_ c)) = false.
Proof.
induction s;intros. now simpl. simpl. auto.
Qed.

Hint Rewrite nu_Failure : cDB.

Lemma nu_Success : forall (s : Trace)(c : Contract), nu (s \\ (Success _;_ c)) = nu (s \\ c).
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

Lemma matchesb_seq : forall (s0 s1 : Trace)(c0 c1 : Contract), nu (s0\\c0) = true -> nu (s1\\c1) = true -> nu ((s0++s1)\\(c0 _;_c1)) = true.
Proof.
induction s0;intros;simpl in *.
- rewrite nu_seq_trace_derive; auto. 
- destruct (nu c0); autorewrite with cDB; simpl; auto with bool.
Qed.


Hint Rewrite matchesb_seq : cDB.

Lemma nu_par_trace_derive_r : forall (s : Trace)(c0 c1 : Contract), 
nu c0 = true -> nu (s \\ c1) = true -> nu (s \\ (c0 _*_ c1)) = true.
Proof.
induction s;intros;simpl in *. intuition.
rewrite derive_distr_plus. simpl. rewrite (IHs c0);auto with bool.
Qed.



Lemma nu_par_trace_derive_l : forall (s : Trace)(c0 c1 : Contract), 
nu c0 = true -> nu (s \\ c1) = true -> nu (s \\ (c1 _*_ c0)) = true.
Proof.
induction s;intros;simpl in *. intuition.
rewrite derive_distr_plus. simpl. rewrite (IHs c0);auto with bool.
Qed.

Hint Resolve nu_par_trace_derive_l nu_par_trace_derive_r : cDB.

Lemma matchesb_par : forall (s0 s1 s : Trace)(c0 c1 : Contract), interleave s0 s1 s ->
nu (s0\\c0) = true -> nu (s1\\c1) = true -> nu (s\\(c0 _*_c1)) = true.
Proof.
intros. generalize dependent c1. generalize dependent c0.
induction H;intros;simpl in*; auto with cDB. 
- rewrite derive_distr_plus. simpl. rewrite IHinterleave;auto.
- rewrite derive_distr_plus. simpl. rewrite (IHinterleave c0);auto with bool.
Qed.


Hint Resolve matchesb_par : cDB.


Lemma Matches_Comp_i_matchesb : forall (c : Contract)(s : Trace), s =~ c -> nu (s\\c) = true.
Proof.
intros; induction H; 
solve [ autorewrite with cDB; simpl; auto with bool 
      | simpl;eq_event_destruct;eauto with cDB]. (*Only change: eauto, add matchesb_par*)
Qed.



Lemma Matches_Comp_nil_nu : forall (c : Contract), nu c = true -> [] =~ c.
Proof.
intros;induction c; simpl in H ; try discriminate; autoIC.
- apply orb_prop in H. destruct H; autoIC.
- rewrite <- (app_nil_l []); autoIC.
- apply andb_prop in H. destruct H. eauto with cDB.
Qed.


(*This direction with longer trace on the right because of induction step on trace*)
Lemma Matches_Comp_derive : forall (c : Contract)(e : EventType)(s : Trace), s =~ e \ c-> (e::s) =~ c.
Proof.
induction c;intros; simpl in*; try solve [inversion H].
- eq_event_destruct. inversion H. subst. autoIC. inversion H.
- inversion H; autoIC. (*apply IH directly*) 
- destruct (nu c1) eqn:Heqn.
  * inversion H.
    ** inversion H2. subst. rewrite app_comm_cons. auto with cDB.
    ** subst. rewrite <- (app_nil_l (e::s)).
       auto using Matches_Comp_nil_nu with cDB.
  * inversion H. subst. rewrite app_comm_cons. auto with cDB.
- inversion H.
  * inversion H2; subst; eauto with cDB.
  * inversion H1;subst; eauto with cDB. (*New case*)
Qed.




Theorem Matches_Comp_iff_matchesb : forall (c : Contract)(s : Trace), s =~ c <-> nu (s \\ c) = true.
Proof.
split;intros.
- auto using Matches_Comp_i_matchesb.
- generalize dependent c. induction s;intros. 
  simpl in H. auto using Matches_Comp_nil_nu.
  auto using Matches_Comp_derive.
Qed.

Lemma derive_spec_comp : forall (c : Contract)(e : EventType)(s : Trace), e::s =~ c <-> s =~ e \ c.
Proof.
intros. repeat rewrite Matches_Comp_iff_matchesb. now simpl.
Qed.