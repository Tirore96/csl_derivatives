Require Import Lists.List.
Require Import FunInd.
Require Import Bool.Bool.
Require Import Bool.Sumbool.
Import ListNotations.

Set Implicit Arguments.


Inductive EventType : Type :=
| Transfer : EventType
| Notify : EventType.


Definition eqb_event (e1 e2:EventType):bool :=
match e1, e2 with
| Transfer, Transfer => true
| Notify, Notify => true
| _, _ => false
end.

Definition eq_event_dec (e1 e2 : EventType) : {e1 = e2}+{~(e1=e2)}.
Proof. destruct (eqb_event e1 e2) eqn:Heqn.
- left. destruct e1 ; destruct e2; try reflexivity ; try discriminate Heqn.
- right. destruct e1 ; destruct e2 ;  intro H ; try  discriminate Heqn ; try discriminate H.
Qed.

Definition Trace := List.list EventType % type.

Inductive Contract : Set :=
| Success : Contract
| Failure : Contract
| Event : EventType -> Contract
| CPlus : Contract -> Contract -> Contract
| CSeq : Contract -> Contract -> Contract.

Notation "e _._ c" := (CSeq (Event e) c)
                    (at level 41, right associativity).

Notation "c0 _;_ c1"  := (CSeq c0 c1)
                         (at level 50, left associativity).

Notation "c0 _+_ c1"  := (CPlus c0 c1)
                         (at level 61, left associativity).


Fixpoint eqb_contract (c0 c1 : Contract) : bool :=
match c0,c1 with
| Success, Success => true
| Failure, Failure => true
| (Event e), (Event e') => eqb_event e e'
| (CPlus c0 c1), (CPlus c2 c3) => (eqb_contract c0 c2) && (eqb_contract c1 c3)
| (CSeq c0 c1), (CSeq c2 c3) => (eqb_contract c0 c2) && (eqb_contract c1 c3)
| _, _ => false
end.


Lemma eqb_contract_true : forall (c0 c1 : Contract), eqb_contract c0 c1 = true -> c0 = c1.
Proof.
induction c0. 
- destruct c1 ; intros ; try reflexivity ; try (simpl in H ; try discriminate).
- intros ;  destruct c1; try reflexivity; (try simpl in H ; discriminate).
- intros. destruct c1; try reflexivity; (try simpl in H ; try discriminate).
  apply f_equal. destruct e; destruct e0 ; try reflexivity ; try (simpl in H ; discriminate).
- induction c1 ; intros ; try discriminate.
  * simpl in H. apply andb_prop in H as [H1 H2].
    apply IHc0_1 in H1. rewrite H1. apply IHc0_2 in H2.  rewrite H2.  reflexivity. 
- induction c1 ; intros ; try discriminate. simpl in H.
  * simpl in H. apply andb_prop in H as [H1 H2].
    apply IHc0_1 in H1. rewrite H1. apply IHc0_2 in H2.  rewrite H2.  reflexivity. 
Defined.

Lemma eqb_contract_false : forall (c0 c1 : Contract), eqb_contract c0 c1 = false -> c0 <> c1.
Proof.
induction c0.
- destruct c1 ; intros ; try discriminate.
- destruct c1 ; intros ; try discriminate.
- destruct c1 ; intros ; try discriminate.
  * destruct e; destruct e0 ; try reflexivity ; try (simpl in H ; discriminate).
- induction c1 ; intros ; try discriminate.
  * simpl in H. apply andb_false_elim in H as [H1 | H1].
    ** apply IHc0_1 in H1. intro H. inversion H. contradiction.
    ** apply IHc0_2 in H1. intro H. inversion H. contradiction. 
- induction c1 ; intros ; try discriminate.
  * simpl in H. apply andb_false_elim in H as [H1 | H1].
    ** apply IHc0_1 in H1. intro H. inversion H. contradiction.
    ** apply IHc0_2 in H1. intro H. inversion H. contradiction.  
Defined.



Definition eq_contract_dec : forall (c0 c1: Contract), {c0=c1} + {c0<>c1}.
Proof.
intros. destruct (eqb_contract c0 c1) eqn:Heqn.
- left. apply eqb_contract_true. assumption.
- right. apply eqb_contract_false. assumption.
Defined.
 

(*For a nullary contract c, nu c = true*)
Fixpoint nu(c:Contract):bool :=
match c with
| Success => true
| Failure => false
| Event e => false
| c0 _;_ c1 => nu c0 && nu c1
| c0 _+_ c1 => nu c0 || nu c1
end.


(*Derivative of contract with respect to an event*)
Fixpoint derive(e:EventType)(c:Contract):Contract :=
match c with
| Success => Failure
| Failure => Failure
| Event e1 => if eq_event_dec e1 e then Success else Failure
| c0 _;_ c1 => match nu c0 with
               | true => ((derive e c0) _;_ c1) _+_ (derive e c1)
               | false => (derive e c0) _;_ c1
               end
| c0 _+_ c1 => (derive e c0) _+_(derive e c1) 
end.

Notation "c / e" := (derive e c).

Fixpoint matches (c:Contract)(s:Trace):bool :=
match s with
| [] => nu c
| e::s' => matches (c / e) s'
end.

(*Expression*)
Notation "s =~ c" := (matches c s) (at level 63).

(** Relation between [matches] and [derive]. *)
Theorem derive_spec : forall (e:EventType)(s:Trace)(c:Contract),
  (e::s) =~ c  = s =~ c / e.
Proof. intros e s c. simpl. reflexivity.
Qed.

Reserved Notation "s ==~ re" (at level 63).

Inductive matches_comp : Trace -> Contract -> Prop :=
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
  where "s ==~ c" := (matches_comp s c).

Hint Constructors matches_comp : core.

Lemma failure_false2 : forall (s : Trace), ~(s ==~ Failure).
Proof.
intros. intro H. inversion H.
Qed.

(*No trace can be derived from Failure*)
Lemma failure_false : forall (s : Trace), (s =~ Failure) = false.
Proof. induction s.
- simpl. reflexivity.
- simpl. apply IHs.
Defined.


(*If s matches c, it also matches c _+_ any contract*)
Lemma plus_left_oper : forall (s : Trace)(l r : Contract), s =~ l = true -> s =~ (l _+_ r) = true.
Proof. induction s as [| n s' IHs'].
- intros l r H. simpl in H. simpl. rewrite H. rewrite orb_true_l. reflexivity.
- simpl. intros l r H. auto. 
Qed. 

(*_+_ is commutative*)
Lemma plus_comm_oper : forall (s : Trace)(l r : Contract), s =~ (l _+_ r) = true -> s =~ (r _+_ l) = true.
Proof. induction s as [| e s' IHs'].
- simpl. intros l r H. rewrite orb_comm. apply H.
- intros l r H. simpl. auto.
Qed.
 
(*If s matches c, it also matches any contract _+_ c*)
Lemma plus_right_oper : forall (s : Trace)(l r : Contract), s =~ r = true -> s =~ (l _+_ r) = true.
Proof. intros. apply plus_comm_oper. apply plus_left_oper. apply H.
Qed.

(*If s matches c2, it will still match after prefixing c2 with a nullary contract*)
Lemma seq_nu_left : forall (s : Trace)(c1 c2 : Contract), nu c1 = true -> (s =~c2 = true) 
                    -> (s =~ c1 _;_ c2 = true).
Proof. induction s as [| e s' IHs'].
- intros. simpl in *. apply andb_true_intro. auto.
- intros. simpl in *. rewrite H. apply plus_right_oper. assumption.
Qed.

(*MSeq defined operationally*)
Lemma mseq_oper : forall (s1 s2 : Trace)(c1 c2 : Contract), s1 =~ c1 = true -> 
                      s2 =~ c2 = true -> ((s1 ++ s2) =~ c1 _;_ c2) = true.
Proof. 
induction s1.
- simpl. intros. rewrite <- (app_nil_l s2).
  apply seq_nu_left ; try assumption.
- intros. simpl. destruct (nu c1).
  * simpl in H. rewrite <- (app_nil_l (_ ++ s2)). apply plus_left_oper.
    simpl. apply IHs1 ; try assumption.
  * apply IHs1 ; try assumption.
Qed. 

Lemma comp_oper : forall (s : Trace)(c : Contract), s ==~ c -> (s =~ c) = true.
Proof with simpl. 
intros. induction H.
- reflexivity.
- simpl. destruct (eq_event_dec x x). reflexivity. exfalso. now apply n.
- auto using mseq_oper.
- auto using plus_left_oper. 
- auto using plus_right_oper. 
Qed.

(*If s matches c1 _+_ c2, then it matches c1 or c2*)
Lemma plus_or_oper : forall (s : Trace)(c1 c2 : Contract), (s =~ (c1 _+_ c2)) = true -> 
               (s =~ c1) = true \/ (s =~ c2) = true.
Proof. induction s ; simpl ; intros ; auto using orb_prop.
Qed.

(*Only the empty trace can be derived from Success*)
Lemma success_empty : forall (s : Trace), (s =~ Success) = true -> s = [].
Proof. induction s.
- intro. reflexivity.
- simpl. rewrite failure_false. intro H. discriminate.
Qed.


Definition exists_seq_decomp (s : Trace) (c1 c2 : Contract) : Prop := 
 s =~ c1 _;_ c2 = true ->
     exists s1 s2 : Trace, s = s1 ++ s2 /\ s1 =~ c1 = true /\ s2 =~ c2 = true.
Hint Unfold exists_seq_decomp : core.

(*To show e::s matching c1 _;_ c2 can be decomposed, it suffices to show 
  s matching c1/e ;_ c2 can be decomposed*)
Lemma mseq_oper_inv_helper : forall (s : Trace)(c1 c2 : Contract)(e : EventType), 
  (exists_seq_decomp s (c1 / e) c2) -> exists_seq_decomp (e :: s) c1 c2.
Proof.
unfold exists_seq_decomp. intros. simpl in *. destruct (nu c1) eqn:Heqn.
- apply plus_or_oper in H0. destruct H0 as [H2 | H2].
  * apply H in H2. destruct H2 as [s' [s'' [P1 [P2 P3]]]].
    exists (e::s'). exists s''. simpl. rewrite P1. split ; try reflexivity ; auto.
  * exists []. exists (e::s). simpl ; try reflexivity ; auto. 
- apply H in H0. destruct H0 as [s' [s'' [P1 [P2 P3]]]]. exists (e::s'). exists s''. 
  split.
  * simpl. rewrite <- P1. reflexivity.
  * split ; auto.
Qed.




(*The inverse rule of MSeq given operationally*)
Lemma mseq_oper_inv : forall (s : Trace)(c1 c2 : Contract), 
       (s =~ c1 _;_ c2) = true -> (exists (s1 s2 : Trace), s = s1++s2 /\ (s1 =~ c1) = true /\ (s2 =~ c2) = true ).
Proof. induction s.
- intros. exists []. exists []. simpl in *. apply andb_prop in H as [H1 H2].
  rewrite H1. rewrite H2. repeat split ; try reflexivity.
- intros. apply mseq_oper_inv_helper ; auto. 
Qed.

Lemma oper_imp_comp : forall (s : Trace)(c : Contract), (s =~ c) = true -> s ==~ c.
Proof.
intros. generalize dependent s. induction c.
- intros. destruct s ; try constructor.
  * inversion H. rewrite failure_false in H1. discriminate H1.
- intros. rewrite failure_false in H. discriminate H. 
- intros. destruct s eqn:Heqn.
  * inversion H.
  * simpl in H. destruct (eq_event_dec e e0).
    ** destruct t. apply success_empty in H. subst. apply MEvent. simpl in H. 
       rewrite failure_false in H. discriminate H.
    ** rewrite failure_false in H. discriminate H.
- intros. apply plus_or_oper in H. destruct H.
  * apply MPlusL. apply IHc1. apply H.
  * apply MPlusR. apply IHc2. apply H.
- intros s H. apply mseq_oper_inv in H as [s' [s'' [P1 [P2 P3]]]].
  rewrite P1. apply MSeq.
  * apply (IHc1 s' P2).
  * apply (IHc2 s'' P3). 
Qed.

Lemma comp_iff_oper : forall (s : Trace)(c : Contract), s ==~ c <-> (s =~ c) = true.
Proof.
split.
- (*->*) apply comp_oper.
- (*<-*) apply oper_imp_comp.
Qed.

(*the proposition s ==~ c is reflected in the value s =~ c *)
Lemma matches_reflect : forall (s : Trace) (c : Contract), reflect (s ==~ c) (s =~ c).
Proof.
  intros n m. destruct (n =~ m) eqn:Heqn.
  - apply ReflectT. apply oper_imp_comp. assumption. 
  - apply ReflectF. intro H. apply comp_oper in H. rewrite Heqn in H. inversion H.
Qed.


