Require Import Lists.List.
Require Import FunInd.
Require Import Bool.Bool.
Require Import Bool.Sumbool.
Require Import Structures.GenericMinMax.
From Equations Require Import Equations.
Import ListNotations.
Require Import micromega.Lia.

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
Defined.

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






(***********************Some dependencies used by ParallelContract and ContractEquation******************)

Lemma plus_comm : forall (c1 c2 : Contract),(forall s, s ==~ (c1 _+_ c2) <-> s ==~ (c2 _+_ c1)).
Proof.
split.
- intros. inversion H ; auto. 
- intros. inversion H ; auto.
Qed.

Lemma plus_assoc : forall (c1 c2 c3 : Contract), (forall s, s==~((c1 _+_ c2) _+_ c3) <-> s ==~ (c1 _+_ (c2 _+_ c3))).
Proof.
split.
- intro H. inversion H.
  * inversion H2.
    ** apply MPlusL. apply H6.
    ** apply MPlusR. apply MPlusL. apply H6.
  * apply MPlusR. apply MPlusR. apply H1.
- intro H. inversion H.
  * inversion H2.
    ** apply MPlusL. apply MPlusL. apply MSuccess.
    ** apply MPlusL. apply MPlusL. apply MEvent.
    ** apply MPlusL. apply MPlusL. apply MSeq.
      *** apply H4.
      *** apply H5.
    ** apply MPlusL. apply MPlusL. apply MPlusL. apply H4.
    ** apply MPlusL. apply MPlusL. apply MPlusR. apply H4.
  * inversion H1.
    ** apply MPlusL. apply MPlusR. apply H6.
    ** apply MPlusR. apply H6.
Qed.

Lemma seq_assoc : forall (c1 c2 c3 : Contract),forall s, s==~((c1 _;_ c2) _;_ c3) <-> s==~ (c1 _;_ (c2 _;_ c3)).
Proof.
split.
- intro H. inversion H. inversion H3. rewrite <- app_assoc. apply MSeq.
  * apply H8.
  * apply MSeq.
    ** apply H9.
    ** apply H4.
- intro H. inversion H. inversion H4. rewrite -> app_assoc. apply MSeq.
  * apply MSeq.
    ** apply H3.
    ** apply H8.
  * apply H9.
Qed.

Lemma plus_or : forall (s : Trace)(c1 c2 : Contract), s ==~ (c1 _+_ c2) <-> s ==~ c1 \/ s ==~c2.
Proof. 
split.
- intros. repeat rewrite comp_iff_oper in *.
apply plus_or_oper in H. apply H.
- intros. destruct H. { now apply MPlusL. } { now apply MPlusR. }
Qed.


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


(**************Contract unfolding**************)

Definition alphabet := [Notify;Transfer].

(*Inductive EventPre : EventType -> Contract -> Prop :=
 | ep e c : EventPre e (Event e _;_ c). 

Hint Constructors EventPre : core.

Inductive PlusNorm : list EventType -> list Contract -> Prop :=
  | pn_nil : PlusNorm [] []
  | pn_cons e c el cl (H0 : EventPre e c) (H1 : PlusNorm el cl) : PlusNorm (e::el) (c::cl).

Hint Constructors PlusNorm : core.*)


Inductive Stuck : Contract -> Prop :=
 | STFailure : Stuck Failure
 | STPLus c0 c1 (H0 : Stuck c0) (H1 : Stuck c1) : Stuck (c0 _+_ c1)
 | STSeq c0 c1 (H0 : Stuck c0) : Stuck (c0 _;_ c1).

Hint Constructors Stuck : core.

Inductive NotStuck : Contract -> Prop :=
 | NSTSuccess : NotStuck Success
 | NSEvent e : NotStuck (Event e)
 | NSTPlusL c0 c1 (H0 : NotStuck c0) : NotStuck (c0 _+_ c1)
 | NSTPlusR c0 c1 (H1 : NotStuck c1) : NotStuck (c0 _+_ c1)
 | NSTSeq c0 c1 (H0 : NotStuck c0) : NotStuck (c0 _;_ c1).

Hint Constructors NotStuck : core.

Fixpoint stuck (c : Contract) :=
match c with
| Failure => true
| c0 _+_ c1 => stuck c0 && stuck c1
| c0 _;_ _ => stuck c0
| _ => false
end.

Search (_ || _ = false).
Lemma stuck_false : forall (c : Contract), stuck c = false -> NotStuck c.
Proof.
induction c; intros.
- constructor.
- simpl in H. discriminate.
- constructor.
- simpl in H. apply andb_false_elim in H as [H | H]; auto.
- simpl in H. auto.
Defined.

Lemma stuck_true : forall (c : Contract), stuck c = true -> (Stuck c).
Proof.
induction c; intros; try (simpl in H ; discriminate).
- constructor.
- simpl in H. apply andb_prop in H as [H1 H2].  auto.
- simpl in H. auto.
Defined.


Definition stuck_dec (c : Contract) : {Stuck c}+{NotStuck c}.
Proof. destruct (stuck c) eqn:Heqn.
- left. auto using stuck_true.
- right. auto using stuck_false.
Defined.

Lemma NotStuck_negation : forall (c : Contract), NotStuck c -> ~(Stuck c).
Proof.
intros. induction H ; intro H2; inversion H2.
all : inversion H2; contradiction.
Qed.

Check max.
Fixpoint con_size (c:Contract):nat :=
match c with
| Failure => 0
| Success => 1
| Event _ => 2
| c0 _+_ c1 => max (con_size c0) (con_size c1) 
| c0 _;_ c1 => if stuck_dec c0 then 0 else (con_size c0) + (con_size c1)
end.

(*
Lemma stuck_plus_and : forall (c0 c1 :Contract), Stuck (c0 _+_ c1) -> Stuck c0 /\ Stuck c1.
Proof. Admitted.

Lemma stuck_plus_or : forall (c0 c1 : Contract), ~ Stuck (c0 _+_ c1) -> ~(Stuck c0) \/ ~(Stuck c1).
Proof.
intros. destruct c0 ; destruct c1 ; try (left; intro H2; inversion H2 ; assert_succeeds); try (right; intro H2; inversion H2).
intros.*)

Lemma stuck_0 : forall (c : Contract), Stuck c -> con_size c = 0.
Proof.
intros. induction H.
- reflexivity.
- simpl. rewrite IHStuck1. rewrite IHStuck2. reflexivity.
- simpl. destruct (stuck_dec c0). reflexivity. apply NotStuck_negation in n. contradiction.
Defined.

Lemma NotStuck_0lt : forall (c : Contract), NotStuck c -> 0 < con_size c.
Proof.
intros. induction H; simpl ; try lia.
destruct (stuck_dec c0).
- apply NotStuck_negation in H. contradiction.
- lia.
Defined.


Lemma stuck_not_nullary : forall (c : Contract), Stuck c -> nu c = false.
Proof.
intros. induction H.
- reflexivity.
- simpl. rewrite IHStuck1. rewrite IHStuck2. reflexivity.
- simpl. rewrite IHStuck. reflexivity.
Defined.

Lemma stuck_derive : forall (c : Contract)(e : EventType), Stuck c -> c / e = c.
Proof.
intros. induction H.
- reflexivity.
- simpl. rewrite IHStuck1. rewrite IHStuck2. reflexivity.
- simpl. apply stuck_not_nullary in H. rewrite H. rewrite IHStuck. reflexivity.
Defined.

Locate Max.max.





Search (?a + ?b <  _ + ?b).
Lemma not_stuck_derives : forall (c : Contract), NotStuck c -> (forall (e : EventType), con_size (c / e) < con_size c).
Proof.
intros. induction c.
- simpl. lia.
- inversion H.
- simpl. destruct (eq_event_dec e0 e) ; simpl ; lia.
- simpl. inversion H.
  * destruct (stuck_dec c2).
    ** apply stuck_0 in s as s2. rewrite (stuck_derive _ s). rewrite s2. repeat rewrite (Max.max_comm _ 0). simpl.
       auto.
    ** apply IHc1 in H1.  apply IHc2 in n. lia.
  * destruct (stuck_dec c1).
    ** apply stuck_0 in s as s2. rewrite (stuck_derive _ s). rewrite s2. simpl.
       auto.
    ** apply IHc1 in n.  apply IHc2 in H0. lia.
- inversion H. subst. simpl. destruct (nu c1) eqn:Heqn.
  * destruct (stuck_dec c1). apply NotStuck_negation in H1. contradiction.
    simpl. destruct (stuck_dec (c1 / e)).
    ** simpl. destruct (stuck_dec c2).
      *** rewrite stuck_derive. apply PeanoNat.Nat.lt_add_pos_l. apply NotStuck_0lt. all :assumption.
      *** rewrite <- (plus_O_n (con_size (c2 / e))). apply IHc2 in n0. lia.
    ** apply IHc1 in H1. destruct (stuck_dec c2).
      *** rewrite (stuck_derive _ s). apply Max.max_case_strong.
        **** intros. apply Plus.plus_lt_compat_r. assumption.
        **** intros. lia.
      *** apply IHc1 in n. apply IHc2 in n1. lia.
  * destruct (stuck_dec c1).
    ** apply NotStuck_negation in H1. contradiction.
    ** simpl. destruct (stuck_dec (c1 / e)).
      *** pose proof (NotStuck_0lt H1). lia.
      *** apply Plus.plus_lt_compat_r. auto.
Defined.


Equations plus_norm (c : Contract) : (Contract) by  wf (con_size (c)) :=
plus_norm c := if stuck_dec c then Failure
               else let c' := Success _+_ fold_left (fun acc e => acc _+_ (Event e) _;_ (plus_norm (c / e)))  alphabet Failure
                    in if nu c then Success _+_ c' else c'.
Next Obligation. auto using not_stuck_derives. Defined.

Global Transparent plus_norm.
Eval compute in plus_norm (Transfer _._ Notify _._ Success _+_ Success).

Event Transfer)).

Equations plus_norm2 (c : Contract) : (Contract) by  wf (0) :=
plus_norm2 Failure := Failure;
plus_norm2 c := Event Notify _;_ plus_norm (c / Notify) .
Admit Obligations.

Eval compute in (plus_norm2 (Success _+_ Event Transfer)).

Print plus_norm2_functional.

  times c0 c1 :=
        if eq_contract_dec (norm c0) Failure
        then []
        else if eq_contract_dec (norm c1) Failure
        then []
        else if eq_contract_dec (norm c0) Success then [norm c1]
        else if eq_contract_dec (norm c1) Success then [norm c0]
        (*Incorrect, for completeness if c0 is nullary, then expression below ++ [norm c1] should be returned*)
        else (flat_map (fun e => map (fun c => (Event e) _;_ c) (times ((norm c0)  / e) (norm c1) )) alphabet)
             ++
             (flat_map (fun e => map (fun c => (Event e) _;_ c) (times (norm c0)  ((norm c1)  /e ))) alphabet).
Next Obligation.

Definition plus_list (c : Contract) (alphabet : list EventType): list Contract := map (fun e => (Event e _;_ c/e)) alphabet .

Hint Unfold plus_list : core.

Lemma derive_spec_comp : forall (c : Contract)(e : EventType)(s : Trace), e::s ==~ c <-> s ==~ c / e.
Proof.
split ; repeat rewrite comp_iff_oper ; intro H ; rewrite <- H ; apply derive_spec.
Qed.

Definition list_derivative (l : list Contract)(e : EventType) := map (fun c => c / e) l.

Hint Unfold list_derivative : core.



Lemma list_derivative_spec : forall (l : list Contract)(e : EventType), (plus_fold l) / e = plus_fold (list_derivative l e).
Proof. intros. induction l.
- reflexivity.
- simpl. f_equal. assumption.
Qed.




Lemma plus_list_spec_alphabet : forall (e : EventType)(s : Trace)(c : Contract)(alphabet : list EventType), In e alphabet -> 
(e::s ==~ c <-> e::s ==~ plus_fold (plus_list c alphabet)).
Proof.
intros. repeat rewrite derive_spec_comp. rewrite list_derivative_spec. rewrite in_plus_fold.
unfold plus_list. unfold list_derivative. rewrite map_map. split.
- intros. exists (Success _;_ (c /e)). split. 
  * rewrite in_map_iff. exists e. simpl. destruct (eq_event_dec e e);try contradiction.
    split ; [ reflexivity | assumption].
  * rewrite <- (app_nil_l s). constructor; auto.
- intros [c0 [P0 P1]]. rewrite in_map_iff in P0. destruct P0 as [x [P3 P4]]. subst.
 simpl. simpl in P1. destruct (eq_event_dec x e).
  * inversion P1. inversion H3. subst. simpl. assumption.
  * inversion P1. inversion H3.
Qed.

Definition plus_norm_aux c := plus_fold (plus_list c alphabet).

Lemma plus_norm_aux_spec : forall (e : EventType)(s : Trace)(c : Contract),
(e::s ==~ c <-> e::s ==~ plus_norm_aux c).
Proof. 
unfold plus_norm_aux. 
assert (forall e : EventType, In e alphabet). { unfold alphabet. destruct e ; repeat (try apply in_eq ; try apply in_cons). }
intros. apply plus_list_spec_alphabet. auto.
Qed.

Definition plus_norm c := let c' := plus_norm_aux c
                          in if nu c then Success _+_ c' else c'.

Search (_ || _ = true).
Lemma empty_nu : forall (c : Contract), [] ==~ c <-> nu c = true.
Proof.
intros. split. 
- induction c; intros.
  * reflexivity.
  * inversion H.
  * inversion H.
  * inversion H. { simpl. rewrite IHc1; try assumption. reflexivity. }
                { simpl. rewrite IHc2; try assumption. rewrite orb_comm.  reflexivity. }
  * simpl. inversion H. apply app_eq_nil in H1 as [H11 H12]. subst. rewrite IHc1. rewrite IHc2. reflexivity.
  all: assumption.
- intros. induction c.
  * constructor.
  * discriminate H.
  * discriminate H.
  * simpl in H. apply orb_prop in H as [H | H]; auto.
  * simpl in H. rewrite <- (app_nil_l []). apply andb_prop in H as [H1 H2]; auto.
Qed.

Lemma seq_failure : forall (c : Contract)(s : Trace), ~(s ==~ c _;_ Failure).
Proof. intros. intro. inversion H. inversion H4. Defined.



Lemma empty_plus_norm_aux_false : forall (c : Contract), ~([] ==~ plus_norm_aux c).
Proof.
unfold plus_norm_aux. induction c; intros; intro; simpl in H.
- inversion H. apply seq_failure in H2 as [].  inversion H1. apply seq_failure in H6 as [].  inversion H6. 
- inversion H. apply seq_failure in H2 as [].  inversion H1. apply seq_failure in H6 as [].  inversion H6. 
- inversion H.
  * subst. inversion H2. apply app_eq_nil in H0 as [H00 H01]. subst. inversion H4.
  * subst. inversion H1. inversion H3. apply app_eq_nil in H5 as [H05 H15]. subst. inversion H8.
    inversion H3.
- inversion H.
  * subst. inversion H2. apply app_eq_nil in H0 as [H05 H15]. subst. inversion H4.
  * subst. inversion H1. inversion H3. apply app_eq_nil in H5 as [H05 H15]. subst. inversion H8. inversion H3. 
- inversion H.
  * subst. inversion H2. apply app_eq_nil in H0 as [H05 H15]. subst. inversion H4.
  * subst. inversion H1. inversion H3. apply app_eq_nil in H5 as [H05 H15]. subst. inversion H8. inversion H3.
Qed. 

Lemma plus_norm_spec : forall (c : Contract)(s : Trace),
(s ==~ c <-> s ==~ plus_norm c).
Proof.
intros. unfold plus_norm. destruct (nu c) eqn:Heqn.
- destruct s.
  * split.
    ** intros. auto.
    ** intros. apply empty_nu. assumption.
  * assert (HA: e :: s ==~ Success _+_ plus_norm_aux c <-> e :: s ==~ plus_norm_aux c).
    { split. ** intros. inversion H. inversion H2. assumption. **  intros. apply MPlusR. assumption. }
    rewrite HA. apply plus_norm_aux_spec.
- destruct s.
  * split. 
    ** intros. apply empty_nu in H. rewrite Heqn in H. discriminate. 
    ** intros. apply empty_plus_norm_aux_false in H as [].
  * apply plus_norm_aux_spec.
Qed.