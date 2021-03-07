Require Import Lists.List.
Require Import FunInd.
Require Import Recdef.
Require Import Bool.Bool.
Require Import Bool.Sumbool.
Require Import Program.
Require Import Arith.PeanoNat.
Require Import Structures.GenericMinMax.
From Equations Require Import Equations.
Require Import micromega.Lia.
Require Import FunctionalExtensionality.
Import ListNotations.
Require Export Setoid.
Require Export Relation_Definitions.
Require Import Arith.

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

(*
Lemma contract_or : forall (c0 c1 : Contract), c0 = c1 \/ c0 <> c1.
Proof.
induction c0.
- destruct c1 ; try (left ; reflexivity) ; try (right ; intro H ; discriminate).
- destruct c1 ; try (left ; reflexivity) ; try (right ; intro H ; discriminate).
- destruct c1 ; try (left ; reflexivity) ; try (right ; intro H ; discriminate).
  * destruct e; destruct e0; try (left; apply f_equal ; reflexivity). try (right ; intro H ; discriminate).
    ** right. intro H ; discriminate.
- induction c1. *)

Search (_ && _).
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


Definition c_eq (c c':Contract) : Prop := forall s, s ==~ c <-> s ==~ c'.
Notation "a =R= b" := (c_eq a b) (at level 70).

Lemma c_eq_refl : reflexive Contract c_eq.
Proof.
  unfold reflexive. intro x. split.
- intros H. apply H.
- intros H. apply H.
Qed.

Lemma c_eq_sym : symmetric Contract c_eq.
Proof.
  unfold symmetric. intros x y. unfold c_eq. intro H. split.
- intro H2. apply H. apply H2.
- intro H2. apply H. apply H2.
Qed.


Lemma c_eq_trans: transitive Contract c_eq.
Proof.
  unfold transitive.  intros x y z.  unfold c_eq. intros Hxy Hyz s. split.
- intro H. apply Hyz. apply Hxy. apply H.
- intro H. apply Hxy. apply Hyz. apply H.
Qed.

Add Parametric Relation : Contract c_eq
  reflexivity proved by c_eq_refl
  symmetry proved by c_eq_sym
  transitivity proved by c_eq_trans
  as Contract_setoid.


(*Algebraic properties *)

Lemma plus_comm : forall (c1 c2 : Contract), (c1 _+_ c2) =R= (c2 _+_ c1).
Proof.
split ; intros ; inversion H ; auto.
Qed.

Lemma plus_assoc : forall (c1 c2 c3 : Contract), ((c1 _+_ c2) _+_ c3) =R= (c1 _+_ (c2 _+_ c3)).
Proof.
split.
- intro H. inversion H.
  * inversion H2 ; auto. 
  * auto.
- intro H. inversion H.
  * inversion H2 ; auto.
  * inversion H1 ; auto.
Qed.


Lemma seq_assoc : forall (c1 c2 c3 : Contract), ((c1 _;_ c2) _;_ c3) =R= (c1 _;_ (c2 _;_ c3)).
Proof.
split.
- intros. inversion H. inversion H3. rewrite <- app_assoc. all : auto.
- intro H. inversion H. inversion H4. rewrite -> app_assoc. all : auto. 
Qed.

Lemma plus_or : forall (s : Trace)(c1 c2 : Contract), s ==~ (c1 _+_ c2) <-> s ==~ c1 \/ s ==~c2.
Proof. 
split.
- intros. repeat rewrite comp_iff_oper in *. 
apply plus_or_oper in H. assumption.
- intros. destruct H; auto.
Qed.


Lemma plus_distr : forall (c1 c2 c3 : Contract), (c1 _;_ (c2 _+_ c3)) =R= (c1 _;_ c2) _+_ (c1 _;_ c3).
Proof. split.
- intros. inversion H ; inversion H4 ; auto.
- intros. apply plus_or in H as [H | H] ; inversion H ; auto.
Qed.

Lemma plus_distr2 : forall (c1 c2 c3 : Contract), ((c1 _+_ c2) _;_ c3) =R= (c1 _;_ c3) _+_ (c2 _;_ c3).
Proof. split.
- intros ; inversion H ; inversion H3 ; auto.
- intros ; inversion H ; try inversion H2 ; try inversion H1 ; auto.
Qed.

(*Parallel contracts section*)
Inductive PContract : Set :=
| PSuccess : PContract
| PFailure : PContract
| PEvent : EventType -> PContract
| PPlus : PContract -> PContract -> PContract
| PPar : PContract -> PContract -> PContract.

Notation "e -.- c" := (PPar (PEvent e) c)
                    (at level 41, right associativity).

Notation "c0 -*- c1"  := (PPar c0 c1)
                         (at level 50, left associativity).

Notation "c0 -+- c1"  := (PPlus c0 c1)
                         (at level 61, left associativity).


(*Taken from csl-formalization*)
Inductive interleave (A : Set) : list A -> list A -> list A -> Prop :=
| IntLeftNil  : forall t, interleave nil t t
| IntRightNil : forall t, interleave t nil t
| IntLeftCons : forall t1 t2 t3 e, interleave t1 t2 t3 -> interleave (e :: t1) t2 (e :: t3)
| IntRightCons : forall t1 t2 t3 e, interleave t1 t2 t3 -> interleave t1 (e :: t2) (e :: t3).


Reserved Notation "s p==~ re" (at level 63).

Inductive pmatches_comp : Trace -> PContract -> Prop :=
  | MPSuccess : [] p==~ PSuccess
  | MPEvent x : [x] p==~ (PEvent x)
  | MPPar s1 c1 s2 c2 s
             (H1 : s1 p==~ c1)
             (H2 : s2 p==~ c2)
             (H3 : interleave s1 s2 s)
           : s p==~ (c1 -*- c2)
  | MPPlusL s1 c1 c2
                (H1 : s1 p==~ c1)
              : s1 p==~ (c1 -+- c2)
  | MPPlusR c1 s2 c2
                (H2 : s2 p==~ c2)
              : s2 p==~ (c1 -+- c2)
  where "s p==~ c" := (pmatches_comp s c).


Fixpoint con_size (c:Contract):nat :=
match c with
| Success => 2
| Failure => 1
| Event e => 3
| c0 _;_ c1 => (con_size c0) * (con_size c1)
| c0 _+_ c1 => (con_size c0) + (con_size c1)
end.

Check sumbool_and.


Fixpoint norm  (c : Contract) : Contract :=
match c with
| Success => Success
| Failure => Failure
| Event e => Event e
| c0 _;_ c1 => let c0' := norm c0
               in let c1' := norm c1
                  in if (sumbool_or _ _ _ _ (eq_contract_dec c0' Failure) (eq_contract_dec c1' Failure ))  then Failure
                     else if (eq_contract_dec c0' Success) then c1'
                     else if (eq_contract_dec c1' Success) then c0'
                     else c0' _;_ c1'
| c0 _+_ c1 => let c0' := norm c0
               in let c1' := norm c1
                  in if (sumbool_and _ _ _ _ (eq_contract_dec c0' Success) (eq_contract_dec c1' Success)) then Success
                     else if (eq_contract_dec c0' Failure) then c1'
                     else if (eq_contract_dec c1' Failure) then c0'
                     else c0' _+_ c1'
end.


Lemma norm_plus_induct : forall (P : Contract -> Prop)(c0 c1 : Contract),
(norm c0 = Success -> norm c1 = Success -> P Success) ->
((norm c0 <> Success \/ norm c1 <> Success) ->  norm c0 = Failure -> P (norm c1)) ->
((norm c0 <> Success \/ norm c1 <> Success) ->  (norm c0 <> Failure) -> norm c1 = Failure -> P (norm c0)) ->
((norm c0 <> Success \/ norm c1 <> Success) ->  (norm c0 <> Failure) -> (norm c1 <> Failure) -> P (norm c0 _+_ norm c1))
-> P (norm (c0 _+_ c1)).
Proof.
intros. simpl. destruct (eq_contract_dec (norm c0) Failure). 
- destruct (sumbool_and (norm c0 = Success) (norm c0 <> Success)
      (norm c1 = Success) (norm c1 <> Success)
      (eq_contract_dec (norm c0) Success)
      (eq_contract_dec (norm c1) Success)) as [[a0 a1] | [a | a] ]; auto.
- destruct (sumbool_and (norm c0 = Success) (norm c0 <> Success)
      (norm c1 = Success) (norm c1 <> Success)
      (eq_contract_dec (norm c0) Success)
      (eq_contract_dec (norm c1) Success)) as [[a0 a1] | [a | a] ]; 
  destruct (eq_contract_dec (norm c1) Failure) ; auto.
Qed.

Lemma norm_seq_induct : forall (P : Contract -> Prop)(c0 c1 : Contract),
(norm c0 = Failure \/ norm c1 = Failure -> P Failure) ->
((norm c0 <> Failure /\ norm c1 <> Failure) ->  norm c0 = Success -> P (norm c1)) ->
((norm c0 <> Failure /\ norm c1 <> Failure) ->  (norm c0 <> Success) -> norm c1 = Success -> P (norm c0)) ->
((norm c0 <> Failure /\ norm c1 <> Failure) ->  (norm c0 <> Success) -> (norm c1 <> Success) -> P (norm c0 _;_ norm c1))
-> P (norm (c0 _;_ c1)).
Proof.
intros. simpl. destruct (eq_contract_dec (norm c0) Success).
- destruct (sumbool_or (norm c0 = Failure) (norm c0 <> Failure)
      (norm c1 = Failure) (norm c1 <> Failure)
      (eq_contract_dec (norm c0) Failure)
      (eq_contract_dec (norm c1) Failure)) ; try auto.
- destruct (sumbool_or (norm c0 = Failure) (norm c0 <> Failure) (norm c1 = Failure)
      (norm c1 <> Failure) (eq_contract_dec (norm c0) Failure)
      (eq_contract_dec (norm c1) Failure)) ; auto.
  * destruct (eq_contract_dec (norm c1) Success) ; auto.
Qed.


Lemma match_closed_norm : forall (s : Trace)(c : Contract), s ==~ c <-> s ==~ (norm c).
Proof.
split.
- intros. generalize dependent s. induction c; intros; try (simpl ; assumption).
  * apply norm_plus_induct.
    ** intros. rewrite H0 in IHc1. rewrite H1 in IHc2. inversion H; auto. 
    ** intros [H2 | H2] H3 ; inversion H; auto.
       all: (apply IHc1 in H4; rewrite H3 in H4; inversion H4).
    ** intros [ H2 | H2] H3 H4;
       inversion H ; auto; (rewrite H4 in IHc2; apply IHc2 in H5; inversion H5).
    ** intros [H2 | H2] H3 H4; inversion H; auto using MPlusL,MPlusR. 
  * apply norm_seq_induct.
    ** intros [H1 | H1]; inversion H.
      *** rewrite H1 in IHc1. apply IHc1 in H4. inversion H4.
      *** rewrite H1 in IHc2. apply IHc2 in H5. inversion H5.
    ** intros [H1 H2] H3 ; inversion H. apply IHc1 in H6. 
       rewrite H3 in H6. inversion H6. simpl. auto.
    ** intros [H1 H2] H3 H4; inversion H. apply IHc2 in H8.
       rewrite H4 in H8. inversion H8. rewrite app_nil_r. auto.
    ** intros [H1 H2] H3 H4. inversion H. auto.
- intros. generalize dependent s. induction c; intros; try (simpl ; assumption).
  * simpl in H. destruct (sumbool_and (norm c1 = Success) (norm c1 <> Success)
        (norm c2 = Success) (norm c2 <> Success)
        (eq_contract_dec (norm c1) Success)
        (eq_contract_dec (norm c2) Success)) as [[a1 a2] | [a | a]] ; auto.
    ** rewrite a1 in IHc1. auto.
    ** destruct (eq_contract_dec (norm c1) Failure) ; auto.
      *** destruct (eq_contract_dec (norm c2) Failure) ; auto.
        **** inversion H ; auto.
    ** destruct (eq_contract_dec (norm c1) Failure); auto.
      *** destruct (eq_contract_dec (norm c2) Failure) ; auto.
        **** inversion H ; auto.
  * simpl in H. destruct ( sumbool_or (norm c1 = Failure) (norm c1 <> Failure)
        (norm c2 = Failure) (norm c2 <> Failure)
        (eq_contract_dec (norm c1) Failure)
        (eq_contract_dec (norm c2) Failure)) as [[o | o ] | [o1 o2 ]] ; auto.
    ** inversion H.
    ** inversion H.
    ** destruct (eq_contract_dec (norm c1) Success) ; auto. 
      ***  rewrite <- (app_nil_l s). constructor ; try auto. { apply IHc1. rewrite e. constructor. }
      *** destruct (eq_contract_dec (norm c2) Success).
        **** rewrite <- (app_nil_r s). constructor ; try auto. { apply IHc2. rewrite e. auto. }
        **** inversion H. auto. 
Qed.

Lemma norm_failure_not_match : forall (c : Contract), norm c = Failure ->
forall (s : Trace), ~(s ==~ c).
Proof.
intros.
- intros. intro H2. apply match_closed_norm in H2. rewrite H in H2. inversion H2.
Qed.

Lemma norm_failure_equivalence : forall (c : Contract), norm c = Failure ->
forall (s : Trace), ~(s ==~ c).
Proof.
intros.
- apply norm_failure_not_match. assumption.
Qed.

Lemma norm_success_equivalence : forall (c : Contract), norm c = Success -> [] ==~ c.
Proof. intros. apply match_closed_norm. rewrite H. auto.
Qed.


(*A safe contract has a smaller derivative*)
Inductive safe : Contract -> Prop :=
| SASuccess : safe Success
| SAEvent e : safe (Event e)
| SASeq c1 c2 (H1 : safe c1) (H2 : safe c2) : safe (c1 _;_ c2)
| SAPlus c1 c2 (H1 : safe c1) (H2 : safe c2) : safe (c1 _+_ c2).
Hint Constructors safe : core.

Lemma failure_not_safe : forall (c : Contract), (norm c) = Failure -> ~(safe (norm c)).
Proof.
intros. intro H'. inversion H' ; try (rewrite H in H1 ; discriminate H1).
Qed.

Lemma safe_not_failure : forall (c : Contract),  (safe (norm c)) -> c <> Failure.
Proof.
intros. induction c; simpl in H; intro H2; try discriminate H2.
- inversion H.
Qed.

(*
Lemma not_safe_is_failure : forall (c : Contract), ~(safe (norm c)) -> (norm c) = Failure.
Proof.
intros. induction c ; try (simpl in H; exfalso; apply H; constructor).
- reflexivity.
- s H. intro H'. inversion H' ; try (rewrite H in H1 ; discriminate H1).
Qed.*)


Lemma norm_not_failure_plus : forall (c1 c2 : Contract), (norm c1 <> Failure -> safe (norm c1)) -> 
(norm c2 <> Failure -> safe (norm c2)) -> norm (c1 _+_ c2) <> Failure -> safe (norm c1) \/ safe (norm c2).
Proof. 
intros. simpl in H1. 
destruct (sumbool_and (norm c1 = Success) (norm c1 <> Success)
         (norm c2 = Success) (norm c2 <> Success)
         (eq_contract_dec (norm c1) Success)
         (eq_contract_dec (norm c2) Success)) as [[a1 a2] | a1].
  - right. rewrite a2. auto.
  - destruct (eq_contract_dec (norm c1) Failure). 
    * auto || auto.
    * destruct (eq_contract_dec (norm c2) Failure).
      ** auto || auto.
      ** auto || auto. 
Qed. 

Lemma norm_not_failure_seq : forall (c1 c2 : Contract), (norm c1 <> Failure -> safe (norm c1))  -> 
(norm c2 <> Failure -> safe (norm c2)) -> (norm (c1 _;_ c2)) <> Failure -> safe (norm c1) /\ safe (norm c2).
Proof.
intros. simpl in H1. 
destruct (sumbool_or (norm c1 = Failure) (norm c1 <> Failure)
         (norm c2 = Failure) (norm c2 <> Failure)
         (eq_contract_dec (norm c1) Failure)
         (eq_contract_dec (norm c2) Failure)).
- contradiction.
- destruct (eq_contract_dec (norm c1) Success).
  * rewrite e. split ; try constructor. auto.
  * destruct a as [a1 a2]. split ; auto.
Qed.



Lemma size_ge_1 : forall (c : Contract), 1 <= con_size c.
Proof. induction c.
- simpl. intuition. 
- simpl. intuition.
- simpl. intuition.
- simpl. rewrite IHc1. intuition.
- simpl. rewrite IHc1. rewrite <- (Nat.mul_1_r (con_size c1)) at 1. apply Nat.mul_le_mono.
  { intuition. } { intuition. }
Qed.

Hint Resolve size_ge_1 : core.

Lemma mult_two_contracts_ge1 : forall (c1 c2 : Contract), 1 <= con_size c1 * con_size c2.
Proof.
intros. rewrite <- Nat.mul_1_l at 1. apply Nat.mul_le_mono ; auto.
Qed.

Lemma not_failure_imp_safe : forall (c : Contract), (norm c) <> Failure -> safe (norm c).
Proof.
induction c; try (intros ; simpl ; auto) ; try contradiction.
- destruct (sumbool_and (norm c1 = Success) (norm c1 <> Success)
      (norm c2 = Success) (norm c2 <> Success)
      (eq_contract_dec (norm c1) Success)
      (eq_contract_dec (norm c2) Success)) as [a1 | [e2|e3]]; try auto.
  * destruct (eq_contract_dec (norm c1) Failure). 
    ** simpl in H. rewrite e in H. simpl in H. 
       destruct (eq_contract_dec (norm c2) Success). 
      *** rewrite e0. auto. 
      *** auto. 
    ** destruct (eq_contract_dec (norm c2) Failure).
      *** auto.
      *** destruct ( sumbool_and (norm c1 = Success) (norm c1 <> Success)
      (norm c2 = Success) (norm c2 <> Success)
      (eq_contract_dec (norm c1) Success)
      (eq_contract_dec (norm c2) Success)) ; constructor ; auto.
  * destruct (eq_contract_dec (norm c1) Failure).
    ** simpl in H. rewrite e in H. simpl in H.
       destruct (eq_contract_dec (norm c2) Success) ; auto.
    ** destruct (eq_contract_dec (norm c2) Failure) ; auto.
- destruct (sumbool_or (norm c1 = Failure) (norm c1 <> Failure) 
      (norm c2 = Failure) (norm c2 <> Failure)
      (eq_contract_dec (norm c1) Failure)
      (eq_contract_dec (norm c2) Failure)).
  * simpl in H. destruct o as [o | o].
    ** rewrite o in H. simpl in H. 
       destruct (eq_contract_dec (norm c2) Failure) ; contradiction.
    ** rewrite o in H. simpl in H.
       destruct (sumbool_or (norm c1 = Failure) (norm c1 <> Failure)
        (Failure = Failure) (Failure <> Failure)
        (eq_contract_dec (norm c1) Failure)
        (eq_contract_dec Failure Failure)).
      *** contradiction.
      *** destruct a as [a1 a2]. contradiction.
  * destruct (eq_contract_dec (norm c1) Success).
    ** destruct a as [a1 a2]. auto.
    ** destruct (eq_contract_dec (norm c2) Success).
      *** destruct a as [a1 a2]. auto.
      *** destruct a as [a1 a2] ; auto.
Qed.



Lemma norm_idempotent : forall (c0 : Contract), norm (norm c0) = norm c0.
Proof.
intros. induction c0 ; try reflexivity.
- apply norm_plus_induct ; intros ; auto ; try reflexivity.
  * simpl. rewrite IHc0_1. rewrite IHc0_2.
    destruct (sumbool_and (norm c0_1 = Success) (norm c0_1 <> Success)
    (norm c0_2 = Success) (norm c0_2 <> Success)
    (eq_contract_dec (norm c0_1) Success)
    (eq_contract_dec (norm c0_2) Success)).
    ** destruct H.
      *** destruct a. contradiction.
      *** destruct a. contradiction.
    ** destruct (eq_contract_dec (norm c0_1) Failure).
      *** contradiction.
      *** destruct (eq_contract_dec (norm c0_2) Failure).
        **** contradiction.
        **** reflexivity.
- apply norm_seq_induct ; intros ; auto ; try reflexivity.
  * simpl. destruct (sumbool_or (norm (norm c0_1) = Failure)
    (norm (norm c0_1) <> Failure) (norm (norm c0_2) = Failure)
    (norm (norm c0_2) <> Failure)
    (eq_contract_dec (norm (norm c0_1)) Failure)
    (eq_contract_dec (norm (norm c0_2)) Failure)).
    ** destruct o.
      *** destruct H. rewrite IHc0_1 in *. contradiction.
      *** destruct H. rewrite IHc0_2 in *. contradiction.
    ** destruct (eq_contract_dec (norm (norm c0_1)) Success). 
      *** destruct a.  rewrite IHc0_1 in *. contradiction.
      *** destruct (eq_contract_dec (norm (norm c0_2)) Success).
        ****  rewrite IHc0_2 in *. contradiction.
        **** rewrite IHc0_1. rewrite IHc0_2. reflexivity.
Qed.


Lemma safe_le : forall (c : Contract), safe c -> forall (e : EventType), con_size (c / e) <= (con_size c) - 1.
Proof. 
intros c H. induction H.
- intuition.
- intuition. simpl. destruct (eq_event_dec e e0) ; auto.
- intro e. simpl. destruct (nu c1) eqn:Heqn.
  * simpl. specialize IHsafe1 with e. specialize IHsafe2 with e. 
    transitivity ((con_size c1 - 1) * con_size c2 + (con_size c2 - 1)).
    ** apply Nat.add_le_mono. { apply Mult.mult_le_compat_r. intuition. } { intuition. }
    ** rewrite Nat.mul_sub_distr_r. simpl. rewrite Nat.add_0_r. rewrite Nat.add_comm. 
      rewrite <- (Nat.add_sub_swap _ _ _ (size_ge_1 c2)) . rewrite (Nat.add_le_mono_r _ _ 1).
      rewrite Nat.sub_add.
      *** rewrite Nat.sub_add. 2: { apply mult_two_contracts_ge1. }
          rewrite Nat.add_comm. rewrite Nat.sub_add. { reflexivity. }
          rewrite <- Nat.mul_1_l at 1. apply Nat.mul_le_mono_r. apply size_ge_1.
      *** rewrite <- Nat.add_0_r at 1. apply Nat.add_le_mono. { apply size_ge_1. } { lia. }
  * simpl. transitivity ((con_size c1 - 1) * con_size c2).
    ** apply Nat.mul_le_mono_r. apply IHsafe1.
    ** rewrite Nat.mul_sub_distr_r. apply Nat.sub_le_mono_l. transitivity (1 * 1).
      *** simpl. intuition.
      *** apply Mult.mult_le_compat_l. apply size_ge_1.
- intro e. simpl. assert (HR: con_size c1 + con_size c2 - 1 = (con_size c1 - 1) + con_size c2).
  * rewrite (Nat.add_sub_swap _ _ _ (size_ge_1 c1)). rewrite Nat.add_comm. reflexivity.
  * rewrite HR. apply Nat.add_le_mono.
    ** apply IHsafe1.
    ** transitivity (con_size c2 - 1). { apply IHsafe2. } { lia. } 
Qed.

Lemma safe_lt : forall (c : Contract), safe c -> forall (e : EventType), con_size (c / e) < (con_size c).
Proof.
intros c H e. pose proof (safe_le H e). apply Lt.le_lt_n_Sm in H0. rewrite (Minus.minus_Sn_m _ _ (size_ge_1 c)) in H0.
rewrite Nat.sub_succ in H0. rewrite Nat.sub_0_r in H0. apply H0. 
Qed.

Definition alphabet := [Transfer;Notify].


Lemma all_in_alpabet : forall e : EventType, In e alphabet.
Proof.
intros. unfold alphabet. destruct e. 
- apply in_eq.
- apply in_cons. apply in_eq.
Qed.

Search (1 * ?a).
Lemma norm_le : forall (c : Contract), con_size (norm c) <= con_size c.
Proof.
assert (HA: 2 = 1 +1). { reflexivity. }
induction c.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. destruct (sumbool_and (norm c1 = Success) (norm c1 <> Success)
      (norm c2 = Success) (norm c2 <> Success)
      (eq_contract_dec (norm c1) Success)
      (eq_contract_dec (norm c2) Success)).
  * simpl. rewrite  HA. apply Nat.add_le_mono ; apply size_ge_1.
  * destruct (eq_contract_dec (norm c1) Failure). 
    ** lia.
    ** destruct (sumbool_and (norm c1 = Success) (norm c1 <> Success)
      (norm c2 = Success) (norm c2 <> Success)
      (eq_contract_dec (norm c1) Success)
      (eq_contract_dec (norm c2) Success));
       destruct (eq_contract_dec (norm c2) Failure) ; simpl ; lia.
- simpl. destruct (eq_contract_dec (norm c1) Failure).
  * simpl. destruct (eq_contract_dec (norm c2) Failure ); simpl; apply mult_two_contracts_ge1.
  * destruct (sumbool_or (norm c1 = Failure) (norm c1 <> Failure) 
      (norm c2 = Failure) (norm c2 <> Failure) in_right
      (eq_contract_dec (norm c2) Failure)).
    ** simpl; apply mult_two_contracts_ge1.
    ** destruct (eq_contract_dec (norm c1) Success). 
      *** rewrite <- Nat.mul_1_l at 1. apply Nat.mul_le_mono ; auto.
      *** destruct (eq_contract_dec (norm c2) Success).
        **** rewrite <- Nat.mul_1_r at 1.
           apply Nat.mul_le_mono ; auto.
        **** simpl. apply Nat.mul_le_mono ; auto.
Qed.


Lemma times_termination : forall (c0 c1 : Contract)(e : EventType), 
norm c0 <> Failure -> (norm c1) <> Failure -> con_size (norm c0 / e) + con_size (norm c1) < con_size c0 + con_size c1.
Proof.
intros. apply not_failure_imp_safe in H. apply not_failure_imp_safe in H0. 
apply (Nat.lt_le_trans _ (con_size (norm c0) + con_size (norm c1)) _).
- apply Nat.add_lt_le_mono ; auto using (safe_lt H).
- apply Nat.add_le_mono ; apply norm_le.
Qed.


Equations times (c0 : Contract) (c1 : Contract) : (list Contract) by  wf ((con_size (c0)) + (con_size (c1))) lt :=
  times c0 c1 :=
        if eq_contract_dec (norm c0) Failure
        then []
        else if eq_contract_dec (norm c1) Failure
        then []
        else if eq_contract_dec (norm c0) Success then [norm c1]
        else if eq_contract_dec (norm c1) Success then [norm c0]
        (*Incorrect, for completeness nullary contracts which are not necessarily Success needs a case as well*)
        else (flat_map (fun e => map (fun c => (Event e) _;_ c) (times ((norm c0)  / e) (norm c1) )) alphabet)
             ++
             (flat_map (fun e => map (fun c => (Event e) _;_ c) (times (norm c0)  ((norm c1)  /e ))) alphabet).
Next Obligation.
apply (times_termination _ _ e) ; assumption.
Qed.
Next Obligation.
rewrite Nat.add_comm. rewrite (Nat.add_comm (con_size c0)). 
apply (times_termination _ _ e); assumption.
Qed.
Global Transparent times.
Print eq_contract_dec.

Compute ((times Failure Failure)).

(*Compute (times (Transfer _._ Success) ( Transfer _._ Success)).*)

Definition list_derivative (l : list Contract)(e : EventType) := map (fun c => c / e) l.


Equations plus_fold (l : list Contract) : Contract :=
  plus_fold [] := Failure;
  plus_fold (c::l) := c _+_ (plus_fold l).

Global Transparent plus_fold.


Lemma list_derivative_spec : forall (l : list Contract)(e : EventType), (plus_fold l) / e = plus_fold (list_derivative l e).
Proof. intros. funelim (plus_fold l).
- reflexivity.
- simpl. specialize H with e. now rewrite H.
Qed.

Lemma list_derivative_app : forall (l1 l2 : list Contract)(e : EventType), 
list_derivative (l1 ++ l2) e = (list_derivative l1 e) ++ (list_derivative l2 e).
Proof.
intros. unfold list_derivative. apply map_app.
Qed.

Search (?a :: ?b = [?a] ++ ?b). 

Search (map (fun _ => map _ _)). 

Lemma plus_failure : forall (s : Trace)(c : Contract), s ==~ c _+_ Failure -> s ==~ c.
Proof.
intros. inversion H. assumption. inversion H1.
Qed.

Lemma plus_fold_app : forall (s:Trace)(l1 l2 : list Contract), 
s ==~ plus_fold (l1 ++ l2) <-> s ==~ (plus_fold l1) _+_ (plus_fold l2).
Proof.
intro. induction l1.
- intros. split.
  * intros. simpl in H. apply MPlusR. assumption.
  * intros. simpl. simpl in H. apply plus_comm in H. apply plus_failure in H. assumption.
- intros. split.
  * intros. simpl in *. apply plus_or in H as [H | H]. { apply MPlusL. apply MPlusL. assumption. }
                                                       { specialize IHl1 with l2. apply IHl1 in H. 
                                                         apply plus_assoc. apply MPlusR. assumption. } 
  * intros. simpl in *. apply plus_assoc in H. apply plus_or in H as [H | H].
    ** apply MPlusL. assumption.
    ** apply MPlusR. apply IHl1. assumption.
Qed.

Lemma flat_map_list_derivative : forall (f: EventType -> list Contract) (l: list EventType)(e : EventType),
  list_derivative (flat_map f l) e = flat_map (fun x=> list_derivative (f x) e) l.
Proof. intros. repeat rewrite flat_map_concat_map. repeat unfold list_derivative. 
rewrite concat_map. rewrite map_map. reflexivity.
Qed.


Lemma inline_derivative_l : forall (c0 c1 : Contract)(e' : EventType),
list_derivative (flat_map (fun e => map (fun c => (Event e) _;_ c) (times ((norm c0) / e) (norm c1) )) alphabet) e' = 
(flat_map (fun e => map (fun c =>  (if eq_event_dec e e' then Success _;_ c else Failure _;_ c) ) (times ((norm c0) / e) (norm c1) )) alphabet).
Proof.
intros. rewrite flat_map_list_derivative. 
unfold list_derivative.
assert (HA : (fun x => map (fun c : Contract => c / e') (map (fun c : Contract => Event x _;_ c)  (times ((norm c0)/x) (norm c1) ))) =
             fun x => (map (fun c : Contract => (if eq_event_dec x e' then Success _;_ c else Failure _;_ c)) (times ((norm c0)/x) (norm c1)))).
- apply functional_extensionality. intros. rewrite map_map.
  assert (HA2: (fun x0 : Contract => (Event x _;_ x0) / e') = 
               (fun c : Contract => if eq_event_dec x e' then Success _;_ c else Failure _;_ c)).
  * apply functional_extensionality. intros. simpl. destruct (eq_event_dec x e') ; reflexivity.
  * now rewrite HA2.
- now rewrite HA. 
Qed.


Lemma inline_derivative_r : forall (c0 c1 : Contract)(e' : EventType),
list_derivative (flat_map (fun e => map (fun c => (Event e) _;_ c) (times ((norm c0)) ((norm c1)/ e) )) alphabet) e' = 
(flat_map (fun e => map (fun c =>  (if eq_event_dec e e' then Success _;_ c else Failure _;_ c) ) (times ((norm c0)) ((norm c1) / e) )) alphabet).
Proof.
intros. rewrite flat_map_list_derivative. 
unfold list_derivative.
assert (HA : (fun x => map (fun c : Contract => c / e') (map (fun c : Contract => Event x _;_ c)  (times ((norm c0)) ((norm c1)/ x) ))) =
             fun x => (map (fun c : Contract => (if eq_event_dec x e' then Success _;_ c else Failure _;_ c)) (times ((norm c0)) ((norm c1) / x)))).
- apply functional_extensionality. intros. rewrite map_map.
  assert (HA2: (fun x0 : Contract => (Event x _;_ x0) / e') = 
               (fun c : Contract => if eq_event_dec x e' then Success _;_ c else Failure _;_ c)).
  * apply functional_extensionality. intros. simpl. destruct (eq_event_dec x e'); reflexivity.
  * now rewrite HA2.
- now rewrite HA. 
Qed.


Lemma interleave_filter : forall (A:Set)(f : A -> bool)(l : list A), interleave (filter f l) (filter (fun x => negb (f x)) l) l.
Proof. 
intros. induction l.
- simpl. constructor.
- simpl. destruct (f a) eqn:Heqn ; simpl ; constructor ; assumption.
Qed.

Lemma interleave_closed_map : forall (A B:Set)(l1 l2 l : list A)(f : A ->  B), interleave l1 l2 l -> 
  interleave (map f l1) (map f l2) (map f l).
Proof. intros. induction H; simpl ; try constructor ; try assumption. 
Qed.


Lemma interleave_closed_concat : forall (A:Set) (l1 l2 l : list (list A)), interleave l1 l2 l -> 
  interleave (concat l1) (concat l2) (concat l).
Proof. intros.
assert (cons_app : forall (A : Type)(a : A) (l' : list A), a :: l' = [a] ++ l').
  { intros. reflexivity. }
 induction H; try (simpl ; constructor).
- induction e.
  * simpl. assumption.
  * simpl. simpl in IHe. constructor. assumption.
- induction e.
  * simpl. assumption.
  * simpl. simpl in IHe. constructor. assumption.
Qed.

Lemma interleave_closed_flat_map : forall (A B:Set) (l1 l2 l : list A)(f : A -> list B), interleave l1 l2 l -> 
  interleave (flat_map f l1) (flat_map f l2) (flat_map f l).
Proof. intros. repeat rewrite flat_map_concat_map. apply interleave_closed_concat.
apply interleave_closed_map. induction H ; try (simpl ; constructor) ; assumption.
Qed.




Lemma or_imp : forall a b c : Prop, (a \/ b -> c) -> (b -> c).
intros. apply H. right. assumption.
Qed.

Lemma map_congruence : forall (A B:Set) (f g : A -> B) (l1 l2 : list A),
l1 = l2 -> (forall (x : A), In x l1 -> f x = g x) -> map f l1 = map g l2.
Proof. intros. subst. induction l2. 
- intros. subst. reflexivity.
- intros. simpl. pose proof (H0 a (in_eq a _)). rewrite H. apply f_equal.
  simpl in H0.
  * assert (HA: forall x : A, In x l2 -> f x = g x).
    {  intros. specialize H0 with x. apply H0. right. assumption. }
    apply IHl2. assumption.
Qed. 


Fixpoint trans (p : PContract) : Contract :=
match p with
| PSuccess => Success
| PFailure => Failure
| PEvent e => Event e
| p0 -*- p1 => plus_fold (times (trans p0) (trans p1))
| p0 -+- p1 => (trans p0) _+_ (trans p1)
end.


Lemma derive_spec_comp : forall (c : Contract)(e : EventType)(s : Trace), e::s ==~ c <-> s ==~ c / e.
Proof.
split ; repeat rewrite comp_iff_oper ; intro H ; rewrite <- H ; apply derive_spec.
Qed.



Lemma decompose_plus_fold : forall (l1 l2 : list Contract)(s : Trace)(e : EventType), s ==~ (plus_fold (l1 ++ l2)) -> 
s ==~ plus_fold l1 \/ s ==~ plus_fold l2.
Proof.
intros. apply plus_fold_app in H. apply plus_or. assumption.
Qed.



Equations or_fold (l : list bool) : bool :=
  or_fold [] := false;
  or_fold (c::l) := c || (or_fold l).

Global Transparent or_fold.


Lemma plus_fold_or_fold : forall (s : Trace) (l : list Contract),
 (s =~ plus_fold l) = true -> or_fold (map (fun c => s =~ c) l) = true.
Proof.
intros. induction l.
- simpl in H. apply comp_iff_oper in H. inversion H.
- simpl in *. apply comp_iff_oper in H. apply plus_or in H as [H | H].
  * simpl. apply orb_true_intro. left. apply comp_iff_oper. assumption.
  * apply orb_true_intro. right. apply IHl. apply comp_iff_oper. assumption.
Qed.

Lemma in_plus_fold : forall (s : Trace)(l : list Contract), s ==~ plus_fold l <-> 
(exists c, In c l /\ s ==~ c).
Proof.
intros. split.
- induction l.
  * intros.  simpl in H. inversion H.
  * intros. simpl in H. apply plus_or in H as [H | H].
    ** exists a. split. apply in_eq. assumption.
    ** apply IHl in H as [c' [P1 P2]]. exists c'. split. { apply in_cons. assumption. } { assumption. }
- intros. destruct H as [ c' [P1 P2]]. induction l.
  * destruct P1.
  * apply in_inv in P1 as [P1 | P1].
    ** simpl. rewrite P1. apply MPlusL. assumption. 
    ** simpl.  apply MPlusR. auto.
Qed.

(*in_inv*)
Lemma oper_false : forall (s : Trace)(c : Contract), ~(s ==~c) -> s =~ c = false.
Proof.
intros. destruct (s =~ c) eqn:Heqn.
- apply comp_iff_oper in Heqn. contradiction.
- reflexivity.
Qed.

Lemma reduce_success : forall (s : Trace)(c : Contract), s =~ Success _;_ c = s =~ c.
Proof.
intros. destruct s.
- reflexivity.
- simpl. destruct (s =~ c / e) eqn:Heqn. 
  * apply comp_iff_oper. apply MPlusR. apply comp_iff_oper. assumption.
  * apply oper_false. intro H2. apply plus_or in H2 as [H2 | H2].
    ** inversion H2. inversion H3.
    ** apply comp_iff_oper in H2. rewrite Heqn in H2. discriminate.
Qed.

Lemma reduce_success_comp : forall (s : Trace)(c : Contract), s ==~ Success _;_ c <-> s ==~ c.
Proof.
split.
- intros. apply comp_iff_oper in H. rewrite reduce_success in H.
apply comp_iff_oper in H. assumption.
- intros. rewrite <- (app_nil_l s). constructor ; auto.
Qed.


Lemma times_derivative_or: forall (c0 c1 : Contract)(e : EventType)(s : Trace), s ==~ (plus_fold (times c0 c1)) / e
 -> s ==~ plus_fold ((times ((norm c0) / e) (norm c1))) \/ s==~ plus_fold (times (norm c0) ((norm c1) / e)).
Proof. 
intros. simp times in H. destruct (eq_contract_dec (norm c0) Failure) eqn:Heqn1.
  * inversion H. 
  * destruct (eq_contract_dec (norm c1) Failure).
    ** inversion H.
    ** destruct (eq_contract_dec (norm c0) Success).
      *** simpl in H. right. rewrite e0. simp times. simpl.
          destruct (eq_contract_dec (norm (norm c1 / e)) Failure).
        **** apply plus_failure in H. apply norm_failure_equivalence with (s:=s) in e1.
             contradiction.
        **** apply plus_failure in H. simpl. apply MPlusL. apply -> match_closed_norm.
             assumption.
      *** destruct (eq_contract_dec (norm c1) Success).
        **** left. rewrite e0. simp times. simpl. 
              destruct (eq_contract_dec (norm (norm c0 / e)) Failure).
          ***** simpl in H. apply plus_failure in H.
                apply match_closed_norm in H. rewrite e1 in H. inversion H.
          ***** destruct (eq_contract_dec (norm (norm c0 / e)) Success).
            ****** simpl in H. apply plus_failure in H. 
                   apply match_closed_norm in H. rewrite e1 in H.
                   simpl. apply MPlusL. assumption.
            ****** simpl in *. apply MPlusL. apply -> match_closed_norm.
                   apply plus_failure in H. assumption.  
(*Everything up until this point is only for the base cases Failure and Success*)
        **** rewrite list_derivative_spec in H. rewrite list_derivative_app in H.
             apply plus_fold_app in H. apply plus_or in H as [H | H].
          ***** left. rewrite inline_derivative_l in H. 
                apply in_plus_fold in H as [c' [P1 P2]].
                apply in_flat_map in P1 as [x' [P3 P4]].
            ****** apply in_plus_fold. destruct (eq_event_dec x' e).
              ******* apply in_map_iff in P4 as [c'' [P5 P6]].
                      exists c''. rewrite e0 in P6. rewrite <- P5 in P2.
                      apply -> reduce_success_comp in P2.  split ; try assumption.
              ******* apply in_map_iff in P4 as [c'' [P5 P6]]. rewrite <- P5 in P2.
                      inversion P2. inversion H0.
          ***** right. rewrite inline_derivative_r in H. 
                apply in_plus_fold in H as [c' [P1 P2]].
                apply in_flat_map in P1 as [x' [P3 P4]].
            ****** apply in_plus_fold. destruct (eq_event_dec x' e).
              ******* apply in_map_iff in P4 as [c'' [P5 P6]].
                      exists c''. rewrite e0 in P6. rewrite <- P5 in P2.
                      apply -> reduce_success_comp in P2.  split ; try assumption.
              ******* apply in_map_iff in P4 as [c'' [P5 P6]]. rewrite <- P5 in P2.
                      inversion P2. inversion H0.
Qed.
 

Lemma or_times_derivative: forall (c0 c1 : Contract)(e : EventType)(s : Trace), 
s ==~ plus_fold ((times ((norm c0) / e) (norm c1))) \/ s==~ plus_fold (times (norm c0) ((norm c1) / e))
-> s ==~ (plus_fold (times c0 c1)) / e.
Proof.
intros. simp times. destruct (eq_contract_dec (norm c0) Failure).
  * rewrite e0 in H. simp times in H. simpl in H. destruct H ; inversion H.
  * destruct (eq_contract_dec (norm c1) Failure). 
    ** rewrite e0 in H.  simp times in H.
       destruct (eq_contract_dec (norm (norm c0 / e)) Failure). 
      *** destruct H.
        **** simpl in H. inversion H.
        **** destruct (eq_contract_dec (norm (norm c0)) Failure). 
          ***** simpl in H.  inversion H. 
          ***** destruct (eq_contract_dec (norm (Failure / e)) Failure). 
            ******  simpl in H.  inversion H. 
            ****** contradiction. 
      *** destruct (eq_contract_dec (norm Failure) Failure).
          destruct H. simpl in H ; inversion H.
          destruct (eq_contract_dec (norm (norm c0)) Failure).
          simpl in H. inversion H.
          destruct (eq_contract_dec (norm (Failure / e)) Failure).
        **** simpl in H. inversion H. 
        **** destruct (eq_contract_dec (norm (norm c0)) Success).
             simpl in H. inversion H. inversion H2. inversion H1.
             destruct (eq_contract_dec (norm (Failure / e)) Success). contradiction. contradiction.
        **** contradiction.
    ** destruct (eq_contract_dec (norm c0) Success). 
      *** rewrite e0 in H. simpl in H. destruct H.
        **** inversion H.
        **** simp times in H. simpl in H.
             destruct (eq_contract_dec (norm (norm c1 / e)) Failure).
          ***** simpl in H. inversion H.
          ***** simpl in H. inversion H. 
            ****** simpl. apply MPlusL.  apply match_closed_norm in H2. auto.
            ****** inversion H1.
      *** destruct (eq_contract_dec (norm c1) Success).
        **** rewrite e0 in H. simp times in H. simpl in H.  
          ***** destruct (eq_contract_dec (norm (norm c0 / e)) Failure).
            ****** destruct H.
              ******* simpl in H. inversion H.
              ******* destruct (eq_contract_dec (norm (norm c0)) Failure ) ; simpl in H ; inversion H.
           ****** destruct H. 
              ******* destruct (eq_contract_dec (norm (norm c0 / e)) Success). 
                ******** simpl in H. inversion H.
                  ********* inversion H2. simpl. apply MPlusL. apply match_closed_norm. rewrite e1.
                            auto.
                  ********* inversion H1.
                ******** simpl in *. inversion H. { apply MPlusL. apply match_closed_norm. apply H2. } inversion H1.
              ******* destruct (eq_contract_dec (norm (norm c0)) Failure); simpl in H; inversion H.
          **** rewrite list_derivative_spec. rewrite list_derivative_app.
             apply plus_fold_app. destruct H. 
            ***** apply MPlusL. rewrite inline_derivative_l. 
                  apply in_plus_fold. apply in_plus_fold in H as [c' [P1 P2]].
                  exists (Success _;_ c'). split. 2: { apply reduce_success_comp. assumption. }
                  apply in_flat_map. exists e. split. { apply all_in_alpabet. }
                  apply in_map_iff. exists c'. 
                  destruct (eq_event_dec e e) ; auto || auto. contradiction n3. reflexivity.
            ***** apply MPlusR. rewrite inline_derivative_r. 
                  apply in_plus_fold. apply in_plus_fold in H as [c' [P1 P2]].
                  exists (Success _;_ c'). split. 2: { apply reduce_success_comp. assumption. }
                  apply in_flat_map. exists e. split. { apply all_in_alpabet. }
                  apply in_map_iff. exists c'. 
                  destruct (eq_event_dec e e) ; auto || auto. contradiction n3. reflexivity.
Qed.


Lemma plus_fold_empty_success : forall (c0 c1 : Contract), [] ==~ plus_fold (times c0 c1)
 -> [] ==~ norm c0 /\ [] ==~ norm c1.
Proof.
intros. funelim (times c0 c1).
  destruct (eq_contract_dec (norm c0) Failure).
  * rewrite <- Heqcall in H1. simpl in H1. inversion H1.
  * destruct (eq_contract_dec (norm c1) Failure) eqn:Heqn1.
    ** rewrite <- Heqcall in H1. simpl in H1. inversion H1.
    ** destruct (eq_contract_dec (norm c0) Success).
      *** simp times in H1. rewrite e in H1.
          simpl in H1. rewrite Heqn1 in H1. simpl in H1. apply plus_failure in H1.
          rewrite e. split. { constructor. } { assumption. }
      *** destruct (eq_contract_dec (norm c1) Success).
        **** rewrite e. rewrite <- Heqcall in H1. simpl in H1. apply plus_failure in H1.
             split. assumption. constructor.
        **** rewrite <- Heqcall in H1.
             apply plus_fold_app in H1. apply plus_or in H1 as [H1 | H1];
             apply in_plus_fold in H1 as [c' [P1 P2]]; apply in_flat_map in P1 as [x' [P3 P4]];
             apply in_map_iff in P4 as [e' [P5 P6]]; rewrite <- P5 in P2;
             inversion P2; apply app_eq_nil in H1 as [H6 H7]; rewrite H6 in H4; inversion H4.
Qed.


Lemma times_par : forall (s : Trace)(c1 c2 : Contract) , s ==~ plus_fold (times c1 c2) <-> exists (s1 s2 : Trace), 
interleave s1 s2 s /\ s1 ==~ c1 /\ s2 ==~ c2.
Proof.
split.
- generalize dependent c2. generalize dependent c1. induction s.
  * intros. exists []. exists []. split. constructor. apply plus_fold_empty_success in H as [H1 H2].
    subst ; split ; apply match_closed_norm; assumption. 
  * intros. apply derive_spec_comp in H. apply times_derivative_or in H as [H | H].
    ** specialize IHs with (c1:=norm c1 / a)(c2:=norm c2). apply IHs in H as [s1' [s2' [P1 [P2 P3]]]].
      exists (a :: s1'). exists s2'. split.
      *** try (constructor ; assumption).
      *** split. { apply match_closed_norm. apply derive_spec_comp. assumption. } { apply match_closed_norm in P3. assumption.  }
    ** specialize IHs with (c1:=norm c1)(c2:=norm c2 / a). apply IHs in H as [s1' [s2' [P1 [P2 P3]]]].
       exists s1'. exists (a::s2'). split.
      *** try (constructor ; assumption).
      *** split. { apply match_closed_norm. assumption. } { apply match_closed_norm . apply derive_spec_comp. assumption.  }
- generalize dependent c2. generalize dependent c1. induction s.
  * intros. destruct H as [s1 [s2 [P1 [P2 P3]]]]. apply plus_fold_empty_success. inversion P1.
    ** rewrite <- H in P2. rewrite H1 in P3. split; apply -> match_closed_norm; assumption.
    ** rewrite <- H0 in P3. rewrite H1 in P2. apply plus_fold_empty_success.
       apply plus_fold_empty_success. split; apply -> match_closed_norm ; assumption.
  * intros. destruct H as [s1 [s2 [P1 [P2 P3]]]]. apply derive_spec_comp. inversion P1.
    ** apply or_times_derivative. right. apply IHs. inversion H1. exists []. exists s.
       split. { constructor. } { split. { rewrite <- H in P2. apply -> match_closed_norm. assumption. }
                                        { rewrite H1 in P3. apply derive_spec_comp. apply -> match_closed_norm. assumption. } }
    ** apply or_times_derivative. left. apply IHs. exists s. exists [].
       split. { constructor. } { split. { rewrite H1 in P2. apply derive_spec_comp. apply -> match_closed_norm. assumption. }
                                        { rewrite <- H0 in P3. apply -> match_closed_norm. assumption. } }
    ** apply or_times_derivative. left. apply IHs. exists t1. exists s2.
       split. { assumption. } { split. { rewrite <- H0 in P2. apply derive_spec_comp. apply -> match_closed_norm. rewrite <- H. assumption. }
                                        { apply -> match_closed_norm. assumption. } }
    ** apply or_times_derivative. right. apply IHs. inversion H1. exists s1. exists t2.
       split. { assumption. } { split. { apply -> match_closed_norm. assumption. }
                                        { apply derive_spec_comp. rewrite <- H. rewrite H4. apply -> match_closed_norm. assumption. } }
Qed.




Lemma matches_pmatches : forall (p : PContract), (forall (s : Trace), s ==~ (trans p) -> s p==~ p).
Proof. induction p.
- intros s H. simpl in H. inversion H. apply MPSuccess.
- intros s H. simpl in H. inversion H.
- intros s H. simpl in H. inversion H. apply MPEvent.
- intros s H. simpl in H. inversion H.
  * apply MPPlusL. apply IHp1. apply H2.
  * apply MPPlusR. apply IHp2. apply H1.
- intros s H. simpl in H. apply times_par in H. destruct H as [s1 [s2 [P1 [P2 P3]]]].
  * apply MPPar with (s1:=s1)(s2:=s2). { apply (IHp1 _ P2). } { apply (IHp2 _ P3). } { apply P1. }
Qed.

Lemma pmatches_matches : forall (p : PContract), (forall (s : Trace), s p==~ p -> s ==~ (trans p)).
Proof.
intros. induction H.
- constructor.
- constructor.
- simpl. apply times_par. exists s1. exists s2. split ; try split ; assumption.
- simpl. apply MPlusL. assumption.
- simpl. apply MPlusR. assumption.
Qed.

