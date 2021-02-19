Require Import Lists.List.
Require Import Bool.Bool.
Import ListNotations.
Require Export Setoid.
Require Export Relation_Definitions.

Inductive EventType : Type :=
| Transfer : EventType
| Notify : EventType.

Definition eq_event (e1:EventType)(e2:EventType):bool :=
match e1,e2 with
| Transfer,Transfer => true
| Notify, Notify => true
| _ , _ => false
end.

Lemma eq_event_refl : forall e, eq_event e e = true.
Proof. destruct e.
- reflexivity.
- reflexivity.
Qed.

Lemma eq_event_equals : forall (e1 e2 : EventType), (eq_event e1 e2) = true -> e1 = e2.
Proof. intros e1 e2 H. destruct e1.
  - simpl in H. destruct e2.
    * reflexivity.
    * discriminate.
  - simpl in H. destruct e2.
    * discriminate.
    * reflexivity.
Qed.

Lemma equals_eq_event : forall (e1 e2 : EventType), e1 = e2 -> (eq_event e1 e2) = true.
Proof. intros e1 e2 H. inversion H. apply eq_event_refl.
Qed.

Lemma eq_event_iff_eq : forall (e1 e2 : EventType), (eq_event e1 e2) = true <-> e1 = e2.
Proof. split.
- apply eq_event_equals.
- apply equals_eq_event.
Qed.

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H :   P) : reflect P true
| ReflectF (H : ~ P) : reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
intros P b H. inversion H.
- split.
  * intro H2. reflexivity.
  * intro H2. apply H0.
- split. intros H2. inversion H. rewrite <- H1 in H4. discriminate H4.
  destruct b.
  * discriminate.
  * exfalso. unfold not in H3. apply H3 in H2. apply H2.
  * intro H3. discriminate.
Qed.

Lemma eq_event_prop : forall n m, reflect (n = m) (eq_event n m).
Proof.
  intros n m. apply iff_reflect. split.
- apply eq_event_iff_eq.
- apply eq_event_iff_eq.
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
| Event e1 => if eq_event e1 e then Success else Failure
| c0 _;_ c1 => match nu c0 with
               | true => ((derive e c0) _;_ c1) _+_ (derive e c1)
               | false => (derive e c0) _;_ c1
               end
| c0 _+_ c1 => (derive e c0) _+_ (derive e c1)
end.


Notation "c / e" := (derive e c).

Fixpoint matches (c:Contract)(s:Trace):bool :=
match s with
| [] => nu c
| e::s' => matches (c / e) s'
end.

(*Expression*)
Notation "s =~ c" := (matches c s) (at level 62).

(*Propositions*)

Notation "s !=~ c" := (matches c s = false) (at level 62).

(** Relation between [matches] and [derive]. *)
Theorem derivation : forall (e:EventType)(s:Trace)(c:Contract),
  (e::s) =~ c  = s =~ c / e.
Proof. intros e s c. simpl. reflexivity.
Qed.

Reserved Notation "s ==~ re" (at level 60).

Inductive exp_match : Trace -> Contract -> Prop :=
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
  where "s ==~ c" := (exp_match s c).

(* eq_event x x *)
(*mseq at op level*)

(*If s matches c, it also matches c _+_ any contract*)
Lemma plus_left_oper : forall (s : Trace)(l r : Contract), s =~ l = true -> s =~ (l _+_ r) = true.
Proof. intros s. induction s as [| n s' IHs'].
- intros l r H. simpl in H. simpl. rewrite H. rewrite orb_true_l. reflexivity.
- simpl. intros l r H. apply IHs'. apply H.
Qed. 

(*_+_ is commutative*)
Lemma plus_comm_oper : forall (s : Trace)(l r : Contract), s =~ (l _+_ r) = true -> s =~ (r _+_ l) = true.
Proof. induction s as [| e s' IHs'].
- simpl. intros l r H. rewrite orb_comm. apply H.
- intros l r H. simpl. apply IHs'. simpl in H. apply H.
Qed.
 
(*If s matches c, it also matches any contract _+_ c*)
Lemma plus_right_oper : forall (s : Trace)(l r : Contract), s =~ r = true -> s =~ (l _+_ r) = true.
Proof. intros s l r H. apply plus_comm_oper. apply plus_left_oper. apply H.
Qed.

(*If s matches c2, it will still match after prefixing c2 with a nullary contract*)
Lemma seq_nu_left : forall (s : Trace)(c1 c2 : Contract), nu c1 = true -> (s =~c2 = true) 
                    -> (s =~ c1 _;_ c2 = true).
Proof. induction s as [| e s' IHs'].
- intros c1 c2 H1 H2. unfold matches. simpl. simpl in H2. apply andb_true_intro.
  split.
  * apply H1.
  * apply H2.
- intros c1 c2 H1 H2. simpl. rewrite H1. simpl in H2. apply plus_right_oper. apply H2.
Qed.

(*MSeq defined operationally*)
Lemma mseq_oper : forall (s1 s2 : Trace)(c1 c2 : Contract), s1 =~ c1 = true -> 
                      s2 =~ c2 = true -> ((s1 ++ s2) =~ c1 _;_ c2) = true.
Proof. induction s1 as [| e s1' IHs1'].
- simpl. intros s2 c1 c2 H1 H2. rewrite <- (app_nil_l s2).
  apply seq_nu_left.
  * apply H1.
  * simpl. apply H2.
- intros s2 c1 c2 H1 H2. simpl. destruct (nu c1).
  * simpl in H1. simpl in H1. rewrite <- (app_nil_l (s1' ++ s2)). apply plus_left_oper.
    simpl. apply IHs1'.
    ** apply H1.
    ** apply H2.
  * apply IHs1'.
    ** simpl in H1. apply H1.
    ** apply H2.
Qed. 

Lemma comp_imp_oper : forall (s : Trace)(c : Contract), s ==~ c -> (s =~ c) = true.
Proof. 
intros s c H. induction H.
- simpl. reflexivity. (*MSucces*)
- simpl. rewrite eq_event_refl. reflexivity. (*MChar*)
- apply mseq_oper. (*MSeq*)
  * apply IHexp_match1.
  * apply IHexp_match2.   
- apply plus_left_oper. apply IHexp_match.  (*MPlusL*)
- apply plus_right_oper. apply IHexp_match. (*MPlusR*)
Qed.

(*No trace can be derived from Failure*)
Lemma failure_false : forall (s : Trace), (s =~ Failure) = false.
Proof. induction s.
- simpl. reflexivity.
- simpl. apply IHs.
Qed.

(*Only the empty trace can be derived from Success*)
Lemma success_empty : forall (s : Trace), (s =~ Success) = true -> s = [].
Proof. induction s.
- intro H. reflexivity.
- simpl. rewrite failure_false. intro H. discriminate.
Qed.

(*If s matches c1 _+_ c2, then it matches c1 or c2*)
Lemma plus_or_oper : forall (s : Trace)(c1 c2 : Contract), (s =~ (c1 _+_ c2)) = true -> 
               (s =~ c1) = true \/ (s =~ c2) = true.
Proof. induction s.
- intros c1 c2 H. simpl. simpl in H. apply orb_prop in H. apply H.
- intros c1 c2 H. simpl. apply IHs. simpl in H. apply H.
Qed.


Definition exists_seq_decomp_def (s : Trace) (c1 c2 : Contract) : Prop := 
 s =~ c1 _;_ c2 = true ->
     exists s1 s2 : Trace, s = s1 ++ s2 /\ s1 =~ c1 = true /\ s2 =~ c2 = true.

(*To show e::s matching c1 _;_ c2 can be decomposed, it suffices to show 
  s matching c1/e ;_ c2 can be decomposed*)
Lemma mseq_oper_inv_helper : forall (s : Trace)(c1 c2 : Contract)(e : EventType), 
  (exists_seq_decomp_def s (c1 / e) c2) -> exists_seq_decomp_def (e :: s) c1 c2.
Proof.
unfold exists_seq_decomp_def. intros s c1 c2 e H1 H2. simpl in H2. destruct (nu c1) eqn:Heqn.
- apply plus_or_oper in H2 as H2. destruct H2 as [H2 | H2].
  * apply H1 in H2. destruct H2 as [s' [s'' [P1 [P2 P3]]]].
    exists (e::s'). exists s''. simpl. rewrite P1. split.
    ** reflexivity.
    ** split. 
      *** apply P2.
      *** apply P3.
  * exists []. exists (e::s). simpl. split.
    ** reflexivity.
    ** split. { apply Heqn. } { apply H2. }
- apply H1 in H2. destruct H2 as [s' [s'' [P1 [P2 P3]]]]. exists (e::s'). exists s''. split.
  * simpl. rewrite <- P1. reflexivity.
  * split.
    ** simpl. apply P2.
    ** apply P3.
Qed.




(*The inverse rule of MSeq given operationally*)
Lemma mseq_oper_inv : forall (s : Trace)(c1 c2 : Contract), 
       (s =~ c1 _;_ c2) = true -> (exists (s1 s2 : Trace), s = s1++s2 /\ (s1 =~ c1) = true /\ (s2 =~ c2) = true ).
Proof. induction s.
- intros c1 c2 H. exists []. exists []. simpl. simpl in H. apply andb_prop in H as [H1 H2].
  rewrite H1. rewrite H2. split.
  * reflexivity.
  * split.
    ** reflexivity.
    ** reflexivity.
- intros c1 c2 H. apply mseq_oper_inv_helper.
  * unfold exists_seq_decomp_def. intros H2. apply IHs. apply H2.
  * apply H.
Qed.

Lemma oper_imp_comp : forall (s : Trace)(c : Contract), (s =~ c) = true -> s ==~ c.
Proof.
intros s c. generalize dependent s. induction c.
- intros s H. destruct s. (*Success*)
  * apply MSuccess.
  * inversion H. rewrite failure_false in H1. discriminate H1.
- intros s H. rewrite failure_false in H. discriminate H. (*Failure*)
- intros s H. destruct s eqn:Heqn. (*Event e*)
  * inversion H.
  * simpl in H. destruct (eq_event_prop e e0). (*reflection*)
    ** apply success_empty in H. rewrite H0. rewrite H. apply MEvent.
    ** rewrite failure_false in H. discriminate H.
- intros s H. apply plus_or_oper in H. destruct H. (*c1 _+_ c2*)
  * apply MPlusL. apply IHc1. apply H.
  * apply MPlusR. apply IHc2. apply H.
- intros s H. apply mseq_oper_inv in H as [s' [s'' [P1 [P2 P3]]]]. (*c1 _;_ c2*)
  rewrite P1. apply MSeq.
  * apply (IHc1 s' P2).
  * apply (IHc2 s'' P3). 
Qed.

Lemma comp_iff_oper : forall (s : Trace)(c : Contract), s ==~ c <-> (s =~ c) = true.
Proof.
split.
- (*->*) apply comp_imp_oper.
- (*<-*) apply oper_imp_comp.
Qed.

(*the boolean value s =~ c is reflected in the proposition s ==~ c *)
Lemma matches_prop : forall (s : Trace) (c : Contract), reflect (s ==~ c) (s =~ c).
Proof.
  intros n m. apply iff_reflect. split.
- apply comp_iff_oper.
- apply comp_iff_oper.
Qed.


Definition c_eq (c c':Contract) : Prop := forall s, s ==~ c <-> s ==~ c'.
Notation "a =R= b" := (c_eq a b) (at level 70).

Definition c_le (c c':Contract) : Prop := forall s, s ==~ c -> s ==~ c'.
Notation "a <R= b" := (c_le a b) (at level 70).

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



Lemma plus_comm_le : forall (c1 c2 : Contract), (c1 _+_ c2) <R= (c2 _+_ c1).
Proof.
- intros c1 c2 s H. inversion H.
  * apply MPlusR. apply H2.
  * apply MPlusL. apply H1.
Qed. 

Lemma plus_comm : forall (c1 c2 : Contract), (c1 _+_ c2) =R= (c2 _+_ c1).
Proof.
split.
- apply plus_comm_le.
- apply plus_comm_le.
Qed.

Lemma plus_assoc : forall (c1 c2 c3 : Contract), ((c1 _+_ c2) _+_ c3) =R= (c1 _+_ (c2 _+_ c3)).
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

Search (_ ++ _ = _).

Lemma seq_assoc : forall (c1 c2 c3 : Contract), ((c1 _;_ c2) _;_ c3) =R= (c1 _;_ (c2 _;_ c3)).
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

Lemma plus_or : forall (s : Trace)(c1 c2 : Contract), s ==~ (c1 _+_ c2) -> s ==~ c1 \/ s ==~c2.
Proof. 
intros s c1 c2 H. repeat rewrite comp_iff_oper in *.
apply plus_or_oper in H. apply H.
Qed.


Lemma plus_distr : forall (c1 c2 c3 : Contract), (c1 _;_ (c2 _+_ c3)) =R= (c1 _;_ c2) _+_ (c1 _;_ c3).
Proof. split.
- intro H. inversion H. inversion H4.
  * apply MPlusL. apply MSeq. { apply H3. } { apply H7. }
  * apply MPlusR. apply MSeq. { apply H3. } { apply H7. }
- intro H. apply plus_or in H as [H | H].
  * inversion H. apply MSeq.
    ** apply H3.
    ** apply MPlusL. apply H4.
  * inversion H. apply MSeq.
    ** apply H3.
    ** apply MPlusR. apply H4.
Qed.

Lemma plus_distr2 : forall (c1 c2 c3 : Contract), ((c1 _+_ c2) _;_ c3) =R= (c1 _;_ c3) _+_ (c2 _;_ c3).
Proof. split.
- intros H. inversion H. inversion H3.
  * apply MPlusL. apply MSeq. { apply H7. } { apply H4. }
  * apply MPlusR. apply MSeq. { apply H7. } { apply H4. }
- intros H. inversion H.
  * inversion H2. apply MSeq. { apply MPlusL. apply H7. } { apply H8. }
  * inversion H1. apply MSeq. { apply MPlusR. apply H7. } { apply H8. }
Qed.


