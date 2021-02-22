Require Import Lists.List.
Require Import Bool.Bool.
Require Import Program.
Require Import Arith.PeanoNat.
Require Import Structures.GenericMinMax.
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

Definition is_failure (c : Contract) :=
match c with
| Failure => true
| _ => false
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
| c0 _+_ c1 => let c0' := (derive e c0)  (*Expressed like this to ensure size decrease*)
               in let c1' := (derive e c1) 
                  in if (is_failure c0')
                        then c1' 
                        else c0' _+_ c1'
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
Theorem derivation : forall (e:EventType)(s:Trace)(c:Contract),
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


Lemma is_failure_failure : forall c0 : Contract, is_failure c0 = true -> c0 = Failure.
Proof.
intros c0 H. induction c0.
- discriminate H.
- reflexivity.
- discriminate H.
- discriminate H.
- discriminate H.
Qed.

(*No trace can be derived from Failure*)
Lemma failure_false : forall (s : Trace), (s =~ Failure) = false.
Proof. induction s.
- simpl. reflexivity.
- simpl. apply IHs.
Qed.

Lemma remove_failure : forall (s : Trace)(c : Contract), s =~ (Failure _+_ c) = true -> s =~ c = true.
Proof. induction s.
- intros c H. simpl. simpl in H. apply H.
- intros c H. simpl in H. simpl. apply H.
Qed.

Lemma add_failure : forall (s : Trace)(c : Contract), s =~ c = true -> s =~ (Failure _+_ c) = true .
Proof. induction s.
- intros c H. simpl. simpl in H. apply H.
- intros c H. simpl. simpl in H. apply H. 
Qed.

(*Helper lemma reflecting change in derive function*)
Lemma plus_if : forall (s : Trace)(c0 c1 : Contract), 
s =~ (c0 _+_ c1) = true -> s =~ (if is_failure c0 then c1 else (c0 _+_ c1)) = true.
Proof.
intros s c0. generalize dependent s. induction c0.
- intros s c1 H. simpl. apply H.
- intros s c1 H. simpl. apply remove_failure in H. apply H.
- intros s c1 H. simpl. apply H.
- intros s c1 H. simpl. apply H.
- intros s c1 H. simpl. apply H.
Qed. 


(*Helper lemma reflecting change in derive function*)
Lemma if_plus : forall (s : Trace)(c0 c1 : Contract), 
s =~ (if is_failure c0 then c1 else (c0 _+_ c1)) = true -> s =~ (c0 _+_ c1) = true.
Proof.
intros s c0. generalize dependent s. induction c0.
- intros s c1 H. simpl in H. apply H.
- intros s c1 H. simpl in H. apply add_failure. apply H.
- intros s c1 H. simpl in H. apply H.
- intros s c1 H. simpl in H. apply H.
- intros s c1 H. simpl in H. apply H.
Qed. 

Lemma failure_or_not : forall (c : Contract), c = Failure \/ c <> Failure.
Proof.
induction c.
- right. unfold not. intro H. discriminate.
- left. reflexivity.
- right. unfold not. intro H. discriminate.
- right. unfold not. intro H. discriminate.
- right. unfold not. intro H. discriminate.
Qed.

(*If s matches c, it also matches c _+_ any contract*)
Lemma plus_left_oper : forall (s : Trace)(l r : Contract), s =~ l = true -> s =~ (l _+_ r) = true.
Proof. intros s. induction s as [| n s' IHs'].
- intros l r H. simpl in H. simpl. rewrite H. rewrite orb_true_l. reflexivity.
- simpl. intros l r H. apply plus_if. apply IHs'. apply H.
Qed. 

(*_+_ is commutative*)
Lemma plus_comm_oper : forall (s : Trace)(l r : Contract), s =~ (l _+_ r) = true -> s =~ (r _+_ l) = true.
Proof. induction s as [| e s' IHs'].
- simpl. intros l r H. rewrite orb_comm. apply H.
- intros l r H. simpl. apply plus_if. apply IHs'. simpl in H. apply if_plus. apply H.
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
  * apply IHmatches_comp1.
  * apply IHmatches_comp2.   
- apply plus_left_oper. apply IHmatches_comp.  (*MPlusL*)
- apply plus_right_oper. apply IHmatches_comp. (*MPlusR*)
Qed.

(*If s matches c1 _+_ c2, then it matches c1 or c2*)
Lemma plus_or_oper : forall (s : Trace)(c1 c2 : Contract), (s =~ (c1 _+_ c2)) = true -> 
               (s =~ c1) = true \/ (s =~ c2) = true.
Proof. induction s.
- intros c1 c2 H. simpl. simpl in H. apply orb_prop in H. apply H.
- intros c1 c2 H. simpl. apply IHs. simpl in H. apply if_plus in H. apply H.
Qed.

(*Only the empty trace can be derived from Success*)
Lemma success_empty : forall (s : Trace), (s =~ Success) = true -> s = [].
Proof. induction s.
- intro H. reflexivity.
- simpl. rewrite failure_false. intro H. discriminate.
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
Inductive interleave : Trace -> Trace -> Trace -> Prop :=
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
| c0 _;_ c1 => (con_size c0) + (con_size c1)
| c0 _+_ c1 => max (con_size c0) (con_size c1)
end.


Inductive reducible : Contract -> Prop :=
| RSuccess : reducible Success
| REvent x : reducible (Event x)
| RPlusL c0 c1 
            (H : reducible c0)
           : reducible (c0 _+_ c1)
| RPlusR c0 c1 
            (H : reducible c1)
           : reducible (c0 _+_ c1)
| RPlusLF c : reducible (Failure _+_ c)
| RPlusRF c : reducible (c _+_ Failure)
| RSeq c0 c1 : reducible (c0 _;_ c1).

Lemma reducible_size : forall (c : Contract), reducible c -> con_size c > con_size Failure.
Proof. Admitted.

Lemma size_reducible : forall (c : Contract), con_size c > con_size Failure -> reducible c.
Proof. Admitted.


Lemma can_reduce : forall (c : Contract), reducible c -> (forall (e : EventType), con_size (c / e) < con_size c).
Proof. intros c H. induction H.
- intuition.
- intuition. simpl. destruct (eq_event x e). { intuition. } { intuition. }
- intro e. simpl. destruct (is_failure (c0 / e)).
  * apply reducible_size in H as H2. apply Nat.max_case_strong.
    ** intro H3. simpl in H2. unfold gt. Abort. symmetry in H2. apply Nat.max_lt_iff. transitivity (con_size c1).
    **
    Abort.

Lemma not_failure_imp_reduce : forall (c : Contract), Failure <> c -> reducible c.
Proof. induction c.
- intro H. simpl. apply RSuccess.
- contradiction.
- intro H. simpl. apply REvent.
- intro H. destruct (failure_or_not c1).
  * rewrite H0. apply RPlusLF.
  * assert (H': Failure <> c1). { unfold not in *. intro H2. apply H0. symmetry. apply H2. } 
    apply IHc1 in H'. apply (RPlusL c1 c2 H').
- intro H. apply RSeq.
Qed.


Lemma dec : forall (c : Contract), Failure <> c -> (forall (e : EventType), con_size (c / e) < con_size c).
Proof. intros c H e. apply not_failure_imp_reduce in H. apply can_reduce. apply H.
Qed.

Lemma wildcard_right : forall c0 c1, (forall wildcard' : Contract,
        ~ (wildcard' = c0 /\ Failure = c1) ) -> Failure <> c1.
Proof. Admitted.

Lemma wildcard_left : forall c0 c1, (forall wildcard' : Contract,
        ~ (Failure = c1 /\ wildcard' = c0) ) -> Failure <> c1.
Proof. Admitted.

Search (?a + ?b <= ?c + ?b).

Program Fixpoint times (c0 c1 : Contract) {measure ((con_size c0) + (con_size c1))} : Contract :=
match c0,c1 with
| Failure,_ => Failure
| _, Failure => Failure
| _,_ => (times ((c0 / Transfer)) c1) _+_ (times c0 ((c1 / Transfer)) )   _+_
       (times ((c0 / Notify))   c1) _+_ (times c0 ((c1 / Notify)) )
end.
Next Obligation.  
apply Plus.plus_lt_compat_r. 
apply wildcard_left in H0. apply dec with (e := Transfer) in H0. apply H0.
Qed. 
Next Obligation.
apply Plus.plus_lt_compat_l. 
apply wildcard_right in H. apply dec with (e := Transfer) in H. apply H.
Qed. 
Next Obligation.
apply Plus.plus_lt_compat_r. 
apply wildcard_left in H0. apply dec with (e := Notify) in H0. apply H0.
Qed.
Next Obligation.
apply Plus.plus_lt_compat_l. 
apply wildcard_right in H. apply dec with (e := Notify) in H. apply H.
Qed.
Next Obligation.
split.
  - intuition. discriminate H1.
  - intuition. discriminate H0.
Qed.
Next Obligation.
split.
  - intuition. discriminate H2.
  - intuition. discriminate H1.
Qed.
Next Obligation.
split.
  - intuition. discriminate H3.
  - intuition. discriminate H2.
Qed.
Next Obligation.
split.
  - intuition. discriminate H3.
  - intuition. discriminate H2.
Qed.
Next Obligation.
split.
  - intuition. discriminate H2.
  - intuition. discriminate H1.
Qed.
Next Obligation.
split.
  - intuition. discriminate H3.
  - intuition. discriminate H2.
Qed.
Next Obligation.
split.
  - intuition. discriminate H4.
  - intuition. discriminate H3.
Qed.
Next Obligation.
split.
  - intuition. discriminate H4.
  - intuition. discriminate H3.
Qed.
Next Obligation.
split.
  - intuition. discriminate H3.
  - intuition. discriminate H2.
Qed.
Next Obligation.
split.
  - intuition. discriminate H4.
  - intuition. discriminate H3.
Qed.
Next Obligation.
split.
  - intuition. discriminate H5.
  - intuition. discriminate H4.
Qed.
Next Obligation.
split.
  - intuition. discriminate H5.
  - intuition. discriminate H4.
Qed.
Next Obligation.
split.
  - intuition. discriminate H3.
  - intuition. discriminate H2.
Qed.
Next Obligation.
split.
  - intuition. discriminate H4.
  - intuition. discriminate H3.
Qed.
Next Obligation.
split.
  - intuition. discriminate H5.
  - intuition. discriminate H4.
Qed.
Next Obligation.
split.
  - intuition. discriminate H5.
  - intuition. discriminate H4.
Qed.



Fixpoint trans (p : PContract) : Contract :=
match p with
| PSuccess => Success
| PFailure => Failure
| PEvent e => Event e
| p0 -*- p1 => times (trans p0) (trans p1)
| p0 -+- p1 => (trans p0) _+_ (trans p1)
end.



Lemma pmatches_matches : forall (p : PContract), (forall (s : Trace), s p==~ p <-> s ==~ (trans p)).
Proof. Admitted.

