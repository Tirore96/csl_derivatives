Require Import Lists.List.
Require Import Bool.Bool.
Require Import Bool.Sumbool.
Require Import Program.
From Equations Require Import Equations.
Require Import micromega.Lia.
Require Import Arith.
Import ListNotations.

Require CSL.Contract.

Module CSLC := CSL.Contract.

Definition Trace := CSLC.Trace.
Definition EventType := CSLC.EventType.
Definition eq_event_dec := CSLC.eq_event_dec.
Definition alphabet := CSLC.alphabet.
Definition Transfer := CSLC.Transfer.
Definition Notify := CSLC.Notify.
Set Implicit Arguments.



(*Parallel contracts section*)
Inductive Contract : Set :=
| Success : Contract
| Failure : Contract
| Event : CSLC.EventType -> Contract
| Plus : Contract -> Contract -> Contract
| Seq : Contract -> Contract -> Contract
| Par : Contract -> Contract -> Contract.

Notation "e _._ c" := (Seq (Event e) c)
                    (at level 41, right associativity).

Notation "c0 _*_ c1"  := (Par c0 c1)
                         (at level 50, left associativity).

Notation "c0 _;_ c1"  := (Seq c0 c1)
                         (at level 50, left associativity).

Notation "c0 _+_ c1"  := (Plus c0 c1)
                         (at level 61, left associativity).

(*For a nullary contract c, nu c = true*)
Fixpoint nu(c:Contract):bool :=
match c with
| Success => true
| Failure => false
| Event e => false
| c0 _;_ c1 => nu c0 && nu c1
| c0 _*_ c1 => nu c0 && nu c1
| c0 _+_ c1 => nu c0 || nu c1
end.


(*Derivative of contract with respect to an event*)
Fixpoint derive(e:EventType)(c:Contract):Contract :=
match c with
| Success => Failure
| Failure => Failure
| Event e1 => if eq_event_dec e1 e then Success else Failure
| c0 _;_ c1 => if nu c0 then (derive e c0) _;_ c1 _+_ (derive e c1)
                        else (derive e c0) _;_ c1
| c0 _*_ c1 => (derive e c0) _*_ c1 _+_ c0 _*_ (derive e c1)
| c0 _+_ c1 => (derive e c0) _+_ (derive e c1) 
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

(*Taken from csl-formalization*)
Inductive interleave (A : Set) : list A -> list A -> list A -> Prop :=
| IntLeftNil  : forall t, interleave nil t t
| IntRightNil : forall t, interleave t nil t
| IntLeftCons : forall t1 t2 t3 e, interleave t1 t2 t3 -> interleave (e :: t1) t2 (e :: t3)
| IntRightCons : forall t1 t2 t3 e, interleave t1 t2 t3 -> interleave t1 (e :: t2) (e :: t3).
Hint Constructors interleave : core.

Reserved Notation "s ==~ re" (at level 63).

Inductive pmatches_comp : Trace -> Contract -> Prop :=
  | MSuccess : [] ==~ Success
  | MEvent x : [x] ==~ (Event x)
  | MSeq s1 c1 s2 c2
             (H1 : s1 ==~ c1)
             (H2 : s2 ==~ c2)
           : (s1 ++ s2) ==~ (c1 _;_ c2)
  | MPar s1 c1 s2 c2 s
             (H1 : s1 ==~ c1)
             (H2 : s2 ==~ c2)
             (H3 : interleave s1 s2 s)
           : s ==~ (c1 _*_ c2)
  | MPlusL s1 c1 c2
                (H1 : s1 ==~ c1)
              : s1 ==~ (c1 _+_ c2)
  | MPlusR c1 s2 c2
                (H2 : s2 ==~ c2)
              : s2 ==~ (c1 _+_ c2)
  where "s ==~ c" := (pmatches_comp s c).

Hint Constructors pmatches_comp : core.

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

Lemma mseq_oper : forall (s1 s2 : Trace)(c1 c2 : Contract), s1 =~ c1 = true -> 
                      s2 =~ c2 = true -> ((s1 ++ s2) =~ c1 _;_ c2) = true.
Proof. 
induction s1.
- simpl. intros. destruct s2.
  * unfold matches. simpl in *. rewrite H. rewrite H0. auto.
  * simpl. rewrite H. simpl in H0. rewrite plus_right_oper; try reflexivity. assumption.
- intros. simpl. destruct (nu c1).
  * simpl in H. apply plus_left_oper. auto.
  * auto.
Qed. 

Lemma mpar_oper : forall (s1 s2 s: Trace)(c1 c2 : Contract), s1 =~ c1 = true -> 
                      s2 =~ c2 = true -> interleave s1 s2 s -> s =~ c1 _*_ c2 = true.
Proof. 
induction s1; intros.
- generalize dependent s. generalize dependent c2. induction s2;intros.
  * inversion H1;subst ; simpl in *; rewrite H; rewrite H0; reflexivity.
  * inversion H1;simpl; rewrite plus_right_oper; try reflexivity; apply IHs2; auto; constructor.
- generalize dependent s. generalize dependent c2. induction s2;intros.
  * inversion H1; subst ; simpl in *; apply plus_left_oper; apply IHs1 with []; auto; constructor.
  * inversion H1;subst.
    ** simpl. rewrite plus_left_oper; try reflexivity. apply IHs1 with (a0::s2);auto.
    ** simpl. rewrite plus_right_oper; try reflexivity. simpl in H0. apply IHs2;auto.
Qed.


Lemma comp_oper : forall (s : Trace)(c : Contract), s ==~ c -> (s =~ c) = true.
Proof.
intros. induction H.
- reflexivity.
- simpl. destruct (eq_event_dec x x). reflexivity. exfalso. now apply n.
- auto using mseq_oper.
- eauto using mpar_oper.
- auto using plus_left_oper.
- auto using plus_right_oper. 
Qed.

Lemma failure_false : forall (s : Trace), (s =~ Failure) = false.
Proof. induction s.
- simpl. reflexivity.
- simpl. apply IHs.
Qed.

Lemma plus_or_oper : forall (s : Trace)(c1 c2 : Contract), (s =~ (c1 _+_ c2)) = true -> 
               (s =~ c1) = true \/ (s =~ c2) = true.
Proof. induction s ; simpl ; intros ; auto using orb_prop.
Qed.

Definition exists_seq_decomp (s : Trace) (c1 c2 : Contract) : Prop := 
 s =~ c1 _;_ c2 = true ->
     exists s1 s2 : Trace, s = s1 ++ s2 /\ s1 =~ c1 = true /\ s2 =~ c2 = true.
Hint Unfold exists_seq_decomp : core.

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

Ltac rwd_ff_d H := rewrite failure_false in H;discriminate.

Lemma success_empty : forall (s : Trace), (s =~ Success) = true -> s = [].
Proof. induction s.
- intro. reflexivity.
- simpl. rewrite failure_false. intro H. discriminate.
Qed.

(*The inverse rule of MSeq given operationally*)
Lemma mpar_oper_inv : forall (s : Trace)(c1 c2 : Contract), 
       (s =~ c1 _*_ c2) = true -> (exists (s1 s2 : Trace), interleave s1 s2 s /\ (s1 =~ c1) = true /\ (s2 =~ c2) = true ).
Proof.
induction s.
- intros. exists []. exists []. split. auto. simpl in H. apply andb_prop in H as [H1 H2]. split; auto.
- intros. simpl in H. apply plus_or_oper in H as [H | H];apply IHs in H as [s1 [s2 [P1 [P2 P3]]]].
  * exists (a::s1). exists s2. split. constructor. assumption. split;auto.
  * exists (s1). exists (a::s2). split. constructor. assumption. split;auto.
Qed.

Lemma oper_comp : forall (s : Trace)(c : Contract), (s =~ c) = true -> s ==~ c.
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
- intros. apply mpar_oper_inv in H as [s1 [s2 [P1 [P2 P3]]]]. eauto. 
Qed.

Lemma comp_iff_oper : forall (s : Trace)(c : Contract), s ==~ c <-> (s =~ c) = true.
Proof.
split.
- (*->*) apply comp_oper.
- (*<-*) apply oper_comp.
Qed.

Lemma matches_reflect : forall (s : Trace) (c : Contract), reflect (s ==~ c) (s =~ c).
Proof.
  intros n m. destruct (n =~ m) eqn:Heqn.
  - apply ReflectT. apply oper_comp. assumption. 
  - apply ReflectF. intro H. apply comp_oper in H. rewrite Heqn in H. inversion H.
Qed.

Lemma derive_spec_comp : forall (c : Contract)(e : EventType)(s : Trace), e::s ==~ c <-> s ==~ c / e.
Proof.
split ; repeat rewrite comp_iff_oper ; intro H ; rewrite <- H ; apply derive_spec.
Qed.


(**************Contract unfolding**************)

Inductive Stuck : Contract -> Prop :=
 | STFailure : Stuck Failure
 | STPLus c0 c1 (H0 : Stuck c0) (H1 : Stuck c1) : Stuck (c0 _+_ c1)
 | STSeq c0 c1 (H0 : Stuck c0) : Stuck (c0 _;_ c1)
 | STParL c0 c1 (H0 : Stuck c0) : Stuck (c0 _*_ c1)
 | STParR c0 c1 (H1 : Stuck c1) : Stuck (c0 _*_ c1).
Hint Constructors Stuck : core.

Inductive NotStuck : Contract -> Prop :=
 | NSTSuccess : NotStuck Success
 | NSEvent e : NotStuck (Event e)
 | NSTPlusL c0 c1 (H0 : NotStuck c0) : NotStuck (c0 _+_ c1)
 | NSTPlusR c0 c1 (H1 : NotStuck c1) : NotStuck (c0 _+_ c1)
 | NSTSeq c0 c1 (H0 : NotStuck c0) : NotStuck (c0 _;_ c1)
 | NSTPar c0 c1 (H0 : NotStuck c0)(H1 : NotStuck c1) : NotStuck (c0 _*_ c1).

Hint Constructors NotStuck : core.

Fixpoint stuck (c : Contract) :=
match c with
| Failure => true
| c0 _+_ c1 => stuck c0 && stuck c1
| c0 _;_ _ => stuck c0
| c0 _*_ c1 => stuck c0 || stuck c1
| _ => false
end.



Lemma stuck_false : forall (c : Contract), stuck c = false -> NotStuck c.
Proof.
induction c; intros.
- constructor.
- simpl in H. discriminate.
- constructor.
- simpl in H. apply andb_false_elim in H as [H | H]; auto.
- simpl in H. auto.
- simpl in H. apply orb_false_iff in H as [H1 H2]. auto.
Defined.

Lemma stuck_true : forall (c : Contract), stuck c = true -> (Stuck c).
Proof.
induction c; intros; try (simpl in H ; discriminate).
- constructor.
- simpl in H. apply andb_prop in H as [H1 H2].  auto.
- simpl in H. auto.
- simpl in H. apply orb_prop in H as [H | H]; auto.
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
| c0 _*_ c1 => if  sumbool_or _ _ _ _ (stuck_dec c0) (stuck_dec c1) then 0 else (con_size c0) + (con_size c1)
end.


Lemma stuck_0 : forall (c : Contract), Stuck c -> con_size c = 0.
Proof.
intros. induction H.
- reflexivity.
- simpl. rewrite IHStuck1. rewrite IHStuck2. reflexivity.
- simpl. destruct (stuck_dec c0). reflexivity. apply NotStuck_negation in n. contradiction.
- simpl. destruct (sumbool_or (Stuck c0) (NotStuck c0) (Stuck c1)
    (NotStuck c1) (stuck_dec c0) (stuck_dec c1)); auto.
  destruct a. apply NotStuck_negation in H0. contradiction.
- simpl. destruct (sumbool_or (Stuck c0) (NotStuck c0) (Stuck c1)
    (NotStuck c1) (stuck_dec c0) (stuck_dec c1)); auto.
  destruct a. apply NotStuck_negation in H1. contradiction.
Defined.

Lemma stuck_not_nullary : forall (c : Contract), Stuck c -> nu c = false.
Proof.
intros. induction H.
- reflexivity.
- simpl. rewrite IHStuck1. rewrite IHStuck2. reflexivity.
- simpl. rewrite IHStuck. reflexivity.
- simpl. rewrite IHStuck. reflexivity.
- simpl. rewrite IHStuck. rewrite andb_comm. reflexivity.
Defined.

Lemma Stuck_derive : forall (c : Contract)(e : EventType), Stuck c -> Stuck (c /e).
Proof.
intros. induction H; simpl in *.
- constructor.
- constructor; auto.
- apply stuck_not_nullary in H. rewrite H. auto.
- auto.
- auto.
Qed.



Lemma Stuck_derive_0 : forall (c : Contract)(e:EventType), Stuck c -> con_size (c / e) = 0.
Proof.
intros. apply stuck_0. apply Stuck_derive. assumption.
Qed.

Ltac NotStuck_con H := apply NotStuck_negation in H; contradiction.

Lemma NotStuck_0lt : forall (c : Contract), NotStuck c -> 0 < con_size c.
Proof.
intros. induction H; simpl ; try lia.
destruct (stuck_dec c0).
- NotStuck_con H.
- lia.
- destruct (sumbool_or (Stuck c0) (NotStuck c0) (Stuck c1)
    (NotStuck c1) (stuck_dec c0) (stuck_dec c1)).
  * destruct o. NotStuck_con H. NotStuck_con H0.
  * destruct a. lia.
Defined.




Lemma not_stuck_derives : forall (c : Contract), NotStuck c -> (forall (e : EventType), con_size (c / e) < con_size c).
Proof.
intros. induction c.
- simpl. lia.
- inversion H.
- simpl. destruct (eq_event_dec e0 e) ; simpl ; lia.
- simpl. inversion H.
  * destruct (stuck_dec c2).
    ** apply stuck_0 in s as s2. rewrite (Stuck_derive_0 _ s). rewrite Max.max_comm. simpl. 
       apply Max.max_case_strong.
      *** intros. auto.
      *** intros. rewrite s2 in H3. pose proof (NotStuck_0lt H1). lia.
    ** apply IHc1 in H1. apply IHc2 in n. lia.
  * destruct (stuck_dec c1).
    ** apply stuck_0 in s as s2. rewrite (Stuck_derive_0 _ s). simpl. 
       apply Max.max_case_strong.
      *** intros. rewrite s2 in H3. pose proof (NotStuck_0lt H0). lia.
      *** intros. auto.
    ** apply IHc1 in n. apply IHc2 in H0. lia.
- inversion H. subst. simpl. destruct (nu c1) eqn:Heqn.
  * destruct (stuck_dec c1). apply NotStuck_negation in H1. contradiction.
    simpl. destruct (stuck_dec (c1 / e)).
    ** simpl. destruct (stuck_dec c2).
      *** rewrite Stuck_derive_0. pose proof (NotStuck_0lt H1). lia. assumption.
      *** rewrite <- (plus_O_n (con_size (c2 / e))). apply IHc2 in n0. lia.
    ** apply IHc1 in H1. destruct (stuck_dec c2).

      *** rewrite (Stuck_derive_0 _ s). rewrite Max.max_comm.  simpl. apply plus_lt_compat_r.  assumption. 
      *** apply IHc1 in n. apply IHc2 in n1. lia.
  * destruct (stuck_dec c1).
    ** apply NotStuck_negation in H1. contradiction.
    ** simpl. destruct (stuck_dec (c1 / e)).
      *** pose proof (NotStuck_0lt H1). lia.
      *** apply Plus.plus_lt_compat_r. auto.
- inversion H. subst. simpl. destruct (sumbool_or (Stuck (c1 / e)) (NotStuck (c1 / e))
                                      (Stuck c2) (NotStuck c2) (stuck_dec (c1 / e))
      (                                 stuck_dec c2)) as [[o | o] | o].
  * destruct (sumbool_or (Stuck c1) (NotStuck c1) 
      (Stuck (c2 / e)) (NotStuck (c2 / e)) 
      (stuck_dec c1) (stuck_dec (c2 / e))) as [[o0 | o0] | o0].
    ** NotStuck_con H2.
    ** simpl. destruct (sumbool_or (Stuck c1) (NotStuck c1) (Stuck c2)
    (NotStuck c2) (stuck_dec c1) (stuck_dec c2)) as [[o1 | o1] | o1].
      *** NotStuck_con H2.
      *** NotStuck_con H3.
      *** pose proof (NotStuck_0lt H2). lia.
    ** destruct (sumbool_or (Stuck c1) (NotStuck c1) (Stuck c2)
    (NotStuck c2) (stuck_dec c1) (stuck_dec c2)) as [[o1 | o1] | o1].
      *** NotStuck_con H2. 
      *** NotStuck_con H3. 
      *** simpl. apply plus_lt_compat_l. auto. 
  * NotStuck_con H3. 
  * destruct o. destruct (sumbool_or (Stuck c1) (NotStuck c1) 
      (Stuck (c2 / e)) (NotStuck (c2 / e)) 
      (stuck_dec c1) (stuck_dec (c2 / e))) as [[o0 | o0] | o0].
    ** NotStuck_con H2. 
    ** destruct (sumbool_or (Stuck c1) (NotStuck c1) (Stuck c2)
    (NotStuck c2) (stuck_dec c1) (stuck_dec c2)) as [[o | o] | o].
      *** NotStuck_con H2.
      *** NotStuck_con H3.
      *** rewrite Max.max_comm. simpl. apply plus_lt_compat_r. auto.
    ** destruct (sumbool_or (Stuck c1) (NotStuck c1) (Stuck c2)
    (NotStuck c2) (stuck_dec c1) (stuck_dec c2)) as [[o | o] | o].
      *** NotStuck_con H2.
      *** NotStuck_con H3.
      *** apply Max.max_case_strong. 
        **** intros. apply plus_lt_compat_r. auto.
        **** intros. apply plus_lt_compat_l. auto.
Qed.

Fixpoint plus_fold (l : list Contract) : Contract :=
match l with
| [] => Failure
| c ::l => c _+_ (plus_fold l)
end.

Lemma in_plus_fold : forall (s : Trace)(l : list Contract), s ==~ plus_fold l <-> 
(exists c, In c l /\ s ==~ c).
Proof.
intros. split.
- induction l.
  * intros. simpl in H. inversion H.
  * intros. simpl in H. inversion H. 
    ** exists a. split. apply in_eq. assumption.
    ** apply IHl in H1 as [c' [P1 P2]]. exists c'. split ; auto using  in_cons.
- intros. destruct H as [ c' [P1 P2]]. induction l.
  * destruct P1.
  * apply in_inv in P1 as [P1 | P1].
    ** simpl. rewrite P1. auto.
    ** simpl. auto.
Qed.



Equations plus_norm (c : Contract) : (Contract) by  wf (con_size c) :=
plus_norm  c := if stuck_dec c then Failure
               else if nu c then Success _+_ plus_fold (map (fun e => (Event e) _;_ (plus_norm (c / e))) alphabet)
                            else  plus_fold (map (fun e => (Event e) _;_ (plus_norm (c / e))) alphabet).

Next Obligation. auto using not_stuck_derives. Defined.
Next Obligation. auto using not_stuck_derives. Defined.
Global Transparent plus_norm.
Eval compute in plus_norm (Transfer _._ Notify _._ Success _+_ Success).

Lemma Stuck_failure : forall (c : Contract), Stuck c -> (forall s, s ==~ c <-> s ==~ Failure).
Proof.
intros. split. 2: { intros. inversion H0. }
generalize dependent s.  induction c; intros.
- inversion H.
- assumption. 
- inversion H.
- inversion H. inversion H0; auto.
- inversion H. inversion H0. apply IHc1 in H7. inversion H7. assumption.
- inversion H0. inversion H.
  * eapply IHc1 in H8. inversion H8. eauto.
  * eapply IHc2 in H8. inversion H8. eauto.
Qed.


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
  * inversion H. inversion H5; subst;simpl.
    ** rewrite IHc1. rewrite IHc2. reflexivity. all:auto.
    ** rewrite IHc1. rewrite IHc2. reflexivity. all:auto.
- intros. induction c.
  * constructor.
  * discriminate H.
  * discriminate H.
  * simpl in H. apply orb_prop in H as [H | H]; auto.
  * simpl in H. rewrite <- (app_nil_l []). apply andb_prop in H as [H1 H2]; auto.
  * simpl in H. apply andb_prop in H as [H1 H2]. apply MPar with [] []; auto. 
Qed.


Lemma plus_norm_cons : forall (e:EventType)(s:Trace)(c:Contract),
(forall (e : EventType) (s : Trace), s ==~ c / e <-> s ==~ plus_norm (c / e)) ->
e :: s ==~ c <-> e :: s ==~ plus_fold (map (fun e0 : EventType => Event e0 _;_ plus_norm (c / e0)) alphabet).
Proof.
intros. repeat rewrite derive_spec_comp.
assert (HA: forall (l : list Contract)(e : EventType), (plus_fold l) / e = plus_fold (map (fun c => c / e) l)).
{ intros. induction l. - reflexivity. - simpl. f_equal. assumption. } rewrite HA. rewrite in_plus_fold.
rewrite map_map. rewrite H. split;intros.
- exists (Success _;_ (plus_norm (c / e))). split.
  * rewrite in_map_iff. exists e. split. 
      ** simpl. destruct (eq_event_dec e e);[ reflexivity | contradiction ].
      ** unfold alphabet. destruct e ; repeat (try apply in_eq ; try apply in_cons).
  * rewrite <- (app_nil_l s). constructor; auto.
- destruct H0 as [c0 [P0 P1]]. rewrite in_map_iff in P0. destruct P0 as [x [P3 P4]]. subst.
  simpl in P1. destruct (eq_event_dec x e).
  * inversion P1. inversion H3. subst. simpl. assumption.
  * inversion P1. inversion H3.
Qed.


Lemma plus_norm_nil : forall (c : Contract), ~([] ==~ plus_fold (map (fun e0 : EventType => Event e0 _;_ plus_norm (c / e0)) alphabet)).
Proof.
intros. intro H. apply in_plus_fold in H as [c0 [P0 P1]]. apply in_map_iff in P0 as [e [P P3]]. 
subst. inversion P1. apply app_eq_nil in H0 as [H0 H00]. subst. inversion H1.
Qed.
 
Theorem plus_norm_spec : forall (c : Contract)(s : Trace), s ==~ c <-> s ==~ plus_norm c.
Proof.
intros. funelim (plus_norm c). destruct (stuck_dec c).
- apply Stuck_failure. assumption.
- destruct (nu c) eqn:Heqn.
  * destruct s.
    ** split;intros;auto. apply empty_nu. assumption.
    ** assert (HA: forall (c : Contract), e::s ==~ Success _+_ c <-> e::s ==~ c).
       { split; intros. inversion H0. inversion H3. assumption. auto. } rewrite HA.
       apply plus_norm_cons. auto.
  * destruct s.
    ** split;intros.
      *** apply empty_nu in H0. rewrite Heqn in H0. discriminate.
      *** apply plus_norm_nil in H0 as [].
    ** apply plus_norm_cons. auto.
Qed.


Inductive Sequential : Contract -> Type :=
 | SeqFailure : Sequential Failure
 | SeqSuccess : Sequential Success
 | SeqEvent e  : Sequential (Event e)
 | SeqPlus c0 c1 (H0: Sequential c0) (H1 : Sequential c1) : Sequential (c0 _+_ c1)
 | SeqSeq c0 c1 (H0: Sequential c0) (H1 : Sequential c1) : Sequential (c0 _;_ c1).

 
Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with
    | Some x => f x
    | None => None
  end.

Print option.
Fixpoint translate_aux (c : Contract) : option CSLC.Contract :=
match c with
| Failure => Some CSLC.Failure
| Success => Some CSLC.Success
| Event e => Some (CSLC.Event e)
| c0 _+_ c1 => bind (translate_aux c0) (fun c0' => bind (translate_aux c1) (fun c1' => Some (CSLC.CPlus c0' c1')))
| c0 _;_ c1 => bind (translate_aux c0) (fun c0' => bind (translate_aux c1) (fun c1' => Some (CSLC.CSeq c0' c1')))
| c0 _*_ c1 => None
end.

Lemma translate_aux_sequential : forall (c : Contract), Sequential c -> exists c', translate_aux c = Some c'.
Proof. 
intros. induction H.
- exists CSLC.Failure. reflexivity.
- exists CSLC.Success. reflexivity.
- exists (CSLC.Event e). reflexivity.
- destruct IHSequential1,IHSequential2. exists (CSLC.CPlus x x0).
  simpl. unfold bind. destruct (translate_aux c0).
  * destruct (translate_aux c1).
    ** inversion H1. inversion H2. reflexivity.
    ** inversion H2.
  * inversion H1.
- destruct IHSequential1,IHSequential2. exists (CSLC.CSeq x x0).
  simpl. unfold bind. destruct (translate_aux c0).
  * destruct (translate_aux c1).
    ** inversion H1. inversion H2. reflexivity.
    ** inversion H2.
  * inversion H1.
Qed.

Lemma translate_aux_spec : forall (c : Contract)(c' : CSLC.Contract),translate_aux c = Some c' -> (forall s, s ==~ c <-> CSLC.matches_comp s c').
Proof.
split. generalize dependent c'. generalize dependent s.
- induction c; intros.
  * inversion H. inversion H0. constructor.
  * inversion H0.
  * inversion H0. inversion H. constructor.
  * inversion H. unfold bind in H2. destruct (translate_aux c1). 
    ** destruct (translate_aux c2). 
      *** inversion H2. inversion H0;auto.
      *** inversion H2.
    ** inversion H2.
  * inversion H. unfold bind in H2. destruct (translate_aux c1). 
    ** destruct (translate_aux c2). 
      *** inversion H2. inversion H0;auto.
      *** inversion H2.
    ** inversion H2.
  * simpl in H. discriminate.
- generalize dependent c'. generalize dependent s. induction c; intros.
  * inversion H. subst. inversion H0.  constructor.
  * inversion H. subst. inversion H0.
  * inversion H.  subst. inversion H0. constructor.
  * inversion H. unfold bind in H2. destruct (translate_aux c1).
    ** destruct (translate_aux c2).
      *** inversion H2. subst. inversion H0.
        **** subst. constructor. eapply IHc1. eauto. auto.
        **** subst. apply MPlusR. eapply IHc2. eauto. auto.
      *** inversion H2.
    ** inversion H2.
  * inversion H. unfold bind in H2. destruct (translate_aux c1).
    ** destruct (translate_aux c2).
      *** inversion H2. subst. inversion H0. subst. constructor;eauto. 
      *** inversion H2.
    ** inversion H2.
  * inversion H.
Qed.


Lemma plus_norm_sequential : forall (c : Contract), Sequential (plus_norm c).
Proof. 
intros. funelim (plus_norm c).
destruct (stuck_dec c).
- constructor.
- destruct (nu c).
  * constructor. constructor. induction alphabet.
    ** simpl. constructor.
    ** simpl. repeat constructor. auto. assumption.
  * induction alphabet.
    ** simpl. constructor.
    ** simpl. repeat constructor. auto. assumption.
Defined.

Definition translate (c : Contract) : option CSLC.Contract := translate_aux (plus_norm c).



Theorem correct_translation : forall (c : Contract), exists c', translate c = Some c' /\ (forall s, pmatches_comp s c <-> CSLC.matches_comp s c').
Proof.
intros. unfold translate. pose proof (translate_aux_sequential (plus_norm_sequential c)).
destruct H. exists x. split. assumption. split; intros.
- apply plus_norm_spec in H0. apply translate_aux_spec with (plus_norm c); assumption.
- apply plus_norm_spec. apply translate_aux_spec with (plus_norm c) x s in H. rewrite H. assumption.
Qed. 