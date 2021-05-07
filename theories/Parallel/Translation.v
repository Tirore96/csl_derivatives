Require Import Lists.List.
Require Import Bool.Bool.
Require Import Bool.Sumbool.
Require Import Program.
From Equations Require Import Equations.
Require Import micromega.Lia.
Require Import Arith.
Import ListNotations.

Require Import CSL.Parallel.Contract.

Set Implicit Arguments.



Inductive Stuck : Contract -> Prop :=
 | STFailure : Stuck Failure
 | STPLus c0 c1 (H0 : Stuck c0) (H1 : Stuck c1) : Stuck (c0 _+_ c1)
 | STSeq c0 c1 (H0 : Stuck c0) : Stuck (c0 _;_ c1)
 | STParL c0 c1 (H0 : Stuck c0) : Stuck (c0 _*_ c1)
 | STParR c0 c1 (H1 : Stuck c1) : Stuck (c0 _*_ c1).
Hint Constructors Stuck : tDB.

Inductive NotStuck : Contract -> Prop :=
 | NSTSuccess : NotStuck Success
 | NSEvent e : NotStuck (Event e)
 | NSTPlusL c0 c1 (H0 : NotStuck c0) : NotStuck (c0 _+_ c1)
 | NSTPlusR c0 c1 (H1 : NotStuck c1) : NotStuck (c0 _+_ c1)
 | NSTSeq c0 c1 (H0 : NotStuck c0) : NotStuck (c0 _;_ c1)
 | NSTPar c0 c1 (H0 : NotStuck c0)(H1 : NotStuck c1) : NotStuck (c0 _*_ c1).

Hint Constructors NotStuck : tDB.

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
induction c; intros;simpl in*;auto with tDB bool; try discriminate.
apply andb_false_elim in H as [H | H]; auto with tDB.
apply orb_false_iff in H as [H1 H2]; auto with tDB.
Defined.

Lemma stuck_true : forall (c : Contract), stuck c = true -> (Stuck c).
Proof.
induction c; intros; simpl in *; auto with tDB; try discriminate. 
apply orb_prop in H as [H | H]; auto with tDB.
Defined.


Definition stuck_dec (c : Contract) : {Stuck c}+{NotStuck c}.
Proof. destruct (stuck c) eqn:Heqn; auto using stuck_true || auto using stuck_false.
Defined.

Lemma NotStuck_negation : forall (c : Contract), NotStuck c -> ~(Stuck c).
Proof.
intros. induction H ; intro H2; inversion H2.
all : inversion H2; contradiction.
Qed.

Fixpoint con_size (c:Contract):nat :=
match c with
| Failure => 0
| Success => 1
| Event _ => 2
| c0 _+_ c1 => max (con_size c0) (con_size c1) 
| c0 _;_ c1 => if stuck_dec c0 then 0 else (con_size c0) + (con_size c1)
| c0 _*_ c1 => if  sumbool_or _ _ _ _ (stuck_dec c0) (stuck_dec c1) then 0 else (con_size c0) + (con_size c1)
end.

Ltac stuck_tac :=
  (repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         | [ |- context[if ?a then _ else _] ] => destruct a
         | [ H: Stuck ?c0, H1: NotStuck ?c0  |- _ ] => apply NotStuck_negation in H1; contradiction
  end);auto with tDB.



Lemma stuck_0 : forall (c : Contract), Stuck c -> con_size c = 0.
Proof.
intros. induction H;auto;simpl; try solve [ lia | stuck_tac].
Defined.

Lemma stuck_not_nullary : forall (c : Contract), Stuck c -> nu c = false.
Proof.
intros. induction H; simpl ;subst ;auto with bool.
all : rewrite IHStuck. all: auto with bool.
rewrite andb_comm. auto with bool.
Defined.

Lemma Stuck_derive : forall (c : Contract)(e : EventType), Stuck c -> Stuck (e \ c).
Proof.
intros. induction H; simpl in *.
- constructor.
- constructor; auto.
- apply stuck_not_nullary in H. rewrite H. auto with tDB.
- auto with tDB.
- auto with tDB.
Qed.



Lemma Stuck_derive_0 : forall (c : Contract)(e:EventType), Stuck c -> con_size (e \ c) = 0.
Proof.
intros. apply stuck_0. apply Stuck_derive. assumption.
Qed.

Ltac NotStuck_con H := apply NotStuck_negation in H; contradiction.

Lemma NotStuck_0lt : forall (c : Contract), NotStuck c -> 0 < con_size c.
Proof.
intros. induction H; simpl ; try lia.
- stuck_tac. lia.
- stuck_tac. destruct o; stuck_tac. lia.
Defined.
(*
Lemma not_stuck_derives : forall (c : Contract), NotStuck c -> (forall (e : EventType), con_size (e \ c ) < con_size c).
Proof.
intros. generalize dependent e. induction H;intros;simpl.
- lia.
- stuck_tac.
- apply NotStuck_0lt in H. apply Max.max_case_strong. intros.
  unfold lt. lia.
*)

Lemma lt_le_l : forall n0 n1 n2 n3, n0 <= n2 -> n1 < n3 -> n0 + n1 < n2 + n3.
Proof.
intros. lia.
Qed.

Lemma lt_le_r : forall n0 n1 n2 n3, n0 < n2 -> n1 <= n3 -> n0 + n1 < n2 + n3.
Proof.
intros. lia.
Qed.

Lemma S_plus : forall n, S n = 1 + n.
Proof.
lia.
Qed.

Lemma not_stuck_derives : forall (c : Contract), NotStuck c -> (forall (e : EventType), con_size (e \ c) < con_size c).
Proof.
intros. induction c.
- simpl. lia.
- inversion H.
- simpl. destruct (EventType_eq_dec e0 e) ; simpl ; lia.
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
    simpl. destruct (stuck_dec (e \ c1)).
    ** simpl. destruct (stuck_dec c2).
      *** rewrite Stuck_derive_0. pose proof (NotStuck_0lt H1). lia. assumption.
      *** rewrite <- (plus_O_n (con_size (e \ c2))). apply IHc2 in n0. lia.
    ** apply IHc1 in H1. destruct (stuck_dec c2).

      *** rewrite (Stuck_derive_0 _ s). rewrite Max.max_comm.  simpl. apply plus_lt_compat_r.  assumption. 
      *** apply IHc1 in n. apply IHc2 in n1. lia.
  * destruct (stuck_dec c1).
    ** apply NotStuck_negation in H1. contradiction.
    ** simpl. destruct (stuck_dec (e \ c1)).
      *** pose proof (NotStuck_0lt H1). lia.
      *** apply Plus.plus_lt_compat_r. auto.
- inversion H. subst. simpl. destruct (sumbool_or (Stuck (e \ c1)) (NotStuck (e \ c1))
                                      (Stuck c2) (NotStuck c2) (stuck_dec (e \ c1))
      (                                 stuck_dec c2)) as [[o | o] | o].
  * destruct (sumbool_or (Stuck c1) (NotStuck c1) 
      (Stuck (e \ c2)) (NotStuck (e \ c2)) 
      (stuck_dec c1) (stuck_dec (e \ c2))) as [[o0 | o0] | o0].
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
      (Stuck (e \ c2)) (NotStuck (e \ c2)) 
      (stuck_dec c1) (stuck_dec (e \ c2))) as [[o0 | o0] | o0].
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

(*
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
Qed.*)


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



Equations plus_norm (c : Contract) : (Contract) by  wf (con_size c) :=
plus_norm  c := if stuck_dec c then Failure
               else if nu c then Success _+_ plus_fold (map (fun e => (Event e) _;_ (plus_norm (c / e))) alphabet)
                            else             plus_fold (map (fun e => (Event e) _;_ (plus_norm (c / e))) alphabet).

Next Obligation. auto using not_stuck_derives. Defined.
Next Obligation. auto using not_stuck_derives. Defined.
Global Transparent plus_norm.
Eval compute in plus_norm (Transfer _._ Notify _._ Success _+_ Success).


(*
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
Qed.*)


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