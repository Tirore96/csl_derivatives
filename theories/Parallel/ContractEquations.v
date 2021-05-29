Require Import CSL.Parallel.Contract.  
Require Import Lists.List Bool.Bool Bool.Sumbool Setoid Coq.Arith.PeanoNat.
Require Import micromega.Lia.
From Equations Require Import Equations.
Require Import Arith.
Require Import micromega.Lia.

Import ListNotations.

Set Implicit Arguments.

Reserved Notation "c0 =R= c1" (at level 63).

Inductive Sequential : Contract -> Prop :=
 | SeqFailure : Sequential Failure
 | SeqSuccess : Sequential Success
 | SeqEvent e  : Sequential (Event e)
 | SeqPlus c0 c1 (H0: Sequential c0) (H1 : Sequential c1) : Sequential (c0 _+_ c1)
 | SeqSeq c0 c1 (H0: Sequential c0) (H1 : Sequential c1) : Sequential (c0 _;_ c1).
Hint Constructors Sequential : eqDB.

Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with
    | Some x => f x
    | None => None
  end.


Fixpoint translate_aux (c : Contract) : option CSLC.Contract :=
match c with
| Failure => Some CSLC.Failure
| Success => Some CSLC.Success
| Event e => Some (CSLC.Event e)
| c0 _+_ c1 => bind (translate_aux c0) (fun c0' => bind (translate_aux c1) (fun c1' => Some (CSLC.CPlus c0' c1')))
| c0 _;_ c1 => bind (translate_aux c0) (fun c0' => bind (translate_aux c1) (fun c1' => Some (CSLC.CSeq c0' c1')))
| c0 _||_ c1 => None
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


Require CSL.Core.ContractEquations.
Module CSLEQ := CSL.Core.ContractEquations.

Ltac option_inversion :=
  (repeat match goal with
         | [ H: None = Some _ |- _ ] => discriminate
         | [ H: Some _ = None |- _ ] => discriminate
         | [ H: Some _ = Some _ |- _ ] => inversion H; clear H
          end);subst.

Ltac c_inversion :=
  (repeat match goal with
         | [ H: _ (:) Failure |- _ ] => inversion H
         | [ H: ?s (:) _ _+_ _ |- _ ] => inversion H; clear H
         | [ H: ?s (:) _ _;_ _ |- _ ] => inversion H; clear H
         | [ H: ?s (:) _ _||_ _ |- _ ] => inversion H; clear H
         | [ H: [?x] (:) Event _ |- _ ] => fail
         | [ H: ?s (:) Event _ |- _ ] => inversion H; subst
         | [ H: [] (:) Success |- _ ] => fail
         | [ H: _ (:) Success |- _ ] => inversion H; clear H

         end); option_inversion; auto with cDB.

Ltac core_inversion := option_inversion;CSLEQ.c_inversion.

Lemma translate_aux_spec : forall (c : Contract)(c' : CSLC.Contract),translate_aux c = Some c' -> (forall s, s (:) c <-> CSLC.Matches_Comp s c').
Proof.
split. generalize dependent c'. generalize dependent s.
- induction c; intros;simpl in*;c_inversion.
  all: unfold bind in H; destruct (translate_aux c1);try c_inversion;
       destruct (translate_aux c2); c_inversion; c_inversion.
- generalize dependent c'. generalize dependent s; induction c; intros;simpl in*.
  * core_inversion.
  * core_inversion.
  * core_inversion.
  * unfold bind in H. destruct (translate_aux c1);try c_inversion.
    destruct (translate_aux c2);try c_inversion.
    core_inversion; eauto with cDB.
  * unfold bind in H. destruct (translate_aux c1);try c_inversion.
    destruct (translate_aux c2);try c_inversion.
    core_inversion; eauto with cDB.
  * discriminate.
Qed.


Inductive c_eq : Contract -> Contract -> Prop :=
| c_core p0 p1 c0 c1 (H0: translate_aux p0 = Some c0) 
                     (H1:translate_aux p1 = Some c1)
                     (H2: CSLEQ.c_eq c0 c1) : p0 =R= p1

| c_plus_assoc c0 c1 c2 : (c0 _+_ c1) _+_ c2 =R= c0 _+_ (c1 _+_ c2)
| c_plus_comm c0 c1: c0 _+_ c1 =R= c1 _+_ c0
| c_plus_neut c: c _+_ Failure =R= c
| c_plus_idemp c : c _+_ c =R= c 
| c_seq_assoc c0 c1 c2 : (c0 _;_ c1) _;_ c2 =R= c0 _;_ (c1 _;_ c2)
| c_seq_neut_l c : (Success _;_ c) =R= c 
| c_seq_neut_r c : c _;_ Success =R= c 
| c_seq_failure_l c : Failure _;_ c =R= Failure  
| c_seq_failure_r c :  c _;_ Failure =R= Failure 
| c_distr_l c0 c1 c2 : c0 _;_ (c1 _+_ c2) =R= (c0 _;_ c1) _+_ (c0 _;_ c2)
| c_distr_r c0 c1 c2 : (c0 _+_ c1) _;_ c2 =R= (c0 _;_ c2) _+_ (c1 _;_ c2)

| c_par_assoc c0 c1 c2 : (c0 _||_ c1) _||_ c2 =R= c0 _||_ (c1 _||_ c2)
| c_par_neut c : c _||_ Success =R= c 
| c_par_comm c0 c1: c0 _||_ c1 =R= c1 _||_ c0
| c_par_failure c : c _||_ Failure =R= Failure   
| c_par_distr_l c0 c1 c2 : c0 _||_ (c1 _+_ c2) =R= (c0 _||_ c1) _+_ (c0 _||_ c2)

| c_par_event e0 e1 c0 c1 : Event e0 _;_ c0 _||_ Event e1 _;_ c1 =R= Event e0 _;_ (c0 _||_ (Event e1 _;_ c1)) _+_ Event e1 _;_ ((Event e0 _;_ c0) _||_ c1)

| c_refl c : c =R= c
| c_sym c0 c1 (H: c0 =R= c1) : c1 =R= c0
| c_trans c0 c1 c2 (H1 : c0 =R= c1) (H2 : c1 =R= c2) : c0 =R= c2
| c_plus_ctx c0 c0' c1 c1' (H1 : c0 =R= c0') (H2 : c1 =R= c1') : c0 _+_ c1 =R= c0' _+_ c1'
| c_seq_ctx c0 c0' c1 c1' (H1 : c0 =R= c0') (H2 : c1 =R= c1') : c0 _;_ c1 =R= c0' _;_ c1'
| c_par_ctx c0 c0' c1 c1' (H1 : c0 =R= c0') (H2 : c1 =R= c1') : c0 _||_ c1 =R= c0' _||_ c1'
  where "c1 =R= c2" := (c_eq c1 c2).


Hint Constructors c_eq : eqDB.

Add Parametric Relation : Contract c_eq
  reflexivity proved by c_refl
  symmetry proved by c_sym
  transitivity proved by c_trans
  as Contract_setoid.

Add Parametric Morphism : Par with
signature c_eq ==> c_eq ==> c_eq as c_eq_par_morphism.
Proof.
  intros. auto with eqDB.
Qed.

Add Parametric Morphism : CPlus with
signature c_eq ==> c_eq ==> c_eq as c_eq_plus_morphism.
Proof.
  intros. auto with eqDB.
Qed.

Add Parametric Morphism : CSeq with
signature c_eq ==> c_eq ==> c_eq as c_eq_seq_morphism.
Proof.
  intros. auto with eqDB.
Qed.




(********************Soundness*****************************)
Lemma cons_app : forall (A: Type) (a : A)(l : list A), a::l = [a]++l.
Proof. auto.
Qed.



Lemma event_seq : forall s e0 c0 e1 c1, s (:) (Event e0 _;_ c0) _||_ (Event e1 _;_ c1) <-> 
s (:) Event e0 _;_ (c0 _||_ (Event e1 _;_ c1)) _+_ Event e1 _;_ ((Event e0 _;_ c0) _||_ c1).
Proof.
split;intros.
- c_inversion. inversion H5;subst. symmetry in H1. apply app_eq_nil in H1.
  destruct H1;subst;simpl. inversion H8. 
  *  apply MPlusL. rewrite cons_app. constructor;auto.
     econstructor;eauto. auto with cDB. 
  * inversion H8;subst. simpl in H. inversion H. 
    apply MPlusR. rewrite cons_app. constructor;auto;subst. 
     econstructor;eauto. eapply MSeq;eauto.
- c_inversion.
  * inversion H6;subst. econstructor. econstructor;eauto. 
    econstructor;eauto. simpl in*;auto with cDB.
  * inversion H6;subst. econstructor. econstructor;eauto. 
    econstructor;eauto. simpl in*;auto with cDB.
Qed.

Lemma c_eq_soundness : forall (c0 c1 : Contract), c0 =R= c1 -> (forall s : Trace, s (:) c0 <-> s (:) c1).
Proof.
intros c0 c1 H. induction H ;intros; try solve [split;intros;c_inversion].
  * repeat rewrite translate_aux_spec;eauto. now apply CSLEQ.c_eq_soundness.
  * split;intros;c_inversion; [ rewrite <- app_assoc | rewrite app_assoc ]; auto with cDB.
  * rewrite <- (app_nil_l s). split;intros;c_inversion.
  * rewrite <- (app_nil_r s) at 1. split;intros;c_inversion. subst.
    repeat rewrite app_nil_r in H1. now rewrite <- H1.
  * split;intros; inversion H; subst.  (*new*)
    ** inversion H3. subst. eapply interl_app in H5;eauto. destruct_ctx.
       eauto with cDB.
    ** inversion H4. subst. eapply interl_comm in H5. eapply interl_comm in H8.
       eapply interl_app in H5;eauto. destruct_ctx. econstructor;eauto. 
       econstructor;eauto. all: eauto using interl_comm.
  * split;intros.
    ** inversion H. subst. inversion H4. subst.
       apply interl_eq_r in H5. subst;auto.
    ** eauto with cDB. 
  * split;intros.
    ** inversion H. subst. econstructor;eauto using interl_comm.
    ** inversion H. subst. econstructor;eauto using interl_comm.
  * split;intros.
    ** inversion H. subst. inversion H4;  eauto with cDB. 
    ** inversion H. subst.
      *** inversion H2. subst. econstructor;eauto with cDB. 
      *** inversion H1. subst. econstructor;eauto with cDB. (*new*)
  * apply event_seq.
  * now symmetry.
  * eauto using iff_trans.
  * split;intros; inversion H1; [ rewrite IHc_eq1 in H4 
                                | rewrite IHc_eq2 in H4
                                | rewrite <- IHc_eq1 in H4 
                                | rewrite <- IHc_eq2 in H4];auto with cDB.
  * split;intros; c_inversion; constructor;
                                [ rewrite <- IHc_eq1
                                | rewrite <- IHc_eq2
                                | rewrite IHc_eq1
                                | rewrite IHc_eq2];auto.
  * split;intros; c_inversion; econstructor;eauto;
                                [ rewrite <- IHc_eq1
                                | rewrite <- IHc_eq2
                                | rewrite IHc_eq1
                                | rewrite IHc_eq2];auto.
Qed.


Lemma Matches_plus_comm : forall c0 c1 s, s (:) c0 _+_ c1 <-> s (:) c1 _+_ c0.
Proof. auto using c_eq_soundness  with eqDB. Qed.

Lemma Matches_plus_neut_l : forall c s, s (:) Failure _+_ c <-> s (:) c.
Proof. intros. rewrite Matches_plus_comm. auto using c_eq_soundness  with eqDB. Qed.

Lemma Matches_plus_neut_r : forall c s, s (:) c _+_ Failure <-> s (:) c.
Proof. auto using c_eq_soundness  with eqDB. Qed.

Lemma Matches_seq_neut_l : forall c s, s (:) (Success _;_ c) <-> s (:) c.
Proof. auto using c_eq_soundness  with eqDB. Qed.

Lemma Matches_seq_neut_r : forall c s, s (:) c _;_ Success <-> s (:) c.
Proof. auto using c_eq_soundness  with eqDB. Qed.

Lemma Matches_seq_assoc : forall c0 c1 c2 s, s (:) (c0 _;_ c1) _;_ c2  <-> s (:) c0 _;_ (c1 _;_ c2).
Proof. auto using c_eq_soundness  with eqDB. Qed.

Hint Rewrite Matches_plus_neut_l 
             Matches_plus_neut_r 
             Matches_seq_neut_l
             Matches_seq_neut_r c_par_distr_l c_par_neut c_par_failure : eqDB.

Lemma c_plus_neut_l : forall c, Failure _+_ c =R= c.
Proof. intros. rewrite c_plus_comm. auto with eqDB.
Qed.

Lemma c_par_neut_l : forall c, Success _||_ c =R= c.
Proof. intros. rewrite c_par_comm. auto with eqDB.
Qed.

Lemma c_par_failure_l  : forall c, Failure _||_ c =R= Failure.
Proof. intros. rewrite c_par_comm. auto with eqDB.
Qed.

Lemma c_par_distr_r : forall c0 c1 c2, (c0 _+_ c1) _||_ c2 =R= (c0 _||_ c2) _+_ (c1 _||_ c2).
Proof. intros. rewrite c_par_comm. rewrite c_par_distr_l. auto with eqDB.
Qed.


Hint Rewrite c_plus_neut_l 
             c_plus_neut 
             c_seq_neut_l
             c_seq_neut_r
             c_seq_failure_l 
             c_seq_failure_r 
             c_distr_l
             c_distr_r c_par_neut_l c_par_failure_l c_par_distr_r c_par_event : eqDB.

Ltac auto_rwd_eqDB := autorewrite with eqDB;auto with eqDB.




Definition alphabet := [Notify;Transfer].

Lemma in_alphabet : forall e, In e alphabet.
Proof.
destruct e ; repeat (try apply in_eq ; try apply in_cons).
Qed.

Hint Resolve in_alphabet : eqDB.
Opaque alphabet.

Fixpoint Σ (A:Type) (l : list A) (f : A -> Contract) : Contract :=
match l with
| [] => Failure
| c ::l => f c _+_ (Σ l f)
end.




(*Not used in this file, maybe used in decision procedure*)
Lemma in_Σ : forall (A:Type)(f : A -> Contract)(l : list A)(s : Trace), s (:) Σ l f <-> 
(exists c, In c (map f l) /\ s (:) c).
Proof. 
induction l;intros;simpl.
- split;intros. c_inversion. destruct_ctx. contradiction.
- split;intros. c_inversion. exists (f a). split;auto.
  rewrite IHl in H1. destruct_ctx. exists x. split;auto.
  destruct_ctx. inversion H. subst. auto with cDB.
  apply MPlusR. rewrite IHl. exists x. split;auto.
Qed.


Definition o c := if nu c then Success else Failure.

Lemma o_plus : forall c0 c1, o (c0 _+_ c1) =R= o c0 _+_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;auto_rwd_eqDB.
Qed.

Lemma o_seq : forall c0 c1, o (c0 _;_ c1) =R= o c0 _;_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;auto_rwd_eqDB.
Qed.

Lemma o_par : forall c0 c1, o (c0 _||_ c1) =R= o c0 _||_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;auto_rwd_eqDB.
Qed.


Lemma o_true : forall c, nu c = true -> o c = Success.
Proof.
intros. unfold o. destruct (nu c);auto. discriminate.
Qed. 

Lemma o_false : forall c, nu c = false -> o c = Failure.
Proof.
intros. unfold o. destruct (nu c);auto. discriminate.
Qed. 

Lemma o_destruct : forall c, o c = Success \/ o c = Failure.
Proof.
intros. unfold o. destruct (nu c);auto || auto.
Qed.

Hint Rewrite o_plus o_seq o_par : eqDB.

Hint Rewrite o_true o_false : oDB. (*maybe remove*)


(******************Translation***************)

Inductive Stuck : Contract -> Prop :=
 | STFailure : Stuck Failure
 | STPLus c0 c1 (H0 : Stuck c0) (H1 : Stuck c1) : Stuck (c0 _+_ c1)
 | STSeq c0 c1 (H0 : Stuck c0) : Stuck (c0 _;_ c1)
 | STParL c0 c1 (H0 : Stuck c0) : Stuck (c0 _||_ c1)
 | STParR c0 c1 (H1 : Stuck c1) : Stuck (c0 _||_ c1).
Hint Constructors Stuck : tDB.

Inductive NotStuck : Contract -> Prop :=
 | NSTSuccess : NotStuck Success
 | NSEvent e : NotStuck (Event e)
 | NSTPlusL c0 c1 (H0 : NotStuck c0) : NotStuck (c0 _+_ c1)
 | NSTPlusR c0 c1 (H1 : NotStuck c1) : NotStuck (c0 _+_ c1)
 | NSTSeq c0 c1 (H0 : NotStuck c0) : NotStuck (c0 _;_ c1)
 | NSTPar c0 c1 (H0 : NotStuck c0)(H1 : NotStuck c1) : NotStuck (c0 _||_ c1).

Hint Constructors NotStuck : tDB.

Fixpoint stuck (c : Contract) :=
match c with
| Failure => true
| c0 _+_ c1 => stuck c0 && stuck c1
| c0 _;_ _ => stuck c0
| c0 _||_ c1 => stuck c0 || stuck c1
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

Print sumbool.



Fixpoint con_size (c:Contract):nat :=
match c with
| Failure => 0
| Success => 1
| Event _ => 2
| c0 _+_ c1 => max (con_size c0) (con_size c1) 
| c0 _;_ c1 => if stuck_dec c0 then 0 else (con_size c0) + (con_size c1)
| c0 _||_ c1 => if  sumbool_or _ _ _ _ (stuck_dec c0) (stuck_dec c1) then 0 else (con_size c0) + (con_size c1)
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
- stuck_tac. destruct o0; stuck_tac. lia.
Defined.


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

      *** rewrite (Stuck_derive_0 _ s). rewrite Max.max_comm.  simpl.  apply plus_lt_compat_r.  assumption. 
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

Lemma Stuck_failure : forall (c : Contract), Stuck c -> (forall s, s (:) c <-> s (:) Failure).
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
               else (o c) _+_ Σ alphabet (fun e => (Event e) _;_ (plus_norm (e \ c))).

Next Obligation. auto using not_stuck_derives. Defined.

Global Transparent plus_norm.
Compute (plus_norm (Event Transfer _;_ Event Notify _||_ Event Notify _;_ Event Transfer)).

Lemma Σ_derive : forall (A:Type)(l : list A)(f : A -> Contract)(e : EventType), e \ (Σ l f) = Σ l (fun c => e \ f c).
Proof. 
induction l;auto;simpl;intros;rewrite IHl;auto.
Qed.

Lemma plus_norm_cons : forall (e:EventType)(s:Trace)(c:Contract),
(forall (e : EventType) (s : Trace), s (:) e \ c <-> s (:) plus_norm (e \ c)) ->
e :: s (:) c <-> e :: s (:) Σ alphabet (fun e0 : EventType => Event e0 _;_ plus_norm (e0 \ c)).
Proof.
intros. repeat rewrite derive_spec_comp.
rewrite Σ_derive. rewrite in_Σ.
rewrite H. split;intros.
- exists (Success _;_ (plus_norm (e \ c))). split.
  * rewrite in_map_iff. exists e. split;auto with eqDB. 
    simpl. destruct (EventType_eq_dec e e);[ reflexivity | contradiction ].
  * rewrite <- (app_nil_l s). constructor; auto with cDB.
- destruct_ctx. rewrite in_map_iff in H0. destruct_ctx.
  subst. simpl in H1. destruct (EventType_eq_dec x0 e).
  * inversion H1. inversion H5. subst. simpl. assumption.
  * inversion H1. inversion H5.
Qed.



Lemma plus_norm_nil : forall (c : Contract), ~([] (:) Σ alphabet (fun e0 : EventType => Event e0 _;_ plus_norm (e0 \ c))).
Proof.
intros. intro H. apply in_Σ in H as [c0 [P0 P1]]. apply in_map_iff in P0 as [e [P P3]]. 
subst. inversion P1. apply app_eq_nil in H0 as [H0 H00]. subst. inversion H1.
Qed.



Lemma cons_Success : forall (c : Contract) e s, e::s (:) Success _+_ c <-> e::s (:) c.
Proof.
split; intros. inversion H. inversion H2. all: auto with cDB.
Qed.

Lemma plus_Failure : forall (c : Contract) s, s (:) Failure _+_ c <-> s (:) c.
Proof.
intro c. apply c_eq_soundness. auto_rwd_eqDB.
Qed.

Theorem plus_norm_spec : forall (c : Contract)(s : Trace), s (:) c <-> s (:) plus_norm c.
Proof.
intros. funelim (plus_norm c). destruct (stuck_dec c).
- apply Stuck_failure. assumption.
- destruct s.
  * unfold o. destruct (nu c) eqn:Heqn.
    ** split;intros;auto using Matches_Comp_nil_nu with cDB.
    ** split;intros. 
      *** rewrite Matches_Comp_iff_matchesb in H0. simpl in *. 
          rewrite Heqn in H0. discriminate.
      *** c_inversion. apply plus_norm_nil in H3 as []. 
  * unfold o. destruct (nu c) eqn:Heqn.
    ** rewrite cons_Success. auto using plus_norm_cons.
    ** rewrite plus_Failure. auto using plus_norm_cons.
Qed.



(**********plus_norm respects axiomatization *******)



Lemma Stuck_eq_Failure : forall c, Stuck c -> c =R= Failure.
Proof.
intros. induction H;auto with eqDB.
- rewrite IHStuck1. rewrite IHStuck2. auto_rwd_eqDB.
- rewrite IHStuck. auto_rwd_eqDB.
- rewrite IHStuck. rewrite c_par_comm. auto_rwd_eqDB.
- rewrite IHStuck. auto_rwd_eqDB.
Qed.



Lemma plus_norm_Failure : plus_norm Failure =R= Failure.
Proof.
simp plus_norm. stuck_tac;auto_rwd_eqDB. inversion n.
Qed. 

Lemma Σ_Seq_Failure : forall es, Σ es (fun e : EventType => Event e _;_ plus_norm Failure) =R= Failure.
Proof.
induction es. simpl. reflexivity.
simpl. rewrite IHes. auto_rwd_eqDB.
Qed.

Lemma plus_norm_Success : plus_norm Success =R= Success.
Proof.
simp plus_norm. stuck_tac. symmetry. auto using Stuck_eq_Failure.
simpl. rewrite Σ_Seq_Failure. auto_rwd_eqDB.
Qed. 

Hint Rewrite plus_norm_Failure plus_norm_Success : eqDB.

Ltac eq_m_left := repeat rewrite c_plus_assoc; apply c_plus_ctx;
                  auto_rwd_eqDB.

Ltac eq_m_right := repeat rewrite <- c_plus_assoc; apply c_plus_ctx;
                  auto_rwd_eqDB.


Lemma Σ_alphabet_or : forall alphabet0 e ,
 Σ alphabet0 (fun a : CSLC.EventType => if EventType_eq_dec e a then Success else Failure) =R= Success /\ In e alphabet0 \/
 Σ alphabet0 (fun a : CSLC.EventType => if EventType_eq_dec e a then Success else Failure) =R= Failure /\ ~(In e alphabet0).
Proof.
induction alphabet0;intros.
- simpl. now right.
- simpl. eq_event_destruct.
  * subst. edestruct IHalphabet0.
    ** destruct H. left. split.
       rewrite H. auto_rwd_eqDB. now left.
    ** destruct H. rewrite H.
       auto_rwd_eqDB.
  * edestruct IHalphabet0; destruct H; rewrite H; auto_rwd_eqDB.
    right. split;auto with eqDB. intro H2. destruct H2.
    symmetry in H1. contradiction. contradiction.
Qed.

(************Summation rules used in showing normalization respects axiomatization*****)
Lemma Σ_alphabet : forall e, Σ alphabet (fun a => if EventType_eq_dec e a then Success else Failure) =R= Success.
Proof.
intros. destruct (Σ_alphabet_or alphabet e).
- destruct H. auto.
- destruct H. pose proof (in_alphabet e). contradiction.
Qed.

(*
Add Parametric Morphism A l : (Σ l) with
signature (fun f0 f1 => forall (a:A), f0 a =R= f1 a)  ==> c_eq as c_eq_Σ_morphism.
Proof.
induction l;intros; simpl; auto with eqDB.
Qed.
*)
Definition fun_eq (f0 f1 : EventType -> Contract) := (forall a, f0 a =R= f1 a).

Add Parametric Morphism l : (Σ l)  with
signature fun_eq  ==> c_eq as c_eq_Σ_morphism.
Proof.
induction l;intros; simpl; auto with eqDB.
Qed.



Notation "f0 =F= f1" := (fun_eq f0 f1)(at level 63).

Check c_eq_Σ_morphism.

Lemma fun_eq_refl : forall f, f =F= f.
Proof.
intros. unfold fun_eq. auto with eqDB.
Qed.

Lemma fun_eq_sym : forall f0 f1,f0 =F= f1 -> f1 =F= f0.
Proof.
intros. unfold fun_eq. auto with eqDB.
Qed.

Lemma fun_eq_trans : forall f0 f1 f2,f0 =F= f1 -> f1 =F= f2 -> f0 =F= f2.
Proof.
intros. unfold fun_eq. eauto with eqDB.
Qed.

Add Parametric Relation : (EventType -> Contract) fun_eq
  reflexivity proved by fun_eq_refl
  symmetry proved by fun_eq_sym
  transitivity proved by fun_eq_trans
  as fun_Contract_setoid.



Lemma seq_derive_o : forall e c0 c1, e \ (c0 _;_ c1) =R= e \ c0 _;_ c1 _+_ o (c0) _;_ e \ c1.
Proof.
intros;simpl.  destruct (nu c0) eqn:Heqn.
- destruct (o_destruct c0). rewrite H. auto_rwd_eqDB.
  unfold o in H. rewrite Heqn in H. discriminate.
- destruct (o_destruct c0). unfold o in H. rewrite Heqn in H. discriminate.
  rewrite H. auto_rwd_eqDB.
Qed.

Lemma seq_derive_o_fun : forall c0 c1, (fun e0 => e0 \ (c0 _;_ c1)) =F= (fun e0 => e0 \ c0 _;_ c1 _+_ o (c0) _;_ e0 \ c1).
Proof.
intros. unfold fun_eq.  pose proof seq_derive_o. simpl in *. auto.
Qed.


Hint Rewrite seq_derive_o_fun : funDB.

Definition seq_fun (f0 f1 : EventType -> Contract) := fun a => f0 a _;_ f1 a.
Notation "f0 _f;f_ f1" := (seq_fun f0 f1)(at level 59).

Lemma to_seq_fun : forall f0 f1, (fun a => f0 a _;_ f1 a) =F= f0 _f;f_ f1.
Proof.
intros. unfold seq_fun. reflexivity.
Qed.

Opaque seq_fun.

Add Parametric Morphism : (seq_fun) with
signature fun_eq ==> fun_eq ==> fun_eq as fun_eq_seq_morphism.
Proof.
intros. repeat rewrite <- to_seq_fun. unfold fun_eq in *. intros. auto with eqDB.
Qed.


Definition plus_fun (f0 f1 : EventType -> Contract) := fun a => f0 a _+_ f1 a.

Notation "f0 _f+f_ f1" := (plus_fun f0 f1)(at level 61).
Lemma to_plus_fun : forall f0 f1, (fun a => f0 a _+_ f1 a) =F= f0 _f+f_ f1.
Proof.
intros. unfold plus_fun. reflexivity.
Qed.

Opaque plus_fun.

Add Parametric Morphism : (plus_fun) with
signature fun_eq ==> fun_eq ==> fun_eq as fun_eq_plus_morphism.
Proof.
intros. repeat rewrite <- to_plus_fun. unfold fun_eq in *. intros. auto with eqDB.
Qed.


Definition par_fun (f0 f1 : EventType -> Contract) := fun a => f0 a _||_ f1 a.
Notation "f0 _f*f_ f1" := (par_fun f0 f1)(at level 60).
Lemma to_par_fun : forall f0 f1, (fun a => f0 a _||_ f1 a) =F= f0 _f*f_ f1.
Proof.
intros. unfold par_fun. reflexivity.
Qed.

Opaque plus_fun.

Add Parametric Morphism : (par_fun) with
signature fun_eq ==> fun_eq ==> fun_eq as fun_eq_par_morphism.
Proof.
intros. repeat rewrite <- to_par_fun. unfold fun_eq in *. intros. auto with eqDB.
Qed.

Hint Rewrite to_seq_fun to_plus_fun to_par_fun : funDB.



Lemma Σ_split_plus : forall (A: Type) l (P P' : A -> Contract),
Σ l (fun a : A => P a _+_ P' a) =R= Σ l (fun a : A => P a) _+_  Σ l (fun a : A => P' a).
Proof.
intros.
induction l;intros.
- simpl. auto_rwd_eqDB.
- simpl. rewrite IHl. eq_m_left. rewrite c_plus_comm. eq_m_left.
Qed.


Lemma Σ_factor_seq_r : forall l (P: EventType -> Contract) c,
Σ l (fun a  => P a _;_ c) =R= Σ l (fun a  => P a) _;_ c.
Proof.
induction l;intros.
- simpl. auto_rwd_eqDB.
- simpl. auto_rwd_eqDB.
Qed.

Lemma Σ_factor_seq_l : forall l (P: EventType -> Contract) c,
Σ l (fun a  => c _;_ P a) =R= c _;_ Σ l (fun a  => P a).
Proof.
induction l;intros.
- simpl. auto_rwd_eqDB.
- simpl. auto_rwd_eqDB.
Qed.


Lemma Σ_factor_par_l : forall l1 c (P' : EventType -> Contract),
Σ l1 (fun a' : EventType => c _||_ P' a') =R=
c _||_ Σ l1 (fun a0 : EventType => P' a0).
Proof.
induction l1;intros.
- simpl. auto_rwd_eqDB.
- simpl. rewrite IHl1. auto_rwd_eqDB.
Qed.

Lemma Σ_factor_par_r : forall l1 c (P' : EventType -> Contract),
Σ l1 (fun a0 : EventType => P' a0) _||_ c =R=
Σ l1 (fun a' : EventType => P' a' _||_ c).
Proof.
induction l1;intros.
- simpl. auto_rwd_eqDB.
- simpl. rewrite <- IHl1. auto_rwd_eqDB.
Qed.

Lemma Σ_par_ΣΣ : forall l0 l1 (P0 P1 : EventType -> Contract),
Σ l0 (fun a0  => P0 a0) _||_ Σ l1 (fun a1 => P1 a1) =R=
Σ l0 (fun a0  => Σ l1 (fun a1  => (P0 a0) _||_ (P1 a1))).
Proof. 
induction l0;intros.
- simpl. auto_rwd_eqDB.
- simpl. auto_rwd_eqDB.
  rewrite Σ_factor_par_l. rewrite IHl0.  reflexivity. 
Qed. 


Lemma ΣΣ_prod_swap : forall l0 l1 (P : EventType -> EventType -> Contract), 
Σ l0 (fun a0 => Σ l1 (fun a1 => P a0 a1)) =R=
Σ l1 (fun a0 => Σ l0 (fun a1 => P a1 a0)).
Proof.
induction l0;intros.
- simpl. induction l1;intros;simpl;auto with eqDB. rewrite IHl1.
  auto with eqDB.
- simpl. rewrite Σ_split_plus. eq_m_left.
Qed.

Lemma fold_Failure : forall l, Σ l (fun _ : EventType => Failure) =R= Failure.
Proof.
induction l;intros. simpl. reflexivity.
simpl. rewrite IHl. autorewrite with eqDB. reflexivity.
Qed.

Hint Resolve fold_Failure : eqDB.

(*Duplicate some of the rules to the function level*)

Lemma Σ_plus_decomp_fun : forall l f0 f1, Σ l (f0 _f+f_ f1) =R= Σ l f0 _+_  Σ l f1.
Proof.
intros. rewrite <- to_plus_fun. apply Σ_split_plus.
Qed.

Lemma Σ_factor_seq_l_fun : forall l f c, Σ l ((fun _ => c ) _f;f_ f) =R= c _;_ Σ l f.
Proof.
intros. rewrite <- to_seq_fun. apply Σ_factor_seq_l.
Qed.

Lemma Σ_factor_seq_r_fun : forall l f0 c, Σ l (f0 _f;f_ (fun _ => c )) =R= Σ l f0 _;_ c.
Proof.
intros. rewrite <- to_seq_fun. apply Σ_factor_seq_r.
Qed.


(*Rules for rewriting functions*)
Lemma Σ_distr_l_fun : forall f0 f1 f2, f0  _f;f_ (f1 _f+f_ f2) =F= f0 _f;f_ f1 _f+f_ f0 _f;f_ f2.
Proof.
intros. rewrite <- to_plus_fun. rewrite <- to_seq_fun.
symmetry. repeat rewrite <- to_seq_fun. rewrite <- to_plus_fun.
unfold fun_eq. intros. auto_rwd_eqDB.
Qed.


Lemma Σ_distr_par_l_fun : forall f0 f1 f2, f0  _f*f_ (f1 _f+f_ f2) =F= f0 _f*f_ f1 _f+f_ f0 _f*f_ f2.
Proof.
intros. rewrite <- to_plus_fun. repeat rewrite <- to_par_fun.
rewrite <- to_plus_fun. unfold fun_eq.  auto with eqDB.
Qed.

Lemma Σ_distr_par_r_fun : forall f0 f1 f2, (f0 _f+f_ f1)  _f*f_ f2 =F= f0 _f*f_ f2 _f+f_ f1 _f*f_ f2.
Proof.
intros. rewrite <- to_plus_fun. repeat rewrite <- to_par_fun.
rewrite <- to_plus_fun. unfold fun_eq. intros.  rewrite c_par_distr_r. reflexivity.
Qed.




Lemma Σ_seq_assoc_left_fun : forall f0 f1 f2 , f0 _f;f_ (f1 _f;f_ f2) =F= (f0 _f;f_ f1) _f;f_ f2.
Proof.
intros. symmetry. rewrite <- (to_seq_fun f0). rewrite <- to_seq_fun.
rewrite <- (to_seq_fun f1). rewrite <- to_seq_fun. unfold fun_eq.
auto with eqDB.
Qed.

Lemma Σ_seq_assoc_right_fun : forall f0 f1 f2 ,  (f0 _f;f_ f1) _f;f_ f2 =F= f0 _f;f_ (f1 _f;f_ f2).
Proof.
intros. symmetry. apply Σ_seq_assoc_left_fun.
Qed.

Lemma o_seq_comm_fun : forall c f, (f _f;f_ (fun _ : EventType => o c)) =F= (fun _ : EventType => o c) _f;f_ f.
Proof.
intros. repeat rewrite <- to_seq_fun. unfold fun_eq.
intros. destruct (o_destruct c); rewrite H; auto_rwd_eqDB.
Qed.



Hint Rewrite Σ_distr_l_fun Σ_plus_decomp_fun Σ_factor_seq_l_fun Σ_factor_seq_r_fun Σ_seq_assoc_left_fun
             Σ_distr_par_l_fun Σ_distr_par_r_fun o_seq_comm_fun : funDB.


Lemma derive_unfold_seq : forall c1 c2, 
o c1 _+_ Σ alphabet (fun a : EventType => Event a _;_ a \ c1) =R= c1 ->
o c2 _+_ Σ alphabet (fun a : EventType => Event a _;_ a \ c2) =R= c2 -> 
o (c1 _;_ c2) _+_ 
Σ alphabet (fun a : EventType => Event a _;_ a \ (c1 _;_ c2)) =R=
c1 _;_ c2.
Proof.
intros. rewrite <- H at 2. rewrite <- H0 at 2.
autorewrite with funDB eqDB.
eq_m_left. 
rewrite Σ_seq_assoc_right_fun. rewrite Σ_factor_seq_l_fun.
rewrite <- H0 at 1.
autorewrite with eqDB funDB.
rewrite c_plus_assoc.
rewrite (c_plus_comm (Σ _ _ _;_  Σ _ _)).
eq_m_right.
Qed.

Lemma rewrite_in_fun : forall f0 f1, f0 =F= f1 -> (fun a => f0 a) =F= (fun a => f1 a).
Proof.
intros. unfold fun_eq in*. auto.
Qed.

Lemma rewrite_c_in_fun : forall (c c' : Contract) , c =R= c' -> (fun _ : EventType => c) =F= (fun _ : EventType => c').
Proof.
intros. unfold fun_eq. intros. auto. 
Qed.

Lemma fun_neut_r : forall f, f _f*f_ (fun _ => Success) =F= f.
Proof.
intros. rewrite <- to_par_fun. unfold fun_eq. intros.
auto_rwd_eqDB.
Qed.

Lemma fun_neut_l : forall f, (fun _ => Success) _f*f_ f =F= f.
Proof.
intros. rewrite <- to_par_fun. unfold fun_eq. intros.
auto_rwd_eqDB.
Qed.

Lemma fun_Failure_r : forall f, f _f*f_ (fun _ => Failure) =F= (fun _ => Failure).
Proof.
intros. rewrite <- to_par_fun. unfold fun_eq. intros.
auto_rwd_eqDB.
Qed.

Lemma fun_Failure_l : forall f, (fun _ => Failure) _f*f_ f =F= (fun _ => Failure).
Proof.
intros. rewrite <- to_par_fun. unfold fun_eq. intros.
auto_rwd_eqDB.
Qed.

Hint Rewrite fun_neut_r fun_neut_l fun_Failure_r fun_Failure_l : funDB.

Lemma o_seq_comm_fun3: forall c1 c2, 
Σ alphabet (Event _f;f_ ((fun a : EventType => a \ c1) _f*f_ (fun _ : EventType => o c2))) =R=
Σ alphabet (Event _f;f_ ((fun a : EventType => a \ c1))) _||_ o c2. 
Proof.
intros. destruct (o_destruct c2);
rewrite H; autorewrite with funDB eqDB; reflexivity.
Qed.

Lemma o_seq_comm_fun4: forall c1 c2,
Σ alphabet (Event _f;f_ ((fun _ : EventType => o c1) _f*f_ (fun a : EventType => a \ c2))) =R=
o c1 _||_ Σ alphabet (Event _f;f_ (fun a : EventType => a \ c2)).
Proof.
intros. destruct (o_destruct c1);
rewrite H; autorewrite with funDB eqDB; reflexivity.
Qed.


Hint Rewrite to_seq_fun to_plus_fun to_par_fun : funDB.


Definition Σ_fun (f : EventType -> EventType -> Contract) := fun a  => Σ alphabet (f a).

Lemma to_Σ_fun : forall f, (fun a : EventType => Σ alphabet (f a)) =F= Σ_fun f.
Proof.
intros. unfold Σ_fun. reflexivity.
Qed.


Definition app a (f : EventType -> Contract) := f a.

Lemma to_app : forall f a, f a = app a f.
Proof.
intros. unfold app. reflexivity.
Qed.

Opaque app.

Add Parametric Morphism a : (app a) with
signature fun_eq ==>  c_eq as afun_eq_par_morphism.
Proof.
intros. repeat rewrite <- to_app. unfold fun_eq in *. intros. auto with eqDB.
Qed.


Lemma o_seq_comm_fun_fun : forall c1 c2 a,
(fun a1 : EventType => (Event _f;f_ (fun a0 : EventType => a0 \ c1)) a _||_ (Event _f;f_ (fun a0 : EventType => a0 \ c2)) a1) =F=
(fun a1 : EventType => (Event a _;_ a \ c1) _||_ Event a1 _;_ a1 \ c2).
Proof.
intros. unfold fun_eq. intros. repeat rewrite to_app.
repeat rewrite <- to_seq_fun.
 apply c_par_ctx; now rewrite <- to_app.
Qed.

Lemma o_seq_comm_fun_fun2 : forall c1 c2 a,
(fun a1 : EventType => (Event a _;_ a \ c1) _||_ Event a1 _;_ a1 \ c2) =F=
(fun a1 : EventType => (Event a _;_ (a \ c1 _||_ Event a1 _;_ a1 \ c2))) _f+f_ (fun a1 => Event a1 _;_ (Event a _;_ a \ c1 _||_ a1 \ c2)).
Proof.
intros. rewrite <- to_plus_fun. unfold fun_eq. intros.
auto_rwd_eqDB.
Qed.




Lemma derive_unfold_par : forall c1 c2, 
o c1 _+_ Σ alphabet (fun a : EventType => Event a _;_ a \ c1) =R= c1 ->
o c2 _+_ Σ alphabet (fun a : EventType => Event a _;_ a \ c2) =R= c2 -> 
o (c1 _||_ c2) _+_ 
Σ alphabet (fun a : EventType => Event a _;_ a \ (c1 _||_ c2)) =R=
c1 _||_ c2.
Proof.
intros;simpl.
rewrite <- H at 2. rewrite <- H0 at 2.
rewrite to_seq_fun in *. autorewrite with funDB eqDB.
eq_m_left.
rewrite <- (rewrite_c_in_fun H). rewrite <- (rewrite_c_in_fun H0).
autorewrite with funDB eqDB.
rewrite o_seq_comm_fun3.
rewrite o_seq_comm_fun4.
repeat rewrite <- c_plus_assoc.
rewrite (c_plus_comm _ (_ _||_ o c2)) .
eq_m_left. rewrite (c_plus_comm). 
eq_m_left. rewrite Σ_par_ΣΣ.
symmetry. 
rewrite rewrite_in_fun. 2: { unfold fun_eq. intros. rewrite o_seq_comm_fun_fun.
                             rewrite o_seq_comm_fun_fun2.
    rewrite Σ_plus_decomp_fun at 1. eapply c_refl. }
rewrite Σ_split_plus. rewrite c_plus_comm.
apply c_plus_ctx.
- rewrite ΣΣ_prod_swap. apply c_eq_Σ_morphism.
 
rewrite <- to_par_fun.
repeat rewrite <- to_seq_fun.
unfold fun_eq. intros.
rewrite Σ_factor_seq_l. apply c_seq_ctx. reflexivity.
repeat rewrite <- Σ_factor_par_r.
apply c_par_ctx; auto with eqDB.
- apply c_eq_Σ_morphism. rewrite <- to_par_fun.
repeat rewrite <- to_seq_fun. unfold fun_eq. intros.
rewrite Σ_factor_seq_l. apply c_seq_ctx;auto with eqDB. 
repeat rewrite Σ_factor_par_l.
apply c_par_ctx; auto with eqDB.

Qed.

Lemma derive_unfold : forall c, o c _+_ Σ alphabet (fun a : EventType => Event a _;_ a \ c) =R= c.
Proof.
induction c;intros.
- unfold o; simpl. autorewrite with funDB eqDB using reflexivity.
- unfold o. simpl. autorewrite with funDB eqDB. reflexivity. 
- unfold o;simpl. autorewrite with funDB eqDB.
  rewrite rewrite_in_fun. 2: { instantiate (1:= (fun _ => Event e) _f;f_ (fun a : EventType => if EventType_eq_dec e a then Success else Failure)).
  repeat rewrite <- to_seq_fun. unfold fun_eq. intros. eq_event_destruct.
  subst. reflexivity. auto_rwd_eqDB. }
  rewrite Σ_factor_seq_l_fun. rewrite Σ_alphabet. auto_rwd_eqDB.
- simpl;auto_rwd_eqDB.
  rewrite <- IHc1 at 2. rewrite <- IHc2 at 2. autorewrite with funDB eqDB.
  repeat rewrite <- c_plus_assoc. eq_m_right. eq_m_left.
- auto using derive_unfold_seq.
- auto using derive_unfold_par.
Qed.


Lemma plus_norm_c_eq : forall c, plus_norm c =R= c.
Proof.
intros. funelim (plus_norm c). stuck_tac.
- symmetry. auto using Stuck_eq_Failure.
- rewrite <- (derive_unfold c) at 2. eq_m_left.
  apply c_eq_Σ_morphism. unfold fun_eq. intros. rewrite H;auto. reflexivity.
Qed.




Lemma Sequential_Σ : forall (A:Type) (l : list A) f, (forall a, In a l -> Sequential (f a)) -> Sequential (Σ l f).
Proof.
induction l;intros; auto with eqDB.
simpl. constructor. auto using in_eq.
apply IHl. intros. apply H. simpl. now right. 
Qed.

(*************Completeness = rewrite to normal form + appeal to CSL_core ***********)

Lemma plus_norm_Sequential : forall c, Sequential (plus_norm c).
Proof.
intros. funelim (plus_norm c). stuck_tac.
- constructor. 
- constructor. 
  * destruct (o_destruct c); rewrite H0; auto with eqDB.
  * apply Sequential_Σ. intros. constructor. constructor. auto.
Qed.

Lemma c_eq_completeness : forall (c0 c1 : Contract),(forall s : Trace, s (:) c0 <-> s (:) c1) ->  c0 =R= c1.
Proof.
intros. rewrite <- plus_norm_c_eq. rewrite <- (plus_norm_c_eq c1).
pose proof (plus_norm_Sequential c0). pose proof (plus_norm_Sequential c1).
apply translate_aux_sequential in H0.
apply translate_aux_sequential in H1. destruct_ctx.
pose proof c_eq_soundness (plus_norm_c_eq c0).
setoid_rewrite <- H2 in H.
pose proof c_eq_soundness (plus_norm_c_eq c1).
setoid_rewrite <- H3 in H.
eapply c_core;eauto. apply CSLEQ.c_eq_completeness.
setoid_rewrite translate_aux_spec in H; eauto.
Qed.















 
