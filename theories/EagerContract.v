Require Import CSL.Contract.
Require Import Lists.List.
Import ListNotations.

Inductive Tau : Contract -> Contract -> Prop :=
 | TPlusL c c' : Tau (c _+_ c') c
 | TPlusR c c' : Tau (c _+_ c') c'
 | TSeqSuc c : Tau (Success _;_ c) c
 | TSeqStep c c0 c1 (H0: Tau c0 c1): Tau (c0 _;_ c) (c1 _;_ c).
Hint Constructors Tau : core.


Inductive EDerive : Contract -> EventType -> Contract -> Prop :=
 | ESuccess e : EDerive Success e Failure
 | EFailure e : EDerive Failure e Failure
 | EEventS e : EDerive (Event e) e Success
 | EEventF e0 e (H0: e0 <> e) : EDerive (Event e0) e Failure
 | ESeqStep e c c0 c1 (H0: EDerive c0 e c1): EDerive (c0 _;_ c) e (c1 _;_ c)
 | ETauStep e c0 c0' c1 (H0: Tau c0 c0') (H1: EDerive c0' e c1) : EDerive c0 e c1.
Hint Constructors EDerive : core.

Lemma Tau_soundness : forall (c0 c1 : Contract), Tau c0 c1 -> (forall s, s ==~ c1 -> s ==~ c0).
Proof.
intros. generalize dependent s. induction H;intros;auto.
- rewrite <- (app_nil_l s). auto. 
- inversion H0. constructor; auto.
Qed.

Lemma EDerive_soundness : forall (c0 c1 : Contract)(e : EventType), EDerive c0 e c1 -> (forall s, s ==~ c1 -> s ==~ c0 / e).
Proof.
intros. generalize dependent s. induction H;intros;simpl;try solve [inversion H0].
- destruct (eq_event_dec e e). auto. contradiction.
- inversion H1.
- destruct (nu c0) eqn:Heqn.
  * inversion H0. apply MPlusL. constructor;auto. 
  * inversion H0.  constructor;auto. 
- apply IHEDerive in H1. rewrite <- derive_spec_comp. rewrite <- derive_spec_comp in H1.
  apply (Tau_soundness _ _ H0). assumption.
Qed.

Ltac rewrite_forall l := exists l; split; try (rewrite Forall_forall; intros; inversion H; subst; auto; inversion H0).

Inductive TauSteps : Contract -> Contract -> Prop :=
 | TauNone c : TauSteps c c
 | TauMore c0 c1 c2 (H0: Tau c0 c1) (H1:TauSteps c1 c2) : TauSteps c0 c2.
Hint Constructors TauSteps : core.

Lemma TauStepsSeq : forall (c0 c1 c : Contract), TauSteps c0 c1 -> TauSteps (c0 _;_ c) (c1 _;_ c).
Proof.
intros. generalize dependent c. induction H;intros.
- constructor.
- apply TauMore with (c1 _;_ c);eauto.
Qed.

Lemma TauStepTrans : forall (c0 c1 c2 : Contract), TauSteps c0 c1 -> TauSteps c1 c2 -> TauSteps c0 c2.
Proof. intros. generalize dependent c2. induction H;intros;eauto. Qed.


Lemma TauSteps_Nu : forall (c : Contract), Nu c -> TauSteps c Success.
Proof. intros. induction H;intros;eauto. apply TauStepTrans with (Success _;_ c1);eauto using TauStepsSeq. Qed.


Lemma TauSteps_EDerive : forall (c0 c1 c2 : Contract)(e : EventType), TauSteps c0 c1 -> EDerive c1 e c2 -> EDerive c0 e c2.
Proof. intros. induction H.
- assumption.
- apply ETauStep with c1;auto.
Qed.

Lemma EDerive_completeness : forall (c c' : Contract)(e : EventType), Derive c e c' -> exists (l : list Contract), 
Forall (EDerive c e) l /\ (forall s, s ==~ c'-> s ==~ plus_fold l).
Proof.
intros. induction H.
- rewrite_forall [Failure]. intros. inversion H.
- rewrite_forall [Failure]. intros. inversion H.
- rewrite_forall [Success]. intros. inversion H. simpl. auto.
- rewrite_forall [Failure]. rewrite Forall_forall. intros. inversion H. subst. auto. inversion H1.
  intros. inversion H. 
- destruct IHDerive1 as [l1 [P1 P2]]. destruct IHDerive2 as [l2 [P3 P4]].
   exists (l1++l2). split.
  * rewrite Forall_forall in *. intros. apply in_app_or in H1 as [H1 | H1].
    ** eapply ETauStep. eapply TPlusL. eauto.
    ** eapply ETauStep. eapply TPlusR. eauto.
  * intros. rewrite plus_fold_app. inversion H1;auto.
- destruct IHDerive1 as [l1 [P1 P2]]. destruct IHDerive2 as [l2 [P3 P4]].
  exists (l2 ++ (map (fun c => c _;_ c1) l1)). split.
  * rewrite Forall_forall. intros. apply in_app_or in H2 as [H2 | H2].
    ** rewrite Forall_forall in P3. apply TauSteps_Nu in H0. apply TauSteps_EDerive with (Success _;_ c1). 
      *** apply TauStepsSeq. assumption.
      *** eauto.
    ** rewrite in_map_iff in H2. destruct H2 as [c [P5 P6]].
       subst. constructor. rewrite Forall_forall in P1. auto.
  * intros. rewrite plus_fold_app. inversion H2;subst.
    ** inversion H5. subst. apply MPlusR. apply P2 in H7. rewrite in_plus_fold in H7.
       destruct H7 as [c' [P9 P10]]. rewrite in_plus_fold. exists (c' _;_ c1). split.
      *** rewrite in_map_iff. exists c'. split. reflexivity. assumption.
      *** auto.
    ** apply MPlusL. auto.
- destruct IHDerive as [l [P1 P2]]. exists (map (fun c => c _;_ c1) l). split.
  * rewrite Forall_forall in *. intros. rewrite in_map_iff in H1.
    destruct H1 as [c' [P3 P4]]. subst. auto.
  * intros. inversion H1. subst. rewrite in_plus_fold.
    apply P2 in H5. rewrite in_plus_fold in H5. destruct H5 as [c' [P3 P4]].
    exists (c' _;_ c1). rewrite in_map_iff. split.
    ** exists c'. split. reflexivity. assumption.
    ** auto.
Qed.

(*Another representation of eager contract derivative is shown to be equivalent to the one above*)
Inductive ETauDerive : Contract -> option EventType -> Contract -> Prop :=
 | ETPlusL c c' : ETauDerive (c _+_ c') None c
 | ETPlusR c c' : ETauDerive (c _+_ c') None c'
 | ETSeqSuc c : ETauDerive (Success _;_ c) None c
 | ETSuccess e : ETauDerive Success (Some e) Failure
 | ETFailure e : ETauDerive Failure (Some e) Failure
 | ETEventS e : ETauDerive (Event e) (Some e) Success
 | ETEventF e0 e (H0: e0 <> e) : ETauDerive (Event e0) (Some e) Failure
 | ETSeqStep o c c0 c1 (H0: ETauDerive c0 o c1): ETauDerive (c0 _;_ c) o (c1 _;_ c)
 | ETTauStep e c0 c0' c1 (H0: ETauDerive c0 None c0') (H1: ETauDerive c0' (Some e) c1) : ETauDerive c0 (Some e) c1.
Hint Constructors ETauDerive : core.

Lemma Tau_EtauDerive : forall (c0 c1 : Contract), Tau c0 c1 <-> ETauDerive c0 None c1.
Proof. intros. split;intros.
- induction H;eauto.
- generalize dependent c1. induction c0;intros; inversion H;subst;eauto.
Qed.

Lemma EDerive_EtauDerive : forall (c0 c1 : Contract)(e : EventType), EDerive c0 e c1 <-> ETauDerive c0 (Some e) c1.
Proof. intros. split ; intros. 
- induction H;eauto. rewrite Tau_EtauDerive in H0. eauto.
- remember (Some e). induction H; try discriminate;eauto.
  * inversion Heqo. constructor.
  * inversion Heqo. subst. auto.
  * inversion Heqo. subst. rewrite <- Tau_EtauDerive in H. eauto. 
Qed.