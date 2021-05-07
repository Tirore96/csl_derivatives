Require Import CSL.Parallel.Contract CSL.Parallel.TranslationOnly.  
Require Import Lists.List Bool.Bool Bool.Sumbool Setoid Coq.Arith.PeanoNat.
From Equations Require Import Equations.
Require Import micromega.Lia.
(** printing =~ %$=\sim$% *)

(** printing _+_ %$+$% *)

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
         | [ H: _ =~ Failure |- _ ] => inversion H
         | [ H: ?s =~ _ _+_ _ |- _ ] => inversion H; clear H
         | [ H: ?s =~ _ _;_ _ |- _ ] => inversion H; clear H
         | [ H: ?s =~ _ _*_ _ |- _ ] => inversion H; clear H
         | [ H: [?x] =~ Event _ |- _ ] => fail
         | [ H: ?s =~ Event _ |- _ ] => inversion H; subst
         | [ H: [] =~ Success |- _ ] => fail
         | [ H: _ =~ Success |- _ ] => inversion H; clear H

         end); option_inversion; auto with cDB.

Ltac core_inversion := option_inversion;CSLEQ.c_inversion.

Lemma translate_aux_spec : forall (c : Contract)(c' : CSLC.Contract),translate_aux c = Some c' -> (forall s, s =~ c <-> CSLC.Matches_Comp s c').
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

| c_par_assoc c0 c1 c2 : (c0 _*_ c1) _*_ c2 =R= c0 _*_ (c1 _*_ c2)
| c_par_neut c : c _*_ Success =R= c 
| c_par_comm c0 c1: c0 _*_ c1 =R= c1 _*_ c0
| c_par_failure c : c _*_ Failure =R= Failure   
| c_par_distr_l c0 c1 c2 : c0 _*_ (c1 _+_ c2) =R= (c0 _*_ c1) _+_ (c0 _*_ c2)

| c_par_event e0 e1 c0 c1 : Event e0 _;_ c0 _*_ Event e1 _;_ c1 =R= Event e0 _;_ (c0 _*_ (Event e1 _;_ c1)) _+_ Event e1 _;_ ((Event e0 _;_ c0) _*_ c1)

| c_refl c : c =R= c
| c_sym c0 c1 (H: c0 =R= c1) : c1 =R= c0
| c_trans c0 c1 c2 (H1 : c0 =R= c1) (H2 : c1 =R= c2) : c0 =R= c2
| c_plus_ctx c0 c0' c1 c1' (H1 : c0 =R= c0') (H2 : c1 =R= c1') : c0 _+_ c1 =R= c0' _+_ c1'
| c_seq_ctx c0 c0' c1 c1' (H1 : c0 =R= c0') (H2 : c1 =R= c1') : c0 _;_ c1 =R= c0' _;_ c1'
| c_par_ctx c0 c0' c1 c1' (H1 : c0 =R= c0') (H2 : c1 =R= c1') : c0 _*_ c1 =R= c0' _*_ c1'
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


Lemma cons_app : forall (A: Type) (a : A)(l : list A), a::l = [a]++l.
Proof. auto.
Qed.

Lemma event_seq : forall s e0 c0 e1 c1, s =~ (Event e0 _;_ c0) _*_ (Event e1 _;_ c1) <-> 
s =~ Event e0 _;_ (c0 _*_ (Event e1 _;_ c1)) _+_ Event e1 _;_ ((Event e0 _;_ c0) _*_ c1).
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

Lemma c_eq_soundness : forall (c0 c1 : Contract), c0 =R= c1 -> (forall s : Trace, s =~ c0 <-> s =~ c1).
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


Lemma Matches_plus_comm : forall c0 c1 s, s =~ c0 _+_ c1 <-> s =~ c1 _+_ c0.
Proof. auto using c_eq_soundness  with eqDB. Qed.

Lemma Matches_plus_neut_l : forall c s, s =~ Failure _+_ c <-> s =~ c.
Proof. intros. rewrite Matches_plus_comm. auto using c_eq_soundness  with eqDB. Qed.

Lemma Matches_plus_neut_r : forall c s, s =~ c _+_ Failure <-> s =~ c.
Proof. auto using c_eq_soundness  with eqDB. Qed.

Lemma Matches_seq_neut_l : forall c s, s =~ (Success _;_ c) <-> s =~ c.
Proof. auto using c_eq_soundness  with eqDB. Qed.

Lemma Matches_seq_neut_r : forall c s, s =~ c _;_ Success <-> s =~ c.
Proof. auto using c_eq_soundness  with eqDB. Qed.

Lemma Matches_seq_assoc : forall c0 c1 c2 s, s =~ (c0 _;_ c1) _;_ c2  <-> s =~ c0 _;_ (c1 _;_ c2).
Proof. auto using c_eq_soundness  with eqDB. Qed.

Hint Rewrite Matches_plus_neut_l 
             Matches_plus_neut_r 
             Matches_seq_neut_l
             Matches_seq_neut_r c_par_distr_l c_par_neut c_par_failure : eqDB.

Lemma c_plus_neut_l : forall c, Failure _+_ c =R= c.
Proof. intros. rewrite c_plus_comm. auto with eqDB.
Qed.

Lemma c_par_neut_l : forall c, Success _*_ c =R= c.
Proof. intros. rewrite c_par_comm. auto with eqDB.
Qed.

Lemma c_par_failure_l  : forall c, Failure _*_ c =R= Failure.
Proof. intros. rewrite c_par_comm. auto with eqDB.
Qed.

Lemma c_par_distr_r : forall c0 c1 c2, (c0 _+_ c1) _*_ c2 =R= (c0 _*_ c2) _+_ (c1 _*_ c2).
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

Fixpoint Σ (l : list Contract) : Contract :=
match l with
| [] => Failure
| c ::l => c _+_ (Σ l)
end.

(*Maybe not needed*)
Lemma Σ_app : forall (l1 l2 : list Contract), 
Σ (l1 ++ l2) =R= (Σ l1) _+_ (Σ l2).
Proof.
induction l1;intros;simpl;auto_rwd_eqDB.
rewrite IHl1. now rewrite c_plus_assoc.
Qed.

(*Not used in this file, maybe used in decision procedure*)
Lemma in_Σ : forall (l : list Contract)(s : Trace), s =~ Σ l <-> 
(exists c, In c l /\ s =~ c).
Proof. 
induction l;intros;simpl.
- split;intros. c_inversion. destruct_ctx. contradiction.
- split;intros. c_inversion. exists a. split;auto.
  rewrite IHl in H1. destruct_ctx. exists x. split;auto.
  destruct_ctx. inversion H. subst. auto with cDB.
  apply MPlusR. rewrite IHl. exists x. split;auto.
Qed.

Lemma in_Σ_idemp : forall l c, In c l -> c _+_ Σ l =R= Σ l.
Proof.
induction l;intros;simpl; auto_rwd_eqDB.
simpl in H;contradiction.
simpl in H. destruct H. subst. all: rewrite <- c_plus_assoc.
auto_rwd_eqDB. rewrite (c_plus_comm c). rewrite c_plus_assoc. 
apply c_plus_ctx;auto_rwd_eqDB.
Qed. 

Lemma incl_Σ_idemp : forall (l1 l2 : list Contract), incl l1 l2 -> Σ l2 =R= Σ (l1++l2).
Proof. 
induction l1;intros;simpl;auto_rwd_eqDB.
apply incl_cons_inv in H as [H0 H1].
rewrite <- IHl1;auto. now rewrite in_Σ_idemp;auto.
Qed.

Lemma Σ_app_comm : forall (l1 l2 : list Contract), Σ (l1++l2) =R= Σ (l2++l1).
Proof.
induction l1;intros;simpl. now rewrite app_nil_r.
repeat rewrite Σ_app. rewrite <- c_plus_assoc.
rewrite c_plus_comm. apply c_plus_ctx;auto_rwd_eqDB.
Qed.

Lemma incl_Σ_c_eq : forall (l1 l2 : list Contract), incl l1 l2 -> incl l2 l1-> Σ l1 =R= Σ l2.
Proof.
intros. rewrite (incl_Σ_idemp H). 
rewrite (incl_Σ_idemp H0). apply Σ_app_comm.
Qed.


Equations plus_norm (c : Contract) : (Contract) by  wf (con_size c) :=
plus_norm  c := if stuck_dec c then Failure
               else if nu c then Success _+_ Σ (map (fun e => (Event e) _;_ (plus_norm (e \ c))) alphabet)
                            else             Σ (map (fun e => (Event e) _;_ (plus_norm (e \ c))) alphabet).

Next Obligation. auto using not_stuck_derives. Defined.
Next Obligation. auto using not_stuck_derives. Defined.
Global Transparent plus_norm.


Lemma plus_norm_cons : forall (e:EventType)(s:Trace)(c:Contract),
(forall (e : EventType) (s : Trace), s =~ e \ c <-> s =~ plus_norm (e \ c)) ->
e :: s =~ c <-> e :: s =~ Σ (map (fun e0 : EventType => Event e0 _;_ plus_norm (e0 \ c)) alphabet).
Proof.
intros. repeat rewrite derive_spec_comp.
assert (HA: forall (l : list Contract)(e : EventType), e \ (Σ l) = Σ (map (fun c => e \ c) l)).
{ intros. induction l. - reflexivity. - simpl. f_equal. assumption. } rewrite HA. rewrite in_Σ.
rewrite map_map. rewrite H. split;intros.
- exists (Success _;_ (plus_norm (e \ c))). split.
  * rewrite in_map_iff. exists e. split;auto with eqDB. 
    simpl. destruct (EventType_eq_dec e e);[ reflexivity | contradiction ].
  * rewrite <- (app_nil_l s). constructor; auto with cDB.
- destruct H0 as [c0 [P0 P1]]. rewrite in_map_iff in P0. destruct P0 as [x [P3 P4]]. subst.
  simpl in P1. destruct (EventType_eq_dec x e).
  * inversion P1. inversion H3. subst. simpl. assumption.
  * inversion P1. inversion H3.
Qed.


Lemma plus_norm_nil : forall (c : Contract), ~([] =~ Σ (map (fun e0 : EventType => Event e0 _;_ plus_norm (e0 \ c)) alphabet)).
Proof.
intros. intro H. apply in_Σ in H as [c0 [P0 P1]]. apply in_map_iff in P0 as [e [P P3]]. 
subst. inversion P1. apply app_eq_nil in H0 as [H0 H00]. subst. inversion H1.
Qed.
 
Theorem plus_norm_spec : forall (c : Contract)(s : Trace), s =~ c <-> s =~ plus_norm c.
Proof.
intros. funelim (plus_norm c). destruct (stuck_dec c).
- apply Stuck_failure. assumption.
- destruct (nu c) eqn:Heqn.
  * destruct s.
    ** split;intros;auto with cDB. auto using Matches_Comp_nil_nu. 
    ** assert (HA: forall (c : Contract), e::s =~ Success _+_ c <-> e::s =~ c).
       { split; intros. inversion H0. inversion H3. assumption. auto with cDB. } rewrite HA.
       apply plus_norm_cons. auto.
  * destruct s.
    ** split;intros.
      *** rewrite Matches_Comp_iff_matchesb in H0. simpl in H0. 
          rewrite Heqn in H0. discriminate.
      *** apply plus_norm_nil in H0 as [].
    ** apply plus_norm_cons. auto.
Qed.

Lemma Stuck_eq_Failure : forall c, Stuck c -> c =R= Failure.
Proof.
intros. induction H;auto with eqDB.
- rewrite IHStuck1. rewrite IHStuck2. auto_rwd_eqDB.
- rewrite IHStuck. auto_rwd_eqDB.
- rewrite IHStuck. rewrite c_par_comm. auto_rwd_eqDB.
- rewrite IHStuck. auto_rwd_eqDB.
Qed.

Ltac stuck_tac := 
   match goal with
    | [ |- context[if stuck_dec ?c then _ else _ ]] => destruct (stuck_dec c)
        end.

Lemma plus_norm_Failure : plus_norm Failure =R= Failure.
Proof.
simp plus_norm. stuck_tac;auto_rwd_eqDB. inversion n.
Qed. 

Lemma Σ_Seq_Failure : forall es, Σ (map (fun e : EventType => Event e _;_ plus_norm Failure) es) =R= Failure.
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

Lemma map_ext_in_R :
  forall (A : Type)(f g:A->Contract) l, (forall a, In a l -> f a =R= g a) -> Σ (map f l) =R= Σ (map g l).
Proof.
induction l;intros;simpl;auto with eqDB.
apply c_plus_ctx. apply H. apply in_eq. apply IHl.
intros. apply H. simpl. now right.
Qed.

(*
Lemma ext_in_map_R :
  forall (A : Type)(f g:A->Contract) l, Σ (map f l) =R= Σ (map g l) -> forall a, In a l -> f a =R= g a.
Proof.
induction l;intros. simpl in H0. contradiction.
simpl in H0. destruct H0.
- subst. simpl in H. apply IHl. apply map_ext_in_R.
*)

Inductive Atom : Contract -> Prop :=
| AFailure : Atom Failure
| ASuccess : Atom Success.

Inductive NormalForm : Contract -> Prop :=
| NFF: NormalForm Failure
| NFS: NormalForm Success
| NFList es l (H1: forall a, In a l -> NormalForm a) : NormalForm (Σ (map (fun x => Event (fst x) _;_ snd x) (combine es l)))
| NFListS es l  (H1: forall a, In a l -> NormalForm a) : NormalForm (Success _+_ Σ (map (fun x => Event (fst x) _;_ snd x) (combine es l))).

Lemma Sequential_Σ : forall l, Forall Sequential l -> Sequential (Σ l).
Proof.
induction l;intros.
- simpl. constructor.
- simpl. rewrite Forall_forall in H. constructor.
  apply H. apply in_eq. apply IHl. rewrite <- Forall_forall in H.
  inversion H. auto.
Qed.


Lemma NormalForm_i_Sequential : forall c, NormalForm c -> Sequential c.
Proof.
intros. induction H;auto with eqDB.
- apply Sequential_Σ. rewrite Forall_forall in *. intros.
  rewrite in_map_iff in H0. destruct_ctx. subst. constructor.
  constructor. destruct x0. apply in_combine_r in H2. auto.
- constructor;auto with eqDB. apply Sequential_Σ. rewrite Forall_forall in *. intros.
  rewrite in_map_iff in H0. destruct_ctx. subst. constructor.
  constructor. destruct x0. apply in_combine_r in H2. auto.
Qed.

Lemma NormalForm_trans : forall c, NormalForm c -> exists c', translate_aux c = Some c'.
Proof.
intros. apply translate_aux_sequential. auto using NormalForm_i_Sequential.
Qed.


Lemma Σ_extend : forall l c, c _+_ Σ l = Σ (c :: l ).
Proof.
induction l;intros. auto. simpl. auto.
Qed.

Lemma decompose_map : 
forall es c, map (fun e => Event e _;_ plus_norm (e \ c)) es = map (fun x => (Event (fst x) _;_ snd x)) (combine es (map (fun e => plus_norm (e \ c) ) es)).
Proof.
induction es;intros.
- simpl. auto.
- simpl. rewrite IHes. auto.
Qed. 

Lemma plus_norm_NormalForm : forall c, NormalForm (plus_norm c).
Proof.
intros. funelim (plus_norm c). stuck_tac.
- constructor.
- destruct (nu c).
  * rewrite decompose_map. erewrite map_ext. eapply NFListS.
    intros. rewrite in_map_iff in H0. destruct_ctx.
    subst. auto. intros. destruct a. simpl. auto.
  * rewrite decompose_map. erewrite map_ext. eapply NFList.
    intros. rewrite in_map_iff in H0. destruct_ctx.
    subst. auto. intros. destruct a. simpl. auto.
Qed.

Lemma plus_norm_trans : forall c, exists c', translate_aux (plus_norm c) = Some c'.
Proof.
intros. eauto using plus_norm_NormalForm, NormalForm_trans.
Qed.
(*
Lemma plus_norm_core : forall c0 c1 c0' c1', tra c0 = Some c0' -> translate c1 = Some c1'
-> (forall s, s=~ c0 <-> s =~ c1 ) -> c0' =R= c1'.*)
(*
Lemma NormalFormEvent : forall l e , 
NormalForm (Σ (map (fun e0 => Event e0 _;_ plus_norm (if EventType_eq_dec e e0 then Success else Failure)) l)).
Proof.
intros.
induction l;intros.
- simpl. constructor. constructor.
- simpl. eq_event_destruct;subst.
  * rewrite Σ_extend. constructor. rewr con*)

(*
Lemma Σ_Seq_Event : forall alphabet0 e, (forall e', In e' alphabet0) ->
Σ
  (map (fun e0 : EventType => Event e0 _;_ plus_norm (if EventType_eq_dec e e0 then Success else Failure))
     alphabet0) =R= Event e.
Proof. intros.
eapply c_core;simpl;eauto. destruct e. simpl.
induction alphabet0;intros.
- simpl in H. contradiction.
- simpl. rewrite IHalphabet0.
intros.*)
(*
Fixpoint translate_aux_core c :=
match c with
| CSLC.Failure => CSLC.Failure
| CSLC.Event e => CSLEQ.Σ (map (fun e1 => CSLC.CSeq (CSLC.Event e1) (CSLC.derive e)(if EventType_eq_dec e e1 then CSLC.Success else CSLC.Failure)) alphabet0)).

Lemma translate_aux_Event : forall alphabet0 e x, 
translate_aux (Σ (map (fun e0 : EventType => Event e0 _;_ plus_norm (if EventType_eq_dec e e0 then Success else Failure)) alphabet0)) =
Some x -> CSLEQ.c_eq x
(CSLEQ.Σ (map (fun e1 => CSLC.CSeq (CSLC.Event e1) (if EventType_eq_dec e e1 then CSLC.Success else CSLC.Failure)) alphabet0)).
Proof.
induction alphabet0;intros. 
- simpl in*. inversion H;subst. constructor.
- simpl. eq_event_destruct;subst.
  * rewrite IHalphabet0. simpl. auto.
intros.
    Some x

Lemma trans_plus_norm_Event : forall e x, translate_aux (plus_norm (Event e)) = Some x -> CSLEQ.c_eq (CSLC.Event e) x.
Proof. 
intros. simp plus_norm in H. simpl in H.*)

Lemma derive_Success : forall e, e \ Success = Failure.
Proof.
intros. destruct e;auto.
Qed.
(*
Lemma Σ_event : forall l e c, (forall c', In c' (c::l) -> c =R= Failure \/ c =R= Event e) -> Σ (c::l) =R= Event e.
Proof.
induction l;intros.
simpl. auto_rwd_eqDB. specialize 
now right.
simpl. left. specialize IHl with e. simpl in H.
specialize H with a.
-
simpl.

*)

Lemma Σ_event : forall l e,
Σ (map (fun a => Event e _;_ (if EventType_eq_dec e a then Success else Failure)) l) =R= 
Event e _;_  Σ (map (fun a => (if EventType_eq_dec e a then Success else Failure)) l).
Proof.
induction l;intros.
- simpl. auto_rwd_eqDB.
- simpl. rewrite IHl. auto_rwd_eqDB.
Qed.

Lemma or_imp : forall (A B C : Prop), (A \/ B -> C) -> (A -> C) /\ (B -> C). 
Proof.
intros. split;auto.
Qed.
(*
Lemma Σ_Success : forall l, (exists c, In c l /\ c =R= Success) -> (forall c, In c l -> c =R= Success \/ c =R= Failure) -> Σ l =R= Success.
Proof.
induction l;intros.
- destruct_ctx. simpl in H. contradiction.
- destruct_ctx. simpl in *. destruct H.
  subst.
  * rewrite H1. rewrite IHl.
  * specialize H0 with a. apply or_imp in H0. destruct H0.
    destruct H0;auto. rewrite H0. auto_rwd_eqDB.
    rewrite H0. auto_rwd_eqDB.
  *

destruct H;subst.
    ** rewrite H1. auto_rwd_eqDB.
    ** specialize H0 with a. apply or_imp in H0. destruct H0.
       destruct H0;auto. rewrite H0.
  * destruct H;s ubst.
    ** rewrite H1. 
  rewrite IHl. auto_rwd_eqDB.  subst. simpl.*)


Lemma Σ_alphabet_or : forall alphabet0 e ,
 Σ (map (fun a : CSLC.EventType => if EventType_eq_dec e a then Success else Failure) alphabet0) =R= Success /\ In e alphabet0 \/
 Σ (map (fun a : CSLC.EventType => if EventType_eq_dec e a then Success else Failure) alphabet0) =R= Failure /\ ~(In e alphabet0).
Proof.
induction alphabet0;intros.
- simpl. now right.
- simpl. eq_event_destruct.
  * subst. edestruct IHalphabet0.
    ** destruct H. left. split.
       rewrite H. auto_rwd_eqDB. now left.
    ** destruct H. rewrite H.
       auto_rwd_eqDB.
  * edestruct IHalphabet0.
    ** destruct H. rewrite H. auto_rwd_eqDB.
    ** destruct H. rewrite H. auto_rwd_eqDB.
       right. split;auto with eqDB. intro H2. destruct H2.
       symmetry in H1. contradiction. contradiction.
Qed.

Lemma Σ_alphabet : forall e, Σ (map (fun a => if EventType_eq_dec e a then Success else Failure) alphabet) =R= Success.
Proof.
intros. destruct (Σ_alphabet_or alphabet e).
- destruct H. auto.
- destruct H. pose proof (in_alphabet e). contradiction.
Qed.

Lemma Σ_decompose_fun : forall (A: Type) l (P P' : A -> Contract),
Σ (map (fun a : A => P a _+_ P' a) l) =R= Σ (map (fun a : A => P a) l) _+_  Σ (map (fun a : A => P' a) l).
Proof.
induction l;intros.
- simpl. auto_rwd_eqDB.
- simpl. rewrite c_plus_assoc. rewrite c_plus_assoc. apply c_plus_ctx;auto with eqDB.
  rewrite (c_plus_comm (Σ _)).
  rewrite c_plus_assoc. apply c_plus_ctx;auto with eqDB. rewrite IHl.
  auto_rwd_eqDB.
Qed.

Lemma Σ_decompose_Seq : forall l (P: EventType -> Contract) c,
Σ (map (fun a  => P a _;_ c) l) =R= Σ (map (fun a  => P a) l) _;_ c.
Proof.
induction l;intros.
- simpl. auto_rwd_eqDB.
- simpl. auto_rwd_eqDB.
Qed.

Lemma Σ_decompose_Seq_l : forall l (P: EventType -> Contract) c,
Σ (map (fun a  => c _;_ P a) l) =R= c _;_ Σ (map (fun a  => P a) l).
Proof.
induction l;intros.
- simpl. auto_rwd_eqDB.
- simpl. auto_rwd_eqDB.
Qed.


Lemma Σ_par_distr_aux : forall l1 c (P' : EventType -> Contract),
c _*_ Σ (map (fun a0 : EventType => P' a0) l1) =R=
Σ (map (fun a' : EventType => c _*_ P' a') l1).
Proof.
induction l1;intros.
- simpl. auto_rwd_eqDB.
- simpl. rewrite <- IHl1. auto_rwd_eqDB.
Qed.

Lemma Σ_par_distr : forall l0 l1 (P P' : EventType -> Contract),
Σ (map (fun a  => P a) l0) _*_ Σ (map (fun a => P' a) l1) =R=
Σ (map (fun aa  => P (fst aa) _*_ P' (snd aa)) (list_prod l0 l1)).
Proof. 
induction l0;intros.
- simpl. auto_rwd_eqDB.
- simpl.  auto_rwd_eqDB.
  rewrite map_app. rewrite Σ_app. apply c_plus_ctx.
  * rewrite map_map. simpl. apply Σ_par_distr_aux.
  * auto_rwd_eqDB.
Qed. 


Lemma Σ_par_distr_aux_r : forall l1 c (P' : EventType -> Contract),
Σ (map (fun a0 : EventType => P' a0) l1) _*_ c =R=
Σ (map (fun a' : EventType => P' a' _*_ c) l1).
Proof.
induction l1;intros.
- simpl. auto_rwd_eqDB.
- simpl. rewrite <- IHl1. auto_rwd_eqDB.
Qed.
(*
Lemma Σ_par_distr_r : forall l0 l1 (P P' : EventType -> Contract),
Σ (map (fun a  => P a) l0) _*_ Σ (map (fun a => P' a) l1) =R=
Σ (map (fun aa  => P (fst aa) _*_ P' (snd aa)) (list_prod l0 l1)).
Proof. 
induction l0;intros.
- simpl. auto_rwd_eqDB.
- simpl.  auto_rwd_eqDB.
  rewrite map_app. rewrite Σ_app. apply c_plus_ctx.
  * rewrite map_map. simpl. apply Σ_par_distr_aux.
  * auto_rwd_eqDB.
Qed. *)

Definition o c := if nu c then Success else Failure.

Lemma o_plus : forall c0 c1, o (c0 _+_ c1) =R= o c0 _+_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;auto_rwd_eqDB.
Qed.

Lemma o_seq : forall c0 c1, o (c0 _;_ c1) =R= o c0 _;_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;auto_rwd_eqDB.
Qed.

Lemma o_par : forall c0 c1, o (c0 _*_ c1) =R= o c0 _*_ o c1.
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

Hint Rewrite o_true o_false : oDB.

Ltac eq_m_left := repeat rewrite c_plus_assoc; apply c_plus_ctx;
                  auto_rwd_eqDB.

Ltac eq_m_right := repeat rewrite <- c_plus_assoc; apply c_plus_ctx;
                  auto_rwd_eqDB.
(*
Lemma derive_eq : forall e c,
o c _+_ Event e _;_ e \ c =R= c  \/
e \ c =R= Failure.
Proof.
induction c;intros;simpl.
- left. auto_rwd_eqDB. 
- left. auto_rwd_eqDB.
- eq_event_destruct;auto_rwd_eqDB. subst. now left.
- destruct IHc1; destruct IHc2.
  * rewrite <- H at 3. rewrite <- H0 at 3. left.
    auto_rwd_eqDB. rewrite (c_plus_assoc _ (_ _;_ _)).
    rewrite (c_plus_comm (_ _;_ _) (o c2 _+_ _)).
    eq_m_left.
  * rewrite H0. auto_rwd_eqDB. left. rewrite c_plus_assoc. 
    rewrite (c_plus_comm _ (_ _;_ _)). rewrite <- c_plus_assoc.
    rewrite H. (o _)). 

    
    destruct (nu c1). simpl. 
    ** destruct (nu c2).
      *** auto_rwd_eqDB. rewrite c_plus_assoc. rewrite (c_plus_comm _ (Success _+_ _)).
          repeat rewrite <- (c_plus_assoc). rewrite c_plus_idemp.
          repeat rewrite c_plus_assoc.  
          apply c_plus_ctx. reflexivity. auto_rwd_eqDB.
      *** auto_rwd_eqDB.
    ** simpl. destruct (nu c2).
      *** auto_rwd_eqDB. rewrite c_plus_comm.
          repeat rewrite c_plus_assoc. apply c_plus_ctx.
          reflexivity. auto_rwd_eqDB.
      *** auto_rwd_eqDB.
  *
 _ Success) .
          rewrite c_plus_comm. specialize IHc1 with e. destruct IHc1.
  * left. setoid_rewrite <- H at 3. destruct_ctx. setoid_rewrite H0 at 1. 
  setoid_rewrite H at 1.*)
(*
Lemma test : forall alphabet0 c1 c2,
Σ (map (fun a : EventType => Event a _;_ (a \ c1 _*_ c2)) alphabet0) _+_ Σ (map (fun a : EventType => Event a _;_ (c1 _*_ a \ c2)) alphabet0) =R=
o c1 _*_ (Σ (map (fun a : EventType => Event a _;_ a \ c2) alphabet0) _+_
o c2 _*_ Σ (map (fun a : EventType => Event a _;_ a \ c1) alphabet0) _+_
Σ (map (fun a : EventType => Event a _;_ a \ c1) alphabet0)) _*_ Σ (map (fun a : EventType => Event a _;_ a \ c2) alphabet0) .
Proof.
induction alphabet0;intros.
- simpl. auto_rwd_eqDB.
- simpl. rewrite (c_plus_comm (Event a _;_ (c1 _*_ a \ c2))).
  repeat rewrite <- (c_plus_assoc _ (Σ _)) .
  rewrite (c_plus_assoc (_ _;_ _)). rewrite IHalphabet0.
  destruct (o_destruct c1); rewrite H in *.
  * destruct (o_destruct c2); rewrite H0 in *.
    ** repeat rewrite (c_par_neut_l).
       auto_rwd_eqDB.
       rewrite (c_par_comm (_ _+_ _)).
       auto_rwd_eqDB. 
       rewrite (c_plus_comm ((Σ _) _*_ (Σ _))).
       rewrite <- (c_plus_comm (_ _;_ (c1 _*_ a \ c2))).
Check c_par_event.
       rewrite <- c_plus_assoc.

    autorewrite with eqDB in *.
    **
   in H. rewrite IHalphabet0.*)

Lemma fold_Failure : forall l, Σ (map (fun _ : EventType => Failure) l) =R= Failure.
Proof.
induction l;intros. simpl. reflexivity.
simpl. rewrite IHl. autorewrite with eqDB. reflexivity.
Qed.

Lemma Σ_list_prod_aux : forall l1 a c1 c2,
Event a _;_ (a \ c1 _*_ Σ (map (fun a0 : EventType => Event a0 _;_ a0 \ c2) l1)) =R=
Σ (map (fun a0 : EventType * EventType => Event (fst a0) _;_ (fst a0 \ c1 _*_ Event (snd a0) _;_ snd a0 \ c2)) (map (fun y : EventType => (a, y)) l1)).
Proof.
induction l1;intros;simpl.
- auto_rwd_eqDB.
- rewrite map_map. simpl. 
  auto_rwd_eqDB. apply c_plus_ctx;auto with eqDB.
  rewrite IHl1. rewrite map_map. simpl. reflexivity.
Qed.


Lemma Σ_list_prod : forall l0 l1 c1 c2,
Σ (map (fun a => Event a _;_ (a \ c1 _*_ Σ (map (fun a0 : EventType => Event a0 _;_ a0 \ c2) l1))) l0) =R=
Σ (map (fun a : EventType * EventType => Event (fst a) _;_ (fst a \ c1 _*_ Event (snd a) _;_ snd a \ c2)) (list_prod l0 l1)).
Proof.
induction l0;intros;simpl.
- reflexivity.
- rewrite map_app. rewrite Σ_app. rewrite IHl0. apply c_plus_ctx;auto with eqDB.
  apply Σ_list_prod_aux.
Qed.




Lemma ΣΣ_prod : forall l0 l1 (P : EventType * EventType -> Contract), 
Σ (map (fun a  => P a) (list_prod l0 l1))  =R=
Σ (map (fun a0 => Σ (map (fun a1 => P (a0,a1)) l1)) l0).
Proof.
induction l0;intros.
- simpl. reflexivity.
- simpl. rewrite map_app. rewrite Σ_app.
  eq_m_left. rewrite map_map. reflexivity.
Qed. 
(*

Lemma Σ_plus_decompose
Σ (map (fun a0 : EventType => P (a, a0) _+_ Σ (map (fun a1 : EventType => P (a1, a0)) l0)) l1)
*)
Lemma ΣΣ_prod_swap : forall l0 l1 (P : EventType * EventType -> Contract), 
Σ (map (fun a0 => Σ (map (fun a1 => P (a0,a1)) l1)) l0)=R=
Σ (map (fun a0 => Σ (map (fun a1 => P (a1,a0)) l0)) l1).
Proof.
induction l0;intros.
- simpl. induction l1;intros;simpl;auto with eqDB. rewrite IHl1.
  auto with eqDB.
- simpl. rewrite Σ_decompose_fun. eq_m_left.
Qed.



Ltac rwd_in_map f := rewrite map_ext_in_R ; try instantiate (1:=f);intros; auto_rwd_eqDB.

Lemma derive_unfold : forall c, o c _+_ Σ (map (fun a : EventType => Event a _;_ a \ c) alphabet) =R= c.
Proof.
induction c;intros;simpl in *;auto_rwd_eqDB.
- rwd_in_map (fun (_ : EventType) => Failure).
  induction alphabet. simpl. auto_rwd_eqDB.
  simpl. rewrite IHl. auto_rwd_eqDB. 
- auto_rwd_eqDB. rwd_in_map (fun a => Event e _;_ (if EventType_eq_dec e a then Success else Failure)).
  * rewrite Σ_event. rewrite Σ_alphabet. auto_rwd_eqDB.
  * intros. eq_event_destruct;subst. reflexivity.
    auto_rwd_eqDB.
- rwd_in_map (fun a => Event a _;_ a \ c1  _+_  Event a _;_ a \ c2);
  intros; auto_rwd_eqDB.  rewrite Σ_decompose_fun. 
  rewrite <- c_plus_assoc. rewrite (c_plus_comm (o _)).
rewrite (c_plus_assoc (o _)).
  rewrite IHc1. rewrite (c_plus_comm _ c1).
  rewrite c_plus_assoc. rewrite IHc2. auto_rwd_eqDB.
- destruct (nu c1) eqn:Heqn.
  * rwd_in_map (fun a => Event a _;_ a \ c1 _;_ c2  _+_  Event a _;_ a \ c2);
    intros; auto_rwd_eqDB.  rewrite Σ_decompose_fun.
    rewrite Σ_decompose_Seq. rewrite <- IHc1 at 2.
    rewrite <- IHc2 at 2. rewrite <- IHc2 at 3. auto_rwd_eqDB. eq_m_left.
    apply o_true in Heqn. rewrite Heqn.
    auto_rwd_eqDB. rewrite (c_plus_comm (Σ _ _;_ Σ _ )).
    eq_m_right. 
  * apply o_false in Heqn. rewrite Heqn in*. autorewrite with eqDB in *.
    rwd_in_map (fun a => Event a _;_ a \ c1 _;_ c2);
    intros; auto_rwd_eqDB. rewrite Σ_decompose_Seq. 
    rewrite IHc1. reflexivity.
- auto_rwd_eqDB.
  rewrite (map_ext_in_R _ (fun a : EventType =>  ((Event a _;_ (a \ c1 _*_ o c2) _+_ Event a _;_ ( a \ c1 _*_Σ (map (fun a : EventType => Event a _;_ a \ c2) alphabet))) 
_+_ (Event a _;_ (o c1 _*_ a \ c2) _+_ Event a _;_ (Σ (map (fun a : EventType => Event a _;_ a \ c1) alphabet) _*_ a \ c2 )))));

  try solve [intros; rewrite <- c_distr_l; rewrite <- c_par_distr_l;  rewrite IHc2;
  rewrite <- c_distr_l; rewrite <- c_distr_l;
  rewrite <- c_par_distr_r; rewrite IHc1; reflexivity].
  rewrite <- IHc1 at 2.
  rewrite <- IHc2 at 2.
  auto_rwd_eqDB. repeat rewrite (c_par_comm (_ _+_ _)). auto_rwd_eqDB.
  rewrite c_plus_assoc. eq_m_left. 
repeat rewrite Σ_decompose_fun.
repeat rewrite <- c_plus_assoc. 
remember (Σ (map (fun a : EventType => Event a _;_ (a \ c1 _*_ Σ (map (fun a0 : EventType => Event a0 _;_ a0 \ c2) alphabet))) alphabet)) as a.
remember (Σ (map (fun a0 : EventType => Event a0 _;_ (Σ (map (fun a1 : EventType => Event a1 _;_ a1 \ c1) alphabet) _*_ a0 \ c2)) alphabet)) as b.
repeat rewrite c_plus_assoc. rewrite (c_plus_comm a).
repeat rewrite <- c_plus_assoc.
rewrite (c_plus_assoc _ b).
apply c_plus_ctx.
  * rewrite c_plus_comm. apply c_plus_ctx.
    ** destruct (o_destruct c1).
      *** rewrite H. auto_rwd_eqDB. apply map_ext_in_R;
          intros; auto_rwd_eqDB.
      *** rewrite H. auto_rwd_eqDB. 
          rewrite (map_ext_in_R _ (fun _ : EventType => Failure)).
          apply fold_Failure. intros. auto_rwd_eqDB.
    ** destruct (o_destruct c2).
      *** rewrite H. auto_rwd_eqDB. apply map_ext_in_R.
          intros. auto_rwd_eqDB.
      *** rewrite H. auto_rwd_eqDB. 
          rewrite (map_ext_in_R _ (fun _ : EventType => Failure)).
          apply fold_Failure. intros. auto_rwd_eqDB.
  * subst. rewrite Σ_par_distr.
rewrite (map_ext_in_R _ ((fun a : EventType * EventType =>  Event (fst a) _;_ (fst a \ c1 _*_ Event (snd a) _;_ snd a \ c2) _+_ 
Event (snd a) _;_ (Event (fst a) _;_ fst a \ c1 _*_ snd a \ c2))));
    intros; auto_rwd_eqDB. rewrite Σ_decompose_fun.
 rewrite c_plus_comm. repeat rewrite ΣΣ_prod;simpl. apply c_plus_ctx.
    ** apply map_ext_in_R. intros. rewrite Σ_decompose_Seq_l.
       rewrite <- Σ_par_distr_aux. reflexivity.
    ** pose proof (ΣΣ_prod_swap alphabet alphabet
(fun p => Event (snd p) _;_ (Event (fst p) _;_ (fst p) \ c1 _*_ (snd p) \ c2))).
       simpl in H. rewrite H. apply map_ext_in_R.
       intros. rewrite Σ_decompose_Seq_l. apply c_seq_ctx;auto with eqDB.
       rewrite Σ_par_distr_aux_r. reflexivity.
Qed.

(*
Lemma derive_unfold : forall c, (if nu c then Success else Failure) _+_ Σ (map (fun a : EventType => Event a _;_ a \ c) alphabet) =R= c.
Proof.
induction c;intros;simpl in *.
- rewrite (map_ext_in_R _ (fun _ => Failure)).
  induction alphabet. simpl. auto_rwd_eqDB.
  simpl. rewrite <- c_plus_assoc. rewrite (c_plus_comm Success).
  rewrite c_plus_assoc.
  rewrite IHl. auto_rwd_eqDB.
  intros. destruct a;simpl; auto_rwd_eqDB.
- rewrite (map_ext_in_R _ (fun _ => Failure)).
  induction alphabet. simpl. auto_rwd_eqDB.
  simpl. rewrite <- c_plus_assoc.
  rewrite c_plus_idemp. apply IHl. 
  intros. destruct a;simpl; auto_rwd_eqDB.
- auto_rwd_eqDB. 
 rewrite (map_ext_in_R _ (fun a => Event e _;_ (if EventType_eq_dec e a then Success else Failure))).
  * rewrite Σ_event. rewrite Σ_alphabet. auto_rwd_eqDB.
  * intros. eq_event_destruct;subst. reflexivity.
    auto_rwd_eqDB.
- rewrite (map_ext_in_R _ (fun a => Event a _;_ a \ c1  _+_  Event a _;_ a \ c2));
  intros; auto_rwd_eqDB.  rewrite Σ_decompose_fun.
  destruct (nu c1);simpl.
  * destruct (nu c2);simpl.
    ** rewrite <- (c_plus_idemp Success).
       rewrite c_plus_assoc. rewrite <- (c_plus_assoc _ (Σ _)).
       rewrite IHc1. rewrite (c_plus_comm c1). rewrite <- c_plus_assoc.
       rewrite IHc2. auto_rwd_eqDB.
    ** autorewrite with eqDB in IHc2. rewrite IHc2.
       rewrite <- c_plus_assoc. rewrite IHc1. reflexivity.
  * destruct (nu c2);simpl.
    ** autorewrite with eqDB in IHc1. rewrite IHc1.
       rewrite (c_plus_comm c1). rewrite <- c_plus_assoc.  rewrite IHc2.
       auto_rwd_eqDB. 
    ** autorewrite with eqDB in *. rewrite IHc1. rewrite IHc2. reflexivity.
- destruct (nu c1 && nu c2) eqn:Heqn.
  * apply andb_prop in Heqn. destruct Heqn. rewrite H in*.
    rewrite H0 in *.
    rewrite (map_ext_in_R _ (fun a => Event a _;_ a \ c1 _;_ c2  _+_  Event a _;_ a \ c2));
    intros; auto_rwd_eqDB.  rewrite Σ_decompose_fun.
    rewrite Σ_decompose_Seq. rewrite <- IHc1.
    rewrite <- IHc2. rewrite (c_distr_l (Success _+_ _)).
    repeat rewrite (c_distr_r). auto_rwd_eqDB.
    rewrite (c_plus_assoc Success). apply c_plus_ctx;auto with eqDB.
    rewrite c_plus_assoc. apply c_plus_ctx;auto with eqDB.
  * rewrite andb_false_iff in Heqn. destruct Heqn.
    ** rewrite H in*. rewrite (map_ext_in_R _ (fun a => Event a _;_ a \ c1 _;_ c2));
       intros; auto_rwd_eqDB. rewrite Σ_decompose_Seq. 
          autorewrite with eqDB in IHc1. rewrite IHc1. reflexivity.
    ** rewrite H in*. destruct (nu c1) eqn:Heqn.
      *** rewrite (map_ext_in_R _ (fun a => Event a _;_ a \ c1 _;_ c2  _+_  Event a _;_ a \ c2));
          intros; auto_rwd_eqDB.  rewrite Σ_decompose_fun.
          rewrite Σ_decompose_Seq. autorewrite with eqDB in IHc2.
          rewrite <- IHc1. auto_rwd_eqDB.
          rewrite <- IHc2. auto_rwd_eqDB.
      *** rewrite (map_ext_in_R _ (fun a => Event a _;_ a \ c1 _;_ c2));
          intros; auto_rwd_eqDB. rewrite Σ_decompose_Seq.
          autorewrite with eqDB in IHc1. rewrite IHc1. reflexivity.
- rewrite <- IHc1 at 2.
  rewrite <- IHc2 at 2.
  auto_rwd_eqDB. repeat rewrite (c_par_comm (_ _+_ _)). auto_rwd_eqDB.
  rewrite c_plus_assoc. apply c_plus_ctx.
  * destruct (nu c1); destruct (nu c2);simpl;auto_rwd_eqDB.
  *
  rewrite 
 destruct (nu c1 && nu c2) eqn:Heqn.
  * apply andb_prop in Heqn. destruct Heqn.
 rewrite H in*. 
    rewrite H0 in IHc2.
 Check c_par_event.
    rewrite (map_ext_in_R _ (fun a => Event a _;_ (a \ c1 _*_ c2)  _+_  Event a _;_ (c1 _*_ a \ c2)));
          intros; auto_rwd_eqDB.
 Check c_par_event. 
rewrite Σ_decompose_fun.
 Check c_par_event.
    rewrite <- IHc1.
    rewrite <-  rewrite <- (c_par_comm c2). auto_rwd_eqDB.
    rewrite <- IHc2. repeat rewrite (c_par_comm (_ _+_ _)).
    auto_rwd_eqDB. rewrite Σ_par_distr. 
 Check c_par_event.*)

Lemma plus_norm_c_eq : forall c, plus_norm c =R= c.
Proof.
intros. funelim (plus_norm c).
stuck_tac.
- symmetry. auto using Stuck_eq_Failure.
- destruct (nu c) eqn:Heqn.
  * rewrite map_ext_in_R. 2: { intros. rewrite H at 1;auto. eapply c_refl. }
 
  * reflexivity.
induction c;intros.
4: { simp plus_norm. stuck_tac.
  * inversion s.
    apply Stuck_eq_Failure in H2. apply Stuck_eq_Failure in H3.
    rewrite H2. rewrite H3. auto_rwd_eqDB.
  * simpl. destruct (nu c1 || nu c2) eqn:Heqn.
    **
- auto_rwd_eqDB. 
- auto_rwd_eqDB. 

Lemma plus_norm_c_eq : forall c, plus_norm c =R= c.
Proof.
induction c;intros.
4: { simp plus_norm. stuck_tac.
  * inversion s.
    apply Stuck_eq_Failure in H2. apply Stuck_eq_Failure in H3.
    rewrite H2. rewrite H3. auto_rwd_eqDB.
  * simpl. destruct (nu c1 || nu c2) eqn:Heqn.
    **
- auto_rwd_eqDB. 
- auto_rwd_eqDB. 

- destruct (plus_norm_trans (Event e)).
  eapply c_core;simpl;  eauto. symmetry. auto using trans_plus_norm_Event.


  apply trans_plus_norm_Event in H.
  pose proof (translate_aux_spec H). eapply NormalForm_trans. simp plus_norm. stuck_tac. symmetry. auto using Stuck_eq_Failure.
  simpl. pose proof in_alphabet. induction alphabet. 
  specialize H with Transfer. simpl in H. contradiction.
   simpl. rewrite IHl. eq_event_destruct;subst.
   auto_rwd_eqDB. auto_rwd_eqDB. rewrite e0 in e1. discriminate.
  * auto_rwd_eqDB.

 apply Stuck_eq_Failure.  simp plus_norm. auto with eqDB.

Section axiomatization.

  Hypothesis sum_rule : forall c, exists c', NormalForm c' /\ c =R= c'.

  Lemma c_eq_completeness : forall (c0 c1 : Contract),(forall s : Trace, s =~ c0 <-> s =~ c1) ->  c0 =R= c1.
  Proof.
  intros. destruct (sum_rule c0). destruct (sum_rule c1). destruct_ctx.
  pose proof c_eq_soundness H3. setoid_rewrite H4 in H. 
  pose proof c_eq_soundness H2. setoid_rewrite H5 in H.
  rewrite H3. rewrite H2.
  apply NormalForm_trans in H0. apply NormalForm_trans in H1. destruct_ctx. 
  eapply c_core. eauto. eauto. apply CSLEQ.c_eq_completeness.
  setoid_rewrite <- translate_aux_spec. eapply H. all: eauto.
  Qed.

End axiomatization.
 






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



(*
Lemma stuck_c_eq_Failure : forall c c', translate_aux c = Some c' -> Stuck c -> CSLEQ.c_eq CSLC.Failure c'.
Proof. Admitted.*)

Ltac core_tac := eapply c_core;simpl;eauto with eqDB.

Lemma stuck_c_eq_Failure : forall c, Stuck c -> Failure =R= c.
Proof.
intros. induction H; try solve [core_tac].
- rewrite <- IHStuck1. rewrite <- IHStuck2. core_tac.
- rewrite <- IHStuck.

Lemma plus_norm_eq : forall p, plus_norm p =R= p.
Proof. 
intros. funelim (plus_norm p). destruct (stuck_dec c).
- induction s.
  * eapply c_core;simpl;eauto with eqDB.
  * destruct (translate_aux c) eqn:Heqn.
  * apply stuck_c_eq_Failure in Heqn as H';auto. eapply c_core;simpl;eauto.
  *
    simpl. eauto. eapply Heqn. eauto.
    simpl. inversion s.



Theorem c_eq_complete : forall c0 c1, (forall s, s =~ c0 <-> s=~c1) -> c0 =R= c1.
Proof.
intros. rewrite <- plus_norm_eq. rewrite <- (plus_norm_eq c1).
destruct (correct_translation c0). destruct (correct_translation c1).
destruct_ctx. unfold translate in *.
 eapply c_core;eauto. apply CSLEQ.c_eq_completeness. 
 setoid_rewrite <- H3. setoid_rewrite <- H2. auto.
Qed.













Inductive NormalForm : list Contract -> Prop :=
| NF_nil : NormalForm []
| NF_cons e c l (H: NormalForm l) : NormalForm ((Event e _;_ c):: l).



Equations interleavings  (s0 s1: Trace) : (list Trace) by  wf ((length s0) + (length s1)) :=
interleavings [] s1 := [s1];
interleavings s0 [] := [s0];
interleavings (e0::s0') (e1::s1') := (map (fun s => e0::s) (interleavings s0' (e1::s1'))) ++ 
                                     (map (fun s => e1::s) (interleavings (e0::s0') s1')).
Next Obligation.  lia. Defined.

Theorem interleavings_i_interleave_fun : forall (s0 s1 s : Trace), In s (interleavings s0 s1) -> interleave_fun s0 s1 s.
Proof.
intros. funelim (interleavings s0 s1).
- simp interleavings in H. simpl in H. destruct H;try contradiction. subst. auto with cDB.
- simp interleavings in H. simpl in H. destruct H;try contradiction. subst. auto with cDB.
- simp interleavings in H1. apply in_app_or in H1. destruct H1.
  * rewrite in_map_iff in H1. destruct_ctx. apply H in H2. 
    subst. auto with cDB.
  * rewrite in_map_iff in H1. destruct_ctx. apply H0 in H2. 
    subst. auto with cDB.
Qed.

Lemma in_one : forall (A:Type) (a a0 : A), In a [a0] -> a = a0.
Proof.
intros. simpl in H. destruct H;try contradiction;auto.
Qed.

Lemma interleavings_nil_r : forall s, interleavings s []  = [s].
Proof.
induction s;intros; reflexivity.
Qed.

Lemma interleavings_one_l : forall (s : Trace)e,  In (e :: s) (interleavings [e] s).
Proof.
intros. funelim (interleavings [e] s).
-  simp interleavings. apply in_eq.
- rewrite <- Heqcall. apply in_or_app. left. rewrite in_map_iff.
  exists (e0::l0). split;auto. simp interleavings. apply in_eq.
Qed.

Lemma interleavings_one_r : forall (s : Trace)e,  In (e :: s) (interleavings s [e]).
Proof.
intros. funelim (interleavings s [e]).
-  simp interleavings. apply in_eq.
- rewrite <- Heqcall. apply in_or_app. right. rewrite in_map_iff.
  exists (e::l). split;auto. simp interleavings. apply in_eq.
Qed.

Lemma interleavings_extend_l : forall (s0 s1 s : Trace) e,  In s (interleavings s0 s1) ->
In (e::s) (interleavings (e::s0) s1).
Proof. 
intros. destruct s1. simp interleavings in*. rewrite interleavings_nil_r in *. 
apply in_one in H. subst. apply in_eq. 
simp interleavings. apply in_or_app. left. rewrite in_map_iff.
exists s. split;auto.
Qed.

Lemma interleavings_extend_r : forall (s0 s1 s : Trace) e,  In s (interleavings s0 s1) ->
In (e::s) (interleavings s0 (e::s1)).
Proof. 
intros. destruct s0. simp interleavings in*. apply in_one in H. subst.
apply in_eq. 
simp interleavings. apply in_or_app. right. rewrite in_map_iff.
exists s. split;auto.
Qed.

Theorem interleave_fun_i_interleavings : forall (s s0 s1: Trace), interleave_fun s0 s1 s
-> In s (interleavings s0 s1).
Proof.
induction s;intros. simpl in H. destruct H. subst. simpl. now left.
simpl in H. destruct s0.
- subst. simpl. now left.
- destruct H.
  * destruct H. subst. apply IHs in H0. auto using interleavings_extend_l.
  * destruct s1.
    ** simp interleavings. inversion H. apply in_eq.
    ** destruct H. subst. apply IHs in H0. auto using interleavings_extend_r.
Qed.

Theorem interleave_fun_iff_interleavings : forall (s s0 s1: Trace),
interleave_fun s0 s1 s <-> In s (interleavings s0 s1).
Proof. split; auto using interleave_fun_i_interleavings, interleavings_i_interleave_fun.
Qed.



Fixpoint L (c : Contract) : list Trace :=
match c with
| Success => [[]]
| Failure => []
| Event e => [[e]]
| c0 _+_ c1 => (L c0) ++ (L c1)
| c0 _;_ c1 => map (fun p => (fst p)++(snd p)) (list_prod (L c0) (L c1))
| c0 _*_ c1 => flat_map (fun p => interleavings (fst p) (snd p)) (list_prod (L c0) (L c1))
end.


Lemma Matches_member : forall (s : Trace)(c : Contract), s =~ c -> In s (L c). 
Proof.
intros. induction H ; simpl ; try solve [auto using in_or_app || auto using in_or_app ].
- rewrite in_map_iff. exists (s1,s2). rewrite in_prod_iff. split;auto.
- rewrite in_flat_map. exists (s1,s2). split.
  * rewrite in_prod_iff. split;auto.
  * simpl. rewrite <- interleave_fun_iff_interleavings. 
    now rewrite <- interl_iff_fun.
Qed.

Lemma member_Matches : forall (c : Contract)(s : Trace), In s (L c) -> s =~ c. 
Proof.
induction c;intros;simpl in*; try solve [ destruct H;try contradiction; subst; constructor].
- apply in_app_or in H. destruct H; auto with cDB.
- rewrite in_map_iff in H. destruct_ctx. destruct x.
  rewrite in_prod_iff in H0. destruct H0. simpl in H.
  subst. auto with cDB.
- rewrite in_flat_map in H. destruct_ctx.
  rewrite <- interleave_fun_iff_interleavings in H0. 
  destruct x. rewrite in_prod_iff in H. destruct H.
  simpl in*. rewrite <- interl_iff_fun in H0. eauto with cDB.
Qed.

Theorem Matches_iff_member : forall s c, s =~ c <-> In s (L c).
Proof.
split; auto using Matches_member,member_Matches.
Qed.

Lemma Matches_incl : forall (c0 c1 : Contract), (forall (s : Trace), s =~ c0 -> s =~ c1) -> 
incl (L c0) (L c1).
Proof.
intros. unfold incl. intros. rewrite <- Matches_iff_member in *. auto.
Qed.

Lemma comc_equiv_destruct : forall (c0 c1: Contract),(forall s : Trace, s =~ c0 <-> s =~ c1) <->
(forall s : Trace, s =~ c0 -> s =~ c1) /\ (forall s : Trace, s =~ c1 -> s =~ c0).
Proof.
 split ; intros.
- split;intros; specialize H with s; destruct H; auto.
- destruct H. split;intros;auto.
Qed.


Theorem Matches_eq_i_incl_and : forall (c0 c1 : Contract), (forall (s : Trace), s =~ c0 <-> s =~ c1) -> 
incl (L c0) (L c1) /\ incl (L c1) (L c0) .
Proof.
intros. apply comc_equiv_destruct in H. destruct H. split; auto using Matches_incl. 
Qed.




Fixpoint Π (s : Trace) :=
match s with
| [] => Success
| e::s' => (Event e) _;_ (Π s')
end.

Lemma Π_app : forall (l1 l2 : Trace), Π l1 _;_ Π l2 =R= Π (l1++l2).
Proof.
induction l1;intros;simpl; auto_rwd_eqDB.
rewrite <- IHl1. auto_rwd_eqDB.
Qed.

(*
Definition Π (l : list Trace) := Σ (map Π l).
Hint Unfold Π : eqDB.*)


Lemma Π_distr_aux : forall (ss : list Trace) (s : Trace), Π s _;_ (Σ (map Π ss)) =R=
 Σ (map (fun x => Π (fst x ++ snd x)) (map (fun y : list EventType => (s, y)) ss)).
Proof.
induction ss;intros;simpl;auto_rwd_eqDB.
apply c_plus_ctx;auto using Π_app.
Qed.

Lemma Π_distr_aux2 : forall c l0, c _;_ Σ (map Π l0) =R=
 Σ (map (fun x => c _;_ Π x) l0).
Proof.
induction l0;intros;simpl;auto_rwd_eqDB.
Qed.


(*
Lemma Π_distr2 : forall l0 l1,  Σ l0 _;_ Σ l1 =R=
 Σ (map (fun x => (fst x) _;_ (snd x)) (list_prod l0 l1)).
Proof.
induction l0;intros;simpl. auto_rwd_eqDB.
repeat rewrite map_app. rewrite Σ_app. rewrite <- IHl0.
auto_rwd_eqDB. rewrite map_map. simpl. 
apply c_plus_ctx; auto using Π_distr_aux2 with eqDB. 
Qed.*)

(*Mention in report*)


Lemma exchange : forall p q r s, 
 (p _*_ q) _;_ (r _*_ s) _+_ (p _;_ r) _*_ (q _;_ s) =R= (p _;_ r) _*_ (q _;_ s).
Proof. Admitted.

Lemma exchange2 : forall a b c, 
 a _*_ (b _;_ c) _+_ (a _*_ b) _;_ c =R=
 a _*_ (b _;_ c).
Proof. Admitted.


(*
Lemma Π_par_aux2 : forall (s0 s1 : Trace) e, Event e _;_ Π s0 _*_ Π s1 =R=
 Σ (map (fun x => Π (e::x)) (interleavings s0 s1)).
Proof.
intros. simpl. rewrite <- Π_distr_aux2. 
apply c_seq_ctx. auto with eqDB.*)

Lemma Σ_interleavings : forall (s0 s1 : Trace),
Σ (map Π (interleavings s0 s1)) =R= (Π s0) _*_ (Π s1).
Proof.
intros. funelim (interleavings s0 s1).
- simp interleavings. simpl. rewrite c_par_comm. auto_rwd_eqDB.
- rewrite interleavings_nil_r. simpl. auto_rwd_eqDB.
- simp interleavings. rewrite map_app. rewrite Σ_app.
  repeat rewrite map_map. clear Heqcall. simpl.
  repeat rewrite <- Π_distr_aux2. rewrite H.
  rewrite H0. simpl.

  remember ( Π l) as c. remember (Π l0) as d.
  now rewrite c_par_event.
Qed.


Lemma Π_distr : forall l0 l1,  Σ (map Π l0) _;_ Σ (map Π l1) =R=
 Σ (map (fun x => Π (fst x ++ snd x)) (list_prod l0 l1)).
Proof.
induction l0;intros;simpl. auto_rwd_eqDB.
repeat rewrite map_app. rewrite Σ_app. rewrite <- IHl0.
auto_rwd_eqDB. 
apply c_plus_ctx; auto using Π_distr_aux with eqDB. 
Qed.

(*


Lemma Σ_interleavings_aux : forall (s0 s1 : Trace) c,
Σ (map (fun x => c _;_ Π x) (interleavings s0 s1)) =R= c _;_ ((Π s0) _*_ (Π s1)).
Proof.
intros. funelim (interleavings s0 s1).
- simp interleavings. simpl. rewrite c_par_comm. auto_rwd_eqDB.
- rewrite interleavings_nil_r. simpl. auto_rwd_eqDB.
- simp interleavings. rewrite map_app.
  rewrite Σ_app. rewrite map_map.
  rewrite map_ext_in_R.
  * rewrite H. rewrite map_map. simpl. rewrite map_ext_in_R.
    ** rewrite H0. simpl.
  setoid_rewrite <- c_seq_assoc. rewrite H0.

 rewrite <- c_seq_neut. rewrite <- exchange. rewrite <- par_der. reflexivity. auto with eqDB. apply par_der.  rewrite simpl in H0. rewrite 
  rewrite map_map. simpl.
  rewrite <- H.
*)



Lemma Π_par_aux : forall (ss : list Trace) (s : Trace), Π s _*_ (Σ (map Π ss)) =R=
 Σ (map Π (flat_map (fun x => interleavings (fst x) (snd x)) (map (fun y : list EventType => (s, y)) ss))).
Proof.
induction ss;intros;simpl;auto_rwd_eqDB.
rewrite map_app. rewrite Σ_app. rewrite <- IHss.
rewrite c_par_distr_l. rewrite Σ_interleavings. auto with eqDB.
Qed.


Lemma Π_distr_par : forall l0 l1,  Σ (map Π l0) _*_ Σ (map Π l1) =R=
 Σ (map Π (flat_map (fun x =>(interleavings (fst x) (snd x))) (list_prod l0 l1))).
Proof.
induction l0;intros;simpl. rewrite c_par_comm. auto_rwd_eqDB.
rewrite flat_map_app. rewrite map_app. rewrite  Σ_app.
rewrite <- IHl0. rewrite <- Π_par_aux. 
rewrite c_par_comm. rewrite c_par_distr_l.
 auto with eqDB. 
Qed.



Theorem Π_L_ceq : forall (c : Contract), Σ (map Π (L c)) =R= c.
Proof.
induction c; simpl; try solve [auto_rwd_eqDB].
- rewrite map_app. rewrite Σ_app.
  auto using c_plus_ctx. 
- rewrite map_map.
  rewrite <- IHc1 at 2. rewrite <- IHc2 at 2.
  symmetry. apply Π_distr.
- rewrite <- IHc1 at 2. rewrite <- IHc2 at 2.
  rewrite Π_distr_par. auto with eqDB.
Qed.



Lemma c_eq_completeness : forall (c0 c1 : Contract), (forall s : Trace, s =~ c0 <-> s =~ c1) -> c0 =R= c1.
Proof.
intros. rewrite <- Π_L_ceq. rewrite <- (Π_L_ceq c1). 
apply Matches_eq_i_incl_and in H.
destruct H. auto using incl_map, incl_Σ_c_eq.
Qed.



Theorem Matches_iff_c_eq : forall c0 c1, (forall s, s =~ c0 <-> s =~ c1) <-> c0 =R= c1.
Proof.
split; auto using c_eq_completeness, c_eq_soundness.
Qed.

Lemma L_Σ : forall l, L (Σ l) = flat_map L l.
Proof.
induction l;intros;simpl;auto. now rewrite IHl.
Qed.























 
