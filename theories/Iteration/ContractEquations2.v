Require Import CSL.Iteration.Contract.  
Require Import Lists.List Bool.Bool Bool.Sumbool Setoid Coq.Arith.PeanoNat.
Require Import micromega.Lia.
From Equations Require Import Equations.
Require Import Arith.
Require Import micromega.Lia.
(** printing =~ %$=\sim$% *)

(** printing _+_ %$+$% *)

Import ListNotations.

Set Implicit Arguments.


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

Definition Σe es cs := Σ (map (fun x => Event (fst x) _;_ snd x) (combine es cs)).

Definition Σed c := ( Σ (map (fun a : EventType => Event a _;_ a \ c) alphabet)).
Notation "Σe\ c" := (Σed c)
                    (at level 30, no associativity).

CoInductive Bisimilarity : Contract -> Contract -> Prop :=
 CBisimilarity c0 c1 (H0: forall e, Bisimilarity (e \ c0) (e \ c1)) (H1: nu c0 = nu c1) : Bisimilarity c0 c1.

Theorem matches_eq_is_bisimilarity : forall c0 c1, (forall s, s=~ c0 <-> s=~c1) <-> Bisimilarity c0 c1.
Proof.
split. 
- generalize dependent c1. generalize dependent c0. cofix matches_eq_is_bisimilarity.
  intros. constructor.
  * intros. apply matches_eq_is_bisimilarity. setoid_rewrite <- derive_spec_comp. auto.
  * apply eq_true_iff_eq. setoid_rewrite Matches_Comp_iff_matchesb in H.
    specialize H with []. simpl in*. auto.
- intro.
  repeat setoid_rewrite matches_Matches. intro. generalize dependent c1.
  generalize dependent c0. induction s;intros.
  * inversion H. repeat rewrite Matches_Comp_iff_matchesb. simpl.
    now rewrite <- eq_iff_eq_true.
  * repeat rewrite derive_spec_comp. inversion H. auto.
Qed.



Reserved Notation "c0 =R= c1" (at level 63).
Section coinductive_rule.
  Hypothesis R : Contract -> Contract -> Prop.

  CoInductive c_eq_co : Contract -> Contract -> Prop :=
  | co_base_p c0 c1 (H: R c0 c1) : c_eq_co c0 c1 
  | co_sum_p l0 l1 (H0 : length l0 = length alphabet) 
                   (H1 : length l1 = length alphabet) 
                   (H1: forall n, c_eq_co (nth n l0 Failure) (nth n l1 Failure)) : c_eq_co (Σe alphabet l0) (Σe alphabet l1).
  
End coinductive_rule.



Inductive c_eq : Contract -> Contract -> Prop :=
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

| c_unfold c :  Success _+_ (c _;_ Star c) =R= Star c
| c_refl c : c =R= c
| c_sym c0 c1 (H: c0 =R=c1) : c1 =R=c0
| c_trans c0 c1 c2 (H1 : c0 =R=c1) (H2 : c1 =R=c2) : c0 =R=c2
| c_plus_ctx c0 c0' c1 c1' (H1 : c0 =R=c0') (H2 : c1 =R=c1') : c0 _+_ c1 =R=c0' _+_ c1'
| c_seq_ctx c0 c0' c1 c1' (H1 : c0 =R=c0') (H2 : c1 =R=c1') : c0 _;_ c1 =R=c0' _;_ c1'
| c_par_ctx c0 c0' c1 c1' (H1 : c0 =R=c0') (H2 : c1 =R=c1') : c0 _*_ c1 =R=c0' _*_ c1'

| c_coind c0 c1 (H : c_eq_co c_eq c0 c1) : c0 =R= c1
  where "c1 =R= c2" := (c_eq c1 c2).
Hint Constructors c_eq : eqDB.

Notation "c0 =C= c1" := (c_eq_co c_eq c0 c1)(at level 63).



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

         end); auto with cDB.


(********************Soundness*****************************)
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

Lemma test : forall l e n, nth_error alphabet n = Some e ->
e \ Σe alphabet l =R= nth n l Failure.
Proof. Admitted.
(*
Lemma test2 : forall l0 l1 e n, nth_error alphabet n = Some e -> 
(forall s, s =~ nth n l0 Failure <-> s =~ nth n l1 Failure)<->(forall s, s =~ e \ Σe alphabet l0  <-> s =~ e \ Σe alphabet l1).
Proof.
intros. split.
- intro H2. repeat setoid_rewrite test; eauto.
- intro H2. repeat setoid_rewrite <- test;eauto.
Qed.*)

Lemma in_alphabet_nth : forall e, exists n, nth_error alphabet n = Some e.
Proof.
intros. apply In_nth_error. auto with eqDB.
Qed.

Lemma Σe_not_nu : forall es l0, nu (Σe es l0) = false.
Proof.
unfold Σe.
intros. induction ((combine es l0)).
- simpl. auto.
- simpl. rewrite IHl. auto.
Qed.
(*
Section sum_case.
  Variable l0 l1 : list Contract.
  Hypothesis H : Σe alphabet l0 =R= Σe alphabet l1.
  Hypothesis H1 : length l0 = length alphabet.
  Hypothesis H2 : length l1 = length alphabet.
  Hypothesis H3 : forall n : nat, nth n l0 Failure =R= nth n l1 Failure.
  Hypothesis H4 : forall c0 c1 : Contract, c0 =R= c1 -> Bisimilarity c0 c1.

  Theorem sum_soundness : Bisimilarity (Σe alphabet l0) (Σe alphabet l1).
  Proof.
  constructor.
  - intros. apply H4. *)


(*
Lemma c_eq_sound_aux : forall c0 c1, c0 =C= c1 -> Bisimilarity c0 c1.
Proof.
cofix H.
intros. inversion H0;subst.
constructor.
  * intros. pose proof (in_alphabet_nth e).
    destruct_ctx. apply H. apply matches_eq_is_bisimilarity. apply <- matches_eq_is_bisimilarity.
    apply H.  Guarded.
    apply <- matches_eq_is_bisimilarity. apply H. Guarded. rewrite <- test2.


 eapply H3. apply H4. Guarded.
  * repeat rewrite Σe_not_nu. auto.
Qed.
*)

Section soundness. 
  Hypothesis H_co : forall c0 c1 : Contract, c0 =C= c1 -> Bisimilarity c0 c1.
  Variables c0 c1 : Contract.
  Hypothesis H : c0 =C= c1.

Theorem c_eq_soundness_aux : forall s : Trace, s =~ c0 <-> s =~ c1.
Proof. Admitted.
End soundness.

Lemma c_eq_derive : forall c0 c1 e, c0 =C= c1 -> e \ c0 =C= e \ c1.
Proof. Admitted. 

Lemma c_eq_nu : forall c0 c1, c0 =C= c1 -> nu c0 = nu c1.
Proof. Admitted. 

Lemma c_eq_co_soundness : forall c0 c1, c0 =C= c1 -> Bisimilarity c0 c1.
Proof.
cofix H_co.
intros c0 c1 H12. inversion H12;subst.
- induction H. 
 25: { constructor. intros. apply H_co. Guarded. apply c_eq_derive. apply H. Guarded.
   rewrite <- matches_eq_is_bisimilarity.
   subst. induc
  clear H_co. apply c_eq_soundness_aux.  induction H0.


  Proof.
  cofix H.
  intros. inversion H1.
  - subst. apply H0. apply H2. 
  - constructor.
    * intros. apply H.
      ** apply H0.  intros.
    *
  - intros. apply H.
    * apply H0. 
    *



Lemma c_eq_base_soundness : forall (c0 c1 : Contract), c0 =R= c1 -> (forall s : Trace, s =~ c0 <-> s =~ c1).
Proof.
Check (reason_principle c_eq).
intros c0 c1. apply (@reason_principle c_eq c0 c1). induction H ;intros; try solve [split;intros;c_inversion].
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
  * split;intros; c_inversion. inversion H;subst. auto with cDB. auto with cDB.
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
  * generalize dependent s. inversion H.
    ** eapply reason_principle.
      *** intros.
    ** intros. inversion H.
  *
Qed.


Lemma c_eq_soundness : forall (c0 c1 : Contract), c0 =R= c1 -> (forall s : Trace, s =~ c0 <-> s =~ c1).
Proof.
intros c0 c1 H. induction H.
- inversion H ;intros; try solve [split;intros;c_inversion].
  * split;intros;c_inversion; [ rewrite <- app_assoc | rewrite app_assoc ]; auto with cDB.
  * rewrite <- (app_nil_l s). split;intros;c_inversion.
  * rewrite <- (app_nil_r s) at 1. split;intros;c_inversion. subst.
    repeat rewrite app_nil_r in H3. now rewrite <- H3.
  * split;intros; inversion H2; subst.  (*new*)
    ** inversion H5. subst. eapply interl_app in H8;eauto. destruct_ctx.
       eauto with cDB.
    ** inversion H7. subst. eapply interl_comm in H8. eapply interl_comm in H9.
       eapply interl_app in H8;eauto. destruct_ctx. econstructor;eauto. 
       econstructor;eauto. all: eauto using interl_comm.
  * split;intros.
    ** inversion H2. subst. c_inversion. subst. apply interl_eq_r in H8. 
       subst. auto.
    ** eauto with cDB. 
  * split;intros.
    ** inversion H2. subst. econstructor;eauto using interl_comm.
    ** inversion H2. subst. econstructor;eauto using interl_comm.
  * split;intros.
    ** inversion H2. subst. inversion H7;  eauto with cDB. 
    ** inversion H2. subst.
      *** inversion H5. subst. econstructor;eauto with cDB. 
      *** inversion H5. subst. econstructor;eauto with cDB. (*new*)
  * apply event_seq.
  * split;intros; c_inversion. inversion H2;subst. auto with cDB. auto with cDB.
  * generalize dependent s. generalize dependent c1. generalize dependent c0.
    generalize dependent l1. generalize dependent l0. setoid_rewrite matches_eq_is_bisimilarity.
    cofix H. intros. constructor.
    ** intros. rewrite generalize dependent s.
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
  * inversion H1. subst.
Qed.

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





(*
Lemma seq_ctx_sound : forall c0 c0' c1 c1', Bisimilarity c0 c0' -> Bisimilarity c1 c1' -> Bisimilarity (c0 _;_ c0') (c1 _*_ c1').
Proof. Admitted.
Lemma Star_ctx_sound : forall c0 c1, Bisimilarity c0 c1 -> Bisimilarity (Star c0) (Star c1).
Proof.
cofix H.
intros. constructor.
- intros. simpl. inversion H0. apply seq_ctx_sound*)




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







Lemma Σ_eq : forall l0 l1, (forall n, nth n l0 Failure =R= nth n l1 Failure )-> Σ l0 =R= Σ l1.
Proof. Admitted.

Lemma Σ_test : forall c l0, c =R= Σe alphabet l0 -> exists l1, c = Σe alphabet l1 /\ (forall n, nth n l0 Failure =R= nth n l1 Failure ).
Proof. Admitted.





Lemma c_eq_trans : forall c0 c1 c2, c0 =C= c1 -> c1 =C= c2 -> c0 =C= c2.
Proof.
cofix H. intros. inversion H0.
- inversion H1.
  * constructor. eauto using c_trans.
  * subst. apply Σ_test in H2. destruct_ctx.
    subst. apply co_sum. constructor.

 auto with eqDB. eapply co_trans_mix;eauto. reflexivity.
- subst. eapply co_trans_mix. apply H2. eapply H.
  eauto.
  eapply co_trans_mix. reflexivity. apply H3. apply H4.
 eauto. 
- subst. inversion H1.
  * subst. rewrite H4 in H3. eapply co_trans_mix_r;eauto.
  * subst. rewrite H4 in H3. eapply co_trans_mix_l. rewrite H1 in H1.
  * constructor. rewrite H2. auto.
  * apply co_sum. rewrite H2.

Lemma c_eq_trans : forall c0 c1 c2, c0 =C= c1 -> c1 =C= c2 -> c0 =C= c2. 
Proof.
cofix H. intros. inversion H0.
- inversion H1; subst.
  * constructor. rewrite H2. auto.
  * apply co_sum. rewrite H2.
 inversion H0. constructor. rewrite H0. auto.
- subst. constructor. rewrite H0.
 constructor. rewrite H0. apply H. inversion H1.
  * constructor. rewrite H2. auto.
  * subst. apply co_sum.
Qed.

Add Parametric Relation : Contract c_eq
  reflexivity proved by c_refl
  symmetry proved by c_sym
  transitivity proved by c_trans
  as IContract_setoid.

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
*)








(*
| co_sum es l0 l1 (H0 : length l0 = length es) 
                  (H1 : length l1 = length es) 
                    (H: forall p, In p (combine l0 l1) -> (fst p) =C= (snd p)) : 
         Σ (map (fun x => Event (fst x) _;_ snd x) (combine es l0)) =C= Σ (map (fun x => Event (fst x) _;_ snd x) (combine es l1))*)

(*
Lemma Σe_derive : forall l0 es e, e \ Σe es l0 =R=  Σe\ es l0*)


Lemma length_combine : forall (A:Type) (B:Type) (l0 l1 : list A) (es : list B), length l0 = length l1 -> length (combine es l0) = length (combine es l1).
Proof. Admitted.

Lemma Σe_cons : forall e es c cs, Σe (e :: es) (c :: cs) = Event e _;_ c _+_ Σe es cs.
Proof.
intros. unfold Σe. simpl. reflexivity.
Qed.

Lemma test : forall l0 l1 es e, (length l0 = length l1) -> (forall n : nat, nth n l0 Failure =C= nth n l1 Failure) ->
  e \ Σe es l0 =C= e \ Σe es l1.
Proof.
induction l0.
- intros. destruct l1 ; try (simpl in * ; discriminate).
  constructor.  reflexivity.
- intros. destruct l1; try (simpl in * ; discriminate).
  destruct es.  simpl. constructor. reflexivity.
  repeat rewrite Σe_cons. simpl.
  eq_event_destruct. subst. specialize H0 with 0.
  simpl in H0. inversion H0.
  * subst.
  rewrite IHl0.
  simpl.
 destruct l1 ; try (simpl in * ; discriminate).
  constructor.  reflexivity. rewrite Heqn in H.
  simpl in H. Search (length _ = S _). destruct ((combine es l1)) eqn:Heqn2.
  simpl in H. discriminate. simpl.
  simpl in H. symmetry in H.  rewrite length_zero_iff_nil in H. 
 rewrite H in Heqn. erewrite H in Heqn.
induction l0;intros.
- simpl. simpl in H. symmetry in H. rewrite length_zero_iff_nil in H.
  subst. simpl. constructor. reflexivity.
- simpl. Search (length _ = 0). 
intros.











Definition o c := if nu c then Success else Failure.
Transparent o.
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

(*Normal form*)


Lemma map_ext_in_R :
  forall (A : Type)(f g:A->Contract) l, (forall a, In a l -> f a =R= g a) -> Σ (map f l) =R= Σ (map g l).
Proof.
induction l;intros;simpl;auto with eqDB.
apply c_plus_ctx. apply H. apply in_eq. apply IHl.
intros. apply H. simpl. now right.
Qed.

Ltac eq_m_left := repeat rewrite c_plus_assoc; apply c_plus_ctx;
                  auto_rwd_eqDB.

Ltac eq_m_right := repeat rewrite <- c_plus_assoc; apply c_plus_ctx;
                  auto_rwd_eqDB.


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
  * edestruct IHalphabet0; destruct H; rewrite H; auto_rwd_eqDB.
    right. split;auto with eqDB. intro H2. destruct H2.
    symmetry in H1. contradiction. contradiction.
Qed.

(************Summation rules *****)
Lemma Σ_alphabet : forall e, Σ (map (fun a => if EventType_eq_dec e a then Success else Failure) alphabet) =R= Success.
Proof.
intros. destruct (Σ_alphabet_or alphabet e).
- destruct H. auto.
- destruct H. pose proof (in_alphabet e). contradiction.
Qed.

Lemma Σ_split_plus : forall (A: Type) l (P P' : A -> Contract),
Σ (map (fun a : A => P a _+_ P' a) l) =R= Σ (map (fun a : A => P a) l) _+_  Σ (map (fun a : A => P' a) l).
Proof.
induction l;intros.
- simpl. auto_rwd_eqDB.
- simpl. rewrite c_plus_assoc. rewrite c_plus_assoc. apply c_plus_ctx;auto with eqDB.
  rewrite (c_plus_comm (Σ _)).
  rewrite c_plus_assoc. apply c_plus_ctx;auto with eqDB. rewrite IHl.
  auto_rwd_eqDB.
Qed.

Lemma Σ_factor_seq_r : forall l (P: EventType -> Contract) c,
Σ (map (fun a  => P a _;_ c) l) =R= Σ (map (fun a  => P a) l) _;_ c.
Proof.
induction l;intros.
- simpl. auto_rwd_eqDB.
- simpl. auto_rwd_eqDB.
Qed.

Lemma Σ_factor_seq_l : forall l (P: EventType -> Contract) c,
Σ (map (fun a  => c _;_ P a) l) =R= c _;_ Σ (map (fun a  => P a) l).
Proof.
induction l;intros.
- simpl. auto_rwd_eqDB.
- simpl. auto_rwd_eqDB.
Qed.


Lemma Σ_factor_par_l : forall l1 c (P' : EventType -> Contract),
Σ (map (fun a' : EventType => c _*_ P' a') l1) =R=
c _*_ Σ (map (fun a0 : EventType => P' a0) l1).
Proof.
induction l1;intros.
- simpl. auto_rwd_eqDB.
- simpl. rewrite IHl1. auto_rwd_eqDB.
Qed.

Lemma Σ_factor_par_r : forall l1 c (P' : EventType -> Contract),
Σ (map (fun a0 : EventType => P' a0) l1) _*_ c =R=
Σ (map (fun a' : EventType => P' a' _*_ c) l1).
Proof.
induction l1;intros.
- simpl. auto_rwd_eqDB.
- simpl. rewrite <- IHl1. auto_rwd_eqDB.
Qed.

Lemma Σ_par_ΣΣ : forall l0 l1 (P0 P1 : EventType -> Contract),
Σ (map (fun a0  => P0 a0) l0) _*_ Σ (map (fun a1 => P1 a1) l1) =R=
Σ (map (fun a0  => Σ (map (fun a1  => (P0 a0) _*_ (P1 a1)) l1)) l0).
Proof. 
induction l0;intros.
- simpl. auto_rwd_eqDB.
- simpl. auto_rwd_eqDB.
  rewrite Σ_factor_par_l. rewrite IHl0.  reflexivity. 
Qed. 


Lemma ΣΣ_prod_swap : forall l0 l1 (P : EventType -> EventType -> Contract), 
Σ (map (fun a0 => Σ (map (fun a1 => P a0 a1) l1)) l0)=R=
Σ (map (fun a0 => Σ (map (fun a1 => P a1 a0) l0)) l1).
Proof.
induction l0;intros.
- simpl. induction l1;intros;simpl;auto with eqDB. rewrite IHl1.
  auto with eqDB.
- simpl. rewrite Σ_split_plus. eq_m_left.
Qed.

Lemma fold_Failure : forall l, Σ (map (fun _ : EventType => Failure) l) =R= Failure.
Proof.
induction l;intros. simpl. reflexivity.
simpl. rewrite IHl. autorewrite with eqDB. reflexivity.
Qed.

Hint Resolve fold_Failure : eqDB.



Ltac rwd_in_map f := rewrite map_ext_in_R ; try instantiate (1:=f);intros; auto_rwd_eqDB.

Lemma derive_unfold_seq : forall c1 c2, 
o c1 _+_ Σ (map (fun a : EventType => Event a _;_ a \ c1) alphabet) =R= c1 ->
o c2 _+_ Σ (map (fun a : EventType => Event a _;_ a \ c2) alphabet) =R= c2 -> 
o (c1 _;_ c2) _+_ 
Σ (map (fun a : EventType => Event a _;_ a \ (c1 _;_ c2)) alphabet) =R=
c1 _;_ c2.
Proof.
intros;simpl;auto_rwd_eqDB.
- destruct (nu c1) eqn:Heqn.
  * rwd_in_map (fun a => Event a _;_ a \ c1 _;_ c2  _+_  Event a _;_ a \ c2);
    intros; auto_rwd_eqDB.  rewrite Σ_split_plus.
    rewrite Σ_factor_seq_r. rewrite <- H at 2.
    rewrite <- H0 at 2. rewrite <- H0 at 3. auto_rwd_eqDB. eq_m_left.
    apply o_true in Heqn. rewrite Heqn.
    auto_rwd_eqDB. rewrite (c_plus_comm (Σ _ _;_ Σ _ )).
    eq_m_right. 
  * apply o_false in Heqn. rewrite Heqn in*. autorewrite with eqDB in *.
    rwd_in_map (fun a => Event a _;_ a \ c1 _;_ c2);
    intros; auto_rwd_eqDB. rewrite Σ_factor_seq_r. 
    rewrite H. reflexivity.
Qed.


Lemma derive_unfold_par : forall c1 c2, 
o c1 _+_ Σ (map (fun a : EventType => Event a _;_ a \ c1) alphabet) =R= c1 ->
o c2 _+_ Σ (map (fun a : EventType => Event a _;_ a \ c2) alphabet) =R= c2 -> 
o (c1 _*_ c2) _+_ 
Σ (map (fun a : EventType => Event a _;_ a \ (c1 _*_ c2)) alphabet) =R=
c1 _*_ c2.
Proof.
intros;simpl;auto_rwd_eqDB.
rewrite (map_ext_in_R _ (fun a : EventType =>  ((Event a _;_ (a \ c1 _*_ o c2) _+_ Event a _;_ ( a \ c1 _*_Σ (map (fun a : EventType => Event a _;_ a \ c2) alphabet))) 
_+_ (Event a _;_ (o c1 _*_ a \ c2) _+_ Event a _;_ (Σ (map (fun a : EventType => Event a _;_ a \ c1) alphabet) _*_ a \ c2 )))));

try solve [intros; rewrite <- c_distr_l; rewrite <- c_par_distr_l;  rewrite H0;
           rewrite <- c_distr_l; rewrite <- c_distr_l;
           rewrite <- c_par_distr_r; rewrite H; reflexivity].
rewrite <- H at 2. rewrite <- H0 at 2.
  auto_rwd_eqDB. repeat rewrite (c_par_comm (_ _+_ _)). auto_rwd_eqDB.
  rewrite c_plus_assoc. eq_m_left. 
repeat rewrite Σ_split_plus.
repeat rewrite <- c_plus_assoc. 
remember (Σ (map (fun a : EventType => Event a _;_ (a \ c1 _*_ Σ (map (fun a0 : EventType => Event a0 _;_ a0 \ c2) alphabet))) alphabet)) as a.
remember (Σ (map (fun a0 : EventType => Event a0 _;_ (Σ (map (fun a1 : EventType => Event a1 _;_ a1 \ c1) alphabet) _*_ a0 \ c2)) alphabet)) as b.
repeat rewrite c_plus_assoc. rewrite (c_plus_comm a).
repeat rewrite <- c_plus_assoc.
rewrite (c_plus_assoc _ b).
apply c_plus_ctx.
  * rewrite c_plus_comm. apply c_plus_ctx.
    ** destruct (o_destruct c1);rewrite H1.
      *** auto_rwd_eqDB. apply map_ext_in_R;
          intros; auto_rwd_eqDB.
      *** auto_rwd_eqDB. 
          rewrite (map_ext_in_R _ (fun _ : EventType => Failure)).
          apply fold_Failure. intros. auto_rwd_eqDB.
    ** destruct (o_destruct c2);rewrite H1.
      *** auto_rwd_eqDB. apply map_ext_in_R.
          intros. auto_rwd_eqDB.
      *** auto_rwd_eqDB. 
          rewrite (map_ext_in_R _ (fun _ : EventType => Failure)).
          apply fold_Failure. intros. auto_rwd_eqDB.
  * subst. symmetry. rewrite Σ_par_ΣΣ.
rewrite (map_ext_in_R _ (fun a0 : EventType => Σ (map (fun a1 : EventType => Event a0 _;_ (a0 \ c1 _*_ Event a1 _;_ a1 \ c2)) alphabet)
                                           _+_ Σ (map (fun a1 : EventType => Event a1 _;_ (Event a0 _;_ a0 \ c1 _*_ a1 \ c2)) alphabet)));
    intros; auto_rwd_eqDB;
    try solve [rewrite <- Σ_split_plus; apply map_ext_in_R;
    intros; auto_rwd_eqDB].
 rewrite Σ_split_plus. rewrite c_plus_comm. apply c_plus_ctx.
    ** rewrite ΣΣ_prod_swap. apply map_ext_in_R.
       intros. rewrite Σ_factor_seq_l. apply c_seq_ctx;auto with eqDB.
       rewrite Σ_factor_par_r. reflexivity.
    ** apply map_ext_in_R. intros. 
       rewrite Σ_factor_seq_l. apply c_seq_ctx;auto with eqDB.
       rewrite Σ_factor_par_l. reflexivity.
Qed.


Lemma Star_ctx : forall c0 c1, c0 =R= c1 -> Star c0 =R= Star c1.
Proof. Admitted.

Lemma Star_Success : forall c, Star (Success _+_ c) =R= Star c.
Proof. Admitted.



Lemma Σed_star : forall c, Σe\ (Star c) =R= Σe\ c _;_ Star c.
Proof.
intros. unfold Σed at 1. simpl. rewrite (map_ext_in_R _ (fun a : EventType => (Event a _;_ a \ c) _;_ Star c));
    intros; auto_rwd_eqDB. rewrite Σ_factor_seq_r. unfold Σed. reflexivity.
Qed.

(*
Lemma Σed_Star : forall c, Σe\ c _;_ Star c =C= Σe\ c _;_ Star (Σe\ c).
Proof.
cofix H.
intros. unfold Σe\. rewrite <- Σ_factor_seq_r. apply co_sum.*)
Ltac unf := unfold o, Σed.


Inductive NotStar : Contract -> Prop :=
| NSFailure : NotStar Failure
| NSSuccess : NotStar Success
| NSEvent e : NotStar (Event e)
| NSPlus c0 c1 : NotStar (c0 _+_ c1)
| NSSeq c0 c1 : NotStar (c0 _;_ c1)
| NSPar c0 c1 : NotStar (c0 _*_ c1).

Lemma Σed_Success : Σe\ Success  =R= Failure. 
Proof.
unfold Σed. induction alphabet. simpl. reflexivity.
simpl. rewrite IHl. auto_rwd_eqDB.
Qed.

Lemma test2 : forall c, c = Star c -> False.
Proof.
induction c;intros; try discriminate. inversion H.
apply IHc. auto.
Qed.

Lemma test3 : forall c, c = Star (Star c) -> False.
Proof.
induction c;intros; try discriminate. inversion H.
apply IHc. auto.
Qed.

Lemma not_c_eq_not_eq : forall c0 c1, (~ c0 =R= c1) -> c0 <> c1.
Proof.
intros. intro H2. apply H. rewrite H2. reflexivity.
Qed.

Lemma sym_not : forall c0 c1, (~c0 =R= c1) -> (~c1 =R= c0).
Proof.
intros. intro H2. apply H. inversion H2; try solve [ symmetry in H2; contradiction ].
Qed.

Lemma not_derive_star : forall (c: Contract),  Star c =R= Success _+_ Σe\ c _;_ Star c -> False. 
Proof.
intros.
inversion H. subst. symmetry in H0.
eapply 
rewrite Heqc0 in Heqc1. .
- apply IHc_eq. rewrite Heqc1. rewrite Heqc0.
Lemma not_derive_star : forall (c: Contract),  Star c =R= Success _+_ Σe\ c _;_ Star c -> False. 
Proof.
intros. remember (Star c). remember (Success _+_ Σe\ c _;_ c0).
induction H; try discriminate.
rewrite Heqc0 in Heqc1. discriminate.
- apply IHc_eq. rewrite Heqc1. rewrite Heqc0.
rewrite Heqc0 in Heqc0.
2: {
apply IHc_eq.
2: { 
 eapply test2. eauto. in Heqc0.
induction c.
- intros. rewrite Σed_Success in H. autorewrite with eqDB in H.
  inversion H.

Lemma test : forall c, Star c =R= c -> False.
Proof.
intros. remember (Star c). induction H; try discriminate.
- eauto using test2.
- eapply test3. IHc_eq. rewrite Heqc0. apply test3.

inversion Heqc0.
induction c.
-



Lemma derive_unfold_test : forall (c: Contract),  NotStar c -> o c _+_  Σe\ c =R= c.
Proof.
induction c;intros.
- unf; simpl. rewrite Σ_factor_seq_r. simpl;auto_rwd_eqDB.
- unf; simpl;auto_rwd_eqDB. rwd_in_map (fun (_ : EventType) => Failure).
- unf; simpl; rwd_in_map (fun a => Event e _;_ (if EventType_eq_dec e a then Success else Failure)).
  * rewrite Σ_factor_seq_l. rewrite Σ_alphabet. auto_rwd_eqDB.
  * simpl. eq_event_destruct;subst; auto_rwd_eqDB.
- unfold Σed. simpl;auto_rwd_eqDB. rwd_in_map (fun a => Event a _;_ a \ c1  _+_  Event a _;_ a \ c2);
       intros; auto_rwd_eqDB. rewrite Σ_split_plus. 
       rewrite <- c_plus_assoc. rewrite (c_plus_comm (o _)).
       rewrite (c_plus_assoc (o _)).
       rewrite IHc1. rewrite (c_plus_comm _ c1).
       rewrite c_plus_assoc. rewrite IHc2. auto_rwd_eqDB.
- unfold Σed. auto using derive_unfold_seq.
- unfold Σed. auto using derive_unfold_par.
- unfold o.  simpl. transitivity (Star (o c _+_ Σe\ c)).
2: { apply Star_ctx. auto. }
destruct (o_destruct c).
  * rewrite H. transitivity (Star (Σe\ c)).
2 : {  rewrite Star_Success . reflexivity. }
rewrite Σed_star. rewrite <- (c_unfold (Σe\ c)).
apply c_plus_ctx. reflexivity. apply c_seq_ctx. reflexivity. 

 reflexivity.
 ( rewrite <- c_unfold at 2.
  rewrite <- IHc at 2. auto_rwd_eqDB. rewrite (c_plus_comm ((o c) _;_ _ )). 
  rewrite <- c_plus_assoc. rewrite Star_test. eq_m_left.
  rewrite Σe\_star. auto_rwd_eqDB.
Qed.


Lemma derive_unfold : forall c, o c _+_  Σe\ c =R= c.
Proof.
induction c;intros.
- unf; simpl. rewrite Σ_factor_seq_r. simpl;auto_rwd_eqDB.
- unf; simpl;auto_rwd_eqDB. rwd_in_map (fun (_ : EventType) => Failure).
- unf; simpl; rwd_in_map (fun a => Event e _;_ (if EventType_eq_dec e a then Success else Failure)).
  * rewrite Σ_factor_seq_l. rewrite Σ_alphabet. auto_rwd_eqDB.
  * simpl. eq_event_destruct;subst; auto_rwd_eqDB.
- unfold Σed. simpl;auto_rwd_eqDB. rwd_in_map (fun a => Event a _;_ a \ c1  _+_  Event a _;_ a \ c2);
       intros; auto_rwd_eqDB. rewrite Σ_split_plus. 
       rewrite <- c_plus_assoc. rewrite (c_plus_comm (o _)).
       rewrite (c_plus_assoc (o _)).
       rewrite IHc1. rewrite (c_plus_comm _ c1).
       rewrite c_plus_assoc. rewrite IHc2. auto_rwd_eqDB.
- unfold Σed. auto using derive_unfold_seq.
- unfold Σed. auto using derive_unfold_par.
- unfold o.  simpl. transitivity (Star (o c _+_ Σe\ c)).
2: { apply Star_ctx. auto. }
destruct (o_destruct c).
  * rewrite H. transitivity (Star (Σe\ c)).
2 : {  rewrite Star_Success . reflexivity. }
rewrite Σed_star. rewrite <- (c_unfold (Σe\ c)).
apply c_plus_ctx. reflexivity. apply c_seq_ctx. reflexivity. 

 reflexivity.
 ( rewrite <- c_unfold at 2.
  rewrite <- IHc at 2. auto_rwd_eqDB. rewrite (c_plus_comm ((o c) _;_ _ )). 
  rewrite <- c_plus_assoc. rewrite Star_test. eq_m_left.
  rewrite Σe\_star. auto_rwd_eqDB.
Qed.
 rewrite <- Star_test.
rewrite (map_ext_in_R _ (fun a : EventType => (Event a _;_ a \ c) _;_ Star c));
    intros; auto_rwd_eqDB. rewrite Σ_factor_seq_r.

symmetry. transitivity (Star (o c _+_ Σ (map (fun a : EventType => Event a _;_ a \ c) alphabet))).
  apply Star_ctx. symmetry. auto. symmetry.
destruct (o_destruct c).
  * symmetry. rewrite <- c_unfold. rewrite IHc at 2. rewrite H. rewrite Star_Success. symmetry.
     rewrite <- c_unfold. reflexivity. auto.
   simpl.
  unfold o. simpl. rewrite Σ_factor_seq_r.  fold o. rewrite c_unfold. erewrite Star_ctx. unfold o. simpl. 

rewrite <- c_unfold at 2. (*
destruct (o_destruct c). 
  * rewrite H in *.*) rewrite <- IHc at 2.
    auto_rwd_eqDB.
destruct (o_destruct c). 
  * rewrite H in *.
    ** auto_rwd_eqDB.

 eq_m_left. apply c_seq_ctx. constructor.  rewrite test. rewrite H in *. rewrite IHc. reflexivity.
  * rewrite H in *. autorewrite with eqDB in IHc.
    rewrite IHc. reflexivity.
Qed. 



(******************Translation***************)

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
 | NSTPar c0 c1 (H0 : NotStuck c0)(H1 : NotStuck c1) : NotStuck (c0 _*_ c1)
 | NSTI c : NotStuck (Star c).

Hint Constructors NotStuck : tDB.

Fixpoint stuck (c : Contract) :=
match c with
| Failure => true
| c0 _+_ c1 => stuck c0 && stuck c1
| c0 _;_ _ => stuck c0
| c0 _*_ c1 => stuck c0 || stuck c1
| _ => false
end.

Lemma Stuck_eq_Failure : forall c, Stuck c -> c =R= Failure.
Proof.
intros. induction H;auto with eqDB.
- rewrite IHStuck1. rewrite IHStuck2. auto_rwd_eqDB.
- rewrite IHStuck. auto_rwd_eqDB.
- rewrite IHStuck. rewrite c_par_comm. auto_rwd_eqDB.
- rewrite IHStuck. auto_rwd_eqDB.
Qed.

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

Lemma Stuck_failure : forall (c : Contract), Stuck c -> (forall s, s =~ c <-> s =~ Failure).
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
               else (o c) _+_ Σ (map (fun e => (Event e) _;_ (plus_norm (e \ c))) alphabet).

Next Obligation. auto using not_stuck_derives. Defined.

(*Global Transparent plus_norm.*)


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
- unfold o. destruct (nu c) eqn:Heqn.
  * destruct s.
    ** split;intros;auto with cDB. auto using Matches_Comp_nil_nu. 
    ** assert (HA: forall (c : Contract), e::s =~ Success _+_ c <-> e::s =~ c).
       { split; intros. inversion H0. inversion H3. assumption. auto with cDB. } rewrite HA.
       apply plus_norm_cons. auto.
  * destruct s.
    ** split;intros.
      *** rewrite Matches_Comp_iff_matchesb in H0. simpl in H0. 
          rewrite Heqn in H0. discriminate.
      *** c_inversion. apply plus_norm_nil in H3 as [].
    ** split;intros. apply MPlusR. rewrite <- plus_norm_cons;auto.
       c_inversion. rewrite plus_norm_cons;auto. 
Qed.



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


(**********plus_norm respects axiomatization *******)





Lemma plus_norm_c_eq : forall c, plus_norm c =R= c.
Proof.
intros. funelim (plus_norm c). stuck_tac.
- symmetry. auto using Stuck_eq_Failure.
- rewrite map_ext_in_R. apply derive_unfold.
  intros. rewrite H at 1;auto. eapply c_refl.
Qed.



(*************Completeness = rewrite to normal form + appeal to CSL_core ***********)

Lemma c_eq_completeness : forall (c0 c1 : Contract),(forall s : Trace, s =~ c0 <-> s =~ c1) ->  c0 =R= c1.
Proof.
intros. destruct (sum_decomposition_exists c0). destruct (sum_decomposition_exists c1). destruct_ctx.
pose proof c_eq_soundness H3. setoid_rewrite H4 in H. 
pose proof c_eq_soundness H2. setoid_rewrite H5 in H.
rewrite H3. rewrite H2.
apply NormalForm_trans in H0. apply NormalForm_trans in H1. destruct_ctx. 
eapply c_core. eauto. eauto. apply CSLEQ.c_eq_completeness.
setoid_rewrite <- translate_aux_spec. eapply H. all: eauto.
Qed.





(**********************Define Sigma normal form and show plus_norm always returns a Sigma normal form*************************************)
Inductive Atom : Contract -> Prop :=
| AFailure : Atom Failure
| ASuccess : Atom Success.
Hint Constructors Atom : eqDB.

Lemma Atom_i_Sequential : forall c, Atom c -> Sequential c.
Proof.
intros. inversion H;auto with eqDB.
Qed.

Hint Resolve Atom_i_Sequential : eqDB.

Inductive NormalForm : Contract -> Prop :=
| NFA c (H: Atom c) : NormalForm c
| NFList c es l (H: Atom c) (H1: forall a, In a l -> NormalForm a) : NormalForm (c _+_ Σ (map (fun x => Event (fst x) _;_ snd x) (combine es l))).

Lemma Sequential_Σ : forall l, (forall c, In c l -> Sequential c) -> Sequential (Σ l).
Proof.
induction l;intros; auto with eqDB.
simpl. constructor. auto using in_eq.
apply IHl. intros. apply H. simpl. now right. 
Qed.


Lemma NormalForm_i_Sequential : forall c, NormalForm c -> Sequential c.
Proof.
intros. induction H;auto with eqDB.
- inversion H;
  constructor; subst; auto with eqDB;
  apply Sequential_Σ; intros;
  rewrite in_map_iff in *; destruct_ctx; subst; try constructor;
  (try constructor); destruct x; apply in_combine_r in H3; auto.
Qed.

Lemma NormalForm_trans : forall c, NormalForm c -> exists c', translate_aux c = Some c'.
Proof.
intros. apply translate_aux_sequential. auto using NormalForm_i_Sequential.
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
- constructor. constructor.
- rewrite decompose_map. erewrite map_ext. eapply NFList.
  * destruct (o_destruct c); rewrite H0; auto with eqDB.
  * intros. rewrite in_map_iff in *. destruct_ctx.
    subst. auto.
  * intros. simpl. auto.
Qed.



Lemma sum_decomposition_exists : forall c, exists c', NormalForm c' /\ c =R= c'.
Proof.
intros. exists (plus_norm c). split. apply plus_norm_NormalForm. symmetry. apply plus_norm_c_eq.
Qed.













 
