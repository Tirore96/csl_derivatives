Require Import CSL.IterativeContract.
Require Import Setoid.
Require Import Init.Tauto btauto.Btauto.
Require Import Bool.Bool.

(*******************************************************************************************************)


Reserved Notation "c0 =ACI= c1" (at level 63).
Inductive aci_eq : Contract -> Contract -> Prop :=
  | aci_assoc c0 c1 c2 : (c0 _+_ c1 ) _+_ c2 =ACI= c0 _+_ (c1 _+_ c2) (*B1*)
  | aci_comm c0 c1: c0 _+_ c1 =ACI= c1 _+_ c0 (*B3*)
  | aci_idemp c : c _+_ c =ACI= c (*B6*)
  | aci_symm c0 c1 (H: c0 =ACI= c1) : c1 =ACI= c0 
  | aci_trans c0 c1 c2 (H0: c0 =ACI= c1) (H1: c1 =ACI= c2) : c0 =ACI= c2 
  | aci_ctx_plus c0 c0' c1 c1' (H1 : c0 =ACI= c0') (H2 : c1 =ACI= c1') : c0 _+_ c1 =ACI= c0' _+_ c1'
  | aci_ctx_seq c0 c0' c1 c1' (H1 : c0 =ACI= c0') (H2 : c1 =ACI= c1') : c0 _;_ c1 =ACI= c0' _;_ c1'
   where "c0 =ACI= c1" := (aci_eq c0 c1).
Hint Constructors aci_eq : core.





Lemma ACI_nu : forall (c0 c1 : Contract), c0 =ACI= c1 -> nu c0 = nu c1.
Proof. intros; induction H;simpl ; 
try solve [ btauto;auto | rewrite IHaci_eq1; rewrite IHaci_eq2; reflexivity].
rewrite IHaci_eq.  reflexivity. Qed.

Ltac Nu_destruct :=
  repeat match goal with
         | [ |- context[if Nu_dec ?c then _ else _] ] => destruct (Nu_dec c)
         end.
Ltac nnn :=
 match goal with
 | [ H1 : Nu ?c , H2 : NotNu ?c |- _ ] =>  idtac "match " H1 H2; fail
 | _ => idtac
 end.

Lemma ACI_derive : forall (c0 c1 : Contract), c0 =ACI= c1 -> (forall (e : EventType), c0/e =ACI= c1/e).
Proof. intros; induction H ; try solve [simpl;auto | eauto ].
simpl. Nu_destruct;auto.

 nnn. auto.  
- eauto. subst. Qed.

Reserved Notation "c0 =ACI+= c1" (at level 63).
Inductive aci_p_eq : Contract -> Contract -> Prop :=
 | aci_p_aci c0 c1 (H: c0 =ACI= c1) : c0 =ACI+= c1
 | aci_p_seq_assoc c0 c1 c2 : (c0 _;_ c1) _;_ c2 =ACI+= c0 _;_ (c1 _;_ c2) (*B2*)
 | aci_p_distr_l c0 c1 c2 : c0 _;_ (c1 _+_ c2) =ACI+= (c0 _;_ c1) _+_ (c0 _;_ c2) (*B5*)
 | aci_p_distr_r c0 c1 c2 : (c0 _+_ c1) _;_ c2 =ACI+= (c0 _;_ c2) _+_ (c1 _;_ c2) (*B4*)
 | aci_p_seq_neut_l c : c _;_ Success =ACI+= c (*B7*)
 | aci_p_seq_neut_r c : Success _;_ c =ACI+= c (*B7^R*)
 | aci_p_seq_failure_l c :  c _;_ Failure =ACI+= Failure (*B8*) 
 | aci_p_seq_failure_r c :  Failure _;_ c =ACI+= Failure (*B8^R*) 
 | aci_p_plus_neut c: c _+_ Failure =ACI+= c (*B9*)
 where "c0 =ACI+= c1" := (aci_p_eq c0 c1).


Lemma ACI_P_nu : forall (c0 c1 : Contract), c0 =ACI+= c1 -> nu c0 = nu c1.
Proof. intros; inversion H;simpl ; try btauto; auto using ACI_nu. Qed.



Hint Rewrite aci_p_distr_l aci_p_distr_r : base_distr.

Lemma ACI_P_derive : forall (c0 c1 : Contract), c0 =ACI+= c1 -> (forall (e : EventType), c0/e =ACI+= c1/e).
Proof. intros. inversion H. try solve [ auto using aci_p_aci,ACI_derive | simpl;auto].
- simpl. Nu_destruct.
  * rewrite aci_p_distr_r. autorewrite with base_distr. , aci_p_distr_r. auto. simpl. destruct (N


Add Parametric Relation : Contract aci_eq
  reflexivity proved by c_refl
  symmetry proved by c_sym
  transitivity proved by c_trans
  as Contract_setoid.

Add Parametric Morphism : CPlus with
signature c_eq ==> c_eq ==> c_eq as c_eq_plus_morphism.
Proof.
  intros. auto.
Qed.

Add Parametric Morphism : CSeq with
signature c_eq ==> c_eq ==> c_eq as c_eq_seq_morphism.
Proof.
  intros. auto.
Qed.

Notation "c0 =S= c1" := (c0 =ACI= c1 \/ c0 =ACI+= c1)
                    (at level 63, right associativity).

Lemma Grabmeyer_L1 : forall (c0 c1 : Contract) e, c0 =S= c1 -> nu c0 = nu c1 /\ (c0 / e) =S= (c1 / e).
Proof. Admitted.















  

(*
Lemma aci_p_eq_nu : forall (c0 c1 : Contract), c0 =ACI+= c1 -> nu c0 = nu c1.
Proof. Admitted.

Lemma aci_eq_derive : forall (c0 c1 : Contract), c0 =ACI= c1 -> (forall (e : EventType), c0/e =ACI= c1/e).
Proof. Admitted.

Lemma aci_eq_bisimulation : forall (c0 c1 : Contract), c0 =ACI= c1 -> nu c0 = nu c1 /\ (forall (e : EventType), c0/e =ACI= c1/e). 
Proof.
intros. split. auto using aci_eq_nu. auto using aci_eq_derive. Qed.*)



Reserved Notation "c0 =R= c1" (at level 63).

CoInductive c_eq : Contract -> Contract -> Prop :=
  | c_plus_assoc c0 c1 c2 : (c0 _+_ c1) _+_ c2 =R= c0 _+_ (c1 _+_ c2)
  | c_plus_comm c0 c1: c0 _+_ c1 =R= c1 _+_ c0
  | c_plus_neut c: c _+_ Failure =R= c
  | c_plus_idemp c : c _+_ c =R= c 
  | c_seq_assoc c0 c1 c2 : (c0 _;_ c1) _;_ c2 =R= c0 _;_ (c1 _;_ c2)
  | c_seq_neut_l c : (Success _;_ c) =R= c 
  | c_seq_neut_r c : c _;_ Success =R= c 
  | c_seq_failure_l c : Failure _;_ c =R= Failure    (*EXTRA AXIOM*)
  | c_seq_failure_r c :  c _;_ Failure =R= Failure 
  | c_distr_l c0 c1 c2 : c0 _;_ (c1 _+_ c2) =R= (c0 _;_ c1) _+_ (c0 _;_ c2)
  | c_distr_r c0 c1 c2 : (c0 _+_ c1) _;_ c2 =R= (c0 _;_ c2) _+_ (c1 _;_ c2)
  | c_refl c : c =R= c
  | c_sym c0 c1 (H: c0 =R= c1) : c1 =R= c0
  | c_trans c0 c1 c2 (H1 : c0 =R= c1) (H2 : c1 =R= c2) : c0 =R= c2
  | c_plus_morph c0 c0' c1 c1' (H1 : c0 =R= c0') (H2 : c1 =R= c1') : c0 _+_ c1 =R= c0' _+_ c1'
  | c_seq_morph c0 c0' c1 c1' (H1 : c0 =R= c0') (H2 : c1 =R= c1') : c0 _;_ c1 =R= c0' _;_ c1'
  | c_test c0 c1 (H1: forall e : EventType, c0 / e =R= c1 / e) : c0 =R= c1 (*Test Axiom*)
  where "c1 =R= c2" := (c_eq c1 c2).

Hint Constructors c_eq : core.

Add Parametric Relation : Contract c_eq
  reflexivity proved by c_refl
  symmetry proved by c_sym
  transitivity proved by c_trans
  as Contract_setoid.

Add Parametric Morphism : CPlus with
signature c_eq ==> c_eq ==> c_eq as c_eq_plus_morphism.
Proof.
  intros. auto.
Qed.

Add Parametric Morphism : CSeq with
signature c_eq ==> c_eq ==> c_eq as c_eq_seq_morphism.
Proof.
  intros. auto.
Qed.




(*Coinduction principle*)
Section bisimilar.
  Variable R : Contract -> Contract -> Prop.
  Hypothesis Bi_Nu : forall c1 c2, R c1 c2 -> nu c1 = nu c2.
  Hypothesis Bi_Derive : forall c1 c2 e, R c1 c2 -> R (c1 / e) (c2 / e).
  
  Lemma bisimilar_eq : forall c1 c2, R c1 c2 -> (forall (s : Trace), s ==~ c1 <-> s ==~ c2).
  Proof.
  split;intros.
  - generalize dependent c2. generalize dependent c1. induction s;intros.
    * apply Bi_Nu in H. destruct (nu c1) eqn:Heqn.
      ** symmetry in H. apply nu_true in H. apply Nu_empty in H. assumption.
      ** rewrite <- Nu_empty in H0. apply nu_false in Heqn. nnn Heqn.
    * rewrite derive_spec_comp in H0. rewrite derive_spec_comp. eapply IHs. eassumption. auto.
  - generalize dependent c2. generalize dependent c1. induction s;intros.
    * apply Bi_Nu in H. destruct (nu c1) eqn:Heqn.
      ** symmetry in H. apply nu_true in Heqn. apply Nu_empty in Heqn. assumption.
      ** rewrite <- Nu_empty in H0. symmetry in H. apply nu_false in H. nnn H.
    * rewrite derive_spec_comp in H0. rewrite derive_spec_comp. eapply IHs. eauto. assumption.
  Qed.

End bisimilar.


Check R.
Check bisimultation.

























(*

Lemma c_eq_derive : forall (c0 c1 : Contract)(e : EventType), c0 =R= c1 -> c0 / e =R= c1 / e.
Proof.
cofix c_eq_derive.
intros.
induction H.
- simpl. auto.
- simpl. auto.
- simpl. auto.
- simpl. auto.
- simpl. destruct (Nu_dec (c2 _;_ c3)).
  * destruct (Nu_dec c2); inversion n; subst.
    ** destruct (Nu_dec c3).
      *** rewrite c_distr_r. rewrite c_seq_assoc. rewrite c_plus_assoc. reflexivity. 
      *** nnn n1.
    ** nnn n0.
  * inversion n;subst.
    ** destruct (Nu_dec c2).
      *** destruct (Nu_dec c3).
        **** nnn H3.
        **** nnn H3.
      *** auto.
    ** destruct (Nu_dec c2).
      *** destruct (Nu_dec c3).
        **** nnn H3.
        **** rewrite c_distr_r. rewrite c_seq_assoc. auto.
      *** auto.
- simpl. rewrite c_seq_failure_l. eauto.
- simpl. destruct (Nu_dec c1);eauto.
- simpl. auto.
- simpl. destruct (Nu_dec c);eauto.
- simpl. destruct (Nu_dec c2).
  * rewrite c_distr_l. repeat rewrite <- c_plus_assoc. eauto.
  * eauto.
- simpl. destruct (Nu_dec (c2 _+_ c3)).
  * destruct (Nu_dec c2).
    ** destruct (Nu_dec c3).
      *** rewrite c_distr_r. rewrite c_plus_assoc. rewrite (c_plus_comm _ (c4 / e)).
          rewrite <- c_plus_assoc. rewrite <- c_plus_assoc. eauto.
      *** rewrite c_distr_r. rewrite c_plus_assoc. rewrite (c_plus_comm _ (c4 / e)).
          rewrite <- c_plus_assoc. auto.
    ** destruct (Nu_dec c3).
      *** rewrite c_distr_r. rewrite c_plus_assoc. auto.
      *** inversion n. nnn n0. nnn n1.
  * inversion n. subst. destruct (Nu_dec c2).
    ** nnn H4.
    ** destruct (Nu_dec c3).
      *** nnn H5.
      *** rewrite c_distr_r. auto.
- subst. reflexivity.
- subst. 



 rewrite c_plus_assoc. rewrite (c_plus_comm (c3 / e _;_ c4)).
          rewrite <- (c_plus_assoc (c4 / e)). rewrite c_plus_idemp.
          rewrite (c_plus_comm (c4 / e)). rewrite <- c_plus_assoc. rewrite c_plus_assoc.
          rewrite (c_plus_comm (c4 / e ) (c4 / e _+_ c3 / e _;_ c4)). eauto.
 rewrite (c_plus_comm _ (c4 / e)).
          rewrite <- c_plus_assoc. rewrite <- c_plus_assoc. eauto.
  * eauto.
  * eauto.
*)