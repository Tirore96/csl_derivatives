Require Import CSL.Iteration.Contract.
Require Import Setoid.
Require Import Init.Tauto btauto.Btauto.
Require Import Bool.Bool  Bool.Sumbool.
Require Import Lists.List.
Import ListNotations.
Require Import Bool.Bool.
Require Import micromega.Lia.
From Equations Require Import Equations.
(*******************************************************************************************************)
Set Implicit Arguments.

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

(*
Definition non_empty_relation (R : contract_relation) := exists c0 c1, R c0 c1.

Definition bisimulation (R: contract_relation) := non_empty_relation R /\ forall c0 c1, R c0 c1 -> nu c0 = nu c1 /\ forall e, R (e \ c0) (e \ c1).

(*c0 and c1 are in a bisimilarity written as c0 ~ c1*)
Notation "c0 ~ c1" := (exists R, bisimulation R /\ R c0 c1)(at level 73, no associativity).

Lemma simpl_bisim_nu : forall (c0 c1 : Contract), c0 ~ c1 -> nu c0 = nu c1.
Proof. 
intros. destruct H. destruct H. unfold bisimulation in H.
destruct H. specialize H1 with c0 c1.
apply H1 in H0. destruct H0. assumption. 
Qed.

Lemma simpl_bisim_derive : forall (c0 c1 : Contract)(e : EventType), 
                           c0 ~ c1 -> e \ c0 ~ e \ c1.
Proof. intros.  destruct H. exists x. destruct H. split;auto.
       destruct H. apply H1 in H0. destruct H0. auto.
Qed.

Hint Resolve simpl_bisim_nu  simpl_bisim_derive : bisimB.*)



(*Bisimilarity predicate over contract relations*)
(*
Definition bisimilarity (R : contract_relation) := forall c0 c1, R c0 c1 <-> Bisimilarity c0 c1.
Global Transparent bisimilarity.*)
(*
Lemma exists_bisimulation_i_Bisimilarity : forall c0 c1, c0 ~ c1 -> Bisimilarity c0 c1.
Proof.
cofix exists_bisimulation_i_Bisimilarity.
intros. constructor.
- intros. apply exists_bisimulation_i_Bisimilarity. auto with bisimB.
- auto with bisimB.
Qed.

Lemma Bisimilarity_is_bisimulation : bisimulation Bisimilarity.
Proof.
split;intros.
- exists Failure. exists Failure. cofix Bisimilarity_is_bisimulation.
  apply CBisimilarity;intros;simpl;auto.
- destruct H; split;auto.
Qed.

Lemma Bisimilarity_i_exists_bisimulation : forall c0 c1, Bisimilarity c0 c1 -> c0 ~ c1.
Proof.
intros. exists Bisimilarity. split;auto using Bisimilarity_is_bisimulation.
Qed. 

(*Sanity check*)
Theorem exists_bisimulation_is_bisimilarity : bisimilarity (fun c0 c1 => c0 ~ c1). 
Proof.
split; auto using exists_bisimulation_i_Bisimilarity,Bisimilarity_i_exists_bisimulation.
Qed.


Lemma bisimilarity_non_empty : forall (R : contract_relation), bisimilarity R -> non_empty_relation R.
Proof.
intros. destruct H with Failure Failure.
assert (HA: Bisimilarity Failure Failure).
{ cofix bisimilarity_non_empty. constructor. intros. now simpl. auto.  }
exists Failure. exists Failure. auto.
Qed.
 
Lemma bisimilarity_i_bisimulation : forall (R : contract_relation), bisimilarity R -> bisimulation R.
Proof.
intros. unfold bisimilarity in H. split;auto using bisimilarity_non_empty.
intros. pose proof H. destruct H with c0 c1. apply H1 in H0.
destruct H0. split;auto. intros. rewrite H1. auto.
Qed.


Lemma matches_eq_is_bisimulation : bisimulation (fun c0 c1 => c0 =~= c1).
Proof.
split.
- exists Failure. exists Failure. reflexivity.
- split.
  * apply eq_true_iff_eq. setoid_rewrite Matches_Comp_iff_matchesb in H.
    specialize H with []. simpl in*. auto.
  * intros. now repeat rewrite <- derive_spec_comp. 
Qed.*)

(*c0 ==~== c1 is a bisimilarity*)



Reserved Notation "c0 =ACI= c1" (at level 63).
Inductive c_eq_aci : Contract -> Contract -> Prop :=
    | cc_plus_assoc c0 c1 c2 : (c0 _+_ c1) _+_ c2 =ACI= c0 _+_ (c1 _+_ c2) (*ACI axioms*)
    | cc_plus_comm c0 c1: c0 _+_ c1 =ACI= c1 _+_ c0
    | cc_plus_idemp c : c _+_ c =ACI= c 
    | cc_trans c0 c1 c2 (H1 : c0 =ACI= c1) (H2 : c1 =ACI= c2) : c0 =ACI= c2 (*transitivity*)
    | cc_ctx_plus c0 c0' c1 c1' (H1 : c0 =ACI= c0') (H2 : c1 =ACI= c1') : c0 _+_ c1 =ACI= c0' _+_ c1' (*ctx rules*)
    | cc_refl c : c =ACI= c
    | cc_sym c0 c1 (H : c0 =ACI= c1) : c1 =ACI= c0
    where "c0 =ACI= c1" := (c_eq_aci c0 c1).
Hint Constructors c_eq_aci : core.

Add Parametric Relation : Contract c_eq_aci
  reflexivity proved by cc_refl
  symmetry proved by cc_sym
  transitivity proved by cc_trans
  as Contract_setoid.

Add Parametric Morphism : CPlus with
signature c_eq_aci ==> c_eq_aci ==> c_eq_aci as c_eq_aci_plus_morphism.
Proof.
  intros. auto.
Qed.

Lemma c_eq_aci_nu : forall c0 c1, c0 =ACI= c1 -> nu c0 = nu c1.
Proof.
intros. induction H;simpl; try btauto.
- rewrite IHc_eq_aci1. auto.
- rewrite IHc_eq_aci1. now rewrite IHc_eq_aci2. 
- intuition. 
Qed. 

Ltac nu_destruct :=
  repeat match goal with
         | [ |- context[if nu ?c then _ else _] ] => destruct (nu c) eqn:?Heqn
         end.

Lemma o_aci : forall c0 c1, c0 =ACI= c1 -> o c0 = o c1.
Proof.
intros. apply c_eq_aci_nu in H. o_destruct; unfold o; now rewrite H.
Qed. 


Lemma c_eq_aci_derive : forall c0 c1, c0 =ACI= c1 -> (forall e, c0/e =ACI= c1/e).
Proof.
intros. induction H; try solve [simpl ; eauto].
Qed.


Reserved Notation "c0 =R= c1" (at level 63).
CoInductive c_eq : Contract -> Contract -> Prop :=
  | c_fix c0 c1 (H0: forall e, c0/e =R= c1/e) (H1 : nu c0 = nu c1) : c0 =R= c1
    where "c0 =R= c1" := (c_eq c0 c1).
(*
Lemma c_eq_nu : forall c0 c1, c0 =R= c1 -> nu c0 = nu c1.
Proof.
intros. inversion H;auto using c_eq_aci_nu.
Qed.

Lemma c_eq_derive : forall c0 c1, c0 =R= c1 -> (forall e, c0/e =R= c1/e).
Proof.
cofix H.
intros. inversion H0. 
- constructor. auto using c_eq_aci_derive. 
- apply H1.
Qed.*)





Theorem c_eq_soundness : forall c0 c1, c0 =R= c1 -> c0 ==~== c1.
Proof.
intros. pose proof c_eq_is_bisimilarity. pose proof matches_eq_is_bisimilarity.
unfold bisimilarity in *. specialize H1 with c0 c1.
apply <- H1. now apply H0.
Qed.

Theorem c_eq_completeness : forall c0 c1, c0 ==~== c1 -> c0 =R= c1.
Proof.
intros. pose proof c_eq_is_bisimilarity. pose proof matches_eq_is_bisimilarity.
unfold bisimilarity in *. rewrite H0. now rewrite <- H1.
Qed.

Theorem c_eq_iff : forall c0 c1, c0 =R= c1 <-> c0 ==~== c1.
Proof.
intros. split;auto using c_eq_completeness,c_eq_soundness.
Qed.

Lemma c_eq_refl : forall c, c =R= c.
Proof.
intros. apply c_eq_completeness. split;auto.
Qed.

Hint Immediate c_eq_refl : core.

Lemma c_eq_sym : forall c0 c1, c0 =R= c1 -> c1 =R= c0.
Proof.
intros. apply c_eq_completeness. intros. apply c_eq_soundness with (s:=s) in H.
now symmetry in H.
Qed.

Lemma c_eq_trans : forall c0 c1 c2, c0 =R= c1 -> c1 =R= c2 -> c0 =R= c2.
Proof.
intros. apply c_eq_completeness. intros. apply c_eq_soundness with (s:=s ) in H.
apply c_eq_soundness with (s:=s ) in H0. rewrite H. now rewrite H0.
Qed.

Add Parametric Relation : Contract c_eq
  reflexivity proved by c_eq_refl
  symmetry proved by c_eq_sym
  transitivity proved by c_eq_trans
  as Contract_c_eq_setoid.

Add Parametric Morphism : CPlus with
signature c_eq ==> c_eq ==> c_eq as c_eq_plus_morphism.
Proof.
  intros. apply c_eq_completeness. intros. apply c_eq_soundness with (s:=s) in H. 
   apply c_eq_soundness with (s:=s) in H0. split;intros.
  - inversion H1;auto. apply MPlusL. now rewrite <- H. apply MPlusR. now rewrite <- H0.
  - inversion H1;auto. apply MPlusL. now rewrite H. apply MPlusR. now rewrite H0.
Qed.

Add Parametric Morphism : CSeq with
signature c_eq ==> c_eq ==> c_eq as c_eq_seq_morphism.
Proof.
  intros. apply c_eq_completeness. intros. split;intros. inversion H1. apply c_eq_soundness with (s:=s1) in H as H'.
  constructor. now rewrite <- H'. apply c_eq_soundness with (s:=s2) in H0 as H''. now rewrite <- H''.
  inversion H1. apply c_eq_soundness with (s:=s1) in H as H'. 
    constructor. now rewrite H'. apply c_eq_soundness with (s:=s2) in H0 as H''. now rewrite H''.
Qed.

Ltac c_eq_inversion_tac :=
   match goal with
         | [ H: ?c =R= ?c' |- _ ] => inversion H
         end.

Ltac rewrite_nu_tac := 
   repeat (match goal with
            | [ H: nu ?c = nu ?c' |- _ ] => rewrite H;clear H
           end).

(*Declare database*)
Hint Resolve c_eq_refl : coDB.

Ltac c_eq_tac := cofix IH;intros; (try c_eq_inversion_tac) ; constructor ; [intros;simpl;eauto with coDB | simpl;subst; try solve [rewrite_nu_tac ; btauto]].

(*Rewrites/Resolvers*)
Lemma c_eq_idempotent : forall c, c _+_ c =R= c.
Proof. c_eq_tac. Qed.

Lemma c_eq_plus_failure_right : forall c, c _+_ Failure =R= c.
Proof. c_eq_tac. Qed.

Lemma c_eq_plus_failure_left : forall c, Failure _+_ c =R= c.
Proof. c_eq_tac. Qed.


Hint Rewrite c_eq_idempotent c_eq_plus_failure_right c_eq_plus_failure_left : coDB.

(*Resolvers*)
Lemma c_eq_plus_right : forall c0 c1 c1', c1 =R= c1' -> c0 _+_ c1 =R= c0 _+_ c1'.
Proof. c_eq_tac. Qed.

Lemma c_eq_plus_left : forall c0 c0' c1, c0 =R= c0' -> c0 _+_ c1 =R= c0' _+_ c1.
Proof. c_eq_tac. Qed.

Lemma c_eq_plus_both : forall c0 c0' c1 c1', c0 =R= c0' -> c1 =R= c1' -> c0 _+_ c1 =R= c0' _+_ c1'.
Proof. intros. rewrite H. now rewrite H0.
Qed. 

Hint Resolve c_eq_plus_both c_eq_idempotent c_eq_plus_failure_left c_eq_plus_failure_right c_eq_plus_right c_eq_plus_left : coDB.

(*Immediates*)

Lemma plus_comm_ceq : forall c0 c1, (c0 _+_ c1) =R= (c1 _+_ c0).
Proof. c_eq_tac. Qed.

Hint Immediate plus_comm_ceq : coDB.

Lemma plus_assoc_ceq : forall c0 c1 c2, (c0 _+_ c1) _+_ c2 =R= c0 _+_ (c1 _+_ c2).
Proof. c_eq_tac. Qed.

Hint Resolve c_eq_plus_morphism plus_assoc_ceq : coDB.

Ltac c_eq_match_tac := intros;rewrite c_eq_iff; auto with icDB.


Lemma c_eq_Failure_seq :  forall c, Failure _;_ c =R= Failure.
Proof. c_eq_match_tac.
Qed.

Lemma c_eq_Success_seq :  forall c, Success _;_ c =R= c.
Proof. c_eq_match_tac.
Qed.

Hint Resolve c_eq_Failure_seq c_eq_Success_seq : coDB.

Hint Rewrite c_eq_Failure_seq c_eq_Success_seq : coDB.

Ltac auto_rwd := autorewrite with coDB using auto with coDB.


