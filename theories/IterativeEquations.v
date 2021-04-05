Require Import CSL.IterativeContract.
Require Import Setoid.
Require Import Init.Tauto btauto.Btauto.
Require Import Bool.Bool.
Require Import Lists.List.
Import ListNotations.
(*******************************************************************************************************)
Set Implicit Arguments.

Definition contract_relation := Contract -> Contract -> Prop.

Notation "c0 ==~== c1" := (forall s, s ==~ c0 <-> s ==~ c1) (at level 73, no associativity).

Definition non_empty_relation (R : contract_relation) := exists c0 c1, R c0 c1.

Definition bisimulation (R: contract_relation) := non_empty_relation R /\ forall c0 c1, R c0 c1 -> nu c0 = nu c1 /\ forall e, R (c0/e) (c1/e).

(*c0 and c1 are in a bisimilarity written as c0 ~ c1*)
Notation "c0 ~ c1" := (exists R, bisimulation R /\ R c0 c1)(at level 73, no associativity).

(*
Lemma bi_union : forall R0 R1, bisimulation R0 -> bisimulation R1 -> bisimulation (fun x y => R0 x y \/ R1 x y).
Proof.
intros. destruct H, H0. destruct H0 as [c0 [c1 P]]. split.
- exists c0. exists c1. right. auto.
- intros. destruct H0.
  * apply H1 in H0 as [H0 H0']. split ; auto.
  * apply H2 in H0 as [H0 H0']. split ; auto.
Qed.*)

Lemma simpl_bisim_nu : forall (c0 c1 : Contract), c0 ~ c1 -> nu c0 = nu c1.
Proof. 
intros. destruct H. destruct H. unfold bisimulation in H.
destruct H. specialize H1 with c0 c1.
apply H1 in H0. destruct H0. assumption. 
Qed.

Lemma simpl_bisim_derive : forall (c0 c1 : Contract)(e : EventType), 
                           c0 ~ c1 -> c0/e ~ c1/e.
Proof. intros.  destruct H. exists x. destruct H. split;auto.
       destruct H. apply H1 in H0. destruct H0. auto.
Qed.

Hint Resolve simpl_bisim_nu  simpl_bisim_derive : bisimB.

CoInductive Bisimilarity : Contract -> Contract -> Prop :=
 CBisimilarity c0 c1 (H0: forall e, Bisimilarity (c0/e) (c1/e)) (H1: nu c0 = nu c1) : Bisimilarity c0 c1.

(*Bisimilarity predicate over contract relations*)
Definition bisimilarity (R : contract_relation) := forall c0 c1, R c0 c1 <-> Bisimilarity c0 c1.
Global Transparent bisimilarity.

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


Lemma matches_eq_is_bisimulation : bisimulation (fun c0 c1 => c0 ==~== c1).
Proof.
split.
- exists Failure. exists Failure. reflexivity.
- split.
  * apply eq_true_iff_eq. now repeat rewrite nu_empty.
  * intros. now repeat rewrite <- derive_spec_comp. 
Qed.

(*c0 ==~== c1 is a bisimilarity*)
Theorem matches_eq_is_bisimilarity : bisimilarity (fun c0 c1 => forall s, s ==~ c0 <-> s ==~ c1).
Proof.
split. 
- generalize dependent c1. generalize dependent c0. cofix matches_eq_is_bisimilarity.
  intros. constructor.
  * intros. apply matches_eq_is_bisimilarity. setoid_rewrite <- derive_spec_comp. auto.
  * apply eq_true_iff_eq. repeat rewrite nu_empty. auto.
- intro.
  repeat setoid_rewrite matches_Matches. intro. generalize dependent c1.
  generalize dependent c0. induction s;intros.
  * inversion H. repeat rewrite <- matches_Matches. repeat rewrite <- nu_empty.
    now rewrite H1.
  * repeat rewrite derive_spec2. inversion H. auto.
Qed.


Reserved Notation "c0 =ACI= c1" (at level 63).
Inductive c_eq_aci : Contract -> Contract -> Prop :=
    | cc_plus_assoc c0 c1 c2 : (c0 _+_ c1) _+_ c2 =ACI= c0 _+_ (c1 _+_ c2) (*ACI axioms*)
    | cc_plus_comm c0 c1: c0 _+_ c1 =ACI= c1 _+_ c0
    | cc_plus_idemp c : c _+_ c =ACI= c 
    | cc_trans c0 c1 c2 (H1 : c0 =ACI= c1) (H2 : c1 =ACI= c2) : c0 =ACI= c2 (*transitivity*)
    | cc_ctx_plus c0 c0' c1 c1' (H1 : c0 =ACI= c0') (H2 : c1 =ACI= c1') : c0 _+_ c1 =ACI= c0' _+_ c1' (*ctx rules*)
    | cc_ctx_seq c0 c0' c1 c1' (H1 : c0 =ACI= c0') (H2 : c1 =ACI= c1') : c0 _;_ c1 =ACI= c0' _;_ c1'
    where "c0 =ACI= c1" := (c_eq_aci c0 c1).
Hint Constructors c_eq_aci : core.

Lemma c_eq_aci_nu : forall c0 c1, c0 =ACI= c1 -> nu c0 = nu c1.
Proof.
intros. induction H;simpl; try btauto.
- rewrite IHc_eq_aci1. auto.
- rewrite IHc_eq_aci1. now rewrite IHc_eq_aci2. 
- rewrite IHc_eq_aci1. now rewrite IHc_eq_aci2.
Qed. 

Ltac nu_destruct :=
  repeat match goal with
         | [ |- context[if nu ?c then _ else _] ] => destruct (nu c) eqn:?Heqn
         end.

Lemma c_eq_aci_derive : forall c0 c1, c0 =ACI= c1 -> (forall e, c0/e =ACI= c1/e).
Proof.
intros. induction H; try solve [simpl ; eauto].
simpl. nu_destruct;auto.
all: apply c_eq_aci_nu in H; rewrite Heqn in H; rewrite Heqn0 in H; discriminate.
Qed.

Reserved Notation "c0 =R= c1" (at level 63).
CoInductive c_eq : Contract -> Contract -> Prop :=
  | c_aci c0 c1 (H: c0 =ACI= c1) : c0 =R= c1
  | c_fix c0 c1 (H0: forall e, c0/e =R= c1/e) (H1 : nu c0 = nu c1) : c0 =R= c1
    where "c0 =R= c1" := (c_eq c0 c1).

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
Qed.

(*Co-recursive call only needed for showing -> *)
Lemma c_eq_is_bisimilarity : bisimilarity c_eq.
Proof. 
split; generalize dependent c1; generalize dependent c0.
- cofix c_eq_is_bisimilarity. intros.
  constructor; auto using c_eq_nu, c_eq_derive.
- cofix H. intros. destruct H0. apply c_fix.
  * intros. auto.
  * auto.
Qed.


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
