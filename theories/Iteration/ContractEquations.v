Require Import CSL.Iteration.Contract.  
Require Import Lists.List Bool.Bool Bool.Sumbool Setoid Coq.Arith.PeanoNat.
Require Import micromega.Lia.
From Equations Require Import Equations.
Require Import Arith.
Require Import micromega.Lia.

Require Import Paco.paco.


Import ListNotations.

Set Implicit Arguments.
Inductive bisimilarity_gen bisim : Contract -> Contract -> Prop :=
 bisimilarity_con c0 c1 (H0: forall e, bisim (e \ c0) (e \ c1) : Prop ) (H1: nu c0 = nu c1) : bisimilarity_gen bisim c0 c1.



Definition Bisimilarity c0 c1 := paco2 bisimilarity_gen bot2 c0 c1.
Hint Unfold  Bisimilarity : core.

Lemma bisimilarity_gen_mon: monotone2 bisimilarity_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.
Hint Resolve bisimilarity_gen_mon : paco.


Theorem matches_eq_i_bisimilarity : forall c0 c1, (forall s, s(:) c0 <-> s(:)c1) -> Bisimilarity c0 c1.
Proof.
pcofix CIH. intros. pfold. constructor.
- intros. right. apply CIH.  setoid_rewrite <- derive_spec_comp. auto. 
- apply eq_true_iff_eq. setoid_rewrite Matches_Comp_iff_matchesb in H0.
  specialize H0 with []. simpl in*. auto.
Qed.

Theorem bisimilarity_i_matches_eq : forall c0 c1, Bisimilarity c0 c1 -> (forall s, s(:) c0 <-> s(:)c1).
Proof.
intros. generalize dependent c1. generalize dependent c0.
induction s;intros.
- repeat rewrite Matches_Comp_iff_matchesb. simpl.
  rewrite <- eq_iff_eq_true.  punfold H. inversion H. auto.
- repeat rewrite derive_spec_comp. apply IHs. punfold H. inversion_clear H.
  specialize H0 with a. pclearbot. auto.
Qed.

Theorem matches_eq_iff_bisimilarity : forall c0 c1, (forall s, s(:) c0 <-> s(:)c1) <-> Bisimilarity c0 c1.
Proof.
split;auto using matches_eq_i_bisimilarity, bisimilarity_i_matches_eq.
Qed.



Definition alphabet := [Notify;Transfer].

Lemma in_alphabet : forall e, In e alphabet.
Proof.
destruct e ; repeat (try apply in_eq ; try apply in_cons).
Qed.

Hint Resolve in_alphabet : eqDB.
Opaque alphabet.
(*
Fixpoint Σ (l : list Contract) : Contract :=
match l with
| [] => Failure
| c ::l => c _+_ (Σ l)
end.
*)

Fixpoint Σ (A:Type) (l : list A) (f : A -> Contract) : Contract :=
match l with
| [] => Failure
| c ::l => f c _+_ (Σ l f)
end.



Definition Σe es cs := Σ (combine es cs) (fun x => Event (fst x) _;_ snd x).


Definition Σed c := (Σ alphabet (fun a : EventType => Event a _;_ a \ c)).
Notation "Σe\ c" := (Σed c)
                    (at level 30, no associativity).



Reserved Notation "c0 =R= c1" (at level 63).

Section axiomatization.
  Variable co_eq : Contract -> Contract -> Prop.

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

| c_unfold c :  Success _+_ (c _;_ Star c) =R= Star c (*New star rule 1*)
| c_star_plus c :  Star (Success _+_ c) =R= Star c (*New star rule 2*)
| c_refl c : c =R= c
| c_sym c0 c1 (H: c0 =R=c1) : c1 =R=c0
| c_trans c0 c1 c2 (H1 : c0 =R=c1) (H2 : c1 =R=c2) : c0 =R=c2
| c_plus_ctx c0 c0' c1 c1' (H1 : c0 =R=c0') (H2 : c1 =R=c1') : c0 _+_ c1 =R=c0' _+_ c1'
| c_seq_ctx c0 c0' c1 c1' (H1 : c0 =R=c0') (H2 : c1 =R=c1') : c0 _;_ c1 =R=c0' _;_ c1'
| c_par_ctx c0 c0' c1 c1' (H1 : c0 =R=c0') (H2 : c1 =R=c1') : c0 _*_ c1 =R=c0' _*_ c1'
| c_star_ctx c0 c1 (H : c0 =R=c1) : Star c0 =R= Star c1  (*new context rule*)
| c_co_sum es ps  (H: forall p, In p ps -> co_eq (fst p) (snd p) : Prop) (*Apply coinductive premise here*)
                  : (Σe es (map fst ps)) =R= (Σe es (map snd ps))
 where "c1 =R= c2" := (c_eq c1 c2).

End axiomatization.
Check c_eq.

Notation "c0 = ( R ) = c1" := (c_eq R c0 c1)(at level 63).

Hint Constructors c_eq : eqDB.


Add Parametric Relation R : Contract (@c_eq R)
  reflexivity proved by (c_refl R)
  symmetry proved by (@c_sym R)
  transitivity proved by (@c_trans R)
  as Contract_setoid.

Add Parametric Morphism R : Par with
signature (c_eq R) ==> (c_eq R) ==> (c_eq R) as c_eq_par_morphism.
Proof.
intros. eauto with eqDB.
Qed.

Add Parametric Morphism R : CPlus with
signature (c_eq R) ==> (c_eq R) ==> (c_eq R) as c_eq_plus_morphism.
Proof.
intros. eauto with eqDB.
Qed.

Add Parametric Morphism R : CSeq with
signature (c_eq R) ==> (c_eq R) ==> (c_eq R) as co_eq_seq_morphism.
Proof.
intros. eauto with eqDB.
Qed.

Add Parametric Morphism R : Star with
signature (c_eq R) ==> (c_eq R) as c_eq_star_morphism.
Proof.
intros. eauto with eqDB.
Qed.




Lemma c_plus_neut_l : forall R c, Failure _+_ c =(R)= c.
Proof. intros. rewrite c_plus_comm. auto with eqDB.
Qed.

Lemma c_par_neut_l : forall R c, Success _*_ c =(R)= c.
Proof. intros. rewrite c_par_comm. auto with eqDB.
Qed.

Lemma c_par_failure_l  : forall R c, Failure _*_ c =(R)= Failure.
Proof. intros. rewrite c_par_comm. auto with eqDB.
Qed.

Lemma c_par_distr_r : forall R c0 c1 c2, (c0 _+_ c1) _*_ c2 =(R)= (c0 _*_ c2) _+_ (c1 _*_ c2).
Proof. intros. rewrite c_par_comm. rewrite c_par_distr_l. auto with eqDB.
Qed.




Hint Rewrite c_plus_neut_l 
             c_plus_neut 
             c_seq_neut_l
             c_seq_neut_r
             c_seq_failure_l 
             c_seq_failure_r 
             c_distr_l
             c_distr_r c_par_neut_l c_par_failure_l c_par_distr_r c_par_event
             c_par_neut c_par_failure c_par_distr_l : eqDB.

Ltac auto_rwd_eqDB := autorewrite with eqDB;auto with eqDB.


Definition co_eq c0 c1 := paco2 c_eq bot2 c0 c1.



Notation "c0 =C= c1" := (co_eq c0 c1)(at level 63).



Lemma c_eq_gen_mon: monotone2 c_eq. 
Proof.
unfold monotone2.
intros. induction IN; eauto with eqDB.
Qed.
Hint Resolve c_eq_gen_mon : paco.

(*
Lemma co_eq_refl : forall c, c =C= c.
Proof.
pcofix CIH.
intros. pfold. constructor.
Qed.

Lemma co_eq_sym : forall c0 c1, c0 =C= c1 -> c1 =C= c0.
Proof.
intros. pfold. punfold H. induction H;auto with eqDB.
eauto with eqDB.
Qed.

Lemma co_eq_trans : forall c0 c1 c2, c0 =C= c1 -> c1 =C= c2 -> c0 =C= c2.
Proof.
intros. punfold H. punfold H0. inversion H; try solve [inversion H0;subst;pfold; eapply c_trans;eauto].
all : subst; pfold; eauto with eqDB.
Qed.


Add Parametric Relation : Contract (co_eq)
  reflexivity proved by co_eq_refl
  symmetry proved by co_eq_sym
  transitivity proved by co_eq_trans
  as CoContract_setoid.

Add Parametric Morphism : Par with
signature co_eq ==> co_eq ==> co_eq as co_eq_par_morphism.
Proof.
intros. pfold. punfold H. punfold H0. eauto with eqDB.
Qed.

Add Parametric Morphism : CPlus with
signature co_eq ==> co_eq ==> co_eq as co_eq_plus_morphism.
Proof.
intros. pfold. punfold H. punfold H0. eauto with eqDB.
Qed.
Check co_eq_seq_morphism.
Add Parametric Morphism : CSeq with
signature co_eq ==> co_eq ==> co_eq as co_eq_seq_morphism2.
Proof.
intros. pfold. punfold H. punfold H0. eauto with eqDB.
Qed.

Add Parametric Morphism : Star with
signature co_eq ==> co_eq as co_eq_star_morphism.
Proof.
intros. pfold. punfold H. eauto with eqDB.
Qed.
*)


Ltac eq_m_left := repeat rewrite c_plus_assoc; apply c_plus_ctx;
                  auto_rwd_eqDB.

Ltac eq_m_right := repeat rewrite <- c_plus_assoc; apply c_plus_ctx;
                  auto_rwd_eqDB.


Lemma Σe_not_nu : forall es l0, nu (Σe es l0) = false.
Proof.
unfold Σe.
intros. induction ((combine es l0)).
- simpl. auto.
- simpl. rewrite IHl. auto.
Qed.

Ltac finish H := simpl; right; apply H; pfold; auto_rwd_eqDB.

Require Import Coq.btauto.Btauto.
Lemma c_eq_nu : forall R (c0 c1 : Contract) , c0 =(R)= c1 -> nu c0 = nu c1.
Proof. 
intros. induction H; simpl; auto with bool; try btauto.
all : try (rewrite IHc_eq1; rewrite IHc_eq2; auto).
repeat rewrite Σe_not_nu. auto.
Qed.


Lemma co_eq_nu : forall (c0 c1 : Contract) , c0 =C= c1 -> nu c0 = nu c1.
Proof. 
intros. eapply c_eq_nu. punfold H.
Qed.


Lemma Σederive_eq : forall es ps R e, (forall p : Contract * Contract, In p ps ->  (fst p) =(R)= (snd p)) -> e \ (Σe es (map fst ps)) =(R)= e \ (Σe es (map snd ps)).
Proof.
induction es;intros;unfold Σe.
- simpl. reflexivity.
- simpl. destruct ps.
  * simpl. reflexivity.
  * simpl. eq_event_destruct;subst.
    ** auto_rwd_eqDB. rewrite H; auto using in_eq.
       eq_m_left. unfold Σe in IHes. apply IHes.
       intros. apply H. simpl. right. auto.
    ** auto_rwd_eqDB.  unfold Σe in IHes. apply IHes.
       intros. apply H. simpl. right. auto.
Qed.

Lemma co_eq_derive : forall (c0 c1 : Contract) e, c0 =C= c1 -> e \ c0 =C= e \ c1.
Proof.
intros. pfold. punfold H. induction H; try solve [ simpl; auto_rwd_eqDB] . 
- simpl. destruct (nu c0) eqn:Heqn;simpl.
    ** destruct (nu c1).
      *** auto_rwd_eqDB. repeat rewrite <- c_plus_assoc.
          auto with eqDB.
      *** auto_rwd_eqDB. 
    ** auto_rwd_eqDB.
- simpl;destruct (nu c);auto_rwd_eqDB. 
- simpl. destruct (nu c); auto_rwd_eqDB.
- simpl. destruct (nu c0); auto_rwd_eqDB.
    eq_m_left. eq_m_right.
- simpl. destruct (nu c0); destruct (nu c1);simpl; auto_rwd_eqDB;
    repeat rewrite c_plus_assoc ; rewrite (c_plus_comm _ (e \ c2)).
    eq_m_left.  auto_rwd_eqDB.
- simpl. auto_rwd_eqDB. eq_m_right. 
- simpl. rewrite c_plus_comm. eq_m_right.
- simpl. auto_rwd_eqDB. eq_m_left. eq_m_right.
- simpl. auto_rwd_eqDB. eq_event_destruct;subst;auto_rwd_eqDB.
- simpl. auto_rwd_eqDB. destruct (nu c);auto_rwd_eqDB.
- eauto with eqDB.
- simpl. destruct (nu c0) eqn:Heqn; destruct (nu c0') eqn:Heqn2;simpl.
  rewrite IHc_eq1. rewrite IHc_eq2.
  rewrite H0. reflexivity. apply c_eq_nu in H.
   rewrite Heqn in H. rewrite Heqn2 in H. discriminate.
   apply c_eq_nu in H.
   rewrite Heqn in H. rewrite Heqn2 in H. discriminate.
  rewrite IHc_eq1. rewrite H0. reflexivity.
- apply Σederive_eq;auto. intros. apply H in H0.
  pclearbot. punfold H0.
Qed.

Lemma bisim_soundness : forall (c0 c1 : Contract), c0 =C= c1 -> Bisimilarity c0 c1.
Proof.
pcofix CIH. 
intros. pfold. constructor.
- intros. right. apply CIH.  apply co_eq_derive. auto.
- auto using co_eq_nu.
Qed.


(***************Completeness***********)


Definition o c := if nu c then Success else Failure.
Transparent o.
Lemma o_plus : forall c0 c1 R, o (c0 _+_ c1) =(R)= o c0 _+_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;auto_rwd_eqDB.
Qed.

Lemma o_seq : forall c0 c1 R, o (c0 _;_ c1) =(R)= o c0 _;_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;auto_rwd_eqDB.
Qed.

Lemma o_par : forall c0 c1 R, o (c0 _*_ c1) =(R)= o c0 _*_ o c1.
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


(****************New******************)


Lemma Σ_alphabet_or : forall R alphabet0 e,
 Σ alphabet0 (fun a : CSLC.EventType => if EventType_eq_dec e a then Success else Failure) =(R)= Success /\ In e alphabet0 \/
 Σ alphabet0 (fun a : CSLC.EventType => if EventType_eq_dec e a then Success else Failure) =(R)= Failure /\ ~(In e alphabet0).
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
Lemma Σ_alphabet : forall e R, Σ alphabet (fun a => if EventType_eq_dec e a then Success else Failure) =(R)= Success.
Proof.
intros. destruct (Σ_alphabet_or R alphabet e).
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
Definition fun_eq R (f0 f1 : EventType -> Contract) := (forall a, f0 a =(R)= f1 a).

Add Parametric Morphism R l : (Σ l)  with
signature (@fun_eq R)  ==> (@ c_eq R) as c_eq_Σ_morphism.
Proof.
induction l;intros; simpl; auto with eqDB.
Qed.



Notation "f0 =(λ R )= f1" := (fun_eq R f0 f1)(at level 63).

Check c_eq_Σ_morphism.

Lemma fun_eq_refl : forall R f, f =(λ R)= f.
Proof.
intros. unfold fun_eq. auto with eqDB.
Qed.

Lemma fun_eq_sym : forall R f0 f1,f0 =(λ R)= f1 -> f1 =(λ R)= f0.
Proof.
intros. unfold fun_eq. auto with eqDB.
Qed.

Lemma fun_eq_trans : forall R f0 f1 f2,f0 =(λ R)= f1 -> f1 =(λ R)= f2 -> f0 =(λ R)= f2.
Proof.
intros. unfold fun_eq. eauto with eqDB.
Qed.

Add Parametric Relation R : (EventType -> Contract) (@fun_eq R)
  reflexivity proved by (@fun_eq_refl R)
  symmetry proved by (@fun_eq_sym R)
  transitivity proved by (@fun_eq_trans R)
  as fun_Contract_setoid.



Lemma seq_derive_o : forall R e c0 c1, e \ (c0 _;_ c1) = (R) = e \ c0 _;_ c1 _+_ o (c0) _;_ e \ c1.
Proof.
intros;simpl.  destruct (nu c0) eqn:Heqn.
- destruct (o_destruct c0). rewrite H. auto_rwd_eqDB.
  unfold o in H. rewrite Heqn in H. discriminate.
- destruct (o_destruct c0). unfold o in H. rewrite Heqn in H. discriminate.
  rewrite H. auto_rwd_eqDB.
Qed.

Lemma seq_derive_o_fun : forall R c0 c1, (fun e0 => e0 \ (c0 _;_ c1)) =(λ R)= (fun e0 => e0 \ c0 _;_ c1 _+_ o (c0) _;_ e0 \ c1).
Proof.
intros. unfold fun_eq.  pose proof seq_derive_o. simpl in *. auto.
Qed.


Hint Rewrite seq_derive_o_fun : funDB.

Definition seq_fun (f0 f1 : EventType -> Contract) := fun a => f0 a _;_ f1 a.
Notation "f0 _f;f_ f1" := (seq_fun f0 f1)(at level 59).

Lemma to_seq_fun : forall R f0 f1, (fun a => f0 a _;_ f1 a) =(λ R)= f0 _f;f_ f1.
Proof.
intros. unfold seq_fun. reflexivity.
Qed.

Opaque seq_fun.

Add Parametric Morphism R : (seq_fun) with
signature (@fun_eq R) ==> (@fun_eq R) ==> (@fun_eq R) as fun_eq_seq_morphism.
Proof.
intros. repeat rewrite <- to_seq_fun. unfold fun_eq in *. intros. auto with eqDB.
Qed.


Definition plus_fun (f0 f1 : EventType -> Contract) := fun a => f0 a _+_ f1 a.

Notation "f0 _f+f_ f1" := (plus_fun f0 f1)(at level 61).
Lemma to_plus_fun : forall R f0 f1, (fun a => f0 a _+_ f1 a) =(λ R)= f0 _f+f_ f1.
Proof.
intros. unfold plus_fun. reflexivity.
Qed.

Opaque plus_fun.

Add Parametric Morphism R : (plus_fun) with
signature (@fun_eq R) ==> (@fun_eq R) ==> (@fun_eq R) as fun_eq_plus_morphism.
Proof.
intros. repeat rewrite <- to_plus_fun. unfold fun_eq in *. intros. auto with eqDB.
Qed.


Definition par_fun (f0 f1 : EventType -> Contract) := fun a => f0 a _*_ f1 a.
Notation "f0 _f*f_ f1" := (par_fun f0 f1)(at level 60).
Lemma to_par_fun : forall R f0 f1, (fun a => f0 a _*_ f1 a) =(λ R)= f0 _f*f_ f1.
Proof.
intros. unfold par_fun. reflexivity.
Qed.

Opaque plus_fun.

Add Parametric Morphism R : (par_fun) with
signature (@fun_eq R) ==> (@fun_eq R) ==> (@fun_eq R) as fun_eq_par_morphism.
Proof.
intros. repeat rewrite <- to_par_fun. unfold fun_eq in *. intros. auto with eqDB.
Qed.

Hint Rewrite to_seq_fun to_plus_fun to_par_fun : funDB.



Lemma Σ_split_plus : forall R (A: Type) l (P P' : A -> Contract),
Σ l (fun a : A => P a _+_ P' a) = (R) = Σ l (fun a : A => P a) _+_  Σ l (fun a : A => P' a).
Proof.
intros.
induction l;intros.
- simpl. auto_rwd_eqDB.
- simpl. rewrite IHl. eq_m_left. rewrite c_plus_comm. eq_m_left.
Qed.


Lemma Σ_factor_seq_r : forall R l (P: EventType -> Contract) c,
Σ l (fun a  => P a _;_ c) = (R) = Σ l (fun a  => P a) _;_ c.
Proof.
induction l;intros.
- simpl. auto_rwd_eqDB.
- simpl. auto_rwd_eqDB.
Qed.

Lemma Σ_factor_seq_l : forall R l (P: EventType -> Contract) c,
Σ l (fun a  => c _;_ P a) = (R) = c _;_ Σ l (fun a  => P a).
Proof.
induction l;intros.
- simpl. auto_rwd_eqDB.
- simpl. auto_rwd_eqDB.
Qed.


Lemma Σ_factor_par_l : forall R l1 c (P' : EventType -> Contract),
Σ l1 (fun a' : EventType => c _*_ P' a') = (R) =
c _*_ Σ l1 (fun a0 : EventType => P' a0).
Proof.
induction l1;intros.
- simpl. auto_rwd_eqDB.
- simpl. rewrite IHl1. auto_rwd_eqDB.
Qed.

Lemma Σ_factor_par_r : forall R l1 c (P' : EventType -> Contract),
Σ l1 (fun a0 : EventType => P' a0) _*_ c = (R) =
Σ l1 (fun a' : EventType => P' a' _*_ c).
Proof.
induction l1;intros.
- simpl. auto_rwd_eqDB.
- simpl. rewrite <- IHl1. auto_rwd_eqDB.
Qed.

Lemma Σ_par_ΣΣ : forall R l0 l1 (P0 P1 : EventType -> Contract),
Σ l0 (fun a0  => P0 a0) _*_ Σ l1 (fun a1 => P1 a1) = (R) =
Σ l0 (fun a0  => Σ l1 (fun a1  => (P0 a0) _*_ (P1 a1))).
Proof. 
induction l0;intros.
- simpl. auto_rwd_eqDB.
- simpl. auto_rwd_eqDB.
  rewrite Σ_factor_par_l. rewrite IHl0.  reflexivity. 
Qed. 


Lemma ΣΣ_prod_swap : forall R l0 l1 (P : EventType -> EventType -> Contract), 
Σ l0 (fun a0 => Σ l1 (fun a1 => P a0 a1)) = (R) =
Σ l1 (fun a0 => Σ l0 (fun a1 => P a1 a0)).
Proof.
induction l0;intros.
- simpl. induction l1;intros;simpl;auto with eqDB. rewrite IHl1.
  auto with eqDB.
- simpl. rewrite Σ_split_plus. eq_m_left.
Qed.

Lemma fold_Failure : forall R l, Σ l (fun _ : EventType => Failure) = (R) = Failure.
Proof.
induction l;intros. simpl. reflexivity.
simpl. rewrite IHl. autorewrite with eqDB. reflexivity.
Qed.

Hint Resolve fold_Failure : eqDB.

(*Duplicate some of the rules to the function level*)

Lemma Σ_plus_decomp_fun : forall R l f0 f1, Σ l (f0 _f+f_ f1) = (R) = Σ l f0 _+_  Σ l f1.
Proof.
intros. rewrite <- to_plus_fun. apply Σ_split_plus.
Qed.

Lemma Σ_factor_seq_l_fun : forall R l f c, Σ l ((fun _ => c ) _f;f_ f) = (R) = c _;_ Σ l f.
Proof.
intros. rewrite <- to_seq_fun. apply Σ_factor_seq_l.
Qed.

Lemma Σ_factor_seq_r_fun : forall R l f0 c, Σ l (f0 _f;f_ (fun _ => c )) = (R) = Σ l f0 _;_ c.
Proof.
intros. rewrite <- to_seq_fun. apply Σ_factor_seq_r.
Qed.


(*Rules for rewriting functions*)
Lemma Σ_distr_l_fun : forall R f0 f1 f2, f0  _f;f_ (f1 _f+f_ f2) =(λ R)= f0 _f;f_ f1 _f+f_ f0 _f;f_ f2.
Proof.
intros. rewrite <- to_plus_fun. rewrite <- to_seq_fun.
symmetry. repeat rewrite <- to_seq_fun. rewrite <- to_plus_fun.
unfold fun_eq. intros. auto_rwd_eqDB.
Qed.


Lemma Σ_distr_par_l_fun : forall R f0 f1 f2, f0  _f*f_ (f1 _f+f_ f2) =(λ R)= f0 _f*f_ f1 _f+f_ f0 _f*f_ f2.
Proof.
intros. rewrite <- to_plus_fun. repeat rewrite <- to_par_fun.
rewrite <- to_plus_fun. unfold fun_eq.  auto with eqDB.
Qed.

Lemma Σ_distr_par_r_fun : forall R f0 f1 f2, (f0 _f+f_ f1)  _f*f_ f2 =(λ R)= f0 _f*f_ f2 _f+f_ f1 _f*f_ f2.
Proof.
intros. rewrite <- to_plus_fun. repeat rewrite <- to_par_fun.
rewrite <- to_plus_fun. unfold fun_eq. intros.  rewrite c_par_distr_r. reflexivity.
Qed.




Lemma Σ_seq_assoc_left_fun : forall R f0 f1 f2 , f0 _f;f_ (f1 _f;f_ f2) =(λ R)= (f0 _f;f_ f1) _f;f_ f2.
Proof.
intros. symmetry. rewrite <- (to_seq_fun _ f0). rewrite <- to_seq_fun.
rewrite <- (to_seq_fun _ f1). rewrite <- to_seq_fun. unfold fun_eq.
auto with eqDB.
Qed.

Lemma Σ_seq_assoc_right_fun : forall R f0 f1 f2 ,  (f0 _f;f_ f1) _f;f_ f2 =(λ R)= f0 _f;f_ (f1 _f;f_ f2).
Proof.
intros. symmetry. apply Σ_seq_assoc_left_fun.
Qed.

Lemma o_seq_comm_fun : forall R c f, (f _f;f_ (fun _ : EventType => o c)) =(λ R)= (fun _ : EventType => o c) _f;f_ f.
Proof.
intros. repeat rewrite <- to_seq_fun. unfold fun_eq.
intros. destruct (o_destruct c); rewrite H; auto_rwd_eqDB.
Qed.



Hint Rewrite Σ_distr_l_fun Σ_plus_decomp_fun Σ_factor_seq_l_fun Σ_factor_seq_r_fun Σ_seq_assoc_left_fun
             Σ_distr_par_l_fun Σ_distr_par_r_fun : funDB.


Lemma derive_unfold_seq : forall R c1 c2, 
o c1 _+_ Σ alphabet (fun a : EventType => Event a _;_ a \ c1) = (R) = c1 ->
o c2 _+_ Σ alphabet (fun a : EventType => Event a _;_ a \ c2) = (R) = c2 -> 
o (c1 _;_ c2) _+_ 
Σ alphabet (fun a : EventType => Event a _;_ a \ (c1 _;_ c2)) = (R) =
c1 _;_ c2.
Proof.
intros. rewrite <- H at 2. rewrite <- H0 at 2. autorewrite with funDB eqDB.
repeat rewrite c_plus_assoc; apply c_plus_ctx;
                  auto_rwd_eqDB.
rewrite o_seq_comm_fun.
autorewrite with funDB. rewrite Σ_seq_assoc_right_fun.
rewrite Σ_factor_seq_l_fun.
rewrite <- H0 at 1. autorewrite with eqDB funDB.
rewrite c_plus_assoc.
rewrite (c_plus_comm _ (Σ _ _ _;_  Σ _ _)).
eq_m_right.
Qed.

Lemma rewrite_in_fun : forall R f0 f1, f0 =(λ R)= f1 -> (fun a => f0 a) =(λ R)= (fun a => f1 a).
Proof.
intros. unfold fun_eq in*. auto.
Qed.

Lemma rewrite_c_in_fun : forall R (c c' : Contract) , c = (R) = c' -> (fun _ : EventType => c) =(λ R)= (fun _ : EventType => c').
Proof.
intros. unfold fun_eq. intros. auto. 
Qed.

Lemma fun_neut_r : forall R f, f _f*f_ (fun _ => Success) =(λ R)= f.
Proof.
intros. rewrite <- to_par_fun. unfold fun_eq. intros.
auto_rwd_eqDB.
Qed.

Lemma fun_neut_l : forall R f, (fun _ => Success) _f*f_ f =(λ R)= f.
Proof.
intros. rewrite <- to_par_fun. unfold fun_eq. intros.
auto_rwd_eqDB.
Qed.

Lemma fun_Failure_r : forall R f, f _f*f_ (fun _ => Failure) =(λ R)= (fun _ => Failure).
Proof.
intros. rewrite <- to_par_fun. unfold fun_eq. intros.
auto_rwd_eqDB.
Qed.

Lemma fun_Failure_l : forall R f, (fun _ => Failure) _f*f_ f =(λ R)= (fun _ => Failure).
Proof.
intros. rewrite <- to_par_fun. unfold fun_eq. intros.
auto_rwd_eqDB.
Qed.

Hint Rewrite fun_neut_r fun_neut_l fun_Failure_r fun_Failure_l : funDB.

Lemma o_seq_comm_fun3: forall R c1 c2, 
Σ alphabet (Event _f;f_ ((fun a : EventType => a \ c1) _f*f_ (fun _ : EventType => o c2))) = (R) =
Σ alphabet (Event _f;f_ ((fun a : EventType => a \ c1))) _*_ o c2. 
Proof.
intros. destruct (o_destruct c2);
rewrite H; autorewrite with funDB eqDB; reflexivity.
Qed.

Lemma o_seq_comm_fun4: forall R c1 c2,
Σ alphabet (Event _f;f_ ((fun _ : EventType => o c1) _f*f_ (fun a : EventType => a \ c2))) = (R) =
o c1 _*_ Σ alphabet (Event _f;f_ (fun a : EventType => a \ c2)).
Proof.
intros. destruct (o_destruct c1);
rewrite H; autorewrite with funDB eqDB; reflexivity.
Qed.


Hint Rewrite to_seq_fun to_plus_fun to_par_fun : funDB.

(*
Definition Σ_fun (f : EventType -> EventType -> Contract) := fun a  => Σ alphabet (f a).

Lemma to_Σ_fun : forall f, (fun a : EventType => Σ alphabet (f a)) =(λ R)= Σ_fun f.
Proof.
intros. unfold Σ_fun. reflexivity.
Qed.*)


Definition app a (f : EventType -> Contract) := f a.

Lemma to_app : forall f a, f a = app a f.
Proof.
intros. unfold app. reflexivity.
Qed.

Opaque app.

Add Parametric Morphism R a : (app a) with
signature (@fun_eq R) ==>  (@c_eq R) as afun_eq_par_morphism.
Proof.
intros. repeat rewrite <- to_app. unfold fun_eq in *. intros. auto with eqDB.
Qed.


Lemma o_seq_comm_fun_fun : forall R c1 c2 a,
(fun a1 : EventType => (Event _f;f_ (fun a0 : EventType => a0 \ c1)) a _*_ (Event _f;f_ (fun a0 : EventType => a0 \ c2)) a1) =(λ R)=
(fun a1 : EventType => (Event a _;_ a \ c1) _*_ Event a1 _;_ a1 \ c2).
Proof.
intros. unfold fun_eq. intros. repeat rewrite to_app.
repeat rewrite <- to_seq_fun.
 apply c_par_ctx; now rewrite <- to_app.
Qed.

Lemma o_seq_comm_fun_fun2 : forall R c1 c2 a,
(fun a1 : EventType => (Event a _;_ a \ c1) _*_ Event a1 _;_ a1 \ c2) =(λ R)=
(fun a1 : EventType => (Event a _;_ (a \ c1 _*_ Event a1 _;_ a1 \ c2))) _f+f_ (fun a1 => Event a1 _;_ (Event a _;_ a \ c1 _*_ a1 \ c2)).
Proof.
intros. rewrite <- to_plus_fun. unfold fun_eq. intros.
auto_rwd_eqDB.
Qed.




Lemma derive_unfold_par : forall R c1 c2, 
o c1 _+_ Σ alphabet (fun a : EventType => Event a _;_ a \ c1) = (R) = c1 ->
o c2 _+_ Σ alphabet (fun a : EventType => Event a _;_ a \ c2) = (R) = c2 -> 
o (c1 _*_ c2) _+_ 
Σ alphabet (fun a : EventType => Event a _;_ a \ (c1 _*_ c2)) = (R) =
c1 _*_ c2.
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
eq_m_left.
rewrite c_plus_comm. 
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

Lemma derive_unfold : forall R c, o c _+_ Σ alphabet (fun a : EventType => Event a _;_ a \ c) = (R) = c.
Proof.
induction c;intros.
- unfold o; simpl. autorewrite with funDB eqDB. reflexivity. 
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
- unfold o. simpl. rewrite <- IHc. autorewrite with funDB eqDB.
  rewrite <- IHc at 1.
  destruct (o_destruct c);rewrite H in *.
  * repeat rewrite c_star_plus. apply c_unfold.
  * auto_rwd_eqDB.
Qed.



Lemma Σd_to_Σe : forall c es, Σ es (fun a : EventType => Event a _;_ a \ c) = Σe es (map (fun e => e \ c) es).
Proof. 
induction es;intros;simpl;auto.
unfold Σe in *. simpl. rewrite IHes. auto.
Qed.

Lemma map_fst_combine : forall (A: Type)(l0 l1 : list A), length l0 = length l1 -> map fst (combine l0 l1) = l0.
Proof.
induction l0;intros;simpl;auto.
destruct l1 eqn:Heqn. simpl in H. discriminate.
simpl. f_equal. rewrite IHl0;auto.
Qed.

Lemma map_snd_combine : forall (A: Type)(l0 l1 : list A), length l0 = length l1 -> map snd (combine l0 l1) = l1.
Proof.
induction l0;intros;simpl;auto.
- destruct l1. auto. simpl in H. discriminate.
- destruct l1.  simpl in H.  discriminate. 
  simpl. f_equal. auto. 
Qed.


Lemma Σe_to_pair : forall R es l0 l1, length l0 = length l1 -> 
Σe es (map fst (combine l0 l1)) = (R) = Σe es (map snd (combine l0 l1))  -> Σe es l0 = (R) = Σe es l1.
Proof.
intros. rewrite map_fst_combine in H0; auto.
rewrite  map_snd_combine in H0;auto.
Qed.




Lemma combine_map : forall (A B : Type) (l : list A) (f f' : A -> B),
       combine (map f l) (map f' l) = map (fun c => (f c, f' c)) l.
Proof. 
induction l;intros.
- simpl. auto.
- simpl. rewrite IHl. auto.
Qed.

Ltac sum_reshape := repeat rewrite Σd_to_Σe; apply Σe_to_pair;repeat rewrite map_length; auto.

Lemma if_nu : forall R (b0 b1 : bool), b0 = b1 -> (if b0 then Success else Failure) = (R) =
(if b1 then Success else Failure).
Proof.
intros. rewrite H. reflexivity.
Qed.


Ltac unfold_tac := 
 match goal with
         | [ |-  ?c0 = (_) = ?c1  ] => rewrite <- (derive_unfold _ c0) at 1;
                                          rewrite <- (derive_unfold _ c1) at 1;
                                          unfold o; eq_m_left; try solve [apply if_nu; simpl; btauto]
         end.

Ltac simp_premise := 
 match goal with
         | [ H: In ?p (combine (map _ _) (map _ _)) |- _ ] => destruct p; rewrite combine_map in H;
                                                              rewrite in_map_iff in *;
                                                             destruct_ctx;simpl;inversion H;subst;clear H
         end.



Lemma bisim_completeness : forall c0 c1, Bisimilarity c0 c1 -> c0 =C= c1.
Proof.
pcofix CIH.
intros. punfold H0. inversion H0.
pfold.
unfold_tac.
- rewrite H2. reflexivity.
- sum_reshape.
  apply c_co_sum. intros.
  simp_premise.
  right. apply CIH.
  pclearbot.
  unfold Bisimilarity. auto.
Qed.


Theorem soundness : forall c0 c1, c0 =C= c1 -> (forall s, s(:)c0 <-> s(:)c1).
Proof.
intros c0 c1 H. rewrite matches_eq_iff_bisimilarity. auto using bisim_soundness.
Qed.

Theorem completeness : forall c0 c1, (forall s, s(:)c0 <-> s(:)c1) -> c0 =C= c1.
Proof.
intros. apply bisim_completeness. rewrite <- matches_eq_iff_bisimilarity. auto.
Qed.








Lemma test : forall c, Star c =C= Star (Star c).
Proof.
intros. 
pfold. 
unfold_tac. 
sum_reshape. 
apply c_co_sum. intros.
simp_premise.
left.

pfold. 
rewrite c_seq_assoc. apply c_seq_ctx. reflexivity. (*match first sequence*)
unfold_tac.
sum_reshape. 
apply c_co_sum. intros.
simp_premise.
left.

generalize x0. pcofix CIH2. intros. (*Coinduction principle*)
pfold. 
rewrite c_plus_idemp. 
rewrite c_seq_assoc. apply c_seq_ctx. reflexivity.
unfold_tac. 
sum_reshape. 
apply c_co_sum. intros.
simp_premise.
right. apply CIH2.
Qed. 
