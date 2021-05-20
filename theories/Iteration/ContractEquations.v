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
 _bisimilarity_gen c0 c1 (H0: forall e, bisim (e \ c0) (e \ c1) : Prop ) (H1: nu c0 = nu c1) : bisimilarity_gen bisim c0 c1.



Definition Bisimilarity c0 c1 := paco2 bisimilarity_gen bot2 c0 c1.
Hint Unfold  Bisimilarity : core.

Lemma bisimilarity_gen_mon: monotone2 bisimilarity_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.
Hint Resolve bisimilarity_gen_mon : paco.


Theorem matches_eq_i_bisimilarity : forall c0 c1, (forall s, s=~ c0 <-> s=~c1) -> Bisimilarity c0 c1.
Proof.
pcofix CIH. intros. pfold. constructor.
- intros. right. apply CIH.  setoid_rewrite <- derive_spec_comp. auto. 
- apply eq_true_iff_eq. setoid_rewrite Matches_Comp_iff_matchesb in H0.
  specialize H0 with []. simpl in*. auto.
Qed.

Theorem bisimilarity_i_matches_eq : forall c0 c1, Bisimilarity c0 c1 -> (forall s, s=~ c0 <-> s=~c1).
Proof.
intros. generalize dependent c1. generalize dependent c0.
induction s;intros.
- repeat rewrite Matches_Comp_iff_matchesb. simpl.
  rewrite <- eq_iff_eq_true.  punfold H. inversion H. auto.
- repeat rewrite derive_spec_comp. apply IHs. punfold H. inversion_clear H.
  specialize H0 with a. pclearbot. auto.
Qed.

Theorem matches_eq_iff_bisimilarity : forall c0 c1, (forall s, s=~ c0 <-> s=~c1) <-> Bisimilarity c0 c1.
Proof.
split;auto using matches_eq_i_bisimilarity, bisimilarity_i_matches_eq.
Qed.

Theorem Bisimilarity_symmetric : forall c0 c1, Bisimilarity c0 c1 -> Bisimilarity c1 c0.
Proof.
intros. rewrite <- matches_eq_iff_bisimilarity. rewrite <- matches_eq_iff_bisimilarity in H.
symmetry. auto.
Qed.




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


Ltac assoc_left := repeat rewrite <- c_plus_assoc.
Ltac assoc_right := repeat rewrite c_plus_assoc.

Ltac eq_m_left := assoc_left; apply c_plus_ctx;
                  auto_rwd_eqDB.

Ltac eq_m_right := assoc_right; apply c_plus_ctx;
             
     auto_rwd_eqDB.
Check filter.

Check EventType_beq.
Lemma Σe_filter : forall es cs e R, e \ (Σ (map (fun x => Event (fst x) _;_ snd x) (combine es cs))) = (R) =
                                   (e \ (Σ (map (fun x => Event (fst x) _;_ snd x) (filter (fun p => if EventType_eq_dec (fst p) e then true else false) (combine es cs))))).
Proof.
induction es;intros.
- simpl. reflexivity.
- destruct cs.
  * simpl. reflexivity.
  * simpl. eq_event_destruct.
    ** auto_rwd_eqDB. subst. simpl.
       eq_event_destruct. subst. auto_rwd_eqDB.
    ** auto_rwd_eqDB.
Qed.


Lemma Σe_filter2 : forall es cs e R, (e \ (Σ (map (fun x => Event (fst x) _;_ snd x) (filter (fun p => if EventType_eq_dec (fst p) e then true else false) (combine es cs)))))
                                   = (R) = Σ (map snd (filter (fun p => if EventType_eq_dec (fst p) e then true else false) (combine es cs))).
Proof.
induction es;intros.
- simpl. reflexivity.
- simpl. destruct cs.
  * simpl. reflexivity.
  * simpl. eq_event_destruct. 
    ** subst. simpl. eq_event_destruct.
       auto_rwd_eqDB.
    ** rewrite IHes. reflexivity.
Qed.


Lemma Σe_derive_rewrite : forall es cs e R, e \ (Σe es cs) =(R)= Σ (map snd (filter (fun p => if EventType_eq_dec (fst p) e then true else false) (combine es cs))).
Proof.
unfold Σe. intros. rewrite Σe_filter. rewrite Σe_filter2.
reflexivity.
Qed.


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


Lemma Σ_derivative : forall l e, e \ (Σ l) = Σ (map (fun c => e \ c) l).
Proof.
induction l;intros;simpl;auto.
rewrite IHl. auto.
Qed.

Lemma Σe_cons : forall e es c cs, Σe (e :: es) (c :: cs) = Event e _;_ c _+_ Σe es cs.
Proof.
intros. unfold Σe. simpl. reflexivity.
Qed.


Lemma in_alphabet_nth : forall e, exists n, nth_error alphabet n = Some e.
Proof.
intros. apply In_nth_error. auto with eqDB.
Qed.
Check nth.

Lemma nth_nil : forall (A:Type) (d : A) (n : nat), nth n [] d = d.
Proof.
intros. simpl. destruct n;auto.
Qed.

Lemma Sum_nth_Failure : forall l R, (forall n : nat, Failure = (R)= nth n l Failure) ->
                                  Σ l =(R)= Failure.
Proof.
induction l;intros;auto_rwd_eqDB.
simpl. rewrite IHl. specialize H with 0. simpl in H. rewrite <- H. 
auto_rwd_eqDB. intros. specialize H with (S n). simpl in H. auto.
Qed.


Lemma Σ_eq : forall l0 l1 R, (forall n, nth n l0 Failure =(R)= nth n l1 Failure) -> Σ l0 =(R)= Σ l1.
Proof.
induction l0;intros. Search (nth [] _).
- simpl in *. setoid_rewrite nth_nil in H. induction l1. simpl. reflexivity.
  simpl. rewrite IHl1.
  * apply Sum_nth_Failure in H as H'. simpl in H'. rewrite H'.
    symmetry. apply IHl1. intros. specialize H with (S n). simpl in H.
    auto.
  * intros. specialize H with (S n). simpl in H. auto.
- destruct l1.
  * simpl. setoid_rewrite nth_nil in H. symmetry in H.
  apply Sum_nth_Failure in H. simpl in H. auto.
  * simpl. specialize H with 0 as H'. simpl in H'. rewrite H'.
    auto. eq_m_left. apply IHl0. intros. specialize H with (S n).
    simpl in H. auto.
Qed. 

Lemma Σe_eq : forall es l0 l1 R, length l0 = length l1 -> (forall n, nth n l0 Failure =(R)= nth n l1 Failure) -> Σe es l0 =(R)= Σe es l1.
Proof.
induction es;intros;unfold Σe.
- simpl. reflexivity.
- simpl. destruct l0.
  * simpl. destruct l1.
    ** simpl. reflexivity.
    ** simpl in H. discriminate.
  * simpl. destruct l1.
    ** simpl in H. discriminate.
    ** simpl. unfold Σe in IHes. 
       specialize H0 with 0 as H0'. simpl in H0'. rewrite H0'.
       eq_m_left. apply IHes;auto. intros. specialize H0 with (S n).
       simpl in H0. auto.
Qed.

Lemma Σederive_eq : forall es l0 l1 R e, length l0 = length l1 -> (forall n, nth n l0 Failure =(R)= nth n l1 Failure) -> e \ (Σe es l0) =(R)= e \ (Σe es l1).
Proof.
induction es;intros;unfold Σe.
- simpl. reflexivity.
- simpl. destruct l0.
  * simpl. destruct l1.
    ** simpl. reflexivity.
    ** simpl in H. discriminate.
  * simpl. destruct l1.
    ** simpl in H. discriminate.
    ** eq_event_destruct.
      *** simpl. eq_event_destruct.  unfold Σe in IHes. 
       specialize H0 with 0 as H0'. simpl in H0'. rewrite H0'.
       eq_m_left. apply IHes;auto. intros. specialize H0 with (S n).
       simpl in H0. auto.
      *** simpl. eq_event_destruct.  unfold Σe in IHes. 
       specialize H0 with 0 as H0'. simpl in H0'. rewrite H0'.
       eq_m_left. apply IHes;auto. intros. specialize H0 with (S n1).
       simpl in H0. auto.
Qed.

Lemma Σederive_eq2 : forall es ps R e, (forall p : Contract * Contract, In p ps ->  (fst p) =(R)= (snd p)) -> e \ (Σe es (map fst ps)) =(R)= e \ (Σe es (map snd ps)).
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
- simpl. destruct (nu c0); destruct (nu c1);simpl; auto_rwd_eqDB.
    assoc_right. rewrite (c_plus_comm _ (e \ c2)).
    assoc_right. auto_rwd_eqDB. eq_m_right.
- simpl. auto_rwd_eqDB. eq_m_right. 
- simpl. rewrite c_plus_comm. eq_m_right.
- simpl. auto_rwd_eqDB. eq_m_left. assoc_right. apply c_plus_ctx. reflexivity.
    rewrite c_plus_comm. reflexivity.
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
- apply Σederive_eq2;auto. intros. apply H in H0.
  pclearbot. punfold H0.

Qed.



Lemma co_eq_soundness : forall (c0 c1 : Contract), c0 =C= c1 -> Bisimilarity c0 c1.
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







Lemma map_ext_in_R :
  forall (A : Type)(f g:A->Contract) l R, (forall a, In a l -> f a =(R)= g a) -> Σ (map f l) =(R)= Σ (map g l).
Proof.
induction l;intros;simpl;auto with eqDB.
apply c_plus_ctx. apply H. apply in_eq. apply IHl.
intros. apply H. simpl. now right.
Qed.

Lemma map_ext_in_R2 :
  forall (A : Type)(f g:A->Contract) l, (forall a, In a l -> f a =C= g a) -> Σ (map f l) =C= Σ (map g l).
Proof.
induction l;intros;simpl;auto with eqDB. reflexivity.
pfold.
apply c_plus_ctx. specialize H with a. pose proof in_eq. 
specialize H0 with (a:=a) (l:=l). apply H in H0. punfold H0.
simpl in H. assert (HA: forall a0 : A, In a0 l -> f a0 =C= g a0).
intros. auto. apply IHl in HA. punfold HA.
Qed.

Lemma Σ_alphabet_or : forall alphabet0 e R,
 Σ (map (fun a : CSLC.EventType => if EventType_eq_dec e a then Success else Failure) alphabet0) =(R)= Success /\ In e alphabet0 \/
 Σ (map (fun a : CSLC.EventType => if EventType_eq_dec e a then Success else Failure) alphabet0) =(R)= Failure /\ ~(In e alphabet0).
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
Lemma Σ_alphabet : forall e R, Σ (map (fun a => if EventType_eq_dec e a then Success else Failure) alphabet) =(R)= Success.
Proof.
intros. destruct (Σ_alphabet_or alphabet e R).
- destruct H. auto.
- destruct H. pose proof (in_alphabet e). contradiction.
Qed.

Lemma Σ_split_plus : forall (A: Type) l (P P' : A -> Contract) R,
Σ (map (fun a : A => P a _+_ P' a) l) =(R)= Σ (map (fun a : A => P a) l) _+_  Σ (map (fun a : A => P' a) l).
Proof.
induction l;intros.
- simpl. auto_rwd_eqDB.
- simpl. rewrite c_plus_assoc. rewrite c_plus_assoc. apply c_plus_ctx;auto with eqDB.
  rewrite (c_plus_comm _ (Σ _)).
  rewrite c_plus_assoc. apply c_plus_ctx;auto with eqDB. rewrite IHl.
  auto_rwd_eqDB.
Qed.

Lemma Σ_factor_seq_r : forall l (P: EventType -> Contract) c R,
Σ (map (fun a  => P a _;_ c) l) =(R)= Σ (map (fun a  => P a) l) _;_ c.
Proof.
induction l;intros.
- simpl. auto_rwd_eqDB.
- simpl. auto_rwd_eqDB.
Qed.

Lemma Σ_factor_seq_r_C : forall l (P: EventType -> Contract) c,
Σ (map (fun a  => P a _;_ c) l) =C= Σ (map (fun a  => P a) l) _;_ c.
Proof.
intros. pfold. apply Σ_factor_seq_r.
Qed.

Lemma Σ_factor_seq_l : forall l (P: EventType -> Contract) c R,
Σ (map (fun a  => c _;_ P a) l) =(R)= c _;_ Σ (map (fun a  => P a) l).
Proof.
induction l;intros.
- simpl. auto_rwd_eqDB.
- simpl. auto_rwd_eqDB.
Qed.

Lemma Σ_factor_seq_l_R : forall l (P: EventType -> Contract) c,
Σ (map (fun a  => c _;_ P a) l) =C= c _;_ Σ (map (fun a  => P a) l).
Proof.
intros. pfold. apply Σ_factor_seq_l.
Qed.



Lemma Σ_factor_par_l : forall l1 c (P' : EventType -> Contract) R,
Σ (map (fun a' : EventType => c _*_ P' a') l1) =(R)=
c _*_ Σ (map (fun a0 : EventType => P' a0) l1).
Proof.
induction l1;intros.
- simpl. auto_rwd_eqDB.
- simpl. rewrite IHl1. auto_rwd_eqDB.
Qed.

Lemma Σ_factor_par_r : forall l1 c (P' : EventType -> Contract) R,
Σ (map (fun a0 : EventType => P' a0) l1) _*_ c =(R)=
Σ (map (fun a' : EventType => P' a' _*_ c) l1).
Proof.
induction l1;intros.
- simpl. auto_rwd_eqDB.
- simpl. rewrite <- IHl1. auto_rwd_eqDB.
Qed.

Lemma Σ_par_ΣΣ : forall l0 l1 (P0 P1 : EventType -> Contract) R,
Σ (map (fun a0  => P0 a0) l0) _*_ Σ (map (fun a1 => P1 a1) l1) =(R)=
Σ (map (fun a0  => Σ (map (fun a1  => (P0 a0) _*_ (P1 a1)) l1)) l0).
Proof. 
induction l0;intros.
- simpl. auto_rwd_eqDB.
- simpl. auto_rwd_eqDB.
  rewrite Σ_factor_par_l. rewrite IHl0.  reflexivity. 
Qed. 


Lemma ΣΣ_prod_swap : forall l0 l1 (P : EventType -> EventType -> Contract) R, 
Σ (map (fun a0 => Σ (map (fun a1 => P a0 a1) l1)) l0)=(R)=
Σ (map (fun a0 => Σ (map (fun a1 => P a1 a0) l0)) l1).
Proof.
induction l0;intros.
- simpl. induction l1;intros;simpl;auto with eqDB. rewrite IHl1.
  auto with eqDB.
- simpl. rewrite Σ_split_plus. eq_m_left.
Qed.

Lemma fold_Failure : forall l R, Σ (map (fun _ : EventType => Failure) l) =(R)= Failure.
Proof.
induction l;intros. simpl. reflexivity.
simpl. rewrite IHl. autorewrite with eqDB. reflexivity.
Qed.

Hint Resolve fold_Failure : eqDB.



Ltac rwd_in_map f := rewrite map_ext_in_R ; try instantiate (1:=f);intros; auto_rwd_eqDB.

Lemma derive_unfold_seq : forall c1 c2 R, 
o c1 _+_ Σ (map (fun a : EventType => Event a _;_ a \ c1) alphabet) =(R)= c1 ->
o c2 _+_ Σ (map (fun a : EventType => Event a _;_ a \ c2) alphabet) =(R)= c2 -> 
o (c1 _;_ c2) _+_ 
Σ (map (fun a : EventType => Event a _;_ a \ (c1 _;_ c2)) alphabet) =(R)=
c1 _;_ c2.
Proof.
intros;simpl;auto_rwd_eqDB.
- destruct (nu c1) eqn:Heqn.
  * rwd_in_map (fun a => Event a _;_ a \ c1 _;_ c2  _+_  Event a _;_ a \ c2);
    intros; auto_rwd_eqDB.  rewrite Σ_split_plus.
    rewrite Σ_factor_seq_r. rewrite <- H at 2.
    rewrite <- H0 at 2. rewrite <- H0 at 3. auto_rwd_eqDB. eq_m_right.
    apply o_true in Heqn. rewrite Heqn.
    auto_rwd_eqDB. rewrite (c_plus_comm _ _ (Σ _ _;_ Σ _ )).
    assoc_left. rewrite c_plus_comm. assoc_right.
    apply c_plus_ctx. reflexivity.
    auto_rwd_eqDB.
  * apply o_false in Heqn. rewrite Heqn in*. autorewrite with eqDB in *.
    rwd_in_map (fun a => Event a _;_ a \ c1 _;_ c2);
    intros; auto_rwd_eqDB. rewrite Σ_factor_seq_r. 
    rewrite H. reflexivity.
Qed.



Lemma derive_unfold_par : forall c1 c2 R, 
o c1 _+_ Σ (map (fun a : EventType => Event a _;_ a \ c1) alphabet) =(R)= c1 ->
o c2 _+_ Σ (map (fun a : EventType => Event a _;_ a \ c2) alphabet) =(R)= c2 -> 
o (c1 _*_ c2) _+_ 
Σ (map (fun a : EventType => Event a _;_ a \ (c1 _*_ c2)) alphabet) =(R)=
c1 _*_ c2.
Proof.
intros;simpl;auto_rwd_eqDB.
rewrite (map_ext_in_R _ (fun a : EventType =>  ((Event a _;_ (a \ c1 _*_ o c2) _+_ Event a _;_ ( a \ c1 _*_Σ (map (fun a : EventType => Event a _;_ a \ c2) alphabet))) 
_+_ (Event a _;_ (o c1 _*_ a \ c2) _+_ Event a _;_ (Σ (map (fun a : EventType => Event a _;_ a \ c1) alphabet) _*_ a \ c2 )))));

try solve [intros; rewrite <- c_distr_l; rewrite <- c_par_distr_l;  rewrite H0;
           rewrite <- c_distr_l; rewrite <- c_distr_l;
           rewrite <- c_par_distr_r; rewrite H; reflexivity].
rewrite <- H at 2. rewrite <- H0 at 2.
  auto_rwd_eqDB. repeat rewrite (c_par_comm _ (_ _+_ _)). auto_rwd_eqDB.
  assoc_right. apply c_plus_ctx. reflexivity. 
repeat rewrite Σ_split_plus.
repeat rewrite <- c_plus_assoc. 
remember (Σ (map (fun a : EventType => Event a _;_ (a \ c1 _*_ Σ (map (fun a0 : EventType => Event a0 _;_ a0 \ c2) alphabet))) alphabet)) as a.
remember (Σ (map (fun a0 : EventType => Event a0 _;_ (Σ (map (fun a1 : EventType => Event a1 _;_ a1 \ c1) alphabet) _*_ a0 \ c2)) alphabet)) as b.
repeat rewrite c_plus_assoc. rewrite (c_plus_comm _ a).
repeat rewrite <- c_plus_assoc.
rewrite (c_plus_assoc _ _ b).
apply c_plus_ctx.
  * apply c_plus_ctx.
    ** destruct (o_destruct c2);rewrite H1.
      *** auto_rwd_eqDB. apply map_ext_in_R.
          intros. auto_rwd_eqDB.
      *** auto_rwd_eqDB. 
          rewrite (map_ext_in_R _ (fun _ : EventType => Failure)).
          apply fold_Failure. intros. auto_rwd_eqDB.
    ** rewrite c_par_comm. rewrite Σ_factor_par_r. destruct (o_destruct c1);rewrite H1.
      *** auto_rwd_eqDB. Check map_ext_in_R. apply map_ext_in_R.
          intros; auto_rwd_eqDB.
      *** auto_rwd_eqDB. 
          rewrite (map_ext_in_R _ (fun _ : EventType => Failure)).
          rewrite fold_Failure. rewrite <- Σ_factor_par_r.
          auto_rwd_eqDB. intros. auto_rwd_eqDB.
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


Lemma seq_failure_r_C : forall c,  c _;_ Failure =C= Failure.
Proof.
intros. pfold. auto_rwd_eqDB.
Qed. 

Lemma c_star_plus_C : forall c, Star (Success _+_ c) =C= Star c.
Proof.
intros. pfold.   auto_rwd_eqDB.
Qed.

Lemma c_unfold_C : forall (c : Contract),
       Success _+_ c _;_ Star c =C= Star c.
Proof.
intros. pfold.   auto_rwd_eqDB.
Qed.
Check c_unfold.


Lemma Σd_to_Σe : forall c es, Σ (map (fun a : EventType => Event a _;_ a \ c) es) = Σe es (map (fun e => e \ c) es).
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


Lemma Σe_to_pair : forall es l0 l1 R, length l0 = length l1 -> 
Σe es (map fst (combine l0 l1)) =(R)= Σe es (map snd (combine l0 l1))  -> Σe es l0 =(R)= Σe es l1.
Proof.
intros. rewrite map_fst_combine in H0; auto.
rewrite  map_snd_combine in H0;auto.
Qed.


Lemma derive_unfold3 : forall c R, o c _+_ Σ (map (fun a : EventType => Event a _;_ a \ c) alphabet) =(R)= c.
Proof. 
induction c;intros.
- unfold o;simpl;auto_rwd_eqDB. rewrite Σ_factor_seq_r. auto_rwd_eqDB.
- simpl;auto_rwd_eqDB. rwd_in_map (fun (_ : EventType) => Failure).
- rwd_in_map (fun a => Event e _;_ (if EventType_eq_dec e a then Success else Failure)).
  * rewrite Σ_factor_seq_l. rewrite Σ_alphabet. auto_rwd_eqDB.
  * simpl. eq_event_destruct;subst; auto_rwd_eqDB.
- simpl;auto_rwd_eqDB. rwd_in_map (fun a => Event a _;_ a \ c1  _+_  Event a _;_ a \ c2);
  intros; auto_rwd_eqDB. rewrite Σ_split_plus. 
  rewrite <- c_plus_assoc. rewrite (c_plus_comm _ (o _)).
rewrite (c_plus_assoc _ (o _)).
  rewrite IHc1. rewrite (c_plus_comm _ (o c2)).
  rewrite c_plus_assoc. rewrite IHc2. auto_rwd_eqDB.
- auto using derive_unfold_seq.
- auto using derive_unfold_par.
- unfold o. simpl. rewrite (map_ext_in_R _ (fun a : EventType => (Event a _;_ a \ c) _;_ Star c)).
  2: { intros. auto_rwd_eqDB. }
rewrite Σ_factor_seq_r.

 (destruct (o_destruct c)).
  2:{  rewrite H in *. specialize IHc with R.
  autorewrite with eqDB in IHc. rewrite IHc.
  auto_rwd_eqDB. }
  rewrite H in *. rewrite <- IHc. rewrite c_star_plus.
  rewrite <- (c_unfold _ (Σ _)) at 2. 
  apply c_plus_ctx. reflexivity. reflexivity.
Qed.

Lemma combine_map : forall (A B : Type) (l : list A) (f f' : A -> B),
       combine (map f l) (map f' l) = map (fun c => (f c, f' c)) l.
Proof. 
induction l;intros.
- simpl. auto.
- simpl. rewrite IHl. auto.
Qed.

Lemma co_eq_completeness : forall c0 c1, Bisimilarity c0 c1 -> c0 =C= c1.
Proof.
pcofix CIH.
intros. punfold H0. inversion H0.
pfold.
rewrite <- derive_unfold3. rewrite <- (derive_unfold3 c1).
unfold o. apply c_plus_ctx. rewrite H2. reflexivity.
rewrite Σd_to_Σe. rewrite Σd_to_Σe. apply Σe_to_pair.
- repeat rewrite map_length. auto.
- apply c_co_sum. intros.
destruct p. subst. apply in_combine_l  in H4 as H4'.
apply in_combine_r in H4 as H4''. rewrite in_map_iff in *.
destruct_ctx. subst. right. simpl. apply CIH.
pclearbot. rewrite combine_map in H4.
rewrite in_map_iff in H4. destruct_ctx. inversion H.
subst. 
unfold Bisimilarity. auto.
Qed.






Theorem soundness : forall c0 c1, c0 =C= c1 -> (forall s, s=~c0 <-> s=~c1).
Proof.
intros c0 c1 H. rewrite matches_eq_iff_bisimilarity. auto using co_eq_soundness.
Qed.

Theorem completeness : forall c0 c1, (forall s, s=~c0 <-> s=~c1) -> c0 =C= c1.
Proof.
intros. apply co_eq_completeness. rewrite <- matches_eq_iff_bisimilarity. auto.
Qed.