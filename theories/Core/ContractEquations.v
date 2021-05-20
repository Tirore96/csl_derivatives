Require Import CSL.Core.Contract.  
Require Import Lists.List Bool.Bool Bool.Sumbool Setoid Coq.Arith.PeanoNat.

(** printing =~ %$=\sim$% *)

(** printing _+_ %$+$% *)

Import ListNotations.

Set Implicit Arguments.

Reserved Notation "c0 =R= c1" (at level 63).

Inductive c_eq : Contract -> Contract -> Prop :=
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
  | c_plus_ctx c0 c0' c1 c1' (H1 : c0 =R= c0') (H2 : c1 =R= c1') : c0 _+_ c1 =R= c0' _+_ c1'
  | c_seq_ctx c0 c0' c1 c1' (H1 : c0 =R= c0') (H2 : c1 =R= c1') : c0 _;_ c1 =R= c0' _;_ c1'
  where "c1 =R= c2" := (c_eq c1 c2).

Hint Constructors c_eq : eqDB.

Add Parametric Relation : Contract c_eq
  reflexivity proved by c_refl
  symmetry proved by c_sym
  transitivity proved by c_trans
  as Contract_setoid.

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


Ltac c_inversion :=
  (repeat match goal with
         | [ H: _ =~ Failure |- _ ] => inversion H
         | [ H: ?s =~ _ _+_ _ |- _ ] => inversion H; clear H
         | [ H: ?s =~ _ _;_ _ |- _ ] => inversion H; clear H
         | [ H: [?x] =~ Event _ |- _ ] => fail
         | [ H: ?s =~ Event _ |- _ ] => inversion H; subst
         | [ H: [] =~ Success |- _ ] => fail
         | [ H: _ =~ Success |- _ ] => inversion H; clear H
         end);auto with cDB.



Lemma c_eq_soundness : forall (c0 c1 : Contract), c0 =R= c1 -> (forall s : Trace, s =~ c0 <-> s =~ c1).
Proof.
intros c0 c1 H. induction H ;intros; try solve [split;intros;c_inversion].
  * split;intros;c_inversion; [ rewrite <- app_assoc | rewrite app_assoc ]; auto with cDB.
  * rewrite <- (app_nil_l s). split;intros;c_inversion.
  * rewrite <- (app_nil_r s) at 1. split;intros;c_inversion. subst.
    repeat rewrite app_nil_r in H1. now rewrite <- H1.
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
             Matches_seq_neut_r : eqDB.

Lemma c_plus_neut_l : forall c, Failure _+_ c =R= c.
Proof. intros. rewrite c_plus_comm. auto with eqDB.
Qed.

Hint Rewrite c_plus_neut_l 
             c_plus_neut 
             c_seq_neut_l
             c_seq_neut_r
             c_seq_failure_l 
             c_seq_failure_r 
             c_distr_l
             c_distr_r : eqDB.

Ltac auto_rwd_eqDB := autorewrite with eqDB;auto with eqDB.


Fixpoint L (c : Contract) : list Trace :=
match c with
| Success => [[]]
| Failure => []
| Event e => [[e]]
| c0 _+_ c1 => (L c0) ++ (L c1)
| c0 _;_ c1 => map (fun p => (fst p)++(snd p)) (list_prod (L c0) (L c1))
end.


Lemma Matches_member : forall (s : Trace)(c : Contract), s =~ c -> In s (L c). 
Proof.
intros. induction H ; simpl ; try solve [auto using in_or_app || auto using in_or_app ].
rewrite in_map_iff. exists (s1,s2). rewrite in_prod_iff. split;auto.
Qed.

Lemma member_Matches : forall (c : Contract)(s : Trace), In s (L c) -> s =~ c. 
Proof.
induction c;intros;simpl in*; try solve [ destruct H;try contradiction; subst; constructor].
- apply in_app_or in H. destruct H; auto with cDB.
- rewrite in_map_iff in H. destruct_ctx. destruct x.
  rewrite in_prod_iff in H0. destruct H0. simpl in H.
  subst. auto with cDB.
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

Lemma comp_equiv_destruct : forall (c0 c1: Contract),(forall s : Trace, s =~ c0 <-> s =~ c1) <->
(forall s : Trace, s =~ c0 -> s =~ c1) /\ (forall s : Trace, s =~ c1 -> s =~ c0).
Proof.
 split ; intros.
- split;intros; specialize H with s; destruct H; auto.
- destruct H. split;intros;auto.
Qed.


Theorem Matches_eq_i_incl_and : forall (c0 c1 : Contract), (forall (s : Trace), s =~ c0 <-> s =~ c1) -> 
incl (L c0) (L c1) /\ incl (L c1) (L c0) .
Proof.
intros. apply comp_equiv_destruct in H. destruct H. split; auto using Matches_incl. 
Qed.


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


Lemma Π_distr : forall l0 l1,  Σ (map Π l0) _;_ Σ (map Π l1) =R=
 Σ (map (fun x => Π (fst x ++ snd x)) (list_prod l0 l1)).
Proof.
induction l0;intros;simpl. auto_rwd_eqDB.
repeat rewrite map_app. rewrite Σ_app. rewrite <- IHl0.
auto_rwd_eqDB. 
apply c_plus_ctx; auto using Π_distr_aux with eqDB. 
Qed.



Theorem Π_L_ceq : forall (c : Contract), Σ (map Π (L c)) =R= c.
Proof.
induction c; simpl; try solve [auto_rwd_eqDB].
- rewrite map_app. rewrite Σ_app.
  auto using c_plus_ctx. 
- rewrite map_map.
  rewrite <- IHc1 at 2. rewrite <- IHc2 at 2.
  symmetry. apply Π_distr.
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




 
