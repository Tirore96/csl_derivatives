Require Import Lists.List.
Require Import FunInd.
Require Import Bool.Bool.
Require Import Bool.Sumbool.
Require Import Structures.GenericMinMax.
From Equations Require Import Equations.
Import ListNotations.
Require Import micromega.Lia.
Require Import Setoid.
Require Import Init.Tauto btauto.Btauto.
Require Import Logic.ClassicalFacts.

Set Implicit Arguments.



Inductive EventType : Type :=
| Transfer : EventType
| Notify : EventType.


Definition eqb_event (e1 e2:EventType):bool :=
match e1, e2 with
| Transfer, Transfer => true
| Notify, Notify => true
| _, _ => false
end.

Lemma eqb_event_refl : forall (e : EventType), eqb_event e e = true.
Proof.
destruct e ; reflexivity.
Qed.

Lemma eqb_event_not_eq : forall (e0 e1 : EventType), e0 <> e1 -> eqb_event e0 e1 = false.
Proof.
destruct e0, e1;intros;try solve [contradiction | reflexivity]. 
Qed.

Definition eq_event_dec (e1 e2 : EventType) : {e1 = e2}+{~(e1=e2)}.
Proof. destruct (eqb_event e1 e2) eqn:Heqn.
- left. destruct e1 ; destruct e2; try reflexivity ; try discriminate Heqn.
- right. destruct e1 ; destruct e2 ;  intro H ; try  discriminate Heqn ; try discriminate H.
Defined.

Definition Trace := List.list EventType % type.

Inductive Contract : Set :=
| Success : Contract
| Failure : Contract
| Event : EventType -> Contract
| CPlus : Contract -> Contract -> Contract
| CSeq : Contract -> Contract -> Contract
| Star : Contract -> Contract.



Notation "e _._ c" := (CSeq (Event e) c)
                    (at level 41, right associativity).

Notation "c0 _;_ c1"  := (CSeq c0 c1)
                         (at level 50, left associativity).

Notation "c0 _+_ c1"  := (CPlus c0 c1)
                         (at level 61, left associativity).



Fixpoint eqb_contract (c0 c1 : Contract) : bool :=
match c0,c1 with
| Success, Success => true
| Failure, Failure => true
| (Event e), (Event e') => eqb_event e e'
| (CPlus c0 c1), (CPlus c2 c3) => (eqb_contract c0 c2) && (eqb_contract c1 c3)
| (CSeq c0 c1), (CSeq c2 c3) => (eqb_contract c0 c2) && (eqb_contract c1 c3)
| (Star c0),(Star c1) => eqb_contract c0 c1
| _, _ => false
end.

Lemma eqb_contract_true : forall (c0 c1 : Contract), eqb_contract c0 c1 = true -> c0 = c1.
Proof.
induction c0. 
- destruct c1 ; intros ; try reflexivity ; try (simpl in H ; try discriminate).
- intros ;  destruct c1; try reflexivity; (try simpl in H ; discriminate).
- intros. destruct c1; try reflexivity; (try simpl in H ; try discriminate).
  apply f_equal. destruct e; destruct e0 ; try reflexivity ; try (simpl in H ; discriminate).
- induction c1 ; intros ; try discriminate.
  * simpl in H. apply andb_prop in H as [H1 H2].
    apply IHc0_1 in H1. rewrite H1. apply IHc0_2 in H2.  rewrite H2.  reflexivity. 
- induction c1 ; intros ; try discriminate. simpl in H.
  * simpl in H. apply andb_prop in H as [H1 H2].
    apply IHc0_1 in H1. rewrite H1. apply IHc0_2 in H2.  rewrite H2.  reflexivity.
- induction c1 ; intros ; try discriminate. simpl in H. f_equal. auto. 
Defined.

Lemma eqb_contract_false : forall (c0 c1 : Contract), eqb_contract c0 c1 = false -> c0 <> c1.
Proof.
induction c0.
- destruct c1 ; intros ; try discriminate.
- destruct c1 ; intros ; try discriminate.
- destruct c1 ; intros ; try discriminate.
  * destruct e; destruct e0 ; try reflexivity ; try (simpl in H ; discriminate).
- induction c1 ; intros ; try discriminate.
  * simpl in H. apply andb_false_elim in H as [H1 | H1].
    ** apply IHc0_1 in H1. intro H. inversion H. contradiction.
    ** apply IHc0_2 in H1. intro H. inversion H. contradiction. 
- induction c1 ; intros ; try discriminate.
  * simpl in H. apply andb_false_elim in H as [H1 | H1].
    ** apply IHc0_1 in H1. intro H. inversion H. contradiction.
    ** apply IHc0_2 in H1. intro H. inversion H. contradiction.
- induction c1 ; intros ; intro H3; try discriminate. inversion H3. simpl in H.
  apply IHc0 in H. contradiction. 
Defined.

Definition eq_contract_dec : forall (c0 c1: Contract), {c0=c1} + {c0<>c1}.
Proof.
intros. destruct (eqb_contract c0 c1) eqn:Heqn.
- left. apply eqb_contract_true. assumption.
- right. apply eqb_contract_false. assumption.
Defined.

Lemma eq_eqb_contract_helper : forall (c : Contract), eqb_contract c c = true.
Proof.
induction c; try reflexivity.
- apply eqb_event_refl.
- simpl. rewrite IHc1. rewrite IHc2. reflexivity.
- simpl. rewrite IHc1. rewrite IHc2. reflexivity.
- simpl. assumption.
Qed.

Lemma eq_eqb_contract : forall (c0 c1 : Contract), c0 = c1 -> eqb_contract c0 c1 = true.
Proof.
intros. rewrite H. apply eq_eqb_contract_helper. 
Qed.

Lemma eqb_contract_iff : forall (c0 c1: Contract), c0 = c1 <-> eqb_contract c0 c1 = true.
Proof.
split. apply eq_eqb_contract. apply eqb_contract_true. Qed.

Lemma neq_eqb_contract : forall (c0 c1 : Contract), c0 <> c1 -> eqb_contract c0 c1 = false.
Proof.
intros. destruct (eqb_contract c0 c1) eqn:Heqn. 
- rewrite <- eqb_contract_iff in Heqn. contradiction.
- reflexivity.
Qed.

Lemma contract_reflect : forall (c0 c1 : Contract), reflect (c0 = c1) (eqb_contract c0 c1).
Proof.
intros. destruct (eq_contract_dec c0 c1).
- rewrite eq_eqb_contract. constructor; assumption. auto.
- rewrite neq_eqb_contract. constructor; assumption. auto.
Qed.




 

(*For a nullary contract c, nu c = true*)
Fixpoint nu(c:Contract):bool :=
match c with
| Success => true
| Failure => false
| Event e => false
| c0 _;_ c1 => nu c0 && nu c1
| c0 _+_ c1 => nu c0 || nu c1
| Star c => true
end.



Inductive Nu : Contract -> Prop :=
| NSuccess : Nu Success
| NPlusLeft c0 c1 (H0: Nu c0) : Nu (c0 _+_ c1)
| NPlusRight c0 c1 (H0: Nu c1) : Nu (c0 _+_ c1)
| NSeq c0 c1 (H0: Nu c0) (H1: Nu c1) : Nu (c0 _;_ c1)
| NStar c : Nu (Star c).

Hint Constructors Nu : core.

Lemma nu_true : forall (c0 : Contract), nu c0 = true -> Nu c0.
Proof.
induction c0;intros;try solve [ constructor | discriminate].
- simpl in H. apply orb_prop in H as [H | H];  auto.
- simpl in H. apply andb_prop in H as [H1 H2];auto.
Qed.


Inductive NotNu : Contract -> Prop :=
| NNFailure : NotNu Failure
| NNEvent e : NotNu (Event e)
| NNPLus c0 c1 (H0: NotNu c0) (H1: NotNu c1) : NotNu (c0 _+_ c1)
| NNSeqFirst c0 c1 (H0: NotNu c0) : NotNu (c0 _;_ c1)
| NNSeqSecond c0 c1 (H0: NotNu c1) : NotNu (c0 _;_ c1).
Hint Constructors NotNu : core.


Lemma nu_false : forall (c0 : Contract), nu c0 = false -> NotNu c0.
Proof.
induction c0;intros;try solve [ constructor | discriminate].
- simpl in H. apply orb_false_iff in H as [H1 H2]. constructor; auto.
- simpl in H. apply andb_false_iff in H as [H | H]. constructor;auto. apply NNSeqSecond. auto.
Qed.


Definition Nu_dec (c : Contract) : {Nu c}+{NotNu c}.
Proof. destruct (nu c) eqn:Heqn.
- left. auto using nu_true.
- right. auto using nu_false.
Defined.


Lemma NotNu_negation : forall (c : Contract), NotNu c -> ~(Nu c).
Proof.
intros. induction H;intro H2; try solve [inversion H2 | inversion H2; contradiction]. 
Qed.




(*Derivative of contract with respect to an event*)
Equations derive(e:EventType)(c:Contract):Contract :=
derive e Success := Failure;
derive e Failure := Failure;
derive e (Event e1) := if eq_event_dec e1 e then Success else Failure;
derive e (c0 _;_ c1) := if (Nu_dec c0) then ((derive e c0) _;_ c1) _+_ (derive e c1)
                          else (derive e c0) _;_ c1;
derive e (c0 _+_ c1) := (derive e c0) _+_ (derive e c1);
derive e (Star c) := derive e c _;_ (Star c).
Global Transparent derive.

Notation "c / e" := (derive e c).


Inductive Derive : Contract -> EventType -> Contract -> Prop :=
 | DSuccess e : Derive Success e Failure
 | DFailure e : Derive Failure e Failure
 | DEventS e : Derive (Event e) e Success
 | DEventF e0 e (H0: e0 <> e) : Derive (Event e0) e Failure
 | DPlus e c0 c0' c1 c1' (H0: Derive c0 e c0') (H1: Derive c1 e c1') : Derive (c0 _+_ c1) e (c0' _+_ c1')
 | DSeqNu e c0 c0' c1 c1' (H0: Nu c0) (H1: Derive c0 e c0') (H2: Derive c1 e c1'): Derive (c0 _;_ c1) e ((c0' _;_c1) _+_ c1')
 | DSeq e c0 c0' c1 (H0: NotNu c0) (H1 : Derive c0 e c0') : Derive (c0 _;_ c1) e (c0' _;_ c1)
 | DStar e c c' (H: Derive c e c') : Derive (Star c) e (c' _;_ (Star c)).
Hint Constructors Derive : core.

Lemma Derive_derive : forall (c0 c1 : Contract)(e : EventType), Derive c0 e c1 <-> c0 / e = c1.
Proof.
split.
- intros. induction H; try reflexivity. 
  * simpl. destruct (eq_event_dec e e); try solve [ reflexivity | contradiction ].
  * simpl. destruct (eq_event_dec e0 e); try solve [ reflexivity | contradiction ].
  * simpl. subst. reflexivity.
  * simpl. destruct (Nu_dec c0); subst; try reflexivity.
    apply NotNu_negation in n. contradiction.
  * simpl. destruct (Nu_dec c0); subst; try reflexivity.
    apply NotNu_negation in H0. contradiction. 
  * simpl. subst. reflexivity.
- intros. funelim (c0 / e);simpl;auto.
  * destruct (eq_event_dec e0 e); subst; auto.
  * destruct (Nu_dec c1);auto. 
Qed.

Lemma Derive_derive2 : forall (c : Contract)(e : EventType), Derive c e (c / e).
Proof.
intros. rewrite Derive_derive. reflexivity. Qed.


Equations matches (c:Contract)(s:Trace):bool :=
matches c [] := nu c;
matches c (e::s') := matches (c / e) s'.
Global Transparent matches.

(*Expression*)
Notation "s =~ c" := (matches c s) (at level 63).

Inductive bi_matches : Trace -> Contract -> Prop :=
 | BNu c (H : Nu c) : bi_matches [] c
 | BDerive c e s  (H2 : bi_matches s (c / e)) : bi_matches (e::s) c.
Hint Constructors bi_matches : core.





Lemma bi_matches_reflect : forall (s : Trace)(c : Contract), reflect (bi_matches s c) (s =~ c).
Proof.
intros. funelim (s =~ c).
- simpl. destruct (nu c) eqn:Heqn.
  * constructor. constructor. apply nu_true. assumption.
  * constructor. intro H. inversion H. apply nu_false in Heqn. apply NotNu_negation in Heqn.
    contradiction.
- simpl. destruct (l =~ c / e) eqn:Heqn.
  * constructor. inversion H. auto.
  * constructor. intro H2. inversion H2. subst. inversion H. contradiction.
Qed.

(** Relation between [matches] and [derive]. *)
Theorem derive_spec : forall (e:EventType)(s:Trace)(c:Contract),
  (e::s) =~ c  = s =~ c / e.
Proof. intros e s c. simpl. reflexivity.
Qed.

Lemma derive_spec_bi: forall (e : EventType)(s : Trace)(c : Contract),
 bi_matches (e::s) c <-> bi_matches s (c / e).
Proof. split;intros; (try inversion H) ; auto. Qed.

Reserved Notation "s ==~ re" (at level 63).

Inductive matches_comp : Trace -> Contract -> Prop :=
  | MSuccess : [] ==~ Success
  | MEvent x : [x] ==~ (Event x)
  | MSeq s1 c1 s2 c2
             (H1 : s1 ==~ c1)
             (H2 : s2 ==~ c2)
           : (s1 ++ s2) ==~ (c1 _;_ c2)
  | MPlusL s1 c1 c2
                (H1 : s1 ==~ c1)
              : s1 ==~ (c1 _+_ c2)
  | MPlusR c1 s2 c2
                (H2 : s2 ==~ c2)
              : s2 ==~ (c1 _+_ c2)
  | MStar0 c 
              : [] ==~ Star c
  | MStarSeq c s1 s2 (H1: s1 ==~ c) 
                     (H2: s2 ==~ Star c) 
              : s1 ++ s2 ==~ Star c
  where "s ==~ c" := (matches_comp s c).

Hint Constructors matches_comp : core.

Lemma bi_matches_plus_l : forall (s : Trace)(c1 c2 : Contract), bi_matches s c1 -> bi_matches s (c1 _+_ c2).
Proof.
intros. generalize dependent c2. induction H;auto;intros.
rewrite derive_spec_bi. simpl. auto.
Qed.

Lemma bi_matches_plus_r : forall (s : Trace)(c1 c2 : Contract), bi_matches s c2 -> bi_matches s (c1 _+_ c2).
Proof.
intros. generalize dependent c1. induction H;auto;intros.
rewrite derive_spec_bi. simpl. auto.
Qed.

Ltac nnn NN := apply NotNu_negation in NN ; contradiction. 

Lemma bi_matches_seq : forall (s1 s2 : Trace)(c1 c2 : Contract), 
bi_matches s1 c1 -> bi_matches s2 c2 -> bi_matches (s1 ++ s2) (c1 _;_ c2).
Proof.
intros. induction H.
- simpl. destruct H0.
  * auto.
  * constructor. simpl. destruct (Nu_dec c).
    ** apply bi_matches_plus_r. assumption.
    ** nnn n.
- simpl. rewrite derive_spec_bi. simpl. destruct (Nu_dec c).
  * apply bi_matches_plus_l. assumption.
  * assumption.
Qed.

Lemma bi_matches_star : forall (s1 s2 : Trace)(c : Contract), 
bi_matches s1 c -> bi_matches s2 (Star c) -> bi_matches (s1 ++ s2) (Star c).
Proof.
intros. inversion H.
- simpl. assumption.
- simpl. rewrite derive_spec_bi. simpl. apply bi_matches_seq;auto.
Qed.



Lemma Nu_empty : forall (c : Contract), Nu c <-> [] ==~ c.
Proof.
split;intros.
- induction H;auto. rewrite <- (app_nil_l []). auto.
- induction c;auto; inversion H;auto. apply app_eq_nil in H1 as [H1 H1']. subst. auto.
Qed.


Lemma derives_matches : forall (e : EventType)(s : Trace)(c : Contract), s ==~ c / e -> (e::s) ==~ c.
Proof.
intros. generalize dependent e. generalize dependent s. induction c;intros;simpl in H.
- inversion H.
- inversion H.
- destruct (eq_event_dec e e0).
  * inversion H. subst. auto.
  * inversion H.
- inversion H;auto.
- destruct (Nu_dec c1).
  * inversion H.
    ** inversion H2. subst. rewrite app_comm_cons. auto. 
    ** subst. rewrite <- (app_nil_l (e::s)). constructor. apply Nu_empty;auto. auto.
  * inversion H. subst. rewrite app_comm_cons. auto.
- inversion H. subst. rewrite app_comm_cons. auto.
Qed.



Lemma matches_bi_matches : forall (s : Trace)(c : Contract), s ==~ c <-> bi_matches s c.
Proof.
split ; intros.
- induction H;auto.
  * constructor. simpl. destruct (eq_event_dec x x). auto. contradiction.
  * apply bi_matches_seq;auto.
  * apply bi_matches_plus_l;auto.
  * apply bi_matches_plus_r;auto.
  * apply bi_matches_star;auto.
- induction H.
  * apply Nu_empty;auto.
  * apply derives_matches. assumption. 
Qed.

(*the proposition s ==~ c is reflected in the value s =~ c *)
Lemma matches_reflect : forall (s : Trace) (c : Contract), reflect (s ==~ c) (s =~ c).
Proof.
intros. destruct (bi_matches_reflect s c).
- constructor. apply matches_bi_matches. assumption.
- constructor. intro H. rewrite <- matches_bi_matches in n. contradiction.
Qed.

Lemma matches_comp_matches : forall (s : Trace)(c : Contract), s ==~ c <-> s =~ c = true.
Proof.
intros. destruct (matches_reflect s c).
- split ; auto.
- split; intros; try contradiction. discriminate. 
Qed.



Lemma derive_spec_comp : forall (c : Contract)(e : EventType)(s : Trace), e::s ==~ c <-> s ==~ c / e.
Proof.
intros. repeat rewrite matches_comp_matches. simpl. reflexivity.
Qed.


(*************************************************************************************)

Lemma plus_comm : forall (c1 c2 : Contract),(forall s, s ==~ (c1 _+_ c2) <-> s ==~ (c2 _+_ c1)).
Proof.
split.
- intros. inversion H ; auto. 
- intros. inversion H ; auto.
Qed.

Lemma plus_assoc : forall (c1 c2 c3 : Contract), (forall s, s==~((c1 _+_ c2) _+_ c3) <-> s ==~ (c1 _+_ (c2 _+_ c3))).
Proof.
split;intros.
- inversion H;auto.
  inversion H2;auto.
- inversion H;auto.
  inversion H1;auto.
Qed.

Lemma seq_assoc : forall (c1 c2 c3 : Contract),forall s, s==~((c1 _;_ c2) _;_ c3) <-> s==~ (c1 _;_ (c2 _;_ c3)).
Proof.
split.
- intro H. inversion H. inversion H3. rewrite <- app_assoc. apply MSeq.
  * apply H8.
  * apply MSeq.
    ** apply H9.
    ** apply H4.
- intro H. inversion H. inversion H4. rewrite -> app_assoc. apply MSeq.
  * apply MSeq.
    ** apply H3.
    ** apply H8.
  * apply H9.
Qed.

Lemma plus_or : forall (s : Trace)(c1 c2 : Contract), s ==~ (c1 _+_ c2) <-> s ==~ c1 \/ s ==~c2.
Proof. 
split.
- intros. repeat rewrite comp_iff_oper in *. inversion H; auto || auto.
- intros. destruct H;auto. 
Qed.

Fixpoint plus_fold (l : list Contract) : Contract :=
match l with
| [] => Failure
| c ::l => c _+_ (plus_fold l)
end.


Lemma plus_fold_app : forall (s:Trace)(l1 l2 : list Contract), 
s ==~ plus_fold (l1 ++ l2) <-> s ==~ (plus_fold l1) _+_ (plus_fold l2).
Proof.
intro. induction l1.
- intros. split.
  * intros. simpl in H. auto.
  * intros. simpl. simpl in H. inversion H. {  inversion H2. } assumption.
- intros. split.
  * intros. simpl in *. apply plus_or in H as [H | H] ; auto.
    specialize IHl1 with l2. apply IHl1 in H. apply plus_assoc. auto.
  * intros. simpl in *. apply plus_assoc in H. apply plus_or in H as [H | H].
    ** auto.
    ** apply MPlusR. apply IHl1. assumption.
Qed.


Lemma in_plus_fold : forall (s : Trace)(l : list Contract), s ==~ plus_fold l <-> 
(exists c, In c l /\ s ==~ c).
Proof.
intros. split.
- induction l.
  * intros. simpl in H. inversion H.
  * intros. simpl in H. apply plus_or in H as [H | H].
    ** exists a. split. apply in_eq. assumption.
    ** apply IHl in H as [c' [P1 P2]]. exists c'. split ; auto using  in_cons.
- intros. destruct H as [ c' [P1 P2]]. induction l.
  * destruct P1.
  * apply in_inv in P1 as [P1 | P1].
    ** simpl. rewrite P1. auto.
    ** simpl. auto.
Qed.






Fixpoint seq_fold (l : list Contract) :=
match l with
| [] => Success
| a::l' => a _;_ (seq_fold l')
end.



Lemma seq_fold_map : forall (s:Trace), s ==~ seq_fold (map Event s).
Proof.
induction s.
- simpl. auto.
- simpl. assert (HA: a::s = [a]++s). { reflexivity. } rewrite HA. constructor; auto.
Qed.


Lemma seq_fold_app : forall (s:Trace)(s0 s1 : list Contract), s ==~ seq_fold (s0 ++ s1) <-> s ==~ (seq_fold s0) _;_ (seq_fold s1).
Proof.
intros. generalize dependent s. generalize dependent s1.
induction s0;intros.
- simpl. split. intro. rewrite <- (app_nil_l s). constructor;auto. intros. inversion H. inversion H3. subst. simpl. assumption.
- simpl. split.
  * intros. inversion H. subst. rewrite seq_assoc. constructor. assumption. apply IHs0. assumption.
  * intros. rewrite seq_assoc in H. inversion H. subst. constructor. assumption. apply IHs0. assumption.
Qed.

(*******************************************************************************************************)

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
  | c_test c0 c1 (H1: forall e : EventType, c0 / e =R= c1 / e) : c0 =R= c1
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

CoInductive bisimilar2 : Contract -> Contract -> Prop :=
| Bisimilar2 c0 c1 (H0: Nu c0 <-> Nu c1) (H1 : forall e, bisimilar2 (c0 / e) (c1 / e)) : bisimilar2 c0  c1.



Lemma helper : forall c0 c1 e, (forall s : Trace, s ==~ c0 <-> s ==~ c1) -> 
(forall s : Trace, s ==~ c0/e <-> s ==~ c1/e).
Proof. 
intros. specialize H with (e::s). repeat rewrite derive_spec_comp in H. assumption. 
Qed.


Check Bisimilar2.
Lemma test2 : forall (c0 c1 : Contract),(forall s, s ==~ c0 <-> s ==~ c1) -> bisimilar2 c0 c1.
Proof.
cofix test2.
intros. apply Bisimilar2.
- specialize H with []. repeat rewrite <- Nu_empty in H. assumption.
- intros. apply test2. apply helper. assumption.
Qed.

Lemma test3 : forall (c0 c1 : Contract)(e : EventType), c0 =R= c1 -> Event e _;_ c0 =R= Event e _;_ c1.
Proof. intros. auto. Qed.

Lemma test4 : forall (c c': Contract)(e : EventType), NotNu c -> Derive c e c' -> c =R= Event e _;_ c'.
Proof. Admitted.

Definition alphabet := [Notify;Transfer].
Definition expand (c : Contract) := plus_fold (map (fun e => Event e _;_ c / e) alphabet).

Lemma c_eq_expand : forall (c : Contract), c =R= expand c.
Proof. Admitted.

Lemma c_eq_reduce_expand : forall (c0 c1 : Contract), (forall e, c0/e =R= c1/e) -> c0 =R= c1.
Proof. cofix c_eq_reduce_expand. Admitted.

Lemma bisimilar_c_eq : forall (c0 c1 : Contract), bisimilar2 c0 c1 -> c0 =R= c1.
Proof.
cofix bisimilar_c_eq.
intros. inversion H. subst.
apply c_test.
intros. apply bisimilar_c_eq. eauto. Qed.







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

Inductive RTrace : Set :=
| RNil : RTrace
| RElem : EventType -> RTrace
| RApp : RTrace -> RTrace -> RTrace
| RRepeat : list Trace -> RTrace.

Fixpoint stuck_dup (c : Contract) :=
match c with
| Failure => true
| c0 _+_ c1 => stuck_dup c0 && stuck_dup c1
| c0 _;_ _ => stuck_dup c0
| _ => false
end.

CoInductive Stream : Set :=
 | SNil : Stream
 | SCons : EventType -> Stream -> Stream.

CoFixpoint stream_app s1 s2 :=
match s1 with
| SNil => s2
| SCons e s1'=> SCons e (stream_app s1' s2)
end.

Fixpoint stream_of_trace (s : Trace) : Stream :=
match s with
| [] => SNil
| e::s' => SCons e (stream_of_trace s')
end.

CoFixpoint stream_repeat (s_iter s_orig : Trace) :=
match s_iter with
| [] => SNil
| e :: [] => SCons e (stream_repeat s_orig)
| e :: s' => SCons e (
| _ :: _ => (stream_of_trace (removelast s)) (SCons (last s Transfer) (stream_repeat s))
end.
stream_of_trace s  


Fixpoint monoms (c : Contract) : list RTrace :=
match c with
| Success => [RNil]
| Failure => []
| Event e => [RElem e]
| c0 _+_ c1 => (monoms c0) ++ (monoms c1)
| c0 _;_ c1 => map (fun (xy: RTrace*RTrace) => let (x,y):=xy in RApp x y) (list_prod (monoms c0) (monoms c1)) 
| Star c => if nu c || stuck_dup c then [RNil] else [RRepeat (monoms_l c)]
end
with 
monoms_l (c : Contract) : list Trace :=
match c with
| Success => [[]]
| Failure => []
| Event e => [e]
| c0 _+_ c1 => (monoms_l c0) ++ (monoms_l c1)
| c0 _;_ c1 => map ++ (list_prod (monoms_l c0) (monoms_l c1)) 
| Star c => monoms_l c
end.

Fixpoint contract_of_RTrace s :=
match s with
| RNil => Failure
| RElem e => Event e
| RApp s0 s1 => (contract_of_RTrace s0) _;_ (contract_of_RTrace s1)
| RRepeat l => Star (plus_fold (map contract_of_RTrace l))
end.



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


  Lemma bisimilar_c_eq : forall c1 c2, R c1 c2 -> c1 =R= c2. 
  cofix bisimilar_c_eq. assumption.
End bisimilar.





(******************************Contract unfolding not working yet********************************************)




Definition alphabet := [Notify;Transfer].

Inductive Stuck : Contract -> Prop :=
 | STFailure : Stuck Failure
 | STPLus c0 c1 (H0 : Stuck c0) (H1 : Stuck c1) : Stuck (c0 _+_ c1)
 | STSeq c0 c1 (H0 : Stuck c0) : Stuck (c0 _;_ c1).

Hint Constructors Stuck : core.

Inductive NotStuck : Contract -> Prop :=
 | NSTSuccess : NotStuck Success
 | NSEvent e : NotStuck (Event e)
 | NSTPlusL c0 c1 (H0 : NotStuck c0) : NotStuck (c0 _+_ c1)
 | NSTPlusR c0 c1 (H1 : NotStuck c1) : NotStuck (c0 _+_ c1)
 | NSTSeq c0 c1 (H0 : NotStuck c0) : NotStuck (c0 _;_ c1).

Hint Constructors NotStuck : core.

Fixpoint stuck (c : Contract) :=
match c with
| Failure => true
| c0 _+_ c1 => stuck c0 && stuck c1
| c0 _;_ _ => stuck c0
| _ => false
end.

Search (_ || _ = false).
Lemma stuck_false : forall (c : Contract), stuck c = false -> NotStuck c.
Proof.
induction c; intros.
- constructor.
- simpl in H. discriminate.
- constructor.
- simpl in H. apply andb_false_elim in H as [H | H]; auto.
- simpl in H. auto.
Defined.

Lemma stuck_true : forall (c : Contract), stuck c = true -> (Stuck c).
Proof.
induction c; intros; try (simpl in H ; discriminate).
- constructor.
- simpl in H. apply andb_prop in H as [H1 H2].  auto.
- simpl in H. auto.
Defined.


Definition stuck_dec (c : Contract) : {Stuck c}+{NotStuck c}.
Proof. destruct (stuck c) eqn:Heqn.
- left. auto using stuck_true.
- right. auto using stuck_false.
Defined.

Lemma NotStuck_negation : forall (c : Contract), NotStuck c -> ~(Stuck c).
Proof.
intros. induction H ; intro H2; inversion H2.
all : inversion H2; contradiction.
Qed.

Check max.
Fixpoint con_size (c:Contract):nat :=
match c with
| Failure => 0
| Success => 1
| Event _ => 2
| c0 _+_ c1 => max (con_size c0) (con_size c1) 
| c0 _;_ c1 => if stuck_dec c0 then 0 else (con_size c0) + (con_size c1)
end.


Lemma stuck_0 : forall (c : Contract), Stuck c -> con_size c = 0.
Proof.
intros. induction H.
- reflexivity.
- simpl. rewrite IHStuck1. rewrite IHStuck2. reflexivity.
- simpl. destruct (stuck_dec c0). reflexivity. apply NotStuck_negation in n. contradiction.
Defined.

Lemma NotStuck_0lt : forall (c : Contract), NotStuck c -> 0 < con_size c.
Proof.
intros. induction H; simpl ; try lia.
destruct (stuck_dec c0).
- apply NotStuck_negation in H. contradiction.
- lia.
Defined.


Lemma stuck_not_nullary : forall (c : Contract), Stuck c -> nu c = false.
Proof.
intros. induction H.
- reflexivity.
- simpl. rewrite IHStuck1. rewrite IHStuck2. reflexivity.
- simpl. rewrite IHStuck. reflexivity.
Defined.

Lemma stuck_derive : forall (c : Contract)(e : EventType), Stuck c -> c / e = c.
Proof.
intros. induction H.
- reflexivity.
- simpl. rewrite IHStuck1. rewrite IHStuck2. reflexivity.
- simpl. apply stuck_not_nullary in H. rewrite H. rewrite IHStuck. reflexivity.
Defined.

Lemma not_stuck_derives : forall (c : Contract), NotStuck c -> (forall (e : EventType), con_size (c / e) < con_size c).
Proof.
intros. induction c.
- simpl. lia.
- inversion H.
- simpl. destruct (eq_event_dec e0 e) ; simpl ; lia.
- simpl. inversion H.
  * destruct (stuck_dec c2).
    ** apply stuck_0 in s as s2. rewrite (stuck_derive _ s). rewrite s2. repeat rewrite (Max.max_comm _ 0). simpl.
       auto.
    ** apply IHc1 in H1.  apply IHc2 in n. lia.
  * destruct (stuck_dec c1).
    ** apply stuck_0 in s as s2. rewrite (stuck_derive _ s). rewrite s2. simpl.
       auto.
    ** apply IHc1 in n.  apply IHc2 in H0. lia.
- inversion H. subst. simpl. destruct (nu c1) eqn:Heqn.
  * destruct (stuck_dec c1). apply NotStuck_negation in H1. contradiction.
    simpl. destruct (stuck_dec (c1 / e)).
    ** simpl. destruct (stuck_dec c2).
      *** rewrite stuck_derive. apply PeanoNat.Nat.lt_add_pos_l. apply NotStuck_0lt. all :assumption.
      *** rewrite <- (plus_O_n (con_size (c2 / e))). apply IHc2 in n0. lia.
    ** apply IHc1 in H1. destruct (stuck_dec c2).
      *** rewrite (stuck_derive _ s). apply Max.max_case_strong.
        **** intros. apply Plus.plus_lt_compat_r. assumption.
        **** intros. lia.
      *** apply IHc1 in n. apply IHc2 in n1. lia.
  * destruct (stuck_dec c1).
    ** apply NotStuck_negation in H1. contradiction.
    ** simpl. destruct (stuck_dec (c1 / e)).
      *** pose proof (NotStuck_0lt H1). lia.
      *** apply Plus.plus_lt_compat_r. auto.
Defined.


Equations plus_norm (c : Contract) : (Contract) by  wf (con_size c) :=
plus_norm  c := if stuck_dec c then Failure
               else if nu c then Success _+_ plus_fold (map (fun e => (Event e) _;_ (plus_norm (c / e))) alphabet)
                            else  plus_fold (map (fun e => (Event e) _;_ (plus_norm (c / e))) alphabet).

Next Obligation. auto using not_stuck_derives. Defined.
Next Obligation. auto using not_stuck_derives. Defined.
Global Transparent plus_norm.
Eval compute in plus_norm (Transfer _._ Notify _._ Success _+_ Success).

Lemma Stuck_failure : forall (c : Contract), Stuck c -> (forall s, s ==~ c <-> s ==~ Failure).
Proof.
intros. split. 2: { intros. inversion H0. }
generalize dependent s.  induction c; intros.
- inversion H.
- assumption. 
- inversion H.
- inversion H. inversion H0; auto.
- inversion H. inversion H0. apply IHc1 in H7. inversion H7. assumption.
Qed. 

Lemma empty_nu : forall (c : Contract), [] ==~ c <-> nu c = true.
Proof.
intros. split. 
- induction c; intros.
  * reflexivity.
  * inversion H.
  * inversion H.
  * inversion H. { simpl. rewrite IHc1; try assumption. reflexivity. }
                { simpl. rewrite IHc2; try assumption. rewrite orb_comm.  reflexivity. }
  * simpl. inversion H. apply app_eq_nil in H1 as [H11 H12]. subst. rewrite IHc1. rewrite IHc2. reflexivity.
  all: assumption.
- intros. induction c.
  * constructor.
  * discriminate H.
  * discriminate H.
  * simpl in H. apply orb_prop in H as [H | H]; auto.
  * simpl in H. rewrite <- (app_nil_l []). apply andb_prop in H as [H1 H2]; auto.
Qed.


Lemma plus_norm_cons : forall (e:EventType)(s:Trace)(c:Contract),
(forall (e : EventType) (s : Trace), s ==~ c / e <-> s ==~ plus_norm (c / e)) ->
e :: s ==~ c <-> e :: s ==~ plus_fold (map (fun e0 : EventType => Event e0 _;_ plus_norm (c / e0)) alphabet).
Proof.
intros. repeat rewrite derive_spec_comp.
assert (HA: forall (l : list Contract)(e : EventType), (plus_fold l) / e = plus_fold (map (fun c => c / e) l)).
{ intros. induction l. - reflexivity. - simpl. f_equal. assumption. } rewrite HA. rewrite in_plus_fold.
rewrite map_map. rewrite H. split;intros.
- exists (Success _;_ (plus_norm (c / e))). split.
  * rewrite in_map_iff. exists e. split. 
      ** simpl. destruct (eq_event_dec e e);[ reflexivity | contradiction ].
      ** unfold alphabet. destruct e ; repeat (try apply in_eq ; try apply in_cons).
  * rewrite <- (app_nil_l s). constructor; auto.
- destruct H0 as [c0 [P0 P1]]. rewrite in_map_iff in P0. destruct P0 as [x [P3 P4]]. subst.
  simpl in P1. destruct (eq_event_dec x e).
  * inversion P1. inversion H3. subst. simpl. assumption.
  * inversion P1. inversion H3.
Qed.


Lemma plus_norm_nil : forall (c : Contract), ~([] ==~ plus_fold (map (fun e0 : EventType => Event e0 _;_ plus_norm (c / e0)) alphabet)).
Proof.
intros. intro H. apply in_plus_fold in H as [c0 [P0 P1]]. apply in_map_iff in P0 as [e [P P3]]. 
subst. inversion P1. apply app_eq_nil in H0 as [H0 H00]. subst. inversion H1.
Qed.
 
Theorem plus_norm_spec : forall (c : Contract)(s : Trace), s ==~ c <-> s ==~ plus_norm c.
Proof.
intros. funelim (plus_norm c). destruct (stuck_dec c).
- apply Stuck_failure. assumption.
- destruct (nu c) eqn:Heqn.
  * destruct s.
    ** split;intros;auto. apply empty_nu. assumption.
    ** assert (HA: forall (c : Contract), e::s ==~ Success _+_ c <-> e::s ==~ c).
       { split; intros. inversion H0. inversion H3. assumption. auto. } rewrite HA.
       apply plus_norm_cons. auto.
  * destruct s.
    ** split;intros.
      *** apply empty_nu in H0. rewrite Heqn in H0. discriminate.
      *** apply plus_norm_nil in H0 as [].
    ** apply plus_norm_cons. auto.
Qed.