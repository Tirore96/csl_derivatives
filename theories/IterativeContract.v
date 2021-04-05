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
(*
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
*)



(*Derivative of contract with respect to an event*)
Equations derive(e:EventType)(c:Contract):Contract :=
derive e Success := Failure;
derive e Failure := Failure;
derive e (Event e1) := if eq_event_dec e1 e then Success else Failure;
derive e (c0 _;_ c1) := if nu c0 then ((derive e c0) _;_ c1) _+_ (derive e c1)
                          else (derive e c0) _;_ c1;
derive e (c0 _+_ c1) := (derive e c0) _+_ (derive e c1);
derive e (Star c) := derive e c _;_ (Star c).
Global Transparent derive.

Notation "c / e" := (derive e c).

(*
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
*)

Equations matches (c:Contract)(s:Trace):bool :=
matches c [] := nu c;
matches c (e::s') := matches (c / e) s'.
Global Transparent matches.

(*Expression*)
Notation "s =~ c" := (matches c s) (at level 63).

Inductive Matches : Trace -> Contract -> Prop :=
 | BNu c (H : nu c = true) : Matches [] c
 | BDerive c e s  (H2 : Matches s (c / e)) : Matches (e::s) c.
Hint Constructors Matches : core.





Lemma Matches_reflect : forall (s : Trace)(c : Contract), reflect (Matches s c) (s =~ c).
Proof.
intros. funelim (s =~ c).
- simpl. destruct (nu c) eqn:Heqn.
  * constructor. auto. 
  * constructor. intro H. inversion H. rewrite Heqn in H0. discriminate.
- simpl. destruct (l =~ c / e) eqn:Heqn.
  * constructor. inversion H. auto.
  * constructor. intro H2. inversion H2. subst. inversion H. contradiction.
Qed.

(** Relation between [matches] and [derive]. *)
Theorem derive_spec : forall (e:EventType)(s:Trace)(c:Contract),
  (e::s) =~ c  = s =~ c / e.
Proof. intros e s c. simpl. reflexivity.
Qed.

Lemma derive_spec2: forall (e : EventType)(s : Trace)(c : Contract),
 Matches (e::s) c <-> Matches s (c / e).
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

Lemma simpl_Matches_nil_plus : forall c0 c1, nu c0 || nu c1 = true -> Matches [] (c0 _+_ c1).
Proof. intros; constructor ; simpl ; intuition. Qed.

Lemma simpl_Matches_nil_seq : forall c0 c1, nu c0 && nu c1 = true -> Matches [] (c0 _;_ c1).
Proof. intros; constructor ; simpl ; intuition. Qed.



Hint Extern 1 =>
  match goal with
    | [ |- context[Matches [] (?c0 _+_ ?c1)]  ] => intros;  apply simpl_Matches_nil_plus ; intuition
    | [ |- context[Matches [] (?c0 _;_ ?c1)]  ] => intros;  apply simpl_Matches_nil_seq ; intuition
  end : Mbase. 

Lemma Matches_plus_l : forall (s : Trace)(c1 c2 : Contract), Matches s c1 -> Matches s (c1 _+_ c2).
Proof. intros. generalize dependent c2. induction H;eauto with Mbase.
Qed.



Lemma Matches_plus_r : forall (s : Trace)(c1 c2 : Contract), Matches s c2 -> Matches s (c1 _+_ c2).
Proof.
Proof. intros. generalize dependent c1. induction H;eauto with Mbase.
Qed.

Lemma Matches_seq : forall (s1 s2 : Trace)(c1 c2 : Contract), 
Matches s1 c1 -> Matches s2 c2 -> Matches (s1 ++ s2) (c1 _;_ c2).
Proof.
intros. induction H;simpl.
- destruct H0;  auto with Mbase.
  constructor. simpl. destruct (nu c) eqn:Heqn; try discriminate.
  auto using Matches_plus_r.
- rewrite derive_spec2. simpl. destruct (nu c) eqn:heqn ; auto.
  auto using Matches_plus_l.
Qed.

Lemma Matches_star : forall (s1 s2 : Trace)(c : Contract), 
Matches s1 c -> Matches s2 (Star c) -> Matches (s1 ++ s2) (Star c).
Proof.
intros. inversion H; auto.
simpl; rewrite derive_spec2; simpl; auto using Matches_seq.
Qed.

Lemma nu_empty : forall (c : Contract), nu c = true <-> [] ==~ c.
Proof.
split;intros.
- induction c; simpl in H ; try discriminate; auto. apply orb_prop in H. destruct H;auto.
  rewrite <- (app_nil_l []); auto.
- induction c;auto; inversion H; simpl; intuition. 
  apply app_eq_nil in H1 as [H1 H1']. subst. intuition. 
Qed.


(*
Lemma Nu_empty : forall (c : Contract), Nu c <-> [] ==~ c.
Proof.
split;intros.
- induction H;auto. rewrite <- (app_nil_l []). auto.
- induction c;auto; inversion H;auto. apply app_eq_nil in H1 as [H1 H1']. subst. auto.
Qed.*)


Lemma derives_matches : forall (c : Contract)(e : EventType)(s : Trace), s ==~ c / e -> (e::s) ==~ c.
Proof.
induction c;intros;simpl in H; try solve [inversion H].
- destruct (eq_event_dec e e0); inversion H. subst ; auto.
- destruct (nu c1) eqn:Heqn;inversion H;auto.
- destruct (nu c1) eqn:Heqn.
  * inversion H.
    ** inversion H2. rewrite app_comm_cons. auto.
    ** rewrite <- (app_nil_l (e::s)). constructor; auto using nu_empty.
       rewrite <- nu_empty. assumption.
  * inversion H. rewrite app_comm_cons. auto.
- inversion H. rewrite app_comm_cons. auto.
Qed.



Lemma matches_Matches : forall (s : Trace)(c : Contract), s ==~ c <-> Matches s c.
Proof.
split ; intros.
- induction H;auto.
  * constructor. simpl. destruct (eq_event_dec x x). auto. contradiction.
  * apply Matches_seq;auto.
  * apply Matches_plus_l;auto.
  * apply Matches_plus_r;auto.
  * apply Matches_star;auto.
- induction H.
  * apply nu_empty;auto.
  * apply derives_matches. assumption. 
Qed.

(*the proposition s ==~ c is reflected in the value s =~ c *)
Lemma matches_reflect : forall (s : Trace) (c : Contract), reflect (s ==~ c) (s =~ c).
Proof.
intros. destruct (Matches_reflect s c).
- constructor. apply matches_Matches. assumption.
- constructor. intro H. rewrite <- matches_Matches in n. contradiction.
Qed.

Lemma matches_comp_iff_matches : forall (s : Trace)(c : Contract), s ==~ c <-> s =~ c = true.
Proof.
intros. destruct (matches_reflect s c).
- split ; auto.
- split; intros; try contradiction. discriminate. 
Qed.



Lemma derive_spec_comp : forall (c : Contract)(e : EventType)(s : Trace), e::s ==~ c <-> s ==~ c / e.
Proof.
intros. repeat rewrite matches_comp_iff_matches. simpl. reflexivity.
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


