Require Import Lists.List.
Require Import Bool.Bool.
Import ListNotations.
Require Export Setoid.
Require Export Relation_Definitions.

Inductive EventType : Type :=
| Transfer : EventType
| Notify : EventType.

Definition eq_event (e1:EventType)(e2:EventType):bool :=
match e1,e2 with
| Transfer,Transfer => true
| Notify, Notify => true
| _ , _ => false
end.

(*For equality should I try with computational reflection as it
 is done in the libraries: https://coq.inria.fr/library/Coq.Bool.Sumbool.html
 and seen in software foundations: https://softwarefoundations.cis.upenn.edu/vfa-current/Decide.html*)

(*Definition event_dec : forall a b : EventType, {a = b} + {a <> b}.*)


Definition Trace := List.list EventType % type.


Inductive Contract : Set :=
| Success : Contract
| Failure : Contract
| Event : EventType -> Contract -> Contract
| CPlus : Contract -> Contract -> Contract
| CSeq : Contract -> Contract -> Contract.

Notation "e _._ c" := (Event e c)
                    (at level 41, right associativity).

Notation "c0 _;_ c1"  := (CSeq c0 c1)
                         (at level 50, left associativity).

Notation "c0 _+_ c1"  := (CPlus c0 c1)
                         (at level 61, left associativity).

(*For a nullary contract c, nu c = true*)
Fixpoint nu(c:Contract):bool :=
match c with
| Success => true
| Failure => false
| e _._ c => false
| c0 _;_ c1 => nu c0
| c0 _+_ c1 => nu c0 || nu c1
end.


(*Derivative of contract with respect to an event*)
Fixpoint derive(e:EventType)(c:Contract):Contract :=
match c with
| Success => Failure
| Failure => Failure
| e1 _._ c => if eq_event e1 e then c else Failure
| c0 _;_ c1 => match nu c0 with
               | true => (derive e c0) _+_ (derive e c1)
               | false => (derive e c0)
               end
| c0 _+_ c1 => (derive e c0) _+_ (derive e c1)
end.


Notation "c / e" := (derive e c).

Fixpoint matches (c:Contract)(s:Trace):bool :=
match s with
| [] => nu c
| e::s' => matches (c / e) s'
end.

(*Expression*)
Notation "c ~= s" := (matches c s) (at level 60).

(*Propositions*)
Notation "c ~== s" := (matches c s = true) (at level 60).
Notation "c ~!= s" := (matches c s = false) (at level 60).

(** Relation between [matches] and [derive]. *)
Theorem derivation : forall (e:EventType)(s:Trace)(c:Contract),
  c ~= (e::s) = c / e ~= s.
Proof. intros e s c. simpl. auto. 
Qed.

(*[Contract] as Setoid*)
Definition c_eq (c c':Contract) : Prop := forall s, c ~= s = c' ~=s.

Check reflexive.

Notation "a =R= b" := (c_eq a b) (at level 70).

Lemma c_eq_refl : reflexive Contract c_eq.
Proof.
  unfold reflexive. intro x. unfold c_eq. intro s. auto.
Qed.

Lemma c_eq_sym : symmetric Contract c_eq.
Proof.
  unfold symmetric. intros x y. unfold c_eq. intro H. auto.
Qed.


(*Question: Is transitivity both a proposition and a proof method?*)
Lemma c_eq_trans: transitive Contract c_eq.
Proof.
  unfold transitive.  intros x y z.  unfold c_eq in *. intros Hxy Hyz s.
  transitivity (y ~= s); auto.
Qed.

Add Parametric Relation : Contract c_eq
  reflexivity proved by c_eq_refl
  symmetry proved by c_eq_sym
  transitivity proved by c_eq_trans
  as Contract_setoid.

Definition bool_eq (a a':bool) : Prop := a = a'.
Definition event_eq (a a':EventType) : Prop := a = a'.

(*nu is morphism from (Contract,c_eq) to (Bool,bool_eq) *)
Lemma nu_equals : forall c c', c =R= c' -> nu c = nu c'.
Proof.
  unfold c_eq. intros c c' H.
  specialize (H []%list); simpl in H. auto.
Qed.

Add Parametric Morphism : nu with
signature c_eq ==> bool_eq as nu_morphism.
Proof.
  intros x y H. apply nu_equals. auto.
Qed.

(*derive is morphism from (EventType,event_eq) and (Contract,c_eq) to (Contract,c_eq) *)
Lemma derive_equals : forall c c', c =R= c' -> (forall a, c / a =R= c' / a).
Proof.
  intros c c' H. unfold c_eq. intros a s.
  repeat rewrite <- derivation. auto.
Qed.

Add Parametric Morphism : derive with
signature event_eq ==> c_eq ==> c_eq as derive_morphism.
Proof.
  intros x y H. intros x0 y0 H0.
  inversion H. rewrite <- H1.
  apply derive_equals. auto.
Qed.


  
(*Example*)
Example test_1: Success ~== [].
Proof. unfold matches. reflexivity.
Qed.

Definition contract2 := Transfer _._ Notify _._ Success
                       _+_ 
                        Success _;_ Notify _._ Transfer _._ Success. 

Example test_2_1: contract2 ~== [Transfer; Notify].
Proof. unfold matches.  reflexivity.
Qed.

Example test_2_2: contract2 ~== [Notify; Transfer].
Proof. unfold matches.  reflexivity.
Qed.

Example test_2_3: contract2 ~!= [Notify; Notify].
Proof. unfold matches.  reflexivity.
Qed.

(**)

(*Prove algebraic properties*)

(*Is it interesting to mechanize the denotation of a contract? fx for choice it could be
  denotation c1 _+_ c2 := forall s : Trace, s in (denotation c1) \/ s in (denotation c2) *)







