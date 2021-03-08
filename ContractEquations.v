Require Import CSL.Contract.

Reserved Notation "c0 =R= c1" (at level 63).

Inductive c_eq : Contract -> Contract -> Prop :=
  | plus_assoc c0 c1 c2 : (c0 _+_ c1) _+_ c2 =R= c0 _+_ (c1 _+_ c2)
  | plus_comm c0 c1: c0 _+_ c1 =R= c1 _+_ c0
  | plus_neut c: c _+_ Failure =R= c
  | seq_assoc c0 c1 c2 : (c0 _;_ c1) _;_ c2 =R= c0 _;_ (c1 _;_ c2)
  | seq_neut c0 c1 c2 : (c0 _;_ ) _;_ c2 =R= c0 _;_ (c1 _;_ c2)
  | distr_l c0 c1 c2 : c0 _;_ (c1 _+_ c2) =R= (c0 _+_ c1) _;_ (c0 _+_ c2)
  | distr_r c0 c1 c2 : (c0 _+_ c1) _;_ c2 =R= (c0 _+_ c2) _;_ (c1 _+_ c2)
  where "c1 =R= c2" := (c_eq c1 c2).


  | plus_idem : Failure _+_ Failure =R= Failure




Definition c_eq (c c':Contract) : Prop := forall s, s ==~ c <-> s ==~ c'.

Notation "a =R= b" := (c_eq a b) (at level 70).


Lemma plus_comm : forall (c1 c2 : Contract), (c1 _+_ c2) =R= (c2 _+_ c1).
Proof.
split ; intros ; inversion H ; auto.
Qed.

Lemma plus_assoc : forall (c1 c2 c3 : Contract), ((c1 _+_ c2) _+_ c3) =R= (c1 _+_ (c2 _+_ c3)).
Proof.
split.
- intro H. inversion H.
  * inversion H2 ; auto. 
  * auto.
- intro H. inversion H.
  * inversion H2 ; auto.
  * inversion H1 ; auto.
Qed.


Lemma seq_assoc : forall (c1 c2 c3 : Contract), ((c1 _;_ c2) _;_ c3) =R= (c1 _;_ (c2 _;_ c3)).
Proof.
split.
- intros. inversion H. inversion H3. rewrite <- app_assoc. all : auto.
- intro H. inversion H. inversion H4. rewrite -> app_assoc. all : auto. 
Qed.

Lemma plus_or : forall (s : Trace)(c1 c2 : Contract), s ==~ (c1 _+_ c2) <-> s ==~ c1 \/ s ==~c2.
Proof. 
split.
- intros. repeat rewrite comp_iff_oper in *. 
apply plus_or_oper in H. assumption.
- intros. destruct H; auto.
Qed.


Lemma plus_distr : forall (c1 c2 c3 : Contract), (c1 _;_ (c2 _+_ c3)) =R= (c1 _;_ c2) _+_ (c1 _;_ c3).
Proof. split.
- intros. inversion H ; inversion H4 ; auto.
- intros. apply plus_or in H as [H | H] ; inversion H ; auto.
Qed.

Lemma plus_distr2 : forall (c1 c2 c3 : Contract), ((c1 _+_ c2) _;_ c3) =R= (c1 _;_ c3) _+_ (c2 _;_ c3).
Proof. split.
- intros ; inversion H ; inversion H3 ; auto.
- intros ; inversion H ; try inversion H2 ; try inversion H1 ; auto.
Qed.
