Require Import CSL.Contract2.
Require Import Lists.List.
Require Import Sorting.Permutation.
Require Import Sorting.Mergesort.
Require Import Sorting.Sorted.
Require Import Bool.Bool.
Require Import Bool.Sumbool.
Require Import List Setoid Permutation Sorted Orders.
Import ListNotations.

Set Implicit Arguments.


Module TraceOrder <: TotalLeBool.
  Definition t := Trace.

  (*Notify <= Transfer*)
  Definition leb_event x y :=
    match x, y with
    | Transfer,Notify  => false
    | _, _ => true
    end.
  (*leb_event is total, anti symmetric and transitive*)

  Lemma leb_event_total : forall e1 e2, leb_event e1 e2 = true \/ leb_event e2 e1  = true.
  Proof. intros. destruct e1 ; destruct e2 ; auto || auto. Defined.

  Lemma leb_event_anti_sym : forall (e1 e2 : EventType), leb_event e1 e2 = leb_event e2 e1  ->  e1 = e2.
  Proof.
  intros. destruct e1 ; destruct e2 ; try reflexivity ; simpl in H ; simpl in H ; discriminate.
  Qed. 

(*  Lemma leb_event_anti_sym : forall (e1 e2 : EventType), TraceOrder.leb_event e1 e2 = true -> 
  TraceOrder.leb_event e2 e1 = true -> e1 = e2.
  Proof.
  intros. destruct e1 ; destruct e2 ; try reflexivity ; simpl in H ; simpl in H0 ; discriminate.
  Qed. *)

  Lemma leb_event_trans : forall (x y z : EventType), leb_event x y = true -> leb_event y z = true -> leb_event x z = true.
  Proof. intros. destruct x ; destruct y ; destruct z ; simpl in H ; simpl in H0 ; try reflexivity. 
  - destruct H0. simpl. reflexivity.
  - discriminate H.
  Qed.


  (*Lexicographic ordering of traces*)
  Fixpoint leb s1 s2 :=
    match s1, s2 with
    | [],_ => true
    | _,[] => false
    | a1::s1',a2::s2' => if (EventType_eq_dec a1 a2) 
                           then leb s1' s2' 
                           else leb_event a1 a2
    end.
  Infix "<=?" := leb (at level 70, no associativity).

  Lemma leb_anti_sym : forall s1 s2: Trace, s1 <=? s2 = (s2 <=? s1) -> s1 = s2.
  Proof.
  induction s1.
  - intros. destruct s2 ; try reflexivity. simpl in H. discriminate.
  - intros. destruct s2; simpl in H; try discriminate.
    destruct (EventType_eq_dec a e).
    ** rewrite e0. f_equal. destruct (EventType_eq_dec e a).
      *** auto.
      *** symmetry in e0. contradiction.
    ** destruct (EventType_eq_dec e a) ; try (symmetry in e0 ; contradiction).
       apply leb_event_anti_sym in H. contradiction.
  Qed.

  Lemma leb_trans : Transitive (fun s1 s2 => leb s1 s2 = true).
  Proof. unfold Transitive. induction x.
  - intros. reflexivity.
  - intros. destruct y ; destruct z ; try reflexivity ; try (simpl in H ; discriminate).
    simpl. destruct (EventType_eq_dec a e0). 
    * simpl in H. destruct (EventType_eq_dec a e).
      ** simpl in H0. subst. destruct (EventType_eq_dec e0 e0) ; try contradiction.
         eauto.
      ** simpl in H0. subst. destruct (EventType_eq_dec e e0).
        *** subst. contradiction.
        *** rewrite <- H0 in H. apply leb_event_anti_sym in H. contradiction.
    * simpl in H. destruct (EventType_eq_dec a e).
      ** simpl in H0. subst. destruct (EventType_eq_dec e e0) ; [ contradiction | assumption ].
      ** simpl in H0. destruct (EventType_eq_dec e e0).
        *** subst. assumption.
        *** eauto using leb_event_trans.
  Qed.


  Theorem leb_total : forall a1 a2, a1 <=? a2 = true \/ a2 <=? a1 = true.
  Proof.
  induction a1.
    - intros. simpl. now left.
    - destruct a2.
      * simpl. now right.
      * simpl. destruct (EventType_eq_dec a e) ; destruct (EventType_eq_dec e a) ;
               destruct (IHa1 a2) ; auto using leb_event_total || auto using leb_event_total.
  Defined.

  Definition leb_prop s1 s2 := s1 <=? s2 = true.
End TraceOrder.