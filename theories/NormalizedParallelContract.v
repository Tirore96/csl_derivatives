Require Import CSL.Contract.
Require Import CSL.Order.
Require Import CSL.ContractEquations.
Require Import Lists.List.
Require Import Sorting.Permutation.
Require Import Sorting.Mergesort.
Require Import Sorting.Sorted.
Require Import Bool.Bool.
Require Import Bool.Sumbool.
Require Import List Setoid Permutation Sorted Orders.
Require Import Arith.
Require Import micromega.Lia.
Require Import Program.Basics.
Require Import FunctionalExtensionality.
From Equations Require Import Equations.
Import ListNotations.

Set Implicit Arguments.

(*Parallel contracts section*)
Inductive PContract : Set :=
| PSuccess : PContract
| PFailure : PContract
| PEvent : EventType -> PContract
| PPlus : PContract -> PContract -> PContract
| PPar : PContract -> PContract -> PContract.

Notation "e -.- c" := (PPar (PEvent e) c)
                    (at level 41, right associativity).

Notation "c0 -*- c1"  := (PPar c0 c1)
                         (at level 50, left associativity).

Notation "c0 -+- c1"  := (PPlus c0 c1)
                         (at level 61, left associativity).

Check nil.
(*Taken from csl-formalization*)
Inductive interleave (A : Set) : list A -> list A -> list A -> Prop :=
| IntLeftNil  : forall t, interleave nil t t
| IntRightNil : forall t, interleave t nil t
| IntLeftCons : forall t1 t2 t3 e, interleave t1 t2 t3 -> interleave (e :: t1) t2 (e :: t3)
| IntRightCons : forall t1 t2 t3 e, interleave t1 t2 t3 -> interleave t1 (e :: t2) (e :: t3).




Reserved Notation "s #==~ re" (at level 63).


Inductive pmatches_comp : Trace -> PContract -> Prop :=
  | MPSuccess : [] #==~ PSuccess
  | MPEvent x : [x] #==~ (PEvent x)
  | MPPar s1 c1 s2 c2 s
             (H1 : s1 #==~ c1)
             (H2 : s2 #==~ c2)
             (H3 : interleave s1 s2 s)
           : s #==~ (c1 -*- c2)
  | MPPlusL s1 c1 c2
                (H1 : s1 #==~ c1)
              : s1 #==~ (c1 -+- c2)
  | MPPlusR c1 s2 c2
                (H2 : s2 #==~ c2)
              : s2 #==~ (c1 -+- c2)
  where "s #==~ c" := (pmatches_comp s c).


Definition nat_of_event (e : EventType) : nat :=
match e with
| Notify => 0
| Transfer => 1
end.
Definition alphabet := [Notify;Transfer].

Fixpoint p_monoms (p : PContract) : list Trace :=
match p with
| PSuccess => [[]]
| PFailure => []
| PEvent e => [[e]]
| p0 -+- p1 => (p_monoms p0) ++ (p_monoms p1)
| c0 -*- c1 => flat_map (fun m0 => map (fun m1 => m0 ++ m1) (p_monoms c1)) (p_monoms c0)
end.

Definition map_add (e: EventType) (n : nat) (f : (EventType -> nat)) : (EventType -> nat) :=
fun (e' : EventType) => if eq_event_dec e' e then f e' + n else f e'.

Definition map_sub (e : EventType) (n : nat)(f : (EventType -> nat)) : (EventType -> nat) :=
fun (e' : EventType) => if eq_event_dec e' e then f e' - n else f e'.

Search (_ + _ - _ = _).

Lemma map_add_sub : forall (e : EventType)(f : EventType -> nat),
map_sub e 1 (map_add e 1 f) = f.
Proof.
intros. unfold map_add,map_sub. apply functional_extensionality.
intros. destruct (eq_event_dec x e).
  - simpl. lia. 
  - reflexivity.
Qed.



Fixpoint p_maps (p : PContract) : list (EventType -> nat) :=
match p with
| PSuccess => [fun (e : EventType) => 0]
| PFailure => []
| PEvent e => [map_add e 1 (fun (e : EventType) => 0)]
| p0 -+- p1 => (p_maps p0) ++ (p_maps p1)
| c0 -*- c1 => flat_map (fun f0 => map (fun f1 => fun (e : EventType) => (f0 e) + (f1 e)) (p_maps c1)) (p_maps c0)
end.

Fixpoint m_map (s: Trace) : (EventType -> nat) :=
match s with
| [] => fun (e : EventType) => 0
| e::s' => map_add e 1 (m_map s')
end.


Fixpoint eq_map (alphabet : list EventType)(f1 f2 : (EventType -> nat)) : Prop :=
match alphabet with
| [] => True
| e::alphabet' => (f1 e) = (f2 e) /\ eq_map alphabet' f1 f2
end.


(*
Lemma eq_map_sub : forall (alphabet : list EventType) (f1 f2 : (EventType -> nat))(e : EventType),
eq_map alphabet f1 f2 -> eq_map alphabet (map_sub e 1 f1) (map_sub e 1 f2).
Proof.
intros. induction alphabet0.
- reflexivity.
- simpl. split. simpl in H. destruct H.
  * unfold map_sub. destruct (eq_event_dec a e); rewrite H ; reflexivity.
  * simpl in H. destruct H. auto.
Qed.*)

Lemma eq_map_add : forall (alphabet : list EventType) (f1 f2 : (EventType -> nat))(e : EventType),
eq_map alphabet f1 f2 -> eq_map alphabet (map_add e 1 f1) (map_add e 1 f2).
Proof.
intros. induction alphabet0.
- reflexivity.
- simpl. split. simpl in H. destruct H.
  * unfold map_add. destruct (eq_event_dec a e); rewrite H ; reflexivity.
  * simpl in H. destruct H. auto.
Qed.

Lemma eq_map_substitute : forall (alphabet : list EventType) (f1 f2 f3 f : EventType -> nat),
eq_map alphabet f1 f2 -> eq_map alphabet (fun e : EventType => f1 e + f e) f3 = eq_map alphabet (fun e : EventType => f2 e + f e) f3.
Proof. 
intros. induction alphabet0.
- reflexivity.
- simpl in *. destruct H. apply IHalphabet0 in H0. rewrite H0. rewrite H. reflexivity.
Qed.

Lemma eq_map_comm : forall (alphabet : list EventType) (f1 f2 f3 : EventType -> nat),
eq_map alphabet (fun e : EventType => f1 e + f2 e) f3 = eq_map alphabet (fun e : EventType => f2 e + f1 e) f3.
Proof.
intros. induction alphabet0.
- reflexivity.
- simpl. rewrite IHalphabet0. rewrite plus_comm. reflexivity.
Qed. 

Lemma eq_map_interleave : forall (s1 s2 s : Trace)(alphabet : list EventType),
interleave s1 s2 s -> eq_map alphabet (fun e : EventType => (m_map s1) e + (m_map s2) e) (m_map s).
Proof.
intros. induction H; intros.
  * induction alphabet0; try (reflexivity).
    simpl in *. split ; [ reflexivity | assumption ].
  * induction alphabet0; try (reflexivity).
    simpl in *. rewrite plus_comm. simpl. split ; [ reflexivity | assumption ].
  * simpl. assert (HA : (fun e0 : EventType => map_add e 1 (m_map t1) e0 + m_map t2 e0) =
                        map_add e 1 (fun e0 : EventType => (m_map t1) e0 + m_map t2 e0)).
    ** apply functional_extensionality. intros. unfold map_add. destruct (eq_event_dec x e); lia.
    ** rewrite HA. apply eq_map_add. assumption.
  *  simpl. assert (HA : (fun e0 : EventType => m_map t1 e0 + map_add e 1 (m_map t2) e0) =
                        map_add e 1 (fun e0 : EventType => (m_map t1) e0 + m_map t2 e0)).
    ** apply functional_extensionality. intros. unfold map_add. destruct (eq_event_dec x e); lia.
    ** rewrite HA. apply eq_map_add. assumption.
Qed.

Lemma pmatches_count : forall (s : Trace)(p : PContract)(alphabet : list EventType),
 s #==~ p <-> Exists (fun f => eq_map alphabet f (m_map s)) (p_maps p).
Proof.
split.
- generalize dependent s. induction p ; intros.
  * inversion H. simpl. constructor. induction (alphabet0).
    ** simpl. reflexivity.
    ** simpl. split; [reflexivity | assumption].
  * inversion H.
  * inversion H.
    ** simpl. constructor. induction (alphabet0).
      *** simpl. reflexivity.
      *** simpl. split ; [reflexivity | assumption].
  * simpl. induction alphabet0.
    ** simpl. inversion H.
      *** apply IHp1 in H2. apply Exists_exists.
          apply Exists_exists in H2 as [x [P1 P2]].
          exists x. split. 2: { reflexivity. }
          apply in_or_app. left. assumption.
      *** apply IHp2 in H1. apply Exists_exists.
          apply Exists_exists in H1 as [x [P1 P2]].
          exists x. split. 2: { reflexivity. }
          apply in_or_app. right. assumption.
    ** simpl. inversion H.
      *** apply IHp1 in H2 as H2_p. apply Exists_exists.
          apply Exists_exists in H2_p as [x [P1 P2]].
          exists x. split.
        **** apply IHp1 in H2. 
             apply Exists_exists in H2 as [x' [P1' P2']].
             apply in_or_app. left. assumption.
        **** simpl in P2. assumption.
      *** apply IHp2 in H1 as H1_p. apply Exists_exists.
          apply Exists_exists in H1_p as [x [P1 P2]].
          exists x. split.
        **** apply IHp2 in H1. 
             apply Exists_exists in H1 as [x' [P1' P2']].
             apply in_or_app. right. assumption.
        **** simpl in P2. assumption.
  * inversion H. subst. apply IHp1 in H3 as H3_a. apply IHp2 in H4 as H4_a.
    apply Exists_exists in H3_a as [f [P3 P3']]. apply Exists_exists in H4_a as [f' [P4 P4']].
    apply Exists_exists. exists (fun e => (f e) + (f' e)). split.
    ** simpl. apply in_flat_map. exists f. split; try assumption.
       apply in_map_iff. exists f'. split ; try assumption. reflexivity.
    ** rewrite (eq_map_substitute _ _ _ _ _ P3'). rewrite eq_map_comm.
       rewrite (eq_map_substitute _ _ _ _ _ P4'). rewrite eq_map_comm.
       apply eq_map_interleave with (s1:=s1) (s2:=s2);try assumption.
- generalize dependent s. induction p; intros.
  * apply Exists_exists in H as [x' [P1 P2]]. simpl in *. destruct P1.
Admitted.

Equations interl (A:Type)(l1 l2 : list A) : list (list A) by wf ((length l1) + (length l2)) lt :=
interl [] t := [t];
interl t []  := [t];
interl (a1::l1') (a2::l2') => map (fun l => a1::l) (interl (l1') (a2::l2')) ++
                             map (fun l => a2::l) (interl (a1::l1') l2').
Next Obligation. lia. Qed.


Fixpoint traces_of_map (alphabet : list EventType) (f : (EventType -> nat)) : list Trace :=
match alphabet with
| [] => [[]]
| e::alphabet' => if eq_nat_decide (f e) 0 
                    then traces_of_map alphabet' f
                    else let traces := traces_of_map alphabet' (map_sub e (f e) f)
                         in flat_map (fun s => interl (repeat e (f e)) s) traces
end.

(*
Definition EN := PEvent Notify.
Definition ET := PEvent Transfer.
Definition pcon3 := EN -*- (EN -+- ET).

Compute (map (traces_of_map alphabet) (p_maps pcon3)).*)

Definition trans (alphabet : list EventType) (p : PContract) : Contract := contract_of_monoms (flat_map (traces_of_map alphabet) (p_maps p)).


Lemma matches_count : forall (s : Trace)(p : PContract)(alphabet : list EventType),
Exists (fun f => eq_map alphabet f (m_map s)) (p_maps p) <-> s ==~ trans alphabet p.
Proof.
intros. split.
- intros. induction H.
  * induction p.
    ** destruct alphabet0.
      *** unfold trans. simpl in *. unfold contract_of_monoms. simpl. constructor. unfold contract_of_monom. simpl. Admitted.

Lemma pmatches_iff_matches : forall (s : Trace)(p : PContract), s #==~ p <-> s ==~ trans alphabet p.
Proof.
split; intros.
- apply matches_count. apply pmatches_count. assumption.
- apply pmatches_count with (alphabet:=alphabet). apply matches_count. assumption.
Qed.
