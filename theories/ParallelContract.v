Require Import Lists.List.
Require Import Bool.Bool.
Require Import Bool.Sumbool.
Require Import Program.
From Equations Require Import Equations.
Require Import micromega.Lia.
Require Import FunctionalExtensionality.
Require Import Arith.
Import ListNotations.
Require Import CSL.Contract.

Set Implicit Arguments.

Hint Constructors matches_comp : core.



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


(*Taken from csl-formalization*)
Inductive interleave (A : Set) : list A -> list A -> list A -> Prop :=
| IntLeftNil  : forall t, interleave nil t t
| IntRightNil : forall t, interleave t nil t
| IntLeftCons : forall t1 t2 t3 e, interleave t1 t2 t3 -> interleave (e :: t1) t2 (e :: t3)
| IntRightCons : forall t1 t2 t3 e, interleave t1 t2 t3 -> interleave t1 (e :: t2) (e :: t3).


Reserved Notation "s p==~ re" (at level 63).

Inductive pmatches_comp : Trace -> PContract -> Prop :=
  | MPSuccess : [] p==~ PSuccess
  | MPEvent x : [x] p==~ (PEvent x)
  | MPPar s1 c1 s2 c2 s
             (H1 : s1 p==~ c1)
             (H2 : s2 p==~ c2)
             (H3 : interleave s1 s2 s)
           : s p==~ (c1 -*- c2)
  | MPPlusL s1 c1 c2
                (H1 : s1 p==~ c1)
              : s1 p==~ (c1 -+- c2)
  | MPPlusR c1 s2 c2
                (H2 : s2 p==~ c2)
              : s2 p==~ (c1 -+- c2)
  where "s p==~ c" := (pmatches_comp s c).


Fixpoint con_size (c:Contract):nat :=
match c with
| Success => 2
| Failure => 1
| Event e => 3
| c0 _;_ c1 => (con_size c0) * (con_size c1)
| c0 _+_ c1 => (con_size c0) + (con_size c1)
end.

Check sumbool_and.


Fixpoint norm  (c : Contract) : Contract :=
match c with
| Success => Success
| Failure => Failure
| Event e => Event e
| c0 _;_ c1 => let c0' := norm c0
               in let c1' := norm c1
                  in if (sumbool_or _ _ _ _ (eq_contract_dec c0' Failure) (eq_contract_dec c1' Failure ))  then Failure
                     else if (eq_contract_dec c0' Success) then c1'
                     else if (eq_contract_dec c1' Success) then c0'
                     else c0' _;_ c1'
| c0 _+_ c1 => let c0' := norm c0
               in let c1' := norm c1
                  in if (sumbool_and _ _ _ _ (eq_contract_dec c0' Success) (eq_contract_dec c1' Success)) then Success
                     else if (eq_contract_dec c0' Failure) then c1'
                     else if (eq_contract_dec c1' Failure) then c0'
                     else c0' _+_ c1'
end.




Lemma norm_plus_induct : forall (P : Contract -> Prop)(c0 c1 : Contract),
(norm c0 = Success -> norm c1 = Success -> P Success) ->
((norm c0 <> Success \/ norm c1 <> Success) ->  norm c0 = Failure -> P (norm c1)) ->
((norm c0 <> Success \/ norm c1 <> Success) ->  (norm c0 <> Failure) -> norm c1 = Failure -> P (norm c0)) ->
((norm c0 <> Success \/ norm c1 <> Success) ->  (norm c0 <> Failure) -> (norm c1 <> Failure) -> P (norm c0 _+_ norm c1))
-> P (norm (c0 _+_ c1)).
Proof.
intros. simpl. destruct (eq_contract_dec (norm c0) Failure). 
- destruct (sumbool_and (norm c0 = Success) (norm c0 <> Success)
      (norm c1 = Success) (norm c1 <> Success)
      (eq_contract_dec (norm c0) Success)
      (eq_contract_dec (norm c1) Success)) as [[a0 a1] | [a | a] ]; auto.
- destruct (sumbool_and (norm c0 = Success) (norm c0 <> Success)
      (norm c1 = Success) (norm c1 <> Success)
      (eq_contract_dec (norm c0) Success)
      (eq_contract_dec (norm c1) Success)) as [[a0 a1] | [a | a] ]; 
  destruct (eq_contract_dec (norm c1) Failure) ; auto.
Qed.

Lemma norm_seq_induct : forall (P : Contract -> Prop)(c0 c1 : Contract),
(norm c0 = Failure \/ norm c1 = Failure -> P Failure) ->
((norm c0 <> Failure /\ norm c1 <> Failure) ->  norm c0 = Success -> P (norm c1)) ->
((norm c0 <> Failure /\ norm c1 <> Failure) ->  (norm c0 <> Success) -> norm c1 = Success -> P (norm c0)) ->
((norm c0 <> Failure /\ norm c1 <> Failure) ->  (norm c0 <> Success) -> (norm c1 <> Success) -> P (norm c0 _;_ norm c1))
-> P (norm (c0 _;_ c1)).
Proof.
intros. simpl. destruct (eq_contract_dec (norm c0) Success).
- destruct (sumbool_or (norm c0 = Failure) (norm c0 <> Failure)
      (norm c1 = Failure) (norm c1 <> Failure)
      (eq_contract_dec (norm c0) Failure)
      (eq_contract_dec (norm c1) Failure)) ; try auto.
- destruct (sumbool_or (norm c0 = Failure) (norm c0 <> Failure) (norm c1 = Failure)
      (norm c1 <> Failure) (eq_contract_dec (norm c0) Failure)
      (eq_contract_dec (norm c1) Failure)) ; auto.
  * destruct (eq_contract_dec (norm c1) Success) ; auto.
Qed.


Lemma match_closed_norm : forall (s : Trace)(c : Contract), s ==~ c <-> s ==~ (norm c).
Proof.
split.
- intros. generalize dependent s. induction c; intros; try (simpl ; assumption).
  * apply norm_plus_induct.
    ** intros. rewrite H0 in IHc1. rewrite H1 in IHc2. inversion H; auto. 
    ** intros [H2 | H2] H3 ; inversion H; auto.
       all: (apply IHc1 in H4; rewrite H3 in H4; inversion H4).
    ** intros [ H2 | H2] H3 H4;
       inversion H ; auto; (rewrite H4 in IHc2; apply IHc2 in H5; inversion H5).
    ** intros [H2 | H2] H3 H4; inversion H; auto using MPlusL,MPlusR. 
  * apply norm_seq_induct.
    ** intros [H1 | H1]; inversion H.
      *** rewrite H1 in IHc1. apply IHc1 in H4. inversion H4.
      *** rewrite H1 in IHc2. apply IHc2 in H5. inversion H5.
    ** intros [H1 H2] H3 ; inversion H. apply IHc1 in H6. 
       rewrite H3 in H6. inversion H6. simpl. auto.
    ** intros [H1 H2] H3 H4; inversion H. apply IHc2 in H8.
       rewrite H4 in H8. inversion H8. rewrite app_nil_r. auto.
    ** intros [H1 H2] H3 H4. inversion H. auto.
- intros. generalize dependent s. induction c; intros; try (simpl ; assumption).
  * simpl in H. destruct (sumbool_and (norm c1 = Success) (norm c1 <> Success)
        (norm c2 = Success) (norm c2 <> Success)
        (eq_contract_dec (norm c1) Success)
        (eq_contract_dec (norm c2) Success)) as [[a1 a2] | [a | a]] ; auto.
    ** rewrite a1 in IHc1. auto.
    ** destruct (eq_contract_dec (norm c1) Failure) ; auto.
      *** destruct (eq_contract_dec (norm c2) Failure) ; auto.
        **** inversion H ; auto.
    ** destruct (eq_contract_dec (norm c1) Failure); auto.
      *** destruct (eq_contract_dec (norm c2) Failure) ; auto.
        **** inversion H ; auto.
  * simpl in H. destruct ( sumbool_or (norm c1 = Failure) (norm c1 <> Failure)
        (norm c2 = Failure) (norm c2 <> Failure)
        (eq_contract_dec (norm c1) Failure)
        (eq_contract_dec (norm c2) Failure)) as [[o | o ] | [o1 o2 ]] ; auto.
    ** inversion H.
    ** inversion H.
    ** destruct (eq_contract_dec (norm c1) Success) ; auto. 
      ***  rewrite <- (app_nil_l s). constructor ; try auto. { apply IHc1. rewrite e. constructor. }
      *** destruct (eq_contract_dec (norm c2) Success).
        **** rewrite <- (app_nil_r s). constructor ; try auto. { apply IHc2. rewrite e. auto. }
        **** inversion H. auto. 
Qed.

Lemma norm_failure_not_match : forall (c : Contract), norm c = Failure ->
forall (s : Trace), ~(s ==~ c).
Proof.
intros.
- intros. intro H2. apply match_closed_norm in H2. rewrite H in H2. inversion H2.
Qed.

Lemma norm_failure_equivalence : forall (c : Contract), norm c = Failure ->
forall (s : Trace), ~(s ==~ c).
Proof.
intros.
- apply norm_failure_not_match. assumption.
Qed.

Lemma norm_success_equivalence : forall (c : Contract), norm c = Success -> [] ==~ c.
Proof. intros. apply match_closed_norm. rewrite H. auto.
Qed.


(*A safe contract has a smaller derivative*)
Inductive safe : Contract -> Prop :=
| SASuccess : safe Success
| SAEvent e : safe (Event e)
| SASeq c1 c2 (H1 : safe c1) (H2 : safe c2) : safe (c1 _;_ c2)
| SAPlus c1 c2 (H1 : safe c1) (H2 : safe c2) : safe (c1 _+_ c2).
Hint Constructors safe : core.

Lemma failure_not_safe : forall (c : Contract), (norm c) = Failure -> ~(safe (norm c)).
Proof.
intros. intro H'. inversion H' ; try (rewrite H in H1 ; discriminate H1).
Qed.

Lemma safe_not_failure : forall (c : Contract),  (safe (norm c)) -> c <> Failure.
Proof.
intros. induction c; simpl in H; intro H2; try discriminate H2.
- inversion H.
Qed.

(*
Lemma not_safe_is_failure : forall (c : Contract), ~(safe (norm c)) -> (norm c) = Failure.
Proof.
intros. induction c ; try (simpl in H; exfalso; apply H; constructor).
- reflexivity.
- s H. intro H'. inversion H' ; try (rewrite H in H1 ; discriminate H1).
Qed.*)


Lemma norm_not_failure_plus : forall (c1 c2 : Contract), (norm c1 <> Failure -> safe (norm c1)) -> 
(norm c2 <> Failure -> safe (norm c2)) -> norm (c1 _+_ c2) <> Failure -> safe (norm c1) \/ safe (norm c2).
Proof. 
intros. simpl in H1. 
destruct (sumbool_and (norm c1 = Success) (norm c1 <> Success)
         (norm c2 = Success) (norm c2 <> Success)
         (eq_contract_dec (norm c1) Success)
         (eq_contract_dec (norm c2) Success)) as [[a1 a2] | a1].
  - right. rewrite a2. auto.
  - destruct (eq_contract_dec (norm c1) Failure). 
    * auto || auto.
    * destruct (eq_contract_dec (norm c2) Failure).
      ** auto || auto.
      ** auto || auto. 
Qed. 

Lemma norm_not_failure_seq : forall (c1 c2 : Contract), (norm c1 <> Failure -> safe (norm c1))  -> 
(norm c2 <> Failure -> safe (norm c2)) -> (norm (c1 _;_ c2)) <> Failure -> safe (norm c1) /\ safe (norm c2).
Proof.
intros. simpl in H1. 
destruct (sumbool_or (norm c1 = Failure) (norm c1 <> Failure)
         (norm c2 = Failure) (norm c2 <> Failure)
         (eq_contract_dec (norm c1) Failure)
         (eq_contract_dec (norm c2) Failure)).
- contradiction.
- destruct (eq_contract_dec (norm c1) Success).
  * rewrite e. split ; try constructor. auto.
  * destruct a as [a1 a2]. split ; auto.
Qed.



Lemma size_ge_1 : forall (c : Contract), 1 <= con_size c.
Proof. induction c.
- simpl. intuition. 
- simpl. intuition.
- simpl. intuition.
- simpl. rewrite IHc1. intuition.
- simpl. rewrite IHc1. rewrite <- (Nat.mul_1_r (con_size c1)) at 1. apply Nat.mul_le_mono.
  { intuition. } { intuition. }
Qed.

Hint Resolve size_ge_1 : core.

Lemma mult_two_contracts_ge1 : forall (c1 c2 : Contract), 1 <= con_size c1 * con_size c2.
Proof.
intros. rewrite <- Nat.mul_1_l at 1. apply Nat.mul_le_mono ; auto.
Qed.

Lemma not_failure_imp_safe : forall (c : Contract), (norm c) <> Failure -> safe (norm c).
Proof.
induction c; try (intros ; simpl ; auto) ; try contradiction.
- destruct (sumbool_and (norm c1 = Success) (norm c1 <> Success)
      (norm c2 = Success) (norm c2 <> Success)
      (eq_contract_dec (norm c1) Success)
      (eq_contract_dec (norm c2) Success)) as [a1 | [e2|e3]]; try auto.
  * destruct (eq_contract_dec (norm c1) Failure). 
    ** simpl in H. rewrite e in H. simpl in H. 
       destruct (eq_contract_dec (norm c2) Success). 
      *** rewrite e0. auto. 
      *** auto. 
    ** destruct (eq_contract_dec (norm c2) Failure).
      *** auto.
      *** destruct ( sumbool_and (norm c1 = Success) (norm c1 <> Success)
      (norm c2 = Success) (norm c2 <> Success)
      (eq_contract_dec (norm c1) Success)
      (eq_contract_dec (norm c2) Success)) ; constructor ; auto.
  * destruct (eq_contract_dec (norm c1) Failure).
    ** simpl in H. rewrite e in H. simpl in H.
       destruct (eq_contract_dec (norm c2) Success) ; auto.
    ** destruct (eq_contract_dec (norm c2) Failure) ; auto.
- destruct (sumbool_or (norm c1 = Failure) (norm c1 <> Failure) 
      (norm c2 = Failure) (norm c2 <> Failure)
      (eq_contract_dec (norm c1) Failure)
      (eq_contract_dec (norm c2) Failure)).
  * simpl in H. destruct o as [o | o].
    ** rewrite o in H. simpl in H. 
       destruct (eq_contract_dec (norm c2) Failure) ; contradiction.
    ** rewrite o in H. simpl in H.
       destruct (sumbool_or (norm c1 = Failure) (norm c1 <> Failure)
        (Failure = Failure) (Failure <> Failure)
        (eq_contract_dec (norm c1) Failure)
        (eq_contract_dec Failure Failure)).
      *** contradiction.
      *** destruct a as [a1 a2]. contradiction.
  * destruct (eq_contract_dec (norm c1) Success).
    ** destruct a as [a1 a2]. auto.
    ** destruct (eq_contract_dec (norm c2) Success).
      *** destruct a as [a1 a2]. auto.
      *** destruct a as [a1 a2] ; auto.
Qed.



Lemma norm_idempotent : forall (c0 : Contract), norm (norm c0) = norm c0.
Proof.
intros. induction c0 ; try reflexivity.
- apply norm_plus_induct ; intros ; auto ; try reflexivity.
  * simpl. rewrite IHc0_1. rewrite IHc0_2.
    destruct (sumbool_and (norm c0_1 = Success) (norm c0_1 <> Success)
    (norm c0_2 = Success) (norm c0_2 <> Success)
    (eq_contract_dec (norm c0_1) Success)
    (eq_contract_dec (norm c0_2) Success)).
    ** destruct H.
      *** destruct a. contradiction.
      *** destruct a. contradiction.
    ** destruct (eq_contract_dec (norm c0_1) Failure).
      *** contradiction.
      *** destruct (eq_contract_dec (norm c0_2) Failure).
        **** contradiction.
        **** reflexivity.
- apply norm_seq_induct ; intros ; auto ; try reflexivity.
  * simpl. destruct (sumbool_or (norm (norm c0_1) = Failure)
    (norm (norm c0_1) <> Failure) (norm (norm c0_2) = Failure)
    (norm (norm c0_2) <> Failure)
    (eq_contract_dec (norm (norm c0_1)) Failure)
    (eq_contract_dec (norm (norm c0_2)) Failure)).
    ** destruct o.
      *** destruct H. rewrite IHc0_1 in *. contradiction.
      *** destruct H. rewrite IHc0_2 in *. contradiction.
    ** destruct (eq_contract_dec (norm (norm c0_1)) Success). 
      *** destruct a.  rewrite IHc0_1 in *. contradiction.
      *** destruct (eq_contract_dec (norm (norm c0_2)) Success).
        ****  rewrite IHc0_2 in *. contradiction.
        **** rewrite IHc0_1. rewrite IHc0_2. reflexivity.
Qed.


Lemma safe_le : forall (c : Contract), safe c -> forall (e : EventType), con_size (c / e) <= (con_size c) - 1.
Proof. 
intros c H. induction H.
- intuition.
- intuition. simpl. destruct (eq_event_dec e e0) ; auto.
- intro e. simpl. destruct (nu c1) eqn:Heqn.
  * simpl. specialize IHsafe1 with e. specialize IHsafe2 with e. 
    transitivity ((con_size c1 - 1) * con_size c2 + (con_size c2 - 1)).
    ** apply Nat.add_le_mono. { apply Mult.mult_le_compat_r. intuition. } { intuition. }
    ** rewrite Nat.mul_sub_distr_r. simpl. rewrite Nat.add_0_r. rewrite Nat.add_comm. 
      rewrite <- (Nat.add_sub_swap _ _ _ (size_ge_1 c2)) . rewrite (Nat.add_le_mono_r _ _ 1).
      rewrite Nat.sub_add.
      *** rewrite Nat.sub_add. 2: { apply mult_two_contracts_ge1. }
          rewrite Nat.add_comm. rewrite Nat.sub_add. { reflexivity. }
          rewrite <- Nat.mul_1_l at 1. apply Nat.mul_le_mono_r. apply size_ge_1.
      *** rewrite <- Nat.add_0_r at 1. apply Nat.add_le_mono. { apply size_ge_1. } { lia. }
  * simpl. transitivity ((con_size c1 - 1) * con_size c2).
    ** apply Nat.mul_le_mono_r. apply IHsafe1.
    ** rewrite Nat.mul_sub_distr_r. apply Nat.sub_le_mono_l. transitivity (1 * 1).
      *** simpl. intuition.
      *** apply Mult.mult_le_compat_l. apply size_ge_1.
- intro e. simpl. assert (HR: con_size c1 + con_size c2 - 1 = (con_size c1 - 1) + con_size c2).
  * rewrite (Nat.add_sub_swap _ _ _ (size_ge_1 c1)). rewrite Nat.add_comm. reflexivity.
  * rewrite HR. apply Nat.add_le_mono.
    ** apply IHsafe1.
    ** transitivity (con_size c2 - 1). { apply IHsafe2. } { lia. } 
Qed.

Lemma safe_lt : forall (c : Contract), safe c -> forall (e : EventType), con_size (c / e) < (con_size c).
Proof.
intros c H e. pose proof (safe_le H e). apply Lt.le_lt_n_Sm in H0. rewrite (Minus.minus_Sn_m _ _ (size_ge_1 c)) in H0.
rewrite Nat.sub_succ in H0. rewrite Nat.sub_0_r in H0. apply H0. 
Qed.

Definition alphabet := [Transfer;Notify].


Lemma all_in_alpabet : forall e : EventType, In e alphabet.
Proof.
intros. unfold alphabet. destruct e. 
- apply in_eq.
- apply in_cons. apply in_eq.
Qed.

Search (1 * ?a).
Lemma norm_le : forall (c : Contract), con_size (norm c) <= con_size c.
Proof.
assert (HA: 2 = 1 +1). { reflexivity. }
induction c.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. destruct (sumbool_and (norm c1 = Success) (norm c1 <> Success)
      (norm c2 = Success) (norm c2 <> Success)
      (eq_contract_dec (norm c1) Success)
      (eq_contract_dec (norm c2) Success)).
  * simpl. rewrite  HA. apply Nat.add_le_mono ; apply size_ge_1.
  * destruct (eq_contract_dec (norm c1) Failure). 
    ** lia.
    ** destruct (sumbool_and (norm c1 = Success) (norm c1 <> Success)
      (norm c2 = Success) (norm c2 <> Success)
      (eq_contract_dec (norm c1) Success)
      (eq_contract_dec (norm c2) Success));
       destruct (eq_contract_dec (norm c2) Failure) ; simpl ; lia.
- simpl. destruct (eq_contract_dec (norm c1) Failure).
  * simpl. destruct (eq_contract_dec (norm c2) Failure ); simpl; apply mult_two_contracts_ge1.
  * destruct (sumbool_or (norm c1 = Failure) (norm c1 <> Failure) 
      (norm c2 = Failure) (norm c2 <> Failure) in_right
      (eq_contract_dec (norm c2) Failure)).
    ** simpl; apply mult_two_contracts_ge1.
    ** destruct (eq_contract_dec (norm c1) Success). 
      *** rewrite <- Nat.mul_1_l at 1. apply Nat.mul_le_mono ; auto.
      *** destruct (eq_contract_dec (norm c2) Success).
        **** rewrite <- Nat.mul_1_r at 1.
           apply Nat.mul_le_mono ; auto.
        **** simpl. apply Nat.mul_le_mono ; auto.
Qed.


Lemma times_termination : forall (c0 c1 : Contract)(e : EventType), 
norm c0 <> Failure -> (norm c1) <> Failure -> con_size (norm c0 / e) + con_size (norm c1) < con_size c0 + con_size c1.
Proof.
intros. apply not_failure_imp_safe in H. apply not_failure_imp_safe in H0. 
apply (Nat.lt_le_trans _ (con_size (norm c0) + con_size (norm c1)) _).
- apply Nat.add_lt_le_mono ; auto using (safe_lt H).
- apply Nat.add_le_mono ; apply norm_le.
Qed.


Equations times (c0 : Contract) (c1 : Contract) : (list Contract) by  wf ((con_size (c0)) + (con_size (c1))) lt :=
  times c0 c1 :=
        if eq_contract_dec (norm c0) Failure
        then []
        else if eq_contract_dec (norm c1) Failure
        then []
        else if eq_contract_dec (norm c0) Success then [norm c1]
        else if eq_contract_dec (norm c1) Success then [norm c0]
        (*Incorrect, for completeness if c0 is nullary, then expression below ++ [norm c1] should be returned*)
        else (flat_map (fun e => map (fun c => (Event e) _;_ c) (times ((norm c0)  / e) (norm c1) )) alphabet)
             ++
             (flat_map (fun e => map (fun c => (Event e) _;_ c) (times (norm c0)  ((norm c1)  /e ))) alphabet).
Next Obligation.
apply (times_termination _ _ e) ; assumption.
Qed.
Next Obligation.
rewrite Nat.add_comm. rewrite (Nat.add_comm (con_size c0)). 
apply (times_termination _ _ e); assumption.
Qed.
Global Transparent times.
Print eq_contract_dec.

Compute ((times Failure Failure)).

(*Compute (times (Transfer _._ Success) ( Transfer _._ Success)).*)

Definition list_derivative (l : list Contract)(e : EventType) := map (fun c => c / e) l.



Lemma list_derivative_spec : forall (l : list Contract)(e : EventType), (plus_fold l) / e = plus_fold (list_derivative l e).
Proof. intros. induction l.
- reflexivity.
- simpl. f_equal. assumption.
Qed.

Lemma list_derivative_app : forall (l1 l2 : list Contract)(e : EventType), 
list_derivative (l1 ++ l2) e = (list_derivative l1 e) ++ (list_derivative l2 e).
Proof.
intros. unfold list_derivative. apply map_app.
Qed.

Search (?a :: ?b = [?a] ++ ?b). 

Search (map (fun _ => map _ _)). 

Lemma plus_failure : forall (s : Trace)(c : Contract), s ==~ c _+_ Failure -> s ==~ c.
Proof.
intros. inversion H. assumption. inversion H1.
Qed.



Lemma flat_map_list_derivative : forall (f: EventType -> list Contract) (l: list EventType)(e : EventType),
  list_derivative (flat_map f l) e = flat_map (fun x=> list_derivative (f x) e) l.
Proof. intros. repeat rewrite flat_map_concat_map. repeat unfold list_derivative. 
rewrite concat_map. rewrite map_map. reflexivity.
Qed.


Lemma inline_derivative_l : forall (c0 c1 : Contract)(e' : EventType),
list_derivative (flat_map (fun e => map (fun c => (Event e) _;_ c) (times ((norm c0) / e) (norm c1) )) alphabet) e' = 
(flat_map (fun e => map (fun c =>  (if eq_event_dec e e' then Success _;_ c else Failure _;_ c) ) (times ((norm c0) / e) (norm c1) )) alphabet).
Proof.
intros. rewrite flat_map_list_derivative. 
unfold list_derivative.
assert (HA : (fun x => map (fun c : Contract => c / e') (map (fun c : Contract => Event x _;_ c)  (times ((norm c0)/x) (norm c1) ))) =
             fun x => (map (fun c : Contract => (if eq_event_dec x e' then Success _;_ c else Failure _;_ c)) (times ((norm c0)/x) (norm c1)))).
- apply functional_extensionality. intros. rewrite map_map.
  assert (HA2: (fun x0 : Contract => (Event x _;_ x0) / e') = 
               (fun c : Contract => if eq_event_dec x e' then Success _;_ c else Failure _;_ c)).
  * apply functional_extensionality. intros. simpl. destruct (eq_event_dec x e') ; reflexivity.
  * now rewrite HA2.
- now rewrite HA. 
Qed.


Lemma inline_derivative_r : forall (c0 c1 : Contract)(e' : EventType),
list_derivative (flat_map (fun e => map (fun c => (Event e) _;_ c) (times ((norm c0)) ((norm c1)/ e) )) alphabet) e' = 
(flat_map (fun e => map (fun c =>  (if eq_event_dec e e' then Success _;_ c else Failure _;_ c) ) (times ((norm c0)) ((norm c1) / e) )) alphabet).
Proof.
intros. rewrite flat_map_list_derivative. 
unfold list_derivative.
assert (HA : (fun x => map (fun c : Contract => c / e') (map (fun c : Contract => Event x _;_ c)  (times ((norm c0)) ((norm c1)/ x) ))) =
             fun x => (map (fun c : Contract => (if eq_event_dec x e' then Success _;_ c else Failure _;_ c)) (times ((norm c0)) ((norm c1) / x)))).
- apply functional_extensionality. intros. rewrite map_map.
  assert (HA2: (fun x0 : Contract => (Event x _;_ x0) / e') = 
               (fun c : Contract => if eq_event_dec x e' then Success _;_ c else Failure _;_ c)).
  * apply functional_extensionality. intros. simpl. destruct (eq_event_dec x e'); reflexivity.
  * now rewrite HA2.
- now rewrite HA. 
Qed.


Lemma interleave_filter : forall (A:Set)(f : A -> bool)(l : list A), interleave (filter f l) (filter (fun x => negb (f x)) l) l.
Proof. 
intros. induction l.
- simpl. constructor.
- simpl. destruct (f a) eqn:Heqn ; simpl ; constructor ; assumption.
Qed.

Lemma interleave_closed_map : forall (A B:Set)(l1 l2 l : list A)(f : A ->  B), interleave l1 l2 l -> 
  interleave (map f l1) (map f l2) (map f l).
Proof. intros. induction H; simpl ; try constructor ; try assumption. 
Qed.


Lemma interleave_closed_concat : forall (A:Set) (l1 l2 l : list (list A)), interleave l1 l2 l -> 
  interleave (concat l1) (concat l2) (concat l).
Proof. intros.
assert (cons_app : forall (A : Type)(a : A) (l' : list A), a :: l' = [a] ++ l').
  { intros. reflexivity. }
 induction H; try (simpl ; constructor).
- induction e.
  * simpl. assumption.
  * simpl. simpl in IHe. constructor. assumption.
- induction e.
  * simpl. assumption.
  * simpl. simpl in IHe. constructor. assumption.
Qed.

Lemma interleave_closed_flat_map : forall (A B:Set) (l1 l2 l : list A)(f : A -> list B), interleave l1 l2 l -> 
  interleave (flat_map f l1) (flat_map f l2) (flat_map f l).
Proof. intros. repeat rewrite flat_map_concat_map. apply interleave_closed_concat.
apply interleave_closed_map. induction H ; try (simpl ; constructor) ; assumption.
Qed.




Lemma or_imp : forall a b c : Prop, (a \/ b -> c) -> (b -> c).
intros. apply H. right. assumption.
Qed.

Lemma map_congruence : forall (A B:Set) (f g : A -> B) (l1 l2 : list A),
l1 = l2 -> (forall (x : A), In x l1 -> f x = g x) -> map f l1 = map g l2.
Proof. intros. subst. induction l2. 
- intros. subst. reflexivity.
- intros. simpl. pose proof (H0 a (in_eq a _)). rewrite H. apply f_equal.
  simpl in H0.
  * assert (HA: forall x : A, In x l2 -> f x = g x).
    {  intros. specialize H0 with x. apply H0. right. assumption. }
    apply IHl2. assumption.
Qed. 


Fixpoint trans (p : PContract) : Contract :=
match p with
| PSuccess => Success
| PFailure => Failure
| PEvent e => Event e
| p0 -*- p1 => plus_fold (times (trans p0) (trans p1))
| p0 -+- p1 => (trans p0) _+_ (trans p1)
end.


Lemma derive_spec_comp : forall (c : Contract)(e : EventType)(s : Trace), e::s ==~ c <-> s ==~ c / e.
Proof.
split ; repeat rewrite comp_iff_oper ; intro H ; rewrite <- H ; apply derive_spec.
Qed.





(*in_inv*)
Lemma oper_false : forall (s : Trace)(c : Contract), ~(s ==~c) -> s =~ c = false.
Proof.
intros. destruct (s =~ c) eqn:Heqn.
- apply comp_iff_oper in Heqn. contradiction.
- reflexivity.
Qed.

Lemma reduce_success : forall (s : Trace)(c : Contract), s =~ Success _;_ c = s =~ c.
Proof.
intros. destruct s.
- reflexivity.
- simpl. destruct (s =~ c / e) eqn:Heqn. 
  * apply comp_iff_oper. apply MPlusR. apply comp_iff_oper. assumption.
  * apply oper_false. intro H2. apply plus_or in H2 as [H2 | H2].
    ** inversion H2. inversion H3.
    ** apply comp_iff_oper in H2. rewrite Heqn in H2. discriminate.
Qed.

Lemma reduce_success_comp : forall (s : Trace)(c : Contract), s ==~ Success _;_ c <-> s ==~ c.
Proof.
split.
- intros. apply comp_iff_oper in H. rewrite reduce_success in H.
apply comp_iff_oper in H. assumption.
- intros. rewrite <- (app_nil_l s). constructor ; auto.
Qed.


Lemma times_derivative_or: forall (c0 c1 : Contract)(e : EventType)(s : Trace), s ==~ (plus_fold (times c0 c1)) / e
 -> s ==~ plus_fold ((times ((norm c0) / e) (norm c1))) \/ s==~ plus_fold (times (norm c0) ((norm c1) / e)).
Proof. 
intros. simp times in H. destruct (eq_contract_dec (norm c0) Failure) eqn:Heqn1.
  * inversion H. 
  * destruct (eq_contract_dec (norm c1) Failure).
    ** inversion H.
    ** destruct (eq_contract_dec (norm c0) Success).
      *** simpl in H. right. rewrite e0. simp times. simpl.
          destruct (eq_contract_dec (norm (norm c1 / e)) Failure).
        **** apply plus_failure in H. apply norm_failure_equivalence with (s:=s) in e1.
             contradiction.
        **** apply plus_failure in H. simpl. apply MPlusL. apply -> match_closed_norm.
             assumption.
      *** destruct (eq_contract_dec (norm c1) Success).
        **** left. rewrite e0. simp times. simpl. 
              destruct (eq_contract_dec (norm (norm c0 / e)) Failure).
          ***** simpl in H. apply plus_failure in H.
                apply match_closed_norm in H. rewrite e1 in H. inversion H.
          ***** destruct (eq_contract_dec (norm (norm c0 / e)) Success).
            ****** simpl in H. apply plus_failure in H. 
                   apply match_closed_norm in H. rewrite e1 in H.
                   simpl. apply MPlusL. assumption.
            ****** simpl in *. apply MPlusL. apply -> match_closed_norm.
                   apply plus_failure in H. assumption.  
(*Everything up until this point is only for the base cases Failure and Success*)
        **** rewrite list_derivative_spec in H. rewrite list_derivative_app in H.
             apply plus_fold_app in H. apply plus_or in H as [H | H].
          ***** left. rewrite inline_derivative_l in H. 
                apply in_plus_fold in H as [c' [P1 P2]].
                apply in_flat_map in P1 as [x' [P3 P4]].
            ****** apply in_plus_fold. destruct (eq_event_dec x' e).
              ******* apply in_map_iff in P4 as [c'' [P5 P6]].
                      exists c''. rewrite e0 in P6. rewrite <- P5 in P2.
                      apply -> reduce_success_comp in P2.  split ; try assumption.
              ******* apply in_map_iff in P4 as [c'' [P5 P6]]. rewrite <- P5 in P2.
                      inversion P2. inversion H0.
          ***** right. rewrite inline_derivative_r in H. 
                apply in_plus_fold in H as [c' [P1 P2]].
                apply in_flat_map in P1 as [x' [P3 P4]].
            ****** apply in_plus_fold. destruct (eq_event_dec x' e).
              ******* apply in_map_iff in P4 as [c'' [P5 P6]].
                      exists c''. rewrite e0 in P6. rewrite <- P5 in P2.
                      apply -> reduce_success_comp in P2.  split ; try assumption.
              ******* apply in_map_iff in P4 as [c'' [P5 P6]]. rewrite <- P5 in P2.
                      inversion P2. inversion H0.
Qed.
 

Lemma or_times_derivative: forall (c0 c1 : Contract)(e : EventType)(s : Trace), 
s ==~ plus_fold ((times ((norm c0) / e) (norm c1))) \/ s==~ plus_fold (times (norm c0) ((norm c1) / e))
-> s ==~ (plus_fold (times c0 c1)) / e.
Proof.
intros. simp times. destruct (eq_contract_dec (norm c0) Failure).
  * rewrite e0 in H. simp times in H. simpl in H. destruct H ; inversion H.
  * destruct (eq_contract_dec (norm c1) Failure). 
    ** rewrite e0 in H.  simp times in H.
       destruct (eq_contract_dec (norm (norm c0 / e)) Failure). 
      *** destruct H.
        **** simpl in H. inversion H.
        **** destruct (eq_contract_dec (norm (norm c0)) Failure). 
          ***** simpl in H.  inversion H. 
          ***** destruct (eq_contract_dec (norm (Failure / e)) Failure). 
            ******  simpl in H.  inversion H. 
            ****** contradiction. 
      *** destruct (eq_contract_dec (norm Failure) Failure).
          destruct H. simpl in H ; inversion H.
          destruct (eq_contract_dec (norm (norm c0)) Failure).
          simpl in H. inversion H.
          destruct (eq_contract_dec (norm (Failure / e)) Failure).
        **** simpl in H. inversion H. 
        **** destruct (eq_contract_dec (norm (norm c0)) Success).
             simpl in H. inversion H. inversion H2. inversion H1.
             destruct (eq_contract_dec (norm (Failure / e)) Success). contradiction. contradiction.
        **** contradiction.
    ** destruct (eq_contract_dec (norm c0) Success). 
      *** rewrite e0 in H. simpl in H. destruct H.
        **** inversion H.
        **** simp times in H. simpl in H.
             destruct (eq_contract_dec (norm (norm c1 / e)) Failure).
          ***** simpl in H. inversion H.
          ***** simpl in H. inversion H. 
            ****** simpl. apply MPlusL.  apply match_closed_norm in H2. auto.
            ****** inversion H1.
      *** destruct (eq_contract_dec (norm c1) Success).
        **** rewrite e0 in H. simp times in H. simpl in H.  
          ***** destruct (eq_contract_dec (norm (norm c0 / e)) Failure).
            ****** destruct H.
              ******* simpl in H. inversion H.
              ******* destruct (eq_contract_dec (norm (norm c0)) Failure ) ; simpl in H ; inversion H.
           ****** destruct H. 
              ******* destruct (eq_contract_dec (norm (norm c0 / e)) Success). 
                ******** simpl in H. inversion H.
                  ********* inversion H2. simpl. apply MPlusL. apply match_closed_norm. rewrite e1.
                            auto.
                  ********* inversion H1.
                ******** simpl in *. inversion H. { apply MPlusL. apply match_closed_norm. apply H2. } inversion H1.
              ******* destruct (eq_contract_dec (norm (norm c0)) Failure); simpl in H; inversion H.
          **** rewrite list_derivative_spec. rewrite list_derivative_app.
             apply plus_fold_app. destruct H. 
            ***** apply MPlusL. rewrite inline_derivative_l. 
                  apply in_plus_fold. apply in_plus_fold in H as [c' [P1 P2]].
                  exists (Success _;_ c'). split. 2: { apply reduce_success_comp. assumption. }
                  apply in_flat_map. exists e. split. { apply all_in_alpabet. }
                  apply in_map_iff. exists c'. 
                  destruct (eq_event_dec e e) ; auto || auto. contradiction n3. reflexivity.
            ***** apply MPlusR. rewrite inline_derivative_r. 
                  apply in_plus_fold. apply in_plus_fold in H as [c' [P1 P2]].
                  exists (Success _;_ c'). split. 2: { apply reduce_success_comp. assumption. }
                  apply in_flat_map. exists e. split. { apply all_in_alpabet. }
                  apply in_map_iff. exists c'. 
                  destruct (eq_event_dec e e) ; auto || auto. contradiction n3. reflexivity.
Qed.


Lemma plus_fold_empty_success : forall (c0 c1 : Contract), [] ==~ plus_fold (times c0 c1)
 -> [] ==~ norm c0 /\ [] ==~ norm c1.
Proof.
intros. funelim (times c0 c1).
  destruct (eq_contract_dec (norm c0) Failure).
  * rewrite <- Heqcall in H1. simpl in H1. inversion H1.
  * destruct (eq_contract_dec (norm c1) Failure) eqn:Heqn1.
    ** rewrite <- Heqcall in H1. simpl in H1. inversion H1.
    ** destruct (eq_contract_dec (norm c0) Success).
      *** simp times in H1. rewrite e in H1.
          simpl in H1. rewrite Heqn1 in H1. simpl in H1. apply plus_failure in H1.
          rewrite e. split. { constructor. } { assumption. }
      *** destruct (eq_contract_dec (norm c1) Success).
        **** rewrite e. rewrite <- Heqcall in H1. simpl in H1. apply plus_failure in H1.
             split. assumption. constructor.
        **** rewrite <- Heqcall in H1.
             apply plus_fold_app in H1. apply plus_or in H1 as [H1 | H1];
             apply in_plus_fold in H1 as [c' [P1 P2]]; apply in_flat_map in P1 as [x' [P3 P4]];
             apply in_map_iff in P4 as [e' [P5 P6]]; rewrite <- P5 in P2;
             inversion P2; apply app_eq_nil in H1 as [H6 H7]; rewrite H6 in H4; inversion H4.
Qed.


Lemma times_par : forall (s : Trace)(c1 c2 : Contract) , s ==~ plus_fold (times c1 c2) -> exists (s1 s2 : Trace), 
interleave s1 s2 s /\ s1 ==~ c1 /\ s2 ==~ c2.
Proof.
intros. generalize dependent c2. generalize dependent c1. induction s.
  * intros. exists []. exists []. split. constructor. apply plus_fold_empty_success in H as [H1 H2].
    subst ; split ; apply match_closed_norm; assumption. 
  * intros. apply derive_spec_comp in H. apply times_derivative_or in H as [H | H].
    ** specialize IHs with (c1:=norm c1 / a)(c2:=norm c2). apply IHs in H as [s1' [s2' [P1 [P2 P3]]]].
      exists (a :: s1'). exists s2'. split.
      *** try (constructor ; assumption).
      *** split. { apply match_closed_norm. apply derive_spec_comp. assumption. } { apply match_closed_norm in P3. assumption.  }
    ** specialize IHs with (c1:=norm c1)(c2:=norm c2 / a). apply IHs in H as [s1' [s2' [P1 [P2 P3]]]].
       exists s1'. exists (a::s2'). split.
      *** try (constructor ; assumption).
      *** split. { apply match_closed_norm. assumption. } { apply match_closed_norm . apply derive_spec_comp. assumption.  }

Qed.




Lemma matches_pmatches : forall (p : PContract), (forall (s : Trace), s ==~ (trans p) -> s p==~ p).
Proof. induction p.
- intros s H. simpl in H. inversion H. apply MPSuccess.
- intros s H. simpl in H. inversion H.
- intros s H. simpl in H. inversion H. apply MPEvent.
- intros s H. simpl in H. inversion H.
  * apply MPPlusL. apply IHp1. apply H2.
  * apply MPPlusR. apply IHp2. apply H1.
- intros s H. simpl in H. apply times_par in H. destruct H as [s1 [s2 [P1 [P2 P3]]]].
  * apply MPPar with (s1:=s1)(s2:=s2). { apply (IHp1 _ P2). } { apply (IHp2 _ P3). } { apply P1. }
Qed.


(*This lemma does not hold*)
(*
Lemma pmatches_matches : forall (p : PContract), (forall (s : Trace), s p==~ p -> s ==~ (trans p)).
Proof.
intros. induction H.
- constructor.
- constructor.
- simpl. apply times_par. exists s1. exists s2. split ; try split ; assumption.
- simpl. apply MPlusL. assumption.
- simpl. apply MPlusR. assumption.
Qed.
*)

