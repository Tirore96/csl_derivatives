Require Import CSL.Contract.
Require Import CSL.Order.
Require Import Lists.List.
Require Import Sorting.Permutation.
Require Import Sorting.Mergesort.
Require Import Sorting.Sorted.
Require Import Bool.Bool.
Require Import Bool.Sumbool.
Require Import List Setoid Permutation Sorted Orders.
Import ListNotations.

Set Implicit Arguments.

Module Import TraceSort := Sort TraceOrder.

Reserved Notation "c0 =R= c1" (at level 63).

Hint Constructors matches_comp : core.

Inductive c_eq : Contract -> Contract -> Prop :=
  | c_plus_assoc c0 c1 c2 : (c0 _+_ c1) _+_ c2 =R= c0 _+_ (c1 _+_ c2)
  | c_plus_comm c0 c1: c0 _+_ c1 =R= c1 _+_ c0
  | c_plus_neut c: c _+_ Failure =R= c
  | c_plus_idemp c : c _+_ c =R= c 
  | c_seq_assoc c0 c1 c2 : (c0 _;_ c1) _;_ c2 =R= c0 _;_ (c1 _;_ c2)
  | c_seq_neut_l c : (Success _;_ c) =R= c 
  | c_seq_neut_r c : c _;_ Success =R= c 
  | c_distr_l c0 c1 c2 : c0 _;_ (c1 _+_ c2) =R= (c0 _;_ c1) _+_ (c0 _;_ c2)
  | c_distr_r c0 c1 c2 : (c0 _+_ c1) _;_ c2 =R= (c0 _;_ c2) _+_ (c1 _;_ c2)
  | c_refl c : c =R= c
  | c_sym c0 c1 (H: c0 =R= c1) : c1 =R= c0
  | c_trans c0 c1 c2 (H1 : c0 =R= c1) (H2 : c1 =R= c2) : c0 =R= c2
  where "c1 =R= c2" := (c_eq c1 c2).

Add Parametric Relation : Contract c_eq
  reflexivity proved by c_refl
  symmetry proved by c_sym
  transitivity proved by c_trans
  as Contract_setoid.

Lemma c_eq_soundness : forall (c0 c1 : Contract), c0 =R= c1 -> (forall s : Trace, s ==~ c0 <-> s ==~ c1).
Proof.
- intros. induction H.
  * split ; intros ; inversion H; auto. all: inversion H2 ; auto. inversion H1 ; auto.
  * split ; intros ; inversion H ; auto. 
  * split ; intros ; inversion H ; auto. inversion H1.
  * split ; intros ; inversion H ; auto.
  * split ; intros ; inversion H ; auto. 
    ** inversion H3. rewrite <- app_assoc. auto.
    ** inversion H4. rewrite app_assoc. auto.
  * split ; intros. 
    **  inversion H. inversion H3. now assumption.
    ** rewrite <- (app_nil_l s). auto. 
  * split ; intros.
    ** inversion H. inversion H4. rewrite app_nil_r. assumption.
    ** rewrite <- (app_nil_r s). auto.
  * split ; intros ; inversion H.
    ** inversion H4 ; auto.
    ** inversion H2 ; auto.
    ** inversion H1 ; auto.
  * split ; intros ; inversion H.
    ** inversion H3 ; auto.
    ** inversion H2 ; auto.
    ** inversion H1 ; auto.
  * split ; intros ; assumption.
  * destruct IHc_eq. split; intros ; auto. 
  * destruct IHc_eq1. destruct IHc_eq2. split ; intros ; auto.
Qed.


Fixpoint monoms (c : Contract) : list Trace :=
match c with
| Success => [[]]
| Failure => []
| Event e => [[e]]
| c0 _+_ c1 => (monoms c0) ++ (monoms c1)
| c0 _;_ c1 => flat_map (fun m0 => map (fun m1 => m0 ++ m1) (monoms c1)) (monoms c0)
end.

Lemma monoms_seq : forall (s0 s1 s : Trace)(c0 c1 : Contract), In s0 (monoms c0) -> In s1 (monoms c1) -> In (s0++s1) (monoms (c0 _;_ c1)).
Proof.
intros. simpl. apply in_flat_map. exists s0. split. { assumption. }
apply in_map. assumption.
Qed. 



Definition sorted_nodup_monoms_of_contract (c : Contract) : list Trace := sort ((nodup (list_eq_dec eq_event_dec)) (monoms c)).

Definition contract_of_monom (s : Trace) := fold_left (fun acc e => acc _;_ (Event e)) s Success.


Definition contract_of_monoms (l : list Trace) := fold_left (fun acc s => acc _+_ (contract_of_monom s)) l Failure.
Compute (contract_of_monoms (monoms (Transfer _._  Notify _._ Success _+_ Notify _._ Success))).

Definition norm_contract (c : Contract) : Contract := contract_of_monoms (sorted_nodup_monoms_of_contract c).

(*Ltac unfold_norm_contract := unfold norm_contract, contract_of_monoms, sorted_nodup_monoms_of_contract.*)


(*  Lemma incl_Forall_in_iff l l' :*)

Lemma comp_equiv_destruct : forall (c0 c1: Contract),(forall s : Trace, s ==~ c0 <-> s ==~ c1) ->
(forall s : Trace, s ==~ c0 -> s ==~ c1) /\ (forall s : Trace, s ==~ c1 -> s ==~ c0).
Proof.
intros. split ; intros; specialize H with s; destruct H; auto.
Qed.

Lemma norm_eq : forall (c: Contract), norm_contract c =R= c.
Proof. Admitted.

Lemma norm_match : forall (c: Contract), (forall s : Trace, s ==~ (norm_contract c) <-> s ==~ c).
Proof.
intro. apply c_eq_soundness. apply norm_eq.
Qed.
Check nodup.
Lemma in_sorted_no_dump_monoms : forall (s : Trace)(c : Contract), In s (monoms c) -> 
In s (sorted_nodup_monoms_of_contract c).
Proof.
intros. unfold sorted_nodup_monoms_of_contract. apply <- (nodup_In ((list_eq_dec eq_event_dec))) in H.
remember (nodup (list_eq_dec eq_event_dec) (monoms c)) as l.
apply Permutation_in with (l:=l). { apply Permuted_sort. } { assumption. }
Qed.  


Lemma match_member : forall (s : Trace)(c : Contract), s ==~ c <-> In s (monoms c). 
Proof.
split.
- intros. induction H ; try (simpl ; now left).
  * apply monoms_seq; auto.
  * simpl. apply in_or_app. now left.
  * simpl. apply in_or_app. now right.
- intros. apply (norm_match c s). unfold norm_contract. 
  apply in_sorted_no_dump_monoms in H. unfold contract_of_monoms.
  rewrite <- fold_left_rev_right.
  
    Admitted.


Lemma comp_incl : forall (c0 c1 : Contract), (forall (s : Trace), s ==~ c0 -> s ==~ c1) -> 
incl (monoms c0) (monoms c1).
Proof.
intros. unfold incl. intros. apply match_member. apply H. apply match_member. assumption.
Qed.


Lemma sorted_permutation : forall (l1 l2 : list Trace), StronglySorted TraceOrder.leb_prop l1 -> StronglySorted TraceOrder.leb_prop l2 -> 
Permutation l1 l2 -> l1 = l2.
Proof.
induction l1.
- intros. apply Permutation_nil in H1. now rewrite H1.
- intros. destruct l2.
  * apply Permutation_sym in H1. apply Permutation_nil in H1. discriminate.
  * inversion H. inversion H0. subst.
    apply Permutation_in with (x:=a) in H1 as H10. 2: { now constructor. }
    inversion H10.  { rewrite <- H2 in *. apply Permutation_cons_inv in H1. f_equal. auto. }
    pose proof Permutation_sym H1 as H1_sym.
    apply Permutation_in with (x:=t) in H1_sym as H11. 2: {  now constructor. }
    inversion H11.  { rewrite <- H3 in *. apply Permutation_cons_inv in H1_sym. f_equal. apply Permutation_sym in H1_sym. auto. }
    destruct (TraceOrder.leb_total a t). 
    ** rewrite Forall_forall in H9. specialize H9 with a.
       apply H9 in H2. unfold TraceOrder.leb_prop in H2.
       destruct (TraceOrder.leb t a) eqn:Heqn. 2: { discriminate. }
       pose proof TraceOrder.leb_anti_sym a t. unfold TraceOrder.leb_prop in H7.
       rewrite Heqn in H7. rewrite H6 in H7. rewrite H7 in * ; auto. f_equal.
       apply Permutation_cons_inv in H1. auto.
    ** rewrite Forall_forall in H5. specialize H5 with t.
       apply H5 in H3. unfold TraceOrder.leb_prop in H3.
       destruct (TraceOrder.leb a t) eqn:Heqn.  2:{ discriminate. }
       pose proof TraceOrder.leb_anti_sym t a. unfold TraceOrder.leb_prop in H7.
       rewrite Heqn in H7. rewrite H6 in H7. rewrite H7 in * ; auto. f_equal.
       apply Permutation_cons_inv in H1. auto.
Qed.


Lemma comp_equiv_i_norm_eq : forall (c0 c1 : Contract), (forall s : Trace, s ==~ c0 <-> s ==~ c1) -> 
forall (s' : Trace), In s' (monoms c0) <-> In s' (monoms c1).
Proof.
intros. apply comp_equiv_destruct with (c0:=c0)(c1:=c1) in H as [H1 H2].
apply comp_incl in H1. apply comp_incl in H2. split ; auto.
Qed.




Search (Permutation _ _ -> _ ).
Lemma comp_equiv_i_perm_monoms : forall (c0 c1 : Contract), (forall s : Trace, s ==~ c0 <-> s ==~ c1) -> 
 Permutation (nodup (list_eq_dec eq_event_dec) (monoms c0)) 
             (nodup (list_eq_dec eq_event_dec) (monoms c1)).
Proof.
intros. apply NoDup_Permutation ; try apply NoDup_nodup.
intros. rewrite nodup_In. rewrite nodup_In. apply comp_equiv_i_norm_eq. assumption. 
Qed.


Lemma comp_equiv_i_eq_sorted_monoms : forall (c0 c1 : Contract), (forall s : Trace, s ==~ c0 <-> s ==~ c1) -> 
 sorted_nodup_monoms_of_contract c0 = sorted_nodup_monoms_of_contract c1.
Proof.
intros. unfold sorted_nodup_monoms_of_contract. apply sorted_permutation.
- apply (StronglySorted_sort ((nodup (list_eq_dec eq_event_dec) (monoms c0)) )TraceOrder.leb_trans).
- apply (StronglySorted_sort ((nodup (list_eq_dec eq_event_dec) (monoms c1)) )TraceOrder.leb_trans).
- repeat rewrite <- Permuted_sort. apply comp_equiv_i_perm_monoms. assumption.
Qed.







Lemma c_eq_completeness : forall (c0 c1 : Contract), (forall s : Trace, s ==~ c0 <-> s ==~ c1) -> c0 =R= c1.
Proof.
intros. rewrite <- norm_eq. rewrite <- (norm_eq c1). unfold norm_contract. f_equal. 
apply comp_equiv_i_eq_sorted_monoms in H. rewrite H. apply c_refl.
Qed.
