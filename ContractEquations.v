Require Import CSL.Contract.
Require Import CSL.Order.
Require Import CSL.PlusFold.
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
  | c_seq_failure_l c : Failure _;_ c =R= Failure    (*EXTRA AXIOM*)
  | c_seq_failure_r c :  c _;_ Failure =R= Failure 
  | c_distr_l c0 c1 c2 : c0 _;_ (c1 _+_ c2) =R= (c0 _;_ c1) _+_ (c0 _;_ c2)
  | c_distr_r c0 c1 c2 : (c0 _+_ c1) _;_ c2 =R= (c0 _;_ c2) _+_ (c1 _;_ c2)
  | c_refl c : c =R= c
  | c_sym c0 c1 (H: c0 =R= c1) : c1 =R= c0
  | c_trans c0 c1 c2 (H1 : c0 =R= c1) (H2 : c1 =R= c2) : c0 =R= c2
  | c_plus_morph c0 c0' c1 c1' (H1 : c0 =R= c0') (H2 : c1 =R= c1') : c0 _+_ c1 =R= c0' _+_ c1'
  | c_seq_morph c0 c0' c1 c1' (H1 : c0 =R= c0') (H2 : c1 =R= c1') : c0 _;_ c1 =R= c0' _;_ c1'
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


Lemma c_eq_soundness : forall (c0 c1 : Contract), c0 =R= c1 -> (forall s : Trace, s ==~ c0 <-> s ==~ c1).
Proof.
- intros c0 c1 H. induction H ; intros.
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
  * split ; intros ; inversion H. inversion H3.
  * split ; intros ; inversion H. inversion H4.
  * split ; intros ; inversion H.
    ** inversion H4 ; auto.
    ** inversion H2 ; auto.
    ** inversion H1 ; auto.
  * split ; intros ; inversion H.
    ** inversion H3 ; auto.
    ** inversion H2 ; auto.
    ** inversion H1 ; auto.
  * split ; intros ; assumption.
  * specialize IHc_eq with s. destruct IHc_eq. split; intros ; auto. 
  * specialize IHc_eq1 with s. specialize IHc_eq2 with s. destruct IHc_eq1. destruct IHc_eq2. split ; intros ; auto.
  * specialize IHc_eq1 with s. specialize IHc_eq2 with s. destruct IHc_eq1. destruct IHc_eq2. split ;
    intros ; inversion H5 ; auto.
  * split.
    ** intros. inversion H1. constructor ; auto. 
      *** apply IHc_eq1. assumption.
      *** apply IHc_eq2. assumption.
    ** intros. inversion H1. constructor ; auto. 
      *** apply IHc_eq1. assumption.
      *** apply IHc_eq2. assumption.
Qed.

(*Functions defining normalization*)

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

Definition sorted_nodup_monoms (c : Contract) : list Trace := sort ((nodup (list_eq_dec eq_event_dec)) (monoms c)).

Definition contract_of_monom (s : Trace) := seq_fold (map Event s).

Definition contract_of_monoms (l : list Trace) := plus_fold (map contract_of_monom l).

Definition norm (c : Contract) : Contract := contract_of_monoms (sorted_nodup_monoms c).

(*Helper lemma for monoms_ceq*)
Lemma monoms_ceq_plus : forall (c0 c1: Contract), contract_of_monoms (monoms (c0 _+_ c1)) =R= 
(contract_of_monoms (monoms c0)) _+_ (contract_of_monoms (monoms c1)).
Proof. 
intros. unfold contract_of_monoms. simpl. rewrite map_app.
assert (plus_fold_app_eq : plus_fold (map contract_of_monom (monoms c0) ++
   map contract_of_monom (monoms c1)) =R= plus_fold (map contract_of_monom (monoms c0)) _+_
                                          plus_fold (map contract_of_monom (monoms c1))).
  { intros. induction (map contract_of_monom (monoms c0)).
    - simpl. rewrite c_plus_comm. auto.
    - simpl. rewrite c_plus_assoc. apply c_plus_morph ; auto. 
  }
rewrite plus_fold_app_eq. apply c_plus_morph ; apply c_refl. 
Qed.

Ltac unfold_defs := unfold contract_of_monoms, contract_of_monom.

Lemma contract_of_monom_app : forall (l1 l2 : Trace), contract_of_monom l1 _;_ contract_of_monom l2 =R= contract_of_monom (l1++l2).
Proof.
unfold contract_of_monom. induction l1.
- intros. simpl. rewrite c_seq_neut_l. auto.
- intros. simpl. rewrite <- IHl1. auto.
Qed.

Lemma plus_fold_app_seq : forall (l1: Trace)(l2 : list Trace), (contract_of_monom l1 _;_ 
              plus_fold (map contract_of_monom l2)) =R=
              plus_fold (map contract_of_monom (map (fun m1 : list EventType => l1 ++ m1) l2)).
Proof.
induction l2.
- intros. simpl. auto.
- intros. simpl. rewrite c_distr_l. rewrite contract_of_monom_app. auto.
Qed.

Lemma plus_fold_app_plus : forall (l1 l2 : list Contract), plus_fold (l1 ++ l2) =R= plus_fold l1 _+_ plus_fold l2.
Proof.
induction l1.
- intros. simpl. rewrite c_plus_comm. auto.
- intros. simpl. rewrite IHl1. auto.
Qed.


(*Helper lemma for monoms_ceq*)
Lemma monoms_ceq_seq : forall (c0 c1 : Contract), contract_of_monoms (monoms (c0 _;_ c1)) =R=
 contract_of_monoms (monoms c0) _;_ contract_of_monoms (monoms c1).
Proof.
intros. unfold contract_of_monoms. simpl.
induction (monoms c0).
- simpl. auto.
- simpl. rewrite c_distr_r. rewrite <- IHl.
  rewrite plus_fold_app_seq. rewrite map_app. simpl. 
  rewrite plus_fold_app_plus. apply c_refl.
Qed.



(*Normalization without removing duplicates and sorting, can be derived*)
Lemma monoms_ceq : forall (c : Contract), contract_of_monoms (monoms c) =R= c.
Proof.
induction c.
- unfold_defs. simpl. auto.
- unfold_defs. simpl. auto.
- unfold_defs. simpl. rewrite c_plus_neut. auto.
- rewrite monoms_ceq_plus;auto.
- assert (HA : c1 _;_ c2 =R= (contract_of_monoms (monoms c1)) _;_ (contract_of_monoms (monoms c2))) ; auto.
  rewrite HA at 2. rewrite <- monoms_ceq_seq. apply c_refl.
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


Lemma permute_monoms: forall (l1 l2 : list Trace), Permutation l1 l2 -> contract_of_monoms l1 =R= contract_of_monoms l2.
Proof. 
induction l1.
- intros. simpl. unfold contract_of_monoms. apply Permutation_nil in H. now rewrite H.
- intros. simpl. apply Permutation_in with (x:=a) in H as H_in; try apply in_eq.
  apply in_split in H_in as [l2' [l2'' P]]. rewrite P in *. rewrite <- Permutation_middle in H. 
  unfold contract_of_monoms. simpl. rewrite (IHl1 (l2' ++ l2'')). 2: { apply Permutation_cons_inv with(a:=a) . assumption. }
  unfold contract_of_monoms. repeat rewrite map_app. repeat rewrite plus_fold_app_plus. 
  simpl. rewrite c_plus_comm. rewrite (c_plus_comm (contract_of_monom a)). rewrite <- c_plus_assoc. apply c_refl.
Qed.

Lemma nodup_monoms: forall (l : list Trace), contract_of_monoms l =R= contract_of_monoms (nodup (list_eq_dec eq_event_dec) l).
Proof.
induction l.
- simpl. reflexivity.
- simpl. destruct (in_dec (list_eq_dec eq_event_dec) a l).
  * unfold contract_of_monoms in *. simpl. rewrite <- IHl.
    apply in_split in i as [l1 [l2 P]].
    assert (HA: Permutation (l1 ++ a :: l2) (a :: l1 ++ l2)).
    {  apply Permutation_sym. apply Permutation_middle. }
    rewrite P.
    rewrite (permute_monoms HA).
    unfold contract_of_monoms. simpl. 
    rewrite <- c_plus_assoc. rewrite c_plus_idemp. apply c_refl.
  * unfold contract_of_monoms.
    simpl.  rewrite <- IHl. reflexivity.
Qed.


(*Monomials take contain each other, are derivable as contracts *)
Lemma incl_monoms : forall (l1 l2 : list Trace), incl l1 l2 -> incl l2 l1-> contract_of_monoms l1 =R= contract_of_monoms l2.
Proof. 
intros.
rewrite <- nodup_incl with(decA:=(list_eq_dec eq_event_dec)) in H.
rewrite <- nodup_incl with(decA:=(list_eq_dec eq_event_dec)) in H0.
assert (HA:  (forall (s : Trace), In s (nodup (list_eq_dec eq_event_dec) l1) <-> 
                            In s (nodup (list_eq_dec eq_event_dec) l2))).
  {  intros. split. 
    -  intros. unfold incl in H. apply H. apply nodup_In with (decA:=(list_eq_dec eq_event_dec) ). assumption.
    -  intros. unfold incl in H0. apply H0. apply nodup_In with (decA:=(list_eq_dec eq_event_dec) ). assumption.  }
assert (HA_P: Permutation (nodup (list_eq_dec eq_event_dec) l1) (nodup (list_eq_dec eq_event_dec) l2)).
  {  apply NoDup_Permutation; try apply NoDup_nodup. assumption. }
assert (HA_S: sort (nodup (list_eq_dec eq_event_dec) l1) = sort (nodup (list_eq_dec eq_event_dec) l2)).
  {  apply sorted_permutation; try( apply StronglySorted_sort; apply TraceOrder.leb_trans).
     repeat rewrite <- Permuted_sort. assumption. }
rewrite nodup_monoms. rewrite (nodup_monoms l2).
Check Permuted_sort (nodup (list_eq_dec eq_event_dec) l1).
rewrite (permute_monoms ( Permuted_sort (nodup (list_eq_dec eq_event_dec) l1))).
rewrite (permute_monoms ( Permuted_sort (nodup (list_eq_dec eq_event_dec) l2))).
rewrite HA_S. apply c_refl.
Qed.

(*Main normalization theorem *)
Theorem norm_c_eq : forall (c : Contract), norm c =R= c.
Proof.
intros. unfold norm, sorted_nodup_monoms. 
rewrite incl_monoms with (l1:=(sort (nodup (list_eq_dec eq_event_dec) (monoms c))))
                         (l2:=(nodup (list_eq_dec eq_event_dec) (monoms c))).
- rewrite incl_monoms with (l1:=((nodup (list_eq_dec eq_event_dec) (monoms c))))
                         (l2:=( (monoms c))).
  * apply monoms_ceq ;
    try (apply nodup_incl with (decA:=(list_eq_dec eq_event_dec) ) ;  apply incl_refl).
  * (apply nodup_incl with (decA:=(list_eq_dec eq_event_dec) ) ;  apply incl_refl).
  * (apply nodup_incl with (decA:=(list_eq_dec eq_event_dec) ) ;  apply incl_refl).
- assert (HA: Permutation (nodup (list_eq_dec eq_event_dec) (monoms c))
                                (sort (nodup (list_eq_dec eq_event_dec) (monoms c)))).
  { apply Permuted_sort.  }
  apply Permutation_sym in HA. unfold incl. intros. apply Permutation_in with(x:=a) in HA; assumption.
- assert (HA: Permutation (nodup (list_eq_dec eq_event_dec) (monoms c))
                                (sort (nodup (list_eq_dec eq_event_dec) (monoms c)))).
  { apply Permuted_sort.  }
  unfold incl. intros. apply Permutation_in with(x:=a) in HA; assumption.
Qed.




Lemma comp_equiv_destruct : forall (c0 c1: Contract),(forall s : Trace, s ==~ c0 <-> s ==~ c1) ->
(forall s : Trace, s ==~ c0 -> s ==~ c1) /\ (forall s : Trace, s ==~ c1 -> s ==~ c0).
Proof.
intros. split ; intros; specialize H with s; destruct H; auto.
Qed.


(********************************************************************)
(*A Semantic match implies that contracts share the same monoms, this section shows this*)


Lemma in_sorted_no_dump_monoms : forall (s : Trace)(c : Contract), In s (monoms c) -> 
In s (sorted_nodup_monoms c).
Proof.
intros. unfold sorted_nodup_monoms. apply <- (nodup_In ((list_eq_dec eq_event_dec))) in H.
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
- intros. apply (c_eq_soundness (norm_c_eq c)). unfold norm. 
  unfold contract_of_monoms.
  apply in_plus_fold. exists (contract_of_monom s). split.
  * apply in_map. apply in_sorted_no_dump_monoms. assumption.
  * unfold contract_of_monom. apply seq_fold_map.
Qed.

Lemma comp_incl : forall (c0 c1 : Contract), (forall (s : Trace), s ==~ c0 -> s ==~ c1) -> 
incl (monoms c0) (monoms c1).
Proof.
intros. unfold incl. intros. apply match_member. apply H. apply match_member. assumption.
Qed.

(*Main lemma of this section*)
Lemma comp_equiv_i_norm_eq : forall (c0 c1 : Contract), (forall s : Trace, s ==~ c0 <-> s ==~ c1) -> 
forall (s' : Trace), In s' (monoms c0) <-> In s' (monoms c1).
Proof.
intros. apply comp_equiv_destruct with (c0:=c0)(c1:=c1) in H as [H1 H2].
apply comp_incl in H1. apply comp_incl in H2. split ; auto.
Qed.


(*****************************************************************************)


(*Semantic match -> duplicate-free monomials are permutations*)
Lemma comp_equiv_i_perm_monoms : forall (c0 c1 : Contract), (forall s : Trace, s ==~ c0 <-> s ==~ c1) ->
 Permutation (nodup (list_eq_dec eq_event_dec) (monoms c0))
             (nodup (list_eq_dec eq_event_dec) (monoms c1)).
Proof.
intros. apply NoDup_Permutation ; try apply NoDup_nodup.
intros. rewrite nodup_In. rewrite nodup_In. apply comp_equiv_i_norm_eq. assumption.
 Qed.

(*Semantic match -> sorted duplicate-free monomials are equal*)
Lemma comp_equiv_i_eq_sorted_monoms : forall (c0 c1 : Contract), (forall s : Trace, s ==~ c0 <-> s ==~ c1) ->
 sorted_nodup_monoms c0 = sorted_nodup_monoms c1.
Proof.
intros. unfold sorted_nodup_monoms. apply sorted_permutation.
- apply (StronglySorted_sort ((nodup (list_eq_dec eq_event_dec) (monoms c0)) )TraceOrder.leb_trans).
- apply (StronglySorted_sort ((nodup (list_eq_dec eq_event_dec) (monoms c1)) )TraceOrder.leb_trans).
- repeat rewrite <- Permuted_sort. apply comp_equiv_i_perm_monoms. assumption.
Qed.

(*Completeness: Semantic match -> Derivable in =R=*)
Lemma c_eq_completeness : forall (c0 c1 : Contract), (forall s : Trace, s ==~ c0 <-> s ==~ c1) -> c0 =R= c1.
Proof.
intros. rewrite <- norm_c_eq. rewrite <- (norm_c_eq c1). unfold norm. 
apply comp_equiv_i_eq_sorted_monoms in H. rewrite H. apply c_refl.
Qed.

