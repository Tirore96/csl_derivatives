Require Import CSL.IterativeContract.
Require Import Setoid.
Require Import Init.Tauto btauto.Btauto.
Require Import Bool.Bool  Bool.Sumbool.
Require Import Lists.List.
Import ListNotations.
Require Import Bool.Bool.
Require Import micromega.Lia.
From Equations Require Import Equations.
(*******************************************************************************************************)
Set Implicit Arguments.

Definition contract_relation := Contract -> Contract -> Prop.

Notation "c0 ==~== c1" := (forall s, s ==~ c0 <-> s ==~ c1) (at level 73, no associativity).

Definition non_empty_relation (R : contract_relation) := exists c0 c1, R c0 c1.

Definition bisimulation (R: contract_relation) := non_empty_relation R /\ forall c0 c1, R c0 c1 -> nu c0 = nu c1 /\ forall e, R (c0/e) (c1/e).

(*c0 and c1 are in a bisimilarity written as c0 ~ c1*)
Notation "c0 ~ c1" := (exists R, bisimulation R /\ R c0 c1)(at level 73, no associativity).

(*
Lemma bi_union : forall R0 R1, bisimulation R0 -> bisimulation R1 -> bisimulation (fun x y => R0 x y \/ R1 x y).
Proof.
intros. destruct H, H0. destruct H0 as [c0 [c1 P]]. split.
- exists c0. exists c1. right. auto.
- intros. destruct H0.
  * apply H1 in H0 as [H0 H0']. split ; auto.
  * apply H2 in H0 as [H0 H0']. split ; auto.
Qed.*)

Lemma simpl_bisim_nu : forall (c0 c1 : Contract), c0 ~ c1 -> nu c0 = nu c1.
Proof. 
intros. destruct H. destruct H. unfold bisimulation in H.
destruct H. specialize H1 with c0 c1.
apply H1 in H0. destruct H0. assumption. 
Qed.

Lemma simpl_bisim_derive : forall (c0 c1 : Contract)(e : EventType), 
                           c0 ~ c1 -> c0/e ~ c1/e.
Proof. intros.  destruct H. exists x. destruct H. split;auto.
       destruct H. apply H1 in H0. destruct H0. auto.
Qed.

Hint Resolve simpl_bisim_nu  simpl_bisim_derive : bisimB.

CoInductive Bisimilarity : Contract -> Contract -> Prop :=
 CBisimilarity c0 c1 (H0: forall e, Bisimilarity (c0/e) (c1/e)) (H1: nu c0 = nu c1) : Bisimilarity c0 c1.

(*Bisimilarity predicate over contract relations*)
Definition bisimilarity (R : contract_relation) := forall c0 c1, R c0 c1 <-> Bisimilarity c0 c1.
Global Transparent bisimilarity.

Lemma exists_bisimulation_i_Bisimilarity : forall c0 c1, c0 ~ c1 -> Bisimilarity c0 c1.
Proof.
cofix exists_bisimulation_i_Bisimilarity.
intros. constructor.
- intros. apply exists_bisimulation_i_Bisimilarity. auto with bisimB.
- auto with bisimB.
Qed.

Lemma Bisimilarity_is_bisimulation : bisimulation Bisimilarity.
Proof.
split;intros.
- exists Failure. exists Failure. cofix Bisimilarity_is_bisimulation.
  apply CBisimilarity;intros;simpl;auto.
- destruct H; split;auto.
Qed.

Lemma Bisimilarity_i_exists_bisimulation : forall c0 c1, Bisimilarity c0 c1 -> c0 ~ c1.
Proof.
intros. exists Bisimilarity. split;auto using Bisimilarity_is_bisimulation.
Qed. 

(*Sanity check*)
Theorem exists_bisimulation_is_bisimilarity : bisimilarity (fun c0 c1 => c0 ~ c1). 
Proof.
split; auto using exists_bisimulation_i_Bisimilarity,Bisimilarity_i_exists_bisimulation.
Qed.


Lemma bisimilarity_non_empty : forall (R : contract_relation), bisimilarity R -> non_empty_relation R.
Proof.
intros. destruct H with Failure Failure.
assert (HA: Bisimilarity Failure Failure).
{ cofix bisimilarity_non_empty. constructor. intros. now simpl. auto.  }
exists Failure. exists Failure. auto.
Qed.
 
Lemma bisimilarity_i_bisimulation : forall (R : contract_relation), bisimilarity R -> bisimulation R.
Proof.
intros. unfold bisimilarity in H. split;auto using bisimilarity_non_empty.
intros. pose proof H. destruct H with c0 c1. apply H1 in H0.
destruct H0. split;auto. intros. rewrite H1. auto.
Qed.


Lemma matches_eq_is_bisimulation : bisimulation (fun c0 c1 => c0 ==~== c1).
Proof.
split.
- exists Failure. exists Failure. reflexivity.
- split.
  * apply eq_true_iff_eq. now repeat rewrite Matches_Comp_nil.
  * intros. now repeat rewrite <- derive_spec_comp. 
Qed.

(*c0 ==~== c1 is a bisimilarity*)
Theorem matches_eq_is_bisimilarity : bisimilarity (fun c0 c1 => forall s, s ==~ c0 <-> s ==~ c1).
Proof.
split. 
- generalize dependent c1. generalize dependent c0. cofix matches_eq_is_bisimilarity.
  intros. constructor.
  * intros. apply matches_eq_is_bisimilarity. setoid_rewrite <- derive_spec_comp. auto.
  * apply eq_true_iff_eq. repeat rewrite Matches_Comp_nil. auto.
- intro.
  repeat setoid_rewrite matches_Matches. intro. generalize dependent c1.
  generalize dependent c0. induction s;intros.
  * inversion H. repeat rewrite <- matches_Matches. repeat rewrite <- Matches_Comp_nil.
    now rewrite H1.
  * repeat rewrite derive_spec_comp. inversion H. auto.
Qed.


Reserved Notation "c0 =ACI= c1" (at level 63).
Inductive c_eq_aci : Contract -> Contract -> Prop :=
    | cc_plus_assoc c0 c1 c2 : (c0 _+_ c1) _+_ c2 =ACI= c0 _+_ (c1 _+_ c2) (*ACI axioms*)
    | cc_plus_comm c0 c1: c0 _+_ c1 =ACI= c1 _+_ c0
    | cc_plus_idemp c : c _+_ c =ACI= c 
    | cc_trans c0 c1 c2 (H1 : c0 =ACI= c1) (H2 : c1 =ACI= c2) : c0 =ACI= c2 (*transitivity*)
    | cc_ctx_plus c0 c0' c1 c1' (H1 : c0 =ACI= c0') (H2 : c1 =ACI= c1') : c0 _+_ c1 =ACI= c0' _+_ c1' (*ctx rules*)
    | cc_ctx_seq c0 c0' c1 c1' (H1 : c0 =ACI= c0') (H2 : c1 =ACI= c1') : c0 _;_ c1 =ACI= c0' _;_ c1'
    | cc_refl c : c =ACI= c
    | cc_sym c0 c1 (H : c0 =ACI= c1) : c1 =ACI= c0
    where "c0 =ACI= c1" := (c_eq_aci c0 c1).
Hint Constructors c_eq_aci : core.

Add Parametric Relation : Contract c_eq_aci
  reflexivity proved by cc_refl
  symmetry proved by cc_sym
  transitivity proved by cc_trans
  as Contract_setoid.

Add Parametric Morphism : CPlus with
signature c_eq_aci ==> c_eq_aci ==> c_eq_aci as c_eq_aci_plus_morphism.
Proof.
  intros. auto.
Qed.

Add Parametric Morphism : CSeq with
signature c_eq_aci ==> c_eq_aci ==> c_eq_aci as c_eq_aci_seq_morphism.
Proof.
  intros. auto.
Qed.


Lemma c_eq_aci_nu : forall c0 c1, c0 =ACI= c1 -> nu c0 = nu c1.
Proof.
intros. induction H;simpl; try btauto.
- rewrite IHc_eq_aci1. auto.
- rewrite IHc_eq_aci1. now rewrite IHc_eq_aci2. 
- rewrite IHc_eq_aci1. now rewrite IHc_eq_aci2.
- intuition. 
Qed. 

Ltac nu_destruct :=
  repeat match goal with
         | [ |- context[if nu ?c then _ else _] ] => destruct (nu c) eqn:?Heqn
         end.

Lemma o_aci : forall c0 c1, c0 =ACI= c1 -> o c0 = o c1.
Proof.
intros. apply c_eq_aci_nu in H. o_destruct; unfold o; now rewrite H.
Qed. 


Lemma c_eq_aci_derive : forall c0 c1, c0 =ACI= c1 -> (forall e, c0/e =ACI= c1/e).
Proof.
intros. induction H; try solve [simpl ; eauto].
simpl. apply cc_ctx_plus;auto. apply cc_ctx_seq;auto. nu_destruct;auto.
apply o_aci in H. now rewrite H.
Qed.


Reserved Notation "c0 =R= c1" (at level 63).
CoInductive c_eq : Contract -> Contract -> Prop :=
  | c_aci c0 c1 (H: c0 =ACI= c1) : c0 =R= c1
  | c_fix c0 c1 (H0: forall e, c0/e =R= c1/e) (H1 : nu c0 = nu c1) : c0 =R= c1
    where "c0 =R= c1" := (c_eq c0 c1).

Lemma c_eq_nu : forall c0 c1, c0 =R= c1 -> nu c0 = nu c1.
Proof.
intros. inversion H;auto using c_eq_aci_nu.
Qed.

Lemma c_eq_derive : forall c0 c1, c0 =R= c1 -> (forall e, c0/e =R= c1/e).
Proof.
cofix H.
intros. inversion H0. 
- constructor. auto using c_eq_aci_derive. 
- apply H1.
Qed.


Lemma c_eq_is_bisimilarity : bisimilarity c_eq.
Proof. 
split; generalize dependent c1; generalize dependent c0.
- cofix c_eq_is_bisimilarity. intros.
  constructor; auto using c_eq_nu, c_eq_derive.
- cofix H. intros. destruct H0. apply c_fix.
  * intros. auto.
  * auto.
Qed.


Theorem c_eq_soundness : forall c0 c1, c0 =R= c1 -> c0 ==~== c1.
Proof.
intros. pose proof c_eq_is_bisimilarity. pose proof matches_eq_is_bisimilarity.
unfold bisimilarity in *. specialize H1 with c0 c1.
apply <- H1. now apply H0.
Qed.

Theorem c_eq_completeness : forall c0 c1, c0 ==~== c1 -> c0 =R= c1.
Proof.
intros. pose proof c_eq_is_bisimilarity. pose proof matches_eq_is_bisimilarity.
unfold bisimilarity in *. rewrite H0. now rewrite <- H1.
Qed.

Lemma c_eq_refl : forall c, c =R= c.
Proof.
intros. apply c_eq_completeness. split;auto.
Qed.

Hint Immediate c_eq_refl : core.

Lemma c_eq_sym : forall c0 c1, c0 =R= c1 -> c1 =R= c0.
Proof.
intros. apply c_eq_completeness. intros. apply c_eq_soundness with (s:=s) in H.
now symmetry in H.
Qed.

Lemma c_eq_trans : forall c0 c1 c2, c0 =R= c1 -> c1 =R= c2 -> c0 =R= c2.
Proof.
intros. apply c_eq_completeness. intros. apply c_eq_soundness with (s:=s ) in H.
apply c_eq_soundness with (s:=s ) in H0. rewrite H. now rewrite H0.
Qed.

Add Parametric Relation : Contract c_eq
  reflexivity proved by c_eq_refl
  symmetry proved by c_eq_sym
  transitivity proved by c_eq_trans
  as Contract_c_eq_setoid.

Add Parametric Morphism : CPlus with
signature c_eq ==> c_eq ==> c_eq as c_eq_plus_morphism.
Proof.
  intros. apply c_eq_completeness. intros. apply c_eq_soundness with (s:=s) in H. 
   apply c_eq_soundness with (s:=s) in H0. split;intros.
  - inversion H1;auto. apply MPlusL. now rewrite <- H. apply MPlusR. now rewrite <- H0.
  - inversion H1;auto. apply MPlusL. now rewrite H. apply MPlusR. now rewrite H0.
Qed.

Add Parametric Morphism : CSeq with
signature c_eq ==> c_eq ==> c_eq as c_eq_seq_morphism.
Proof.
  intros. apply c_eq_completeness. intros. split;intros. inversion H1. apply c_eq_soundness with (s:=s1) in H as H'.
  constructor. now rewrite <- H'. apply c_eq_soundness with (s:=s2) in H0 as H''. now rewrite <- H''.
  inversion H1. apply c_eq_soundness with (s:=s1) in H as H'. 
    constructor. now rewrite H'. apply c_eq_soundness with (s:=s2) in H0 as H''. now rewrite H''.
Qed.



(*********************************************Decision procedure *****************************************)
Section member.
  Variable A : Set.
  Hypothesis equals : A -> A -> bool.
  
  Fixpoint member (c : A) (l : list A) :=
  match l with
  | [] => false
  | a::l' => equals a c || member c l' 
  end.
End member.

Definition inclb (l0 l1 : list Contract) :bool := 
 forallb (fun c0 => existsb (fun c1 => if Contract_eq_dec c0 c1 then true else false) l1) l0.

Lemma inclb_iff : forall (l0 l1 : list Contract), inclb l0 l1 = true <-> incl l0 l1.
Proof. unfold inclb. unfold incl. split. 
- intros. rewrite forallb_forall in H. apply H in H0. rewrite existsb_exists in H0. destruct H0 as [x [P0 P1]].
destruct (Contract_eq_dec a x).
  * subst. assumption.
  * discriminate.
- intros. rewrite forallb_forall. intros. apply H in H0. rewrite existsb_exists. exists x. split.
  * assumption.
  * destruct (Contract_eq_dec x x).
    ** reflexivity.
    ** contradiction. 
Qed.


Lemma incl_reflect : forall (l0 l1 : list Contract), reflect (incl l0 l1) (inclb l0 l1).
Proof. 
intros. destruct (inclb l0 l1) eqn:Heqn.
- constructor. rewrite inclb_iff in Heqn. assumption.
- constructor. intro H. rewrite <- inclb_iff in H. rewrite Heqn in H. discriminate.
Qed.

(*
Fixpoint flatten_contract (c : Contract) : list Contract :=
match c with
| c0 _+_ c1 => (flatten_contract c0) ++ (flatten_contract c1)
| _ => [c]
end.

Definition aci_eq (c0 c1 : Contract) : bool :=
 let c0_l := flatten_contract c0 in
 let c1_l := flatten_contract c1 in
 (inclb c0_l c1_l) && (inclb c1_l c0_l) .

Definition aci_p_eq (p0 p1: (Contract * Contract)) : bool :=
 let (c0,c0') := p0 in
 let (c1,c1') := p1 in
 aci_eq c0 c1 && aci_eq c0' c1'.*)

(*
Fixpoint trace_derive (c: Contract) (s : Trace) :=
match s with
| [] => c
| e::s' => trace_derive (c/e) s'
end.*)

Equations trace_derive (c : Contract) (s : Trace) : Contract :=
trace_derive c [] := c;
trace_derive c (e::s') := trace_derive (c/e) s'.
Global Transparent trace_derive.
Definition contains_all_derivatives_of c (l : list Contract) := forall (s : Trace), In (trace_derive c s) l.



Inductive Trace_Derive : Contract -> Trace -> Contract -> Prop :=
| Trace_Derive_Nil c : Trace_Derive c [] c
| Trace_Derive_Cons c s c' e (H: Trace_Derive (c/e) s c') : Trace_Derive c (e::s) c'. (*rule motivated by constructor being analgous to cons on lists*)
Hint Constructors Trace_Derive : core.

(*
Inductive Trace_Derive : Contract -> Trace -> Contract -> Prop :=
| Trace_Derive_Nil c : Trace_Derive c [] c
| Trace_Derive_Cons c s c' e (H: Trace_Derive c s c') : Trace_Derive c (s++[e]) (c'/e).
Hint Constructors Trace_Derive : core.*)



Lemma derive_trace_derive : forall (c : Contract)(s : Trace)(e :EventType), trace_derive c (s++[e]) = (trace_derive c s) / e.
Proof.
intros. generalize dependent c. induction s;simpl;auto.
Qed.

Lemma length_removelast : forall (A: Type)(e:A)(l:list A), length (removelast (e :: l)) = length l.
Proof.
intros. simpl. generalize dependent e. induction l;intros;auto. simpl. f_equal. now simpl.
Qed.
(*
Lemma removelast_cons :  forall (A: Type)(e:A)(l:list A), removelast (e::l) = e::(removelast l).
Proof.
intros. induction l. simpl. (removelast (e :: l)) = length l.
*)

Lemma app_nil : forall (A:Type)(l:list A)(e: A), l ++ [e] = [] -> False.
Proof.
intros. destruct l; discriminate. 
Qed.

Lemma app_singleton : forall (A:Type)(l:list A)(e e': A), l ++ [e] = [e'] -> l = [] /\ e = e'.
Proof.
intro. destruct l;intros. simpl in H. injection H. auto. simpl in H.
inversion H. apply app_nil in H2. destruct H2.
Qed.

(*
Ltac inversion_TD_nil H :=  inversion H; try 
                         (match goal with
                        | [ H' : ?l ++ [?e] = [] |- _ ] => try solve [apply app_nil in H'; contradiction]

                         end);subst.*)

(*
Lemma Trace_Derive_rev : forall (l:Trace)(c c' : Contract)(e: EventType), 
Trace_Derive c (l++[e]) (c'/e) -> Trace_Derive c l c'.
Proof.
induction l;intros.
- inversion_TD_nil H. subst. apply app_singleton in H0. subst.
*)
(*
Lemma Trace_Derive_cons : forall (l:Trace)(c c' : Contract)(e: EventType), 
Trace_Derive (c/e) l c' -> Trace_Derive c (e::l) c'.
Proof.
induction l;intros.
inversion_TD_nil H. subst. rewrite <- (app_nil_l [e]). auto.

 2: { inversion_TD_nil.
inversion_TD_nil H. 2: { 
inversion H. 2: { apply app_nil in H0. contradiction. 
intros.*)

Lemma Trace_Derive_trans : forall s s' c0 c1 c2 , Trace_Derive c0 s c1 -> Trace_Derive c1 s' c2 -> Trace_Derive c0 (s++s') c2.
Proof.
intros. induction H;simpl;auto.
Qed.

(*
Lemma Trace_Derive_first_der : forall (s:Trace) c0 c1 (e:EventType), Trace_Derive c0 (e :: s) c1 -> Trace_Derive (c0/e) s c1.
Proof.
induction s;intros.
inversion_TD_nil H. apply app_singleton in H0. destruct H0. rewrite H1.
rewrite H0 in H2. now inversion_TD_nil H2.

 subst.
intros. remember (e::s). induction H. discriminate.

-*)



Lemma trace_derive_spec : forall (c c' : Contract)(s : Trace), (trace_derive c s) = c' <-> Trace_Derive c s c'.
Proof.
split;intros.
- funelim (trace_derive c s);simpl;auto.
- induction H;auto. 
Qed.






(*
Lemma max_derivative_count_non_zero : forall (c : Contract), 0 < max_derivative_count c.
Proof.
induction c;simpl;try lia. rewrite (mult_n_O 0) at 1. 
apply PeanoNat.Nat.mul_lt_mono;auto.  
transitivity (Nat.pow 2 0). simpl. lia. apply PeanoNat.Nat.pow_lt_mono_r;lia.
rewrite (PeanoNat.Nat.add_lt_mono_r _ _ 1). simpl.
assert (1 < Nat.pow 2 (max_derivative_count c)). { apply PeanoNat.Nat.pow_gt_1;lia. }
lia.
Qed.*)


(*Lemma trace_derive_failure : forall (s : Trace), trace_derive Failure s = Failure.
Proof. intros;induction s;auto. Qed.

Lemma trace_derive_success : forall (s : Trace), trace_derive Success s = Success \/ trace_derive Success s = Failure.
Proof.
induction s.
- simpl; left;auto.
- simpl; right;  auto using trace_derive_failure.
Qed.

Ltac eq_event_destruct :=
  repeat match goal with
         | [ |- context[if eq_event_dec ?e ?e then _ else _] ] => destruct (eq_event_dec e e);try contradiction
         | [ |- context[if eq_event_dec ?e ?e0 then _ else _] ] => destruct (eq_event_dec e e0)
         end.
Lemma trace_derive_event : forall (s : Trace)(e :EventType), trace_derive (Event e) s = Event e \/ trace_derive (Event e) s = Success 
                                                             \/ trace_derive (Event e) s = Failure.
Proof.
destruct s;intros;simpl.
- now left.
- eq_event_destruct.
  * right. auto using trace_derive_success.
  * right. right. apply trace_derive_failure.
Qed.


Lemma trace_derive_plus : forall (c0 c1 : Contract)(s : Trace), trace_derive (c0 _+_ c1) s = (trace_derive c0) s _+_ (trace_derive c1) s.
Proof.
intros. funelim (trace_derive (c0 _+_ c1) s);  simpl ; auto.
Qed.



Hint Rewrite trace_derive_failure trace_derive_success trace_derive_event : trace_deriveDB.

Ltac saia := simpl ; autorewrite with trace_deriveDB; intuition || auto.


Lemma exists_disimilar_event : forall (e : EventType), exists e', e <> e'.
Proof.
intros;  destruct e;  try solve [ exists Transfer; intro H;discriminate | exists Notify; intro H;discriminate ].
Qed.
Search (In _).*)
Definition alphabet := [Notify;Transfer].
Lemma in_alphabet : forall (e : EventType), In e alphabet.
Proof.
intros. unfold alphabet; destruct e; auto using in_cons, in_eq. 
Qed.
Global Opaque alphabet.

Fixpoint approx (A : Type) (n: nat) (f: A -> A) (arg: A) : A :=
match n with
| 0 => arg
| S n' => f (approx n' f arg)
end.

(*Lemma approx_spec : forall (A:Type)(P:A -> Prop)(n : nat)(f: A -> A)(arg:A), P (f arg) -> P (approx n f arg).
Proof.
intros. induction n.
- simpl.*)

(*
Ltac record_destruct :=
match goal with
         | [ |- {| r |} => destruct R
         end.*)
Definition extend_traces_once (ll : list Trace) : list Trace :=
 flat_map (fun e => map (fun l => e::l) ll) alphabet.



Lemma extend_traces_once_spec : forall (s : Trace)(ll : list Trace)(e : EventType), 
 In (e::s) (extend_traces_once ll) <-> In s ll.
Proof.
split;intros.
- unfold extend_traces_once in H. rewrite in_flat_map in H. destruct_ctx.
  rewrite in_map_iff in H0. destruct_ctx. inversion H0. now subst.
- unfold extend_traces_once. rewrite in_flat_map. exists e.
  split;auto using in_alphabet. rewrite in_map_iff. exists s;split;auto.
Qed.

Lemma extend_traces_once_length : forall (ll : list Trace)(n:nat),
 Forall (fun s => length s = n) ll -> Forall (fun s => length s = S n ) (extend_traces_once ll).
Proof.
intros.
inversion H.
- unfold extend_traces_once. rewrite Forall_forall. intros. simpl in H1.
  rewrite in_flat_map in H1. destruct H1. destruct H1. simpl in H2. inversion H2.
- rewrite Forall_forall. intros. unfold extend_traces_once in H3.
  rewrite in_flat_map in H3. destruct H3. destruct H3.
  rewrite in_map_iff in H4. destruct H4. destruct H4. subst.
  simpl. f_equal. rewrite Forall_forall in H. auto.
Qed.

Hint Rewrite extend_traces_once_spec : deriveDB.

Ltac auto_rew := autorewrite with deriveDB using auto.

Definition n_length_traces (n : nat) := approx n extend_traces_once [[]].

Lemma n_length_traces_spec_helper : forall (s' s : Trace)(ll:list Trace), 
 In s ll -> In (s'++s) (approx (length s') extend_traces_once ll).
Proof.
induction s';intros.
- now simpl.
- simpl. auto_rew. 
Qed.

Hint Unfold n_length_traces : core.

Lemma in_n_length_traces_1 : forall (e : EventType), In [e] (n_length_traces 1).
Proof.
destruct e;simpl. 
- unfold n_length_traces. simpl. unfold extend_traces_once. simpl. 
  rewrite in_flat_map. exists Transfer. split;auto using in_alphabet,in_eq.
- unfold n_length_traces. simpl. unfold extend_traces_once. simpl. 
  rewrite in_flat_map. exists Notify. split;auto using in_alphabet,in_eq.
Qed.


(*Lemma list_length_1 : forall (A:Type)(l:list A), length l = 1 -> exists e, l = [e].
Proof.
intros. induction l. discriminate. simpl in H. inversion H.
apply length_zero_iff_nil in H1. subst. now exists a.
Qed.*)


Lemma in_n_length_traces_inc_iff : forall (n:nat)(e : EventType)(s : Trace), In (e::s) (n_length_traces (S n)) <-> In s (n_length_traces n).
Proof.
induction n;split;intros.
- unfold n_length_traces in H. simpl in H. rewrite extend_traces_once_spec in H.
  unfold n_length_traces. now simpl.
- simpl in H. destruct H. subst. apply in_n_length_traces_1. inversion H.
- unfold n_length_traces in *. simpl in *. now rewrite extend_traces_once_spec in H.
- unfold n_length_traces in *. simpl in *. now rewrite extend_traces_once_spec.
Qed.

Hint Rewrite in_n_length_traces_inc_iff : deriveDB.



Lemma length_iff_length_traces : forall (n :nat)(s : Trace), In s (n_length_traces n) <-> length s = n.
Proof.
induction n;split;intros.
- simpl in H. destruct H. now rewrite <- H. destruct H.
- simpl.  apply length_zero_iff_nil in H. now left.
- destruct s. unfold n_length_traces in H. simpl in H. unfold extend_traces_once in H.
  rewrite in_flat_map in H. destruct_ctx. rewrite in_map_iff in H0. destruct_ctx. discriminate.
  simpl. f_equal. rewrite <- IHn.  rewrite <- in_n_length_traces_inc_iff. eapply H.
- destruct s. discriminate. rewrite in_n_length_traces_inc_iff.
  rewrite IHn. simpl in H. auto.
Qed.

(*Lemma n_length_traces_length_aux : forall (n:nat)(s:Trace), In s (n_length_traces n) -> length s = n.
Proof.
induction n;intros.
- simpl in H. destruct H. now subst. contradiction.
- destruct s.  unfold n_length_traces in H. simpl in H.
  unfold extend_traces_once in H. rewrite in_flat_map in H. 
  destruct_ctx. rewrite in_map_iff in H0. destruct_ctx. discriminate. 
  auto using in_n_length_traces_inc.
in *. auto using extend_traces_once_length.
Qed.

Lemma n_length_traces_length_aux : forall (n:nat), Forall (fun s => length s = n)(n_length_traces n).
Proof.
induction n;intros.
- simpl. unfold n_length_traces. simpl. constructor;auto.
- unfold n_length_traces in *. simpl in *. auto using extend_traces_once_length.
Qed.

Lemma In_n_length_traces_iff_length : forall (n :nat)(s : Trace), In s (n_length_traces n) <-> length s = n.
Proof.
split;auto using length_i_In_n_length_traces.
intros.




Lemma n_length_traces_length : forall (s:Trace)(n:nat), In s (n_length_traces n) -> length s = n.
Proof.
intros. pose proof (n_length_traces_length_aux n). rewrite Forall_forall in H0. auto.
Qed.*)
 
Definition nth_derivatives (c : Contract)(n:nat) : list Contract :=  map (trace_derive c) (n_length_traces n).

(*Nice symmetry in this lemma when unfolding left hand side with in_map_iff *)
Lemma nth_derivatives_iff : forall (n : nat)(c c_der : Contract), In c_der (nth_derivatives c n) <-> exists (s : Trace), Trace_Derive c s c_der /\  length s = n.
Proof.
intros. unfold nth_derivatives. split;intros.
- rewrite in_map_iff in H. destruct_ctx. exists x.
  split. now rewrite <- trace_derive_spec. now rewrite <- length_iff_length_traces. 
- destruct_ctx. rewrite in_map_iff. exists x.
  split. now rewrite trace_derive_spec. now rewrite length_iff_length_traces.
Qed.

(*Ltac in_map_iff_destruct :=
  repeat match goal with
         | [ H: In ?c (map _ _) |- _ ] => rewrite in_map_iff in H
         | [ H: ?H0 /\ ?H1 |- _ ] => destruct H
         | [ H: exists _, _  |- _ ] => destruct H
         end.*)
(*
Lemma Trace_Derive_In_nth_derivatives : forall (c c' : Contract)(s:Trace), Trace_Derive c s c' -> In c' (nth_derivatives c (length s)).
Proof.
intros. induction H.
simpl. now left.
unfold nth_derivatives in *. in_map_iff_destruct.
rewrite in_map_iff. exists (e::x). split.
now simpl.
 
destruct IHTrace_Derive. 



destruct IHTrace_Derive. in_map_iff_destruct IHTrace_Derive.
auto.*)
(*

Lemma length_removelast : forall (A: Type)(e:A)(l:list A), length (removelast (e :: l)) = length l.
Proof.
intros. simpl. generalize dependent e. induction l;intros;auto. simpl. f_equal. now simpl.
Qed.

(*express lemma with n, so that induction can be done on n, instead of s, generalizing induction hypothesis*)
Lemma trace_derive_Nth_Derivative_aux: forall (n:nat)(s:Trace)(c: Contract), length s = n -> Nth_Derivative c (trace_derive c s) n.
Proof.
induction n;intros. apply length_zero_iff_nil in H. now subst.
rewrite app_removelast_last with (A:=EventType)(l:=s)(d:=Transfer).
rewrite derive_trace_derive. constructor. apply IHn.
destruct s. simpl in H. discriminate. rewrite length_removelast.  simpl in H.
auto. intro H2. rewrite H2 in H. simpl in H. discriminate.
Qed.

Lemma trace_derive_Nth_Derivative: forall (s:Trace)(c: Contract), Nth_Derivative c (trace_derive c s) (length s).
Proof.
auto using trace_derive_Nth_Derivative_aux.
Qed.



Lemma nth_derivatives_spec : forall c c_der n, In c_der (nth_derivatives c n) -> Nth_Derivative c c_der n.
Proof.
intros. unfold nth_derivatives in H.
in_map_iff_destruct H. rewrite <- H.
apply n_length_traces_length in H0. rewrite <- H0. apply trace_derive_Nth_Derivative.
Qed.*)

(*
Lemma nth_derivatives_spec : forall (c : Contract)(s:Trace), In (trace_derive c s) (nth_derivatives c (length s)).
Proof.
intros. generalize dependent c. induction s;intros;simpl; try now left.
unfold nth_derivatives. rewrite in_map_iff. exists (a::s). split ; simpl;auto.
apply n_length_traces_spec.
Qed. *)
Definition simple_n_derivative_closure (c : Contract)(n:nat) := flat_map (nth_derivatives c) (seq 0 (1+n)).

Lemma nth_derivatives_in_closure : forall (c c_der : Contract)(n n':nat), n<=n' -> In c_der (nth_derivatives c n) -> In c_der (simple_n_derivative_closure c n').
Proof.
intros. unfold simple_n_derivative_closure. rewrite in_flat_map. exists n.
split. apply in_seq. split;lia. auto.
Qed.

Lemma in_closure_nth_derivatives : forall (c c_der : Contract)(n' :nat),  In c_der (simple_n_derivative_closure c n') -> 
       exists n, n<=n' /\ In c_der (nth_derivatives c n).
Proof.
intros. unfold simple_n_derivative_closure in H. rewrite in_flat_map in H.
destruct_ctx. exists x. rewrite in_seq in H. destruct H. split;try lia;auto.
Qed.

Lemma simple_n_derivative_closure_spec : forall (c c_der : Contract)(n : nat), In c_der (simple_n_derivative_closure c n) <-> 
exists (s : Trace), Trace_Derive c s c_der /\  length s <= n.
Proof.
split;intros.
- apply in_closure_nth_derivatives in H. destruct_ctx. rewrite nth_derivatives_iff in H0.
  destruct_ctx. exists x0. rewrite H1.  split;auto.
- destruct_ctx. eapply nth_derivatives_in_closure;eauto.
  rewrite nth_derivatives_iff. exists x. split;auto.
Qed.

Fixpoint In_mod_ACI (c : Contract) (l : list Contract) :=
match l with
| [] => False
| c' ::l' => c' =ACI= c \/ In_mod_ACI c l'
end.

Lemma In_mod_ACI_i_In : forall (c : Contract) (l : list Contract), In_mod_ACI c l -> exists c', In c' l /\ c' =ACI= c.
Proof.
intros c l. generalize dependent c. induction l;intros.
- simpl in H. inversion H.
- simpl in H. destruct H.
  * exists a. split;auto using in_eq.
  * apply IHl in H. destruct H. exists x. destruct H. split;auto using in_cons.
Qed.

Lemma In_i_In_mod_ACI : forall (c : Contract) (l : list Contract), (exists c', In c' l /\ c' =ACI= c) -> In_mod_ACI c l.
Proof.
intros. generalize dependent c. induction l;intros.
- destruct H. destruct H. simpl in H. inversion H.
- simpl. destruct H. destruct H. simpl in H. inversion H.
  * subst. now left.
  * right. apply IHl. exists x;split;auto.
Qed.

Theorem In_mod_ACI_iff_In : forall (c : Contract) (l : list Contract), In_mod_ACI c l <-> exists c', In c' l /\ c' =ACI= c.
Proof.
split; auto using In_i_In_mod_ACI.
intros. now apply In_mod_ACI_i_In.
Qed.

Theorem In_mod_ACI_cons : forall (c c' : Contract) (l : list Contract), In_mod_ACI c (c'::l) <-> c' =ACI= c \/ In_mod_ACI c l.
Proof.
split;intros.
- rewrite In_mod_ACI_iff_In in H. destruct_ctx. induction H.
  * subst. now left.
  * right. rewrite In_mod_ACI_iff_In. exists x. split;auto.
- destruct H.
  * rewrite In_mod_ACI_iff_In. exists c'. split;auto using in_eq.
  * rewrite In_mod_ACI_iff_In in *. destruct_ctx. exists x.
    split;auto using in_cons,in_eq.
Qed. 


Definition ACI_preserving (f : Contract -> Contract) := forall c0 c1, c0 =ACI= c1 -> f c0 =ACI= f c1.

Fixpoint max_derivative_count (c : Contract) :=
match c with
| Failure => 1
| Success => 2
| Event _ => 3
| c0 _+_ c1 => (max_derivative_count c0)* (max_derivative_count c1)
| c0 _;_ c1 => (max_derivative_count c0) * Nat.pow 2 (max_derivative_count c1)
| Star c0 => (Nat.pow 2 (max_derivative_count c0)) - 1
end.

CoInductive Closure : Contract -> list Contract -> Prop :=
| Closure_fix c l (H0: forall e, Closure (c/e) l) (H1 : exists c', c' =R= c /\ In c' l)  : Closure c l.

Lemma In_Closure_i_Trace_Derive : forall (c: Contract)(l : list Contract), 
Closure c l -> (forall (s : Trace)(c_der : Contract), Trace_Derive c s c_der -> exists c', c' =R= c_der /\ In c' l).
Proof.
intros. generalize dependent c. induction s;intros.
- inversion H0. subst. inversion H. destruct_ctx. exists x;auto.
- inversion H0. inversion H. subst. eapply IHs. eapply H6. eauto.
Qed.

Lemma Trace_Derive_i_In_Closure : forall (c: Contract)(l : list Contract), 
(forall (s : Trace)(c_der : Contract), Trace_Derive c s c_der -> exists c', c' =R= c_der /\ In c' l) -> Closure c l.
Proof.
cofix H_co.
intros. constructor.
- intros. apply H_co. intros. eapply H. constructor. eauto.
- eauto.
Qed.

Theorem Closure_iff : forall (c: Contract)(l : list Contract), 
Closure c l <-> (forall (s : Trace)(c_der : Contract), Trace_Derive c s c_der -> exists c', c' =R= c_der /\ In c' l).
Proof.
split;intros. 
- eapply In_Closure_i_Trace_Derive;eauto.
- eapply Trace_Derive_i_In_Closure;eauto.
Qed.

Lemma Closure_Failure : Closure Failure [Failure].
Proof.
cofix IH. constructor.
- intros. now simpl. 
- exists Failure. split;auto using in_eq.
Qed.

Hint Resolve Closure_Failure : ClosureDB.

Ltac autoC := auto with ClosureDB.

Lemma Closure_cons : forall (c c_der : Contract)(l : list Contract), Closure c l -> Closure c (c_der::l).
Proof.
cofix IH.
intros. constructor;inversion H;eauto. 
simpl. destruct_ctx. exists x. split;auto. 
Qed.

Hint Resolve Closure_Failure Closure_cons in_eq in_cons in_nil : ClosureDB.

Lemma Closure_Success : Closure Success [Success;Failure].
Proof.
cofix IH.
constructor; simpl; auto with ClosureDB. exists Success. split; auto with ClosureDB.

Qed.

Hint Resolve Closure_Success : ClosureDB.

Ltac eq_event_destruct :=
  repeat match goal with
         | [ |- context[if EventType_eq_dec ?e ?e then _ else _] ] => destruct (EventType_eq_dec e e);try contradiction
         | [ |- context[if EventType_eq_dec ?e ?e0 then _ else _] ] => destruct (EventType_eq_dec e e0)
         end.

Lemma Closure_Event : forall (e : EventType), Closure (Event e) [Event e;Success;Failure].
Proof.
cofix IH.
constructor; intros;simpl.
- eq_event_destruct; auto with ClosureDB. 
- exists (Event e). split;auto.
Qed.

Hint Resolve Closure_Event : ClosureDB.

Definition plus_prod (l0 l1 : list Contract) := map (fun p => (fst p) _+_ (snd p)) (list_prod l0 l1).

Hint Unfold plus_prod : ClosureDB.

Lemma Closure_Plus : forall (c0 c1 : Contract)(l0 l1 : list Contract), Closure c0 l0 -> Closure c1 l1 -> 
 Closure (c0 _+_ c1) (plus_prod l0 l1).
Proof.
cofix IH.
intros. inversion H. inversion H0. constructor;simpl;eauto. destruct_ctx. exists (x0 _+_ x).
split;auto. rewrite H2. now rewrite H6. 
unfold plus_prod. rewrite in_map_iff. exists (x0,x). split;auto.
apply in_prod;auto.
Qed.

Fixpoint flatten (c : Contract) : list Contract :=
match c with
| c0 _+_ c1 => (flatten c0) ++ (flatten c1)
| _ => [c]
end.

Definition plus_combine (l0 l1 : list Contract) := map (fun p => (fst p) _+_ (snd p)) (combine l0 l1).

Lemma flatten_non_empty : forall (c:Contract), exists c' l, flatten c = c'::l.
Proof.
induction c;intros.
- exists Success. exists []. auto.
- exists Failure. exists []. auto.
- exists (Event e). exists []. auto.
- destruct_ctx. exists x1. exists (x2 ++ (flatten c2)).
  simpl. rewrite H0. now simpl.
- exists (c1 _;_ c2). exists []. now simpl.
- exists (Star c). exists []. now simpl.
Qed.


Lemma Trace_Derive_seq_head : forall s c0 c1, hd Failure (flatten ((c0 _;_ c1) // s)) = ((c0 // s) _;_ c1).
Proof.
induction s;intros. now simpl. simpl. rewrite derive_plus. simpl.
destruct (flatten_non_empty ((c0 / a _;_ c1) // s)).
destruct_ctx. rewrite <- IHs. rewrite H. now simpl.
Qed. 

Lemma Trace_Derive_seq_head2 : forall s c0 c1, exists l, (flatten ((c0 _;_ c1) // s)) = ((c0 // s) _;_ c1):: l.
Proof.
induction s;intros. exists []. now simpl. simpl. rewrite derive_plus. simpl.
destruct (flatten_non_empty ((c0 / a _;_ c1) // s)). specialize IHs with (c0/a) c1.
destruct_ctx. rewrite H0. exists (x1 ++ (flatten ((o c0 _;_ c1 / a) // s))).
now simpl.
Qed. 

Lemma flatten_seq_derivative : forall c0 c1 e, flatten ((c0 _;_ c1)/ e) = [c0/e _;_ c1;o(c0)_;_(c1/e)].
Proof.
intros. now simpl.
Qed.

Lemma flatten_seq_trace_derive : forall s c0 c1 e, flatten ((c0 _;_ c1)// (e::s)) = flat_map (fun c => flatten (c//s)) (flatten ((c0 _;_ c1)/e)). 
Proof.
induction s;intros. now simpl. simpl. rewrite derive_plus. simpl.
rewrite derive_plus. simpl. rewrite derive_plus. simpl.
rewrite app_nil_r. auto.
Qed.

(*
Lemma unfold_derive_o_seq : forall c0 c1 e, (o c0 _;_ c1) / e = Failure _;_ c1 _+_ (o (o c0)) _;_ c1/e.
Proof.
intros. simpl. o_destruct. rewrite H at 1. now simpl.
rewrite H at 1. now simpl.
Qed.


Lemma test2 : forall c0 c1 e, Forall (fun c => exists c' s, c = (o c') _;_ (c1//s)) (flatten ((o c0 _;_ c1)/e)).
Proof.
intros. rewrite Forall_forall. intros. rewrite unfold_derive_o_seq in H. simpl in H.
destruct H. subst. exists Failure. rewrite o_false;auto. exists []. now simpl.
destruct H. subst. exists (o c0). exists [e]. now simpl. inversion H.
Qed.*)

Lemma o_derive : forall c e, (o c)/e = Failure.
Proof.
intros. o_destruct. unfold o. rewrite H0. now simpl. unfold o. rewrite H0. now simpl.
Qed.

Lemma Failure_trace_derive : forall s, Failure//s = Failure.
Proof.
induction s;intros;auto.
Qed.

Hint Immediate o_derive Failure_trace_derive : ClosureDB.

(*
Lemma test3 : forall s' c0 c1, Forall (fun c => exists c' s, c = (o c') _;_ (c1//s)) (flatten (((o c0) _;_ c1)//s')).
Proof.
induction s';intros.
- rewrite Forall_forall. intros. simpl in H. destruct H.
  * subst. exists c0. exists []. now simpl.
  * inversion H.
- rewrite Forall_forall. intros. simpl in H. rewrite derive_plus in H. simpl in H.
  apply in_app_or in H. destruct H.
  * specialize IHs' with Failure c1. rewrite Forall_forall in IHs'.
    specialize IHs' with x. rewrite o_derive in H. apply IHs' in H. destruct_ctx.
    exists x0. now exists x1.
  * specialize IHs' with (o c0) (c1/a). rewrite Forall_forall in IHs'.
    specialize IHs' with x. apply IHs' in H. destruct_ctx. subst.
    exists x0. exists (a::x1). now simpl.
Qed.*)

Lemma o_or : forall (c : Contract), o c = Success \/ o c = Failure.
Proof.
intros. o_destruct. rewrite H. now left. rewrite H. now right.
Qed.


Theorem flatten_seq_derive_shape : forall s c0 c1, exists l, (flatten ((c0 _;_ c1) // s)) = ((c0 // s) _;_ c1):: l /\
 Forall (fun c => exists c' s, c = (o c') _;_ (c1//s)) l.
Proof.
induction s;intros.
- simpl. exists []. split;auto.
- rewrite flatten_seq_trace_derive. rewrite flatten_seq_derivative. simpl.
  rewrite app_nil_r. specialize IHs with (c0/a) c1 as IHs'.
  specialize IHs with (o c0) (c1/a). destruct_ctx. rewrite H1. rewrite H.
  exists (x ++ o c0 // s _;_ c1 / a :: x0). split;auto.
  rewrite Forall_forall in *. intros. apply in_app_or in H3. destruct H3.
  * apply H0 in H3. destruct_ctx. exists x2. now exists x3.
  * simpl in H3. destruct H3. 
    ** rewrite <- H3. destruct (o_or c0).
      *** rewrite H4. destruct s.
        **** simpl. exists Success. now exists [a].
        **** simpl. rewrite Failure_trace_derive. exists Failure. 
             now exists [a].
      *** rewrite H4. rewrite Failure_trace_derive. exists Failure.
          now exists [a].
    ** apply H2 in H3. destruct_ctx. rewrite H3.
       exists x2. now exists (a::x3).
Qed.

Lemma flatten_seq_derive_contains_seqs : forall s c0 c1 c_der, In c_der (flatten ((c0 _;_ c1) // s)) -> exists c0' c1', c0' _;_ c1' = c_der.
Proof.
induction s;intros.
- simpl in H. destruct H;try contradiction. exists c0. now exists c1.
- simpl in H. rewrite derive_plus in H. simpl in H. apply in_app_or in H. destruct H; now apply IHs in H.
Qed.

(*
Theorem in_flatten_seq_o_derive : forall s c0 c1 c_der0 c_der1, In (c_der0 _;_ c_der1) (flatten (((o c0) _;_ c1) // s)) <-> 
(c0' = Success \/ c0' = Failure) /\ (c1')

 = ((o c0)//s _;_ c1) \/ (s <> [] /\ exists n, c_der = Success _;_ (c1 // (skipn n s)) \/ c_der = Failure _;_ (c1 // (skipn n s))).
Proof.*)

Lemma o_idempotent : forall (c : Contract), o (o c) = o c.
Proof.
intros. destruct (o_or c); rewrite H;auto. 
Qed.

Hint Immediate o_idempotent : ClosureDB.
(*



(c_der0 = (o c0) \/ (s <>[] /\ c_der0 = Failure)) /\ exists n, c_der1 = c1//(skipn n s).
Proof.



Theorem in_flatten_seq_o_derive : forall s c0 c1 c_der0 c_der1, In (c_der0 _;_ c_der1) (flatten (((o c0) _;_ c1) // s)) <-> 
(c_der0 = (o c0) \/ (s <>[] /\ c_der0 = Failure)) /\ exists n, c_der1 = c1//(skipn n s).*)

Ltac derive_plus_tac H := rewrite derive_plus in H; simpl in H; apply in_app_or in H; destruct H.
Theorem in_flatten_seq_o_derive : forall s e c0 c1 c_der0 c_der1, In (c_der0 _;_ c_der1) (flatten (((o c0) _;_ c1) // (e::s))) <-> 
(c_der0 = Failure /\ exists n, c_der1 = c1//(firstn n s)) \/ (c_der0 = o c0 /\ exists n, c_der1 = c1//(e::(firstn n s))).
Proof.
induction s;intros.
- split;intros;simpl. destruct H;try contradiction. inversion H. subst.
  left.  split;autoC. exists 0. now simpl. destruct H;try contradiction. 
  inversion H. subst. right. split;autoC. exists 1. now simpl.
  destruct H. destruct_ctx. subst. left. simpl. rewrite firstn_nil.
  rewrite o_derive. auto.  destruct_ctx. destruct x. simpl in H0. subst. subst. right.
  rewrite o_idempotent. 
  auto. simpl in H0. subst. right. left. rewrite o_idempotent. auto.
- split;intros.
  * simpl trace_derive in H. remember (a::s). simpl in H.
    derive_plus_tac H. rewrite Heql in H. rewrite o_derive in H.
    assert (HA : Failure = o Failure). { auto. } rewrite HA in H.
    apply IHs in H. destruct H.
    ** destruct_ctx. subst. left.
 rewrite <- Heql in H. simpl in H. fold in H. derive_plus_tac H. 
    ** simpl in IHs. rewrite o_derive in H. assert (HA : Failure = o Failure). { auto. }
       rewrite HA in H. setoid_rewrite o_idempotent in IHs. 
       rewrite o_idempotent in H. apply IHs in H. destruct H.
      *** destruct_ctx. subst. left. split;auto. destruct H. derive_plus_tac H.
      *** simpl in IHs. rewrite derive_plus in H. simpl in H. simpl in H.



 left.
  destruct (o_or c0); intuition. now exists 0. left. symmetry. destruct_ctx.
  destruct (o_or c0). destruct H. subst. rewrite H1. rewrite skipn_nil. auto.
  destruct H. contradiction. destruct H. subst. rewrite skipn_nil. auto.
  destruct H. contradiction.
- split;intros.
  * rewrite derive_plus in H. simpl in H. apply in_app_or in H. destruct H.
    ** rewrite o_derive in H. assert (HA: Failure = o Failure). auto.
       rewrite HA in H. apply IHs in H. destruct_ctx. subst. split.
      *** destruct H.
        **** subst. right. split. intro H3. discriminate. auto.
        **** destruct H. subst. right. split. intro H3. discriminate. auto.
      *** destruct H. subst. exists (S x). auto. exists (S x). auto.
    ** apply IHs in H. destruct_ctx. subst. destruct H.
      *** split. subst. rewrite o_idempotent. now left. split.
 

  subst. rewrite H1. left.
  destruct H. subst.  inversion H. now left. destruct_ctx. contradiction.

Theorem in_flatten_seq_derive : forall s c0 c1 c_der0 c_der1, In (c_der0 _;_ c_der1) (flatten ((c0 _;_ c1) // s)) <-> 
(c_der0 _;_ c_der1 = c0 // s _;_ c1) \/ ( s<> [] /\ (c_der0 = Success \/ c_der0 = Failure) /\ exists n, c_der1 = c1//(skipn n s)).
Proof.
intro. 
induction s;intros;simpl.
- split;intros. destruct H;try contradiction. inversion H. subst. now left.
  destruct H. inversion H. now left. destruct_ctx. contradiction.
- split;intros.
  * rewrite derive_plus in H. simpl in H. apply in_app_or in H. destruct H.
    ** apply IHs in H. destruct H.
      *** now left.
      *** destruct_ctx. destruct H0.
        **** subst. right. split.  intro H2.  discriminate. split. now left. 
             exists (S x). now simpl.
        **** subst. right. split. intro H2. discriminate. split. now right.
             exists (S x). now simpl.
    ** apply IHs in H. destruct H.
      *** inversion H. subst. left. simpl; left.
 intuition;try contradiction. auto.
 destruct H;subst.
  exists 1. now simpl. split. destruct H. inversion H. subst.
  destruct (o_or c0). rewrite H0. right. now left. rewrite H0. right. right. auto.
  inversion H. inversion H. inversion H0. subst. exists 0. now simpl.
  inversion H0. destruct_ctx. destruct H. destruct x.
  * simpl in H0. subst. intuition. auto.
 subst. destruct H;subst. simpl. now right. susbt. 
 rewrite H.
 rewrite Heqt in *. simpl in H. destruct H;try contradiction. inversion H.
  now left. destruct H. rewrite Heqt. simpl. auto. now left.
  destruct H. subst.  rewrite H.


c_der = (c0//s _;_ c1) \/ (s <> [] /\ exists n, c_der = Success _;_ (c1 // (skipn n s)) \/ c_der = Failure _;_ (c1 // (skipn n s))).
Proof.
induction s;intros.
- simpl. split;intros. destruct H. now left. contradiction. destruct H. now left.
  destruct_ctx. destruct H. auto.
- split;intros.
  * simpl in H. rewrite derive_plus in H. simpl in H.
    apply in_app_or in H. destruct H.
    ** apply IHs in H. destruct H.
      *** left. now simpl.
      *** right. split;auto. intro H3. discriminate. destruct_ctx.
          destruct H0.
        **** rewrite H0. exists (S x). simpl. now left.
        **** rewrite H0. exists (S x). simpl. now right.
    ** apply IHs in H. destruct H.
      *** right. split. intro H3. discriminate. rewrite H.
          destruct (o_or c0).
        **** rewrite H0. exists ( left;simpl;auto. auto. subst. simpl. rewrite IHs.
   split split;intros.
  * inversion H;try contradiction. now left.
  * destruct H. now left. destruct H. destruct H.
    ** simpl in H.


 destruct s. 
      *** simpl in H. destruct H;try contradiction.
          right. split. intro. discriminate. rewrite <- H. exists 0.
          destruct (o_or c0);rewrite H0; auto || auto.
      *** rewrite flatten_seq_trace_derive in H. rewrite in_flat_map in H.
          destruct_ctx.
        **** inversion




 ((c0 // s) _;_ c1):: l /\
 Forall (fun c => exists c' s, c = (o c') _;_ (c1//s)) l.


Check firstn.
Inductive Flat_Seq_Derivative : Contract -> Contract -> Trace -> nat -> list Contract -> Prop :=
| FSD_Single c0 c1 s : Flat_Seq_Derivative c0 c1 s 0 [c0//s _;_ c1]
| FSD_Cons c0 c1 s n l (H: Flat_Seq_Derivative c0 c1 s n l) : Flat_Seq_Derivative c0 c1 s (S n) (c1//(firstn (S n) s)::l).

Ltac in_forall HF HIn := rewrite Forall_forall in HF; apply HF in HIn;destruct_ctx;subst.

Lemma flatten_seq_derive_FSD : forall c0 c1 c_der s l, Flat_Seq_Derivative c0 c1 s (length s) l -> 
 In c_der (flatten ((c0 _;_ c1) // s)) <-> ((exists c', c' =R= c_der /\ In c' l) \/ c_der =R= Failure).
Proof. 
intros. remember (length s). induction H.
- simpl. symmetry in Heqn. apply length_zero_iff_nil in Heqn. subst. destruct (flatten_seq_derive_shape [] c0 c1). destruct H. split;intros.
  * rewrite H in H1. simpl in H1. destruct H1.
    ** subst. simpl. left. exists (c0 _;_ c1). split;auto.
    ** in_forall H0 H1. simpl. destruct (o_or x0). 
      *** rewrite H1. left. exists (c0 _;_ c1). split. split;auto.



  * inversion H1. subst. rewrite H.  auto using in_eq. contradiction.
  * rewrite H in H1. simpl in H1. destruct H1;auto.
    rewrite Forall_forall in H0. apply H0 in H1. destruct_ctx. subst.
    ** now left. 
    rewrite Forall_forall in H1.

Lemma FSD_max_length : forall c0 c1 c_der s l, n > length s ->  Flat_Seq_Derivative c0 c1 s n l ...

Definition seq_closure_list (c0 c1 : Contract) (l0 l1 : list Contract) := 
 let first_elements := map (fun c => c _;_ c1) l0 in
 let mid_success_elems := map (fun c => Success _;_ c) l1 in
 let mid_failure_elems := map (fun c => Failure _;_ c) l1 in
 

Lemma Closure_Seq : forall (c0 c1 : Contract)(l0 l1 : list Contract), Closure c0 l0 -> Closure c1 l1 -> 
 Closure (c0 _;_ c1) ((map (fun c => c _;_ c1) l0) ++ ) l1).


(*Lemma Trace_Derive_seq_tail : forall  l e s c0 c1 c', flatten ((c0 _;_ c1) // s) = e::l ->
In c' l -> exists c'' n, Trace_Derive c1 (firstn n s) c'' /\ (c' = Success _;_ c'' \/ c' = Failure _;_ c'').
Proof.
induction l;intros.
- simpl in H0. inversion H0.
- simpl in H0. inversion H0.
  * rewrite derive_plus in H. simpl in H.
  destruct (flatten_non_empty ((c0 / a _;_ c1) // s)).
  destruct_ctx. rewrite H0 in H. simpl in H. apply in_app_or in H.
  destruct H.
  *

  destruct (flatten_non_empty ((c0 _;_ c1) // (a :: s))).
Trace_Derive (c0 _;_ c1) s c_der -> In_mod_ACI c_der ???



Definition decompose_seq_aux (c0 c1 : Contract) (s : Trace) := 
match s with
| [] => if nu c0 then
 (trace_derive c0 s) _;_ c1 _+_ 


Lemma Trace_Derive_seq : forall (c0 c1 c_der : Contract)(s : Trace), Trace_Derive (c0 _;_ c1) s c_der ->
 c_der =ACI= *)

Lemma plus_prod_length : forall (l0 l1 : list Contract), length (plus_prod l0 l1) = length l0 * length l1.
Proof.
intros. unfold plus_prod. rewrite map_length. now rewrite prod_length.
Qed.

Hint Resolve Closure_Plus  : ClosureDB.

Lemma exists_finite_closure : forall (c : Contract), exists (l : list Contract), Closure c l /\ length l = max_derivative_count c.
Proof.
induction c;intros.
- exists [Success;Failure]. split;auto with ClosureDB. 
- exists [Failure]. split;auto with ClosureDB.
- exists [Event e;Success;Failure]. split;auto with ClosureDB.
- destruct_ctx. exists (plus_prod x0 x). split;simpl; auto with ClosureDB.
  rewrite plus_prod_length. rewrite H2. now rewrite H0.
-
  rewrite prod_length.
  simpl.

Definition simple_derivative_closure (c : Contract) := simple_n_derivative_closure c (max_derivative_count c).


Eval compute in flat_map (nth_derivatives Failure) (seq 0 1).
Lemma simple_derivative_closure_spec_helper : forall (n:nat)(c : Contract)(s:Trace), length s <n -> 
In (trace_derive c s) (flat_map (nth_derivatives c) (seq 0 n)).
Proof.
induction n;intros.
- simpl. destruct s;simpl in H; inversion H.
- rewrite in_flat_map. exists (length s). split; auto using nth_derivatives_spec.
  rewrite in_seq. simpl.  unfold lt. split; auto.
    transitivity (length s);lia.
Qed.


Lemma in_simple_derivative_closure : forall (c : Contract)(s : Trace), length s < max_derivative_count c ->
 In (trace_derive c s) (simple_derivative_closure c).
Proof.
intros. unfold simple_derivative_closure. now apply simple_derivative_closure_spec_helper.
Qed.

Lemma in_simple_derivative_closure_failure_success : In Failure (simple_derivative_closure Success).
Proof. unfold simple_derivative_closure. rewrite in_flat_map. exists 1.
rewrite in_seq.
split;auto. rewrite <- (trace_derive_failure [Transfer]). apply nth_derivatives_spec.
Qed.

Lemma in_simple_derivative_closure_success_event : forall (e : EventType), In Success (simple_derivative_closure (Event e)).
Proof.
intros.
unfold simple_derivative_closure. rewrite in_flat_map. exists 1.
rewrite in_seq.
split;simpl;auto. assert (HA: Success = (trace_derive (Event e) [e])). { simpl. now eq_event_destruct. }
rewrite HA. apply nth_derivatives_spec.
Qed.

Hint Unfold simple_derivative_closure : core.

(*
Lemma in_simple_derivative_closure_trans : forall (c0 c1 c2 : Contract), In c0 (simple_derivative_closure c1) ->
In c1 (simple_derivative_closure c2) -> In c0 (simple_derivative_closure c2).
Proof.
intros. unfold simple_derivative_closure in *. rewrite in_flat_map in *.
destruct H. destruct H0. exists (x+x0). split.
- destruct H. destruct H0. rewrite in_seq in *. split;simpl in *. lia.*)

Lemma in_simple_derivative_closure_failure_event : forall (e : EventType), In Failure (simple_derivative_closure (Event e)).
Proof.
intros.
 unfold simple_derivative_closure. rewrite in_flat_map. exists 1.
 split;simpl;auto. destruct ((exists_disimilar_event e)). 
 assert (HA: Failure = trace_derive (Event e) [x]). { simpl. now eq_event_destruct. }
 rewrite HA. apply nth_derivatives_spec.
Qed.

Print In.

 

(*
Lemma In_mod_ACI_iff : forall (f : Contract -> Contract) 
         (l : list Contract) (y : Contract), ACI_preserving f ->
       In_mod_ACI y (map f l) <->
       (exists x : Contract, f x =ACI= y /\ In_mod_ACI x l).
Proof.
split;intros.
- rewrite In_mod_ACI_iff_In in H0. destruct H0. destruct H0.
  rewrite in_map_iff in H0. destruct H0. destruct H0. exists x0. 
  rewrite H0. split;auto. rewrite In_mod_ACI_iff_In. exists x0. split;auto.
- destruct H0. destruct H0. rewrite In_mod_ACI_iff_In. 
  rewrite In_mod_ACI_iff_In in H1. destruct H1. exists (f x0). split.
  * rewrite in_map_iff. exists x0. destruct H1. split ;auto.
  * destruct H1. inversion H0.
    ** rewrite H4. auto. subst. unfold ACI_preserving in H. auto.
    **
 f_equal. symmetry in H1. auto.
  rewrite In_mod_ACI_iff_In in H0. destruct H0. destruct H0. exists  exists (f x).
  split;auto. rewrite in_map_iff. 
    split;auto. exists x.
   rewrite in_map_iff in H. destruct H. destruct H. exists x. split;auto.
  rewrite In_mod_ACI_iff_In. exists x. split;auto.
- destruct H. destruct H. rewrite in_map_iff. exists x.
intros. split;intros.*)

Ltac In_mod_destruct H := rewrite In_mod_ACI_iff_In in H; destruct H; destruct H;
rewrite in_map_iff in H; destruct H; destruct H.
Definition simple_n_derivative_closure (c : Contract) (n:nat) := flat_map (nth_derivatives c) (seq 0 n).
Definition plus_combine (l0 l1 : list Contract) := map (fun p => (fst p) _+_ (snd p)) (combine l0 l1).
Lemma simple_derivative_closure_plus : forall c0 c1, simple_derivative_closure (c0 _+_ c1) =
plus_combine (simple_n_derivative_closure c0 (max_derivative_count (c0 _+_ c1))) 
             (simple_n_derivative_closure c1 (max_derivative_count (c0 _+_ c1))).
Proof. Admitted.

Lemma derivative_closure_in_list_prod : forall c0 c1 c_der,
  (forall s, In_mod_ACI (trace_derive c0 s) (simple_derivative_closure c0)) -> 
  (forall s, In_mod_ACI (trace_derive c1 s) (simple_derivative_closure c1)) -> 
  In_mod_ACI c_der (map (fun p => (fst p) _+_ (snd p))(list_prod (simple_derivative_closure c0) (simple_derivative_closure c1)))
 -> In_mod_ACI c_der (simple_derivative_closure (c0 _+_ c1)).
Proof. 
intros. rewrite simple_derivative_closure_plus. rewrite In_mod_ACI_iff_In.
In_mod_destruct H1. destruct x0.
rewrite in_prod_iff in H3. destruct H3.
subst. simpl in H2. exists (c _+_ c2). subst. simpl in H2. split;auto.
unfold simple_derivative_closure. simpl.
-

 rewrite In_mod_ACI_iff_In in H1. destruct H1. destruct H1.
rewrite in_map_iff in H1. destruct H1. destruct H1.
rewrite In_mod_ACI_iff_In.
(*Lemma derivative_closure_in_list_prod : forall c0 c1 c_der, In c_der (simple_derivative_closure (c0 _+_ c1)) 
-> In_mod_ACI c_der (map (fun p => (fst p) _+_ (snd p))(list_prod (simple_derivative_closure c0) (simple_derivative_closure c1))).
Proof.
intros. unfold simple_derivative_closure in H. rewrite in_flat_map in H.
destruct H. destruct H. rewrite 

Lemma simple_derivative_closure_plus : forall (c0 c1 : Contract)(s : Trace),
 (forall s, exists c0', trace_derive c0 s =ACI= c0' /\ In c0' (simple_derivative_closure c0)) ->
 (forall s, exists c1', trace_derive c1 s =ACI= c1' /\ In c1' (simple_derivative_closure c1)) ->
 exists c', trace_derive (c0 _+_ c1) s =ACI= c' /\ 
 In c' (map (fun p => (fst p) _+_ (snd p))(list_prod (simple_derivative_closure c0) (simple_derivative_closure c1))).
Proof.
intros.
Admitted.*)
(* unfold simple_derivative_closure in H1. rewrite in_flat_map in H1.
destruct H1. destruct H1. unfold nth_derivatives in H2. rewrite in_map_iff in H2.
destruct H2. destruct H2. rewrite trace_derive_plus in H2.
rewrite in_map_iff. specialize H with x0. specialize H0 with x0.
destruct H. destruct H. destruct H0. destruct H0. exists (x1, x2).
split. injection H2. exists (trace_derive c0 x0, trace_derive c1 x0).
split.
- now simpl.
- rewrite in_prod_iff. split. simpl in H. rewrite in_seq in H. destruct H.
simpl in H2. pose proof (n_length_traces_length x). rewrite Forall_forall in H3. 
apply H3 in H1. apply in_simple_derivative_closure. rewrite H1. Search (?a < ?b * _).
assert (HA: x = x * 1). { lia. } rewrite HA in H2. SearchRewrite (1 * _).
 lia. subst. unfold incl. intr*)

(*To show P for derivative_closure of c0 _+_ c1, it suffices to show it for cartesian product of c0' and c1's closure*)


(*Contracts from all ACI equivalence classes are present in the simple derivative closure *)
Lemma simple_derivative_closure_spec : forall (c : Contract) (s : Trace), 
In_mod_ACI (trace_derive c s) (simple_derivative_closure c).
Proof.
induction c;intros.
- rewrite In_mod_ACI_iff_In. destruct (trace_derive_success s).
  * exists Success. rewrite H. saia. 
  * exists Failure. rewrite H. split;auto using in_simple_derivative_closure_failure_success.
- rewrite In_mod_ACI_iff_In. exists Failure. saia.
- rewrite In_mod_ACI_iff_In. destruct (trace_derive_event s e).
  * exists (Event e). rewrite H. saia.
  * destruct H.
    ** exists Success. rewrite H. split; auto using in_simple_derivative_closure_success_event. 
    ** exists Failure. rewrite H. split;auto using in_simple_derivative_closure_failure_event.
- apply derivative_closure_in_list_prod;auto.
  specialize IHc1 with s. specialize IHc2 with s. rewrite In_mod_ACI_iff_In in *.
  destruct IHc1. destruct IHc2. exists (x _+_ x0). split.
  * rewrite in_map_iff. exists (x, x0). split;auto.
    destruct H. destruct H0.
    apply in_prod;auto.
  * rewrite trace_derive_plus. destruct H. destruct H0.
    rewrite H1. now rewrite H2.
-
 Admitted. 



(*All derivatives of c can be found with traces of size max_derivative_count c or less *)
(*Remember rewrite c0 _;_ c1 / e to using the o-notation*)
Theorem finite_distinct_derivatives : forall (c : Contract)(s : Trace), exists s', 
 length s' < max_derivative_count c /\ (trace_derive c s) =ACI= (trace_derive c s').
Proof with (simpl;intuition || auto). 
induction c;intros.
- simpl. destruct s;simpl.
  * exists []. saia. 
  * exists [Transfer]. saia. 
- simpl. exists []. saia. 
- simpl. destruct s eqn:Heqn.
  * exists []. saia.
  * simpl. eq_event_destruct.
    ** destruct (trace_derive_success t);rewrite H.
      *** exists [e]. simpl. eq_event_destruct; saia. 
      *** destruct (exists_disimilar_event e). exists [x]. simpl.
          eq_event_destruct. contradiction. saia.
    ** destruct (exists_disimilar_event e). exists [x]. simpl.
          eq_event_destruct. contradiction. saia.
- simpl. setoid_rewrite trace_derive_plus. induction s.
  * exists []. simpl. split;auto.
    rewrite (mult_n_O 0) at 1. auto using PeanoNat.Nat.mul_lt_mono, max_derivative_count_non_zero.
  *
    ** 

 exists [].
-
    ** exists [e]. saia.
  simpl. intuition || auto.
 assert (HA : exists 







(*Drawback, contains duplicates*)
Definition derivative_closure_once (l_pair : (list Contract) * (list Contract)) :=
 let (internal_nodes,leafs) := l_pair in
 (internal_nodes++leafs,flat_map (fun c => map (fun e => c/e) alphabet) leafs).



(*include c in left list to represent value of (trace_derive c []) *)
(*More effecient way to compute derivative closure than trivially iterating over all trace with trace_derive*)
Definition approx_derivative_closure (n : nat) (c : Contract) :=
 approx n derivative_closure_once ([c],[c]).

Lemma trace_derive_in_derivative_closure_snd : forall (c : Contract) (s : Trace), In (trace_derive c s) (snd (approx_derivative_closure (length s) c)).
Proof. Admitted.

Lemma derivative_closure_snd_in_fst : forall n n' c c_der , In c_der (snd (approx_derivative_closure n c)) -> 
                                                            n<n' -> In c_der (fst (approx_derivative_closure n' c)).
Proof. Admitted.

Definition derivative_closure (c : Contract) : list Contract := fst (approx_derivative_closure (max_derivative_count c) c).

Lemma simple_derivative_closure_i_derivative_closure : forall c,incl (simple_derivative_closure c) (derivative_closure c).
Proof. Admitted.

Lemma derivative_closure_i_simple_derivative_closure : forall c,incl (derivative_closure c) (simple_derivative_closure c).
Proof. Admitted.

Lemma derivative_closure_spec : forall (c : Contract), contains_all_derivatives_of c (derivative_closure c).
Proof. Admitted.


(*********************************************Extend to pairs of contracts***************************)
Fixpoint trace_p_derive (p: Contract * Contract) (s : Trace) :=
match s with
| [] => p
| e::s' => trace_p_derive (fst p / e, snd p /e) s'
end.


Definition p_derivative_closure_once (l_pair : (list (Contract*Contract)) * (list (Contract * Contract))) :=
 let (internal_nodes,leafs) := l_pair in
 (internal_nodes++leafs,flat_map (fun p => map (fun e => ((fst p) / e,(snd p) / e)) alphabet) leafs).

Definition approx_p_derivative_closure (n : nat) (p : (Contract * Contract)) :=
 approx n p_derivative_closure_once ([p],[p]).

Lemma trace_derive_in_p_derivative_closure_snd : forall (c0 c1: Contract) (s : Trace), In (trace_p_derive (c0,c1) s) (snd (approx_p_derivative_closure (length s) (c0,c1))).
Proof. Admitted.

Lemma p_derivative_closure_snd_in_fst : forall n n' p p_der , In p_der (snd (approx_p_derivative_closure n p)) -> 
                                                            n<n' -> In p_der (fst (approx_p_derivative_closure n' p)).
Proof. Admitted.

Definition max_p_derivative_count (p : Contract * Contract) := (max_derivative_count (fst p)) * (max_derivative_count (snd p)).

Definition all_p_derivatives (p : Contract * Contract) : list (Contract * Contract) := fst (approx_p_derivative_closure (max_p_derivative_count p) p).

Lemma all_p_derivatives_spec : forall (c0 c1 : Contract)(s : Trace), In (trace_p_derive (c0,c1) s) (all_p_derivatives (c0,c1)).
Proof. Admitted.


(*Show lemma that all derivatives are in derivative_closure*)
Lemma derivative_closure_is_bisimulation : forall (c0 c1 : Contract), 
 Forall (fun (p : Contract * Contract) => nu (fst p) = nu (snd p)) (all_p_derivatives (c0,c1)) -> bisimulation (fun x y => (In (x,y) (all_p_derivatives (c0,c1)))).
Proof. Admitted.

Definition decide_contract_equivalence (c0 c1 : Contract) := 
 forallb (fun (p : Contract * Contract) => eqb (nu (fst p)) (nu (snd p))) (all_p_derivatives (c0,c1)).


Lemma Bisimilarity_reflect : forall (c0 c1 : Contract), reflect (Bisimilarity c0 c1) (decide_contract_equivalence c0 c1).
Proof. Admitted.







































(*Maybe keep*)
Lemma finitely_many_derivatives : forall c, exists (l : list Contract), (forall s, member aci_eq (trace_derive c s) l = true).
Proof. Admitted.


Global Opaque alphabet.
Definition direct_derivatives (c : Contract) : list Contract := map (fun e => c/e) alphabet.






Definition direct_p_derivatives (p : Contract * Contract) : list (Contract * Contract) := 
 map (fun e => ((fst p) / e,(snd p) / e)) alphabet.
(*processed contract -> all direct derivatives are in either internal_nodes or leafs
  not processed contract -> no direct derivatives in either internal_nodes or leafs*)
Definition p_derivative_closure_once (l_pair : (list (Contract*Contract)) * (list (Contract * Contract))) :=
 let (internal_nodes,leafs) := l_pair in
 let internal_nodes' := internal_nodes++leafs in
 let leaf_children := flat_map direct_p_derivatives leafs
 in (internal_nodes',filter (fun c => negb (member aci_p_eq c internal_nodes')) leaf_children).

Definition approx_p_derivative_closure (n : nat) (p : (Contract * Contract)) :=
 approx n p_derivative_closure_once ([],[p]).


(*All internal_nodes and leafs share the property that they can be derived from trace_derive c s
  with some trace s. Only new derivatives are placed in leafs, and finitely_many_derivatives states
  that there are only finitely many of those, therefore at some point, this list will be empty
  in which case a fixpoint has been reached*)
Lemma p_derivative_closure_convergence : forall (c0 c1 : Contract), exists (n:nat),
 approx_p_derivative_closure n (c0,c1) =  approx_p_derivative_closure (n+1) (c0,c1). 
Proof. Admitted.

Definition p_derivative_relation (arg_rec arg_inp : list (Contract*Contract) * list (Contract*Contract)) :=
  p_derivative_closure_once arg_inp <> arg_inp /\  (*Not converged*)
  p_derivative_closure_once arg_inp = arg_rec. (*is preceeding element*)

Lemma well_founded_p_derivative_relation: well_founded p_derivative_relation.
Proof. Admitted.

Instance wf_p_derivative_relation : WellFounded p_derivative_relation := well_founded_p_derivative_relation.

Lemma list_not_eq : forall (A:Type) (l0 l1 : list A) (p : A), l0++p::l1 = l0 -> False.
Proof.
intro. induction l0;intros.
- discriminate.
- inversion H. eauto. 
Qed.


Lemma cons_i_not_convergence : forall (p : Contract*Contract)(internal_nodes leafs : list (Contract*Contract)),
   p_derivative_closure_once (internal_nodes,p::leafs) <> (internal_nodes,p::leafs).
Proof.
intros. simpl. intro H. injection H. intros.
eauto using list_not_eq.
Qed.

Equations p_derivative_closure (internal_nodes_leafs : list (Contract*Contract) * list (Contract*Contract)) : list (Contract*Contract) by  wf internal_nodes_leafs p_derivative_relation :=
p_derivative_closure (internal_nodes, []) := internal_nodes;
p_derivative_closure (internal_nodes, leafs) := p_derivative_closure (p_derivative_closure_once (internal_nodes, leafs)).
Next Obligation.
unfold p_derivative_relation. split.
- apply cons_i_not_convergence.
- auto.
Qed.
Global Transparent p_derivative_closure.


Definition derivative_closure (c0 c1 : Contract) : list (Contract*Contract) := p_derivative_closure ([],[(c0,c1)]).


(*Show lemma that all derivatives are in derivative_closure*)
Lemma derivative_closure_is_bisimulation : forall (c0 c1 : Contract), 
 Forall (fun (p : Contract * Contract) => nu (fst p) = nu (snd p)) (derivative_closure c0 c1) -> bisimulation (fun x y => (In (x,y) (derivative_closure c0 c1))).
Proof. Admitted.

Definition decide_contract_equivalence (c0 c1 : Contract) := 
 forallb (fun (p : Contract * Contract) => eqb (nu (fst p)) (nu (snd p)) ) (derivative_closure c0 c1).

Lemma Bisimilarity_reflect : forall (c0 c1 : Contract), reflect (Bisimilarity c0 c1) (decide_contract_equivalence c0 c1).
Proof. Admitted.



