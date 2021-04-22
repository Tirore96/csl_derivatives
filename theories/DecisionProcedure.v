Require Import CSL.IterativeContract.
Require Import CSL.IterativeEquations.
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



Equations trace_derive (c : Contract) (s : Trace) : Contract :=
trace_derive c [] := c;
trace_derive c (e::s') := trace_derive (c/e) s'.
Global Transparent trace_derive.
Definition contains_all_derivatives_of c (l : list Contract) := forall (s : Trace), In (trace_derive c s) l.


(*
Inductive Trace_Derive : Contract -> Trace -> Contract -> Prop :=
| Trace_Derive_Nil c : Trace_Derive c [] c
| Trace_Derive_Cons c s c' e (H: Trace_Derive (c/e) s c') : Trace_Derive c (e::s) c'. (*rule motivated by constructor being analgous to cons on lists*)
Hint Constructors Trace_Derive : coDB.*)

Ltac autodp := auto with dpDB.
Ltac eautodp := eauto with dpDB.

(*
Lemma derive_trace_derive : forall (c : Contract)(s : Trace)(e :EventType), trace_derive c (s++[e]) = (trace_derive c s) / e.
Proof.
intros. generalize dependent c. induction s;simpl;auto.
Qed.*)
(*
Lemma trace_derive_spec : forall (c c' : Contract)(s : Trace), (trace_derive c s) = c' <-> Trace_Derive c s c'.
Proof.
split;intros.
- funelim (trace_derive c s);simpl;auto with coDB.
- induction H;auto. 
Qed.*)

Hint Resolve in_eq in_cons : core.

Definition alphabet := [Notify;Transfer].
Lemma in_alphabet : forall (e : EventType), In e alphabet.
Proof.
intros. unfold alphabet; destruct e; auto. 
Qed.
Global Opaque alphabet.

Definition In_mod_R (c : Contract) (l : list Contract) := exists c', c' =R= c /\ In c' l.

Lemma In_mod_R_eq : forall c l, In_mod_R c (c :: l).
Proof.
intros. exists c;auto.
Qed.

Ltac d_ctx := unfold In_mod_R in *;destruct_ctx.

Lemma In_mod_R_cons : forall c c' l, In_mod_R c l -> In_mod_R c (c' :: l).
Proof.
intros. d_ctx. exists x. split;auto.
Qed.

Hint Resolve In_mod_R_eq In_mod_R_cons : dpDB.


Lemma In_mod_R_app : forall l0 l1 c, In_mod_R c l0 \/ In_mod_R c l1 -> In_mod_R c (l0++l1).
Proof.
induction l0;intros. simpl. destruct H.
d_ctx. simpl in H0. contradiction. auto.
inversion H.
- d_ctx. exists x. split;auto. apply in_or_app. now left.
- d_ctx. exists x. split;auto. apply in_or_app. now right.
Qed.

Notation "l0 =L= l1" := (plus_fold l0 =R= plus_fold l1) (at level 73, no associativity).


Definition In_mod_ACI (c : Contract) (l : list Contract) := exists c', c' =ACI= c /\ In c' l.

Ltac dd_ctx := unfold In_mod_ACI in *;destruct_ctx.

CoInductive AllDerivatives : Contract -> list Contract -> Prop :=
| AD_fix c l (H0: forall e, AllDerivatives (c/e) l) (H1 : In_mod_ACI c l)  : AllDerivatives c l.

Definition is_FailureConf (ll : list (list Contract)) := ll<>[] /\  forall l, In l ll -> In Failure l.

Print NoDup.

Inductive In_mod_LACI : list Contract -> list (list Contract) -> Prop :=
| Iml_nil : In_mod_LACI [] []
| Iml_extend_ll l l' ll (H: In_mod_LACI l ll) : In_mod_LACI l (l'::ll)
| Iml_extend_l c l ll (H0: exists l', In l' ll /\ In c l') (H1: In_mod_LACI l ll) : In_mod_LACI (c::l) ll.

Equations n_prod_list (A:Type)(ll : list (list A)) : list (list A) by wf (length ll) lt :=
n_prod_list [] := [[]];
n_prod_list (l::ll') := map (fun p => (fst p)::(snd p)) (list_prod l (n_prod_list (ll'))).
Global Transparent n_prod_list.

Definition f_extend (ll : list (list Contract)) := map (fun l => l++[Failure]) ll.

Lemma in_n_prod_list_extend : forall (l l' : list Contract) e(ll : list (list Contract)),
 In l (n_prod_list ll) -> In e l' -> In (e::l) (n_prod_list (l'::ll)).
Proof.
induction l;intros.
- simp n_prod_list. rewrite in_map_iff.
  exists (e,[]). split;auto. apply in_prod;auto.
- simp n_prod_list. rewrite in_map_iff.
  exists (e,a::l). split;auto. apply in_prod;auto.
Qed.

Lemma in_n_prod_cons : forall (l l' : list Contract) e(ll : list (list Contract)),
 In (e::l) (n_prod_list (l'::ll)) -> In e l' /\ In l (n_prod_list ll).
Proof.
intros. simp n_prod_list in H. rewrite in_map_iff in H.
d_ctx. inversion H. subst. destruct x.
rewrite in_prod_iff in H0. simpl.
destruct H0;auto.
Qed.

Lemma in_n_prod_iff : forall (l l' : list Contract) e(ll : list (list Contract)),
 In (e::l) (n_prod_list (l'::ll)) <-> In e l' /\ In l (n_prod_list ll) .
Proof.
split;intros. auto using in_n_prod_cons.
destruct H. auto using in_n_prod_list_extend.
Qed.

Lemma in_n_prod_app : forall (l l' : list Contract) (ll ll' : list (list Contract)),
 In l (n_prod_list ll) -> In l' (n_prod_list ll')  -> In (l++l') (n_prod_list (ll++ll')).
Proof.
induction l;intros;simpl.
- destruct ll. simpl in H. destruct H;try contradiction.
  auto. simp n_prod_list in H. rewrite in_map_iff in H.
  d_ctx. discriminate.
- destruct ll. simpl. simpl in H. destruct H;try contradiction. 
  discriminate. rewrite <- app_comm_cons. rewrite in_n_prod_iff. 
  rewrite in_n_prod_iff in H. destruct H;auto.
Qed.

Lemma in_n_prod_repeat : forall (A:Type) (n:nat) (e:A) (l:list A) ,
 In e l-> In (repeat e n) (n_prod_list (repeat l n)).
Proof.
intro. induction n;intros;simpl. now left.
apply IHn in H as H'. simp n_prod_list.
 rewrite in_map_iff. exists (e,repeat e n).
split;auto. rewrite in_prod_iff. split;auto.
Qed.

Lemma In_mod_LACI_f_extend : forall ll, In_mod_LACI [] (f_extend ll).
Proof.
induction ll;intros;simpl. constructor. constructor.
auto.
Qed.

Lemma Failure_plus_fold : forall l, Failure _+_ (plus_fold l) =ACI= plus_fold l.
Proof.
induction l;intros;simpl;auto. rewrite cc_plus_comm.
rewrite cc_plus_assoc.
apply cc_ctx_plus;auto. rewrite cc_plus_comm. auto.
Qed.


Lemma In_plus_Failure : forall l ll, In_mod_ACI (plus_fold l) ll-> In_mod_ACI (Failure _+_ plus_fold l) ll.
Proof.
induction l;intros. 
- simpl in *. dd_ctx. exists x. split. rewrite H. all: auto.
- dd_ctx. exists x. split. simpl in H. rewrite H. rewrite Failure_plus_fold.
  now simpl. auto.
Qed. 

Lemma In_plus_Failure2 : forall l ll, In_mod_ACI (Failure _+_ plus_fold l) ll -> In_mod_ACI (plus_fold l) ll.
Proof.
induction l;intros.
- simpl. dd_ctx. exists x. split;auto. simpl in H. rewrite H. auto.
- simpl. dd_ctx. exists x. split;auto. rewrite H. 
  rewrite Failure_plus_fold. reflexivity. 
Qed.

Lemma In_mod_ACI_In_mod_LACI : forall l ll, In_mod_ACI (plus_fold l) (Failure::(map plus_fold (n_prod_list (f_extend ll)))) -> In_mod_LACI l (f_extend ll).
Proof.
induction l;intros. apply In_mod_LACI_f_extend. simpl in H.
destruct (Contract_eq_dec a Failure).
- subst. constructor. apply In_plus_Failure2 in H. apply IHl in H.
  inversion H.
  * subst.
  exists l.
  *
constructor.
-
 simpl in H. unfold In_mod_ACI in H. d_ctx.

Lemma In_mod_LACI_flatten : forall l ll, In_mod_LACI l ll -> In_mod_ACI (plus_fold l) (map plus_fold (n_prod_list (f_extend ll))).
Proof.
intros. induction H.
- simpl. exists (Failure _+_ Failure). split; auto.
- simpl. unfold In_mod_ACI. 
induction ll;intros.
- unfold is_FailureConf in*. destruct H. contradiction.
- simpl. unfold is_FailureConf in*. simpl.





Lemma AllDerivatives_plus_fold : forall (l : list Contract)(ll : list (list Contract)),
is_FailureConf ll -> In_mod_LACI l ll -> In_mod_ACI (plus_fold l) (map plus_fold ll).
Proof.
induction l;intros.
- simpl. unfold In_mod_LACI in *. exists Failure. simpl. split;auto.
  unfold is_FailureConf in *. unfold In_mod_ACI.
cofix IH.
intros. constructor.
- intros. rewrite plus_fold_derive. apply IH;auto.
  intros.

Definition In_mod_L (l : list Contract) (ll : list (list Contract)) := exists l', l' =L= l /\ In l' ll.

Ltac dd_ctx := unfold In_mod_L,In_mod_R in *;destruct_ctx.

Lemma In_mod_L_eq : forall l ll, In_mod_L l (l :: ll).
Proof.
intros. exists l;auto.
Qed.

Lemma In_mod_L_cons : forall l l' ll, In_mod_L l ll -> In_mod_L l (l' :: ll).
Proof.
intros. unfold In_mod_L in *. destruct H. destruct H. exists x.
split;auto.
Qed.

Hint Resolve In_mod_L_eq In_mod_L_cons : dpDB.


Lemma In_mod_L_app : forall ll0 ll1 l, In_mod_L l ll0 \/ In_mod_L l ll1 -> In_mod_L l (ll0++ll1).
Proof.
induction ll0;intros. simpl. destruct H.
unfold In_mod_L in *.
d_ctx. simpl in H0. contradiction. auto.
inversion H.
- dd_ctx. exists x. split;auto. apply in_or_app. now left.
- dd_ctx. exists x. split;auto. apply in_or_app. now right.
Qed.

Fixpoint flatten (c : Contract) : list Contract :=
match c with
| c0 _+_ c1 => (flatten c0) ++ (flatten c1)
| _ => [c]
end.


CoInductive AllFlatDerivatives : list Contract -> list (list Contract) -> Prop :=
| AFD_fix l ll (H0: forall e, AllFlatDerivatives (flat_map (fun c => flatten (c/e)) l) ll) (H1 : In_mod_L l ll)  : AllFlatDerivatives l ll.

Lemma All_AllFlat : forall c0 l, AllDerivatives c0 l -> AllFlatDerivatives (flatten c0) (map flatten l).
Proof.
cofix IH.
intros. constructor.
- intros. inversion H. subst.
- 

(*
Lemma In_AllDerivatives_i_Trace_Derive : forall (c: Contract)(l : list Contract), 
AllDerivatives c l -> (forall (s : Trace)(c_der : Contract), Trace_Derive c s c_der -> exists c', c' =R= c_der /\ In c' l).
Proof.
intros. generalize dependent c. induction s;intros.
- inversion H0. subst. inversion H. d_ctx. exists x;auto.
- inversion H0. inversion H. subst. eapply IHs. eapply H6. eauto.
Qed.*)

Lemma In_AllDerivatives : forall (c: Contract)(l : list Contract)(s : Trace), 
AllDerivatives c l -> In_mod_R (c//s) l. 
Proof.
intros. generalize dependent c. induction s;intros.
- inversion H. now simpl. 
- inversion H. subst. eapply IHs. eauto.
Qed.

(*
Lemma Trace_Derive_i_In_AllDerivatives : forall (c: Contract)(l : list Contract), 
(forall (s : Trace)(c_der : Contract), Trace_Derive c s c_der -> exists c', c' =R= c_der /\ In c' l) -> AllDerivatives c l.
Proof.
cofix H_co.
intros. constructor.
- intros. apply H_co. intros. eapply H. constructor. eauto.
- eauto with icDB.
Qed.*)

(*
Theorem AllDerivatives_iff : forall (c: Contract)(l : list Contract), 
AllDerivatives c l <-> (forall (s : Trace)(c_der : Contract), Trace_Derive c s c_der -> exists c', c' =R= c_der /\ In c' l).
Proof.
split;intros. 
- eapply In_AllDerivatives_i_Trace_Derive;eauto.
- eapply Trace_Derive_i_In_AllDerivatives;eauto.
Qed.*)

(*
Inductive OnlyDerivatives : Contract -> list Contract -> Prop :=
| OD_nil c : OnlyDerivatives c [c]
| OD_cons c c' l e (H: In_mod_R c' l) (H1: OnlyDerivatives c 
*)


Lemma AllDerivatives_Failure : AllDerivatives Failure [Failure].
Proof.
cofix IH. constructor;auto;simpl;auto.
exists Failure;split;auto.
Qed.

Hint Resolve AllDerivatives_Failure : dpDB.



Lemma AllDerivatives_cons : forall (c c_der : Contract)(l : list Contract), AllDerivatives c l -> AllDerivatives c (c_der::l).
Proof.
cofix IH.
intros. inversion H. constructor;auto.
apply In_mod_R_cons;auto.
Qed.

Hint Resolve AllDerivatives_cons : dpDB.

(*
Lemma AllDerivatives_derive : forall c l e, AllDerivatives c l -> AllDerivatives (c/e) l.
Proof.
cofix IH. intros. inversion H.
- d_ctx.
constructor; autodp. specialize H0 with e. destruct H0. auto.
Qed.*)

Lemma AllDerivatives_Success : AllDerivatives Success [Success;Failure].
Proof.
constructor; autodp.
Qed.


Hint Resolve AllDerivatives_Success : dpDB.

Ltac eq_event_destruct :=
  repeat match goal with
         | [ |- context[if EventType_eq_dec ?e ?e then _ else _] ] => destruct (EventType_eq_dec e e);try contradiction
         | [ |- context[if EventType_eq_dec ?e ?e0 then _ else _] ] => destruct (EventType_eq_dec e e0)
         end.

Lemma AllDerivatives_Event : forall (e : EventType), AllDerivatives (Event e) [Event e;Success;Failure].
Proof.
cofix IH.
intros.
constructor; intros;simpl.
- eq_event_destruct; autodp. 
- exists (Event e). split;auto. 
Qed.

Hint Resolve AllDerivatives_Event : dpDB.

Definition plus_prod (l0 l1 : list Contract) :=
match l0,l1 with
| [],_ => l1
| _,[] => l0
|_,_ =>  map (fun p => (fst p) _+_ (snd p)) (list_prod l0 l1)
end.

Equations n_prod (ll : list (list Contract)) : list Contract by wf (length ll) lt :=
n_prod [] := [];
n_prod (l::[]) := l;
n_prod (l::ll') := plus_prod l (n_prod (ll')).

Global Transparent n_prod.

Hint Unfold plus_prod : core.


Lemma concat_n_prod : forall l ls, n_prod (l::ls) = plus_prod l ((n_prod ls)).
Proof.
intros. funelim (n_prod (l::ls)). simp n_prod. destruct l;auto.
rewrite H. auto.
Qed.

Lemma in_n_prod : forall c0 c1 l0 l1, In c0 l0 -> In c1 l1 -> In (c0 _+_ c1) (n_prod [l0; l1]).
Proof. Admitted.
(*
Inductive List_AllDerivatives : list Contract -> list (list Contract) -> Prop :=
| List_AllDerivatives_nil : List_AllDerivatives [] []
| List_AllDerivatives_cons c l cs ls (H0 : AllDerivatives c l) (H1 : List_AllDerivatives cs ls) : List_AllDerivatives (c::cs) (l::ls).

Hint Constructors List_AllDerivatives : coDB.

Lemma AllDerivatives_Flatten_iff : forall l ll, List_AllDerivatives l ll <-> AllDerivatives (plus_fold l) (n_prod ll).
Proof. Admitted.*)



Lemma flatten_non_empty : forall (c:Contract), exists c' l, flatten c = c'::l.
Proof.
induction c;intros.
- exists Success. exists []. auto.
- exists Failure. exists []. auto.
- exists (Event e). exists []. auto.
- d_ctx. exists x1. exists (x2 ++ (flatten c2)).
  simpl. rewrite H0. now simpl.
- exists (c1 _;_ c2). exists []. now simpl.
- exists (Star c). exists []. now simpl.
Qed.

(*
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
*)


Lemma Failure_trace_derive : forall s, Failure//s = Failure.
Proof.
induction s;intros;auto.
Qed.

Hint Immediate o_derive Failure_trace_derive : dpDB.

Lemma o_or : forall (c : Contract), o c = Success \/ o c = Failure.
Proof.
intros. o_destruct. rewrite H. now left. rewrite H. now right.
Qed.

(*
Theorem flatten_seq_derive_shape : forall s c0 c1, exists l, (flatten ((c0 _;_ c1) // s)) = ((c0 // s) _;_ c1):: l /\
 Forall (fun c => exists c' s, c = (o c') _;_ (c1//s)) l.
Proof.
induction s;intros.
- simpl. exists []. split;auto.
- rewrite flatten_seq_trace_derive. rewrite flatten_seq_derivative. simpl.
  rewrite app_nil_r. specialize IHs with (c0/a) c1 as IHs'.
  specialize IHs with (o c0) (c1/a). d_ctx. rewrite H1. rewrite H.
  exists (x ++ o c0 // s _;_ c1 / a :: x0). split;auto.
  rewrite Forall_forall in *. intros. apply in_app_or in H3. destruct H3.
  * apply H0 in H3. d_ctx. exists x2. now exists x3.
  * simpl in H3. destruct H3. 
    ** rewrite <- H3. destruct (o_or c0).
      *** rewrite H4. destruct s.
        **** simpl. exists Success. now exists [a].
        **** simpl. rewrite Failure_trace_derive. exists Failure. 
             now exists [a].
      *** rewrite H4. rewrite Failure_trace_derive. exists Failure.
          now exists [a].
    ** apply H2 in H3. d_ctx. rewrite H3.
       exists x2. now exists (a::x3).
Qed.*)

Definition seq_configurations (c1 : Contract) (l0 l1 : list Contract) := 
 (repeat (Failure::l1) (length l1))++[map (fun c => c _;_ c1) l0].


Inductive Flat_Seq_Derivative : Contract -> Contract -> list Contract -> Prop :=
| FSD_Single c0 c1 s : Flat_Seq_Derivative c0 c1 [c0//s _;_ c1]
| FSD_Cons_S c0 c1 l s (H: Flat_Seq_Derivative c0 c1 l) : Flat_Seq_Derivative c0 c1 ((Success _;_(c1//s))::l)
| FSD_Cons_F c0 c1 l s (H: Flat_Seq_Derivative c0 c1 l) : Flat_Seq_Derivative c0 c1 ((Failure _;_(c1//s))::l).


Lemma helper : forall s c0 e, (c0 // s) / e = c0 // (s ++ [e]).
Proof.
induction s;intros. now simpl.
simpl. now rewrite IHs.
Qed.

Lemma helper2  : forall c e, c/e = c//[e].
Proof. auto. Qed.


Lemma Flat_Seq_Derivative_closed : forall c0 c1 l e, Flat_Seq_Derivative c0 c1 l -> 
Flat_Seq_Derivative c0 c1 (flat_map (fun c => flatten (c/e)) l).
Proof.
intros. induction H.
- simpl. rewrite helper2. o_destruct; rewrite H.
  all: constructor; rewrite helper; constructor.
- simpl. rewrite o_Success. rewrite helper. constructor. constructor.
  auto.
- simpl. rewrite o_Failure. rewrite helper. constructor. constructor.
  auto.
Qed.

Lemma plus_fold_flatten : forall c , plus_fold (flatten c) =R= c.
Proof.
induction c;intros;simpl;auto_rwd.
rewrite c_eq_iff. setoid_rewrite plus_fold_app.
rewrite <- c_eq_iff. rewrite IHc1.
now rewrite IHc2.
Qed.


Lemma plus_fold_derive_flatten : forall (l : list Contract) (e : EventType), (plus_fold l) / e =R= plus_fold (flat_map (fun c => (flatten (c/e))) l).
Proof.
induction l;intros.
- now simpl.
- simpl. rewrite c_eq_iff. setoid_rewrite plus_fold_app.
  rewrite <- c_eq_iff. rewrite IHl. now rewrite plus_fold_flatten.
Qed.

Lemma Flat_Seq_Derivative_repeat_Failure : forall n c0 c1 l , Flat_Seq_Derivative c0 c1 l -> Flat_Seq_Derivative c0 c1  ((repeat (Failure _;_ (c1)) n)++l).
Proof.
induction n;intros.
- now simpl.
- simpl. assert (HA: c1 = c1 // []). { auto. } rewrite HA. constructor. auto.
Qed.

Lemma Flat_Seq_Derivative_repeat_Success : forall n c0 c1 l , Flat_Seq_Derivative c0 c1 l -> Flat_Seq_Derivative c0 c1  ((repeat (Success _;_ (c1)) n)++l).
Proof.
induction n;intros.
- now simpl.
- simpl. assert (HA: c1 = c1 // []). { auto. } rewrite HA. constructor. auto.
Qed.

Lemma plus_fold_repeat_failure : forall n c1, plus_fold (repeat (Failure _;_ c1) n) =R= Failure.
Proof.
induction n;intros;simpl;auto.
rewrite IHn. auto_rwd.
Qed.

Equations n_prod_list (A:Type)(ll : list (list A)) : list (list A) by wf (length ll) lt :=
n_prod_list [] := [[]];
n_prod_list (l::ll') := map (fun p => (fst p)::(snd p)) (list_prod l (n_prod_list (ll'))).
Global Transparent n_prod_list.

Eval compute in (n_prod_list [[0;1];[2;3]]).

Eval compute in (n_prod_list []).

Check incl.

Check In_mod_R.

(*
Lemma n_prod_list_app : forall (A:Type)(ll0 ll1 : list (list A)), 
n_prod_list (ll0++ll1) = n_prod_list((n_prod_list ll0)++(n_prod_list ll1)).
Proof.
induction ll0;intros.
- simpl. simp n_prod_list. simpl.*)

(*
Inductive In_N_Prod_List : list Contract -> list (list Contract) -> Prop :=
| INPL_nil : In_N_Prod_List [] []
| INPL_cons l ll e l' (H0: In_N_Prod_List l ll) (H1: In e l') : In_N_Prod_List (e::l) (l'::ll).
*)

 
(*Nicer to use an inductive definition because of the 
  generated induction principle, and avoiding to deal with out of bounds
  cases*)
(*

Lemma n_prod_list_singleton : forall (A : Type)(l : list A), n_prod_list [l] = map (fun e => [e]) l.
Proof.
intros. destruct l. funelim (n_prod_list [l]). induction l;intros.
- contradiction. 
- simp n_prod_list. simpl. simpl. f_equal.*)


Lemma in_n_prod_list_extend : forall (l l' : list Contract) e(ll : list (list Contract)),
 In l (n_prod_list ll) -> In e l' -> In (e::l) (n_prod_list (l'::ll)).
Proof.
induction l;intros.
- simp n_prod_list. rewrite in_map_iff.
  exists (e,[]). split;auto. apply in_prod;auto.
- simp n_prod_list. rewrite in_map_iff.
  exists (e,a::l). split;auto. apply in_prod;auto.
Qed.

Lemma in_n_prod_cons : forall (l l' : list Contract) e(ll : list (list Contract)),
 In (e::l) (n_prod_list (l'::ll)) -> In e l' /\ In l (n_prod_list ll).
Proof.
intros. simp n_prod_list in H. rewrite in_map_iff in H.
d_ctx. inversion H. subst. destruct x.
rewrite in_prod_iff in H0. simpl.
destruct H0;auto.
Qed.

Lemma in_n_prod_iff : forall (l l' : list Contract) e(ll : list (list Contract)),
 In (e::l) (n_prod_list (l'::ll)) <-> In e l' /\ In l (n_prod_list ll) .
Proof.
split;intros. auto using in_n_prod_cons.
destruct H. auto using in_n_prod_list_extend.
Qed.

Lemma in_n_prod_app : forall (l l' : list Contract) (ll ll' : list (list Contract)),
 In l (n_prod_list ll) -> In l' (n_prod_list ll')  -> In (l++l') (n_prod_list (ll++ll')).
Proof.
induction l;intros;simpl.
- destruct ll. simpl in H. destruct H;try contradiction.
  auto. simp n_prod_list in H. rewrite in_map_iff in H.
  d_ctx. discriminate.
- destruct ll. simpl. simpl in H. destruct H;try contradiction. 
  discriminate. rewrite <- app_comm_cons. rewrite in_n_prod_iff. 
  rewrite in_n_prod_iff in H. destruct H;auto.
Qed.

Lemma in_n_prod_repeat : forall (A:Type) (n:nat) (e:A) (l:list A) ,
 In e l-> In (repeat e n) (n_prod_list (repeat l n)).
Proof.
intro. induction n;intros;simpl. now left.
apply IHn in H as H'. simp n_prod_list.
 rewrite in_map_iff. exists (e,repeat e n).
split;auto. rewrite in_prod_iff. split;auto.
Qed.

Print or.


(*
Lemma in_n_prod_list2 : forall (l : list Contract)(ll : list (list Contract)),
In l (n_prod_list ll) -> In_N_Prod_List l ll.
Proof.
induction l;intros.
- destruct ll.  constructor.
  simp n_prod_list in H. rewrite in_map_iff in H.
  d_ctx. discriminate.
- destruct ll. simp n_prod_list in H. simpl in H.
  destruct H. discriminate. contradiction.
  eapply in_n_prod_list3 in H; destruct H.
  constructor;eauto.
Qed.*)
(*
Lemma in_n_prod_list : forall (l : list Contract)(ll : list (list Contract)),
In_N_Prod_List l ll -> In l (n_prod_list ll).
Proof.
intros. induction H.
- simpl. now left.
-
 constructor.*)

(*
(default:A),
(forall l', In l' ll -> ~(In default l')) ->
(forall n, In (nth n l default) (nth n ll [default])) ->
In l (n_prod_list ll).
Proof.
intros. funelim (n_prod_list ll).
- simpl. specialize H0 with 0. simpl in H0.
  destruct H0;try contradiction. destruct l;auto.
  simpl in H0. induction l.
- intros. funelim (n_prod_list ll).
  *  simpl. now left.
  * specialize H1 with 0. simpl in H1. apply H0 in H1;auto. contradiction.
- intros. 
 simpl. now left.
  *
- simpl. left. destruct l;auto.
  simpl in H. destruct n. unfold n_prod_list. 
*)
(*
Lemma InAllDerivatives : forall c l, AllDerivatives c l -> In_mod_R c l.
Proof.
intros. inversion H.
- exists c. split;auto.
-

Lemma InAllDerivatives : forall s c l, AllDerivatives c l -> In_mod_R (c//s) l.
Proof.
induction s;intros.
- simpl. inversion H. 
intros inversion H.
-
*)
Lemma AllDerivatives_nil : forall c, AllDerivatives c [] -> False.
Proof.
intros. inversion H. unfold In_mod_R in H1. d_ctx.
simpl in H4. contradiction.
Qed.



Lemma plus_list_equivalence_incl : forall (l0 l1 : list Contract), (forall c, In_mod_R c l0 <-> In_mod_R c l1) <-> l0 =L= l1.
Proof. Admitted.

Lemma plus_list_eq_repeat_failure : forall n l0 l1, l0 =L= l1 -> l0 =L= repeat Failure n ++ l1.
Proof.
induction n;intros.
- now simpl.
- simpl. rewrite IHn;eauto. auto_rwd.
Qed.

Lemma repeat_failure_nil : forall n , repeat Failure n =L= [].
Proof.
induction n;intros;simpl;auto_rwd.
auto.
Qed.


(*
Lemma In_mod_L_n_prod_iff : forall (l l' : list Contract) e(ll : list (list Contract)),
 In (e::l) (n_prod_list (l'::ll)) <-> In e l' /\ In l (n_prod_list ll) .
Proof.
split;intros. auto using in_n_prod_cons.
destruct H. auto using in_n_prod_list_extend.
Qed.*)


Lemma In_mod_L_n_prod_list_extend : forall (ll : list (list Contract)) c(l  : list (Contract)),
 In_mod_L l (n_prod_list ll) -> In c l -> In_mod_L (c::l) (n_prod_list (l::ll)).
Proof. Admitted.
(*intros. Check in_n_prod_list_extend.
dd_ctx. eapply in_n_prod_list_extend in H1.
exists (c::l). split;auto. eauto. eauto.
Qed.*)
(*Continue from here in_n_prod_cons*)
(*
Lemma In_mod_L_n_prod_cons : forall (ll : list (list Contract)) c(l l' : list (Contract)),
 In_mod_L (c::l) (n_prod_list (l'::ll)) -> In c l' /\ In_mod_L l (n_prod_list ll).
Proof.
intros. simp n_prod_list in H. dd_ctx. rewrite in_map_iff in H0.
dd_ctx. inversion H0. subst. split.
- destruct x0. rewrite in_prod_iff in H1. simpl.
destruct H1;auto. exists c. split;auto.
- destruct x0. rewrite in_prod_iff in H1. simpl.
  exists l. destruct H1. split;auto.
Qed.*)
(*
Lemma In_mod_L_n_prod_iff : forall (ll : list (list Contract)) c(l l' : list (Contract)),
 In_mod_L (c::l) (n_prod_list (l'::ll)) <-> In_mod_R c l' /\ In_mod_L l (n_prod_list ll).
Proof.
split;intros. auto using In_mod_L_n_prod_cons.
destruct H. eapply In_mod_L_n_prod_list_extend. eauto using In_mod_L_n_prod_list_extend.
Qed.



Lemma in_n_prod_repeat : forall (A:Type) (n:nat) (e:A) (l:list A) ,
 In e l-> In (repeat e n) (n_prod_list (repeat l n)).
Proof.
intro. induction n;intros;simpl. now left.
apply IHn in H as H'. simp n_prod_list.
 rewrite in_map_iff. exists (e,repeat e n).
split;auto. rewrite in_prod_iff. split;auto.
Qed.*)

Lemma In_mod_L_n_prod_app : forall (l l' : list Contract) (ll ll' : list (list Contract)),
 In_mod_L l (n_prod_list ll) -> In_mod_L l' (n_prod_list ll')  -> In_mod_L (l++l') (n_prod_list (ll++ll')).
Proof. Admitted.
(*
induction l;intros;simpl.
- destruct ll. simp n_prod_list in H.
  destruct H;try contradiction.
  auto. simp n_prod_list in H. rewrite in_map_iff in H.
  d_ctx. discriminate.
- destruct ll. dd_ctx. simpl in H2. destruct H2;try contradiction.
  discriminate. rewrite <- app_comm_cons. rewrite in_n_prod_iff. 
  rewrite in_n_prod_iff in H. destruct H;auto.
Qed.*)

Lemma Flat_Seq_Derivative_sc : forall c0 c1 l l0 l1, AllDerivatives c0 l0 -> AllDerivatives c1 l1 ->
In l (n_prod_list (seq_configurations c1 l0 l1)) -> Flat_Seq_Derivative c0 c1 l.
Proof. Admitted.

Lemma in_l_list_eq : forall (c : Contract)(l : list Contract), In c l -> c::l =L= l.
Proof.
Admitted.

Lemma test_occ : forall c c1 l l0 l1,
In_mod_L l (n_prod_list (seq_configurations c1 l0 l1)) -> In c l1 -> (~ In c l) -> exists c', In c' (Failure::l1) /\  count_occ Contract_eq_dec l c' > 1.
Proof.
Admitted.

Lemma reduce_occ : forall (l : list Contract) c, repeat c ((count_occ Contract_eq_dec l c)) ++ (remove Contract_eq_dec c l) =L= l.
Proof.
induction l;intros;simpl.
- auto.
- destruct (Contract_eq_dec a c).
  * destruct (Contract_eq_dec c a).
    ** simpl. subst. simpl in IHl. auto_rwd. specialize IHl with c.
       apply c_eq_plus_morphism;auto.
    ** simpl. subst. contradiction.
  * destruct (Contract_eq_dec c a).
    ** simpl. subst. contradiction.
    ** rewrite c_eq_iff. setoid_rewrite plus_fold_app. simpl.
       setoid_rewrite <- plus_assoc. 
       rewrite <- c_eq_iff. rewrite <- IHl.
       rewrite (plus_comm_ceq _ a).
       rewrite c_eq_iff.  repeat  setoid_rewrite  plus_assoc. 
       rewrite <- c_eq_iff. 
 auto_rwd. apply c_eq_plus_morphism;auto.
       rewrite c_eq_iff. setoid_rewrite plus_fold_app.
       rewrite <- c_eq_iff. auto_rwd. apply c_eq_plus_morphism; eauto.
Qed.

Lemma list_eq_cons_comm : forall l c0 c1, c0 :: c1 :: l =L= c1:: c0 ::l.
Proof.
induction l;intros.
- simpl. auto_rwd.
- simpl. specialize IHl with c1 a. simpl in IHl. rewrite IHl.
  repeat rewrite (plus_comm_ceq a _ ). repeat rewrite <- plus_assoc_ceq.
  apply c_eq_plus_morphism;auto. now rewrite (plus_comm_ceq c1).
Qed.


Lemma reduce_occ2 : forall (l : list Contract) c, c::(remove Contract_eq_dec c l) =L= c::l.
Proof.
induction l;intros. auto.
simpl.
destruct (Contract_eq_dec c a).
- subst. specialize IHl with a. simpl in IHl. rewrite IHl.
  rewrite <- plus_assoc_ceq. auto_rwd.
- simpl. rewrite <- (plus_assoc_ceq c). rewrite (plus_comm_ceq _ a).
  rewrite plus_assoc_ceq. specialize IHl with c as IHl'. simpl in IHl'.
   rewrite IHl'. auto_rwd. rewrite plus_comm_ceq.
   rewrite plus_assoc_ceq. 
 apply c_eq_plus_morphism;auto. apply plus_comm_ceq.
Qed.
(*


Lemma flat_seq_in_seq_configuration : forall c c1 l l0 l1,
In c l1 -> In_mod_L l (n_prod_list (seq_configurations c1 l0 l1)) -> In_mod_L (c::l) (n_prod_list (seq_configurations c1 l0 l1)).
Proof.
intros. dd_ctx. destruct (in_dec Contract_eq_dec c l).
- dd_ctx. exists x. rewrite in_l_list_eq;auto.
- eapply test_occ in H0;eauto. dd_ctx. apply reduce_occ in H1.
 split;auto.

*)

Lemma flat_seq_in_seq_configuration : forall c0 c1 l l0 l1, AllDerivatives c0 l0 -> AllDerivatives c1 l1 -> Flat_Seq_Derivative c0 c1 l -> 
In_mod_L l (n_prod_list (seq_configurations c1 l0 l1)).
Proof. 
intros. induction H1. 
- unfold seq_configurations.
  apply In_AllDerivatives with (s:=s) in H as H9.
  rewrite <- (app_nil_l [c0 // s _;_ c1]).
  apply In_mod_L_n_prod_app.
  unfold In_mod_L. exists (repeat Failure (length l1)). split.
  apply repeat_failure_nil. apply in_n_prod_repeat. auto.
  simp n_prod_list. unfold In_mod_L. destruct H9.
  exists [x _;_ c1]. split;auto. simpl. auto_rwd. destruct H1.
  now rewrite H1. rewrite in_map_iff. exists (x _;_ c1,[]).
   simpl. split;auto. rewrite in_prod_iff. split;auto.
   rewrite in_map_iff. exists x. destruct H1. split;auto.
Admitted.
(*
 rewrite H1. simpl.
  symmetry.
  symmetry. split;auto. simpl. auto_rwd. 
  apply In_mod_L_app.
  exists ((repeat Failure (length l1))++[c0//s _;_ c1]).
  split. symmetry. now apply plus_list_eq_repeat_failure.
  
  * apply in_n_prod_app.
    ** apply in_n_prod_repeat;auto.
    ** simp n_prod_list. rewrite in_map_iff.
       exists (c0//s _;_ c1,[]). split;auto. rewrite in_prod_iff. simpl.
       split;auto. rewrite in_map_iff. exists x. split;auto.
  * apply plus_list_eq_repeat_failure. simpl.
    rewrite H1. auto_rwd.
- pose proof H as H'. pose proof H0 as H0'. apply IHFlat_Seq_Derivative in H.
  apply IHFlat_Seq_Derivative in H0. all:auto.
  apply In_AllDerivatives with (s:=s) in H0' as H9.
  d_ctx. exists x1. split;auto. intros. simpl in H6.
  destruct H6;auto. subst. exists x.  split;auto.
  rewrite H2. auto_rwd. auto.
    d_ctx. exists x. apply In_mod_R_app.
      *** simpl.
       exists (c0 // s _;_ c1,[]). split;auto.
       simpl.
       rewrite in_prod_iff. split;auto. rewrite in_map_iff.
       exists (c0//s). split;auto.*)

Lemma seq_configuration_in_flat_seq : forall c0 c1 l l0 l1, Flat_Seq_Derivative c0 c1 l -> exists l', In l' (n_prod_list (seq_configurations c1 l0 l1)) /\
(forall c, In c l -> In_mod_R c l').
Proof. Admitted.


Lemma in_seq_configuration_iff : forall c0 c1 l l0 l1, Flat_Seq_Derivative c0 c1 l -> exists l', In l' (n_prod_list (seq_configurations c1 l0 l1)) /\
(forall c, In c l -> In_mod_R c l') /\ (forall c, In c l' -> In_mod_R c l).
Proof. Admitted.



Lemma Flat_seq_in_conf : forall c0 c1 l l0 l1, Flat_Seq_Derivative c0 c1 l -> exists l', In l' (n_prod_list (seq_configurations c1 l0 l1)) 
/\ plus_fold l =R= plus_fold l' /\ Flat_Seq_Derivative c0 c1 l'.
Proof. Admitted.

Lemma in_n_prod_list_plus_fold : forall l l_conf, In l (n_prod_list l_conf) 
-> In (plus_fold l) (map plus_fold (n_prod_list l_conf)).
Proof. Admitted.

Lemma All_Derivatives_Flat_Seq_test : forall c0 c1 l l0 l1, 
AllDerivatives (plus_fold l) (map plus_fold (n_prod_list (seq_configurations c1 l0 l1))).
Proof.


Lemma All_Derivatives_Flat_Seq : forall c0 c1 l l0 l1, Flat_Seq_Derivative c0 c1 l -> AllDerivatives c0 l0
-> AllDerivatives c1 l1 -> AllDerivatives (plus_fold l) (map plus_fold (n_prod_list (seq_configurations c1 l0 l1))).
Proof.
cofix IH.
intros. apply Flat_seq_in_conf with (l0:=l0) (l1:=l1) in H as H'.
d_ctx. eapply AD_sub. symmetry. eauto. econstructor.
- intros. eapply AD_sub. symmetry. eapply plus_fold_derive_flatten.
  eapply IH;eauto. apply Flat_Seq_Derivative_closed;auto. 
- apply in_n_prod_list_plus_fold;auto.
Qed.

Lemma All_Derivatives_Seq : forall c0 c1 l0 l1, AllDerivatives c0 l0 -> AllDerivatives c1 l1
-> AllDerivatives ( c0 _;_c1) (map plus_fold (n_prod_list (seq_configurations c1 l0 l1))).
Proof.
intros. eapply AD_sub with (c0 _;_ c1 _+_ Failure);auto_rwd.
assert (HA: c0 _;_ c1 _+_ Failure = plus_fold [c0 _;_ c1]). { now simpl. }
rewrite HA. eapply All_Derivatives_Flat_Seq;eauto.
assert (HA2: c0 _;_ c1 = c0//[] _;_ c1). { auto. } rewrite HA2.
constructor.
Qed.
 

Lemma Flat_Seq_Derivative_length : forall c0 c1 l1 l, AllDerivatives c1 l1 -> Flat_Seq_Derivative c0 c1 l -> exists l', Flat_Seq_Derivative c0 c1 l' /\
 plus_fold l =R= plus_fold l' /\ length l' = length l1 + 1.
Proof.
intros. induction H0.
- exists ((repeat (Failure _;_ c1) (length l1))++[(c0//s _;_ c1)]). split.
  * apply Flat_Seq_Derivative_repeat_Failure. constructor.
  * split.
    ** rewrite c_eq_iff. setoid_rewrite plus_fold_app.
       rewrite <- c_eq_iff. simpl. rewrite plus_fold_repeat_failure.
       auto_rwd.
    ** simpl. rewrite app_length. rewrite repeat_length. auto.  
- apply IHFlat_Seq_Derivative in H. d_ctx. (*Idempotence argument*)
 Admitted.









Lemma AllDerivatives_Seq : forall (c0 c1 c : Contract)(l0 l1 : list Contract) l l', l=c::l' -> AllDerivatives c0 l0 -> AllDerivatives c1 l1 -> 
AllDerivatives (c0 _;_ c1) (n_prod (seq_configurations c1 l0 l1)).
Proof. 
cofix IH.
intros. constructor.
- intros. simpl. constructor. intros. simpl. cofix IH_plus. unfold seq_closure. rewrite concat_n_prod. 
apply AllDerivatives_Plus.
  * cofix IH_plus. constructor.
    ** intros. simpl.

 




































(*
Inductive Flat_Seq_Derivative : Contract -> Contract -> list Contract -> Prop :=
| FSD_Single c0 c1 c_der0 l0  (H0: OnlyDerivatives c0 l0) 
                              (H1: In_mod_R c_der0 l0) : Flat_Seq_Derivative c0 c1 [c_der0  _;_ c1]
| FSD_Cons c0 c1 l0 l1 l_der c_der1 (H0: OnlyDerivatives c1 l1) 
                                    (H1: In_mod_R c_der1 l1) 
                                    (H2: Flat_Seq_Derivative c0 c1 l0 l_der) (H0: OnlyDerivatives c0 l0) (H2: In_mod_R c_der0 l0)(H1: In_mod_R c_der1 (Failure::l1)) : Flat_Seq_Derivative c0 c1 l0 l1 (c_der1::l_der).

Inductive Flat_Seq_Derivative : Contract -> Contract -> list Contract -> list Contract -> list Contract -> Prop :=
| FSD_Single c0 c1 l0 l1 c_der0 (H0: AllDerivatives c0 l0) (H1: AllDerivatives c1 l1) (H2: In_mod_R c_der0 l0): Flat_Seq_Derivative c0 c1 l0 l1 [c_der0  _;_ c1]
| FSD_Cons c0 c1 l0 l1 l_der c_der1 (H: Flat_Seq_Derivative c0 c1 l0 l1 l_der) (H1: In_mod_R c_der1 (Failure::l1)) : Flat_Seq_Derivative c0 c1 l0 l1 (c_der1::l_der).*)
(*
Lemma in_share_AllDerivatives: forall c0 c l0 , AllDerivatives c0 l0 -> In_mod_R c l0 -> AllDerivatives c l0.
Proof.
cofix IH.
intros. constructor.
- intros. inversion H. eapply IH;auto. apply H. 

Lemma in_AllDerivatives: forall c0 l0 c e, AllDerivatives c0 l0 -> In_mod_R c l0 -> In_mod_R (c/e) l0.
Proof.
intros. unfold In_mod_R in H0. d_ctx. inversion H. unfold In_mod_R in *)

Lemma flatten_cons : forall c, exists c' l, c'::l = flatten c .
Proof. Admitted.

(*
Lemma seq_o_derivative_shape: forall c0 c1 s , Forall (fun c2 : Contract => exists s' : Trace, c2 = Failure _;_ c1 // s' \/ c2 = Success _;_ c1 // s')
  (flatten ((o c0 _;_ c1) // s)).
Proof.
induction s;intros.
- simpl. rewrite Forall_forall. intros. simpl in H. destruct H;try contradiction.
  rewrite <- H. exists []. o_destruct. rewrite H0. now right.
  rewrite H0. now left.
- simpl. rewrite derive_plus. simpl. rewrite Forall_app. split;auto.*)

Lemma seq_derivative_shape : forall (s : Trace)(c0 c1 : Contract) c l, c::l = flatten ((c0 _;_ c1)//s) -> c = c0//s _;_c1 /\ 
Forall (fun (c : Contract) => exists (s' : Trace), c = Failure _;_ c1//s' \/ c = Success _;_ c1//s') l. 
Proof.
induction s;intros;simpl in *.
- inversion H. split;auto.
- rewrite derive_plus in H. simpl in H. destruct (flatten_cons (((c0 / a _;_ c1) // s))).
  destruct H0. Search (_ ++ _ = _ -> _). rewrite <- H0 in H. simpl in H.
  inversion H. apply IHs in H0. destruct H0. split;auto. 
  rewrite Forall_app. split;auto.
  
 subst.
induction l;intros. split.
- destruct s. simpl in *. inversion H. auto. simpl in H.
  rewrite derive_plus in H. simpl in H.
  destruct (flatten_cons ((c0 / e _;_ c1) // s)).
  destruct (flatten_cons (((o c0 _;_ c1 / e) // s))). d_ctx.
  rewrite H0 in H. rewrite H1 in H. simpl in H. inversion H.
  Search ([] = _). apply app_cons_not_nil in H4. contradiction.
- auto.
- split.
  * simpl in H.
 destruct s. simpl in H. inversion H. subst.

 simpl in H4.
  discriminate. inversion H4.
  subst.
 destruct (flatten ((c0 / e _;_ c1) // s)). inversion H.
induction s;intros.
- simpl. exists (c0 _;_ c1). exists []. split;auto.
- simpl. rewrite derive_plus. simpl.
  specialize IHs with (c0/a) c1.
  d_ctx. exists x. exists (x0 ++ (flatten ((o c0 _;_ c1 / a) // s))).
  split;auto.
  * now rewrite <- H.
  * split;auto. simpl. pose proof H1. rewrite Forall_forall in H1. rewrite Forall_forall.
    intros. apply in_app_or in H3. destruct H2.
    ** apply H1 in H2. auto.
    **
       eapply IHs. auto_rwd.

Lemma Flat_Seq_Derivative_closed : forall c0 c1 l, Forall (fun c => Failure _;_ ) l exists s, c0 c1 l -> 
Flat_Seq_Derivative c0 c1 (flat_map (fun c => flatten (c/e)) l).
Proof.









Lemma in_seq_configurations : forall c0 c1 l l0 l1, Flat_Seq_Derivative c0 c1 l -> AllDerivatives c0 l0
-> AllDerivatives c1 l1 -> In_mod_R (plus_fold l) (n_prod (seq_configurations c1 l0 l1)).
Proof.
intros. unfold seq_configurations. induction H.
- 
-
Lemma All_Derivatives_Seq : forall c0 c1 l l0 l1, Flat_Seq_Derivative c0 c1 l -> AllDerivatives c0 l0
-> AllDerivatives c1 l1 -> AllDerivatives (plus_fold l) (n_prod (seq_configurations c1 l0 l1)).
Proof.
cofix IH.
intros. econstructor.
- intros. eapply AD_sub. symmetry. apply plus_fold_derive_flatten.
  eapply IH;eauto. apply Flat_Seq_Derivative_closed; eauto.
- unfold seq_configurations.




  * auto.
  * 
 apply constructor.
- intros. rewrite plus_fold_derive_flatten. eapply IH.
  * eapply Flat_Seq_Derivative_closed. unfold seq_configurations.


Ltac in_forall HF HIn := rewrite Forall_forall in HF; apply HF in HIn;d_ctx;subst.

Lemma flatten_seq_derive_FSD : forall c0 c1 c_der s l, Flat_Seq_Derivative c0 c1 s (length s) l -> 
 In c_der (flatten ((c0 _;_ c1) // s)) <-> ((exists c', c' =R= c_der /\ In c' l) \/ c_der =R= Failure).
Proof. 
intros. remember (length s). induction H.
- simpl. symmetry in Heqn. apply length_zero_iff_nil in Heqn. subst. destruct (flatten_seq_derive_shape [] c0 c1). destruct H. split;intros.
  * rewrite H in H1. simpl in H1. destruct H1.
    ** subst. simpl. left. exists (c0 _;_ c1). split;auto.
    ** in_forall H0 H1. simpl. destruct (o_or x0). 
      *** rewrite H1. left. exists (c0 _;_ c1). split. split;auto.




(**********************************)

Lemma AllDerivatives_sub : forall c0 c1 l, c0 =R= c1 -> AllDerivatives c0 l -> AllDerivatives c1 l.
Proof.
cofix IH.
intros. constructor. intros; simpl.
- inversion H. eapply IH. inversion H. eauto. inversion H0. eauto.
- inversion H0. d_ctx. subst. exists x. split;auto. now rewrite H2.
Qed.

Lemma AllDerivatives_sub_iff : forall c0 c1 l, c0 =R= c1 -> AllDerivatives c0 l <-> AllDerivatives c1 l.
Proof.
intros. split;eauto using AllDerivatives_sub. apply AllDerivatives_sub.
now symmetry.
Qed.

Lemma plus_fold_plus : forall c0 c1, plus_fold [c0;c1] =R= c0 _+_ c1.
Proof. c_eq_tac. Qed.

Hint Resolve plus_fold_plus : coDB.

(*
Lemma AllDerivatives_Plus : forall (c0 c1 : Contract)(l0 l1 : list Contract), AllDerivatives c0 l0 -> AllDerivatives c1 l1 -> 
 AllDerivatives (c0 _+_ c1) (n_prod [l0;l1]).
Proof.
cofix IH. intros. eapply AllDerivatives_sub. eapply plus_fold_plus. eapply AllDerivatives_Flatten_iff.
eauto with coDB.
Qed.
Hint Resolve AllDerivatives_Plus : coDB.*)

Lemma AllDerivatives_plus_plus_fold : forall (c0 c1 : Contract)(l : list Contract), AllDerivatives (c0 _+_ c1) l -> 
 AllDerivatives (plus_fold [c0;c1] ) l.
Proof. c_eq_tac. auto_rwd. inversion H. apply AllDerivatives_sub with(c0:= c0/e _+_ c1/e);
       simpl in H0. auto_rwd. auto. inversion H. d_ctx.
       exists x. auto_rwd.
Qed.

Lemma AllDerivatives_plus_fold_plus : forall (c0 c1 : Contract)(l : list Contract), 
 AllDerivatives (plus_fold [c0;c1] ) l -> AllDerivatives (c0 _+_ c1) l .
Proof.
c_eq_tac. inversion H. simpl in H0.  apply AllDerivatives_sub with(c0:= c0/e _+_ (c1/e _+_ Failure));
simpl. auto_rwd. auto. inversion H. d_ctx. exists x. simpl in H1.
split;auto. now autorewrite with coDB in H1.
Qed.

(*coinductive definition can't handle rewriting as it violates constrctur guardedness*)
Lemma AllDerivatives_plus_fold_iff : forall (c0 c1 : Contract)(l : list Contract), 
 AllDerivatives (plus_fold [c0;c1] ) l <-> AllDerivatives (c0 _+_ c1) l.
Proof. split;auto using AllDerivatives_plus_plus_fold,AllDerivatives_plus_fold_plus.
Qed.


Lemma AllDerivatives_comm : forall c0 c1 l, AllDerivatives (c0 _+_ c1) l -> AllDerivatives (c1 _+_ c0) l.
Proof. c_eq_tac. inversion H;eauto. inversion H. d_ctx.
       exists x. split;auto. rewrite H1. auto with coDB.
Qed.

Hint Immediate AllDerivatives_comm : coDB.


Hint Resolve in_eq in_cons : core.

Lemma AllDerivatives_Failure_seq : forall c, AllDerivatives (Failure _;_ c) ([Failure]).
Proof.
cofix IH.
intros. constructor.
- intros;simpl. rewrite o_Failure. eapply AllDerivatives_sub.  repeat rewrite c_eq_Failure_seq. 
 symmetry. eapply c_eq_idempotent. auto with dpDB.
- exists Failure. split;auto with dpDB. now rewrite c_eq_Failure_seq.
Qed.

Definition failure_seq_list l := map (fun l => Failure::l) (repeat l (length l)).



Search ((o _)/_).
Locate o_derive.

Ltac closure_sub c := apply AllDerivatives_sub with (c0:=c).

Lemma AllDerivatives_o_seq : forall (l1 : list Contract)(c0 c1 : Contract),  AllDerivatives c1 l1 -> AllDerivatives ((o c0) _;_ c1) (Failure::l1).
Proof.
induction l1;intros. apply AllDerivatives_nil in H. contradiction. 
constructor;intros.
- simpl. autorewrite with icDB. closure_sub (o c0 _;_ c1 / e);auto_rwd.
Admitted.
(*
  apply IH. Guarded. Guarded.   inversion H. eauto.  


cofix IH.
intros. constructor;intros.
- destruct l1. apply AllDerivatives_nil in H. contradiction. simpl.
  autorewrite with icDB. closure_sub (o c0 _;_ c1 / e);auto_rwd.
  apply IH. Guarded. Guarded.   inversion H. eauto.  
- destruct (o_or c0); destruct H0;rewrite H0.
  * inversion H. d_ctx. exists x.
    split;auto_rwd. auto.
  * exists Failure. split;auto_rwd. auto.
Qed.*)

Lemma AllDerivatives_Seq : forall (c0 c1 : Contract)(l0 l1 : list Contract), AllDerivatives c0 l0 -> AllDerivatives c1 l1 -> AllDerivatives (c0 _;_ c1) (l0 ++l1).
Proof.
cofix IH.
intros. constructor.
- intros;simpl.

 apply AllDerivatives_comm. unfold seq_closure. rewrite concat_n_prod.

Lemma AllDerivatives_Seq : forall (c0 c1 : Contract)(l0 l1 : list Contract), AllDerivatives c0 l0 -> AllDerivatives c1 l1 -> AllDerivatives (c0 _;_ c1) (seq_closure c1 l0 l1).
Proof. 
cofix IH.
intros. constructor.
- intros. simpl. constructor. intros. simpl. cofix IH_plus. unfold seq_closure. rewrite concat_n_prod. 
apply AllDerivatives_Plus.
  * cofix IH_plus. constructor.
    ** intros. simpl.

 


Definition plus_combine (l0 l1 : list Contract) := map (fun p => (fst p) _+_ (snd p)) (combine l0 l1).





(****************Code below hasn't been cleaned up**********************************************************)


(*
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
- rewrite In_mod_ACI_iff_In in H. d_ctx. induction H.
  * subst. now left.
  * right. rewrite In_mod_ACI_iff_In. exists x. split;auto.
- destruct H.
  * rewrite In_mod_ACI_iff_In. exists c'. split;auto using in_eq.
  * rewrite In_mod_ACI_iff_In in *. d_ctx. exists x.
    split;auto using in_cons,in_eq.
Qed. *)

Lemma lift_bmatches : forall c0 c1, (forall s, nu (c0//s) = nu (c1//s)) -> c0 =R= c1.
Proof.
intros. rewrite c_eq_iff. intros. specialize H with s. repeat rewrite Matches_Comp_iff_matchesb.
rewrite H. reflexivity.
Qed.

Lemma c_eq_idempotent : forall c, c _+_ c =R= c.
Proof.
cofix IH.
intros. constructor. intros. simpl. auto. simpl. btauto.
Qed.


Ltac nu_solve := simpl ; try btauto.



Ltac derive_plus_tac H := rewrite derive_plus in H; simpl in H; apply in_app_or in H; destruct H.

(*Reduce all failure cases to Failure*)
Theorem in_flatten_seq_i_Failure_derive : forall s c1 c_der, In c_der (flatten ((Failure _;_ c1) // s)) -> 
c_der =b= Failure.
Proof.
induction s;intros.
- simpl in H. destruct H;try contradiction. inversion H. subst.
  auto_rwd.
- auto_rwd. simpl in H. auto_rwd_in H. simpl in H. apply in_app_or in H.
  destruct H. apply IHs with (s:=s0) in H. rewrite H. auto_rwd.
  apply IHs with (s:=s0) in H. rewrite H. auto_rwd.
Qed.

Theorem Failure_derive_i_in_flatten_seq : forall s c1, exists c_der, c_der =b= Failure /\ 
 (In c_der (flatten ((Failure _;_ c1) // s))).
Proof.
induction s;intros.
- exists (Failure _;_ c1). simpl. split;autoM.
- simpl. auto_rwd. simpl. specialize IHs with c1 as IHs'. d_ctx. exists x.
  split;autoM. rewrite in_app_iff.  now left. 
Qed.

Definition bool_incl_lists (l0 l1 : list Contract) := forall c, In c l0 -> exists c', In c' l1 /\ c' =b= c.

Definition bool_equiv_lists (l0 l1 : list Contract) := bool_incl_lists l0 l1 /\ bool_incl_lists l1 l0.


Lemma test : forall s c, bool_equiv_lists (flatten ((Failure _;_ c) // s)) [Failure].
Proof.
intros. unfold bool_equiv_lists,bool_incl_lists. split.
- intros. pose proof Failure_derive_i_in_flatten_seq s c. d_ctx.
  exists x.
Admitted.

Theorem in_flatten_seq_o_derive : forall s c0 c1 c_der, In c_der (flatten (((o c0) _;_ c1) // s)) -> 
c_der =b= Failure \/ c_der =b= (o c0) _;_ c1//s. 
Proof.
induction s;intros.
- simpl in H. destruct H;try contradiction. inversion H. destruct (o_or c0).
  * rewrite H1. right. autoM.
  * rewrite H1. left. autoM. 
- simpl in H. auto_rwd_in H. simpl in H. apply in_app_or in H. destruct H.
  * rewrite o_derive in H. eauto using in_flatten_seq_i_Failure_derive.
  * rewrite o_idempotent in H. apply IHs in H. destruct H.
    ** now left.
    ** right. now simpl.
Qed.


Theorem in_flatten_seq_derive : forall s c0 c1 c_der, In c_der (flatten ((c0 _;_ c1) // s)) -> 
c_der =b= Failure \/ (exists l0 l1 , s = l0++l1 /\ c_der =b= (o (c0 // l0)) _;_ c1 // l1) \/ (c_der =b= c0//s _;_ c1).
Proof.
induction s;intros.
- simpl in H. destruct H; try contradiction. subst. right. right. auto.
- simpl in H. auto_rwd_in H. simpl in H. apply in_app_or in H.
  destruct H.
  * apply IHs in H. destruct H.
    ** now left.
    ** destruct H. 
      *** d_ctx. subst. right. left. exists (a::x). exists x0.
          split;auto.
      *** right. right. auto.
  * apply in_flatten_seq_o_derive in H. destruct H;auto. 
    right. left. exists []. exists (a::s). split;auto.
Qed.

Definition seq_derive_cases (c0 c1 :Contract) := [c0 ; c1].
Lemma test2 : forall s c0 c1, bool_equiv_lists (flatten ((c0 _;_ c1) // s)) (seq_derive_cases c0 c1).
Proof. Admitted.
Definition plus_fold (l : list Contract) := Failure.
Lemma bool_equiv_AllDerivatives : forall (pl0 pl1 l : list Contract) (c : Contract), bool_equiv_lists pl0 pl1 ->
 AllDerivatives (plus_fold pl0) l <-> AllDerivatives (plus_fold pl1) l.

Lemma AllDerivatives_Seq : forall (c0 c1 : Contract)(l0 l1 : list Contract), AllDerivatives c0 l0 -> AllDerivatives c1 l1 -> 
 AllDerivatives (c0 _;_ c1) ((map (fun c => c _;_ c1) l0) ++ ) l1).

Theorem in_flatten_seq_derive : forall s c0 c1 c_der0 c_der1, In (c_der0 _;_ c_der1) (flatten ((c0 _;_ c1) // s)) <-> 
(c_der0 _;_ c_der1 = c0 // s _;_ c1) \/ ( s<> [] /\ (c_der0 = Success \/ c_der0 = Failure) /\ exists n_lo n_hi, c_der1 = c1//(firstn n_hi (skipn n_lo s))).
Proof.
intro. 
induction s;intros;simpl.
- split;intros. destruct H;try contradiction. inversion H. subst. now left.
  destruct H. inversion H. now left. d_ctx. contradiction.
- split;intros.
  * rewrite derive_plus in H. simpl in H. apply in_app_or in H. destruct H.
    ** apply IHs in H. destruct H.
      *** now left.
      *** d_ctx. destruct H0.
        **** subst. right. split.  intro H2.  discriminate. split. now left. 
             exists (S x). exists x0. now simpl.
        **** subst. right. split. intro H2. discriminate. split. now right.
             exists (S x). exists x0. now simpl.
    ** apply IHs in H. destruct H.
      *** inversion H. subst. right. split. intro H2. discriminate.
          split. destruct (o_or c0). rewrite H0. 
          destruct s. simpl. now left. simpl. rewrite Failure_trace_derive.
          now right. rewrite H0. rewrite Failure_trace_derive. now right.
          exists 0. exists 1. simpl. auto.
      *** d_ctx. subst. destruct H0.
        **** rewrite H0. right. split;auto. intro H2. discriminate.
             split. now left. exists 0. exists x0.
 Check trace_derive_failure. rewrite  r simpl; left.
 intuition;try contradiction. auto.
 destruct H;subst.
  exists 1. now simpl. split. destruct H. inversion H. subst.
  destruct (o_or c0). rewrite H0. right. now left. rewrite H0. right. right. auto.
  inversion H. inversion H. inversion H0. subst. exists 0. now simpl.
  inversion H0. d_ctx. destruct H. destruct x.
  * simpl in H0. subst. intuition. auto.
 subst. destruct H;subst. simpl. now right. susbt. 
 rewrite H.
 rewrite Heqt in *. simpl in H. destruct H;try contradiction. inversion H.
  now left. destruct H. rewrite Heqt. simpl. auto. now left.
  destruct H. subst.  rewrite H.



Theorem in_flatten_seq_Failure_derive : forall s c1 c_der0 c_der1, In (c_der0 _;_ c_der1) (flatten ((Failure _;_ c1) // s)) <-> 
c_der0 = Failure /\ exists n_low n_high, c_der1 = c1//(skipn n_low (firstn n_high s)).
Proof.
induction s;intros.
- split;intros;simpl in *. destruct H;try contradiction. inversion H. subst.
  split;auto. exists 0. exists 0. now simpl. d_ctx.
  rewrite firstn_nil in H0. rewrite skipn_nil in H0. subst. left; now simpl.
- split;intros.
  * simpl in H. derive_plus_tac H. 
    ** apply IHs in H. d_ctx. subst. split;auto. exists (S x). now simpl.
    ** apply IHs in H. d_ctx. subst. split;auto. exists (S x).

Ltac derive_plus_tac H := rewrite derive_plus in H; simpl in H; apply in_app_or in H; destruct H.
Theorem in_flatten_seq_o_derive : forall s e c0 c1 c_der0 c_der1, In (c_der0 _;_ c_der1) (flatten (((o c0) _;_ c1) // (e::s))) <-> 
(c_der0 = Failure /\ exists n, c_der1 = c1//(firstn n s)) \/ (c_der0 = o c0 /\ exists n, c_der1 = c1//(e::(firstn n s))).
Proof.
induction s;intros.
- split;intros;simpl. destruct H;try contradiction. inversion H. subst.
  left.  split;autoC. exists 0. now simpl. destruct H;try contradiction. 
  inversion H. subst. right. split;autoC. exists 1. now simpl.
  destruct H. d_ctx. subst. left. simpl. rewrite firstn_nil.
  rewrite o_derive. auto.  d_ctx. destruct x. simpl in H0. subst. subst. right.
  rewrite o_idempotent. 
  auto. simpl in H0. subst. right. left. rewrite o_idempotent. auto.
- split;intros.
  * simpl trace_derive in H. remember (a::s). simpl in H.
    derive_plus_tac H. rewrite Heql in H. rewrite o_derive in H.
    assert (HA : Failure = o Failure). { auto. } rewrite HA in H.
    apply IHs in H. destruct H.
    ** d_ctx. subst. left.
 rewrite <- Heql in H. simpl in H. fold in H. derive_plus_tac H. 
    ** simpl in IHs. rewrite o_derive in H. assert (HA : Failure = o Failure). { auto. }
       rewrite HA in H. setoid_rewrite o_idempotent in IHs. 
       rewrite o_idempotent in H. apply IHs in H. destruct H.
      *** d_ctx. subst. left. split;auto. destruct H. derive_plus_tac H.
      *** simpl in IHs. rewrite derive_plus in H. simpl in H. simpl in H.



 left.
  destruct (o_or c0); intuition. now exists 0. left. symmetry. d_ctx.
  destruct (o_or c0). destruct H. subst. rewrite H1. rewrite skipn_nil. auto.
  destruct H. contradiction. destruct H. subst. rewrite skipn_nil. auto.
  destruct H. contradiction.
- split;intros.
  * rewrite derive_plus in H. simpl in H. apply in_app_or in H. destruct H.
    ** rewrite o_derive in H. assert (HA: Failure = o Failure). auto.
       rewrite HA in H. apply IHs in H. d_ctx. subst. split.
      *** destruct H.
        **** subst. right. split. intro H3. discriminate. auto.
        **** destruct H. subst. right. split. intro H3. discriminate. auto.
      *** destruct H. subst. exists (S x). auto. exists (S x). auto.
    ** apply IHs in H. d_ctx. subst. destruct H.
      *** split. subst. rewrite o_idempotent. now left. split.
 

  subst. rewrite H1. left.
  destruct H. subst.  inversion H. now left. d_ctx. contradiction.

Theorem in_flatten_seq_derive : forall s c0 c1 c_der0 c_der1, In (c_der0 _;_ c_der1) (flatten ((c0 _;_ c1) // s)) <-> 
(c_der0 _;_ c_der1 = c0 // s _;_ c1) \/ ( s<> [] /\ (c_der0 = Success \/ c_der0 = Failure) /\ exists n, c_der1 = c1//(skipn n s)).
Proof.
intro. 
induction s;intros;simpl.
- split;intros. destruct H;try contradiction. inversion H. subst. now left.
  destruct H. inversion H. now left. d_ctx. contradiction.
- split;intros.
  * rewrite derive_plus in H. simpl in H. apply in_app_or in H. destruct H.
    ** apply IHs in H. destruct H.
      *** now left.
      *** d_ctx. destruct H0.
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
  inversion H0. d_ctx. destruct H. destruct x.
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
  d_ctx. destruct H. auto.
- split;intros.
  * simpl in H. rewrite derive_plus in H. simpl in H.
    apply in_app_or in H. destruct H.
    ** apply IHs in H. destruct H.
      *** left. now simpl.
      *** right. split;auto. intro H3. discriminate. d_ctx.
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
          d_ctx.
        **** inversion




 ((c0 // s) _;_ c1):: l /\
 Forall (fun c => exists c' s, c = (o c') _;_ (c1//s)) l.


Check firstn.
Inductive Flat_Seq_Derivative : Contract -> Contract -> Trace -> nat -> list Contract -> Prop :=
| FSD_Single c0 c1 s : Flat_Seq_Derivative c0 c1 s 0 [c0//s _;_ c1]
| FSD_Cons c0 c1 s n l (H: Flat_Seq_Derivative c0 c1 s n l) : Flat_Seq_Derivative c0 c1 s (S n) (c1//(firstn (S n) s)::l).

Ltac in_forall HF HIn := rewrite Forall_forall in HF; apply HF in HIn;d_ctx;subst.

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
    rewrite Forall_forall in H0. apply H0 in H1. d_ctx. subst.
    ** now left. 
    rewrite Forall_forall in H1.

Lemma FSD_max_length : forall c0 c1 c_der s l, n > length s ->  Flat_Seq_Derivative c0 c1 s n l ...

Definition seq_closure_list (c0 c1 : Contract) (l0 l1 : list Contract) := 
 let first_elements := map (fun c => c _;_ c1) l0 in
 let mid_success_elems := map (fun c => Success _;_ c) l1 in
 let mid_failure_elems := map (fun c => Failure _;_ c) l1 in
 




(*Lemma Trace_Derive_seq_tail : forall  l e s c0 c1 c', flatten ((c0 _;_ c1) // s) = e::l ->
In c' l -> exists c'' n, Trace_Derive c1 (firstn n s) c'' /\ (c' = Success _;_ c'' \/ c' = Failure _;_ c'').
Proof.
induction l;intros.
- simpl in H0. inversion H0.
- simpl in H0. inversion H0.
  * rewrite derive_plus in H. simpl in H.
  destruct (flatten_non_empty ((c0 / a _;_ c1) // s)).
  d_ctx. rewrite H0 in H. simpl in H. apply in_app_or in H.
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

Hint Resolve AllDerivatives_Plus  : dpDB.

Lemma exists_finite_closure : forall (c : Contract), exists (l : list Contract), AllDerivatives c l /\ length l = max_derivative_count c.
Proof.
induction c;intros.
- exists [Success;Failure]. split;auto with dpDB. 
- exists [Failure]. split;auto with dpDB.
- exists [Event e;Success;Failure]. split;auto with dpDB.
- d_ctx. exists (plus_prod x0 x). split;simpl; auto with dpDB.
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



