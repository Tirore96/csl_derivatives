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

Lemma In_mod_R_cons : forall c c' l, In_mod_R c l -> In_mod_R c (c' :: l).
Proof.
intros. unfold In_mod_R in *. destruct_ctx. exists x. split;auto.
Qed.

Hint Resolve In_mod_R_eq In_mod_R_cons : dpDB.

 


CoInductive AllDerivatives : Contract -> list Contract -> Prop :=
| AD_fix c l (H0: forall e, AllDerivatives (c/e) l) (H1 : In c l)  : AllDerivatives c l
| AD_sub c0 c1 l (H0: c0 =R= c1) (H1: AllDerivatives c0 l)  : AllDerivatives c1 l. (*Report: Necessary constructor for substitution because of Coq's guardedness constraint*)


(*
Inductive OnlyDerivatives : Contract -> list Contract -> Prop :=
| OD_nil c : OnlyDerivatives c [c]
| OD_cons c c' l e (H: In_mod_R c' l) (H1: OnlyDerivatives c 
*)
(*
Lemma In_AllDerivatives_i_Trace_Derive : forall (c: Contract)(l : list Contract), 
AllDerivatives c l -> (forall (s : Trace)(c_der : Contract), Trace_Derive c s c_der -> exists c', c' =R= c_der /\ In c' l).
Proof.
intros. generalize dependent c. induction s;intros.
- inversion H0. subst. inversion H. destruct_ctx. exists x;auto.
- inversion H0. inversion H. subst. eapply IHs. eapply H6. eauto.
Qed.

Lemma Trace_Derive_i_In_AllDerivatives : forall (c: Contract)(l : list Contract), 
(forall (s : Trace)(c_der : Contract), Trace_Derive c s c_der -> exists c', c' =R= c_der /\ In c' l) -> AllDerivatives c l.
Proof.
cofix H_co.
intros. constructor.
- intros. apply H_co. intros. eapply H. constructor. eauto.
- eauto with coDB.
Qed.

Theorem AllDerivatives_iff : forall (c: Contract)(l : list Contract), 
AllDerivatives c l <-> (forall (s : Trace)(c_der : Contract), Trace_Derive c s c_der -> exists c', c' =R= c_der /\ In c' l).
Proof.
split;intros. 
- eapply In_AllDerivatives_i_Trace_Derive;eauto.
- eapply Trace_Derive_i_In_AllDerivatives;eauto.
Qed.*)

Lemma AllDerivatives_Failure : AllDerivatives Failure [Failure].
Proof.
cofix IH. constructor;auto;simpl;auto.
Qed.

Hint Resolve AllDerivatives_Failure : dpDB.



Lemma AllDerivatives_cons : forall (c c_der : Contract)(l : list Contract), AllDerivatives c l -> AllDerivatives c (c_der::l).
Proof.
cofix IH.
intros. inversion H. 
- constructor;auto. 
- eapply AD_sub. eauto. apply IH. auto.
Qed.

Hint Resolve AllDerivatives_cons : dpDB.

(*
Lemma AllDerivatives_derive : forall c l e, AllDerivatives c l -> AllDerivatives (c/e) l.
Proof.
cofix IH. intros. inversion H.
- destruct_ctx.
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
- now left.
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

Fixpoint flatten (c : Contract) : list Contract :=
match c with
| c0 _+_ c1 => (flatten c0) ++ (flatten c1)
| _ => [c]
end.

Lemma concat_n_prod : forall l ls, n_prod (l::ls) = plus_prod l ((n_prod ls)).
Proof.
intros. funelim (n_prod (l::ls)). simp n_prod. destruct l;auto.
rewrite H. auto.
Qed.

Lemma in_n_prod : forall c0 c1 l0 l1, In c0 l0 -> In c1 l1 -> In (c0 _+_ c1) (n_prod [l0; l1]).
Proof. Admitted.

Inductive List_AllDerivatives : list Contract -> list (list Contract) -> Prop :=
| List_AllDerivatives_nil : List_AllDerivatives [] []
| List_AllDerivatives_cons c l cs ls (H0 : AllDerivatives c l) (H1 : List_AllDerivatives cs ls) : List_AllDerivatives (c::cs) (l::ls).

Hint Constructors List_AllDerivatives : coDB.

Lemma AllDerivatives_Flatten_iff : forall l ll, List_AllDerivatives l ll <-> AllDerivatives (plus_fold l) (n_prod ll).
Proof. Admitted.



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



Lemma Failure_trace_derive : forall s, Failure//s = Failure.
Proof.
induction s;intros;auto.
Qed.

Hint Immediate o_derive Failure_trace_derive : dpDB.

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


Inductive Flat_Seq_Derivative : Contract -> Contract -> list Contract -> Prop :=
| FSD_Single c0 c1 s : Flat_Seq_Derivative c0 c1 [c0//s _;_ c1]
| FSD_Cons_S c0 c1 l s (H: Flat_Seq_Derivative c0 c1 l) : Flat_Seq_Derivative c0 c1 ((Success _;_(c1//s))::l)
| FSD_Cons_F c0 c1 l s (H: Flat_Seq_Derivative c0 c1 l) : Flat_Seq_Derivative c0 c1 ((Failure _;_(c1//s))::l).

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
intros. unfold In_mod_R in H0. destruct_ctx. inversion H. unfold In_mod_R in *)

Lemma helper : forall s c0 e, (c0 // s) / e = c0 // (s ++ [e]).
Proof.
induction s;intros. now simpl.
simpl. now rewrite IHs.
Qed.

Lemma helper2  : forall c e, c/e = c//[e].
Proof. auto. Qed.

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
  destruct (flatten_cons (((o c0 _;_ c1 / e) // s))). destruct_ctx.
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
  destruct_ctx. exists x. exists (x0 ++ (flatten ((o c0 _;_ c1 / a) // s))).
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

Definition seq_configurations (c1 : Contract) (l0 l1 : list Contract) := 
 (repeat (Failure::l1) (length l1))++[map (fun c => c _;_ c1) l0].

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




(**********************************)

Lemma AllDerivatives_sub : forall c0 c1 l, c0 =R= c1 -> AllDerivatives c0 l -> AllDerivatives c1 l.
Proof.
cofix IH.
intros. constructor. intros; simpl.
- inversion H. eapply IH. inversion H. eauto. inversion H0. eauto.
- inversion H0. destruct_ctx. subst. exists x. split;auto. now rewrite H2.
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
       simpl in H0. auto_rwd. auto. inversion H. destruct_ctx.
       exists x. auto_rwd.
Qed.

Lemma AllDerivatives_plus_fold_plus : forall (c0 c1 : Contract)(l : list Contract), 
 AllDerivatives (plus_fold [c0;c1] ) l -> AllDerivatives (c0 _+_ c1) l .
Proof.
c_eq_tac. inversion H. simpl in H0.  apply AllDerivatives_sub with(c0:= c0/e _+_ (c1/e _+_ Failure));
simpl. auto_rwd. auto. inversion H. destruct_ctx. exists x. simpl in H1.
split;auto. now autorewrite with coDB in H1.
Qed.

(*coinductive definition can't handle rewriting as it violates constrctur guardedness*)
Lemma AllDerivatives_plus_fold_iff : forall (c0 c1 : Contract)(l : list Contract), 
 AllDerivatives (plus_fold [c0;c1] ) l <-> AllDerivatives (c0 _+_ c1) l.
Proof. split;auto using AllDerivatives_plus_plus_fold,AllDerivatives_plus_fold_plus.
Qed.


Lemma AllDerivatives_comm : forall c0 c1 l, AllDerivatives (c0 _+_ c1) l -> AllDerivatives (c1 _+_ c0) l.
Proof. c_eq_tac. inversion H;eauto. inversion H. destruct_ctx.
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

Lemma AllDerivatives_nil : forall c, AllDerivatives c [] -> False.
Proof.
intros. inversion H. destruct_ctx. simpl in H4. contradiction.
Qed.

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
  * inversion H. destruct_ctx. exists x.
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
- rewrite In_mod_ACI_iff_In in H. destruct_ctx. induction H.
  * subst. now left.
  * right. rewrite In_mod_ACI_iff_In. exists x. split;auto.
- destruct H.
  * rewrite In_mod_ACI_iff_In. exists c'. split;auto using in_eq.
  * rewrite In_mod_ACI_iff_In in *. destruct_ctx. exists x.
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
- simpl. auto_rwd. simpl. specialize IHs with c1 as IHs'. destruct_ctx. exists x.
  split;autoM. rewrite in_app_iff.  now left. 
Qed.

Definition bool_incl_lists (l0 l1 : list Contract) := forall c, In c l0 -> exists c', In c' l1 /\ c' =b= c.

Definition bool_equiv_lists (l0 l1 : list Contract) := bool_incl_lists l0 l1 /\ bool_incl_lists l1 l0.


Lemma test : forall s c, bool_equiv_lists (flatten ((Failure _;_ c) // s)) [Failure].
Proof.
intros. unfold bool_equiv_lists,bool_incl_lists. split.
- intros. pose proof Failure_derive_i_in_flatten_seq s c. destruct_ctx.
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
      *** destruct_ctx. subst. right. left. exists (a::x). exists x0.
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
  destruct H. inversion H. now left. destruct_ctx. contradiction.
- split;intros.
  * rewrite derive_plus in H. simpl in H. apply in_app_or in H. destruct H.
    ** apply IHs in H. destruct H.
      *** now left.
      *** destruct_ctx. destruct H0.
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
      *** destruct_ctx. subst. destruct H0.
        **** rewrite H0. right. split;auto. intro H2. discriminate.
             split. now left. exists 0. exists x0.
 Check trace_derive_failure. rewrite  r simpl; left.
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



Theorem in_flatten_seq_Failure_derive : forall s c1 c_der0 c_der1, In (c_der0 _;_ c_der1) (flatten ((Failure _;_ c1) // s)) <-> 
c_der0 = Failure /\ exists n_low n_high, c_der1 = c1//(skipn n_low (firstn n_high s)).
Proof.
induction s;intros.
- split;intros;simpl in *. destruct H;try contradiction. inversion H. subst.
  split;auto. exists 0. exists 0. now simpl. destruct_ctx.
  rewrite firstn_nil in H0. rewrite skipn_nil in H0. subst. left; now simpl.
- split;intros.
  * simpl in H. derive_plus_tac H. 
    ** apply IHs in H. destruct_ctx. subst. split;auto. exists (S x). now simpl.
    ** apply IHs in H. destruct_ctx. subst. split;auto. exists (S x).

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

Hint Resolve AllDerivatives_Plus  : dpDB.

Lemma exists_finite_closure : forall (c : Contract), exists (l : list Contract), AllDerivatives c l /\ length l = max_derivative_count c.
Proof.
induction c;intros.
- exists [Success;Failure]. split;auto with dpDB. 
- exists [Failure]. split;auto with dpDB.
- exists [Event e;Success;Failure]. split;auto with dpDB.
- destruct_ctx. exists (plus_prod x0 x). split;simpl; auto with dpDB.
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



