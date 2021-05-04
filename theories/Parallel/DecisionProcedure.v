Require Import Bool.Bool List Coq.Arith.PeanoNat Setoid.
Require Import CSL.Core.Contract CSL.Core.ContractEquations.  
Import ListNotations.

Set Implicit Arguments.


Section inclb. 
  Variable A : Type.
  Hypothesis eq_dec : forall (x y : A), {x = y} + {x <> y}.

  Definition inclb (l0 l1 : list A) :bool := 
  forallb (fun a0 => existsb (fun a1 => if eq_dec a0 a1 then true else false) l1) l0.

  Lemma inclb_iff : forall (l0 l1 : list A), inclb l0 l1 = true <-> incl l0 l1.
  Proof. unfold inclb. unfold incl. split. 
  - intros. rewrite forallb_forall in H. apply H in H0. 
    rewrite existsb_exists in H0. destruct H0. destruct H0. 
    destruct (eq_dec a x);subst;auto.
    discriminate.
  - intros. rewrite forallb_forall. intros. apply H in H0. rewrite existsb_exists.
    exists x. split;auto.
    destruct (eq_dec x x);auto.
  Qed.

  Lemma incl_reflect : forall (l0 l1 : list A), reflect (incl l0 l1) (inclb l0 l1).
  Proof. 
  intros. destruct (inclb l0 l1) eqn:Heqn.
  - constructor. now rewrite inclb_iff in Heqn.
  - constructor. intro H. rewrite <- inclb_iff in H. rewrite Heqn in H. discriminate.
  Qed.


  Lemma inclb_false_iff : forall (l0 l1 : list A), inclb l0 l1 = false <-> ~ (incl l0 l1).
  Proof. 
  intros. destruct (incl_reflect l0 l1);split;intros;try solve [ discriminate | contradiction | auto ].
  Qed.
End inclb.


Definition trace_inclb := inclb (list_eq_dec EventType_eq_dec).
Lemma c_eq_reflect : forall c0 c1, reflect (c0 =R= c1) (trace_inclb (L c0) (L c1) && trace_inclb (L c1) (L c0)).
Proof. 
intros. destruct ((trace_inclb (L c0) (L c1) && trace_inclb (L c1) (L c0))) eqn:Heqn;
unfold trace_inclb in*;constructor; rewrite <- Matches_iff_c_eq; rewrite Matches_eq_iff_incl_and;
repeat rewrite <- inclb_iff; rewrite <- andb_true_iff; 
[ eauto | intro H; rewrite H in Heqn; discriminate].
Qed.


(*Deciding contract equivalence*)

Theorem c_eq_dec : forall c0 c1, {c0 =R= c1} + {~ (c0 =R= c1) }.
Proof.
intros. destruct (c_eq_reflect c0 c1).
- now left.
- now right.
Qed.


(**********Reflective tactic***********)

Inductive Expr :=
| Var : nat -> Expr
| ESuccess : Expr
| EFailure : Expr
| EPlus : Expr -> Expr -> Expr
| ESeq : Expr -> Expr -> Expr.

Hint Constructors Expr : eqDB.


Fixpoint contract_of_Expr vals e :=
match e with
| Var v => vals v
| ESuccess => Success
| EFailure => Failure
| EPlus e0 e1 => (contract_of_Expr vals e0) _+_ (contract_of_Expr vals e1)
| ESeq e0 e1 => (contract_of_Expr vals e0) _;_ (contract_of_Expr vals e1)
end.

Fixpoint L_Expr (e : Expr) : list (list nat) :=
match e with
| Var v => [[v]]
| ESuccess => [[]]
| EFailure => []
| EPlus e0 e1 => (L_Expr e0) ++ (L_Expr e1)
| ESeq e0 e1 => map (fun p => (fst p)++(snd p)) (list_prod (L_Expr e0) (L_Expr e1))
end.

Fixpoint L_inv_vars (f : nat -> Contract) (vars : list nat) :=
match vars with
| [] => Success
| n::vars' => (f n) _;_ (L_inv_vars f vars')
end.

Lemma L_inv_vars_app : forall (l1 l2 : list nat)(f : nat -> Contract), (L_inv_vars f l1) _;_ (L_inv_vars f l2) =R= (L_inv_vars f) (l1++l2).
Proof.
induction l1;intros;simpl; auto_rwd_eqDB.
rewrite <- IHl1. auto_rwd_eqDB.
Qed.

Definition L_inv_Expr (f : nat -> Contract) (l : list (list nat)) := Σ (map (L_inv_vars f) l).
Hint Unfold L_inv_Expr : eqDB.

Lemma L_inv_vars_seq_L_inv_Expr : forall (ss : list (list nat)) (s : list nat) (f : nat -> Contract),
 L_inv_vars f s _;_ L_inv_Expr f ss =R=
 Σ (map (fun x => L_inv_vars f (fst x ++ snd x)) (map (fun y : list nat => (s, y)) ss)).
Proof.
induction ss;intros;simpl;auto_rwd_eqDB.
unfold L_inv_Expr. simpl.
auto_rwd_eqDB. apply c_plus_ctx;eauto using L_inv_vars_app.
Qed.

Lemma L_inv_Expr_seq_L_inv_Expr : forall l0 l1 (f : nat -> Contract), L_inv_Expr f l0 _;_ L_inv_Expr f l1 =R=
 Σ (map (fun x => L_inv_vars f (fst x ++ snd x)) (list_prod l0 l1)).
Proof.
induction l0;intros;simpl. unfold L_inv_Expr. simpl. auto_rwd_eqDB.
repeat rewrite map_app. rewrite Σ_app. rewrite <- IHl0.
unfold L_inv_Expr at 1. simpl. auto_rwd_eqDB. 
apply c_plus_ctx; eauto using L_inv_vars_seq_L_inv_Expr with eqDB. 
Qed.


Theorem L_inv_L_ceq : forall (e : Expr)(f : nat -> Contract), L_inv_Expr f (L_Expr e) =R= contract_of_Expr f e.
Proof.
induction e;intros; unfold L_inv_Expr; simpl; try solve [auto_rwd_eqDB].
- rewrite map_app. rewrite Σ_app.
  eauto using c_plus_ctx. 
- rewrite map_map.
  rewrite <- IHe1. rewrite <- IHe2.
  symmetry. apply L_inv_Expr_seq_L_inv_Expr.
Qed.

(*
Lemma expr_L : forall (e : Expr)(vals : nat -> Contract), contract_of_Expr vals e =R= Σ (map (L_inv_vars vals) (L_Expr e)).
Proof.
induction e;intros;simpl; try solve [auto_rwd_eqDB].
- rewrite map_app. rewrite Σ_app.
  apply c_plus_ctx;auto.
- rewrite map_map. apply c_eq_completeness. intros. rewrite in_Σ. split;intros.
  * inversion H. subst.
 
    eapply c_eq_soundness in IHe1.
    rewrite in_Σ in IHe1. 
    eapply IHe1 in H3. 
 
    eapply c_eq_soundness in IHe2. 
    rewrite in_Σ in IHe2. 
    eapply IHe2 in H4.

    clear IHe1. clear IHe2.

    destruct_ctx. rewrite in_map_iff in *. destruct_ctx.
    exists (L_inv_vars vals (x2++x1)). 
    (*rewrite L_inv_vars_app.*) subst. 
    split; try constructor; auto with eqDB.

    rewrite in_map_iff. exists (x2,x1). split;auto.
    rewrite in_prod_iff. split;auto. rewrite c_eq_soundness.

  * destruct_ctx. rewrite in_map_iff in H.
    destruct_ctx. destruct x0. rewrite map_app in H.
    specialize IHe1 with vals. specialize IHe2 with vals. 
    pose proof (c_seq_ctx IHe1 IHe2). apply c_eq_soundness with (s:=s) in H2.
    rewrite H2. subst. rewrite L_inv_trace_app in H0. c_inversion.
    constructor; rewrite in_Σ;
    rewrite in_prod_iff in H1;destruct_ctx.
    ** exists (L_inv_trace (map vals l));split;auto.
       rewrite in_map_iff. exists l. split;auto.
    ** exists (L_inv_trace (map vals l0));split;auto.
       rewrite in_map_iff. exists l0. split;auto.
Qed.*)


(*
Definition list_contract_of_Expr_vars (vals : nat -> Contract) (l : list (list nat)) := 
 map (fun l0 => L_inv_trace (map vals l0)) l.
*)


Definition nat_inclb  := inclb (list_eq_dec Nat.eq_dec).

Definition expr_eqb (e0 e1 : Expr) := nat_inclb (L_Expr e0) (L_Expr e1) && nat_inclb (L_Expr e1) (L_Expr e0).

Definition expr_eq e0 e1 := incl (L_Expr e0) (L_Expr e1) /\ incl (L_Expr e1) (L_Expr e0).

Lemma expr_eq_reflect : forall (e0 e1 : Expr), reflect (expr_eq e0 e1) (expr_eqb e0 e1).
Proof.
intros. destruct (expr_eqb e0 e1) eqn:Heqn; unfold expr_eq;  unfold expr_eqb in Heqn;
unfold nat_inclb in *;
constructor;repeat rewrite <- inclb_iff; rewrite <- andb_true_iff;
[eauto | intro H; rewrite H in Heqn ; discriminate].
Qed.

(*
Lemma expr_L : forall (e : Expr)(vals : nat -> Contract), contract_of_Expr vals e =R= Σ (map (L_inv_vars vals) (L_Expr e)).
Proof.
induction e;intros;simpl; try solve [auto_rwd_eqDB].
- rewrite map_app. rewrite Σ_app.
  apply c_plus_ctx;auto.
- rewrite map_map. apply c_eq_completeness. intros. rewrite in_Σ. split;intros.
  * inversion H. subst.
 
    eapply c_eq_soundness in IHe1.
    rewrite in_Σ in IHe1. 
    eapply IHe1 in H3. 
 
    eapply c_eq_soundness in IHe2. 
    rewrite in_Σ in IHe2. 
    eapply IHe2 in H4.

    clear IHe1. clear IHe2.

    destruct_ctx. rewrite in_map_iff in *. destruct_ctx.
    exists (L_inv_vars vals (x2++x1)). 
    (*rewrite L_inv_vars_app.*) subst. 
    split; try constructor; auto with eqDB.

    rewrite in_map_iff. exists (x2,x1). split;auto.
    rewrite in_prod_iff. split;auto. rewrite c_eq_soundness.

  * destruct_ctx. rewrite in_map_iff in H.
    destruct_ctx. destruct x0. rewrite map_app in H.
    specialize IHe1 with vals. specialize IHe2 with vals. 
    pose proof (c_seq_ctx IHe1 IHe2). apply c_eq_soundness with (s:=s) in H2.
    rewrite H2. subst. rewrite L_inv_trace_app in H0. c_inversion.
    constructor; rewrite in_Σ;
    rewrite in_prod_iff in H1;destruct_ctx.
    ** exists (L_inv_trace (map vals l));split;auto.
       rewrite in_map_iff. exists l. split;auto.
    ** exists (L_inv_trace (map vals l0));split;auto.
       rewrite in_map_iff. exists l0. split;auto.
Qed.*)

(*
Lemma incl_L_Expr : forall e0 e1 f, incl (L_Expr e0) (L_Expr e1) -> 
incl (L (contract_of_Expr f e0)) (L (contract_of_Expr f e1)).
Proof.
unfold incl in*;intros.
intros. unfold incl in*. intros.*)

Reserved Notation "c0 =ACI= c1" (at level 63).

Inductive c_aci : Contract -> Contract -> Prop :=
  | aci_plus_assoc c0 c1 c2 : (c0 _+_ c1) _+_ c2 =ACI= c0 _+_ (c1 _+_ c2)
  | aci_plus_comm c0 c1: c0 _+_ c1 =ACI= c1 _+_ c0
  | aci_plus_idemp c : c _+_ c =ACI= c 
  | aci_refl c : c =ACI= c
  | aci_sym c0 c1 (H: c0 =ACI= c1) : c1 =ACI= c0
  | aci_trans c0 c1 c2 (H1 : c0 =ACI= c1) (H2 : c1 =ACI= c2) : c0 =ACI= c2
  | aci_plus_ctx c0 c0' c1 c1' (H1 : c0 =ACI= c0') (H2 : c1 =ACI= c1') : c0 _+_ c1 =ACI= c0' _+_ c1'
  where "c1 =ACI= c2" := (c_aci c1 c2).

Hint Constructors c_aci : eqDB.

Add Parametric Relation : Contract c_aci
  reflexivity proved by aci_refl
  symmetry proved by aci_sym
  transitivity proved by aci_trans
  as Contract_aci_setoid.

Add Parametric Morphism : CPlus with
signature c_aci ==> c_aci ==> c_aci as c_aci_plus_morphism.
Proof.
  intros. auto with eqDB.
Qed.

(*
Lemma c_aci_reflect_Expr : forall (l0 l1 : list (list nat)), 
reflect (forall(f : nat -> Contract), (L_inv_Expr f l0) =ACI= (L_inv_Expr f l1)) (nat_inclb l0 l1 && nat_inclb l1 l0).
Proof. Admitted. 
*)
Lemma aci_i_c_eq : forall c0 c1, c0 =ACI= c1 -> c0 =R= c1.
Proof. Admitted.

Lemma Σ_map_Failure : forall (A:Type)(l:list A),
Σ (map (fun _ : A => Failure) l) =R= Failure.
Proof.
induction l;intros;simpl;auto with eqDB.
rewrite IHl. auto with eqDB.
Qed.


Lemma Success_neq_Failure : ~ (Success =R= Failure).
Proof.
intro. rewrite <- Matches_iff_c_eq in H. specialize H with [].
destruct H. pose proof MSuccess. apply H in H1. c_inversion.
Qed.

Lemma Success_plus_neq_Failure : forall c, ~ (Success _+_ c =R= Failure).
Proof.
intros. intro H. rewrite <- Matches_iff_c_eq in H. specialize H with [].
destruct H. assert (HA : [] =~ Failure -> False). intros.
inversion H1. auto with cDB.
Qed.

Lemma Event_plus_neq_Failure : forall c e, ~ (Event e _+_ c =R= Failure).
Proof.
intros. intro H. rewrite <- Matches_iff_c_eq in H. specialize H with [e].
destruct H. assert (HA : [e] =~ Failure -> False). intros.
inversion H1. auto with cDB.
Qed.

Lemma Σ_R_plus : forall c0 c1, c0 _+_ c1 =R= Failure -> Failure =R= c0.
Proof.
intros. rewrite <- Matches_iff_c_eq in *.
intros. specialize H with s. destruct H. split;intros.
- apply H0 in H1. apply H in H1. inversion H1.
- apply H. auto with cDB.
Qed.




Section Σ_f.
  Variable A : Type.
  Hypothesis eq_dec : forall (x0 x1 : A), {x0 = x1} + {x0 <> x1}.

(*
  Lemma in_Σ_idemp_f : forall (x:A) (l1 : list A), 
  (forall f : A -> Contract, f x _+_ Σ (map f l1) =R= Σ (map f l1)) -> In x l1.
  Proof.
  induction l1;intros;simpl in*. specialize H with (fun _ => Success).
  simpl in H. auto_rwd_eqDB. rewrite c_plus_neut in H.
  auto using Success_neq_Failure.

  destruct (in_dec eq_dec x l1). auto.
  specialize H with (fun c => if eq_dec c a then Failure
                              else if eq_dec c x then Success else Failure).
  
  simpl in H. destruct (eq_dec a a); try contradiction.
  destruct (eq_dec x x); try contradiction.
  destruct (eq_dec x a).
  - subst. now left.
  - rewrite c_plus_neut_l in H.
    rewrite map_ext_in with (g:= fun _ => Failure) in H.
    * rewrite Σ_map_Failure in H. rewrite c_plus_neut in H.
      exfalso. auto using Success_neq_Failure.
    * intros. destruct (eq_dec a0 a);auto.
      destruct (eq_dec a0 x);auto. subst. contradiction.
  Qed.*)

  Lemma Σ_map_in_Failure : forall (l : list A) c,
      Σ (map (fun x : A => if in_dec eq_dec x l then Failure else c) l) =R= Failure.
  Proof.
  intros. rewrite map_ext_in with (g:=fun _ => Failure).
  apply Σ_map_Failure. intros. destruct (in_dec eq_dec a l);auto.
  contradiction.
  Qed.

  Lemma incl_Σ_idemp_f : forall (l1 l2 : list A), 
  (forall (f : A -> Contract), Σ (map f l2) =R= Σ (map f (l1++l2))) -> incl l1 l2.
  Proof. 
  induction l1;intros;simpl;auto_rwd_eqDB. apply incl_nil_l.
  simpl in H. symmetry in H.
  apply incl_cons.
  - destruct (in_dec eq_dec a l2); auto. 
    specialize H with (fun x => if in_dec eq_dec x l2 then Failure else Success).
    rewrite map_app in H. rewrite Σ_app in H.
    destruct (in_dec eq_dec a l2);try contradiction.
    rewrite Σ_map_in_Failure in H. rewrite c_plus_neut in H.
    apply Success_plus_neq_Failure in H. contradiction.
  - apply IHl1. intros. destruct (in_dec eq_dec a (l1++l2)).
    * rewrite <- (in_Σ_idemp ((map f (l1 ++ l2)))). symmetry.
      eauto. auto using in_map.
    * specialize H with (fun x => if in_dec eq_dec x (l1++l2) then f x else Failure).
      simpl in H. destruct (in_dec eq_dec a (l1 ++ l2)); try contradiction.
    rewrite c_plus_neut_l in H.
    setoid_rewrite map_ext_in with (g:= f) in H.
    symmetry. auto.
      ** intros. destruct (in_dec eq_dec a0 (l1 ++ l2));auto;try contradiction.
      ** intros. destruct (in_dec eq_dec a0 (l1 ++ l2));auto;try contradiction.
         exfalso. apply n1. apply in_or_app. now right.
  Qed.

  Lemma incl_Σ_c_eq_f_aux : forall (l1 l2 : list A), 
  (forall (f:A -> Contract), Σ (map f l1) =R= Σ (map f l2)) -> incl l1 l2.
  Proof.
  intros. apply incl_Σ_idemp_f.  intros.
  rewrite map_app. rewrite Σ_app. rewrite H. auto_rwd_eqDB.
  Qed.

  Theorem incl_Σ_c_eq_f : forall (l1 l2 : list A), 
  (forall (f:A -> Contract), Σ (map f l1) =R= Σ (map f l2)) -> incl l1 l2 /\ incl l2 l1.
  Proof. 
  intros. apply incl_Σ_c_eq_f_aux in H as H'. symmetry in H.
  apply incl_Σ_c_eq_f_aux in H. split;auto.
  Qed.

End Σ_f.

Lemma c_eq_reflect_Expr_aux : forall (l0 l1 : list (list nat)), 
reflect (forall (f : list nat -> Contract), Σ (map f l0) =R= Σ (map f l1))
                                         (nat_inclb l0 l1 && nat_inclb l1 l0).
Proof.
intros. destruct ((nat_inclb l0 l1 && nat_inclb l1 l0)) eqn:Heqn; unfold nat_inclb in*;constructor.
- rewrite andb_true_iff in Heqn; repeat rewrite inclb_iff in Heqn.
  destruct Heqn. intros. apply incl_Σ_c_eq; auto using incl_map.
- rewrite andb_false_iff in Heqn. repeat rewrite inclb_false_iff in Heqn.
  intro H. apply incl_Σ_c_eq_f in H. destruct H. destruct Heqn;contradiction.
  apply (list_eq_dec Nat.eq_dec).
Qed.

Fixpoint flatten (c: Contract) : list Contract :=
match c with
| c0 _+_ c1 => flatten c0 ++ (flatten c1)
| _ => [c]
end.
(*
Lemma Σ_ACI_in : forall (l0 l1 : list Contract),
a _+_ Σ l0 =ACI= Σ l1 ->*)
(*
Definition ntp (c : Contract) := ~(exists c0 c1, c = c0 _+_ c1).

Definition flatlist (l : list Contract) := Forall ntp l.

Lemma ACI_0 : Success =ACI= Failure -> False.
Proof.
intros. apply aci_i_c_eq in H. apply Success_neq_Failure in H. 
auto.
Qed.

Lemma ACI_1 : forall c, Success _+_ c  =ACI= Failure -> False.
Proof.
intros. eapply Success_plus_neq_Failure.
eauto using aci_i_c_eq.
Qed.*)
(*
Lemma Σ_ACI_Failure : forall (l : list Contract) , flatlist l ->
Σ l =ACI= Failure -> l = [] \/ Forall (fun c => c=Failure) l.
Proof.
induction l;intros.
- now left.
- right. simpl in H0. unfold flatlist in H. rewrite Forall_forall in *.
intros. apply H in H1. unfold ntp in H1. destruct a eqn:Heqn.
* apply ACI_1 in H0. contradiction.
**)

Inductive NotPlus : Contract -> Prop :=
| NPSuccess : NotPlus Success
| NPFailure : NotPlus Failure
| NPEvent e : NotPlus (Event e)
| NPSeq c0 c1 : NotPlus (c0 _;_ c1).

Inductive NotPlusList : list Contract -> Prop :=
| NPNil : NotPlusList []
| NPCons c l (H0 : NotPlus c) (H1 : NotPlusList l): NotPlusList (c::l).

(*served Notation "c0 =I= c1" (at level 63).
Inductive c_i : Contract -> Contract -> Prop :=
  | i_plus_idemp c : c _+_ c =I= c 
  | i_refl c : c =I= c
  | i_sym c0 c1 (H: c0 =I= c1) : c1 =I= c0
  | i_trans c0 c1 c2 (H1 : c0 =I= c1) (H2 : c1 =I= c2) : c0 =I= c2
  | i_plus_ctx c0 c0' c1 c1' (H1 : c0 =I= c0') (H2 : c1 =I= c1') : c0 _+_ c1 =I= c0' _+_ c1'
  where "c1 =I= c2" := (c_i c1 c2).

Hint Constructors c_i : eqDB.

Add Parametric Relation : Contract c_i
  reflexivity proved by i_refl
  symmetry proved by i_sym
  transitivity proved by i_trans
  as Contract_i_setoid.

Add Parametric Morphism : CPlus with
signature c_i ==> c_i ==> c_i as c_i_plus_morphism.
Proof.
  intros. auto with eqDB.
Qed.*)

Definition In_mod_ACI (c : Contract) (l : list Contract) := exists c', c' =ACI= c /\ In c' l.

Lemma Σ_ACI_in : forall l c, In c l -> c _+_ Σ l =ACI= Σ l.
Proof.
induction l;intros. simpl in H. contradiction.
simpl in H. destruct H.
- subst. simpl. rewrite <- aci_plus_assoc. now rewrite aci_plus_idemp.
- simpl. rewrite <- aci_plus_assoc. rewrite (aci_plus_comm c).
  rewrite aci_plus_assoc. rewrite IHl;auto. reflexivity.
Qed.

Lemma Σ_ACI_plus : forall c0 c1, c0 _+_ c1 =ACI= Failure -> Failure =ACI= c0.
Proof. intros. apply aci_i_c_eq in H. apply Σ_R_plus in H.

Lemma ACI_dec : forall c0 c1, {c0 =ACI= c1} + {~(c0 =ACI= c1)}.
Proof. Admitted.

Lemma Σ_ACI_plus : forall c0 c1, Failure =ACI= c0 _+_ c1 -> Failure =ACI= c0.
Proof.
induction c0;intros.
- exfalso. eapply Success_plus_neq_Failure. symmetry. eauto using aci_i_c_eq.
- reflexivity.
-  exfalso.  eapply Event_plus_neq_Failure. symmetry. eauto using aci_i_c_eq.
- 
Event_plus_neq_Failure
intros. destruct (ACI_dec Failure c0);auto.
exfalso. apply n.
- destruct
induction c0;intros.


Lemma Σ_ACI_plus_aux : forall l c, Failure =ACI= c _+_ Σ l -> Failure =ACI= c /\ Failure =ACI= Σ l.
Proof.
induction l;intros. simpl.
- split;auto with eqDB. simpl in H. inversion H.
  * subst.
intros. remember (c1 _+_ c2). induction H.
induction c0;intros.
- inversion H. subst.
intros. induction H.

Failure =ACI= Σ l -> (forall c', In c' l -> c' =ACI= Failure).
Proof.



Lemma In_mod_ACI_dec : forall c l, {In_mod_ACI c l} + {~(In_mod_ACI c l)}.
Proof. Admitted.
Check Contract_eq_dec.
Check in_dec.
Lemma Σ_ACI_Failure : forall (l : list Contract),
Failure =ACI= Σ l -> (forall c', In c' l -> c' =ACI= Failure).
Proof.
induction l;intros.
- simpl in H0. contradiction.
- simpl in H0. destruct H0.
  * subst. simpl in H.
    destruct (In_mod_ACI_dec c' l).
  * rewrite Σ_ACI_in in H;auto. apply IHl in H. destruct H.
    ** subst. simpl in*. contradiction.
    ** right. split;auto. intuition. discriminate.
       intros. destruct H. simpl in H0. destruct H0;subst;auto.
  *
      *** subst. auto.
      *** auto. contradiction. intro H2.



Lemma Σ_ACI_aux : forall (l : list Contract) c,
Failure _+_ c =ACI= Σ l -> In_mod_ACI c (Failure::l). 
Proof.
induction l;intros. simpl in H. exists Failure. split;auto with eqDB.
apply in_eq.
simpl in H.
 apply in_nil in H0;contradiction.
simpl in H0. destruct H0.
- subst. apply IHl0. simpl in H.

Lemma Σ_ACI : forall (l0 l1 : list Contract),
Σ l0 =ACI= Σ l1 -> (forall c, In c l0 -> In_mod_ACI c l1).
Proof.
induction l0;intros. apply in_nil in H0;contradiction.
simpl in H0. destruct H0.
- subst. apply IHl0. simpl in H.



Lemma test : forall a b, NotPlus a -> a =ACI= b -> a =I= b. 
Proof.
 induction H0; try solve [inversion H | auto with eqDB].
- inversion H. subst. symmetry.
 Admitted.
Lemma test : forall a b, NotPlus a -> NotPlus b -> a =ACI= b -> a = b.
Proof.
intros. induction H1; try solve [inversion H | auto ].
- symmetry. auto.
- transitivity c1;auto. inversion H;intros; inversion H0;auto;subst.
 a =ACI= Σ l -> In a l.
Proof.
intros. induction H.

Lemma Σ_ACI_flatten_aux : forall (l0 l1 : list Contract), NotPlusList l0
-> NotPlusList l1 -> Σ l0 =ACI= Σ l1 -> incl l0 l1.
Proof.
induction l0;intros;simpl in*. apply incl_nil_l.
apply incl_cons.
- inversion H. apply IHl0 in H5;auto with eqDB. inversion H4.
  * subst.

Lemma NotPlus_eq : forall c0 c1, NotPlus c0 -> c0 =ACI= c1 -> c0 = c1.
Proof.



Lemma test : forall c l, NotPlusList l -> c =ACI= Σ l -> (forall c', In c' l -> c=c').
Proof.
intros. generalize dependent c'. generalize dependent c.
induction H;intros.
- apply in_nil in H1;contradiction.
- inversion H0.
  * subst. simpl in*. destruct H2. subst. rewrite  simpl in H2. destruct H2.
  * subst.


Proof.
Lemma not_plus : forall a l, NotPlusList (a::l) -> Failure =ACI= Σ (a :: l) -> 
Failure =ACI= Σ l.
Proof.
intros. generalize dependent a. induction H.
- now simpl.
- intros.
induction l;intros. simpl; auto with eqDB.

simpl in H. rewrite <- aci_plus_assoc in H.
apply IHl in H. rewrite <- H.


Lemma Σ_ACI_Failure : forall (l : list Contract) , NotPlusList l -> 
Failure =ACI= Σ l <-> l = [] \/ Forall (fun c => c = Failure) l. 
Proof.
induction l;intros. simpl.
split;intros;auto with eqDB.
inversion H. subst. apply IHl in H3. split;intros.
- right. rewrite Forall_forall. intros. simpl.

Lemma Σ_ACI_in : forall (l : list Contract) c, NotPlusList l -> 
c0 =ACI= Σ l <-> (forall c', In c' l -> c=c').
Proof.


Lemma Σ_ACI_in : forall (l : list Contract) c,
Failure _+_ c =ACI= Σ l <-> (forall c', In c' l -> c=c').
Proof.
induction l;split;intros. 
- simpl in *. destruct H0.
- simpl.
 apply in_nil in H0. contradiction.
- simpl.
simpl in H0. destruct H0. subst.
erewrite IHl.
induction l0;intros;simpl in*. apply incl_nil_l.
apply incl_cons.



Lemma Σ_ACI_in : forall (A: Type)(l0 l1 : list A)(f : A -> Contract),
Σ (map f l0) =ACI= Σ (map f l1) -> incl l0 l1 /\ incl l1 l0.
Proof.
induction l0;intros;simpl in*. induction H.


Lemma my_test : forall (l0 l1 : list (list nat)),
(forall (f : list nat -> Contract), Σ (map f l0) =ACI= Σ (map f l1)) <->
(forall (f' : nat -> Contract), Σ (map (L_inv_vars f') l0) =ACI= Σ (map (L_inv_vars f') l1)).
Proof.

Lemma Success_test : forall l, L_inv_vars (fun _ : nat => Success) l =R= Success.
Proof.
induction l;intros;simpl. reflexivity.
now rewrite c_seq_neut_l.
Qed.

Lemma in_Σ_idemp : forall l c, c _+_ Σ l =R= Σ l -> c =R= Failure \/ exists c', In c' l  /\ c=R=c'.
Proof.
induction l;intros. simpl in H. left. rewrite <- H.
auto_rwd_eqDB. simpl in H. exists e. split;auto. apply in_eq.
simpl.

Lemma test_sigma : forall l1 l2, Σ l1 =R= Σ l2 -> (forall x, In x l1 -> exists x', x' =R= x /\ In x' l2).
Proof.
induction l1;intros. simpl in H0. contradiction.
simpl in *. destruct H0. subst.

(*Lemma test1 : forall a l1 l2, 
 (forall f : nat -> Contract, L_inv_vars f a _+_ Σ (map (L_inv_vars f) (l1 ++ l2)) =R= Σ (map (L_inv_vars f) l2)) ->
incl l1 l2.
Proof.
induction a;intros. simpl in H.
- induction l1. apply incl_nil_l. simpl in H.
  apply incl_cons.
  *
induction l1;intros. apply incl_nil_l.
apply incl_cons.
- simpl in*.*)

Lemma test: forall l1 l2 ,(forall (f : nat -> Contract), Σ (map (L_inv_vars f) l2) =R= Σ (map (L_inv_vars f) (l1++l2))) ->
incl l1 l2.
Proof.
induction l1;intros;simpl;auto_rwd_eqDB. apply incl_nil_l.
  simpl in H. symmetry in H.
  apply incl_cons.
  - destruct (in_dec (list_eq_dec Nat.eq_dec) a l2); auto. 
    specialize H with (fun x => if in_dec (Nat.eq_dec) x (concat l2) then Failure else Success).
    rewrite map_app in H. rewrite Σ_app in H.
    * destruct a. simpl in H. setoid_rewrite <- IHl1 in H. 
    assert (HA: L_inv_vars (fun x : nat => if in_dec Nat.eq_dec x (concat l2) then Failure else Success) a =R= Failure).
    rewrite map_ext_in.
    destruct (in_dec eq_dec a l2);try contradiction.
    rewrite Σ_map_in_Failure in H. rewrite c_plus_neut in H.
    apply Success_plus_neq_Failure in H. contradiction.
  - apply IHl1. intros. destruct (in_dec eq_dec a (l1++l2)).
    * rewrite <- (in_Σ_idemp ((map f (l1 ++ l2)))). symmetry.
      eauto. auto using in_map.
    * specialize H with (fun x => if in_dec eq_dec x (l1++l2) then f x else Failure).
      simpl in H. destruct (in_dec eq_dec a (l1 ++ l2)); try contradiction.
    rewrite c_plus_neut_l in H.
    setoid_rewrite map_ext_in with (g:= f) in H.
    symmetry. auto.
      ** intros. destruct (in_dec eq_dec a0 (l1 ++ l2));auto;try contradiction.
      ** intros. destruct (in_dec eq_dec a0 (l1 ++ l2));auto;try contradiction.
         exfalso. apply n1. apply in_or_app. now right.
  Qed.



Lemma test: forall l0 l1, 
(forall f : nat -> Contract, Σ (map (L_inv_vars f) l0) =R= Σ (map (L_inv_vars f) l1)) ->
(forall f : list nat -> Contract, Σ (map f l0) =R= Σ (map  f l1)).
Proof.
induction l0;intros. simpl in*. destruct l1. now simpl.
simpl in H. specialize H with (fun _ => Success). 
rewrite Success_test in H. exfalso. eapply Success_plus_neq_Failure.
symmetry. eauto.
simpl in*. destruct l1. simpl in*. setoid_rewrite IHl0 in H.
rewrite <- H. apply c_plus_ctx.
- instantiate (a::l1). eapply in_Σ_idemp.

 destruct l. simpl in*.
exfalso. eapply Success_plus_neq_Failure. symmetry in H. eauto.
specialize H with (fun _ => Success). simpl in H.
*)
Lemma c_eq_reflect_Expr : forall e0 e1, reflect (forall (f : nat -> Contract), (contract_of_Expr f e0) =R= (contract_of_Expr f e1)) 
                                                                 (nat_inclb (L_Expr e0) (L_Expr e1) && nat_inclb (L_Expr e1) (L_Expr e0)).
Proof. 
intros. destruct (c_eq_reflect_Expr_aux (L_Expr e0) (L_Expr e1));constructor.
- intros. rewrite <- L_inv_L_ceq. rewrite <- L_inv_L_ceq.
  unfold L_inv_Expr. auto.
- intro H. apply n. intros. setoid_rewrite <- L_inv_L_ceq in H. 
  unfold L_inv_Expr in H. eauto using test.
Qed.

(*
  Lemma Σ_app_comm_f : forall (l1 l2 : list A)(f:A -> Contract),
   Σ (map f (l1++l2)) =R= Σ (map f(l2++l1)).
  Proof.
  intros. repeat rewrite map_app. repeat rewrite Σ_app.
  auto_rwd_eqDB.
  Qed.*)




(*
Lemma Σ_map_f : forall (A : Type) (l0 l1 : list A), 
(forall f : A -> Contract, Σ (map f l0) =R= Σ (map f l1)) -> incl l0 l1.
Proof.
induction l0;simpl;intros. apply incl_nil_l.
apply incl_cons.*)

(*
Lemma c_eq_reflect_Expr : forall e0 e1 , reflect (forall (f : nat -> Contract), (contract_of_Expr f e0) =R= (contract_of_Expr f e1)) 
                                                                 (nat_inclb (L_Expr e0) (L_Expr e1) && nat_inclb (L_Expr e1) (L_Expr e0)).
Proof.
intros. destruct (c_aci_reflect_Expr (L_Expr e0) (L_Expr e1));constructor.
- intros. repeat rewrite <- L_inv_L_ceq. auto using aci_i_c_eq.
- intro H. apply n. intros. setoid_rewrite <- L_inv_L_ceq in H.
  unfold L_inv_Expr in *. clear n. 
unfold nat_inclb in*;constructor.
-


Lemma test: forall l0 l1 (f : nat -> Contract),
    Σ (map (L_inv_vars f) l0) =R= Σ (map (L_inv_vars f) l1) -> incl l0 l1.
Proof.
induction l0;simpl;intros. apply incl_nil_l.
apply incl_cons. generalize dependent f. auto. rewrite <- Matches_iff_c_eq in H.
setoid_rewrite in_Σ in H.
*)

Lemma L_Σ : forall l, L (Σ l) = flat_map L l.
Proof.
induction l;intros;simpl;auto. now rewrite IHl.
Qed.


Lemma c_eq_reflect_Expr : forall e0 e1, reflect (forall (f : nat -> Contract), (contract_of_Expr f e0) =R= (contract_of_Expr f e1)) 
                                                                 (nat_inclb (L_Expr e0) (L_Expr e1) && nat_inclb (L_Expr e1) (L_Expr e0)).
Proof. 
intros. destruct (nat_inclb (L_Expr e0) (L_Expr e1) && nat_inclb (L_Expr e1) (L_Expr e0)) eqn:Heqn;
unfold nat_inclb in*;constructor;intros.
- rewrite andb_true_iff in Heqn; repeat rewrite inclb_iff in Heqn.
  destruct Heqn. rewrite <- L_inv_L_ceq. rewrite <- L_inv_L_ceq.
  unfold L_inv_Expr. apply incl_Σ_c_eq; apply incl_map;auto.
- intro H. rewrite andb_false_iff in Heqn. repeat rewrite inclb_false_iff in Heqn.
   setoid_rewrite <- L_inv_L_ceq in H.    unfold L_inv_Expr in H. rewrite <- L_inv_L_ceq.
Check incl_Σ_c_eq_f.
Check incl_Σ_c_eq_f ((list_eq_dec list_eq_dec Nat.eq_dec)) (L_Expr e0)).
  apply (incl_Σ_c_eq_f Nat.eq_dec) in H.
 setoid_rewrite <- L_inv_L_ceq in H. 
  unfold L_inv_Expr in H. rewrite <- L_inv_L_ceq.
  unfold L_inv_Expr. rewrite <- Matches_iff_c_eq. rewrite Matches_eq_iff_incl_and.
  repeat rewrite L_Σ. 
  intro H. destruct_ctx. rewrite andb_false_iff in Heqn. repeat rewrite inclb_false_iff in Heqn.
  destruct Heqn.
  * apply H1. unfold incl in*. intros. unfold L_inv_vars in H.
    setoid_rewrite in_flat_map in H.   
    specialize H with (nth 0 (L (L_inv_vars f a))). setoid_rewrite in_flat_map in H.
  destruct Heqn. eapply incl_map in H0. eapply incl_map in H.
  repeat rewrite L_Σ. unfold incl.




repeat rewrite <- inclb_iff. rewrite <- andb_true_iff.
eauto.
[ eauto | intro H; rewrite H in Heqn; discriminate].
Qed.

Lemma c_eqP : forall (e0 e1 : Expr)(vals : nat -> Contract), 
nat_inclb (L_Expr e0) (L_Expr e1) && nat_inclb (L_Expr e1) (L_Expr e0) = true -> (contract_of_Expr vals e0) =R= (contract_of_Expr vals e1).
Proof.
intros. unfold nat_inclb in*. rewrite andb_true_iff in H. 
repeat rewrite inclb_iff in H. rewrite <- L_inv_L_ceq. 
rewrite <- L_inv_L_ceq. apply c_eq_completeness.
rewrite Matches_eq_iff_incl_and.
destruct (nat_inclb (L_Expr e0) (L_Expr e1) &&
    nat_inclb (L_Expr e1) (L_Expr e0)) eqn:Heqn;
unfold nat_inclb in*;constructor; rewrite <- Matches_iff_c_eq; rewrite Matches_eq_iff_incl_and;
repeat rewrite <- inclb_iff. rewrite <- andb_true_iff.
eapply Heqn.
eauto.
[ eauto | intro H; rewrite H in Heqn; discriminate].
Qed.

 repeat rewrite expr_L. apply c_eq_completeness. intros. repeat rewrite in_Σ. 
destruct (expr_eq_reflect e0 e1);try discriminate.
unfold expr_eq in e. split;intros;destruct_ctx;rewrite in_map_iff in H0;
destruct_ctx;exists x; split;auto; rewrite in_map_iff; exists x0; split ; auto.
Qed.

Ltac intern vars e :=
  let rec loop n vars' :=
    match vars' with
    | [] =>
      let vars'' := eval simpl in (rev (e::(rev vars))) in
      constr:((n, vars''))
    | e :: ?vars'' => constr:((n, vars))
    | _ :: ?vars'' => loop (S n) vars''
    end in
  loop 0 vars.

Ltac reify_expr vars c :=
  match c with
  | ?c1 _+_ ?c2 =>
    let r1 := reify_expr vars c1 in
    match r1 with
    | (?qe1, ?vars') =>
      let r2 := reify_expr vars' c2 in
      match r2 with
      | (?qe2, ?vars'') => constr:((EPlus qe1 qe2, vars''))
      end
    end
  | ?c1 _;_ ?c2 =>
    let r1 := reify_expr vars c1 in
    match r1 with
    | (?qe1, ?vars') =>
      let r2 := reify_expr vars' c2 in
      match r2 with
      | (?qe2, ?vars'') => constr:((ESeq qe1 qe2, vars''))
      end
    end
  | _ =>
    let r := intern vars c in
    match r with
    | (?n, ?vars') => constr:((Var n, vars'))
    end
  end.

Fixpoint fun_of_list_aux (l : list  (nat * Contract)) :=
match l with
| [] => (fun  _ => Failure)
| (n,c)::l' => let f2 := fun_of_list_aux l'
               in (fun t => if Nat.eq_dec n t then c else f2 t)
end.

Definition fun_of_list l := fun_of_list_aux (combine (seq 0 (length l)) l).

Ltac csl_solve :=
  match goal with
  | |- ?c1 =R= ?c2 =>
    let r1 := reify_expr (@nil Contract) c1 in
    match r1 with
    | (?qe1, ?vm') =>
      let r2 := reify_expr vm' c2 in
      match r2 with
      | (?qe2, ?vm'') => exact (@c_eqP qe1 qe2 (fun_of_list vm'') eq_refl) 
      end
    end
  end.


Lemma test2 : forall c0 c0' c1 c1', (c0 _+_ c1) _;_ (c0' _+_ c1') =R= 
                     c0 _;_ c0' _+_ c0 _;_ c1' _+_ c1 _;_ c0' _+_ c1 _;_ c1'. 
Proof. intros. csl_solve. Qed.




