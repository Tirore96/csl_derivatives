Require Import CSL.Contract2.  
Require Import CSL.Order.
Require Import Lists.List.
Require Import Sorting.Permutation.
Require Import Sorting.Mergesort.
Require Import Sorting.Sorted.
Require Import Bool.Bool.
Require Import Bool.Sumbool.
Require Import List Setoid Permutation Sorted Orders.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Set Implicit Arguments.

Module Import TraceSort := Sort TraceOrder.

Reserved Notation "c0 =R= c1" (at level 63).

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

Hint Constructors c_eq : eqDB.

Add Parametric Relation : Contract c_eq
  reflexivity proved by c_refl
  symmetry proved by c_sym
  transitivity proved by c_trans
  as Contract_setoid.

Add Parametric Morphism : CPlus with
signature c_eq ==> c_eq ==> c_eq as c_eq_plus_morphism.
Proof.
  intros. auto with eqDB.
Qed.

Add Parametric Morphism : CSeq with
signature c_eq ==> c_eq ==> c_eq as c_eq_seq_morphism.
Proof.
  intros. auto with eqDB.
Qed.


Ltac c_inversion :=
  (repeat match goal with
         | [ H: ?s =~ _ _+_ _ |- _ ] => inversion H; clear H
         | [ H: ?s =~ _ _;_ _ |- _ ] => inversion H; clear H
         | [ H: _ =~ Failure |- _ ] => inversion H
         | [ H: [] =~ Success |- _ ] => fail
         | [ H: _ =~ Success |- _ ] => inversion H; clear H
         end);auto with cDB eqDB;subst.



Lemma c_eq_soundness : forall (c0 c1 : Contract), c0 =R= c1 -> (forall s : Trace, s =~ c0 <-> s =~ c1).
Proof.
intros c0 c1 H. induction H ;intros; try solve [split;intros;c_inversion].
  * split;intros;c_inversion; [ rewrite <- app_assoc | rewrite app_assoc ]; auto with cDB.
  * rewrite <- (app_nil_l s). split;intros;c_inversion. (*app_nil_l to help inversion*)
  * rewrite <- (app_nil_r s) at 1. split;intros;c_inversion. subst.
    repeat rewrite app_nil_r in H1. now rewrite <- H1.
  * now symmetry.
  * eauto using iff_trans.
  * split;intros; inversion H1; [ rewrite IHc_eq1 in H4 
                                | rewrite IHc_eq2 in H4
                                | rewrite <- IHc_eq1 in H4 
                                | rewrite <- IHc_eq2 in H4];auto with cDB.
  * split;intros; c_inversion; constructor;
                                [ rewrite <- IHc_eq1
                                | rewrite <- IHc_eq2
                                | rewrite IHc_eq1
                                | rewrite IHc_eq2];auto.
Qed.

Lemma Matches_plus_comm : forall c0 c1 s, s =~ c0 _+_ c1 <-> s =~ c1 _+_ c0.
Proof. auto using c_eq_soundness  with eqDB. Qed.

Lemma Matches_plus_neut_l : forall c s, s =~ Failure _+_ c <-> s =~ c.
Proof. intros. rewrite Matches_plus_comm. auto using c_eq_soundness  with eqDB. Qed.

Lemma Matches_plus_neut_r : forall c s, s =~ c _+_ Failure <-> s =~ c.
Proof. auto using c_eq_soundness  with eqDB. Qed.

Lemma Matches_seq_neut_l : forall c s, s =~ (Success _;_ c) <-> s =~ c.
Proof. auto using c_eq_soundness  with eqDB. Qed.

Lemma Matches_seq_neut_r : forall c s, s =~ c _;_ Success <-> s =~ c.
Proof. auto using c_eq_soundness  with eqDB. Qed.

Lemma Matches_seq_assoc : forall c0 c1 c2 s, s =~ (c0 _;_ c1) _;_ c2  <-> s =~ c0 _;_ (c1 _;_ c2).
Proof. auto using c_eq_soundness  with eqDB. Qed.

Hint Rewrite Matches_plus_neut_l 
             Matches_plus_neut_r 
             Matches_seq_neut_l
             Matches_seq_neut_r : eqDB.

Lemma c_plus_neut_l : forall c, Failure _+_ c =R= c.
Proof. intros. rewrite c_plus_comm. auto with eqDB.
Qed.

Hint Rewrite c_plus_neut_l 
             c_plus_neut 
             c_seq_neut_l
             c_seq_neut_r
             c_seq_failure_l 
             c_seq_failure_r 
             c_distr_l
             c_distr_r : eqDB.


Fixpoint monoms (c : Contract) : list Trace :=
match c with
| Success => [[]]
| Failure => []
| Event e => [[e]]
| c0 _+_ c1 => (monoms c0) ++ (monoms c1)
| c0 _;_ c1 => map (fun p => (fst p)++(snd p)) (list_prod (monoms c0) (monoms c1))
end.

Lemma monoms_seq : forall (s0 s1: Trace)(c0 c1 : Contract), In s0 (monoms c0) -> In s1 (monoms c1) -> In (s0++s1) (monoms (c0 _;_ c1)).
Proof.
intros. simpl. rewrite in_map_iff. exists (s0,s1). split;auto.
rewrite in_prod_iff. split;auto. 
Qed. 

Fixpoint seq_fold (l : list Contract) :=
match l with
| [] => Success
| a::l' => a _;_ (seq_fold l')
end.

Lemma seq_fold_map : forall (s:Trace), s =~ seq_fold (map Event s).
Proof.
induction s;simpl;auto with cDB.
assert (HA: a::s = [a]++s);auto. rewrite HA; auto with cDB.
Qed.

Lemma seq_fold_app : forall (s0 s1 : list Contract)(s:Trace), s =~ seq_fold (s0 ++ s1) <-> s =~ (seq_fold s0) _;_ (seq_fold s1).
Proof.
induction s0;intros;simpl.
- now autorewrite with eqDB.
- split;intros. 
  * rewrite Matches_seq_assoc. c_inversion.
    constructor;auto. now rewrite <- IHs0.
  * rewrite Matches_seq_assoc in H. c_inversion.
    constructor;auto. rewrite IHs0;auto with cDB.
Qed.


Definition contract_of_monom (s : Trace) := seq_fold (map Event s).

Definition contract_of_monoms (l : list Trace) := plus_fold (map contract_of_monom l).


Ltac auto_rwd_eqDB := autorewrite with eqDB;auto with eqDB.

Lemma c_eq_plus_fold_app : forall (l1 l2 : list Contract), 
plus_fold (l1 ++ l2) =R= (plus_fold l1) _+_ (plus_fold l2).
Proof.
induction l1;intros;simpl;auto_rwd_eqDB.
rewrite IHl1. now rewrite c_plus_assoc.
Qed.

Ltac unfold_defs := unfold contract_of_monoms, contract_of_monom.

Lemma contract_of_monom_app : forall (l1 l2 : Trace), contract_of_monom l1 _;_ contract_of_monom l2 =R= contract_of_monom (l1++l2).
Proof.
unfold contract_of_monom. induction l1;intros;simpl; auto_rwd_eqDB.
rewrite <- IHl1. auto_rwd_eqDB.
Qed.

Hint Unfold contract_of_monoms contract_of_monom: eqDB.

Lemma monom_seq_monoms : forall (ss : list Trace) (s : Trace), contract_of_monom s _;_ contract_of_monoms ss =R=
 plus_fold (map (fun x => contract_of_monom (fst x ++ snd x)) (map (fun y : list EventType => (s, y)) ss)).
Proof.
induction ss;intros;simpl;auto_rwd_eqDB.
unfold contract_of_monoms. simpl.
auto_rwd_eqDB. apply c_plus_morph;auto using contract_of_monom_app.
Qed.

Lemma monoms_seq_monoms : forall l0 l1, contract_of_monoms l0 _;_ contract_of_monoms l1 =R=
 plus_fold (map (fun x : list EventType * list EventType => contract_of_monom (fst x ++ snd x)) (list_prod l0 l1)).
Proof.
induction l0;intros;simpl. unfold contract_of_monoms. simpl. auto_rwd_eqDB.
repeat rewrite map_app. rewrite c_eq_plus_fold_app. rewrite <- IHl0.
unfold contract_of_monoms at 1. simpl. auto_rwd_eqDB. apply c_plus_morph; auto with eqDB. 
apply monom_seq_monoms.
Qed.

Lemma monoms_ceq : forall (c : Contract), contract_of_monoms (monoms c) =R= c.
Proof.
induction c; try solve [unfold_defs;simpl;auto_rwd_eqDB].
- simpl. unfold contract_of_monoms.
  rewrite map_app. rewrite c_eq_plus_fold_app.
  auto using c_plus_morph. 
- simpl. unfold contract_of_monoms. rewrite map_map.
  rewrite <- IHc1 at 2. rewrite <- IHc2 at 2.
  symmetry. apply monoms_seq_monoms.
Qed.

Lemma c_eq_in_plus_fold_idemp : forall l c, In c l -> c _+_ plus_fold l =R= plus_fold l.
Proof.
induction l;intros;simpl; auto_rwd_eqDB.
simpl in H;contradiction.
simpl in H. destruct H. subst. all: rewrite <- c_plus_assoc.
auto_rwd_eqDB. rewrite (c_plus_comm c). rewrite c_plus_assoc. 
apply c_plus_morph;auto_rwd_eqDB.
Qed. 

Lemma c_eq_incl_plus_fold_aux : forall (l1 l2 : list Contract), incl l1 l2 -> plus_fold l2 =R= plus_fold (l1++l2).
Proof. 
induction l1;intros;simpl;auto_rwd_eqDB.
apply incl_cons_inv in H as [H0 H1].
rewrite <- IHl1;auto. now rewrite c_eq_in_plus_fold_idemp;auto.
Qed.

Lemma c_eq_plus_fold_comm_app : forall (l1 l2 : list Contract), plus_fold (l1++l2) =R= plus_fold (l2++l1).
Proof.
induction l1;intros;simpl. now rewrite app_nil_r.
repeat rewrite c_eq_plus_fold_app. rewrite <- c_plus_assoc.
rewrite c_plus_comm. apply c_plus_morph;auto_rwd_eqDB.
Qed.

Lemma c_eq_incl_plus_fold : forall (l1 l2 : list Contract), incl l1 l2 -> incl l2 l1-> plus_fold l1 =R= plus_fold l2.
Proof.
intros. rewrite (c_eq_incl_plus_fold_aux H). 
rewrite (c_eq_incl_plus_fold_aux H0). apply c_eq_plus_fold_comm_app.
Qed.

Lemma comp_equiv_destruct : forall (c0 c1: Contract),(forall s : Trace, s =~ c0 <-> s =~ c1) ->
(forall s : Trace, s =~ c0 -> s =~ c1) /\ (forall s : Trace, s =~ c1 -> s =~ c0).
Proof.
intros. split ; intros; specialize H with s; destruct H; auto.
Qed.

Lemma Matches_member : forall (s : Trace)(c : Contract), s =~ c -> In s (monoms c). 
Proof.
intros. induction H ; simpl ; try solve [auto using in_or_app || auto using in_or_app ].
rewrite in_map_iff. exists (s1,s2). rewrite in_prod_iff. split;auto.
Qed.

Lemma member_Matches : forall (s : Trace)(c : Contract), In s (monoms c) -> s =~ c. 
Proof.
intros.
eapply c_eq_soundness. symmetry. eapply monoms_ceq.
unfold contract_of_monoms. rewrite in_plus_fold.
exists (contract_of_monom s).
split. 
- rewrite in_map_iff. exists s;split;auto.
- unfold contract_of_monom. apply seq_fold_map.
Qed.

Lemma Matches_incl : forall (c0 c1 : Contract), (forall (s : Trace), s =~ c0 -> s =~ c1) -> 
incl (monoms c0) (monoms c1).
Proof.
intros. unfold incl. intros. auto using Matches_member, member_Matches.
Qed.

Lemma c_eq_completeness : forall (c0 c1 : Contract), (forall s : Trace, s =~ c0 <-> s =~ c1) -> c0 =R= c1.
Proof.
intros. rewrite <- monoms_ceq. rewrite <- (monoms_ceq c1). 
unfold contract_of_monoms. apply comp_equiv_destruct in H as [H0 H1].
apply Matches_incl in H0. apply Matches_incl in H1.
apply c_eq_incl_plus_fold; apply incl_map;auto.
Qed.


(**********Solver***********)

Inductive Expr :=
| Var : nat -> Expr
| ESuccess : Expr
| EFailure : Expr
| EPlus : Expr -> Expr -> Expr
| ESeq : Expr -> Expr -> Expr.


Fixpoint contract_of_Expr vals e :=
match e with
| Var v => vals v
| ESuccess => Success
| EFailure => Failure
| EPlus e0 e1 => (contract_of_Expr vals e0) _+_ (contract_of_Expr vals e1)
| ESeq e0 e1 => (contract_of_Expr vals e0) _;_ (contract_of_Expr vals e1)
end.

Fixpoint vars_lists_of_Expr (e : Expr) : list (list nat) :=
match e with
| Var v => [[v]]
| ESuccess => [[]]
| EFailure => []
| EPlus e0 e1 => (vars_lists_of_Expr e0) ++ (vars_lists_of_Expr e1)
| ESeq e0 e1 => map (fun (a : list nat * list nat) => let (a1,a2):=a in a1++a2) (list_prod (vars_lists_of_Expr e0) (vars_lists_of_Expr e1))
end.


Definition list_contract_of_Expr_vars (vals : nat -> Contract) (l : list (list nat)) := 
 map (fun l0 => seq_fold (map vals l0)) l.


Check forallb.
Check Nat.eq_dec.
Locate nat_dec.

Definition inclb (l0 l1 : list (list nat)) :bool := 
 forallb (fun a0 => existsb (fun a1 => if (list_eq_dec Nat.eq_dec) a0 a1 then true else false) l1) l0.

Lemma inclb_iff : forall (l0 l1 : list (list nat)), inclb l0 l1 = true <-> incl l0 l1.
Proof. unfold inclb. unfold incl. split. 
- intros. rewrite forallb_forall in H. apply H in H0. rewrite existsb_exists in H0. destruct H0 as [x [P0 P1]].
destruct (list_eq_dec Nat.eq_dec a x);subst;auto.
discriminate.
- intros. rewrite forallb_forall. intros. apply H in H0. rewrite existsb_exists. exists x. split;auto.
  destruct (list_eq_dec Nat.eq_dec x x);auto.
Qed.

Lemma incl_reflect : forall (l0 l1 : list (list nat)), reflect (incl l0 l1) (inclb l0 l1).
Proof. 
intros. destruct (inclb l0 l1) eqn:Heqn.
- constructor. now rewrite inclb_iff in Heqn.
- constructor. intro H. rewrite <- inclb_iff in H. rewrite Heqn in H. discriminate.
Qed.

Definition expr_eqb (e0 e1 : Expr) := inclb (vars_lists_of_Expr e0) (vars_lists_of_Expr e1) && inclb (vars_lists_of_Expr e1) (vars_lists_of_Expr e0).

Definition expr_eq e0 e1 := incl (vars_lists_of_Expr e0) (vars_lists_of_Expr e1) /\ incl (vars_lists_of_Expr e1) (vars_lists_of_Expr e0).

Lemma expr_eq_reflect : forall (e0 e1 : Expr), reflect (expr_eq e0 e1) (expr_eqb e0 e1).
Proof.
intros. destruct (expr_eqb e0 e1) eqn:Heqn; unfold expr_eq; unfold expr_eqb in Heqn;
constructor;repeat rewrite <- inclb_iff; auto using andb_prop.
intro H. rewrite <- andb_true_iff in H.  rewrite H in Heqn. discriminate. 
Qed.


Lemma expr_monoms : forall (e : Expr)(vals : nat -> Contract), contract_of_Expr vals e =R= plus_fold (map (fun l => seq_fold (map vals l)) (vars_lists_of_Expr e)).
Proof.
induction e;intros;simpl; try solve [auto_rwd_eqDB].
- rewrite map_app. rewrite c_eq_plus_fold_app.
  apply c_plus_morph;auto.
- rewrite map_map. apply c_eq_completeness. intros. rewrite in_plus_fold. split;intros.
  * inversion H. subst.
 
    eapply c_eq_soundness in IHe1.
    rewrite in_plus_fold in IHe1. 
    eapply IHe1 in H3. 
 
    eapply c_eq_soundness in IHe2. 
    rewrite in_plus_fold in IHe2. 
    eapply IHe2 in H4.

    clear IHe1. clear IHe2.

    destruct_ctx. rewrite in_map_iff in *. destruct_ctx.
    exists (seq_fold (map vals (x2++x1))). 
    rewrite map_app at 2. rewrite seq_fold_app. subst. 
    split; try constructor; auto with eqDB.

    rewrite in_map_iff. exists (x2,x1). split;auto.
    rewrite in_prod_iff. split;auto.

  * destruct_ctx. rewrite in_map_iff in H.
    destruct_ctx. destruct x0. rewrite map_app in H.
    specialize IHe1 with vals. specialize IHe2 with vals. 
    pose proof (c_seq_morph IHe1 IHe2). apply c_eq_soundness with (s:=s) in H2.
    rewrite H2. subst. rewrite seq_fold_app in H0. c_inversion.
    constructor; rewrite in_plus_fold;
    rewrite in_prod_iff in H1;destruct_ctx.
    ** exists (seq_fold (map vals l));split;auto.
       rewrite in_map_iff. exists l. split;auto.
    ** exists (seq_fold (map vals l0));split;auto.
       rewrite in_map_iff. exists l0. split;auto.
Qed.

Lemma c_eqP : forall (e0 e1 : Expr)(vals : nat -> Contract), expr_eqb e0 e1 = true -> (contract_of_Expr vals e0) =R= (contract_of_Expr vals e1).
Proof.
intros. repeat rewrite expr_monoms. apply c_eq_completeness. intros. repeat rewrite in_plus_fold. 
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
































 
