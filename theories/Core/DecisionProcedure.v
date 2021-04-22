Require Import Bool.Bool List Coq.Arith.PeanoNat.
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
End inclb.

Check inclb.
Definition trace_inclb := inclb (list_eq_dec EventType_eq_dec).
Lemma c_eq_reflect : forall c0 c1, reflect (c0 =R= c1) (trace_inclb (monoms c0) (monoms c1) && trace_inclb (monoms c1) (monoms c0)).
Proof. 
intros. destruct ((trace_inclb (monoms c0) (monoms c1) && trace_inclb (monoms c1) (monoms c0))) eqn:Heqn;
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



Definition nat_inclb  := inclb (list_eq_dec Nat.eq_dec).

Definition expr_eqb (e0 e1 : Expr) := nat_inclb (vars_lists_of_Expr e0) (vars_lists_of_Expr e1) && nat_inclb (vars_lists_of_Expr e1) (vars_lists_of_Expr e0).

Definition expr_eq e0 e1 := incl (vars_lists_of_Expr e0) (vars_lists_of_Expr e1) /\ incl (vars_lists_of_Expr e1) (vars_lists_of_Expr e0).

Lemma expr_eq_reflect : forall (e0 e1 : Expr), reflect (expr_eq e0 e1) (expr_eqb e0 e1).
Proof.
intros. destruct (expr_eqb e0 e1) eqn:Heqn; unfold expr_eq;  unfold expr_eqb in Heqn;
unfold nat_inclb in *;
constructor;repeat rewrite <- inclb_iff; rewrite <- andb_true_iff;
[eauto | intro H; rewrite H in Heqn ; discriminate].
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




