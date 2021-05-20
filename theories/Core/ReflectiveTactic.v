Require Import CSL.Core.Contract CSL.Core.ContractEquations.  
Require Import Lists.List Bool.Bool Bool.Sumbool Setoid Coq.Arith.PeanoNat.

Import ListNotations.
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

Fixpoint monoms_of_Expr (e : Expr) : list (list nat) :=
match e with
| Var v => [[v]]
| ESuccess => [[]]
| EFailure => []
| EPlus e0 e1 => (monoms_of_Expr e0) ++ (monoms_of_Expr e1)
| ESeq e0 e1 => map (fun (a : list nat * list nat) => let (a1,a2):=a in a1++a2) (list_prod (monoms_of_Expr e0) (monoms_of_Expr e1))
end.

Fixpoint seq_fold (l : list Contract) :=
match l with
| [] => Success
| a::l' => a _;_ (seq_fold l')
end.

Lemma seq_fold_map : forall (s:Trace), s =~ seq_fold (map Event s).
Proof.
induction s.
- simpl. auto with cDB.
- simpl. assert (HA: a::s = [a]++s). { reflexivity. } rewrite HA. constructor; auto with cDB.
Qed.

Lemma seq_assoc_match : forall (c0 c1 c2 : Contract) s,
      s =~ c0 _;_ c1 _;_ c2 <-> s=~ c0 _;_ (c1 _;_ c2).
Proof.
intros c0 c1 c2. apply c_eq_soundness. auto with eqDB.
Qed.


Lemma seq_fold_app : forall (s:Trace)(s0 s1 : list Contract), s =~ seq_fold (s0 ++ s1) <-> s =~ (seq_fold s0) _;_ (seq_fold s1).
Proof.
intros. generalize dependent s. generalize dependent s1.
induction s0;intros.
- simpl. split. intro. rewrite <- (app_nil_l s). constructor;auto with cDB. intros. inversion H. inversion H3. subst. simpl. assumption.
- simpl. split.
  * intros. inversion H. subst. rewrite seq_assoc_match. constructor. assumption. apply IHs0. assumption.
  * intros. rewrite seq_assoc_match in H. inversion H. subst. constructor. assumption. apply IHs0. assumption.
Qed.



Definition list_contract_of_Expr_monoms (vals : nat -> Contract) (l : list (list nat)) := map (fun l0 => seq_fold (map vals l0)) l.





Check forallb.
Check Nat.eq_dec.
Locate nat_dec.

Definition inclb (l0 l1 : list (list nat)) :bool := forallb (fun a0 => existsb (fun a1 => if (list_eq_dec Nat.eq_dec) a0 a1 then true else false) l1) l0.

Lemma inclb_iff : forall (l0 l1 : list (list nat)), inclb l0 l1 = true <-> incl l0 l1.
Proof. unfold inclb. unfold incl. split. 
- intros. rewrite forallb_forall in H. apply H in H0. rewrite existsb_exists in H0. destruct H0 as [x [P0 P1]].
destruct (list_eq_dec Nat.eq_dec a x).
  * subst. assumption.
  * discriminate.
- intros. rewrite forallb_forall. intros. apply H in H0. rewrite existsb_exists. exists x. split.
  * assumption.
  * destruct (list_eq_dec Nat.eq_dec x x).
    ** reflexivity.
    ** contradiction. 
Qed.


Lemma incl_reflect : forall (l0 l1 : list (list nat)), reflect (incl l0 l1) (inclb l0 l1).
Proof. 
intros. destruct (inclb l0 l1) eqn:Heqn.
- constructor. rewrite inclb_iff in Heqn. assumption.
- constructor. intro H. rewrite <- inclb_iff in H. rewrite Heqn in H. discriminate.
Qed.

Definition expr_eqb (e0 e1 : Expr) := inclb (monoms_of_Expr e0) (monoms_of_Expr e1) && inclb (monoms_of_Expr e1) (monoms_of_Expr e0).

Definition expr_eq e0 e1 := incl (monoms_of_Expr e0) (monoms_of_Expr e1) /\ incl (monoms_of_Expr e1) (monoms_of_Expr e0).

Lemma expr_eq_reflect : forall (e0 e1 : Expr), reflect (expr_eq e0 e1) (expr_eqb e0 e1).
Proof.
intros. unfold expr_eq. unfold expr_eqb. destruct ((inclb (monoms_of_Expr e0) (monoms_of_Expr e1) &&
   inclb (monoms_of_Expr e1) (monoms_of_Expr e0))) eqn:Heqn. 
- apply andb_prop in Heqn as [H0 H1]. constructor. rewrite inclb_iff in H0.
  rewrite inclb_iff in H1. split ; auto.
- destruct (incl_reflect ((monoms_of_Expr e0)) (monoms_of_Expr e1)).
  * simpl in Heqn. constructor. intros [H3 H4]. rewrite <- inclb_iff in H4. rewrite Heqn in H4. discriminate.
  * constructor. intros [H0 H1]. contradiction.
Qed.
Check Σ_app.
Import ListNotations.
Lemma Σ_app_match : forall l1 l2 s, s=~ Σ (l1 ++ l2) <-> s=~ Σ l1 _+_ Σ l2.
Proof.
intros l0 l1. apply c_eq_soundness. apply Σ_app.
Qed.

Lemma expr_monoms : forall (e : Expr)(vals : nat -> Contract), contract_of_Expr vals e =R= Σ (map (fun l => seq_fold (map vals l)) (monoms_of_Expr e)).
Proof.
induction e;intros.
- simpl. auto. rewrite c_plus_neut. auto with eqDB.
- simpl. auto with eqDB.
- simpl. auto with eqDB.
- simpl. apply c_eq_completeness. intros. rewrite map_app. rewrite Σ_app_match.
  apply c_eq_soundness. auto with eqDB.
- simpl. rewrite map_map. apply c_eq_completeness. intros. rewrite in_Σ. split.
  * intros. inversion H. subst. specialize IHe1 with vals.
    specialize IHe2 with vals. eapply c_eq_soundness in IHe1.
    rewrite in_Σ in IHe1. eapply IHe1 in H3. 
    eapply c_eq_soundness in IHe2. rewrite in_Σ in IHe2. 
    eapply IHe2 in H4. destruct H3 as [c3 [P31 P32]].
    destruct H4 as [c4 [P41 P42]]. rewrite in_map_iff in P31. 
    rewrite in_map_iff in P41. destruct P31 as [l1 [P31 P31']].
    destruct P41 as [l2 [P41 P41']]. exists (seq_fold (map vals (l1++l2))).
    split.
    ** rewrite in_map_iff. exists (l1,l2). split.
      *** reflexivity.
      *** rewrite in_prod_iff. split ; auto.
    ** rewrite map_app. rewrite seq_fold_app. subst. constructor; auto.
  * intros. destruct H as [c [P1 P2]]. rewrite in_map_iff in P1.
    destruct P1 as [p [P1 P1']]. destruct p. rewrite map_app in P1.
    specialize IHe1 with vals. specialize IHe2 with vals. 
    pose proof (c_seq_ctx IHe1 IHe2). apply c_eq_soundness with (s:=s) in H.
    rewrite H. subst. rewrite seq_fold_app in P2. inversion P2.
    constructor. apply in_Σ. exists (seq_fold (map vals l)).
    apply in_prod_iff in P1' as [P1' P2']. split.
    ** rewrite in_map_iff. exists l. split. reflexivity. assumption.
    ** assumption.
    **     apply in_prod_iff in P1' as [P1' P2']. apply in_Σ. exists (seq_fold (map vals l0)). split. 
      *** rewrite in_map_iff. exists l0.  split. reflexivity. assumption.
      *** assumption.
Qed.

Lemma c_eqP : forall (e0 e1 : Expr)(vals : nat -> Contract), expr_eqb e0 e1 = true -> (contract_of_Expr vals e0) =R= (contract_of_Expr vals e1).
Proof.
intros. repeat rewrite expr_monoms. apply c_eq_completeness. intros. repeat rewrite in_Σ. 
destruct (expr_eq_reflect e0 e1).
- unfold expr_eq in e. destruct e. split;intros.
  * destruct H2 as [x [P1 P2]]. apply in_map_iff in P1 as [l [Pl1 Pl2]].
    unfold incl in H0. exists x. split. rewrite in_map_iff. exists l. split ; auto. assumption.
  * destruct H2 as [x [P1 P2]]. apply in_map_iff in P1 as [l [Pl1 Pl2]].
    unfold incl in H0. exists x. split. rewrite in_map_iff. exists l. split ; auto. assumption.
- discriminate.
Qed.


Definition ex_con := Transfer _._ Notify _._ Success _+_ Notify _._ Success.

Definition my_vals n :=
if Nat.eq_dec 0 n then (Event Transfer) else if Nat.eq_dec 1 n then (Event Notify) else Failure.

Definition expr1 := (EPlus (ESeq (Var 0) (ESeq (Var 1) ESuccess)) (ESeq (Var 1) ESuccess)).

Definition expr2 := (EPlus (ESeq (Var 1) ESuccess) (ESeq (Var 0) (ESeq (Var 1) ESuccess))).

Eval compute in (contract_of_Expr my_vals expr1).
Eval compute in (contract_of_Expr my_vals expr2).

Lemma test : (Transfer _._ Notify _._ Success _+_ Notify _._ Success) =R= 
             (Notify _._ Success _+_ Transfer _._ Notify _._ Success ).
Proof.
exact (@c_eqP expr1 expr2 my_vals eq_refl).
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

Check nth 0.



Fixpoint fun_of_list_aux (l : list  (nat * Contract)) :=
match l with
| [] => (fun  _ => Failure)
| (n,c)::l' => let f2 := fun_of_list_aux l'
               in (fun t => if Nat.eq_dec n t then c else f2 t)
end.

Definition fun_of_list l := fun_of_list_aux (combine (seq 0 (length l)) l).

Definition fun_test := fun_of_list [Failure;Success].

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



