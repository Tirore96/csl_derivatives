Require Import CSL.Core.Contract.  
Require Import Lists.List Bool.Bool Bool.Sumbool Setoid Coq.Arith.PeanoNat.

(** printing =~ %$=\sim$% *)

(** printing _+_ %$+$% *)

Import ListNotations.

Set Implicit Arguments.

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
  | c_plus_ctx c0 c0' c1 c1' (H1 : c0 =R= c0') (H2 : c1 =R= c1') : c0 _+_ c1 =R= c0' _+_ c1'
  | c_seq_ctx c0 c0' c1 c1' (H1 : c0 =R= c0') (H2 : c1 =R= c1') : c0 _;_ c1 =R= c0' _;_ c1'
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
         | [ H: _ =~ Failure |- _ ] => inversion H
         | [ H: ?s =~ _ _+_ _ |- _ ] => inversion H; clear H
         | [ H: ?s =~ _ _;_ _ |- _ ] => inversion H; clear H
         | [ H: [] =~ Success |- _ ] => fail
         | [ H: _ =~ Success |- _ ] => inversion H; clear H
         end);auto with cDB.



Lemma c_eq_soundness : forall (c0 c1 : Contract), c0 =R= c1 -> (forall s : Trace, s =~ c0 <-> s =~ c1).
Proof.
intros c0 c1 H. induction H ;intros; try solve [split;intros;c_inversion].
  * split;intros;c_inversion; [ rewrite <- app_assoc | rewrite app_assoc ]; auto with cDB.
  * rewrite <- (app_nil_l s). split;intros;c_inversion.
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

Ltac auto_rwd_eqDB := autorewrite with eqDB;auto with eqDB.


Fixpoint L (c : Contract) : list Trace :=
match c with
| Success => [[]]
| Failure => []
| Event e => [[e]]
| c0 _+_ c1 => (L c0) ++ (L c1)
| c0 _;_ c1 => map (fun p => (fst p)++(snd p)) (list_prod (L c0) (L c1))
end.

Fixpoint L_inv_trace (s : Trace) :=
match s with
| [] => Success
| e::s' => (Event e) _;_ (L_inv_trace s')
end.

Lemma L_inv_trace_app : forall (l1 l2 : Trace), L_inv_trace l1 _;_ L_inv_trace l2 =R= L_inv_trace (l1++l2).
Proof.
induction l1;intros;simpl; auto_rwd_eqDB.
rewrite <- IHl1. auto_rwd_eqDB.
Qed.



(*
Lemma L_inv_trace_embed : forall (s:Trace), s =~ L_inv_trace s.
Proof.
induction s;simpl;auto with cDB.
assert (HA: a::s = [a]++s);auto. rewrite HA; auto with cDB.
Qed.

Lemma L_inv_trace_eq : forall (s1 s0:Trace), s0 =~ L_inv_trace s1 -> s0 = s1.
Proof.
induction s1;intros; simpl in H.
- now inversion H.
- c_inversion. apply IHs1 in H4.
  inversion H3. subst. auto. 
Qed.

Lemma L_inv_trace_embed_iff : forall (s1 s0:Trace), s0 =~ L_inv_trace s1 <-> s0 = s1.
Proof. 
split;intros.
auto using L_inv_trace_eq. subst. apply L_inv_trace_embed.
Qed.*)

Lemma L_inv_trace_embed_iff : forall (s1 s0:Trace), s0 =~ L_inv_trace s1 <-> s0 = s1.
Proof. 
induction s1;intros;simpl.
- split;intros; c_inversion. subst. constructor.
- split;intros. c_inversion. inversion H3. 
  simpl. f_equal. now rewrite <- IHs1.
  subst. assert (HA: a::s1 = [a]++s1);auto. 
  specialize IHs1 with s1. rewrite HA. constructor.
  constructor. now rewrite IHs1.
Qed.

Fixpoint Σ (l : list Contract) : Contract :=
match l with
| [] => Failure
| c ::l => c _+_ (Σ l)
end.

(*Maybe not needed*)
Lemma Σ_app : forall (l1 l2 : list Contract), 
Σ (l1 ++ l2) =R= (Σ l1) _+_ (Σ l2).
Proof.
induction l1;intros;simpl;auto_rwd_eqDB.
rewrite IHl1. now rewrite c_plus_assoc.
Qed.


Lemma in_Σ : forall (l : list Contract)(s : Trace), s =~ Σ l <-> 
(exists c, In c l /\ s =~ c).
Proof. 
induction l;intros;simpl.
- split;intros. c_inversion. destruct_ctx. contradiction.
- split;intros. c_inversion. exists a. split;auto.
  rewrite IHl in H1. destruct_ctx. exists x. split;auto.
  destruct_ctx. inversion H. subst. auto with cDB.
  apply MPlusR. rewrite IHl. exists x. split;auto.
Qed.

Lemma in_Σ_idemp : forall l c, In c l -> c _+_ Σ l =R= Σ l.
Proof.
induction l;intros;simpl; auto_rwd_eqDB.
simpl in H;contradiction.
simpl in H. destruct H. subst. all: rewrite <- c_plus_assoc.
auto_rwd_eqDB. rewrite (c_plus_comm c). rewrite c_plus_assoc. 
apply c_plus_ctx;auto_rwd_eqDB.
Qed. 

Lemma incl_Σ_idemp : forall (l1 l2 : list Contract), incl l1 l2 -> Σ l2 =R= Σ (l1++l2).
Proof. 
induction l1;intros;simpl;auto_rwd_eqDB.
apply incl_cons_inv in H as [H0 H1].
rewrite <- IHl1;auto. now rewrite in_Σ_idemp;auto.
Qed.

Lemma Σ_app_comm : forall (l1 l2 : list Contract), Σ (l1++l2) =R= Σ (l2++l1).
Proof.
induction l1;intros;simpl. now rewrite app_nil_r.
repeat rewrite Σ_app. rewrite <- c_plus_assoc.
rewrite c_plus_comm. apply c_plus_ctx;auto_rwd_eqDB.
Qed.

Lemma incl_Σ_c_eq : forall (l1 l2 : list Contract), incl l1 l2 -> incl l2 l1-> Σ l1 =R= Σ l2.
Proof.
intros. rewrite (incl_Σ_idemp H). 
rewrite (incl_Σ_idemp H0). apply Σ_app_comm.
Qed.


Definition L_inv (l : list Trace) := Σ (map L_inv_trace l).
Hint Unfold L_inv : eqDB.

Lemma L_inv_trace_seq_L_inv : forall (ss : list Trace) (s : Trace), L_inv_trace s _;_ L_inv ss =R=
 Σ (map (fun x => L_inv_trace (fst x ++ snd x)) (map (fun y : list EventType => (s, y)) ss)).
Proof.
induction ss;intros;simpl;auto_rwd_eqDB.
unfold L_inv. simpl.
auto_rwd_eqDB. apply c_plus_ctx;auto using L_inv_trace_app.
Qed.

Lemma L_inv_seq_L_inv : forall l0 l1, L_inv l0 _;_ L_inv l1 =R=
 Σ (map (fun x => L_inv_trace (fst x ++ snd x)) (list_prod l0 l1)).
Proof.
induction l0;intros;simpl. unfold L_inv. simpl. auto_rwd_eqDB.
repeat rewrite map_app. rewrite Σ_app. rewrite <- IHl0.
unfold L_inv at 1. simpl. auto_rwd_eqDB. 
apply c_plus_ctx; auto using L_inv_trace_seq_L_inv with eqDB. 
Qed.

Theorem L_inv_L_ceq : forall (c : Contract), L_inv (L c) =R= c.
Proof.
induction c; unfold L_inv; simpl; try solve [auto_rwd_eqDB].
- rewrite map_app. rewrite Σ_app.
  auto using c_plus_ctx. 
- rewrite map_map.
  rewrite <- IHc1 at 2. rewrite <- IHc2 at 2.
  symmetry. apply L_inv_seq_L_inv.
Qed.


(*
Lemma L_inv_embed : forall (ss:list Trace)(s : Trace), In s ss <-> s =~ L_inv ss.
Proof.
intros. unfold L_inv. rewrite in_Σ. setoid_rewrite in_map_iff.
split;intros.
- exists (L_inv_trace s). split;auto using L_inv_trace_embed_iff.
exists s. split;auto. now rewrite L_inv_trace_embed_iff.
- destruct_ctx. subst. rewrite L_inv_trace_embed_iff in H0.
  now subst.
Qed.

Lemma L_inv_L_ceq : forall (c : Contract), L_inv (L c) =R= c.
Proof.
intros. unfold L_inv.
induction c; unfold L_inv; simpl; try solve [auto_rwd_eqDB].
- rewrite map_app. rewrite Σ_app.
  auto using c_plus_ctx. 
- rewrite map_map.
  rewrite <- IHc1 at 2. rewrite <- IHc2 at 2.
  symmetry. apply L_inv_seq_L_inv.
Qed.*)


(*
Lemma L_seq : forall (s0 s1: Trace)(c0 c1 : Contract), In s0 (L c0) -> In s1 (L c1) -> In (s0++s1) (L (c0 _;_ c1)).
Proof.
intros. simpl. rewrite in_map_iff. exists (s0,s1). split;auto.
rewrite in_prod_iff. split;auto. 
Qed. *)


(*
Lemma L_inv_trace_app : forall (s0 s1 : Trace) (s:Trace), s =~ L_inv_trace (s0 ++ s1) <-> s =~ (L_inv_trace s0) _;_ (L_inv_trace s1).
Proof.
induction s0;intros;simpl.
- now autorewrite with eqDB.
- split;intros. 
  * rewrite Matches_seq_assoc. c_inversion.
    constructor;auto. now rewrite <- IHs0.
  * rewrite Matches_seq_assoc in H. c_inversion.
    constructor;auto. rewrite IHs0;auto with cDB.
Qed.*)





(*Ltac unfold_defs := unfold L_inv.*)





Lemma comp_equiv_destruct : forall (c0 c1: Contract),(forall s : Trace, s =~ c0 <-> s =~ c1) <->
(forall s : Trace, s =~ c0 -> s =~ c1) /\ (forall s : Trace, s =~ c1 -> s =~ c0).
Proof.
 split ; intros.
- split;intros; specialize H with s; destruct H; auto.
- destruct H. split;intros;auto.
Qed.

Lemma Matches_member : forall (s : Trace)(c : Contract), s =~ c -> In s (L c). 
Proof.
intros. induction H ; simpl ; try solve [auto using in_or_app || auto using in_or_app ].
rewrite in_map_iff. exists (s1,s2). rewrite in_prod_iff. split;auto.
Qed.

Lemma member_Matches : forall (s : Trace)(c : Contract), In s (L c) -> s =~ c. 
Proof.
intros.
eapply c_eq_soundness. symmetry. eapply L_inv_L_ceq.
unfold L_inv. rewrite in_Σ.
exists (L_inv_trace s).
split;auto. rewrite in_map_iff. exists s;split;auto.
now rewrite L_inv_trace_embed_iff. (*only need one direction*)
Qed.

Theorem Matches_iff_member : forall s c, s =~ c <-> In s (L c).
Proof.
split; auto using Matches_member,member_Matches.
Qed.

Lemma Matches_incl : forall (c0 c1 : Contract), (forall (s : Trace), s =~ c0 -> s =~ c1) -> 
incl (L c0) (L c1).
Proof.
intros. unfold incl. intros. auto using Matches_member, member_Matches.
Qed.

Lemma incl_Matches : forall (c0 c1 : Contract), incl (L c0) (L c1) -> 
(forall (s : Trace), s =~ c0 -> s =~ c1).
Proof.
intros. unfold incl in H. rewrite Matches_iff_member in *. auto.
Qed.

Theorem Matches_iff_incl : forall (c0 c1 : Contract), (forall (s : Trace), s =~ c0 -> s =~ c1) <-> 
incl (L c0) (L c1).
Proof.
split;eauto using Matches_incl,incl_Matches.
Qed.

Corollary Matches_eq_iff_incl_and : forall (c0 c1 : Contract), (forall (s : Trace), s =~ c0 <-> s =~ c1) <-> 
incl (L c0) (L c1) /\ incl (L c1) (L c0) .
Proof.
split;intros.
- repeat rewrite <- Matches_iff_incl. now apply comp_equiv_destruct in H.
- generalize s. rewrite comp_equiv_destruct. now repeat setoid_rewrite Matches_iff_incl.
Qed.


Lemma c_eq_completeness : forall (c0 c1 : Contract), (forall s : Trace, s =~ c0 <-> s =~ c1) -> c0 =R= c1.
Proof.
intros. rewrite <- L_inv_L_ceq. rewrite <- (L_inv_L_ceq c1). 
unfold L_inv. rewrite Matches_eq_iff_incl_and in H.
destruct H. auto using incl_map, incl_Σ_c_eq.
Qed.

Print nat.

Check @eq_refl nat 0.

Lemma zero_i_zero : 0 = 0 -> 0 = 0.
Proof.
intros. exact H.
Qed.

Lemma use_imp : 0=0.
Proof.
apply zero_i_zero. apply eq_refl.
Qed.

Lemma plus_minus : forall (n0 n1 : nat), n0 + n1 = n1 + n0.
Proof.
induction n0.
- intros. simpl. induction n1.
  * reflexivity.
  * simpl. rewrite <- IHn1. reflexivity. 
- intros. simpl. rewrite IHn0.  rewrite plus_n_Sm. reflexivity. 
Qed.

Lemma plus_minus2 : forall (n0 n1 : nat), n0 + n1 = n1 + n0.
Proof.
induction n0;intros;simpl.
- induction n1; try reflexivity.
  simpl. rewrite <- IHn1. reflexivity. 
- rewrite IHn0. rewrite plus_n_Sm. reflexivity. 
Qed.

Lemma plus_minus2 : forall n0 n1, n0 + n1 = n1 + n0.
Proof.
induction n0;intros. simpl. auto.
Show Proof.
induction n1;simpl;auto. 
rewrite <- IHn1. auto. 
Qed.

intros;simpl;auto. simpl.

Definition eq0_def : 0 = 0 := eq_refl.

Lemma eq0_lemma : 0 = 0.
Proof.
apply eq_refl.
Qed.

Print eq0_lemma.

Lemma eq0_auto : 0 = 0.
Proof.
auto.
Qed.

Print eq0_auto.



: 0 = 0.


Check @eq_refl.
Theorem Matches_iff_c_eq : forall c0 c1, (forall s, s =~ c0 <-> s =~ c1) <-> c0 =R= c1.
Proof.
split; auto using c_eq_completeness, c_eq_soundness.
Qed.

Lemma L_Σ : forall l, L (Σ l) = flat_map L l.
Proof.
induction l;intros;simpl;auto. now rewrite IHl.
Qed.

Lemma Σ_c_eq_incl : forall (l1 l2 : list Contract), Σ l1 =R= Σ l2 -> incl l1 l2 /\ incl l2 l1.
Proof.
intros. rewrite <- Matches_iff_c_eq in H. rewrite Matches_eq_iff_incl_and in H.
repeat rewrite L_Σ in H.
destruct H. unfold incl in*.
- split;intros. setoid_rewrite in_flat_map in H. specialize H with a. 





























 
