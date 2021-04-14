Fixpoint approx (A : Type) (n: nat) (f: A -> A) (arg: A) : A :=
match n with
| 0 => arg
| S n' => f (approx n' f arg)
end.


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

Fixpoint max_derivative_count (c : Contract) :=
match c with
| Failure => 1
| Success => 2
| Event _ => 3
| c0 _+_ c1 => (max_derivative_count c0)* (max_derivative_count c1)
| c0 _;_ c1 => (max_derivative_count c0) * Nat.pow 2 (max_derivative_count c1)
| Star c0 => (Nat.pow 2 (max_derivative_count c0)) - 1
end.

Notation "c0 =b= c1" := (forall s, nu (c0//s) = nu (c1//s)) (at level 73, no associativity).

Hint Unfold o : core.

Ltac auto_rwd := autorewrite with MatchDB using auto with MatchDB.

Ltac auto_rwd_in H := autorewrite with MatchDB in H.

Lemma o_Failure : o Failure = Failure.
Proof.
unfold o. now simpl.
Qed.

Lemma o_Success : o Success = Success.
Proof.
unfold o. now simpl.
Qed.

Lemma nu_derive_Failure : forall s, nu (Failure // s) = false.
Proof.
induction s;intros;auto.
Qed.

Hint Rewrite o_Failure o_Success nu_derive_Failure : MatchDB.

Lemma bool_match_Failure_seq : forall c, Failure _;_ c =b= Failure.
Proof.
intros. generalize dependent c. induction s; simpl;auto.
intros. auto_rwd. simpl. now auto_rwd. 
Qed.

Lemma bool_match_Succes_seq : forall c, Success _;_ c =b= c.
Proof.
intros. auto_rwd.
Qed.

Hint Rewrite bool_match_Failure_seq bool_match_Succes_seq : MatchDB.

Hint Immediate bool_match_Failure_seq bool_match_Succes_seq : MatchDB.

Lemma bool_eq_refl : forall c, c =b= c.
Proof.
now intros.
Qed.

Lemma bool_eq_sym : forall c0 c1, c0 =b= c1 -> c1 =b= c0.
Proof.
intros. symmetry. auto.
Qed.

Lemma bool_eq_trans : forall c0 c1 c2, c0 =b= c1 -> c1 =b= c2 -> c0 =b= c2.
Proof.
intros. specialize H with s. rewrite H. specialize H0 with s. now rewrite H0.
Qed.

Definition bool_eq := (fun c0 c1 => forall s, nu (c0//s) = nu (c1//s)).

Add Parametric Relation : Contract (fun c0 c1 => forall s, nu (c0//s) = nu (c1//s))
  reflexivity proved by bool_eq_refl
  symmetry proved by bool_eq_sym
  transitivity proved by bool_eq_trans
  as Contract_bool_eq_setoid.

Lemma bool_eq_iff : forall c0 c1, c0 =b= c1 <-> c0 ==~== c1.
Proof.
intros. split. intros. specialize H with s. split;intros.
rewrite Matches_Comp_iff_matchesb in *. rewrite H0 in H.
now symmetry. rewrite  Matches_Comp_iff_matchesb in *. rewrite <- H in H0.
auto. intros. specialize H with s. repeat rewrite Matches_Comp_iff_matchesb in H.
auto using eq_true_iff_eq.
Qed.

Lemma bool_eq_iff_ceq : forall c0 c1, c0 =b= c1 <-> c0 =R= c1.
Proof.
intros. rewrite bool_eq_iff. symmetry. apply c_eq_iff.
Qed.


Lemma bool_eq_plus_ctx : forall c0 c0' c1 c1', c0 =b= c1 -> c0' =b= c1' -> c0 _+_ c0' =b= c1 _+_ c1'.
Proof.
intros. auto_rwd. specialize H with s. specialize H0 with s. simpl. rewrite H.
rewrite H0. btauto. 
Qed.

Lemma bool_eq_seq_ctx : forall c0 c0' c1 c1', c0 =b= c1 -> c0' =b= c1' -> c0 _;_ c0' =b= c1 _;_ c1'.
Proof.
intros c0 c0' c1 c1' H0 H1. rewrite bool_eq_iff in*.
intros. split;intros.  inversion H. subst. constructor. 
now apply H0. now apply H1. inversion H. subst. constructor.
now apply H0. now apply H1.
Qed.

Add Parametric Morphism : CPlus with
signature bool_eq ==> bool_eq ==> bool_eq as bool_eq_plus_morphism.
Proof.
  intros. unfold bool_eq in*. apply bool_eq_plus_ctx;auto.
Qed.

Add Parametric Morphism : CSeq with
signature bool_eq ==> bool_eq ==> bool_eq as bool_eq_seq_morphism.
Proof.
  intros. unfold bool_eq in*. apply bool_eq_seq_ctx;auto.
Qed.

Ltac to_bool_eq :=
  repeat match goal with
         | [ |- ?c0 =R= ?c1 ] => rewrite bool_eq_iff_ceq
         | [ H : ?c0 =R= ?c1  |- _ ] => rewrite bool_eq_iff_ceq in H
         end.