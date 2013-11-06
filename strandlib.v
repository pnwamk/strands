Require Import Logic List ListSet Arith Peano_dec Omega Ensembles.
Require Import Coq.Sets.Constructive_sets.
Require Import Finite_sets_facts Finite_sets Relation_Definitions.
Require Import Relation_Operators.
Require Import strictorder set_rep_equiv util.
Require Import finite_set_builder.
Require Import LibTactics.

Require Import strandspace.

Open Scope list_scope.
Import ListNotations.
Open Scope ss_scope.

Hint Resolve Coq.Sets.Constructive_sets.Add_not_Empty Noone_in_empty.
Hint Unfold Origin.

Lemma origin_tx : forall n t,
Origin t n ->
is_tx n.
Proof. unfold Origin. iauto. Qed.
Hint Resolve origin_tx.
Lemma origin_st : forall n t,
Origin t n -> t <st msg n. 
Proof. unfold Origin. iauto. Qed.
Hint Resolve origin_st.
Lemma origin_nopred_st : forall n t,
Origin t n ->
forall n', n' << n -> ~ t <st msg n'.
Proof. unfold Origin. iauto. Qed.
Hint Resolve origin_nopred_st.

Lemma particular_min_smsg:
  forall {min actual_content},
    ((strand min) = [actual_content]) ->
    smsg min = actual_content.
Proof.
  intros min actual_content seq.
  assert (length (strand min) = 1) as len. rewrite seq. auto.
  assert ((index min) = 0) as imin. 
  remember (index_len_node min). omega. 
  assert (nth_error (strand min) (index min) = Some (smsg min)) as ntheq. 
  apply node_indexing_equiv.
  rewrite seq in ntheq. rewrite imin in ntheq. simpl in ntheq.
  inversion ntheq as [msmsg].
  auto.
Qed.
Lemma particular_min_msg:
  forall {min actual_content},
    ((strand min) = [actual_content]) ->
    msg min = smsg_msg actual_content.
Proof.
  intros min actual_content seq.
  unfold msg.
  erewrite particular_min_smsg.
  tauto. auto.
Qed.
Lemma key_st_text_false : forall k t,
(#k) <st (!t) -> False.
Proof. intros. inversion H. Qed.
Hint Resolve key_st_text_false.

Lemma tx_rx_false : forall n,
is_tx n -> is_rx n -> False.
Proof. intros. inversion H. inversion H0. rewrite H2 in *. inversion H1. Qed.
Hint Resolve tx_rx_false.
Hint Unfold is_tx is_rx.

Lemma node_strand_3height_opts : forall (n:Node) (sm1 sm2 sm3:SMsg),
(strand n) = [sm1; sm2; sm3] ->
(smsg n) = sm1 \/ (smsg n) = sm2 \/ (smsg n) = sm3.
Proof. 
  intros.
  assert ((index n) = 0 \/ (index n) = 1 \/ (index n) = 2 \/ (index n) > 2). omega. 
  destruct H0; forwards*: (node_indexing_equiv n).
  rewrite H0 in *. rewrite H in *. simpl in *; inversion H1.
  left. auto. destruct H0.
  rewrite H0 in *. rewrite H in *. simpl in *; inversion H1.
  right. left. auto. destruct H0.
  rewrite H0 in *. rewrite H in *. simpl in *; inversion H1.
  right. right. auto.
  destruct n. simpl in *. assert (length (fst x) = 3). rewrite H. 
  simpl. reflexivity. omega.
Qed.
Hint Resolve node_strand_3height_opts.

Lemma nth_error_some_In {X:Type}: forall l i (x:X),
nth_error l i = Some x ->
List.In x l.
Proof.
  intros l. induction l.
  intros i x nth. destruct i. simpl in nth; inversion nth.
  simpl in nth; inversion nth.
  intros i x nth.
  destruct i. simpl in nth. inversion nth. left. reflexivity.
  simpl in nth. right. eapply IHl. exact nth.
Qed.
Hint Resolve nth_error_some_In.

Lemma node_smsg_in_strand : forall n s,
(strand n) = s ->
List.In (smsg n) s.
Proof.
  intros.
  forwards*: (node_indexing_equiv n).
  eapply nth_error_some_In. subst. exact H0.
Qed.  
Hint Resolve node_smsg_in_strand.

Lemma node_hd_or_rest : forall n h rest,
(strand n) = h :: rest ->
(smsg n) = h \/ List.In (smsg n) rest.  
Proof.
  intros n h rest seq. 
  forwards*: (node_smsg_in_strand n (h :: rest)).
Qed.
Hint Resolve node_hd_or_rest.

Lemma hd_pred_all : forall n n',
(strand n) = (strand n') ->
(index n) = 0 ->
(index n') > 0 ->
n << n'.
Proof.
  intros n n' streq ni n'i.
  apply spath_imp_sspath.
  apply spath_from_props. omega. assumption.
Qed.
Hint Resolve hd_pred_all.

Lemma no_origin_after_rx : forall n g rest,
(strand n) = (-g) :: rest ->
~Origin g n.
Proof.
  intros n g rest streq orig.
  forwards*: node_hd_or_rest.
  destruct orig as [Htx [Hst Hnopred]].
  destruct H. forwards*: tx_rx_false.
  assert (exists n0, (index n0) = 0 /\ (strand n0) = (strand n)).
  eexists (exist _ ((strand n), 0) _). simpl. auto.
  destruct H0 as [n0 [n0s n0i]].
  assert (n0 << n). apply hd_pred_all; auto.
  (* BOOKMARK *)
  forwards*: hd_pred_all.
  Admitted.



Lemma origin_imp_st_strand : forall t x s,
Origin t x ->
strand x = s ->
st_on_strand t s = true.
Proof.
  Admitted.
Hint Resolve origin_imp_st_strand.

Lemma equiv_disjunct : forall p,
p \/ p -> p.
Proof. intros. iauto. Qed.

Lemma strand_prev_imp_pred : forall f n x xs,
strand n = f ++ x :: xs ->
smsg n <> x ->
exists n', n' << n /\ smsg n' = x.
Proof.
  Admitted.
Hint Resolve strand_prev_imp_pred.

Lemma no_st_l_r : forall l r t,
~ t <st l ->
~ t <st r ->
t <> (l * r) ->
~ t <st (l * r).
Proof.
  intros l r t notl notr neq contra.
  inversion contra; subst; auto.
Qed.
Hint Resolve no_st_l_r.

Lemma key_st_key : forall (k k' : Key),
(#k) <st (#k') -> k = k'.
Proof. 
  intros. inversion H; auto.
Qed.  
Hint Resolve key_st_key.

Lemma no_encr_st : forall a b k,
~ a <st b ->
a <> {b}^[k] ->
~ a <st {b}^[k].
Proof.
  intros a b k nost neq contra. 
  inversion contra; eauto. 
Qed.
Hint Resolve no_encr_st.
