Require Import Logic List ListSet Arith Peano_dec Omega Ensembles.

Require Import Relation_Definitions Relation_Operators Operators_Properties.
Require Import strictorder set_rep_equiv util.
Require Import CoLoRRelDec CoLoRRelSub.
Require Import ProofIrrelevance.
Require Import LibTactics.

Require Import strandspace.

Open Scope list_scope.
Import ListNotations.
Open Scope ss_scope.


Hint Resolve eq_term_dec eq_sterm_dec eq_strand_dec.

Lemma st_dec : forall a b,
{a <st b} + {~ a <st b}.
Proof.
  intros a b.
  induction b.
  Case "b = txt".
    destruct a.
    SCase "a = txt".
      destruct (eq_text_dec t t0).
        subst t. left. auto.
        right. intros contra. inversion contra. 
        symmetry in H1. contradiction.
    SCase "a = key". right. intros contra. inversion contra.
    SCase "a = join". right. intros contra. inversion contra.
    SCase "a = encr". right. intros contra. inversion contra.
  Case "b = key".
    destruct a.
    SCase "a = txt". right. intros contra. inversion contra.
    SCase "a = key".
      destruct (eq_key_dec k k0).
        subst k. left. auto.
        right. intros contra. inversion contra. 
        symmetry in H1. contradiction.
    SCase "a = join". right. intros contra. inversion contra.
    SCase "a = encr". right. intros contra. inversion contra.
  Case "b = join".
    destruct IHb1.
    SCase "a <st b1". left. apply st_join_l. exact s.
    SCase "~a <st b1". 
      destruct IHb2.
      SSCase "a <st b2". left. apply st_join_r. exact s.
      SSCase "~a <st b2". 
        destruct (eq_term_dec a (b1 * b2)).
        SSSCase "a = b1 * b2".
          subst a. left. constructor.
        SSSCase "a <> b1 * b2".
          right. intros contra. inversion contra; subst; try(contradiction).
          apply n1. reflexivity.
  Case "b = encr".
    destruct IHb.
      left. apply st_encr. exact s.
      destruct (eq_term_dec a ({b}^[k])). subst.
      left. constructor.
      right. intros contra. inversion contra. subst.
      apply n0. reflexivity.
      contradiction.
Qed.
Hint Resolve st_dec.

Lemma filter_subset {X:Type} : 
(forall x y : X, {x=y} + {x<>y}) ->
forall f (l: list X),
subset (filter f l) l.
Proof.
  intros.
  unfold subset.
  intros x xInfil.
  induction l.
  simpl in *. tryfalse.
  destruct (X0 a x). subst.
  left. reflexivity.
  right. apply IHl.
  simpl in xInfil.
  destruct (f a). simpl in xInfil.
  destruct xInfil. tryfalse.
  auto. auto.
Qed.

Lemma index_lt_1_imp_0 : forall n,
index n < 1 -> index n = 0.
Proof.
  intros n lt. omega.
Qed.

Lemma node_sterm_term_tx : forall n t,
sterm(n) = (+ t) ->
term(n) = t.
Proof.
  intros n t nsterm.
  unfold term. rewrite nsterm. reflexivity. 
Qed.
Hint Resolve node_sterm_term_tx.

Lemma node_sterm_term_rx : forall n t,
sterm(n) = (- t) ->
term(n) = t.
Proof.
  intros n t nsterm.
  unfold term. rewrite nsterm. reflexivity. 
Qed.
Hint Resolve node_sterm_term_rx.

Lemma tx_imp_sterm_eq : forall n,
is_tx n ->
sterm n = (+ term n).
Proof.
  intros n tx.
  destruct tx.
  forwards*: node_sterm_term_tx.
  congruence.
Qed.
Hint Resolve tx_imp_sterm_eq.

Lemma rx_imp_sterm_eq : forall n,
is_rx n ->
sterm n = (- term n).
Proof.
  intros n tx.
  destruct tx.
  forwards*: node_sterm_term_rx.
  congruence.
Qed.
Hint Resolve rx_imp_sterm_eq.

Lemma eq_nodes : forall x y : Node,
index(x) = index(y) ->
strand(x) = strand(y) ->
x = y.
Proof.
  intros [[xs xn] xp] [[ys yn] yp] eq_index eq_strand.
  simpl in eq_index. simpl in eq_strand. subst.
  rewrite (proof_irrelevance (lt yn (length ys)) xp yp). reflexivity.
Qed.
Hint Resolve eq_nodes.

Lemma nodes_eq : forall x y : Node,
x = y ->
index(x) = index(y) /\
strand(x) = strand(y).
Proof.
  intros x y xyeq.
  subst. auto.
Qed.
Hint Resolve nodes_eq.

Lemma node_imp_strand_nonempty : forall s n,
strand(n) = s ->
length s > 0.
Proof.
  intros s n Hns.
  destruct n. destruct x.
  destruct n. simpl in l.
  destruct s.
  Case "s = []".
    assert (s0 = nil). auto.
  subst. inversion l.
  Case "s = s :: s1".
    simpl. omega.
    simpl in l. 
    assert (s0 = s). auto.
    rewrite <- H.
    omega.
Qed.
Hint Resolve node_imp_strand_nonempty.

Lemma index_len_node : forall n,
(index n) < length (strand n).
Proof.
  intros n.
  destruct n. simpl. omega.
Qed.
Hint Resolve index_len_node.

Lemma nth_error_val {X:Type}: forall (l: list X) i,
i < length l ->
exists v, nth_error l i = Some v.
Proof.
  intros l.
  induction l.
  intros i lt. simpl in lt. omega.
  intros i lt.
  destruct i.
  exists a. simpl. auto.
  destruct (IHl i). simpl in lt. omega.
  exists x.
  simpl. auto.
Qed.

 Lemma nth_error_node : forall n,
nth_error (strand n) (index n) = Some (sterm n).
Proof.
  intros n.
  unfold sterm. destruct node_sterm_valid. 
  destruct n. simpl in *.
  destruct x0.
  rewrite e. simpl. reflexivity.
Qed.

Lemma nth_node : forall n s i d,
strand n = s ->
index n = i ->
nth i s d = sterm n.
Proof.
  intros n s i d seq idx.
  erewrite <- nth_default_eq.
  unfold nth_default. 
  destruct (nth_error_val s i). 
  rewrite <- seq. rewrite <- idx. apply index_len_node.
  rewrite H. rewrite <- seq in H.
  rewrite <- idx in H. rewrite nth_error_node in H.
  inversion H; auto.
Qed.
Hint Resolve nth_node.

Lemma strand_node : forall (s: Strand) (i: nat),
i < length s ->
exists n, strand n = s /\ index n = i.
Proof.
  intros s i len.  
  eexists (exist _ (s,i) _). simpl.
  split; reflexivity.
Grab Existential Variables.
  simpl. exact len.
Qed.
Hint Resolve strand_node.

Hint Constructors Comm Comm'.

Lemma comm'_in_l : forall N x y,
x -[N]-> y ->
set_In x N.
Proof.
  intros n x y edge.
  inversion edge; subst; auto.
Qed.
Hint Resolve comm'_in_l.

Lemma comm'_in_r : forall N x y,
x -[N]-> y ->
set_In y N.
Proof.
  intros n x y edge.
  inversion edge; subst; auto.
Qed.
Hint Resolve comm'_in_r.

Lemma comm'_imp_comm : forall N x y,
x -[N]-> y ->
x --> y.
Proof.
  intros n x y edge.
  inversion edge; subst; auto.
Qed.
Hint Resolve comm'_imp_comm.

Lemma comm_term_eq : forall x y,
x --> y -> term x = term y.
Proof.
  intros x y edge.
  destruct edge. destruct H.
  destruct H. eauto.
  forwards*: node_sterm_term_tx.
  forwards*: node_sterm_term_rx.
  congruence.
Qed.  
Hint Resolve comm_term_eq.

Lemma tx_rx_false : forall n,
is_tx n -> is_rx n -> False.
Proof. intros. inversion H. inversion H0. rewrite H2 in *. inversion H1. Qed.
Hint Resolve tx_rx_false.
Hint Unfold is_tx is_rx.

Lemma comm_dec : forall x y,
{x --> y} + {~ x --> y}.
Proof.
  intros x y.
  remember (sterm x) as xsterm. remember (sterm y) as ysterm.
  remember (strand x) as xstrand. remember (strand y) as ystrand.
  destruct xsterm.
  Case "x (tx m)".
    destruct ysterm.
    SCase "y (tx m0)".
      right. intros contracomm. inversion contracomm; subst.
      destruct H as [[xtx yrx] strandneq].
      rewrite <- Heqysterm in yrx. inversion yrx.      
    SCase "y (rx m0)".
      destruct (eq_term_dec t t0) as [termeq | termneq].
      SSCase "m = m0".
        destruct (eq_strand_dec xstrand ystrand) as [strandeq | strandneq].
        SSSCase "strands eq".
          right. intros contracomm.
          inversion contracomm; subst. destruct H as [terms strandsneq].
          apply strandsneq. exact strandeq. 
        SSSCase "strands neq".
          subst t0. left.
          apply (comm x y t). split. split.
          auto. auto. subst. exact strandneq.        
      SSCase "m <> m0".
        right. intros contracomm. inversion contracomm; subst. 
        destruct H as [[xtx yrx] strandneq].
        apply termneq. rewrite <- Heqxsterm in xtx.
        rewrite <- Heqysterm in yrx. inversion xtx; subst. 
        inversion yrx; subst. reflexivity.
  Case "x (rx m)".
    right.
    intros contracomm. inversion contracomm; subst.
    destruct H as [[xtx yrx] strandneq].
    rewrite <- Heqxsterm in xtx. inversion xtx.
Qed.
Hint Resolve comm_dec.

Lemma comm'_dec : forall N x y,
{x -[N]-> y} + {~ x -[N]-> y}.
Proof.
  intros N x y.
  destruct (comm_dec x y);
  destruct (set_In_dec eq_node_dec x N);
  destruct (set_In_dec eq_node_dec y N); eauto.
Qed.
Hint Resolve comm'_dec.

Theorem comm_irreflexivity : forall n,
~ n --> n.
Proof.
  intros n contraedge.
  inversion contraedge; subst.
  destruct H as [[txsterm rxsterm] strandneq].
  apply strandneq. reflexivity.
Qed.
Hint Resolve comm_irreflexivity.

Theorem comm_antisymmetry : 
antisymmetric Comm.
Proof.
  intros n m Hcomm contra.
  assert False.
  inversion Hcomm; subst.
  inversion contra; subst.
  destruct H as [H Hneq_s].
  destruct H as [Htx1 Hrx1].
  destruct H0 as [H Hneq_s2].
  destruct H as [Htx2 Hrx2].
  rewrite Htx2 in Hrx1. inversion Hrx1.
  inversion H.
Qed.
Hint Resolve comm_antisymmetry.

Hint Constructors Successor Successor'.

Lemma succ'_in_l : forall N x y,
x =[N]=> y ->
set_In x N.
Proof.
  intros n x y edge.
  inversion edge; subst; auto.
Qed.
Hint Resolve succ'_in_l.

Lemma succ'_in_r : forall N x y,
x =[N]=> y ->
set_In y N.
Proof.
  intros n x y edge.
  inversion edge; subst; auto.
Qed.
Hint Resolve succ'_in_r.

Lemma succ'_imp_succ : forall N x y,
x =[N]=> y ->
x ==> y.
Proof.
  intros n x y edge.
  inversion edge; subst; auto.
Qed.
Hint Resolve succ'_imp_succ.

Lemma succ_dec : forall x y,
{x ==> y} + {~ x ==> y}.
Proof.
  intros x y.
  remember (index x) as xi. remember (index y) as yi.
  remember (strand x) as xstrand. remember (strand y) as ystrand.
  destruct (eq_strand_dec xstrand ystrand) as [seq | sneq].
  Case "strands eq".
    destruct (eq_nat_dec yi (S xi)) as [succi | wrongi].
    SCase "yi = S xi". left. apply (succ x y). rewrite <- Heqxstrand.
      rewrite <- Heqystrand.  exact seq. omega.
    SCase "yi <> S xi".
      right. intros contrasucc. apply wrongi. 
      inversion contrasucc; subst; omega.
  Case "strands neq".
    right. intros contrasucc. apply sneq. 
    inversion contrasucc; subst; auto.
Qed.  
Hint Resolve succ_dec.

Lemma succ'_dec : forall N x y,
{x =[N]=> y} + {~ x =[N]=> y}.
Proof.
  intros N x y.
  destruct (succ_dec x y);
  destruct (set_In_dec eq_node_dec x N);
  destruct (set_In_dec eq_node_dec y N); eauto.
Qed.
Hint Resolve succ'_dec.

Theorem succ_irreflexivity : forall n,
~n ==> n.
Proof.
  intros n edge.
  inversion edge; subst. omega.
Qed.
Hint Resolve succ_irreflexivity.

Theorem succ_antisymmetry :
antisymmetric Successor.
Proof.
  intros n m Hpe1 Hpe2.
  destruct Hpe1. destruct Hpe2.
  rewrite <- H0 in H2. omega.
Qed.
Hint Resolve succ_antisymmetry.

Lemma single_succ : forall x y z,
x ==> y ->
x ==> z ->
y = z.
Proof.
  intros x y z xy xz.
  destruct xy.
  destruct xz.
  apply eq_nodes; auto; try omega; try congruence.
Qed.
Hint Resolve single_succ.

Lemma spath'_in_l : forall N x y,
x =[N]=>+ y ->
set_In x N.
Proof.
  intros n x y edge.
  induction edge; subst; eauto. 
Qed.
Hint Resolve spath'_in_l.

Lemma spath'_in_r : forall N x y,
x =[N]=>+ y ->
set_In y N.
Proof.
  intros n x y edge.
  induction edge; subst; eauto.
Qed.
Hint Resolve spath'_in_r.

Lemma spath'_imp_spath : forall N x y,
x =[N]=>+ y ->
x ==>+ y.
Proof.
  intros N x y edge.
  induction edge.
  constructor. eauto.
  eapply (t_trans Node Successor x y z IHedge1 IHedge2).
Qed.
Hint Resolve spath'_imp_spath.

Lemma spath_imp_eq_strand : forall x y,
x ==>+ y -> strand(x) = strand(y).
Proof.
  intros x y path.
  induction path.
  Case "step".
    destruct H; auto.
  Case "trans".
    rewrite IHpath1.
    rewrite IHpath2.
    reflexivity.
Qed.
Hint Resolve spath_imp_eq_strand.

Lemma spath_imp_index_lt : forall x y,
x ==>+ y -> index(x) < index(y).
Proof.
  intros x y path.
  induction path.
  Case "step". inversion H; subst. omega.
  Case "trans". omega.
Qed.
Hint Resolve spath_imp_index_lt.

Lemma spath_step_holds : forall x x' y,
x ==>+ y ->
x ==> x' ->
x' = y \/ x' ==>+ y.
Proof.
  intros x x' y path. generalize dependent x'.
  apply clos_trans_t1n in path.
  induction path.
    intros. left. eapply single_succ; eauto.
    intros.
    forwards*: (single_succ x y x'). subst.
    right. apply clos_t1n_trans in path. auto.
Qed.
Hint Resolve spath_step_holds.

Lemma spath_from_props : forall x y,
index(x) < index(y) ->
(strand x) = (strand y) ->
x ==>+ y.
Proof.
  intros x.
  destruct x as [[xs xi] xp]. simpl in *. 
  induction xi.
    intros y ind streq.
    destruct y as [[ys yi] yp]. simpl in *. 
    induction yi. omega. 
      destruct yi.
        constructor. constructor. auto. simpl. reflexivity.
        assert (snd (ys, S yi) < length (fst (ys, S yi))) as yp'. simpl. omega.
        apply (t_trans Node Successor
                 (exist (fun n : Strand * nat => snd n < length (fst n)) (xs, 0) xp)
                 (exist (fun n : Strand * nat => snd n < length (fst n)) (ys, S yi) yp')
                 (exist (fun n : Strand * nat => snd n < length (fst n)) (ys, S (S yi)) yp)).
        apply IHyi. omega.
        constructor. constructor. auto. simpl. omega.
    intros y ind streq.
    assert (snd (xs, xi) < length (fst (xs, xi))) as xp'. simpl. omega.
    assert (exist (fun n : Strand * nat => snd n < length (fst n)) (xs, xi) xp') ==>
         (exist (fun n : Strand * nat => snd n < length (fst n)) (xs, S xi) xp).
      constructor. constructor. auto. simpl. omega.
    assert (xi < index y). omega.
    remember (IHxi xp' y H0 streq).
    destruct (spath_step_holds 
              (exist (fun n : Strand * nat => snd n < length (fst n)) (xs, xi) xp')
              (exist (fun n : Strand * nat => snd n < length (fst n)) (xs, S xi) xp)
              y
              s
              H).
    apply nodes_eq in H1. destruct H1. simpl in *.
    constructor. constructor; auto. omega.
    assumption.
Qed.
Hint Resolve spath_from_props.

Lemma spath_irreflexivity : forall n,
~ n ==>+ n.
Proof.
  intros n contra.
  apply spath_imp_index_lt in contra.
  omega.
Qed.
Hint Resolve spath_irreflexivity.

Theorem spath_transitivity :
transitive StrandPath.
Proof.
  intros i j k Hij Hjk.
  apply (t_trans Node Successor i j k Hij Hjk).
Qed.

Hint Unfold union.

Lemma ssedge'_in_l : forall N x y,
x =[N]-> y ->
set_In x N.
Proof.
  intros n x y edge.
  induction edge; subst; eauto. 
Qed.
Hint Resolve ssedge'_in_l.

Lemma ssedge'_in_r : forall N x y,
x =[N]-> y ->
set_In y N.
Proof.
  intros n x y edge.
  induction edge; subst; eauto.
Qed.
Hint Resolve ssedge'_in_r.

Lemma ssedge'_imp_ssedge : forall N x y,
x =[N]-> y ->
x =-> y.
Proof.
  intros N x y edge.
  induction edge.
  constructor. eauto.
  constructor 2. eauto.
Qed.
Hint Resolve ssedge'_imp_ssedge.

Lemma ssedge_builds_ssedge' : forall s x y,
set_In x s ->
set_In y s ->
x =-> y ->
x =[s]-> y.
Proof.
  intros s x y xIn yIn edge.
  destruct edge.
  constructor. auto.
  constructor 2. auto.
Qed.

Lemma ssedge_dec : forall x y,
{x =-> y} + {~x =-> y}.
Proof.
  intros x y.
  destruct (comm_dec x y) as [cxy | nocxy].
  Case "Comm x y".
    left. left. exact cxy.
  Case "~Comm x y".
    destruct (succ_dec x y) as [pxy | nopxy].
    SCase "Successor x y".
      left. right. exact pxy.
    SCase "~Successor x y".
      right. intros contrass.
       destruct contrass.
       SSCase "false Comm".
         apply nocxy; exact H.
       SSCase "false Successor".
         apply nopxy; exact H.
Qed.
Hint Resolve ssedge_dec.

Lemma ssedge'_dec : forall N x y,
{x =[N]-> y} + {~x =[N]-> y}.
Proof.
  intros N x y.
  destruct (ssedge_dec x y).
  destruct (set_In_dec eq_node_dec x N);
  destruct (set_In_dec eq_node_dec y N). 
  forwards: (ssedge_builds_ssedge' N x y). auto. auto.
  auto. auto. right. intros contra. eauto.
  right. intros contra. eauto. right. intros contra. eauto.
  right. intros contra. eauto.
Qed.
Hint Resolve ssedge'_dec.

Theorem ssedge_irreflexivity : forall n,
~ n =-> n.
Proof.
  intros n Hedge.
  inversion Hedge; subst; auto.
  eapply (comm_irreflexivity); eauto.
  eapply (succ_irreflexivity); eauto.
Qed.
Hint Resolve ssedge_irreflexivity.

Theorem ssedge_antisymmetry :
antisymmetric SSEdge.
Proof.
  intros n m Hss Hcontra.
  inversion Hss; subst. inversion Hcontra; subst.
  apply (comm_antisymmetry n m H) in H0. exact H0.
  assert False.
  inversion H; subst. inversion H0; subst.
  inversion H1. apply H5. symmetry. exact H2.
  inversion H1.
  assert False.
  inversion Hcontra; subst. inversion H; subst.
  inversion H0; subst. inversion H3. apply H5.
  symmetry. exact H1.
  inversion H; subst. inversion H0; subst.
  omega. inversion H0.
Qed.
Hint Resolve ssedge_antisymmetry.

Theorem spath_imp_sspath : forall i j,
i ==>+ j -> i << j.
Proof.
  unfold SSPath.
  intros i j Hpath.
  induction Hpath.
  constructor. right. exact H.
  apply (t_trans Node SSEdge x y z IHHpath1 IHHpath2).
Qed.  
Hint Resolve spath_imp_sspath.

Lemma spath_incl_pred : forall B i j,
set_In j (Nodes B) ->
i ==>+ j ->
set_In i (Nodes B).
Proof.
  intros B i j jIn path.
  induction path. destruct B. eauto.
  apply IHpath1. apply IHpath2. auto.
Qed.

Lemma ssedge_imp_sspath : forall x y,
x =-> y ->
x << y.
Proof.
  intros x y edge.
  constructor. auto.
Qed.
Hint Resolve ssedge_imp_sspath.

Lemma comm_imp_ssedge : forall x y,
x --> y -> x =-> y.
Proof.
  intros x y edge. constructor. auto.
Qed.
Hint Resolve comm_imp_ssedge.

Lemma comm_imp_sspath : forall x y,
x --> y ->
x << y.
Proof.
  auto.
Qed.
Hint Resolve comm_imp_sspath.

Lemma succ_imp_ssedge : forall x y,
x ==> y -> x =-> y.
Proof.
  intros x y edge. constructor 2. auto.
Qed.
Hint Resolve succ_imp_ssedge.

Lemma succ_imp_sspath : forall x y,
x ==> y ->
x << y.
Proof.
  auto.
Qed.
Hint Resolve succ_imp_sspath.

Lemma sspath'_in_l : forall N x y,
x <[N]< y ->
set_In x N.
Proof.
  intros N x y edge.
  induction edge; subst; eauto. 
Qed.
Hint Resolve sspath'_in_l.

Lemma sspath'_in_r : forall N x y,
x <[N]< y ->
set_In x N.
Proof.
  intros N x y edge.
  induction edge; subst; eauto.
Qed.
Hint Resolve sspath'_in_r.

Lemma sspath'_imp_sspath : forall N x y,
x <[N]< y ->
x << y.
Proof.
  intros N x y edge.
  induction edge.
  constructor. eauto.
  eapply (t_trans Node SSEdge x y z); eauto.
Qed.
Hint Resolve sspath'_imp_sspath.

Theorem sspath_transitivity :
transitive SSPath.
Proof.
  unfold SSPath.
  intros i j k Hij Hjk.
  apply (t_trans Node SSEdge i j k Hij Hjk).
Qed.

Theorem sspath'_transitivity : forall N,
transitive (SSPath' N).
Proof.
  intros N i j k Hij Hjk.
  apply (t_trans Node (SSEdge' N) i j k Hij Hjk).
Qed.
Hint Constructors SSPathEq'.

Lemma sspatheq'_in_l : forall N x y,
x <[N]<* y ->
set_In x N.
Proof.
  intros N x y edge.
  induction edge; subst; eauto. 
Qed.
Hint Resolve sspatheq'_in_l.

Lemma sspatheq'_in_r : forall N x y,
x <[N]< y ->
set_In y N.
Proof.
  intros N x y edge.
  induction edge; subst; eauto.
Qed.
Hint Resolve sspatheq'_in_r.

Lemma sspatheq'_imp_sspatheq : forall N x y,
x <[N]<* y ->
x <<* y.
Proof.
  intros N x y edge.
  induction edge.
  apply rt_refl.
  induction H. constructor. eauto.
  eapply (rt_trans Node SSEdge x y z); eauto.
Qed.
Hint Resolve sspatheq'_imp_sspatheq.

Theorem sspatheq_opts: forall n m,
n <<* m -> n << m \/ n = m.
Proof.
  intros n m Hpatheq.
  induction Hpatheq.
  left. apply t_step. exact H.
  right. reflexivity.
  destruct IHHpatheq1 as [pathxy | eqxy].
    destruct IHHpatheq2 as [pathyz | eqyz].
      left. eapply t_trans. exact pathxy. exact pathyz.
      subst y. left. exact pathxy.
    destruct IHHpatheq2 as [pathyz | eqyz].
      subst x. left. exact pathyz.
      right. subst. reflexivity.
Qed.
Hint Resolve sspatheq_opts.

Theorem sspatheq_transitivity :
transitive SSPathEq.
Proof.
  unfold transitive.
  intros i j k Hij Hjk.
  destruct Hij. 
    eapply rt_trans. eapply rt_step. exact H. 
    exact Hjk. exact Hjk. 
    eapply rt_trans. exact Hij1. eapply rt_trans.
    exact Hij2. exact Hjk.
Qed.

Theorem sspatheq'_transitivity : forall N,
transitive (SSPathEq' N).
Proof.
  unfold transitive.
  intros N i j k Hij Hjk.
  destruct Hij. auto.
  destruct Hjk. auto.
  forwards*: (sspath'_transitivity).
Qed.

Lemma comm_imp_rx : forall x y,
x --> y ->
is_rx y.
Proof.
  intros x y cedge.
  destruct cedge as [x y m [[tx rx] sneq]].
  exists m. auto.
Qed.  
Hint Resolve comm_imp_rx.

Lemma comm_imp_tx : forall x y,
x --> y ->
is_tx x.
Proof.
  intros x y cedge.
  destruct cedge as [x y m [[tx rx] sneq]].
  exists m. auto.
Qed.  
Hint Resolve comm_imp_tx.

Lemma bundle_ssedge_inclusion : forall (B: Bundle) (n m: Node),
n =-> m ->
set_In m (Nodes B) -> set_In n (Nodes B).
Proof.
  intros B n m ssedge Hin.
  destruct B as [N E ndN ndE valE predIncl Txincl uniqtx acyc]; simpl in *.
  destruct ssedge; eauto.
Qed.
Hint Resolve bundle_ssedge_inclusion.

Lemma sspath_imp_ssedge_l : forall x y,
x << y ->
exists x', x =-> x'.
Proof.
  intros x y sspath.
  induction sspath.
  exists y. exact H.
  exact IHsspath1.
Qed.  
Hint Resolve sspath_imp_ssedge_l.

Lemma sspath_imp_ssedge_r : forall x y,
x << y ->
exists y', y' =->  y.
Proof.
  intros x y sspath.
  induction sspath.
  exists x. exact H.
  exact IHsspath2.
Qed.  
Hint Resolve sspath_imp_ssedge_r.

Lemma sspath'_dec : forall (B: Bundle),
forall x y, {x <{B}< y} + {~x <{B}< y}.
Proof.
  intros B x y.
  forwards*: (restricted_dec_clos_trans_dec).
  unfold CoLoRRelMidex.eq_dec; auto.
  unfold CoLoRRelMidex.rel_dec; auto.
  intros q r qr. split.
  eapply ssedge'_in_l. eauto. 
  eapply ssedge'_in_r. eauto. 
Qed.
Hint Resolve sspath'_dec.

Lemma neq_sspatheq_imp_sspath : forall (x y: Node),
x <> y ->
x <<* y ->
x << y.
Proof.
  intros x y neq patheqxy.
  induction patheqxy.
  Case "SSEdge x y".
    apply t_step. exact H.
  Case "x = y". assert False as F. apply neq. reflexivity. inversion F.
  Case "x y z".
    destruct (eq_node_dec y z) as [eqyz | neqyz].
    SCase "y = z". subst y. apply IHpatheqxy1. exact neq.
    SCase "y <> z". 
      destruct (eq_node_dec x y) as [eqxy | neqxy].
      SSCase "x = y". subst x. apply IHpatheqxy2. exact neqyz.
      SSCase "x <> y". eapply t_trans. apply IHpatheqxy1. exact neqxy.
        apply IHpatheqxy2. exact neqyz.
Qed.      

Lemma sspatheq_trans_cycle : forall (x y: Node),
x <> y ->
x <<* y ->
y <<* x ->
x << x.
Proof.
  intros x y neq patheqxy patheqyx.
  eapply t_trans.
  Case "path x y".
    eapply neq_sspatheq_imp_sspath. exact neq. exact patheqxy.
  Case "path y x".
    eapply neq_sspatheq_imp_sspath. intros contra. subst.
    apply neq. reflexivity.
    exact patheqyx.
Qed.
Hint Resolve sspatheq_trans_cycle.

Definition set_reflexive 
           { X:Type} 
           (s:set X)
           (R: relation X) : Prop := 
  forall x:X, set_In x s -> R x x.

Definition set_transitive
           { X:Type} 
           (s:set X)
           (R: relation X) : Prop := 
  forall x y z:X, set_In x s -> 
                  set_In y s ->
                  set_In z s ->
                  R x y ->
                  R y z ->
                  R x z.

Definition set_antisymmetric
           { X:Type} 
           (s:set X)
           (R: relation X) : Prop := 
  forall x y:X, set_In x s -> 
                  set_In y s ->
                  R x y ->
                  R y x ->
                  x = y.

Record set_order {X:Type} (s: set X) (R: relation X) : Prop :=
  { set_ord_refl : set_reflexive s R;
    set_ord_trans : set_transitive s R;
    set_ord_antisym : set_antisymmetric s R}.

(* Lemma 2.7a (partial order)  *)
Lemma bundle_partial_order : forall (B:Bundle),
set_order (Nodes B) (SSPathEq' (Nodes B)).
Proof.
  intros B.
  split.
  Case "Reflexivity".
    intros x. auto.
  Case "Transitivity".
    intros x y z xIn yIn zIn xy yz.
    eapply sspatheq'_transitivity; eauto.
  Case "AntiSymmetry".
    intros x y xIn yIn xy yx.
    destruct B as [N E ndN ndE valE predIncl Txincl uniqtx acyc]; simpl in *.
    destruct (eq_node_dec x y) as [xyeq | xyneq].
    SCase "x = y". exact xyeq.
    SCase "x <> y".
      destruct xy. tryfalse.
      destruct yx. tryfalse.
      forwards*: (sspath'_transitivity N n m n).
      forwards*: (acyc n).
Qed.
Hint Resolve bundle_partial_order.

Lemma sspath'_strict_order : forall (B: Bundle),
StrictOrder Node (SSPath' (Nodes B)).
Proof.
  intros B.
  destruct B as [N E ndN ndE valE predIncl Txincl uniqtx acyc]; simpl in *.
  split.
  Case "Irreflexivity".
    intros x. apply acyc.
  Case "Transitivity".
    apply sspath'_transitivity.
Qed.
Hint Resolve sspath'_strict_order.

Definition subset_comm' : forall s s' x y,
subset s s' ->
x -[s]-> y ->
x -[s']-> y.
Proof.
  intros s s' x y sbst edge.
  constructor; eauto.
Qed.
Hint Resolve subset_comm'.

Definition subset_succ' : forall s s' x y,
subset s s' ->
x =[s]=> y ->
x =[s']=> y.
Proof.
  intros s s' x y sbst edge.
  constructor; eauto.
Qed.
Hint Resolve subset_succ'.

Definition subset_spath' : forall s s' x y,
subset s s' ->
x =[s]=>+ y ->
x =[s']=>+ y.
Proof.
  intros s s' x y sbst path.
  induction path.
  constructor. constructor. eauto. eauto. eauto.
  econstructor 2. eauto. eauto.
Qed.
Hint Resolve subset_spath'.

Definition subset_ssedge' : forall s s' x y,
subset s s' ->
x =[s]-> y ->
x =[s']-> y.
Proof.
  intros s s' x y sbst edge.
  destruct edge. constructor. eauto.
                 constructor 2. eauto.
Qed.
Hint Resolve subset_ssedge'.

Definition subset_sspath' : forall s s' x y,
subset s s' ->
x <[s]< y ->
x <[s']< y.
Proof.
  intros s s' x y sbst path.
  induction path. constructor. eauto.
  econstructor 2. eauto. eauto.
Qed.
Hint Resolve subset_sspath'.

Definition subset_sspatheq' : forall s s' x y,
subset s s' ->
x <[s]<* y ->
x <[s']<* y.
Proof.
  intros s s' x y sbst path.
  induction path. constructor. eauto. eauto.
Qed.
Hint Resolve subset_sspatheq'.

(* Lemma 2.7b (non-empty subsets contain minimal members) *)
Lemma bundle_subset_minimal : forall B N',
subset N' (Nodes B) ->
N' <> [] ->
exists min, set_minimal B N' min.
Proof.
  intros B N' sub nempty.
  forwards*: (minimal_set_mem 
                Node 
                eq_node_dec
                (SSPath' (Nodes B))
                (sspath'_dec B)
                (sspath'_strict_order B) 
                N').
  destruct H. tryfalse. destruct H.
  exists x.
  split. auto. split. iauto. iauto.  
Qed.
Hint Resolve bundle_subset_minimal.

Hint Unfold set_minimal.
Lemma set_minimal_In : forall B s x,
set_minimal B s x -> set_In x s.
Proof.
  intros B s x setmin.
  destruct setmin; iauto.
Qed.  
Hint Resolve set_minimal_In.

Lemma bundle_pred_inclusion : forall B x y,
set_In y (Nodes B) ->
x << y ->
set_In x (Nodes B).
Proof.
  intros B x y yIn xy.
  destruct B as [N E ndN ndE valE predIncl Txincl uniqtx acyc]; simpl in *.
  induction xy.
  destruct H; eauto.
  eauto.
Qed.
Hint Resolve bundle_pred_inclusion.

Lemma bundle_pred_comm : forall B x y,
set_In y (Nodes B) ->
x --> y ->
x -{B}-> y.
Proof.
  intros B x y yIn xy.
  destruct B as [N E ndN ndE valE predIncl Txincl uniqtx acyc]; simpl in *.
  constructor; eauto.
Qed.
Hint Resolve bundle_pred_comm.

Lemma bundle_pred_succ : forall B x y,
set_In y (Nodes B) ->
x ==> y ->
x ={B}=> y.
Proof.
  intros B x y yIn xy.
  destruct B as [N E ndN ndE valE predIncl Txincl uniqtx acyc]; simpl in *.
  constructor; eauto.
Qed.
Hint Resolve bundle_pred_succ.

Lemma bundle_pred_ssedge : forall B x y,
set_In y (Nodes B) ->
x =-> y ->
x ={B}-> y.
Proof.
  intros B x y yIn xy.
  destruct B as [N E ndN ndE valE predIncl Txincl uniqtx acyc]; simpl in *.
  destruct xy.
  constructor; auto.
  constructor 2; auto.
Qed.
Hint Resolve bundle_pred_ssedge.

Lemma bundle_pred_pred' : forall B x y,
set_In y (Nodes B) ->
x << y ->
x <{B}< y.
Proof.
  intros B x y yIn xy.
  induction xy.
  constructor; auto.
  forwards*: IHxy2.
  eapply t_trans. apply IHxy1. eauto.
  auto.
Qed.
Hint Resolve bundle_pred_pred'.

(* Lemma 2.8' - set minimal is tx (exactly as stated in SS paper) *)
Lemma minimal_is_tx' : forall B N',
    subset N' (Nodes B) ->
    (forall m m' : Node, 
       term(m) = term(m') ->
       (set_In m N' <-> set_In m' N')) ->
    forall n, set_minimal B N' n ->
is_tx n.
Proof.
  intros B N' sub incl n setmin.
  destruct setmin as [sub2 [minIn minnopre]].
  remember B as bundle.
  destruct bundle as [N E ndN ndE valE predIncl Txincl uniqtx acyc]; simpl in *.
  remember (sterm n) as nsterm. symmetry in Heqnsterm.
  destruct nsterm.
  exists t. exact Heqnsterm.
  unfold ExistsUniqueTx in uniqtx.
  destruct (uniqtx n t) as [[x xpred] nRx]. auto. auto.
  forwards: (minnopre x). eapply (incl x n). eauto. auto.
  assert False. apply H. constructor. constructor. auto. contradiction.
Qed.
Hint Resolve minimal_is_tx.

(* Lemma 2.8 convenient consequence *)
Lemma term_filter_min_tx : 
  forall
    (MP : Term -> Prop) 
    (MPdec : forall x, {MP x} + {~MP x})
    (B : Bundle),
forall n, set_minimal B (term_filter MPdec (Nodes B)) n ->
is_tx n.
Proof.
  intros MP MPdec B n nmin.
  destruct nmin as [sub2 [minIn minnopre]].
  remember B as bundle.
  destruct bundle as [N E ndN ndE valE predIncl Txincl uniqtx acyc]; simpl in *.
  remember (sterm n) as nsterm. symmetry in Heqnsterm.
  destruct nsterm.
  exists t. exact Heqnsterm.
  unfold ExistsUniqueTx in uniqtx.
  destruct (uniqtx n t) as [[x xpred] nRx]. auto. auto.
  forwards: (minnopre x).
  unfold term_filter in minIn. apply filter_In in minIn.
  destruct minIn.
  forwards: (comm'_in_l N x n); auto.
  eapply filter_In. split; auto.
  erewrite (comm_term_eq x n). auto. eauto.
  forwards: H. constructor. constructor. auto. tryfalse.
Qed.
Hint Resolve term_filter_min_tx.

Lemma in_term_filter : 
  forall 
    (n:Node)
    (MP : Term -> Prop) 
    (MPdec : forall x, {MP x} + {~MP x})
    (B : Bundle)
    (N': set Node),
N' = (term_filter MPdec (Nodes B)) ->
set_In n N' ->
MP (term n).
Proof.
  intros n MP MPdec B N' N'eq nIn.
  unfold term_filter in *.
  remember (fun n : Node => if MPdec (term n) 
                             then true 
                             else false) as f.
  destruct (filter_In 
              f
              n
              (Nodes B)) as [InImp ImpIn].
  subst f. destruct (MPdec (term n)). auto.
  rewrite N'eq in *.
  apply InImp in nIn. destruct nIn. tryfalse.
Qed.  

Lemma term_filter_in : 
  forall 
    (n:Node)
    (MP : Term -> Prop) 
    (MPdec : forall x, {MP x} + {~MP x})
    (B : Bundle)
    (N': set Node),
set_In n (Nodes B) ->
N' = (term_filter MPdec (Nodes B)) ->
MP (term n) ->
set_In n N'.
Proof.
  intros n MP MPdec B N' inB N'eq MPn.
  unfold term_filter in *.
  subst N'. apply filter_In. split. auto.
  destruct (MPdec (term n)). reflexivity. auto.
Qed.

Lemma eq_term_in_term_filter : 
  forall
    (n n':Node) 
    (MP : Term -> Prop) 
    (MPdec : forall x, {MP x} + {~MP x})
    (B : Bundle)
    (N': set Node),
set_In n' (Nodes B) ->
term n = term n' ->
N' = (term_filter MPdec (Nodes B)) ->
set_In n N' ->
set_In n' N'.
Proof.
  intros n n' MP MPdec B N' n'IN termeq N'eq nIn.
  forwards: (in_term_filter n MP MPdec B N'). auto. auto.
  rewrite termeq in *.
  unfold term_filter in *.
  remember (fun n : Node => if MPdec (term n) 
                             then true 
                             else false) as f.
  destruct (filter_In 
              f
              n'
              (Nodes B)) as [InImp ImpIn].
  rewrite N'eq in *.
  apply ImpIn.
  split; auto. subst f. destruct (MPdec (term n')); auto; tryfalse.
Qed.

(* Lemma 2.9 originating occurrence at minimal element *)
Lemma min_origin : forall B N' n t,
(forall m, (set_In m (Nodes B)
           /\ t <st (term(m))) -> 
           set_In m N') ->
(forall m, set_In m N' -> 
           (set_In m (Nodes B)
           /\ t <st (term(m)))) -> 
set_minimal B N' n ->
Origin t n.
Proof.
  intros B N' n t N'deff N'defb nmin.
  destruct (N'defb n). auto.
  forwards: (minimal_is_tx B N').
  destruct B as [N E ndN ndE valE uniqtx acyc]; simpl in *.
  intros x xIn. apply N'defb. auto.
  forwards: (N'deff n). split.
  destruct nmin as [Bsub [minIn nopred]].
  auto. apply N'defb. iauto.
  destruct B as [N E ndN ndE valE uniqtx acyc]; simpl in *.
  intros m m' termeq.
  split; intros Hin.
  destruct (N'defb m). auto.
  apply N'deff. split. 

  apply N'defb. apply N'deff.


auto. congruence.
  destruct (N'defb m' Hin).
  apply N'deff. split. auto. congruence.
  eassumption. iauto.
  split. assumption. split.
  forwards: minimal_is_tx. destruct nmin; iauto.
  intros j k [Hin [Hin2 termeq]].
  split; intros HIn.
  forwards: (N'defb j); auto. apply N'deff. split. auto.
  rewrite termeq in *. iauto.
  forwards: (N'defb k); auto. apply N'deff. split. auto.
  rewrite termeq in *. iauto.
  eassumption. assumption.
  intros n' n'edge contrast.
  destruct nmin as [inB [inN' nopred]].
  forwards: bundle_pred_pred'. eassumption. eauto.
  forwards: (N'deff n'). split. eauto. auto.
  eapply (nopred n'). auto. auto. 
Qed.
Hint Resolve min_origin.

(* Lemma 2.9 w/ term_filter *)
Lemma term_filter_min_origin : 
  forall 
    (n:Node)
    (t:Term)
    (B : Bundle)
    (N': set Node),
N' = (term_filter (st_dec t) (Nodes B)) ->
set_minimal B N' n ->
Origin t n.
Proof.
  intros n t B N' N'eq ismin.
  inversion ismin as [subs [nIn nopred]].
  apply (min_origin B N').
  intros m [mIn mst]. forwards: (term_filter_in m). eauto.
  eauto. auto. auto.
  intros m mIn. split.
  auto. eapply in_term_filter. eauto. auto. auto.
Qed.


(* Proposition 2.12 *)
Lemma encr_subterm_imp : forall k k' h h',
k <> k' ->
{h'}^[k'] <st {h}^[k] ->
{h'}^[k'] <st h.
Proof.
  intros k k' h h' kneq st.
  inversion st; subst. iauto. auto.
Qed.
Hint Resolve encr_subterm_imp.

Lemma node_alignment : forall n,
RegularNode n \/ PenetratorNode n.
Proof.
  intros n. unfold RegularNode. unfold PenetratorNode.
  apply strand_alignment.
Qed.

Lemma nonreg_imp_pen : forall n,
~ RegularNode n -> PenetratorNode n.
Proof.
  intros n contra. destruct (node_alignment n).
  contradiction. auto.
Qed.

Lemma nonpen_imp_reg : forall n,
~ PenetratorNode n -> RegularNode n.
Proof.
  intros n contra. destruct (node_alignment n).
  auto. contradiction.
Qed.


Lemma origin_tx : forall n t,
Origin t n ->
is_tx n.
Proof.
  intros n t orig.
  destruct orig. iauto.
Qed.
Hint Resolve origin_tx.

Lemma origin_st : forall n t,
Origin t n -> t <st term n. 
Proof.
  intros n t orig.
  destruct orig as [st [tx nopredst]].
  forwards: node_sterm_term_tx. eauto. congruence.
Qed.
Hint Resolve origin_st.

Lemma origin_nosucc_st : forall n t,
Origin t n ->
forall n', n' ==>+ n -> ~ t <st term n'.
Proof.
  intros n t orig. destruct orig as [st [tx nopredst]]. 
  auto.
Qed.
Hint Resolve origin_nosucc_st.

Lemma particular_min_sterm:
  forall {min actual_content},
    ((strand min) = [actual_content]) ->
    sterm min = actual_content.
Proof.
  intros min actual_content seq.
  assert (length (strand min) = 1) as len. rewrite seq. auto.
  assert ((index min) = 0) as imin. 
  remember (index_len_node min). omega.
  forwards: (nth_node min). eauto. eauto.
  simpl in *. congruence.
Grab Existential Variables. assumption.
Qed.
Hint Resolve particular_min_sterm.

Lemma particular_min_term:
  forall {min actual_content},
    ((strand min) = [actual_content]) ->
    term min = sterm_term actual_content.
Proof.
  intros min actual_content seq.
  unfold term.
  erewrite particular_min_sterm.
  tauto. auto.
Qed.
Hint Resolve particular_min_term.

Lemma key_st_text_false : forall k t,
(#k) <st (!t) -> False.
Proof. intros. inversion H. Qed.
Hint Resolve key_st_text_false.


Lemma node_strand_3height_opts : forall (n:Node) (sm1 sm2 sm3:STerm),
(strand n) = [sm1; sm2; sm3] ->
(sterm n) = sm1 \/ (sterm n) = sm2 \/ (sterm n) = sm3.
Proof. 
  intros.
  assert ((index n) = 0 \/ (index n) = 1 \/ (index n) = 2 \/ (index n) > 2). omega. 
  destruct H0; forwards*: (nth_node n).
  rewrite H0 in *. rewrite H in *. simpl in *; inversion H1.
  left. auto. destruct H0.
  rewrite H0 in *. rewrite H in *. simpl in *; inversion H1.
  right. left. auto. destruct H0.
  rewrite H0 in *. rewrite H in *. simpl in *; inversion H1.
  right. right. auto.
  destruct n. simpl in *. assert (length (fst x) = 3). rewrite H. 
  simpl. reflexivity. omega.
Grab Existential Variables. assumption. assumption.
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

Lemma node_sterm_in_strand : forall n s,
(strand n) = s ->
List.In (sterm n) s.
Proof.
  intros.
  forwards*: (nth_error_node n).
  eapply nth_error_some_In. subst. exact H0.
Qed.  
Hint Resolve node_sterm_in_strand.

Lemma node_hd_or_rest : forall n h rest,
(strand n) = h :: rest ->
(sterm n) = h \/ List.In (sterm n) rest.  
Proof.
  intros n h rest seq. 
  forwards*: (node_sterm_in_strand n (h :: rest)).
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

Lemma sterm_index_0 : forall n x0 rest,
index n = 0 ->
strand n = x0 :: rest ->
sterm n = x0.
Proof.
  intros n x0 rest indx streq.
  forwards*: (nth_node n).  
  rewrite indx in *. rewrite streq in *.
  simpl in *. inversion H; auto.  
Grab Existential Variables. assumption.
Qed.
Hint Resolve sterm_index_0.

Lemma term_index_0 : forall n x0 rest,
index n = 0 ->
strand n = x0 :: rest ->
term n = sterm_term x0.
Proof.
  intros n x0 rest indx streq.
  forwards*: (nth_node n).  
  rewrite indx in *. rewrite streq in *.
  simpl in *. inversion H; auto.  
Grab Existential Variables. assumption.
Qed.
Hint Resolve term_index_0.

Lemma sterm_index_1 : forall n x1 x0 rest,
index n = 1 ->
strand n = x0 :: x1 :: rest ->
sterm n = x1.
Proof.
  intros n x1 x0 rest indx streq.
  forwards*: (nth_node n).  
  rewrite indx in *. rewrite streq in *.
  simpl in *. inversion H; auto.  
Grab Existential Variables. assumption.
Qed.
Hint Resolve sterm_index_1.

Lemma term_index_1 : forall n x1 x0 rest,
index n = 1 ->
strand n = x0 :: x1 :: rest ->
term n = sterm_term x1.
Proof.
  intros n x1 x0 rest indx streq.
  forwards*: (nth_node n).  
  rewrite indx in *. rewrite streq in *.
  simpl in *. inversion H; auto.  
Grab Existential Variables. assumption.
Qed.
Hint Resolve sterm_index_1.

Lemma sterm_index_2 : forall n x2 x1 x0 rest,
index n = 2 ->
strand n = x0 :: x1 :: x2 :: rest ->
sterm n = x2.
Proof.
  intros n x2 x1 x0 rest indx streq.
  forwards*: (nth_node n).  
  rewrite indx in *. rewrite streq in *.
  simpl in *. inversion H; auto.  
Grab Existential Variables. assumption.
Qed.
Hint Resolve sterm_index_2.

Lemma term_index_2 : forall n x2 x1 x0 rest,
index n = 2 ->
strand n = x0 :: x1 :: x2 :: rest ->
term n = sterm_term x2.
Proof.
  intros n x2 x1 x0 rest indx streq.
  forwards*: (nth_node n).  
  rewrite indx in *. rewrite streq in *.
  simpl in *. inversion H; auto.  
Grab Existential Variables. assumption.
Qed.
Hint Resolve term_index_2.

Lemma sterm_index_3 : forall n x3 x2 x1 x0 rest,
index n = 3 ->
strand n = x0 :: x1 :: x2 :: x3 :: rest ->
sterm n = x3.
Proof.
  intros n x3 x2 x1 x0 rest indx streq.
  forwards*: (nth_node n).  
  rewrite indx in *. rewrite streq in *.
  simpl in *. inversion H; auto.  
Grab Existential Variables. assumption.
Qed.
Hint Resolve sterm_index_3.

Lemma term_index_3 : forall n x3 x2 x1 x0 rest,
index n = 3 ->
strand n = x0 :: x1 :: x2 :: x3 :: rest ->
term n = sterm_term x3.
Proof.
  intros n x3 x2 x1 x0 rest indx streq.
  forwards*: (nth_node n).  
  rewrite indx in *. rewrite streq in *.
  simpl in *. inversion H; auto.  
Grab Existential Variables. assumption.
Qed.
Hint Resolve term_index_3.

Lemma sterm_index_4 : forall n x4 x3 x2 x1 x0 rest,
index n = 4 ->
strand n = x0 :: x1 :: x2 :: x3 :: x4 :: rest ->
sterm n = x4.
Proof.
  intros n x4 x3 x2 x1 x0 rest indx streq.
  forwards*: (nth_node n).  
  rewrite indx in *. rewrite streq in *.
  simpl in *. inversion H; auto.  
Grab Existential Variables. assumption.
Qed.
Hint Resolve sterm_index_4.

Lemma term_index_4 : forall n x4 x3 x2 x1 x0 rest,
index n = 4 ->
strand n = x0 :: x1 :: x2 :: x3 :: x4 :: rest ->
term n = sterm_term x4.
Proof.
  intros n x4 x3 x2 x1 x0 rest indx streq.
  forwards*: (nth_node n).  
  rewrite indx in *. rewrite streq in *.
  simpl in *. inversion H; auto.  
Grab Existential Variables. assumption.
Qed.
Hint Resolve term_index_4.

Lemma index_strand_len_1 : forall n g,
strand n = [g] ->
index n = 0.
Proof.
  intros n g seq.
  remember (index n) as ind.
  destruct n. simpl in *. rewrite seq in *.
  simpl in *. omega.
Qed.

Lemma origin_tx_head : forall n g rest,
index n = 0 ->
strand n = (+g) :: rest ->
Origin g n.
Proof.
  intros n g rest ind seq.
  forwards: term_index_0. eauto. eauto.
  split. simpl in *. rewrite H. auto.
  split. eauto.
  intros n' edge.
  forwards: spath_imp_index_lt. eauto. omega.
Qed.

Lemma no_origin_after_rx : forall n g rest,
(strand n) = (-g) :: rest ->
~Origin g n.
Proof with eauto.
  intros n g rest streq orig.
  edestruct (node_hd_or_rest n)...
  assert (exists n', strand n' = strand n /\ index n' = 0) as exn'.
  eexists (exist _ ((strand n), 0) _)... 
  destruct exn' as [n' [seq n'indx]].
  destruct orig as [Hst [Htx Hnopred]].
  apply (Hnopred n').
  eapply spath_from_props...
  assert (index n = 0 \/ index  n > 0) as [Hi0 | Higr0]. omega.
  forwards*: (nth_node n).
  rewrite streq in *. rewrite Hi0 in *.
  simpl in *. inversion H0.
  forwards*: tx_rx_false. auto.
  forwards*: (nth_node n').
  rewrite seq in *. rewrite streq in *.
  rewrite n'indx in *. simpl in *.
  inversion H0.
  forwards*: node_sterm_term_rx. rewrite <- seq in *.
  forwards: sterm_index_0. eauto. eauto.
  erewrite (node_sterm_term_rx n' g) in *. auto. auto.
Grab Existential Variables. exact (+g). exact (+g).
  simpl. rewrite streq. simpl. omega. 
Qed.
Hint Resolve no_origin_after_rx.

Lemma equiv_disjunct : forall p,
p \/ p -> p.
Proof. intros. iauto. Qed.

Lemma sterm_not_in_single_list : forall n x y,
sterm n = x ->
x <> y ->
~ List.In (sterm n) [y].
Proof.
  intros n x y stermeq neq notIn.
  rewrite stermeq in *. inversion notIn; tryfalse.
Qed.
Hint Resolve sterm_not_in_single_list.

Lemma tx_neq_rx : forall x y,
(+x) <> (-y).
Proof.
  intros x y contra. inversion contra.
Qed.
Hint Resolve tx_neq_rx.

Lemma rx_neq_tx : forall x y,
(-x) <> (+y).
Proof.
  intros x y contra. inversion contra.
Qed.
Hint Resolve rx_neq_tx.

Lemma key_neq_join : forall k x y,
(#k) <> x * y.
Proof.
  intros k x y contra. inversion contra.
Qed.
Hint Resolve key_neq_join.

Lemma key_neq_encr : forall k x y,
(#k) <> {x}^[y].
Proof.
  intros k x y contra. inversion contra.
Qed.
Hint Resolve key_neq_encr.

Lemma key_neq_txt : forall k t,
(#k) <> (!t).
Proof.
  intros k t contra. inversion contra.
Qed.
Hint Resolve key_neq_txt.


Lemma txt_neq_join : forall t x y,
(!t) <> x * y.
Proof.
  intros t x y contra. inversion contra.
Qed.
Hint Resolve txt_neq_join.

Lemma txt_neq_encr : forall t x y,
(!t) <> {x}^[y].
Proof.
  intros t x y contra. inversion contra.
Qed.
Hint Resolve txt_neq_encr.

Lemma txt_neq_key : forall t k,
(!t) <> (#k).
Proof.
  intros t k contra. inversion contra.
Qed.
Hint Resolve txt_neq_key.

Lemma strand_imp_sterm_in_strand : forall n s,
strand n = s ->
List.In (sterm n) s.
Proof.
  intros n s seq.
  eauto.
Qed.

Lemma value_Some {X:Type}: forall x y : X,
value x = Some y -> x = y.
Proof.
  intros x y vSeq. inversion vSeq. auto.
Qed.
Hint Resolve value_Some.

Lemma nth_error_nil_error : forall X i,
nth_error (nil : list X) i = None.
Proof.
  intros X i.
  induction i. auto.
  auto.
Qed.
Hint Resolve nth_error_nil_error.

Lemma nth_error_nth {X:Type} : forall l i (v d : X),
nth_error l i = Some v -> nth i l d = v.
  intros l.
  induction l.
  intros i v d ntherr.
  rewrite (nth_error_nil_error X i) in *. tryfalse.
  destruct i. simpl in *. auto. simpl in *.
  apply IHl.
Qed.  
Hint Resolve nth_error_nth.


Lemma strand_index_leq : forall x sf sb,
strand x = sf ++ sb ->
index x < length sf ->
List.In (sterm x) sf.
Proof.
  intros x sf sb seq indle.
  forwards*: (nth_error_node x).
  rewrite seq in *.
  forwards: (nth_error_nth (sf ++ sb) (index x) (sterm x)). auto.
  forwards*: (nth_In).
  erewrite app_nth1 in *. rewrite <- H0. eauto. auto.  
Grab Existential Variables. exact (sterm x).
Qed.
Hint Resolve strand_index_leq.


Lemma strand_halfs_index : forall x sf sb,
strand x = sf ++ sb ->
~ List.In (sterm x) sf ->
index x >= length sf.
Proof.
  intros x sf sb seq notIn.
  forwards*: (node_sterm_in_strand x).
  edestruct (in_app_or) as [insf | insb]. eauto.
  tryfalse.
  assert (index x < length sf \/ index x >= length sf) as lenopts. omega.
  destruct lenopts.
  forwards*: strand_index_leq. auto.
Qed.

Lemma nth_app_snd : forall X (l1 l2: list X) i,
i >= length l1 ->
nth_error (l1 ++ l2) i = nth_error l2 (i - length l1).
Proof.
  intros X l1. 
  induction l1.
  intros l2 i len_gr.
  simpl. rewrite <- (minus_n_O i). reflexivity.
  intros l2 i i_gr_l.
  destruct i.
  inversion i_gr_l.
  simpl.
  apply IHl1. inversion i_gr_l.
  omega. subst. simpl in H0. omega.
Qed.

Lemma prev_facts_imp_prev : forall x y,
strand x = strand y ->
index x < index y ->
x << y.
Proof.
  intros x y seq indlt.
  forwards*: spath_from_props.
Qed.
Hint Resolve prev_facts_imp_prev.

Lemma strand_prev_imp_pred : forall f n x xs,
strand n = f ++ x :: xs ->
~ List.In (sterm n) f ->
(sterm n) <> x ->
exists n', n' << n /\ sterm n' = x.
Proof.
  intros f n x xs seq notIn neq.
  forwards*: (node_sterm_in_strand n).
  rewrite seq in *.
  edestruct (in_app_or) as [contra | inxxs]. eauto.
  tryfalse. destruct inxxs. tryfalse.
  remember (strand_halfs_index n f (x :: xs) seq notIn) as greq.
  inversion greq.
  forwards: (nth_error_node n).
  subst. rewrite seq in *. rewrite <- H2 in *.
  forwards*: strand_halfs_index.
  erewrite (nth_app_snd STerm f (x :: xs)) in *.
  rewrite minus_diag in *.
  simpl in *. forwards*: (value_Some (sterm n) x).
  forwards: (nth_error_node n).
  subst. rewrite seq in *. rewrite <- H1 in *.
  forwards*: strand_halfs_index.
  destruct (strand_node (strand n) (length f)) as [n' [ns ni]]. rewrite seq.
  rewrite app_length. simpl. omega.
  exists n'. split.
  apply prev_facts_imp_prev. auto. omega.
  forwards*: (nth_error_node n').
  rewrite ni in *. rewrite seq in *. rewrite ns in *.
  erewrite (nth_app_snd STerm f (x :: xs)) in *.
  rewrite minus_diag in *.  simpl in *. eauto. omega.
Qed.
Hint Resolve strand_prev_imp_pred.

Lemma strand_prev_imp_succ : forall f n x xs,
strand n = f ++ x :: xs ->
~ List.In (sterm n) f ->
(sterm n) <> x ->
exists n', n' ==>+ n /\ sterm n' = x.
Proof.
  intros f n x xs seq notIn neq.
  forwards*: (node_sterm_in_strand n).
  rewrite seq in *.
  edestruct (in_app_or) as [contra | inxxs]. eauto.
  tryfalse. destruct inxxs. tryfalse.
  remember (strand_halfs_index n f (x :: xs) seq notIn) as greq.
  inversion greq.
  forwards: (nth_error_node n).
  subst. rewrite seq in *. rewrite <- H2 in *.
  forwards*: strand_halfs_index.
  erewrite (nth_app_snd STerm f (x :: xs)) in *.
  rewrite minus_diag in *.
  simpl in *. forwards*: (value_Some (sterm n) x).
  forwards: (nth_error_node n).
  subst. rewrite seq in *. rewrite <- H1 in *.
  forwards*: strand_halfs_index.
  destruct (strand_node (strand n) (length f)) as [n' [ns ni]]. rewrite seq.
  rewrite app_length. simpl. omega.
  exists n'. split.
  apply spath_from_props. omega. auto.
  forwards*: (nth_error_node n').
  rewrite ni in *. rewrite seq in *. rewrite ns in *.
  erewrite (nth_app_snd STerm f (x :: xs)) in *.
  rewrite minus_diag in *.  simpl in *. eauto. omega.
Qed.
Hint Resolve strand_prev_imp_succ.

Lemma neq_st_t_false : forall t1 t2,
t1 <> t2 ->
~(!t1) <st (!t2).
Proof.
  intros t1 t2 neeq st.
  inversion st. auto.
Qed.

Lemma neq_term_st_false : forall m t,
m <> (!t) ->
~ m <st (!t).
Proof.
  intros m t neq st.
  inversion st. auto.
Qed.

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

Lemma txt_st_txt : forall t t',
(!t) <st (!t') -> t = t'.
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

Lemma encr_st : forall a b k,
a <> {b}^[k] ->
a <st {b}^[k] ->
a <st b.
Proof.
  intros a b k neq st. 
  inversion st. contradiction. auto.
Qed.
Hint Resolve encr_st.

Lemma st_join_opts : forall a b c : Term,
a <> (b * c) ->
a <st (b * c) ->
a <st b \/ a <st c.
Proof.
  intros a b c neq st.
  inversion st; subst.
  tryfalse.
  auto. auto.
Qed.

Lemma SP_disjunction : forall s,
StandardPenetrator s ->
((exists t, ~ set_In t HTexts /\ s = [ (+(!t)) ])
 \/ 
 (exists g, s = [(-g)])
 \/ 
 (exists g, s = [(-g) ; (+g) ; (+g)]) 
 \/
 (exists g h, s = [(-g) ; (-h) ; (+g*h)])
 \/
 (exists g h, s = [(-g*h) ; (+g) ; (+h)])
 \/ 
 (exists k, ~set_In k HKeys /\ s = [(+ (#k))])
 \/ 
 (exists h k, s = [(- (#k)) ; (-h) ; (+ {h}^[k])])
 \/ 
 (exists k' k h, Inv k' k /\ s = [(- (#k')) ; (- {h}^[k]) ; (+h)])).
Proof.
  intros. inversion H as [t tunk seq minstrand | 
         g seq minstrand |
         g seq minstrand |
         g h seq minstrand |
         g h seq minstrand |
         k' kunk seq minstrand |
         h k' seq minstrand |
         h k' k'' inv seq minstrand]; iauto. 
Qed.