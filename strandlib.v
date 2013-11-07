Require Import Logic List ListSet Arith Peano_dec Omega Ensembles.
Require Import Coq.Sets.Constructive_sets.
Require Import Finite_sets_facts Finite_sets Relation_Definitions.
Require Import Relation_Operators Operators_Properties.
Require Import strictorder set_rep_equiv util.
Require Import finite_set_builder.
Require Import CoLoRRelDec CoLoRRelSub.
Require Import LibTactics.

Require Import strandspace.

Open Scope list_scope.
Import ListNotations.
Open Scope ss_scope.

Hint Resolve Coq.Sets.Constructive_sets.Add_not_Empty Noone_in_empty.



Definition eq_msg_dec : forall x y : Msg,  
  {x = y} + {x <> y}.
Proof.
  decide equality.
Qed.
Hint Resolve eq_msg_dec.

Definition eq_smsg_dec : forall x y : SMsg,  
  {x = y} + {x <> y}.
Proof.
 intros. decide equality.
Qed. 
Hint Resolve eq_smsg_dec.

Definition eq_strand_dec : forall x y : Strand,  
  {x = y} + {x <> y}.
Proof.
 intros. decide equality.
Qed.
Hint Resolve eq_strand_dec.


Lemma node_smsg_msg_tx : forall n t,
smsg(n) = (+ t) ->
msg(n) = t.
Proof.
  intros n t nsmsg.
  unfold msg. rewrite nsmsg. reflexivity. 
Qed.
Hint Resolve node_smsg_msg_tx.

Lemma node_smsg_msg_rx : forall n t,
smsg(n) = (- t) ->
msg(n) = t.
Proof.
  intros n t nsmsg.
  unfold msg. rewrite nsmsg. reflexivity. 
Qed.
Hint Resolve node_smsg_msg_rx.

Definition eq_node_dec : forall x y : Node,
 {x = y} + {x <> y}.
Proof.
  intros [[xs xn] xp] [[ys yn] yp].
  destruct (eq_strand_dec xs ys) as [EQs | NEQs]; subst.
  destruct (eq_nat_dec xn yn) as [EQn | NEQn]; subst.
  left. rewrite (proof_irrelevance (lt yn (length ys)) xp yp). reflexivity.

  right. intros C. inversion C. auto.
  right. intros C. inversion C. auto.
Qed.
Hint Resolve eq_node_dec.

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

Lemma node_indexing_equiv : forall n,
nth_error (strand n) (index n) = Some (smsg n).
Proof.
  intros n.
  unfold smsg. destruct node_smsg_valid. 
  destruct n. simpl in *.
  destruct x0.
  rewrite e. simpl. reflexivity.
Qed.
Hint Resolve node_indexing_equiv.

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

Lemma comm_dec : forall x y,
{x --> y} + {~ x --> y}.
Proof.
  intros x y.
  remember (smsg x) as xsmsg. remember (smsg y) as ysmsg.
  remember (strand x) as xstrand. remember (strand y) as ystrand.
  destruct xsmsg.
  Case "x (tx m)".
    destruct ysmsg.
    SCase "y (tx m0)".
      right. intros contracomm. inversion contracomm; subst.
      destruct H as [[xtx yrx] strandneq].
      rewrite <- Heqysmsg in yrx. inversion yrx.      
    SCase "y (rx m0)".
      destruct (eq_msg_dec m m0) as [msgeq | msgneq].
      SSCase "m = m0".
        destruct (eq_strand_dec xstrand ystrand) as [strandeq | strandneq].
        SSSCase "strands eq".
          right. intros contracomm.
          inversion contracomm; subst. destruct H as [msgs strandsneq].
          apply strandsneq. exact strandeq. 
        SSSCase "strands neq".
          subst m0. left.
          apply (comm x y m). split. split.
          auto. auto. subst. exact strandneq.        
      SSCase "m <> m0".
        right. intros contracomm. inversion contracomm; subst. 
        destruct H as [[xtx yrx] strandneq].
        apply msgneq. rewrite <- Heqxsmsg in xtx.
        rewrite <- Heqysmsg in yrx. inversion xtx; subst. 
        inversion yrx; subst. reflexivity.
  Case "x (rx m)".
    right.
    intros contracomm. inversion contracomm; subst.
    destruct H as [[xtx yrx] strandneq].
    rewrite <- Heqxsmsg in xtx. inversion xtx.
Qed.
Hint Resolve comm_dec.


Theorem comm_irreflexivity : forall n,
~ n --> n.
Proof.
  intros n contraedge.
  inversion contraedge; subst.
  destruct H as [[txsmsg rxsmsg] strandneq].
  apply strandneq. reflexivity.
Qed.
Hint Resolve comm_irreflexivity.

Theorem comm_antisymmetry : 
Antisymmetric Node Comm.
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
      right. intros contrasucc. apply wrongi. inversion contrasucc; subst; omega.
  Case "strands neq".
    right. intros contrasucc. apply sneq. inversion contrasucc; subst; auto.
Qed.  
Hint Resolve succ_dec.


Theorem succ_irreflexivity : forall n,
~n ==> n.
Proof.
  intros n edge.
  inversion edge; subst. omega.
Qed.
Hint Resolve succ_irreflexivity.

Theorem succ_antisymmetry :
Antisymmetric Node Successor.
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

Lemma path_step_holds : forall x x' y,
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
Hint Resolve path_step_holds.

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
    destruct (path_step_holds 
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
Transitive Node StrandPath.
Proof.
  intros i j k Hij Hjk.
  apply (t_trans Node Successor i j k Hij Hjk).
Qed.
Hint Resolve spath_transitivity.

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
Antisymmetric Node SSEdge.
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

Theorem sspath_transitivity :
Transitive Node SSPath.
Proof.
  unfold SSPath.
  intros i j k Hij Hjk.
  apply (t_trans Node SSEdge i j k Hij Hjk).
Qed.
Hint Resolve sspath_transitivity.

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
Transitive Node SSPathEq.
Proof.
  unfold Transitive.
  intros i j k Hij Hjk.
  destruct Hij. 
    eapply rt_trans. eapply rt_step. exact H. 
    exact Hjk. exact Hjk. 
    eapply rt_trans. exact Hij1. eapply rt_trans.
    exact Hij2. exact Hjk.
Qed.


Lemma bundle_ssedge_inclusion : forall (B: Bundle) (n m: Node),
n =-> m ->
(In Node (Nodes B) n <-> In Node (Nodes B) m).
Proof.
  intros B n m ssedge. split; intros Hin.
  destruct B as [N E finN finE valE uniqtx acyc]; simpl in *.
  apply valE in ssedge. apply valE. constructor 2.
  exists n. exact ssedge.
  destruct B as [N E finN finE valE uniqtx acyc].
  apply valE in ssedge. apply valE. constructor 1.
  exists m. exact ssedge.
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

Lemma restricted_to_set : forall (B:Bundle),
exists s, is_restricted SSEdge s /\
forall x, ListSet.set_In x s <-> In Node (Nodes B) x.
Proof.
  intros B.
  destruct B as [N E finN finE valE uniqtx acyc]; simpl in *.
  destruct valE as [EimpInN EimpSSEdge].
  destruct (ensemble_imp_set Node eq_node_dec N finN) 
    as [s [inAll [nodup [n [slen scard]]]]].
  exists s.
  split.
  intros x y sspath.
  split.
  apply inAll. apply EimpInN. constructor. exists y. 
  apply EimpSSEdge. exact sspath.
  apply inAll. apply EimpInN. constructor 2. exists x. 
  apply EimpSSEdge. exact sspath.
  exact inAll.
Qed.

Lemma sspath_dec : forall (B: Bundle) (s: ListSet.set Node),
node_set_Ensemble_equiv s (Nodes B) ->
is_restricted SSEdge s ->
forall x y, {x << y} + {~x << y}.
Proof.
  intros B s bset restrict.
  destruct B as [N E finN finE valE uniqtx acyc]; simpl in *.
  intros x y.
  remember (restricted_dec_clos_trans_dec 
              eq_node_dec 
              ssedge_dec 
              restrict) as alldec.
  apply alldec.
Qed.
Hint Resolve sspath_dec.

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
Hint Resolve neq_sspatheq_imp_sspath.

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

Lemma Origin_imp_strict_defs : forall I t n,
(forall t', t <st t' <-> In Msg I t') ->
Origin t n ->
Origin_with_Ex_Set t n.
Proof.
  intros I t n Iprop Orig.
  exists I. split. exact Iprop.
  destruct Orig as [ntx [nsub nosucc]].
  split. exists (msg n).
  split. apply Iprop in nsub. exact nsub.
  destruct ntx. erewrite node_smsg_msg_tx. exact H. exact H.
  intros n' succ contraIn.
  apply nosucc in succ. apply Iprop in contraIn. contradiction.
Qed.
Hint Resolve Origin_imp_strict_defs.

(* Lemma 2.7a (partial order)  *)
Lemma bundle_partial_order : forall (B:Bundle),
Order Node SSPathEq.
Proof.
  intros B.
  split.
  Case "Reflexivity".
    intros x. apply rt_refl. 
  Case "Transitivity".
    intros x y z xy yz.
    eapply rt_trans. exact xy. exact yz.
  Case "AntiSymmetry".
    intros x y xy yz.
    destruct B as [N E finN finE valE uniqtx acyc]; simpl in *.
    destruct (eq_node_dec x y) as [xyeq | xyneq].
    SCase "x = y". exact xyeq.
    SCase "x <> y". 
      assert (x << x) as contraxx.
        eapply sspatheq_trans_cycle. exact xyneq.
        exact xy. exact yz. apply acyc in contraxx. inversion contraxx.
Qed.
Hint Resolve bundle_partial_order.

Lemma sspath_strict_order : forall (B: Bundle),
StrictOrder Node SSPath.
Proof.
  intros B.
  destruct B as [N E finN finE valE uniqtx acyc]; simpl in *.
  split.
  Case "Irreflexivity".
    intros x. apply acyc.
  Case "Transitivity".
    apply sspath_transitivity.
Qed.
Hint Resolve sspath_strict_order.

(* Lemma 2.7b (non-empty subsets contain minimal members) *)
Lemma bundle_subset_minimal : forall B N',
Included Node N' (Nodes B) ->
N' <> Empty_set Node ->
exists min, set_minimal N' min.
Proof.
  intros B N' incl nempty.
  remember B as bundle.
  destruct bundle as [N E finN finE valE uniqtx acyc]; simpl in *.
  assert (Finite Node N') as finN'. eapply Finite_downward_closed.
    exact finN. exact incl.
  destruct (finite_cardinal Node N' finN') as [n card].
  destruct n. inversion card. rewrite H in nempty.
  assert False as F. apply nempty. reflexivity. inversion F.
  destruct (restricted_to_set B) as [s [restricted setequiv]].
  assert (forall x y, {x << y} + {~ x << y}) as rdec.
  apply (sspath_dec B s). exact setequiv. exact restricted.  
  destruct (minimal_finite_ensemble_mem 
              Node 
              eq_node_dec 
              SSPath 
              rdec
              (sspath_strict_order B) 
              N' 
              n 
              card) as [min [minIn nolt]].
  exists min. split. exact minIn. exact nolt.
Qed.
Hint Resolve bundle_subset_minimal.

(* Lemma 2.8 - set minimal is tx *)
Lemma minimal_is_tx : forall B N',
Included Node N' (Nodes B) ->
(forall m m' : Node, (In Node (Nodes B) m 
               /\ In Node (Nodes B) m'
               /\ msg(m) = msg(m')) -> (* ADDED in N conditions *)
               (In Node N' m <-> In Node N' m')) ->
forall n, set_minimal N' n ->
is_tx n.
Proof.
  intros B N' sub incl n setmin.
  remember B as bundle.
  destruct bundle as [N E finN finE valE uniqtx acyc]; simpl in *.
  assert ((Nodes B) = N) as NB. subst B. simpl. reflexivity.
  remember (smsg n) as nsmsg. symmetry in Heqnsmsg.
  destruct nsmsg.
  exists m. exact Heqnsmsg.
  unfold ExistsUniqueTx in uniqtx.
  assert (In Node N n) as nIn. destruct setmin; auto.
  destruct (uniqtx n m nIn Heqnsmsg) as [[ntx [ntxsmsg [commn inE]]] uniq].
  assert False as F. destruct setmin. apply (H0 ntx). eapply incl.
    split. rewrite <- NB. eapply bundle_ssedge_inclusion. 
    constructor. exact commn. rewrite NB. exact nIn. 
    split. exact nIn. apply node_smsg_msg_tx in ntxsmsg. 
    apply node_smsg_msg_rx in Heqnsmsg. rewrite Heqnsmsg. exact ntxsmsg. 
    exact H. constructor. constructor. exact commn.
  inversion F.
Qed.
Hint Resolve minimal_is_tx.

(* Lemma 2.9 originating occurrence at minimal element *)
Lemma min_origin : forall B N' n t,
(forall m, (In Node (Nodes B) m 
           /\ Subterm t (msg(m))) -> 
           In Node N' m) ->
(forall m, In Node N' m -> 
           (In Node (Nodes B) m 
           /\ Subterm t (msg(m)))) ->
set_minimal N' n ->
Origin t n.
Proof.
  intros B N' n t N'deff N'defb nmin.
  remember B as bundle.
  destruct bundle as [N E finN finE valE uniqtx acyc]; simpl in *.
  assert (N = Nodes B) as NB. subst B. simpl; reflexivity.
  assert (In Node N' n) as nIn. destruct nmin; auto.
  assert (t <st (msg n)) as tsubn.
    apply (N'defb n) in nIn. destruct nIn; auto.
  assert (is_tx n) as nistx.
    assert (Included Node N' N) as incl.
      intros x xIn. apply N'defb in xIn. destruct xIn; auto.
    rewrite NB in incl. apply (minimal_is_tx B N' incl).
    intros x y eqmsg.
    destruct eqmsg as [xIn [yIn eqmsg]].
    split; intros Hin.
    Case "m in -> m' in".
      apply N'defb in Hin. destruct Hin as [xInN tsubx]. 
      assert (Subterm t (msg y)) as ysubt. rewrite <- eqmsg.
        exact tsubx.
      apply N'deff. split. rewrite NB. exact yIn. exact ysubt.
    Case "m' in -> m in".
      apply N'defb in Hin. destruct Hin as [yInN tsuby].
      apply N'deff. split. rewrite NB. exact xIn. 
      assert (Subterm t (msg x)) as xsubt. rewrite eqmsg.
        exact tsuby.
      exact xsubt. 
    exact nmin.
  split. exact nistx.
  split. exact tsubn.
  intros n' succn' contrasub.
  assert (In Node N' n') as n'In.
    apply N'deff. split.
    destruct valE as [pairImpN HInEedge].
    apply pairImpN. left.
    destruct (sspath_imp_ssedge_l n' n succn') as [x n'edge].
    exists x. apply HInEedge. exact n'edge. exact contrasub.
  destruct nmin as [nIn2 noprev]. apply (noprev n'). exact n'In.
  exact succn'.
Qed.
Hint Resolve min_origin.

(* Proposition 2.12 *)
Lemma encr_subterm_imp : forall k k' h h',
k <> k' ->
{h'}^[k'] <st {h}^[k] ->
{h'}^[k'] <st h.
Proof.
  intros k k' h h' kneq st.
  inversion st; subst.
  assert False. apply kneq. reflexivity. contradiction.
  exact H1.
Qed.
Hint Resolve encr_subterm_imp.

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
        destruct (eq_msg_dec a (b1 * b2)).
        SSSCase "a = b1 * b2".
          subst a. left. constructor.
        SSSCase "a <> b1 * b2".
          right. intros contra. inversion contra; subst; try(contradiction).
          apply n1. reflexivity.
  Case "b = encr".
    destruct IHb.
      left. apply st_encr. exact s.
      destruct (eq_msg_dec a ({b}^[k])). subst.
      left. constructor.
      right. intros contra. inversion contra. subst.
      apply n0. reflexivity.
      contradiction.
Qed.
Hint Resolve st_dec.

Fixpoint st_on_strand (t:Msg) (s:Strand) : bool :=
match s with
| nil => false
| x :: xs => 
  if st_dec t (smsg_msg x)
  then true
  else st_on_strand t xs
end.


Theorem align_dec : forall s,
{RegularStrand s} + {PenetratorStrand s}.
Proof.
  intros s. destruct (set_In_dec eq_strand_dec s Protocol); auto.
Qed.
Hint Resolve align_dec.

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
Hint Resolve particular_min_smsg.

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
Hint Resolve particular_min_msg.

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
Hint Resolve no_origin_after_rx.

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

Lemma DolevYao_disjunction : forall s,
DolevYao s ->
((exists t, ~ set_In t PTexts /\ s = [ (+(!t)) ])
 \/ 
 (exists g, s = [(-g)])
 \/ 
 (exists g, s = [(-g) ; (+g) ; (+g)]) 
 \/
 (exists g h, s = [(-g) ; (-h) ; (+g*h)])
 \/
 (exists g h, s = [(-g*h) ; (+g) ; (+h)])
 \/ 
 (exists k, set_In k PKeys /\ s = [(+ (#k))])
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
