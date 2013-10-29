
Require Import Logic List ListSet Arith Peano_dec Omega Ensembles.
Require Import Finite_sets_facts Finite_sets Relation_Definitions.
Require Import Relation_Operators.
Require Import strictorder set_rep_equiv util.
Require Import finite_set_builder.

Require Import strandspace.

Section SimpleSpaces.

Hypothesis PModel : PenetratorModel = DolevYao.

Open Scope list_scope.
Import ListNotations.
Open Scope ss_scope.

(* Proposition 3.3 
   "Let C be a bundle, and let k be a Key s.t. ~ k in Kp,
   If k never originates on a regular node, then K is not
   a subterm of term(n) for any node n in C. In particular,
   for any penetrator node p in C, k is not a subterm
   of the term of p." *)
Theorem non_origin_imp_non_subterm : forall B k,
~ set_In k PKeys ->
(forall n, Origin (#k) n -> ~ RegularNode n) ->
(forall n, In Node (Nodes B) n -> ~ (#k) <st msg(n)).
Proof.
  intros B k notInKp noOrigin n nInN st.
  remember B as bundle.
  destruct bundle as [N E finN finE valE uniqtx acyc]; simpl in *.
  assert (N = Nodes B) as NB. subst B. simpl; reflexivity.
  clear Heqbundle.
  assert (forall x : Node, {(#k) <st msg x} + {~ (#k) <st msg x})
         as Pdec.
    intros x. apply st_dec.    
  destruct (ex_filter_ensemble 
              Node 
              eq_node_dec 
              (fun n => (#k) <st (msg n)) 
              Pdec
              N 
              finN) 
    as [N' [inclN' N'memP]].
  assert (Finite Node N') as finN'. eapply Finite_downward_closed.
    exact finN. exact inclN'.
  destruct finN' as [| N' fin x].
  Case "Empty_set".
    assert (In Node (Empty_set Node) n) as  contra.
      apply N'memP. split. exact nInN. exact st.
    inversion contra.
  Case "non-empty".
    assert (exists min, set_minimal (Add Node N' x) min) as exmin.
      eapply (bundle_subset_minimal B). rewrite <- NB. exact inclN'.
      intros contra. apply Add_not_Empty in contra. contradiction.
    destruct exmin as [min minP].
    assert (Origin (#k) min) as minorg.
      eapply (min_origin B (Add Node N' x)). split.
      intros [mIn mst].
      apply N'memP. split. rewrite NB. exact mIn. exact mst.
      intros mIn. split.
      apply inclN' in mIn. rewrite <- NB. exact mIn.
      apply N'memP in mIn. destruct mIn; auto. exact minP.
    destruct (align_dec (strand min)) as [reg | pen].
    eapply noOrigin. exact minorg. exact reg.
    destruct minorg as [istx [minst minpred]].
    assert (DolevYao (strand min)) as dymin.
    rewrite <- PModel. apply penetrator_behavior. exact pen.
    inversion dymin as 
      [s t tunk seq minstrand | 
       s g seq minstrand |
       s g seq minstrand |
       s g h seq minstrand |
       s g h seq minstrand |
       s k' kunk seq minstrand |
       s h k' seq minstrand |
      s h k' k'' inv seq minstrand]. 
    SCase "M".
      assert (length (strand min) = 1) as len. rewrite seq. auto.
      assert ((index min) = 0) as imin. 
        remember (index_len_node min). omega. 
      assert (nth_error (strand min) (index min) = Some (smsg min)) as ntheq. 
      apply node_indexing_equiv. 
      rewrite seq in ntheq. rewrite imin in ntheq. simpl in ntheq.
      inversion ntheq as [msmsg]. 
      assert (msg min = (!t)) as minmsg.
      apply node_smsg_msg_tx; auto. rewrite minmsg in minst. 
      inversion minst.
    SCase "F".
      assert (length (strand min) = 1) as len. rewrite seq. auto.
      assert ((index min) = 0) as imin. remember (index_len_node min); omega.
      assert (nth_error (strand min) (index min) = Some (smsg min)) as ntheq. 
      apply node_indexing_equiv. 
      rewrite seq in ntheq. rewrite imin in ntheq. simpl in ntheq.
      destruct istx as [t mmsg]. rewrite mmsg in ntheq.
      inversion ntheq.
    SCase "T".
      assert (length (strand min) = 3) as len. rewrite seq. auto.
      assert ((index min) = 0 
              \/ (index min) = 1 
              \/ (index min) = 2) as imin. remember (index_len_node min); omega.
      assert (nth_error (strand min) (index min) = Some (smsg min)) as ntheq. 
      apply node_indexing_equiv. 
      destruct imin as [imin | irest].
      SSCase "index min = 0".
        rewrite seq in ntheq. rewrite imin in ntheq. simpl in ntheq.
        inversion ntheq as [mmsg]. destruct istx as [t mtx]. 
        rewrite mtx in mmsg.
        inversion mmsg.
      destruct irest as [imin | imin].
      SSCase "index min = 1".
        rewrite seq in ntheq. rewrite imin in ntheq. simpl in ntheq.
        inversion ntheq as [mintxmsg]. 
        assert (msg min = g) as minmsg.
        apply node_smsg_msg_tx; auto. rewrite minmsg in minst.
        destruct (strand_node (strand min) 0) as [y [ys yi]].
          rewrite seq. simpl; auto. 
        assert (y << min) as ypremin. constructor.
          constructor 2. constructor. rewrite ys. reflexivity.
          omega.
        apply minpred in ypremin.
        assert (nth_error (strand min) (index y) = Some (smsg y)) as ntheq2.
          rewrite <- ys.
        apply node_indexing_equiv. rewrite seq in ntheq2. rewrite yi in ntheq2.
        simpl in ntheq2. inversion ntheq2 as [rxmsg]. symmetry in rxmsg. 
        eapply node_smsg_msg_rx in rxmsg. rewrite rxmsg in ypremin.
        contradiction.
      SSCase "index min = 2".
        rewrite seq in ntheq. rewrite imin in ntheq. simpl in ntheq.
        inversion ntheq as [mintx]. 
        assert (msg min = g) as minmsg.
        apply node_smsg_msg_tx; auto. rewrite minmsg in minst.
        destruct (strand_node (strand min) 1) as [y [ys yi]].
          rewrite seq. simpl; auto. 
        assert (y << min) as ypremin. constructor.
          constructor 2. constructor. rewrite ys. reflexivity.
          omega.
        apply minpred in ypremin.
        assert (nth_error (strand min) (index y) = Some (smsg y)) as ntheq2.
          rewrite <- ys.
        apply node_indexing_equiv. rewrite seq in ntheq2. rewrite yi in ntheq2.
        simpl in ntheq2. inversion ntheq2 as [rxmsg]. symmetry in rxmsg. 
        eapply node_smsg_msg_tx in rxmsg. rewrite rxmsg in ypremin.
        contradiction.      
    SCase "C".
      assert (length (strand min) = 3) as len. rewrite seq. auto.
      assert ((index min) = 0 
              \/ (index min) = 1 
              \/ (index min) = 2) as imin. remember (index_len_node min); omega.
      assert (nth_error (strand min) (index min) = Some (smsg min)) as ntheq. 
      apply node_indexing_equiv. 
      destruct imin as [imin | irest].
      SSCase "index min = 0".
        rewrite seq in ntheq. rewrite imin in ntheq. simpl in ntheq.
        destruct istx as [t mtx]. rewrite mtx in ntheq.
        inversion ntheq.
      destruct irest as [imin | imin].
      SSCase "index min = 1".
        rewrite seq in ntheq. rewrite imin in ntheq. simpl in ntheq.
        destruct istx as [t mtx]. rewrite mtx in ntheq.
        inversion ntheq.
      SSCase "index min = 2".
        destruct (strand_node (strand min) 0) as [n0 [n0s n0i]].
          rewrite seq. simpl; auto. 
        destruct (strand_node (strand min) 1) as [n1 [n1s n1i]].
          rewrite seq. simpl; auto. 
        rewrite seq in ntheq. rewrite imin in ntheq. simpl in ntheq.
        inversion ntheq as [mmsg]. symmetry in mmsg. 
        apply node_smsg_msg_tx in mmsg. rewrite mmsg in minst.
        inversion minst as [m | m l r Hst | m l r Hst | m1 m2 k1 Hst]; subst.
        SSSCase "#k <st g".
          assert (n0 << min) as n0pred. econstructor 2. constructor. 
            constructor 2. constructor. rewrite n0s. symmetry in n1s. 
            exact n1s. omega. constructor. constructor 2. constructor. 
            exact n1s. omega.
          apply minpred in n0pred. 
          assert (nth_error (strand n0) (index n0) = Some (smsg n0)) as ntheq2. 
            apply node_indexing_equiv.
          rewrite n0i in ntheq2. rewrite n0s in ntheq2. rewrite seq in ntheq2.
          simpl in ntheq2. inversion ntheq2 as [rxmsg]. symmetry in rxmsg.
          apply node_smsg_msg_rx in rxmsg. rewrite rxmsg in n0pred.
          contradiction.
        SSSCase "#k <st h".
          assert (n1 << min) as n1pred. econstructor. constructor 2. 
            constructor. auto. omega.
          apply minpred in n1pred.
          assert (nth_error (strand n1) (index n1) = Some (smsg n1)) as ntheq2. 
            apply node_indexing_equiv.
          rewrite n1s in ntheq2. rewrite n1i in ntheq2. rewrite seq in ntheq2.
          simpl in ntheq2. inversion ntheq2 as [rxmsg]. symmetry in rxmsg.
          apply node_smsg_msg_rx in rxmsg.
          rewrite rxmsg in n1pred. contradiction.
    SCase "S".
      assert (length (strand min) = 3) as len. rewrite seq. auto.
      assert ((index min) = 0 
              \/ (index min) = 1 
              \/ (index min) = 2) as imin. remember (index_len_node min); omega.
      assert (nth_error (strand min) (index min) = Some (smsg min)) as ntheq. 
      apply node_indexing_equiv. 
      destruct imin as [imin | irest].
      SSCase "index min = 0".
        rewrite seq in ntheq. rewrite imin in ntheq. simpl in ntheq.
        destruct istx as [t mtx]. rewrite mtx in ntheq.
        inversion ntheq.
      destruct irest as [imin | imin].
      SSCase "index min = 1".
        rewrite seq in ntheq. rewrite imin in ntheq. simpl in ntheq.
        destruct (strand_node (strand min) 0) as [n0 [n0s n0i]].
          rewrite seq. simpl; auto. 
        assert (n0 << min) as n0pred. econstructor. constructor 2. 
          constructor. auto. omega.
        apply minpred in n0pred.
        assert (nth_error (strand n0) (index n0) = Some (smsg n0)) as ntheq2.  
          apply node_indexing_equiv.
        rewrite n0s in ntheq2. rewrite n0i in ntheq2. rewrite seq in ntheq2.
        simpl in ntheq2. inversion ntheq2 as [mrx]. symmetry in mrx.
        apply node_smsg_msg_rx in mrx. rewrite mrx in n0pred.
        assert (nth_error (strand min) (index min) = Some (smsg min)) as ntheq3. 
          apply node_indexing_equiv.
         rewrite seq in ntheq3. rewrite imin in ntheq3. simpl in ntheq3.
         inversion ntheq3 as [mmsg]. symmetry in mmsg. 
         apply node_smsg_msg_tx in mmsg.
         rewrite mmsg in minst.
         apply n0pred. constructor. exact minst.
      SSCase "index min = 2".
        rewrite imin in ntheq. rewrite seq in ntheq. simpl in ntheq.
        destruct (strand_node (strand min) 0) as [n0 [n0s n0i]].
          rewrite seq. simpl; auto. 
        destruct (strand_node (strand min) 1) as [n1 [n1s n1i]].
          rewrite seq. simpl; auto. 
        assert (n0 << min) as n0pred. apply (t_trans Node SSEdge n0 n1 min). 
          constructor. constructor 2. constructor. rewrite n0s. 
          auto. omega. constructor. constructor 2. constructor.
          exact n1s. omega.
        apply minpred in n0pred.
        assert (nth_error (strand n0) (index n0) = Some (smsg n0)) as ntheq2. 
          apply node_indexing_equiv.
        rewrite n0s in ntheq2. rewrite n0i in ntheq2. rewrite seq in ntheq2.
        simpl in ntheq2. inversion ntheq2 as [mrx]. symmetry in mrx.
        apply node_smsg_msg_rx in mrx. rewrite mrx in n0pred.
        assert (nth_error (strand min) (index min) = Some (smsg min)) as ntheq3. 
          apply node_indexing_equiv.
         rewrite seq in ntheq3. rewrite imin in ntheq3. simpl in ntheq3.
         inversion ntheq3 as [mtx]. symmetry in mtx. 
         apply node_smsg_msg_tx in mtx.
         rewrite mtx in minst.
         apply n0pred. constructor 3. exact minst.
    SCase "K".
      destruct (eq_key_dec k k'); subst. contradiction.
      assert (nth_error (strand min) (index min) = Some (smsg min)) as ntheq. 
        apply node_indexing_equiv.
      rewrite seq in ntheq. 
      assert (length (strand min) = 1) as len. rewrite seq. auto.
      assert ((index min) = 0)as imin. remember (index_len_node min); omega.
      assert (nth_error (strand min) (index min) = Some (smsg min)) as ntheq2. 
        apply node_indexing_equiv.
      rewrite imin in ntheq2. rewrite seq in ntheq2. simpl in ntheq2.
      inversion ntheq2 as [mtx]. symmetry in mtx. apply node_smsg_msg_tx in mtx.
      rewrite mtx in minst.
      inversion minst. contradiction.      
    SCase "E".
      assert (length (strand min) = 3) as len. rewrite seq. auto.
      assert ((index min) = 0 
              \/ (index min) = 1 
              \/ (index min) = 2) as imin. remember (index_len_node min); omega.
      assert (nth_error (strand min) (index min) = Some (smsg min)) as ntheq. 
        apply node_indexing_equiv. 
      destruct imin as [imin | irest].
      SSCase "index min = 0".
        rewrite imin in ntheq. rewrite seq in ntheq. simpl in ntheq.
        inversion ntheq as [mrx]. destruct istx as [t mtx]. rewrite mtx in mrx.
        inversion mrx.
      destruct irest as [imin | imin].
      SSCase "index min = 1".
        rewrite imin in ntheq. rewrite seq in ntheq. simpl in ntheq.
        inversion ntheq as [mrx]. destruct istx as [t mtx]. rewrite mtx in mrx.
        inversion mrx.
      SSCase "index min = 2".
        rewrite imin in ntheq. rewrite seq in ntheq. simpl in ntheq.
        inversion ntheq as [mtx]. symmetry in mtx. apply node_smsg_msg_tx in mtx.
        rewrite mtx in minst.
        inversion minst; subst.
        destruct (strand_node (strand min) 1) as [n1 [n1s n1i]].
          rewrite seq. simpl; auto.  
        assert (n1 << min) as n1pre. constructor. constructor 2.
          constructor. auto. omega.
        apply minpred in n1pre.
        assert (nth_error (strand n1) (index n1) = Some (smsg n1)) as ntheq2. 
          apply node_indexing_equiv.        
        rewrite n1i in ntheq2. rewrite seq in n1s. rewrite n1s in ntheq2. 
        simpl in ntheq2. inversion ntheq2 as [mrx]. symmetry in mrx.
        apply node_smsg_msg_rx in mrx. rewrite mrx in n1pre.
        contradiction.
    SCase "D".
      assert (length (strand min) = 3) as len. rewrite seq. auto.
      assert ((index min) = 0 
              \/ (index min) = 1 
              \/ (index min) = 2) as imin. remember (index_len_node min); omega.
      assert (nth_error (strand min) (index min) = Some (smsg min)) as ntheq. 
        apply node_indexing_equiv. 
      destruct imin as [imin | irest].
      SSCase "index min = 0".
        rewrite imin in ntheq. rewrite seq in ntheq. simpl in ntheq.
        inversion ntheq as [mrx]. symmetry in mrx.
        destruct istx as [t mtx]. rewrite mtx in mrx. inversion mrx.
      destruct irest as [imin | imin].
      SSCase "index min = 1".
        rewrite imin in ntheq. rewrite seq in ntheq. simpl in ntheq.
        inversion ntheq as [mrx]. symmetry in mrx.
        destruct istx as [t mtx]. rewrite mtx in mrx. inversion mrx.
      SSCase "index min = 2".
        destruct (strand_node (strand min) 1) as [n1 [n1s n1i]].
          rewrite seq. simpl; auto.  
        assert (n1 << min) as n1pre. constructor. constructor 2.
          constructor. auto. omega.
        apply minpred in n1pre.
        assert (nth_error (strand n1) (index n1) = Some (smsg n1)) as ntheq2. 
          apply node_indexing_equiv.        
        rewrite n1s in ntheq2. rewrite seq in ntheq2. rewrite n1i in ntheq2. 
        simpl in ntheq2. inversion ntheq2 as [mrx]. symmetry in mrx.
        apply node_smsg_msg_rx in mrx. rewrite mrx in n1pre.
        rewrite imin in ntheq. rewrite seq in ntheq. simpl in ntheq.
        inversion ntheq as [mtx]. symmetry in mtx.
        apply node_smsg_msg_tx in mtx. rewrite mtx in minst.
        apply n1pre. constructor. exact minst.
Qed.

End SimpleSpaces.