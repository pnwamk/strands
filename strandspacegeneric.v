
Require Import Logic List ListSet Arith Peano_dec Omega Ensembles.
Require Import Coq.Sets.Constructive_sets.
Require Import Finite_sets_facts Finite_sets Relation_Definitions.
Require Import Relation_Operators.
Require Import strictorder set_rep_equiv util.
Require Import finite_set_builder.
Require Import LibTactics.

Require Import strandspace strandlib.

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
Proof with eauto.
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
    as [N' [inclN' [N'memP PmemN']]].
  forwards*: (Finite_downward_closed Node N finN N').
  destruct H as [| N' fin x].
  Case "Empty_set". 
    forwards: PmemN'. eauto. contradiction.
  Case "non-empty".
    edestruct (bundle_subset_minimal B) as [min Hmin]. 
      subst N. eauto. auto.
    forwards: (min_origin B (Add Node N' x)). 
    subst N. eauto. subst N... eauto.
    forwards*: origin_tx. forwards*: origin_st.
    forwards*: (noOrigin). forwards*: (penetrator_behaviour).
    rewrite PModel in *.
    (* Case analysis on DolevYao variants *)
    edestruct (DolevYao_disjunction (strand min)) 
      as [[g [tunk seq]] | 
          [[g seq] | 
          [[g seq] | 
          [[g [h seq]] | 
          [[g [h seq]] | 
          [[k' [kunk seq]] | 
          [[k' seq] | 
          [h [k' [k'' [inv seq]]]]]]]]]]]...
    SCase "M & F".
      rewrite (particular_min_msg seq) in *...
    SCase "T".
      forwards*: no_origin_after_rx.
      edestruct (node_strand_3height_opts) as [rxg | txg]. eauto.
      forwards*: tx_rx_false; forwards*: node_smsg_msg_tx.
      forwards*: equiv_disjunct.
      edestruct (strand_prev_imp_pred [] min (-g) [(+g); (+g)]) 
        as [pred [plt psmsg]]...
      forwards*: origin_nopred_st. erewrite (node_smsg_msg_tx min g) in *.
      rewrite (node_smsg_msg_rx pred g) in *. contradiction.
      auto. auto.
    SCase "C".
      forwards*: no_origin_after_rx.
      edestruct (node_strand_3height_opts) as [rxg | [rxh | txgh]]... 
      edestruct (strand_prev_imp_pred [] min (-g) [(-h); (+g * h)]) 
        as [pred [plt psmsg]]...
      forwards*: (origin_nopred_st). 
      edestruct (strand_prev_imp_pred [(-g)] min (-h) [(+g * h)]) 
        as [pred2 [p2lt p2smsg]]...
      forwards*: (origin_nopred_st). 
      rewrite (node_smsg_msg_tx min (g * h)) in *.
      rewrite (node_smsg_msg_rx pred g) in *.
      rewrite (node_smsg_msg_rx pred2 h) in *.
      apply (no_st_l_r g h (#k))... intros contra. tryfalse. 
      auto. auto. auto.
    SCase "S". (* BOOKMARK *)
      forwards*: no_origin_after_rx.
      edestruct (node_strand_3height_opts) as [rxg | [rxh | txgh]]. eauto.
      forwards*: tx_rx_false; forwards*: node_smsg_msg_tx.
      edestruct (strand_prev_imp_pred [] min (-g * h) [(+g); (+h)]) 
        as [pred [plt psmsg]]. 
        simpl. auto. eauto.
      forwards*: (origin_nopred_st). 
      rewrite (node_smsg_msg_rx pred (g * h)) in *.
      rewrite (node_smsg_msg_tx min (g)) in *. eauto. eauto.
      auto.
      edestruct (strand_prev_imp_pred [] min (-g * h) [(+g); (+h)]) 
        as [pred [plt psmsg]]. 
        simpl. auto. eauto.
      forwards*: (origin_nopred_st). 
      rewrite (node_smsg_msg_rx pred (g * h)) in *.
      rewrite (node_smsg_msg_tx min (h)) in *. eauto. eauto.
      auto.
    SCase "K".
      rewrite (particular_min_msg seq) in *. simpl in *.
      forwards*: (key_st_key k k'). subst. contradiction.
    SCase "E".
      edestruct (node_strand_3height_opts) as [rxk | [rxh | txhk]]. eauto.
      forwards*: tx_rx_false; forwards*: node_smsg_msg_tx.
      forwards*: tx_rx_false; forwards*: node_smsg_msg_tx.
      edestruct (strand_prev_imp_pred [(-(#k'))] min (-h) [(+{h}^[k'])]) 
        as [pred [plt psmsg]]. simpl. auto. eauto.
      forwards*: (origin_nopred_st). 
      rewrite (node_smsg_msg_rx pred (h)) in *.
      rewrite (node_smsg_msg_tx min {h}^[k']) in *.
      forwards*: (no_encr_st (#k) h). intros neq.
      inversion neq. eauto. eauto.
    SCase "D".
      edestruct (node_strand_3height_opts) as [rxk | [rxh | txhk]]. eauto.
      forwards*: tx_rx_false; forwards*: node_smsg_msg_tx.
      forwards*: tx_rx_false; forwards*: node_smsg_msg_tx.
      edestruct (strand_prev_imp_pred [(-(#k''))] 
                                      min  
                                      (-{h }^[ k']) 
                                      [(+h)]) 
        as [pred [plt psmsg]]. simpl. auto. eauto.
      forwards*: (origin_nopred_st). 
      rewrite (node_smsg_msg_rx pred ({h}^[k'])) in *.
      rewrite (node_smsg_msg_tx min h) in *.
      eauto. auto. auto.
Qed.

End SimpleSpaces.