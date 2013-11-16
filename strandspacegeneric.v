Require Import Logic List ListSet Arith Peano_dec Omega.
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
(forall n, set_In n (Nodes B) -> ~ (#k) <st msg(n)).
Proof with eauto.
  intros B k notInKp noOrigin n nInN st.
  remember B as bundle.
  destruct bundle as [N E ndN ndE valE predIncl Txincl uniqtx acyc]; simpl in *.
  assert (N = Nodes B) as NB. subst B. simpl; reflexivity.
  clear Heqbundle.
  assert (forall x : Node, {(#k) <st msg x} + {~ (#k) <st msg x})
         as Pdec.
    intros x. apply st_dec.
  remember (fun n => if Pdec n then true else false) as f.
  destruct (ex_filter_set Node (fun x => (#k) <st msg x) Pdec (Nodes B)) 
    as [N' [N'incl N'P]].
  destruct N' as [| x N'].
   Case "Empty_set". 
    forwards: (N'P n). apply H. split. congruence. auto. 
  Case "non-empty".
    edestruct (bundle_subset_minimal B) as [min Hmin]. 
      subst N. eauto. intros contra. tryfalse.
    forwards: (min_origin B (x :: N') min (#k)).
    intros m [mIn mst]. rewrite <- NB in *.
    destruct (N'P m) as [inImpst stImpIn].
    forwards: (stImpIn). auto. auto.
    split. auto. apply N'P. auto. auto.
    forwards: origin_tx. eassumption. 
    forwards: origin_st. eassumption.
    forwards: (noOrigin). eassumption. forwards: (penetrator_behaviour).
    eassumption.
    rewrite PModel in *.
    (* Case analysis on DolevYao variants *)
    edestruct (DolevYao_disjunction (strand min)) 
      as [[g [tunk seq]] | 
          [[g seq] | 
          [[g seq] | 
          [[g [h seq]] | 
          [[g [h seq]] | 
          [[k' [kunk seq]] | 
          [[h [k' seq]] | 
          [k' [k'' [g [inv seq]]]]]]]]]]]. auto.
    SCase "M & F".
      rewrite (particular_min_msg seq) in *... eauto.
    SCase "T".
      forwards: no_origin_after_rx. eauto.
      edestruct (node_strand_3height_opts) as [rxg | txg]. eauto.
      forwards: tx_rx_false... forwards: node_smsg_msg_tx...
      forwards: (equiv_disjunct). eassumption.
      edestruct (strand_prev_imp_succ [] min (-g) [(+g); (+g)]) 
        as [pred [plt psmsg]]. auto. auto. eauto.
      forwards: (origin_nosucc_st). eassumption. eassumption.
      erewrite (node_smsg_msg_tx min g) in *.
      rewrite (node_smsg_msg_rx pred g) in *. contradiction.
      auto. auto. auto. auto.
    SCase "C".
      forwards*: no_origin_after_rx.
      edestruct (node_strand_3height_opts) as [rxg | [rxh | txgh]]... 
      edestruct (strand_prev_imp_succ [] min (-g) [(-h); (+g * h)]) 
        as [pred [plt psmsg]]...
      forwards*: (origin_nosucc_st). 
      edestruct (strand_prev_imp_succ [(-g)] min (-h) [(+g * h)]) 
        as [pred2 [p2lt p2smsg]]...
      forwards*: (origin_nosucc_st). 
      rewrite (node_smsg_msg_tx min (g * h)) in *.
      rewrite (node_smsg_msg_rx pred g) in *.
      rewrite (node_smsg_msg_rx pred2 h) in *.
      apply (no_st_l_r g h (#k))... auto. auto. auto.
    SCase "S".
      forwards*: no_origin_after_rx.
      edestruct (node_strand_3height_opts) as [rxg | [rxh | txgh]]...
      edestruct (strand_prev_imp_succ [] min (-g * h) [(+g); (+h)]) 
        as [pred [plt psmsg]]...
      forwards*: (origin_nosucc_st). 
      rewrite (node_smsg_msg_rx pred (g * h)) in *.
      rewrite (node_smsg_msg_tx min (g)) in *... auto.
      edestruct (strand_prev_imp_succ [] min (-g * h) [(+g); (+h)]) 
        as [pred [plt psmsg]]...
      forwards*: (origin_nosucc_st). 
      rewrite (node_smsg_msg_rx pred (g * h)) in *.
      rewrite (node_smsg_msg_tx min (h)) in *... auto.
    SCase "K".
      rewrite (particular_min_msg seq) in *. simpl in *.
      forwards*: (key_st_key k k'). subst. contradiction.
    SCase "E".
      edestruct (node_strand_3height_opts) as [rxk | [rxh | txhk]]...
      edestruct (strand_prev_imp_succ [(-(#k'))] min (-h) [(+{h}^[k'])]) 
        as [pred [plt psmsg]]...
      forwards*: (origin_nosucc_st). 
      rewrite (node_smsg_msg_rx pred (h)) in *.
      rewrite (node_smsg_msg_tx min {h}^[k']) in *.
      forwards*: (no_encr_st (#k) h). auto. auto.
    SCase "D".
      edestruct (node_strand_3height_opts) as [rxk | [rxh | txhk]]...
      edestruct (strand_prev_imp_succ [(-(#k'))] 
                                      min  
                                      (-{g }^[ k'']) 
                                      [(+g)]) 
        as [pred [plt psmsg]]. auto. eauto. eauto.
      forwards*: (origin_nosucc_st). 
      rewrite (node_smsg_msg_rx pred ({g}^[k''])) in *.
      rewrite (node_smsg_msg_tx min g) in *...
      auto.
Qed.

End SimpleSpaces.