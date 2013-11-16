
Require Import Logic List ListSet Arith Peano_dec Omega Ensembles.
Require Import Finite_sets_facts Finite_sets Relation_Definitions.
Require Import Relation_Operators.
Require Import strictorder set_rep_equiv util.
Require Import finite_set_builder strandlib.
Require Import LibTactics.


Require Import strandspace.

Section NSLSpace.

Open Scope list_scope.
Import ListNotations.
Open Scope ss_scope.

Hypothesis PModel : PenetratorModel = DolevYao.
Variable A B Na Nb : Text.
  Hypothesis neqANa : A <> Na.
  Hypothesis neqANb : A <> Nb.
  Hypothesis neqBNa : B <> Na.
  Hypothesis neqBNb : B <> Nb.
Variable Ka Kb : Key.
  Hypothesis keyinj : Ka = Kb -> A = B.

Hypothesis NSLProtocol : 
  Protocol = [[(+ {(!Na) * (!A)}^[Kb]) ; 
               (- {(!Na) * (!Nb) * (!B)}^[Ka]) ;
               (+ {(!Nb)}^[Kb])] ; 
              [(- {(!Na) * (!A)}^[Kb]) ; 
               (+ {(!Na) * (!Nb) * (!B)}^[Ka]) ;
               (- {(!Nb)}^[Kb])]].

Definition s : Strand :=  [(- {(!Na) * (!A)}^[Kb]) ; 
               (+ {(!Na) * (!Nb) * (!B)}^[Ka]) ;
               (- {(!Nb)}^[Kb])].


(* Proposition 5.2
   Suppose:
   1) The SS is an NSL space, C is a bundle in it,
      and s is a responder strand
      Resp[A, B, Na, Nb] with C-height 3. 
   2) inv(Ka) is not in Kp
   3) Na <> Nb and Nb is uniquely originating in the space. 
   THEN
    C contains an initiator's strand t (Init[A, B, Na, Nb] with 
    C-height 3. *)

Lemma s_regular : RegularStrand s.
Proof.
  unfold RegularStrand. rewrite NSLProtocol.
  unfold s. right. left. reflexivity.
Qed.

Lemma s_height : length s = 3.
Proof.
  simpl. auto.
Qed.

Variable n0 : Node.
Hypothesis n0_def : strand n0 = s /\
                    index n0 = 1.
Variable v0 : Msg.
Hypothesis v0_def : msg n0 = v0.

Lemma v0_val : v0 = {(!Na) * (!Nb) * (!B)}^[Ka].
Proof.
  destruct n0_def.
  forwards*: (nth_node n0 s 1).
  forwards: (node_smsg_msg_tx n0). eauto.
  congruence.
Qed.

Variable n3 : Node.
Hypothesis n3_def : strand n3 = s /\
                    index n3 = 2.
Variable v3 : Msg.
Hypothesis v3_def : msg n3 = v3.

Lemma v3_val : v3 = {(!Nb)}^[Kb].
Proof.
  destruct n3_def.
  forwards*: (nth_node n3 s 2).
  forwards: (node_smsg_msg_rx n3). eauto.
  congruence.
Qed.  

(* Lemma 5.3 Nb originates at n0 *)
Lemma Nb_origin : Origin (!Nb) n0.
Proof.
  (* BOOKMARK *)
  Admitted.


End NSLSpace.
