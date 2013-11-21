Require Import Logic List ListSet Arith Peano_dec Omega Ensembles.
Require Import Finite_sets_facts Finite_sets Relation_Definitions.
Require Import Relation_Operators.
Require Import strictorder set_rep_equiv util.
Require Import finite_set_builder strandlib.
Require Import LibTactics.

Require Import strandspace.

Module NSLSpace.

Open Scope list_scope.
Import ListNotations.
Open Scope ss_scope.

(* Names and Nonces *)
Variable A B Na Nb : Text.
  Hypothesis neqANa : A <> Na.
  Hypothesis neqANb : A <> Nb.
  Hypothesis neqBNa : B <> Na.
  Hypothesis neqBNb : B <> Nb.
(* "Public" and "Private" keys *)
Variable Ka Kb Ka' Kb' : Key.
  Hypothesis keyinj : Ka = Kb -> A = B.
  Hypothesis Ka_inv : Inv Ka Ka'.
  Hypothesis Kb_inv : Inv Kb Kb'.

(* Self-communication in this protocol is nonsensical *)
Hypothesis neqAB : A <> B. 

Lemma neqKaKb : Ka <> Kb.
Proof.
  intros contra. 
  apply keyinj in contra.
  apply neqAB. auto.
Qed.

Definition NSLInitiator : Strand :=  
  [(+ {(!Na) * (!A)}^[Kb]) ; 
   (- {(!Na) * (!Nb) * (!B)}^[Ka]) ;
   (+ {(!Nb)}^[Kb])].

Definition NSLResponder : Strand :=  
  [(- {(!Na) * (!A)}^[Kb]) ; 
   (+ {(!Na) * (!Nb) * (!B)}^[Ka]) ;
   (- {(!Nb)}^[Kb])].

Hypothesis NSLProtocol : 
  Protocol = [NSLInitiator ; NSLResponder].

End NSLSpace.

Export NSLSpace.