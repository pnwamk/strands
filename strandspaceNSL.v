
Require Import Logic List ListSet Arith Peano_dec Omega Ensembles.
Require Import Finite_sets_facts Finite_sets Relation_Definitions.
Require Import Relation_Operators.
Require Import strictorder set_rep_equiv util.
Require Import finite_set_builder.

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
Definition s : Strand :=  [(- {(!Na) * (!A)}^[Kb]) ; 
               (+ {(!Na) * (!Nb) * (!B)}^[Ka]) ;
               (- {(!Nb)}^[Kb])].

Lemma s_regular : RegularStrand s.
Proof.
  unfold RegularStrand. rewrite NSLProtocol.
  unfold s. right. left. reflexivity.
Qed.
(*
Lemma ex_n0 : 
  exists n0, (strand n0) = s /\ (index n0) = 2.
Proof.
  *)

(* Lemma 5.3 Nb originates at n0 *)




End NSLSpace.
