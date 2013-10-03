Require Import Relations Omega Finite_sets List ListSet util.
Require Import Relations_1.

(* List Notations *)
Notation " [ ] " := nil.
Notation " [ x ] " := (cons x nil).
Notation " [ x , .. , y ] " := (cons x .. (cons y nil) ..).
Notation "x :: l" := (cons x l) (at level 60, right associativity). 


Section clos_trans_dec.

Variable X : Type.
 Hypothesis Xeq_dec : forall (x y:X), {x = y} + {x <> y}.

Variable R : relation X.
 Hypothesis Rdec : forall (x y:X), {R x y} + {~R x y}.

Definition AdjList : Type := (prod X (set X)).
Definition Map : Type := set AdjList.

Lemma eq_Xset_dec : forall (x y: set X),
{x = y} + {x <> y}.
Proof.
  decide equality.
Qed.

Lemma eq_AdjList_dec : forall (x y: (X * set X)),
{x = y} + {x <> y}.
Proof.
  decide equality.
  decide equality.
Qed.

Fixpoint reachable_from_set (x:X) (s:set X) : set X :=
match s with
| nil => nil
| h :: srest =>
  if Rdec x h
  then set_add Xeq_dec h (reachable_from_set x srest)
  else reachable_from_set x srest
end.

Lemma reachable_imp_in_set : forall s x y,
 set_In y (reachable_from_set x s) ->
set_In y s.
Proof.
  intros s.
  induction s as [| a s']; intros x y.
  Case "s = []".
    intros yIn. simpl in yIn. inversion yIn.
  Case "s = a :: s'".
    intros yIn.
    destruct (Xeq_dec y a) as [yaeq | yaneq].
    SCase "a = y".
      subst a. left. reflexivity.
    SCase "a <> y".
      simpl in yIn.
      destruct (Rdec x a) as [Rxa | nRxa].
      SSCase "Rxa".
        eapply set_add_elim in yIn.
        destruct yIn. contradiction.
        right. apply (IHs' x y H).
      SSCase "~Rxa".
        right. apply (IHs' x y yIn).
Qed.

Lemma reachable_set_correct : forall x y s,
set_In y s ->
(R x y <->
set_In y (reachable_from_set x s)).
Proof.
  intros x y s yIn.
  split.
  Case "R -> In".
    intros Rxy.
    induction s as [| a s'].
    SCase "s = []".
      inversion yIn.
    SCase "s = a :: s'".
      simpl.
      destruct (Rdec x a) as [Rxa | Rxa].
      SSCase "R x a".
        destruct (Xeq_dec a y) as [yaeq | yaneq].
        SSSCase "y = a".
          subst a. apply set_add_intro2. reflexivity.
        SSSCase "y <> a".
          inversion yIn. contradiction.
          apply set_add_intro1. apply IHs'. exact H.
     SSCase "~R x a".
       destruct (Xeq_dec a y) as [yaeq | yaneq].
       SSSCase "y = a".
         subst a. contradiction.
       SSSCase "y <> a".
         destruct yIn. contradiction.
         apply (IHs' H).
  Case "In -> R".
    induction s as [| a s'].
    SCase "s = []".
      inversion yIn.
    SCase "s = a :: s'".
      intros yInreachable.
      destruct (Xeq_dec y a) as [yaeq | yaneq].
      SSCase "a = y".
        subst a. simpl in yInreachable.
        destruct (Rdec x y) as [Rxy | nRxy].
        SSSCase "R x y". exact Rxy.
        SSSCase "~R x y".
          destruct yIn.
          assert (set_In y s') as yIns'.
            eapply reachable_imp_in_set. exact yInreachable.
          apply IHs'. exact yIns'. exact yInreachable.
          apply IHs'. exact H. exact yInreachable.          
      SSCase "a <> y".
        simpl in yInreachable.
        destruct (Rdec x a) as [Rxa | nRxa].
        SSSCase "R x a".
          apply set_add_elim in yInreachable.
          destruct yInreachable. contradiction.
          destruct yIn. symmetry in H0. contradiction.
          apply (IHs' H0 H).
        SSSCase "~R x a".
          destruct yIn. symmetry in H. contradiction.
          apply (IHs' H yInreachable).
Qed.
        
Fixpoint build_reachable_Map 
         (indices:set X)
         (members:set X) : Map :=
match indices with
| nil => nil
| x :: irest => 
  set_add eq_AdjList_dec 
          (pair x (reachable_from_set x members))
          (build_reachable_Map irest members)
end.

(* To Prove: reachable Map has a AdjList for every node,
   which has the reachable_from_set_contains_all_property *)

Fixpoint get_rel_list (x:X) (adj:Map) : (set X) :=
match adj with
| nil => nil
| a :: rest =>
  if Xeq_dec x (fst a)
  then (snd a)
  else get_rel_list x rest
end.


Definition extend_reachable_list (x:X) (xalist yalist: set X) :=
if set_mem Xeq_dec x yalist
then set_union Xeq_dec xalist yalist
else yalist.

Fixpoint trans_extend_single (x:X) (adj:Map) : Map :=
match adj with
| nil => nil
| alist :: rest =>
  set_add eq_AdjList_dec 
          (pair (fst alist) 
                (extend_reachable_list 
                   x 
                   (get_rel_list x adj) 
                   (snd alist)))
          (trans_extend_single x rest)
end.

Fixpoint trans_extend_Map (nodes: set X) (adj: Map) : Map :=
match nodes with
| nil => adj
| x :: nrest => 
  trans_extend_Map nrest (trans_extend_single x adj)
end.

Fixpoint build_trans_map (nodes: set X) : Map :=
(trans_extend_Map nodes (build_reachable_Map nodes nodes)).


Theorem trans_map_correct : forall x y s,
set_In y s ->
(clos_trans X R x y <->
set_In y  (get_rel_list x (build_trans_map s))).


End clos_trans_dec.