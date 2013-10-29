
Require Import Ensembles Finite_sets Finite_sets_facts.
Require Import List ListSet.
Require Import util.

Open Scope list_scope.

Section set_rep.


Variable X : Type.
 Hypothesis Xeq_dec : forall (x y:X), {x = y} + {x <> y}.

Definition InSet : forall U : Type, Ensemble U -> U -> Prop := Ensembles.In.

Lemma set_imp_ensemble : forall (s: set X),
NoDup s ->
exists E:Ensemble X, (forall x, set_In x s <-> InSet X E x) /\ 
  exists n, (length s = n) /\ (cardinal X E n).
Proof.
  intros s nodup. generalize dependent nodup.
  induction s; intros nodup.
  Case "[]".
    exists (Empty_set X).
    split.
    SCase "set_In <-> InSet".
      intros x.
      split. intros setin. inversion setin.
      intros  inset. inversion inset.
   SCase "length = size".
     exists 0. 
     split. simpl. reflexivity.
     constructor.
 Case "a :: s".    
   destruct IHs as [E [Hin Hcard]].
   inversion nodup; subst. exact H2.
   exists (Add X E a).
   split.
    SCase "set_In <-> InSet".
      intros x.
      split.
      SSCase "->".
        destruct (Xeq_dec a x) as [eqax | neqax].
        intros setIn. subst x.
        apply Add_intro2.
        intros setIn.
        destruct (Hin x) as [setInx InSetx].
        inversion setIn. assert False as F. apply neqax. exact H. inversion F.
        apply setInx in H. eapply Add_intro1 in H. exact H.
      SSCase "<-".
        intros inSet.
        destruct (Xeq_dec a x) as [eqax | neqax].
        subst. simpl. left. reflexivity. 
        inversion inSet; subst.
        apply Hin in H.
        simpl. right. exact H.
        inversion H.
        assert False as F. apply neqax. exact H0. inversion F.
   SCase "length = size".
     destruct (set_In_dec Xeq_dec a s) as [ins | nins].
     inversion nodup; subst.
     assert False as F. apply H1. exact ins. inversion F.
     destruct Hcard as [n [len card]].
     exists (S n).
     split. simpl. auto.
     apply card_add. exact card.
     intros contra.
     destruct (Hin a) as [setIna InSeta].
     apply InSeta in contra.
     apply nins. exact contra.
Qed.

Lemma set_add_Sn : forall (s: set X) (x: X) (n:nat),
~ set_In x s ->
length s = n ->
length (set_add Xeq_dec x s) = S n.
Proof.
  intros s.
  induction s.
  Case "[]".
    intros x n notIn len.
    simpl. simpl in len.
    auto.
  Case "a :: s".
    intros x n notIn len.
    simpl. destruct (Xeq_dec x a).
    subst x.
    assert False as F. apply notIn. simpl. left. reflexivity. inversion F.
    simpl. rewrite <- len. simpl. destruct n. inversion len.
    assert (~ set_In x s) as xnotIns. 
      intros contra. apply notIn. simpl. right. exact contra.
    assert (length s = n) as slen. auto.      
    rewrite (IHs x n xnotIns slen).
    subst. 
    reflexivity.
Qed.

Lemma set_add_nodup : forall x s,
NoDup (x :: s) ->
NoDup (set_add Xeq_dec x s).
Proof.
  intros x s. generalize dependent x.
  induction s.
  Case "[]".
    intros x xnotIn.
    simpl. exact xnotIn.
  Case "a :: s".
    intros x nodup.
    simpl.
    destruct (Xeq_dec x a) as [eqxa | neqxa].
    subst. inversion nodup. assert False as F. apply H1. simpl. left. reflexivity. inversion F.
    inversion nodup; subst. inversion H2; subst.
    assert (~ In x s) as notxIns.
      intros contra. apply H1. simpl. right. exact contra.
    assert (NoDup (x :: s)) as xsnodup.
      constructor. exact notxIns. exact H4.
    constructor.
    intros contra.
    apply set_add_elim2 in contra.
    apply H3. exact contra.
    intros contra2. subst. inversion nodup. apply H5. simpl. left. reflexivity.
    apply IHs. exact xsnodup.
Qed.

Lemma ensemble_imp_set : forall (E: Ensemble X),
Finite X E ->
exists s: set X, (forall x, set_In x s <-> InSet X E x) /\
  NoDup s /\
  exists n, (length s = n) /\ (cardinal X E n).
Proof.
  intros E fin.
  induction fin.
  Case "Empty_set".
    exists nil.
    split.
    intros x. 
    split. intros setIn. inversion setIn.
    intros inSetx. inversion inSetx.
    split. constructor.
    exists 0. split. simpl. reflexivity.
    apply card_empty.
  Case "Add x".
    destruct IHfin as [s [Hin [Hnodup Hcard]]].
    exists (set_add Xeq_dec x s).
    split.
     SCase "set_In <-> InSet".
       intros a.
       split.
       SSCase "->".
         intros setInx.
         apply set_add_elim in setInx.
         destruct setInx as [eqax | aIns].
         subst a. apply Add_intro2. 
         apply Add_intro1. apply Hin. exact aIns.
       SSCase "<-".
         intros InSeta.
         inversion InSeta; subst.
         apply set_add_intro.
         right.
         destruct (Hin a) as [HsetIn HInSet].
         apply HInSet.
         exact H0.
         inversion H0. subst.
         apply set_add_intro. left. reflexivity.
       split.
     SCase "NoDup s".
       assert (~ set_In x s) as xnotIns.
         destruct (set_In_dec Xeq_dec x s).
         apply Hin in s0. assert False as F. apply H. exact s0. inversion F.
         exact n.
         assert (NoDup (x :: s)) as xsnodup.
           constructor. exact xnotIns. exact Hnodup.
           apply set_add_nodup. exact xsnodup.
     SCase "length /\ card".
       destruct Hcard as [n [slen Acard]].
       destruct (set_In_dec Xeq_dec x s).
       SSCase "x in s".
         destruct (Hin x) as [HsetIn HInSet].
         assert False as F. apply H. apply HsetIn.
         exact s0. inversion F.
       SSCase "x not in s".
         exists (S n).
         split.
         apply set_add_Sn. exact n0. exact slen.
         apply card_add. exact Acard. exact H.
Qed.


End set_rep.