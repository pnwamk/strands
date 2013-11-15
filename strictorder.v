Require Import Relations Omega Ensembles Finite_sets Finite_sets_facts.
Require Import List ListSet.
Require Import util set_rep_equiv.

Require Import ListSet List Relations_1.
Require Import LibTactics.

Section strict_order.

Open Scope list_scope.

Variable X : Type.
 Hypothesis Xeq_dec : forall x y : X, {x=y}+{x<>y}.
Variable R : Relation X.

 Definition Irreflexive (X:Type) (R:Relation X) : Prop := forall x:X, ~R x x.
  Inductive StrictOrder (X:Type) (R:Relation X) : Prop :=
       Definition_of_order :
         Irreflexive X R -> Transitive X R -> StrictOrder X R.

 Hypothesis Rdec : forall (x y:X), {R x y} + {~R x y}.
 Hypothesis Rso : StrictOrder X R.

Fixpoint lt_set (pivot:X) (s:set X) : (set X) :=
match s with
| nil => nil
| x :: srest =>
  if Rdec x pivot
  then set_add Xeq_dec x (lt_set pivot srest)
  else lt_set pivot srest
end.

Lemma in_lt_imp_in_set : forall x y s,
set_In y (lt_set x s) ->
set_In y s.
Proof.
  intros x y s.
  induction s as [|h s'].
  Case "s = []".
    intros yIn. inversion yIn.
  Case "s = h :: s'".
    intros yIn.
    destruct (Xeq_dec y h) as [eqyh | neqyh].
    SCase "y = h".
      subst h. left. reflexivity.
    SCase "y <> h".
      right. apply IHs'.
      simpl in yIn.
      destruct (Rdec h x) as [Rhx | nRhx].
      SSCase "Rhx".
        apply set_add_elim in yIn.
        destruct yIn.
          contradiction.
          exact H.
      SSCase "~Rhx".
        exact yIn.
Qed.

Lemma lt_set_rel_equiv : forall x y s,
set_In y s ->
(R y x <-> set_In y (lt_set x s)).
Proof.
  intros x y s yIn.
  split.
  Case "Ryx -> In".
    intros Ryx.
    induction s as [| h s'].
      SCase "s = []".
        inversion yIn.
      SCase "s = h :: s'".
        destruct (Xeq_dec h y) as [eqyh | neqyh].
        SSCase "y = h".
          subst h. simpl.
          destruct (Rdec y x) as [yRyx | nRyx].
            apply set_add_intro2. reflexivity.
            contradiction.
        SSCase " y <> h".
          simpl. 
          destruct (Rdec h x) as [yRhx | nRhx].
            apply set_add_intro1. apply IHs'. 
            destruct yIn. 
              contradiction. exact H.
            apply IHs'. 
            destruct yIn.
              contradiction. exact H.
  Case "Ryx <- In".
    intros yInlt.
    induction s as [| h s'].
    SCase "s = []".
      inversion yIn.
    SCase "s = [h s']".
      destruct (Xeq_dec y h) as [eqyh | neqyh].
      SSCase "y = x".
        subst h. simpl in yInlt.
        destruct (Rdec y x) as [Ryx | nRyx].
          exact Ryx.
          apply IHs'.
          eapply in_lt_imp_in_set. exact yInlt. 
          exact yInlt.
      SSCase "y <> h".
        destruct yIn.
          symmetry in H. contradiction.
          simpl in yInlt.
          destruct (Rdec h x) as [Rhx | nRhx].
            apply set_add_elim in yInlt.
            destruct yInlt.
              contradiction.
              apply IHs'. exact H. exact H0.
              apply IHs'. exact H. exact yInlt.
Qed.

Fixpoint gt_set (pivot:X) (s:set X) : (set X) :=
match s with
| nil => nil
| x :: srest =>
  if Rdec pivot x
  then set_add Xeq_dec x (gt_set pivot srest)
  else gt_set pivot srest
end.

Lemma in_gt_imp_in_set : forall x y s,
set_In y (gt_set x s) ->
set_In y s.
Proof.
  intros x y s.
  induction s as [|h s'].
  Case "s = []".
    intros yIn. inversion yIn.
  Case "s = h :: s'".
    intros yIn.
    destruct (Xeq_dec y h) as [eqyh | neqyh].
    SCase "y = h".
      subst h. left. reflexivity.
    SCase "y <> h".
      right. apply IHs'.
      simpl in yIn.
      destruct (Rdec x h) as [Rxh | nRxh].
      SSCase "Rxh".
        apply set_add_elim in yIn.
        destruct yIn.
          contradiction.
          exact H.
      SSCase "~Rxh".
        exact yIn.
Qed.

Lemma gt_set_rel_equiv : forall x y s,
set_In y s ->
(R x y <-> set_In y (gt_set x s)).
Proof.
  intros x y s yIn.
  split.
  Case "Rxy -> In".
    intros Rxy.
    induction s as [| h s'].
      SCase "s = []".
        inversion yIn.
      SCase "s = h :: s'".
        destruct (Xeq_dec h y) as [eqyh | neqyh].
        SSCase "y = h".
          subst h. simpl.
          destruct (Rdec x y) as [yRxy | nRxy].
            apply set_add_intro2. reflexivity.
            contradiction.
        SSCase " y <> h".
          simpl. 
          destruct (Rdec x h) as [yRxh | nRxh].
            apply set_add_intro1. apply IHs'. 
            destruct yIn. 
              contradiction. exact H.
            apply IHs'. 
            destruct yIn.
              contradiction. exact H.
  Case "Rxy <- In".
    intros yInlt.
    induction s as [| h s'].
    SCase "s = []".
      inversion yIn.
    SCase "s = [h s']".
      destruct (Xeq_dec y h) as [eqyh | neqyh].
      SSCase "y = h".
        subst h. simpl in yInlt.
        destruct (Rdec x y) as [Rxy | nRxy].
          exact Rxy.
          apply IHs'.
          eapply in_gt_imp_in_set. exact yInlt. exact yInlt.
      SSCase "y <> h".
        destruct yIn.
          symmetry in H. contradiction.
          simpl in yInlt.
          destruct (Rdec x h) as [Rxh | nRxh].
            apply set_add_elim in yInlt.
            destruct yInlt.
              contradiction.
              apply IHs'. exact H. exact H0.
              apply IHs'. exact H. exact yInlt.
Qed.

Fixpoint norel_set (pivot:X) (s:set X) : (set X) :=
match s with
| nil => nil
| x :: srest =>
  if Rdec x pivot
  then norel_set pivot srest
  else if Rdec pivot x
       then norel_set pivot srest
       else set_add Xeq_dec x (norel_set pivot srest)
end.

Lemma in_norel_imp_in_set : forall x y s,
set_In y (norel_set x s) ->
set_In y s.
Proof.
  intros x y s.
  induction s as [|h s'].
  Case "s = []".
    intros yIn. inversion yIn.
  Case "s = h :: s'".
    intros yIn.
    destruct (Xeq_dec y h) as [eqyh | neqyh].
    SCase "y = h".
      subst h. left. reflexivity.
    SCase "y <> h".
      right. apply IHs'.
      simpl in yIn.
      destruct (Rdec h x) as [Rhx | nRhx].
      SSCase "Rhx".
        exact yIn.
        destruct (Rdec x h) as [Rxh | nRxh].
        SSSCase "Rxh".
          exact yIn.
        SSCase "~Rxh".
          apply set_add_elim in yIn.
          destruct yIn.
            contradiction.
            exact H.
Qed.

Lemma norel_set_rel_equiv : forall x y s,
set_In y s ->
((and (~R x y) (~R y x)) <-> set_In y (norel_set x s)).
Proof.
  intros x y s yIn.
  split.
  Case "no relation -> In".
    intros Rand.
    destruct Rand as [nRxy nRyx].
    induction s as [| h s'].
      SCase "s = []".
        inversion yIn.
      SCase "s = h :: s'".
        destruct (Xeq_dec h y) as [eqyh | neqyh].
        SSCase "y = h".
          subst h. simpl.
          destruct (Rdec y x) as [yRyx | nRyx2].
          SSSCase "Ryx".
            contradiction.
          SSSCase "~Ryx".
            destruct (Rdec x y) as [yRxy | nRxy2].
            SSSSCase "Rxy".
              contradiction.
            SSSSCase "~Rxy".
              apply set_add_intro2. reflexivity.
        SSCase "y <> h".
          simpl.
          destruct (Rdec h x) as [yRhx | nRhx].
          SSSCase "Rhx".
            apply IHs'.
            destruct yIn.
              contradiction. exact H.
          SSSCase "~Rhx".
            destruct (Rdec x h) as [yRxh | nRxh].
            SSSSCase "Rxh".
              apply IHs'.
              destruct yIn.
                contradiction. exact H.
              apply set_add_intro1.
              apply IHs'.
              destruct yIn.
                contradiction. exact H.
  Case "no relation <- In".
    intros yInlt.
    induction s as [| h s'].
    SCase "s = []".
      inversion yIn.
    SCase "s = [h s']".
      destruct (Xeq_dec y h) as [eqyh | neqyh].
      SSCase "y = h".
        subst h. simpl in yInlt.
        destruct (Rdec x y) as [Rxy | nRxy].
        SSSCase "Rxy".
          destruct (Rdec y x) as [Ryx | nRyx].
          SSSSCase "Ryx".
            assert (R x x) as contraR.
              eapply Rso. exact Rxy. exact Ryx.
            apply Rso in contraR. inversion contraR.
          SSSSCase "~Ryx".
            apply IHs'.
            eapply in_norel_imp_in_set. exact yInlt.
            exact yInlt.
        SSSCase "~Rxy".
          destruct (Rdec y x) as [Ryx | nRyx].
          SSSSCase "Ryx".
            apply IHs'.
            eapply in_norel_imp_in_set. exact yInlt.
            exact yInlt.
          SSSSCase "~Ryx".
            split. exact nRxy. exact nRyx.
      SSCase "y <> h".
        apply IHs'.
        destruct yIn. symmetry in H. contradiction.
        exact H.
        simpl in yInlt.
        destruct (Rdec h x) as [Rhx | nRhx].
        SSSCase "Rhx".
          exact yInlt.
        SSSCase "~Rhx".
          destruct (Rdec x h) as [Rxh | nRxh].
          SSSSCase "Rxh".
            exact yInlt.
          SSSSCase "~Rxh".
            eapply set_add_elim in yInlt.
            destruct yInlt.
              contradiction.
              exact H.
Qed.

Lemma lt_set_only : forall x y s,
set_In y (lt_set x s) ->
~set_In y (gt_set x s) /\ ~set_In y (norel_set x s).
Proof.
  intros x y s yIn.
  split.
  Case "y not in gt".
    intros contraIn.
    apply lt_set_rel_equiv in yIn.
    apply gt_set_rel_equiv in contraIn.
    assert (R y y). eapply Rso. exact yIn. exact contraIn.
    eapply Rso. exact H.
    eapply in_gt_imp_in_set. exact contraIn.
    eapply in_gt_imp_in_set. exact contraIn.
  Case "y not in indiff".
    intros contraIn.
    apply norel_set_rel_equiv in contraIn. destruct contraIn.
    apply lt_set_rel_equiv in yIn.
    contradiction.
    eapply in_lt_imp_in_set. exact yIn.
    eapply in_lt_imp_in_set. exact yIn.
Qed.

Lemma gt_set_only : forall x y s,
set_In y (gt_set x s) ->
~set_In y (lt_set x s) /\ ~set_In y (norel_set x s).
Proof.
  intros x y s yIn.
  split.
  Case "y not in gt".
    intros contraIn.
    apply gt_set_rel_equiv in yIn.
    apply lt_set_rel_equiv in contraIn.
    eapply Rso. eapply Rso. exact yIn. exact contraIn.
    eapply in_lt_imp_in_set. exact contraIn.
    eapply in_gt_imp_in_set. exact yIn.
  Case "y not in indiff".
    intros contraIn.
    apply norel_set_rel_equiv in contraIn. destruct contraIn.
    apply gt_set_rel_equiv in yIn.
    contradiction.
    eapply in_gt_imp_in_set. exact yIn.
    eapply in_gt_imp_in_set. exact yIn.
Qed.

Lemma norel_set_only : forall x y s,
set_In y (norel_set x s) ->
~set_In y (lt_set x s) /\ ~set_In y (gt_set x s).
Proof.
  intros x y s yIn.
  split.
  Case "y not in lt".
    intros contraIn.
    apply lt_set_only in contraIn. destruct contraIn as [ngt nindiff].
    contradiction.
  Case "y not in gt".
    intros contraIn.
    apply gt_set_only in contraIn. destruct contraIn as [nlt nindiff].
    contradiction.
Qed.

Lemma lt_preserve_nodup : forall x s,
NoDup s ->
NoDup (lt_set x s).
Proof.
  intros x s.
  induction s as [| h rest].
  Case "s = []".
    intros nodup.
    simpl. constructor.
  Case "s = [h :: rest]".
    intros nodup.
    simpl.
    destruct (Rdec h x) as [Rhx |nRhx].
      inversion nodup; subst.
      apply set_add_nodup.
      constructor.
      intros contra. apply H1. eapply in_lt_imp_in_set.
      exact contra. apply IHrest. exact H2.
      apply IHrest. inversion nodup; auto.
Qed.

Lemma exists_empty_lt_set : forall s,
s <> nil ->
exists x, set_In x s /\ lt_set x s = nil.
Proof.
  intros s notempty.
  induction s as [| x1 s'].
  Case "s = []".
    assert False as F. apply notempty. reflexivity. inversion F.
  Case "S =  a :: s".
    destruct s' as [| x2 s''].
    SCase "s' = []".
      exists x1. simpl.
      destruct (Rdec x1 x1).
      assert False as F. eapply Rso. exact r. inversion F. 
      split. left. reflexivity. reflexivity.
    SCase "s' = x2 :: s''".
      assert (x2 :: s'' <> nil) as notmt.
        intros contra. inversion contra.
      apply IHs' in notmt.
      destruct notmt as [m mltnil].
      destruct (Rdec x1 m).
      SSCase "R x1 m".
        exists x1. simpl.
        destruct (Rdec x1 x1).
        apply Rso in r0. inversion r0.
        destruct (Rdec x2 x1).
        SSSCase "R x2 x1".
          assert (set_In x2 (lt_set m (x2 :: s''))) as contra.
          eapply lt_set_rel_equiv. left. reflexivity.
          eapply Rso. exact r0. exact r.
          split. left. reflexivity.
          destruct mltnil as [mltnilIn mltnil].
          rewrite mltnil in contra. inversion contra.
          SSSCase "~R x2 x1".
            remember (lt_set x1 s'') as x1lt.
            destruct (x1lt).
            SSSSCase "lt_set x1 s'' = []". split. left. reflexivity. reflexivity.
            SSSSCase "x :: x1lt = lt_set x1 s''".
              assert (set_In x (lt_set x1 s'')) as xInx1lt.
              rewrite <- Heqx1lt. left. reflexivity.
              assert (set_In x s'') as xcontraIn.
              eapply in_lt_imp_in_set. exact xInx1lt.
              assert (R x m) as Rxm.
              eapply Rso. apply lt_set_rel_equiv in xInx1lt.
              exact xInx1lt. exact xcontraIn. exact r.
              assert (set_In x (lt_set m (x2 :: s''))) as contraInmlt.
              apply lt_set_rel_equiv. right. exact xcontraIn. exact Rxm.
              split. left. reflexivity.
              destruct mltnil as [mltnilIn mltnil].
              rewrite mltnil in contraInmlt. inversion contraInmlt.
      SSCase "R x1 m".
        exists m.
        split.
        destruct mltnil as [mltnilIn mltnil].
        right. exact mltnilIn.
        destruct mltnil as [mltnilIn mltnil].
        simpl. destruct (Rdec x1 m). contradiction. 
        exact mltnil.
Qed.

Theorem minimal_set_mem :
  forall (s: set X), 
    s = nil \/ (exists min, set_In min s /\ 
                           forall y, set_In y s -> ~R y min).
Proof.
  intros s.
  destruct s.
  left; auto.
  right.
  edestruct (exists_empty_lt_set (x::s)).
  intros contra. inversion contra.
  destruct H.
  exists x0. split; auto.
  intros y yIn contraR. 
  forwards*: (lt_set_rel_equiv x0 y).
  apply H1 in contraR. rewrite H0 in contraR.
  inversion contraR.
Qed.

End strict_order.
