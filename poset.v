Require String. Open Scope string_scope.
Require Import Relations Omega NPeano Ensembles Finite_sets Finite_sets_facts List ListSet.
(* Case for clearer analysis *)
Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Require Import ListSet List Relations_1.

(* List Notations *)
Notation " [ ] " := nil.
Notation " [ x ] " := (cons x nil).
Notation " [ x , .. , y ] " := (cons x .. (cons y nil) ..).
Notation "x :: l" := (cons x l) (at level 60, right associativity). 

Section po.

Variable X : Type.
 Hypothesis Xeq_dec : forall (x y:X), {x = y} + {x <> y}.

Variable R : Relation X.
 Hypothesis Rdec : forall (x y:X), {R x y} + {~R x y}.
 Hypothesis Rpo : Order X R.


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
x <> y ->
(R y x <-> set_In y (lt_set x s)).
Proof.
  intros x y s yIn xyneq.
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
          eapply in_lt_imp_in_set. exact yInlt. exact yInlt.
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
x <> y ->
(R x y <-> set_In y (gt_set x s)).
Proof.
  intros x y s yIn xyneq.
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
x <> y ->
((and (~R x y) (~R y x)) <-> set_In y (norel_set x s)).
Proof.
  intros x y s yIn xyneq.
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
            assert (x = y) as contraeq.
              apply Rpo. exact Rxy. apply Ryx.
            contradiction.
            apply IHs'.
            eapply in_norel_imp_in_set. exact yInlt.
          SSSSCase "~Ryx".
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
x <> y ->
In y (lt_set x s) ->
~In y (gt_set x s) /\ ~In y (norel_set x s).
Proof.
  intros x y s neq yIn.
  split.
  Case "y not in gt".
    intros contraIn.
    apply lt_set_rel_equiv in yIn.
    apply gt_set_rel_equiv in contraIn.
    apply neq.
    apply Rpo. exact contraIn. exact yIn.
    eapply in_gt_imp_in_set. exact contraIn.
    exact neq.
    eapply in_lt_imp_in_set. exact yIn. exact neq.
  Case "y not in indiff".
    intros contraIn.
    apply norel_set_rel_equiv in contraIn. destruct contraIn.
    apply lt_set_rel_equiv in yIn.
    contradiction.
    eapply in_lt_imp_in_set. exact yIn. exact neq.
    eapply in_lt_imp_in_set. exact yIn. exact neq.
Qed.

Lemma gt_set_only : forall x y s,
x <> y ->
In y (gt_set x s) ->
~In y (lt_set x s) /\ ~In y (norel_set x s).
Proof.
  intros x y s neq yIn.
  split.
  Case "y not in gt".
    intros contraIn.
    apply gt_set_rel_equiv in yIn.
    apply lt_set_rel_equiv in contraIn.
    apply neq.
    apply Rpo. exact yIn. exact contraIn.
    eapply in_lt_imp_in_set. exact contraIn.
    exact neq.
    eapply in_gt_imp_in_set. exact yIn. exact neq.
  Case "y not in indiff".
    intros contraIn.
    apply norel_set_rel_equiv in contraIn. destruct contraIn.
    apply gt_set_rel_equiv in yIn.
    contradiction.
    eapply in_gt_imp_in_set. exact yIn. exact neq.
    eapply in_gt_imp_in_set. exact yIn. exact neq.
Qed.

Lemma norel_set_only : forall x y s,
x <> y ->
In y (norel_set x s) ->
~In y (lt_set x s) /\ ~In y (gt_set x s).
Proof.
  intros x y s neq yIn.
  split.
  Case "y not in lt".
    intros contraIn.
    apply lt_set_only in contraIn. destruct contraIn as [ngt nindiff].
    contradiction. exact neq.
  Case "y not in gt".
    intros contraIn.
    apply gt_set_only in contraIn. destruct contraIn as [nlt nindiff].
    contradiction. exact neq.
Qed.

Lemma lt_set_size_lt_subset : forall x y s,
x <> y ->
In y (lt_set x s) ->
length (lt_set y s) < length (lt_set x s).
(* TODO *)


Lemma exists_minimal_in_po : forall s,
s <> nil ->
exists x, lt_set x s = nil.
(* TODO *)

End po.