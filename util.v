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


(* List Notations *)
Notation " [ ] " := nil.
Notation " [ x ] " := (cons x nil).
Notation " [ x , .. , y ] " := (cons x .. (cons y nil) ..).
Notation "x :: l" := (cons x l) (at level 60, right associativity). 

Definition fst_opt {X:Type} (l:list X) : option X :=
match l with
 | [] => None
 | h :: t => Some h
end.

Fixpoint last_opt {X:Type} (l:list X) : option X :=
 match l with
   | [] => None
   | [a] => Some a
   | h :: t => last_opt t
 end.

(* List whose member's have an inherent relation to their neighbors 
   - a Transitive Path, since it represents the path given by the 
   transitive closure of the relation*)
Inductive TPath {X:Type} : relation X -> list X -> Prop :=
| tpath_step : forall (R: relation X) (x y:X),
                   R x y ->
                   TPath R [ x , y ]
| tpath_cons : forall (R:relation X) (l: list X) (x y:X),
                 TPath R (y :: l)->
                 R x y ->
                 TPath R (x :: y :: l).
Hint Constructors TPath.

(* A Relational Path, with a specified root element *)
Inductive TPath' {X:Type} : relation X -> list X -> X -> Prop :=
| tpath' : forall (R: relation X) (l: list X) (x:X),
             fst_opt l = Some x ->
             TPath R l ->
             TPath' R l x.

(* A Relational Path, with specified head and tail elements *)
Inductive TPath'' {X:Type} : relation X -> list X -> X -> X -> Prop :=
| tpath'' : forall (R: relation X) (l: list X) (x y:X),
              fst_opt l = Some x ->
              last_opt l = Some y ->
              TPath R l ->
              TPath'' R l x y.

Definition TPath_Reflexivity {X:Type} (R: relation X) : Prop :=
forall x,
  TPath R [x].

Definition TPath_Transitivity {X:Type} (R: relation X) : Prop :=
forall l1 l2 x y z,
  TPath'' R l1 x y ->
  TPath'' R l2 y z ->
  TPath'' R (l1 ++ (tail l2)) x z.

Definition TPath_Antisymmetry {X:Type} (R: relation X) : Prop :=
forall l1 l2 x y,
  TPath'' R l1 x y ->
  TPath'' R l2 y x ->
  x = y.

Lemma empty_nth_error : forall {X:Type} (l: list X) (i:nat),
l = [] ->
nth_error l i = None. 
Proof.
  intros X l i lnil.
  subst l.
  destruct i.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Lemma nth_app_snd : forall X (l1 l2: list X) i,
i >= length l1 ->
nth_error (l1 ++ l2) i = nth_error l2 (i - length l1).
Proof.
  intros X l1. 
  induction l1.
  intros l2 i len_gr.
  simpl. rewrite Nat.sub_0_r. reflexivity.
  intros l2 i i_gr_l.
  destruct i.
  inversion i_gr_l.
  simpl.
  apply IHl1. inversion i_gr_l.
  omega. subst. simpl in H0. omega.
Qed.


Lemma nth_error_overshot : forall X (l : list X) i,
i >= (length l) ->
nth_error l i = None.
Proof.
  intros X l.
  induction l.
  intros i i_gr. 
  rewrite empty_nth_error. reflexivity. reflexivity.
  intros i i_gr.
  destruct i.
  inversion i_gr.
  simpl. apply IHl. 
  simpl in i_gr. omega.
Qed.


Lemma tpath_adj_index_R {X:Type} : forall (R:relation X) (l:list X) (x y:X) (i:nat),
TPath R l ->
nth_error l i = Some x ->
nth_error l (S i) = Some y ->
R x y.
Proof.
  intros R l x y i PL. 
  generalize dependent x. generalize dependent y.
  generalize dependent i.
  induction PL.
  Case "step".
    intros i b a Some_a Some_b.
    simpl in *.
    destruct i. simpl in *.
    inversion Some_a. subst. inversion Some_b. subst.
    exact H. simpl in Some_b.
    rewrite empty_nth_error in Some_b. inversion Some_b.
    reflexivity.
  Case "cons".
    intros i b a Some_a Some_b.
    destruct i.
    SCase "i = 0".
      simpl in *.
      inversion Some_a. inversion Some_b.
      subst. exact H.
      simpl in Some_a.
      assert (nth_error (y :: l) (S i) = Some b) as Some_b'.
        simpl in *. exact Some_b.
      apply (IHPL i b a). exact Some_a. exact Some_b'.
Qed.

Definition sublist {X:Type} (l' l:list X) :=
exists h t, l = h ++ l' ++ t.

Lemma empty_firstn_empty {X:Type} : forall n (l : list X),
l = [] ->
firstn n l = [].
Proof.
  intros n l leq.
  subst. destruct n; auto.
Qed.

Lemma tpath_non_nil {X:Type} : forall (R:relation X) (l:list X),
TPath R l ->
l <> [].
Proof.
  intros R l tpath eq.
  destruct tpath.
  inversion eq.
  inversion eq.
Qed.

Lemma tpath_pair_imp_R {X:Type} : forall (R:relation X) x y,
TPath R [x, y] ->
R x y.
Proof.
  intros R x y tp.
  inversion tp; subst.
  exact H1. exact H4.
Qed.

Lemma tpath_app_snd {X:Type} : forall (R: relation X) (l1 l2 : list X) (x:X),
TPath R (x :: l2) ->
TPath R (l1 ++ [x]) ->
TPath R (l1 ++ (x :: l2)).
Proof.
  intros R l1.
  induction l1;
  intros l2 x tpxl2 tpl1x.
  Case "l1 = []".
    simpl. exact tpxl2. 
  Case "l1 = x0 :: l1".
    destruct l1; simpl.
    SCase "l1 = []".
      apply tpath_cons. exact tpxl2.
      simpl in tpl1x.
      apply tpath_pair_imp_R. exact tpl1x.
    SCase "l1 = x0 :: l1".
      apply tpath_cons.
      apply IHl1.
      exact tpxl2.
      simpl.
      inversion tpl1x; subst. symmetry in H3. apply app_eq_nil in H3. 
      destruct H3. inversion H0. exact H2. 
      apply (tpath_adj_index_R R ((a :: x0 :: l1) ++ [x]) a x0 0).
      exact tpl1x. simpl. reflexivity.
      simpl. reflexivity.
Qed.

Lemma last_opt_impl_front_list : forall X (l: list X) (x: X),
last_opt l = Some x ->
exists l', l = l' ++ [x].
Proof.
  intros X l.
  induction l as [| h t].
  Case "[]".
    intros x Hend.
    inversion Hend.
  Case "h :: t".
    intros x Hend.
    destruct t.
    SCase "t = []".
      inversion Hend.
      subst. exists []. reflexivity.
      assert (last_opt (x0 :: t) = Some x) as Hlast_opt. auto.
      remember (IHt x Hlast_opt) as exl'.
      inversion exl'.
      exists (h :: x1). simpl.
      rewrite H. reflexivity.
Qed.

Lemma fst_opt_imp_hd {X:Type} : forall (x: X) (l: list X),
fst_opt l = Some x ->
exists l', l = x :: l'.
Proof.
  intros x l fst_somex.
  destruct l.
  inversion fst_somex. 
  exists l. 
  simpl in fst_somex. inversion fst_somex.
  subst. reflexivity.
Qed.

Lemma last_opt_nonnil {X:Type} : forall (l1 l2: list X),
l2 <> [] ->
last_opt (l1 ++ l2) = last_opt l2. 
Proof.
  intros l1.
  induction l1. 
  Case "l1 = []".
    intros l2 nonmt.
    simpl. reflexivity.
  Case "l1 = a :: l1".
    intros l2 nonmt.
    remember (l1 ++ l2) as lapp.
    destruct lapp.
    assert False as F.
      apply nonmt. symmetry in Heqlapp. apply app_eq_nil in Heqlapp.
      destruct Heqlapp. exact H0.
    inversion F.
    simpl. rewrite <- Heqlapp. rewrite Heqlapp.
    apply IHl1. exact nonmt.
Qed.

Lemma tpath_uncons {X:Type} : forall R (h: X) (rest: list X),
TPath R (h :: rest) ->
length rest > 1 ->
TPath R rest.
Proof.
 intros R h rest tpath len.
 inversion len.
 destruct rest. inversion H0.
 destruct rest. inversion H0. destruct rest.
 inversion tpath. subst. exact H3.
 inversion H0.
 destruct rest. inversion H0.
 inversion H. inversion H. destruct rest. inversion len. inversion H2.
 inversion tpath. subst. exact H4.
Qed.

Lemma tpath_last_app {X:Type} : forall R l (y z: X),
TPath R l ->
last_opt l = Some y ->
R y z ->
TPath R (l ++ [z]).
Proof.
  intros R l.
  induction l as [| h rest]; intros y z tpath last_y Ryz.
  inversion tpath.
  destruct (last_opt_impl_front_list X (h :: rest) y last_y) as [hl l_eq].
  destruct rest.
  inversion tpath.
  simpl.
  constructor.
  destruct rest as [| h' ht].
  Case "rest = []".
    simpl.
    constructor.
    assert (y = x) as eq_yz.
      destruct hl. simpl. inversion l_eq. destruct hl.
      simpl in l_eq. inversion l_eq. reflexivity. inversion l_eq.
      symmetry in H2. destruct (app_eq_nil hl [y] H2) as [hl_nil ynil].
      inversion ynil.
    subst y. exact Ryz.
  Case "rest = h' ht".
    eapply IHrest.
    apply tpath_uncons in tpath. exact tpath.
    simpl. omega.
    inversion last_y.
    simpl. exact H0.
    exact Ryz.
    inversion tpath; subst.
    exact H1. exact H4.
Qed.


Theorem trans_imp_tpath {X:Type} : forall R (x y: X),
clos_trans X R x y->
exists l,
TPath'' R l x y.
Proof.
  intros R x y Rxy.
  induction Rxy.
  Case "R x y".
    exists [x, y].
    constructor. simpl. reflexivity.
    simpl. reflexivity. constructor. exact H.
  Case "Rxy Ryz".
    destruct IHRxy1 as [lxy tpathxy].
    destruct IHRxy2 as [lyz tpathyz].
    destruct tpathxy as [R lxy x y fst_x last_y tpathxy].
    destruct tpathyz as [R lyz y z fst_y last_z tpathyz].
    destruct tpathxy as [R x' y' Rxy | R list_rest x' y' tpathyrest Rxy].
    SCase "tpath_step xy".
      assert (x' = x). inversion fst_x. reflexivity. subst.
      assert (y' = y). inversion last_y. reflexivity. subst.
      destruct tpathyz as [R y' z' Ryz | R list_rest y' z' tpathzrest Ryz].
      SSCase "tpath_step yz".
        assert (y' = y). inversion fst_y. reflexivity. subst.
        assert (z' = z). inversion last_z. reflexivity. subst.
        exists [x, y, z].
        constructor.
        simpl. reflexivity. simpl. reflexivity.
        constructor.
        constructor. exact Ryz. exact Rxy.
      SSCase "tpath_cons yz".
        assert (y' = y). inversion fst_y. reflexivity. subst.
        exists (x :: y :: z' :: list_rest).
        constructor.
        simpl. reflexivity. auto.
        constructor. constructor.
        exact tpathzrest.
        exact Ryz.
        exact Rxy.
    SCase "tpath_cons xy".
      assert (x' = x). inversion fst_x. reflexivity. subst.
      destruct tpathyz as [R y'' z' Ry''z | R list_rest' y'' z' tpathzrest Ry''z].
      SSCase "tpath_step yz'".
        assert (y'' = y). inversion fst_y. reflexivity. subst.
        assert (z' = z). inversion last_z. reflexivity. subst.
        assert (last_opt list_rest = Some y) as y_at_list_rest_end.
          destruct list_rest. inversion tpathyrest. auto.
        clear fst_y last_z fst_x last_y Rxy1 Rxy2.
        exists (x :: y' :: list_rest ++ [z]).
        constructor.
        simpl. reflexivity.
        assert ((x :: y' :: list_rest) ++ [z] = x :: y' :: list_rest ++ [z]) as triv_eq. auto.
        rewrite <- triv_eq.
        rewrite (last_opt_nonnil (x :: y' :: list_rest) [z]). simpl. reflexivity.
        intros contra. eapply nil_cons. symmetry in contra. exact contra.
        constructor. 
        assert (last_opt (y' :: list_rest) = Some y) as y_at_last_too.
          destruct list_rest. inversion tpathyrest. simpl. exact y_at_list_rest_end.
        apply (tpath_last_app R (y' :: list_rest) y z). exact tpathyrest. 
        destruct list_rest. inversion y_at_list_rest_end. simpl. exact y_at_list_rest_end.
      exact Ry''z. exact Rxy.
    SSCase "tpath_cons yz'".
      assert (y'' = y). inversion fst_y. reflexivity. subst.
      clear fst_x fst_y.
      exists ((x :: y' :: list_rest) ++ (z' :: list_rest')).
      constructor.
      simpl. reflexivity. rewrite last_opt_nonnil. auto. intro contra. inversion contra.
      apply tpath_app_snd. exact tpathzrest.
      Check tpath_last_app.
      apply (tpath_last_app R (x :: y' :: list_rest) y z').
      constructor. exact tpathyrest. exact Rxy.
      exact last_y.
      exact Ry''z.
Qed.

Theorem tpath_imp_trans {X:Type} : forall R (l:list X) (x y: X),
TPath'' R l x y ->
clos_trans X R x y.
Proof.
  intros R l. generalize dependent R.
  induction l as [| h t]; intros R a b tpath''.
  Case "l = []".
    inversion tpath''; subst.
    inversion H1.
  Case "l = h :: t".
    destruct t as [| x' rest].
    SCase "t = []".
      inversion tpath''. inversion H1.
    SCase "t = x' rest".
      assert (h = a) as ha_eq.
        inversion tpath''. inversion H. reflexivity.
      subst h.
      destruct rest as [| x'' rest'].
      SSCase "rest = []".
        inversion tpath''0. subst.
        constructor. apply tpath_pair_imp_R.
        inversion H0. subst. exact H1.
      SSCase "rest = x'' :: rest'".
        inversion tpath''0; subst.
        assert (TPath'' R (x' :: x'' :: rest') x' b).
        inversion H1. subst.
        constructor. simpl. reflexivity.
        simpl. simpl in H0. exact H0.
        exact H5.
        eapply t_trans.
        constructor.
        apply (tpath_adj_index_R R (a :: x' :: x'' :: rest') a x' 0).
        exact H1. simpl. reflexivity. simpl. reflexivity.
        apply IHt. exact H2.
Qed.

Section set_util.



  Variable X : Type.
  Hypothesis Xeq_dec : forall x y:X, {x = y} + {x <> y}.

Fixpoint set_subtract (s : set X) (x:X) : set X :=
  match s with
    | [] => []
    | h :: rest 
      => match (Xeq_dec h x) with 
           | (* eq *) left _ =>  rest
           | (* neq *) right _ => (set_add Xeq_dec h (set_subtract rest x))
         end
  end.
Hint Unfold set_subtract.

Lemma set_subtract_neg_In : forall (s: set X) (x:X),
NoDup s ->
~set_In x (set_subtract s x).
Proof.
  intros s.
  induction s.
  Case "[]".
    intros x nodup x_mem.
    simpl in x_mem. exact x_mem.
  Case "a :: s".
    intros x nodup x_mem.
    inversion nodup; subst.
    destruct (Xeq_dec x a) as [eq | neq].
    SCase "x=a".
      subst x.
      assert ((set_subtract (a :: s) a) = s) as subset_ran.
        unfold set_subtract. simpl. destruct (Xeq_dec a a). reflexivity. 
        assert False as F. apply n. reflexivity. inversion F.
      rewrite subset_ran in x_mem.
      contradiction.
      SCase "x<>a".
        simpl in x_mem. destruct (Xeq_dec a x) as [eq1 | leq1]. apply neq. auto.
        apply set_add_elim in x_mem.
        destruct x_mem. apply leq1. auto.
        apply (IHs x) in H2.
        apply H2. exact H.
Qed.

Lemma set_subtract_imp_subset : forall (s : set X) (x: X),
NoDup s ->
set_In x s ->
forall y : X,
set_In y s ->
y <> x ->
set_In y (set_subtract s x).
Proof. 
  intros s.
  induction s.
  Case "[]".
    intros x nodup xIn.
    inversion xIn.
  Case "a :: s".
    intros x nodup xIn y yIn xyneq.
    destruct (Xeq_dec a x).
    SCase "a = x".
      subst.
      simpl. destruct (Xeq_dec x x) as [axeq | axneq].
      inversion yIn; subst.
      assert False as F. apply xyneq. reflexivity. inversion F.
      exact H.
      assert False as F. apply axneq. reflexivity. inversion F.
    SCase "a <> x".
      destruct (Xeq_dec y a) as [ayeq | ayneq].
      SSCase "a = y".
        subst. simpl. 
        destruct (Xeq_dec a x). assert False as F. apply xyneq. exact e. inversion F.
        apply set_add_intro. left. reflexivity. 
      SSCase "a <> y".
        simpl.
        destruct (Xeq_dec a x) as [axeq | axneq].
        inversion yIn; subst. assert False as F. apply xyneq. auto. inversion F.
        exact H.
        apply set_add_intro1.
        apply IHs. auto.
        assert (NoDup s) as nodup_s.
          inversion nodup; subst. exact H2.
       exact nodup_s.
       inversion xIn; subst.
       assert False as F. apply n. reflexivity. inversion F.
       exact H.
       inversion xIn.
       assert False as F. apply n. rewrite H. reflexivity. inversion F.
       inversion yIn; subst. assert False as F. apply ayneq. reflexivity. inversion F.
       exact H0.
       exact xyneq.
Qed.

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

Lemma in_subtract_imp_in : forall s a x,
In a (set_subtract s x) ->
In a s.
Proof.
  intros s.
  induction s.
  intros a x Hin.
  simpl in Hin. inversion Hin.
  intros x y Hin.
  simpl.
  destruct (Xeq_dec a y) as [eqay | neqay].
    subst.
    simpl in Hin.
    destruct (Xeq_dec y y).
    right. exact Hin.
    assert False as F. apply n. reflexivity. inversion F.
    simpl in Hin.
    destruct (Xeq_dec a y).
    right. exact Hin.
    apply set_add_elim in Hin.
    destruct Hin. left. auto.
    apply IHs in H.
    right. exact H.
Qed.

Lemma set_subtract_nodup : forall s x,
NoDup s ->
NoDup (set_subtract s x).
Proof.
  intros s.
  induction s.
  Case "[]".
    intros x nodup.
    simpl. exact nodup.
  Case "a :: s".
    intros x nodup.
    simpl.
    destruct (Xeq_dec a x) as [eqax | neqax].
    inversion nodup; subst. exact H2.
    apply set_add_nodup. 
    constructor.

    intros contra.
    SearchAbout set_subtract.
    inversion nodup; subst. apply H1.
    eapply in_subtract_imp_in.
    exact contra.
    apply IHs.
    inversion nodup. exact H2.
Qed.

Lemma set_subtract_count : forall x s n,
NoDup s ->
set_In x s ->
length s = S n ->
length (set_subtract s x) = n.
Proof.
  intros x s. generalize dependent x.
  induction s.
  Case "[]".
    intros x n nodup xin.
    inversion xin.
  Case "a :: s".
    intros x n nodup xIn len.
    destruct (Xeq_dec a x) as [eqax | neqax].
      subst. simpl.
      destruct (Xeq_dec x x). inversion len. reflexivity.
      assert False as F. apply n0. reflexivity. inversion F.
    assert (set_In x s) as xIns.
      inversion xIn. assert False as F. apply neqax. exact H. inversion F.
      exact H.
    destruct n.
    SCase "n = 0".
      inversion len.
      destruct s. inversion xIns.
      inversion H0.
    SCase "n = S n".
      simpl.
      destruct (Xeq_dec a x) as [eqax | neqax2].
      assert False as F. apply neqax. exact eqax. inversion F.
      eapply set_add_Sn.
      intros contra. inversion nodup.
      apply H1. eapply in_subtract_imp_in. exact contra.
      apply IHs.
      inversion nodup. exact H2.
      exact xIns.
      inversion len. reflexivity.
Qed.

Lemma ensemble_element_sub : forall E x n,
InSet X E x ->
cardinal X E (S n) ->
exists E' : Ensemble X, cardinal X E' n /\ E = Add X E' x. 
Proof.
  intros E x n xInE cardSn.
  assert (Finite X E) as Efin. apply (cardinal_finite X E (S n)). exact cardSn.
  apply ensemble_imp_set in Efin.
  destruct Efin as [s [Hin [Hnodup Hlen]]].
  destruct Hlen as [j [slen cardE]].
  assert (j = S n) as eqjSn.
    apply (cardinal_unicity X E). exact cardE. exact cardSn.
  assert (set_In x s). apply Hin. exact xInE.
  assert (forall y : X, set_In y s -> y <> x -> set_In y (set_subtract s x)) as Hallnotx.
  apply set_subtract_imp_subset. exact Hnodup. exact H.
  assert (NoDup (set_subtract s x)) as nodupsminx.
    apply set_subtract_nodup. exact Hnodup.
  destruct (set_imp_ensemble (set_subtract s x) nodupsminx) as [E' [HE'in HE'len]].
  exists E'.
  split.
  destruct HE'len as [n' [HElen HEcard]].
  assert (n' = n) as eqns.
  assert (length (set_subtract s x) = n) as HElen2.
    apply set_subtract_count. exact Hnodup. exact H.
    omega.
  omega. rewrite eqns in HEcard. exact HEcard. 
  apply Extensionality_Ensembles.
  unfold Same_set.
  split.
  Case "Included X e (Add X E' x)".
    unfold Included. intros y yInE.
    destruct (Xeq_dec x y) as [eqxy | neqxy].
    SCase "x = y".
      rewrite eqxy.
      apply Add_intro2.
    SCase "x <> y".
      apply Add_intro1. apply HE'in. apply Hallnotx.
      apply Hin. exact yInE. intros contra. apply neqxy. auto.
  Case "Included X (Add X e' x) E".
    unfold Included. intros y yInAddE'.
    destruct (Xeq_dec x y) as [eqxy | neqxy].
    SCase "x = y".
      rewrite <- eqxy.
      exact xInE.
    SCase "x <> y".
      apply Hin.
      destruct yInAddE' as [y yInE' | y inSingleton].
      apply HE'in in yInE'. apply in_subtract_imp_in in yInE'.  exact yInE'.
      inversion  inSingleton.
      assert False as F. apply neqxy. exact H0.
      inversion F.
Qed.

End set_util.


(* todo FINISH set_subtract_imp_subset
   create ListSet / Finite Ensemble isomorphism
   Figure out bridge to finite_set_list_length *)

(*
   Need to be able to use the following Hypothesis to prove the exists

   InSet X E h ->
   exists E' : Ensemble X, cardinal X E' n' /\ E = Add X E' h
*)


(*)
Lemma in_imp_ex_subset : forall (s: set X) (x:X),
NoDup s ->
set_In x s ->
s = set_add Xeq_dec x (set_subtract s x). *)
(* Bookmark *)
(* Ugh... does this "eq" work here? I don't think it's = but it is definitily "set_eq" if that
   exists, either way I think I need a rewrite rule from it... =| *)



Theorem finite_set_list_length {X: Type} : 
forall (l: list X) (E: Ensemble X) (c: nat),
(forall x y : X, {x = y} + {x <> y}) ->
cardinal X E c ->
NoDup l ->
(forall x, In x l -> InSet X E x) ->
length l <= c.
Proof.
  intros l.
  induction l as [| h t].
  Case "l = []".
    intros E c eq_dec card nodup In_eq. simpl. omega.
  Case "l = h :: t".
    intros E n eq_dec card nodup In_eq.
    destruct n as [| n'].
    SCase "n = 0".
      assert (InSet X E h) as hinE.
        apply In_eq. apply in_eq.
      inversion card; subst.
      inversion hinE.
   SCase "n = S n".
     assert (InSet X E h) as hinE.
       apply In_eq. apply in_eq.
     cut (exists E', cardinal X E' n' /\ E = Add X E' h).
     intros ex_subset.
     inversion ex_subset as [E' E'props].
     inversion E'props as [E'card Eeq].
     assert (length t <= n') as length_helper.
       apply (IHt E'). exact eq_dec. exact E'card.
     inversion nodup; subst. exact H2.
     intros x xIn.
     rewrite Eeq in In_eq.
     assert (InSet X (Add X E' h) x) as xInE.
       apply In_eq. apply in_cons. exact xIn.
     assert (x <> h) as xneqh.
       intros contra.
       inversion nodup.
       subst x. contradiction.
     apply Add_inv in xInE.
     destruct xInE. exact H. symmetry in H. contradiction.
     simpl. apply le_n_S. exact length_helper.
     apply ensemble_element_sub.
     exact eq_dec. exact hinE. exact card.
Qed.




