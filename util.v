Require String. Open Scope string_scope.
Require Import Relations List Omega NPeano.
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

(*
Lemma tpath_sublist {X:Type} : forall (R: relation X) (l l': list X),
Rpath R l ->
sublist l' l ->
length l' >= 2 ->
Rpath R l'.
Proof.
  intros R l l' tpath sub len.  
  destruct sub as [h [t]].
  subst.
  induction h.
  Case "h = []".
    simpl in rpath.
    induction on 

  


Other useful Lemmas?

- For a Rpath' from a finite set, there is a maximum list length
- Mentioning reverse paths? (use this with above idea to prove minimality?)

*)  
