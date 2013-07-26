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

(* List whose member's have an inherent relation to their neighbors 
   - a Transitive Path, since it represents the path given by the 
  transitive closure of the relation*)
Inductive TPath {X:Type} : relation X -> list X -> Prop :=
| tpath_base : forall (R: relation X) (x y:X),
                   R x y ->
                   TPath R [ x , y ]
| tpath_cons : forall (R:relation X) (l: list X) (x y:X),
                 TPath R (y :: l)->
                 R x y ->
                 TPath R (x :: y :: l).
Hint Constructors TPath.

(* A Transitive Path, with a specified root element *)
Inductive TPath' {X:Type} : relation X -> list X -> X -> Prop :=
| tpath' : forall (R: relation X) (l: list X) (x:X),
             (exists l', l = x :: l') ->
             TPath R l ->
             TPath' R l x.

(* A Transitive Path, with specified head and tail elements *)
Inductive TPath'' {X:Type} : relation X -> list X -> X -> X -> Prop :=
| tpath'' : forall (R: relation X) (l: list X) (x y:X),
              (exists l', l = (x :: l') ++ [ y ]) ->
              TPath R l ->
              TPath'' R l x y.

Definition TPath_Transitivity (X:Type) (R: relation X) : Prop :=
forall l1 l2 x y z,
  TPath'' R l1 x y ->
  TPath'' R l2 y z ->
  TPath'' R (l1 ++ (tail l2)) x z.


Lemma empty_list_error : forall {X:Type} (l: list X) (i:nat),
l = [] ->
nth_error l i = None. 
Proof.
  intros X l i lnil.
  subst l.
  destruct i.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Lemma nth_length : forall X (l : list X) (x y : X),
nth_error (l ++ [x, y]) (length l) = Some x. 
Proof.
  intros X l. induction l. intros x y.
  simpl. auto. simpl. exact IHl.
Qed.

Lemma nth_S_length : forall X (l : list X) (x y : X),
nth_error (l ++ [x, y]) (S (length l)) = Some y.
Proof.
  intros X l. induction l. intros x y.
  simpl. auto. simpl. exact IHl.
Qed.

Lemma valid_index_excl_tail_pair : forall X (l : list X) (x y: X) i,
i <= length l ->
nth_error (l ++ [x, y]) i = nth_error (l ++ [x]) i.
Proof.
  intros X l x y i.
  generalize dependent X.
  induction i.
  intros X l x y len.
  destruct l.
  inversion len.
  simpl. reflexivity.
  simpl. reflexivity.
  intros X l x y Si_len.
  destruct l. inversion Si_len. simpl.
  apply IHi. inversion Si_len; omega.
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


Lemma nth_over_index_none : forall X (l : list X) i,
i >= (length l) ->
nth_error l i = None.
Proof.
  intros X l.
  induction l.
  intros i i_gr. 
  rewrite empty_list_error. reflexivity. reflexivity.
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
  Case "base".
    intros i b a Some_a Some_b.
    simpl in *.
    destruct i. simpl in *.
    inversion Some_a. subst. inversion Some_b. subst.
    exact H. simpl in Some_b.
    rewrite empty_list_error in Some_b. inversion Some_b.
    reflexivity.
  Case "PList hd".
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

Lemma firstn_empty {X:Type} : forall n (l : list X),
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

Lemma tpath_min_len {X:Type} : forall (R:relation X) (l:list X),
TPath R l ->
length l > 1.
Proof.
  intros R l tpl.
  destruct tpl.
  simpl. omega.
  simpl. omega.
Qed.

Lemma tpath_pair {X:Type} : forall (R:relation X) x y,
TPath R [x, y] ->
R x y.
Proof.
  intros R x y tp.
  inversion tp; subst.
  exact H1. exact H4.
Qed.

Lemma tpath_app_hd {X:Type} : forall (R: relation X) (l1 l2 : list X) (x:X),
TPath R (x :: l2) ->
TPath R (l1 ++ [x]) ->
TPath R (l1 ++ (x :: l2)).
Proof.
  intros R l1.
  induction l1.
  intros l2 x tpxl2 tp_contra.
  inversion tp_contra.
  intros l2 x tpxl2 tpal1x.
  assert ((a :: l1) ++ x :: l2 = a :: (l1 ++ (x :: l2))).
    simpl. reflexivity. 
  rewrite H.
  destruct l1.
  Case "l1 = []".
    simpl.
    apply tpath_cons. exact tpxl2.
    simpl in tpal1x.
    apply tpath_pair. exact tpal1x.
  Case "l1 = x0 :: l1".
    assert ((a :: (x0 ::l1) ++ x :: l2) = (a :: x0 :: (l1 ++ x :: l2))) as eq.
    simpl. reflexivity. 
    rewrite eq.
    apply tpath_cons.
    apply IHl1.
    exact tpxl2.
    clear eq.
    assert ((x0 :: l1) ++ [x] = (x0 :: (l1 ++ [x]))) as eq.
      simpl. reflexivity.
    rewrite eq.
    inversion tpal1x; subst. symmetry in H4. apply app_eq_nil in H4. 
    destruct H4. inversion H1. exact H3. 
    apply (tpath_adj_index_R R ((a :: x0 :: l1) ++ [x]) a x0 0).
    exact tpal1x. simpl. simpl. reflexivity.
    simpl. reflexivity.
Qed.

(*
Lemma tpath_sublist {X:Type} : forall (R: relation X) (l l': list X),
TPath R l ->
sublist l' l ->
length l' >= 2 ->
TPath R l'.
Proof.
  intros R l l' tpath sub len.  
  destruct sub as [h [t]].
  subst.
  induction h.
  Case "h = []".
    simpl in tpath.
    induction on 

  


Other useful Lemmas?

- For a Tpath' from a finite set, there is a maximum list length
- Mentioning reverse paths? (use this with above idea to prove minimality?)

*)  