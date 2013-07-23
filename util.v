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
| tpath_hd : forall (R:relation X) (l: list X) (x y:X),
                 TPath R (y :: l)->
                 R x y ->
                 TPath R (x :: y :: l)
| tpath_tail : forall (R:relation X) (l:list X) (x y:X),
                   TPath R (l ++ [ x ] ) ->
                   R x y ->
                   TPath R (l ++ [ x , y ]).

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
  Case "PList tail".
    intros i b a Some_a Some_b.
    assert (i <= (length l) \/ 
            (i > (length l))) as i_options.
      omega.
    destruct i_options as [i_leq | i_gr]. 
    inversion i_leq as [i_eq | i_lt].
    SCase "i = length".
      subst. 
      rewrite (nth_length X l x y) in Some_a.
      rewrite (nth_S_length X l x y) in Some_b.
      inversion Some_a. inversion Some_b. subst. exact H.
    SCase "i < length l".
      assert (i <= length l) as i_le_l. omega.
      remember (valid_index_excl_tail_pair X l x y i i_le_l).
      assert (S i <= length l) as Si_le_l. omega.
      remember (valid_index_excl_tail_pair X l x y (S i) Si_le_l).
      rewrite e in Some_a. rewrite e0 in Some_b.
      apply (IHPL i b a). exact Some_a. exact Some_b.
    SCase "i > length".
      clear IHPL PL.
      assert (i >= length l) as i_gre_l. omega.
      assert (S i >= length l) as Si_gre_l. omega.
      remember (nth_app_snd X l [x, y] i i_gre_l).
      remember (nth_app_snd X l [x, y] (S i) Si_gre_l).
      rewrite e in Some_a. rewrite e0 in Some_b.
      rewrite (Nat.sub_succ_l (length l) i i_gre_l) in Some_b.
      simpl in *.
      destruct l. simpl in *. rewrite Nat.sub_0_r in Some_a.
      rewrite Nat.sub_0_r in Some_b.
      destruct i.
      inversion i_gr. inversion Some_b. rewrite empty_list_error in H1.
      inversion H1. reflexivity.
      inversion Some_b.
      assert (i - length (x0 :: l) > 0) as contra. omega.
      assert ((i - (length (x0 :: l))) >= length [y]). 
        simpl. inversion contra. omega. omega.
      rewrite -> (nth_over_index_none X [y] (i - length (x0 :: l))) in Some_b.
      inversion Some_b. omega.
Qed.

Lemma tpath_firstn {X:Type} : forall (R: relation X) (l: list X) n,
TPath R l ->
length (firstn n l) >= 2 ->
TPath R (firstn n l).
Proof. (* TODO *)

Lemma tpath_split_l {X:Type} : forall (R:relation X) (path:list X),
TPath R path ->
exists l r, path = l ++ r ->
length l >= 2 ->
TPath R l.
Proof. (* TODO *)

Lemma tpath_split_r {X:Type} : forall (R:relation X) (path:list X),
TPath R path ->
exists l r, path = l ++ r ->
length r >= 2 ->
TPath R l.
Proof. (* TODO *)

Lemma tpath_skipn {X:Type} : forall (R: relation X) (l:list X) n,
TPath R l ->
length (skipn n l) >= 2 ->
TPath R (skipn n l).
Proof. (* TODO *)

Lemma tpath_inner_pair_R {X:Type} : forall (R:relation X) (lhd ltail:list X) (x y:X),
TPath R (lhd ++ [x, y] ++ ltail) ->
R x y.
Proof. (* TODO *)
  
  
(*

Other useful Lemmas?

- For a Tpath' from a finite set, there is a maximum list length
- Mentioning reverse paths? (use this with above idea to prove minimality?)

*)  