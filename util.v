Require String. Open Scope string_scope.
Require Import Relations List.
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
   - a "Prop" list *)
Inductive PList {X:Type} : relation X -> list X -> Prop :=
| plist_base : forall (R: relation X) (x y:X),
                   R x y ->
                   PList R [ x , y ]
| plist_hd : forall (R:relation X) (l: list X) (x y:X),
                 PList R (y :: l)->
                 R x y ->
                 PList R (x :: y :: l)
| plist_tail : forall (R:relation X) (l:list X) (x y:X),
                   PList R (l ++ [ x ] ) ->
                   R x y ->
                   PList R (l ++ [ x , y ]).

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

Lemma plist_indexs {X:Type} : forall (R:relation X) (l:list X) (x y:X) (i:nat),
PList R l ->
nth_error l i = Some x ->
nth_error l (S i) = Some y ->
R x y.
Proof.
  intros R l x y i PL ni nSi.
  inversion PL; subst.
  Case "base".
    simpl in *.
    destruct i. simpl in *.
    inversion ni. subst. inversion nSi. subst.
    exact H. simpl in nSi. 
    rewrite empty_list_error in nSi. inversion nSi.
    reflexivity.
  Case "PList hd".
    simpl in nSi.

Lemma list_pair_splice {X:Type} : forall (R:relation X) (l:list X) (x y:X) (i:nat),
In x l ->
In y l ->
nth_error l i = Some x ->
nth_error l (S i) = Some y ->
exists lh lt, l = lh ++ [x,y] ++ lt.
Proof. Admitted.

Lemma plist_inner_pair {X:Type} : forall (R:relation X) (lhd ltail:list X) (x y:X),
PList R (lhd ++ [x, y] ++ ltail) ->
R x y.
Proof. Admitted.