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

(* List whose member's have an inherent relation to their neighbors *)
Inductive ListWitness {X:Type} : relation X -> list X -> Prop :=
| listwit_base : forall (R: relation X) (x y:X),
                   R x y ->
                   ListWitness R [ x , y ]
| listwit_hd : forall (R:relation X) (l: list X) (x y:X),
                 ListWitness R (y :: l)->
                 R x y ->
                 ListWitness R (x :: y :: l)
| listwit_tail : forall (R:relation X) (l:list X) (x y:X),
                   ListWitness R (l ++ [ x ] ) ->
                   R x y ->
                   ListWitness R (l ++ [ x , y ]).