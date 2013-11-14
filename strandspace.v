(** * strandspace.v: Basic Strand Space Definitions *)

(* Created by Andrew Kent
   Brigham Young University
 *)

(* Source Material(s): 

1) Strand Spaces: Proving Security Protocols Correct.
   F. Javier Thayer Fabrega, Jonathan C. Herzog, Joshua D. Guttman. 
   Journal of Computer Security, 7 (1999), pages 191-230.
   http://web.cs.wpi.edu/~guttman/pubs/jcs_strand_spaces.pdf

2) Authentication tests and the structure of bundles.
   Joshua D. Guttman, F. Javier Thayer, Theoretical Computer Science, 
   v.283 n.2, p.333-380, June 14, 2002.
   http://www.mitre.org/work/tech_papers/tech_papers_01/guttman_bundles/
 *)
Require Import Logic List ListSet Arith Peano_dec Omega.
Require Import Relation_Definitions Relation_Operators.
Require Import CoLoRRelDec CoLoRRelSub.
Require Import strictorder set_rep_equiv util.
Require Import finite_set_builder.
Require Import LibTactics.

Module SS.

(* atomic messages *)
Variable Text : Set.
Variable eq_text_dec : forall (x y:Text), {x = y} + {x <> y}.
Hint Resolve eq_text_dec.

(* representing kryptographic key *)
Variable Key : Set.
Variable eq_key_dec : forall (x y:Key), {x = y} + {x <> y}.
Hint Resolve eq_key_dec.

Variable Inv : relation Key.
(* Used to indicate two keys are cryptographic
   inverses of eachother. *)

(* message or text, comprising the set of terms "A" *)
Inductive Msg : Type :=
| msg_text : Text -> Msg
| msg_key  : Key  -> Msg
| msg_join : Msg  -> Msg -> Msg 
| msg_encr : Key  -> Msg -> Msg.
(* [REF 1] Section 2.1 pg 5 
           Section 2.3 pg 9 *)
(* [REF 2] pg 4 paragraph 3 (details of encryption and subterms) *)
Hint Constructors Msg.

Notation "(! x )" := (msg_text x) : ss_scope. 
Notation "(# k )" := (msg_key k) : ss_scope.
Notation "x * y" := (msg_join x y) (at level 40, left associativity) : ss_scope.
Notation "{ m }^[ k ] " := (msg_encr k m) (at level 0, m at level 99, k at level 99) : ss_scope.

Open Scope ss_scope.

(* subterm relationship for messages *)
(* subterm -> encompassing term -> Prop *)
Inductive Subterm : Msg -> Msg -> Prop :=
| st_refl : forall m, Subterm m m
| st_join_l : forall st l r, 
               Subterm st l -> Subterm st (l*r)
| st_join_r : forall st l r, 
               Subterm st r -> Subterm st (l*r)
| st_encr : forall st t k, 
               Subterm st t -> Subterm st ({t}^[k]).
(* [REF 1] Section 2.1 pg 6 and Definition 2.11 *)
Hint Constructors Subterm.

Notation "a <st b" := (Subterm a b) (at level 30) : ss_scope.

(* signed message, + (tx) or - (rx) *)
Inductive SMsg : Type := 
| msg_tx : Msg -> SMsg
| msg_rx : Msg -> SMsg.
(* [REF 1] Definition 2.1 pg 6 
   They are defined as a pair, w/ the first member being in {+, -} 
   and the second a signed message. *)
Hint Constructors SMsg.

Notation "(+ x )" := (msg_tx x) : ss_scope.
Notation "(- x )" := (msg_rx x) : ss_scope.

(* strand *)
Definition Strand : Type := list SMsg.
(* [REF 1] First sentence of Abstract: "sequence of events"  
   Haven't hit a better def, and they start using strands
   pretty early so I'm rolling with this. *)

(* node in a strand space *)
Definition Node : Type := {n: (Strand * nat) | (snd n) < (length (fst n))}.
(* [REF 1] Definition 2.3.1 pg 6
   -"A node is a pair <s,i> where s is a strand and i a nat in [0, (length s))"
     NOTE: changed to be 0 based instead of 1 based sequences
   -"node <s,i> belongs to strand s"
   -"Every node belongs to a unique strand" *)

Definition Edge : Type := (prod Node Node).

(* index of a node *)
Definition index (n:Node) : nat :=
  match n with
    | exist npair _ 
      => snd npair
  end.
(* [REF 1] Definition 2.3.2 pg 6
   "If n = <s,i> then index(n) = i." *)

(* strand of a node *)
Definition strand (n:Node) : Strand :=
  match n with
    | exist npair _ 
      => fst npair
  end.
(* [REF 1] Definition 2.3.2 pg 6
   "If n = <s,i> then ... strand(n) = s." *)

(* signed message of a node *)
Fixpoint Node_smsg_option (n:Node) : (option SMsg) :=
  match n with
    | exist (s, i) p 
      =>  nth_error s i
  end. 
(* [REF 1] Definition 2.3.2 pg 6
   "Define term(n) to be the ith signed term of the trace of s." *)

Lemma nth_error_len : 
forall {X:Type} {l:list X} i,
  None = nth_error l i -> (length l) <= i.
Proof.
  intros X l i. generalize dependent l.
  induction i. 
  Case "i = 0".
    intros l H.
    unfold nth_error in H.
    unfold error in H.
    destruct l.
    auto. inversion H.
  Case "i = S i".
    intros l' H.
    destruct l'.
    simpl; omega.
    inversion H.
    apply IHi in H1.
    simpl. omega. 
Qed.

Lemma node_smsg_valid :
forall (n:Node), {m:SMsg | Some m = Node_smsg_option n}.
Proof.
  intros n.
  remember (Node_smsg_option n) as funcall.
  destruct n. destruct funcall.  
  exists s. reflexivity.

  unfold Node_smsg_option in Heqfuncall.
  destruct x. simpl in l.
  apply nth_error_len in Heqfuncall.
  omega.
Qed.

(* signed message of a node *)
Definition smsg (n:Node) : SMsg :=
  match node_smsg_valid n with
    | exist m _ => m
  end.

Definition smsg_msg (s:SMsg) : Msg :=
  match s with
    | (+t) => t
    | (-t) => t
  end. 

(* unsigned message of a node *)
Definition msg (n:Node) : Msg :=
  smsg_msg (smsg n).
(* [REF 1] Definition 2.3.2 pg 6
   "Define uns_term(n) to be the unsigned part of the ith signed term 
    of the trace of s." *)

Definition is_tx (n:Node) : Prop :=
exists t, smsg n = (+ t).

Definition is_rx (n:Node) : Prop :=
exists t, smsg n = (- t).


Inductive Comm : relation Node :=
| comm :  forall n m t, ((smsg(n) = (+t) 
                          /\ smsg(m) = (-t))
                         /\ strand(n) <> strand(m))
                        -> Comm n m.
Hint Constructors Comm.
(* [REF 1] Definition 2.3.3 pg 6
   "there is an edge n1 -> n2 iff term(n1) = +a and term(n2) = -a ... 
   recording a potential causal link between those strands**"
  **We take this to mean a causal link between two *different* 
  strands, as this is logical, and fits numerous informal 
  descriptions in the literature such as "A strand (process) 
  may send or receive a message but not both at the 
  same time". *)

Notation "a --> b" := (Comm a b) (at level 0, right associativity)  : ss_scope.

Inductive Comm' : set Node -> relation Node :=
| comm' : forall N n m, In n N ->
                        In m N ->
                        n --> m ->
                        Comm' N n m.
Hint Constructors Comm'.

Notation "a -[ N ]-> b" := (Comm' N a b) (at level 0, right associativity)  : ss_scope.

Lemma comm'_in_l : forall N x y,
x -[N]-> y ->
In x N.
Proof.
  intros n x y edge.
  inversion edge; subst; auto.
Qed.
Hint Resolve comm'_in_l.

Lemma comm'_in_r : forall N x y,
x -[N]-> y ->
In y N.
Proof.
  intros n x y edge.
  inversion edge; subst; auto.
Qed.
Hint Resolve comm'_in_r.

Lemma comm'_imp_comm : forall N x y,
x -[N]-> y ->
x --> y.
Proof.
  intros n x y edge.
  inversion edge; subst; auto.
Qed.
Hint Resolve comm'_imp_comm.

(* successor edge *)
(* node's direct predecessor -> node -> Prop *)
Inductive Successor : relation Node :=
| succ : forall i j, strand(i) = strand(j) 
                       -> index(i) + 1 = index(j) 
                       -> Successor i j.
(* [REF 1] Definition 2.3.4 pg 6
   "When n1= <s,i> and n2=<s,i+1> are members of N (set of node), there is
    an edge n1 => n2." *)

Notation "a ==> b" := (Successor a b)  (at level 0, right associativity) : ss_scope. 

Inductive Successor' : set Node -> relation Node :=
| succ' : forall N n m, In n N ->
                        In m N ->
                        n ==> m ->
                        Successor' N n m.
Hint Constructors Successor'.

Notation "a =[ N ]=> b" := (Successor' N a b)  (at level 0, right associativity) : ss_scope. 
Lemma succ'_in_l : forall N x y,
x =[N]=> y ->
In x N.
Proof.
  intros n x y edge.
  inversion edge; subst; auto.
Qed.
Hint Resolve succ'_in_l.

Lemma succ'_in_r : forall N x y,
x =[N]=> y ->
In y N.
Proof.
  intros n x y edge.
  inversion edge; subst; auto.
Qed.
Hint Resolve succ'_in_r.

Lemma succ'_imp_succ : forall N x y,
x =[N]=> y ->
x ==> y.
Proof.
  intros n x y edge.
  inversion edge; subst; auto.
Qed.
Hint Resolve succ'_imp_succ.

(* succecessor multi edge (not nec. immediate succecessor) *)
(* node's eventual succecessor -> node -> Prop *)
Definition StrandPath : relation Node := 
clos_trans Successor.
 (* [REF 1] Definition 2.3.4 pg 6
   "ni =>+ nj means that ni precedes nj (not necessarily immediately) on
    the same strand." *)
Hint Constructors clos_trans.

Notation "a ==>+ b" := (StrandPath a b)  (at level 0, right associativity) : ss_scope.

Definition StrandPath' (N: set Node) : relation Node :=
clos_trans (Successor' N) .

Notation "a =[ N ]=>+ b" := (StrandPath' N a b)  (at level 0, right associativity) : ss_scope. 

Lemma spath'_in_l : forall N x y,
x =[N]=>+ y ->
In x N.
Proof.
  intros n x y edge.
  induction edge; subst; eauto. 
Qed.
Hint Resolve spath'_in_l.

Lemma spath'_in_r : forall N x y,
x =[N]=>+ y ->
In y N.
Proof.
  intros n x y edge.
  induction edge; subst; eauto.
Qed.
Hint Resolve spath'_in_r.

Lemma spath'_imp_spath : forall N x y,
x =[N]=>+ y ->
x ==>+ y.
Proof.
  intros N x y edge.
  induction edge.
  constructor. eauto.
  eapply (t_trans Node Successor x y z IHedge1 IHedge2).
Qed.
Hint Resolve spath'_imp_spath.

Definition SSEdge : relation Node :=
union Comm Successor.
Hint Constructors or.

Notation "a =-> b" := (SSEdge a b) (at level 0, right associativity) : ss_scope.

Definition SSEdge' (N:set Node) : relation Node :=
union (Comm' N) (Successor' N).

Notation "a =[ N ]-> b" := (SSEdge' N a b) (at level 0, right associativity) : ss_scope.

Lemma ssedge'_in_l : forall N x y,
x =[N]-> y ->
In x N.
Proof.
  intros n x y edge.
  induction edge; subst; eauto. 
Qed.
Hint Resolve ssedge'_in_l.

Lemma ssedge'_in_r : forall N x y,
x =[N]-> y ->
In y N.
Proof.
  intros n x y edge.
  induction edge; subst; eauto.
Qed.
Hint Resolve ssedge'_in_r.

Lemma ssedge'_imp_ssedge : forall N x y,
x =[N]-> y ->
x =-> y.
Proof.
  intros N x y edge.
  induction edge.
  constructor. eauto.
  constructor 2. eauto.
Qed.
Hint Resolve ssedge'_imp_ssedge.

(* transitive closure of edges. *)
Definition SSPath : relation Node := 
clos_trans SSEdge.

Notation "a << b" := (SSPath a b) (at level 0, right associativity) : ss_scope.

Definition SSPath' (N:set Node) :=
clos_trans (SSEdge' N).

Notation "a <[ N ]< b" := (SSPath' N a b) (at level 0, right associativity) : ss_scope.

Lemma sspath'_in_l : forall N x y,
x <[N]< y ->
In x N.
Proof.
  intros N x y edge.
  induction edge; subst; eauto. 
Qed.
Hint Resolve sspath'_in_l.

Lemma sspath'_in_r : forall N x y,
x <[N]< y ->
In x N.
Proof.
  intros N x y edge.
  induction edge; subst; eauto.
Qed.
Hint Resolve sspath'_in_r.

Lemma sspath'_imp_sspath : forall N x y,
x <[N]< y ->
x << y.
Proof.
  intros N x y edge.
  induction edge.
  constructor. eauto.
  eapply (t_trans Node SSEdge x y z); eauto.
Qed.
Hint Resolve sspath'_imp_sspath.

(* transitive reflexive closure of edges. *)
Definition SSPathEq : relation Node :=
clos_refl_trans SSEdge.
Hint Constructors clos_refl_trans.

Notation "a <<* b" := (SSPathEq a b) (at level 0, right associativity) : ss_scope.

Inductive SSPathEq' (N:set Node) : relation Node :=
| sspatheq'_refl : forall n, In n N -> SSPathEq' N n n
| sspatheq'_trans : forall n m, n <[N]< m -> SSPathEq' N n m.
Hint Constructors SSPathEq'.

Notation "a <[ N ]<* b" := (SSPathEq' N a b) (at level 0, right associativity) : ss_scope.

Lemma sspatheq'_in_l : forall N x y,
x <[N]<* y ->
In x N.
Proof.
  intros N x y edge.
  induction edge; subst; eauto. 
Qed.
Hint Resolve sspatheq'_in_l.

Lemma sspatheq'_in_r : forall N x y,
x <[N]< y ->
In y N.
Proof.
  intros N x y edge.
  induction edge; subst; eauto.
Qed.
Hint Resolve sspatheq'_in_r.

Lemma sspatheq'_imp_sspatheq : forall N x y,
x <[N]<* y ->
x <<* y.
Proof.
  intros N x y edge.
  induction edge.
  apply rt_refl.
  induction H. constructor. eauto.
  eapply (rt_trans Node SSEdge x y z); eauto.
Qed.
Hint Resolve sspatheq'_imp_sspatheq.

(* In for members of pairs *)
Inductive InPair {X:Type} (x:X) (E:set (X*X)): Prop :=
| inp_l : (exists y, set_In (x,y) E)
          -> InPair x E
| inp_r : (exists y, set_In (y,x) E)
          -> InPair x E.
Hint Constructors InPair.

Record Bundle : Type := Bundle_def
{
  (* Prop 1 - A bundle is a finite portion of a strand space *)
  Nodes : set Node;
  Edges : set Edge;
  ValidEdges:
    (* N is the set of nodes incident with any edge in E *)
    (and (forall x, InPair x Edges -> In x Nodes)
    (* membership in Edge is equiv to an actual edge 
      (assuming set membership) *)
    (forall x y, In (x,y) Edges <-> x =[Nodes]-> y));
  PredIncl:
    (* Prop 3 - Predececcors on a strand are included *)
    (forall x y, In y Nodes -> x ==> y -> x =[Nodes]=> y);
  ExistsUniqueTx:   
    (forall z m, In z Nodes ->
                 smsg(z) = (- m) -> 
                 (* Prop 2 - there exists a transmitter *)
                 (exists x, (smsg(x) = (+ m)
                             /\ x -[Nodes]-> z
                             /\ In (x,z) Edges))
                 (* Prop 2 - a transmitter is unique *)
                 /\ (forall x y, x --> z ->
                                 y --> z ->
                                 x = y));
  (* Prop 4 *)
  Acyclic: forall x, ~ x <[Nodes]< x
}.

Notation "a -{ B }-> b" 
  := (Comm' (Nodes B) a b) (at level 0, right associativity)  : ss_scope.
Notation "a ={ B }=> b" 
  := (Successor' (Nodes B) a b)  (at level 0, right associativity) : ss_scope.
Notation "a ={ B }=>+ b" 
  := (StrandPath' (Nodes B) a b)  (at level 0, right associativity) : ss_scope.
Notation "a ={ B }-> b" 
  := (SSEdge' (Nodes B) a b) (at level 0, right associativity) : ss_scope.
Notation "a <{ B }< b" 
  := (SSPath' (Nodes B) a b) (at level 0, right associativity) : ss_scope.
Notation "a <{ B }<* b" 
  := (SSPathEq' (Nodes B) a b) (at level 0, right associativity) : ss_scope.

Definition set_minimal (N:set Node) (n:Node) : Prop :=
In n N /\
(forall x, ~ x <[N]< n).

Definition OccursIn (t:Msg) (n:Node) : Prop :=
 t <st msg(n).
 (* [REF 1] Definition 2.3.5 pg 6
   "An unsigned term t occurs in n iff t is a subterm of the term of n" *)
(* Bookmark *)

Section OriginAlt.
Require Import Ensembles.

(* As close to paper def as possible *)
Definition EntryPoint (n:Node) (I: Ensemble Msg) : Prop :=
(exists t, In Msg I t /\ smsg(n) = (+ t))
/\ forall n', n' << n -> ~ In Msg I (msg(n')).
 (* [REF 1] Definition 2.3.6 pg 6
   "Suppose I is a set of unsigned terms. The node n is an entrypoint for I
    iff term(n) = +t for some t in I, and forall n' s.t. n' =>+ n, term(n')
    is not in I." *)

(* As close to paper def as possible *)
Definition Origin_with_Ex_Set (t:Msg) (n:Node) : Prop :=
exists I, (forall t', t <st t' <-> In Msg I t')
/\ EntryPoint n I.
 (* [REF 1] Definition 2.3.7 pg 6
   "An unsigned term t originates on n iff n is an entry point
    for the set I = {t' : t is a subterm of t'}" *)
End OriginAlt.

Definition Origin (t:Msg) (n:Node) : Prop :=
is_tx n
/\ t <st msg(n)
/\ forall n', n' << n -> ~t <st msg(n').

Definition UniqOrigin (t:Msg) : Prop :=
exists n, Origin t n
/\ forall m, Origin t m -> n = m.
 (* [REF 1] Definition 2.3.8 pg 7
   "An unsigned term t is uniquely originating iff t originates on
    a unique n." *)

(* Axiom 1 -- provable in this context *)
Theorem free_encryption : forall m1 m2 k1 k2,
{m1}^[k1] = {m2}^[k2] -> m1 = m2 /\ k1 = k2.
Proof.
  intros m m' k k' encreq.
  inversion encreq. split; auto. 
Qed.
 (* [REF 1] Definition 2.4 Axiom 1 pg 10
   "A cipher text can be regarded as a cipher text in
   just one way." 

   NOTE: This was an Axiom in the paper... but in Coq
   with these definitions this is provable... or
   inherently implied by the definitions/structures
*)

(* Axiom 2 -- provable in this context *)
Theorem free_term_algebra : forall m m' n n' k k' t,
(m * n = m' * n' -> m = m' /\ n = n')
/\ m * n <> {m'}^[k]
/\ (#k) <> m * n
/\ (!t) <> m * n
/\ (#k) <> {m}^[k']
/\ (!t) <> {m}^[k].
Proof.
  intros m m' n n' k k' t;
  split. intros eq. inversion eq; auto. 
  split. intros F. inversion F.
  split. intros F. inversion F.
  split. intros F. inversion F.
  split. intros F. inversion F.
  intros F. inversion F.
Qed.

Fixpoint width (m:Msg) : nat :=
match m with
| msg_text _ => 1
| msg_key _ => 1
| msg_encr _  _ => 1
| msg_join x y => width x + width y
end.
(* [REF 1] Definition 2.10 *)

(* Meta Strand Space properties/objects *)
(* [REF 1] 
           Page 4 "One may think of a strand space as containing all the 
                   legitimate executions of the protocol expected within 
                   its useful lifetime, together with all the actions that
                   a penetrator might apply to messages contained in those
                   executions."

           Definition 2.2 pg 6 "A strand space over A (set of possible msgs) 
           is a set E with a trace mapping tr : E -> list smsg" *)

Variable Protocol : set Strand.
Definition RegularStrand (s:Strand) := set_In s Protocol.
Definition RegularNode (n:Node) := RegularStrand (strand n).
Definition PenetratorStrand (s:Strand) := ~RegularStrand s.
Definition PenetratorNode (n:Node) := ~RegularNode n.
Variable PenetratorModel : Strand -> Prop.
 Hypothesis penetrator_behaviour : 
   forall s, PenetratorStrand s -> PenetratorModel s.

(* Keys known to penetrators *)
Variable PKeys : set Key.

(* Texts known to penetrators (allows for nonces, etc...) *)
Variable PTexts : set Text.

Open Scope list_scope.
Import ListNotations.

Inductive DolevYao : Strand -> Prop :=
| DY_M : forall s t, 
           ~ set_In t PTexts ->
           s = [ (+(!t)) ] -> 
           DolevYao s
| DY_F : forall s g, 
           s = [(-g)] -> 
           DolevYao s
| DY_T : forall s g,
           s = [(-g) ; (+g) ; (+g)] ->
           DolevYao s
| DY_C : forall s g h,
           s = [(-g) ; (-h) ; (+g*h)] ->
           DolevYao s
| DY_S : forall s g h,
           s = [(-g*h) ; (+g) ; (+h)] ->
           DolevYao s
| DY_K : forall s k,
           set_In k PKeys ->
           s = [(+ (#k))] ->
           DolevYao s
| DY_E : forall s h k,
           s = [(- (#k)) ; (-h) ; (+ {h}^[k])] ->
           DolevYao s
| DY_D : forall s h k k',
           Inv k' k ->
           s = [(- (#k')) ; (- {h}^[k]) ; (+h)] ->
           DolevYao s.
(* [REF 1] Definition 3.1
    The set of atomic actions/traces a penetrator
    may perform. *)

End SS.

Export SS.