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
Require Import ProofIrrelevance.
Require Import CoLoRRelDec CoLoRRelSub.
Require Import Ensembles.
Require Import strictorder set_rep_equiv util.
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
Inductive Term : Type :=
| term_text : Text -> Term
| term_key  : Key  -> Term
| term_join : Term  -> Term -> Term 
| term_encr : Key  -> Term -> Term.
(* [REF 1] Section 2.1 pg 5 
           Section 2.3 pg 9 *)
(* [REF 2] pg 4 paragraph 3 (details of encryption and subterms) *)
Hint Constructors Term.

Definition eq_term_dec : forall x y : Term,  
  {x = y} + {x <> y}.
Proof. decide equality. Qed.

Notation "(! x )" := (term_text x) : ss_scope. 
Notation "(# k )" := (term_key k) : ss_scope.
Notation "x * y" := (term_join x y) (at level 40, left associativity) : ss_scope.
Notation "{ m }^[ k ] " := (term_encr k m) (at level 0, m at level 99, k at level 99) : ss_scope.

Open Scope ss_scope.

(* subterm relationship for messages *)
(* subterm -> encompassing term -> Prop *)
Inductive Subterm : relation Term :=
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
Inductive STerm : Type := 
| term_tx : Term -> STerm
| term_rx : Term -> STerm.
(* [REF 1] Definition 2.1 pg 6 
   They are defined as a pair, w/ the first member being in {+, -} 
   and the second a signed message. *)
Hint Constructors STerm.

Definition eq_sterm_dec : forall x y : STerm,  
  {x = y} + {x <> y}.
Proof. intros. decide equality; apply eq_term_dec. Qed.

Notation "(+ x )" := (term_tx x) : ss_scope.
Notation "(- x )" := (term_rx x) : ss_scope.

(* strand *)
Definition Strand : Type := list STerm.
(* [REF 1] First sentence of Abstract: "sequence of events"  
   Haven't hit a better def, and they start using strands
   pretty early so I'm rolling with this. *)

Definition eq_strand_dec : forall x y : Strand,  
  {x = y} + {x <> y}.
Proof. intros. decide equality; apply eq_sterm_dec. Qed.

(* node in a strand space *)
Definition Node : Type := {n: (Strand * nat) | (snd n) < (length (fst n))}.
(* [REF 1] Definition 2.3.1 pg 6
   -"A node is a pair <s,i> where s is a strand and i a nat in [0, (length s))"
     NOTE: changed to be 0 based instead of 1 based sequences
   -"node <s,i> belongs to strand s"
   -"Every node belongs to a unique strand" *)

Definition eq_node_dec : forall x y : Node,
 {x = y} + {x <> y}.
Proof.
  intros [[xs xn] xp] [[ys yn] yp].
  destruct (eq_strand_dec xs ys) as [EQs | NEQs]; subst.
  destruct (eq_nat_dec xn yn) as [EQn | NEQn]; subst.
  left. rewrite (proof_irrelevance (lt yn (length ys)) xp yp). reflexivity.

  right. intros C. inversion C. auto.
  right. intros C. inversion C. auto.
Qed.
Hint Resolve eq_node_dec.


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
Fixpoint Node_sterm_option (n:Node) : (option STerm) :=
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

Lemma node_sterm_valid :
forall (n:Node), {m:STerm | Some m = Node_sterm_option n}.
Proof.
  intros n.
  remember (Node_sterm_option n) as funcall.
  destruct n. destruct funcall.  
  exists s. reflexivity.

  unfold Node_sterm_option in Heqfuncall.
  destruct x. simpl in l.
  apply nth_error_len in Heqfuncall.
  omega.
Qed.

(* signed message of a node *)
Definition sterm (n:Node) : STerm :=
  match node_sterm_valid n with
    | exist m _ => m
  end.

Definition sterm_term (s:STerm) : Term :=
  match s with
    | (+t) => t
    | (-t) => t
  end. 

(* unsigned message of a node *)
Definition term (n:Node) : Term :=
  sterm_term (sterm n).
(* [REF 1] Definition 2.3.2 pg 6
   "Define uns_term(n) to be the unsigned part of the ith signed term 
    of the trace of s." *)

Definition is_tx (n:Node) : Prop :=
exists t, sterm n = (+ t).

Definition is_rx (n:Node) : Prop :=
exists t, sterm n = (- t).


Inductive Comm : relation Node :=
| comm :  forall n m t, ((sterm(n) = (+t) 
                          /\ sterm(m) = (-t))
                         /\ strand(n) <> strand(m))
                        -> Comm n m.
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
| comm' : forall N n m, set_In n N ->
                        set_In m N ->
                        n --> m ->
                        Comm' N n m.

Notation "a -[ N ]-> b" := (Comm' N a b) (at level 0, right associativity)  : ss_scope.


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
| succ' : forall N n m, set_In n N ->
                        set_In m N ->
                        n ==> m ->
                        Successor' N n m.

Notation "a =[ N ]=> b" := (Successor' N a b)  (at level 0, right associativity) : ss_scope. 

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

Definition SSEdge : relation Node :=
union Comm Successor.
Hint Constructors or.

Notation "a =-> b" := (SSEdge a b) (at level 0, right associativity) : ss_scope.

Definition SSEdge' (N:set Node) : relation Node :=
union (Comm' N) (Successor' N).

Notation "a =[ N ]-> b" := (SSEdge' N a b) (at level 0, right associativity) : ss_scope.

(* transitive closure of edges. *)
Definition SSPath : relation Node := 
clos_trans SSEdge.

Notation "a << b" := (SSPath a b) (at level 0, right associativity) : ss_scope.

Definition SSPath' (N:set Node) :=
clos_trans (SSEdge' N).

Notation "a <[ N ]< b" := (SSPath' N a b) (at level 0, right associativity) : ss_scope.

(* transitive reflexive closure of edges. *)
Definition SSPathEq : relation Node :=
clos_refl_trans SSEdge.

Notation "a <<* b" := (SSPathEq a b) (at level 0, right associativity) : ss_scope.

Inductive SSPathEq' (N:set Node) : relation Node :=
| sspatheq'_refl : forall n, set_In n N -> SSPathEq' N n n
| sspatheq'_trans : forall n m, n <[N]< m -> SSPathEq' N n m.

Notation "a <[ N ]<* b" := (SSPathEq' N a b) (at level 0, right associativity) : ss_scope.

(* In for members of pairs *)
Inductive InPair {X:Type} (x:X) (E:set (X*X)): Prop :=
| inp_l : (exists y, set_In (x,y) E)
          -> InPair x E
| inp_r : (exists y, set_In (y,x) E)
          -> InPair x E.
Hint Constructors InPair.

Record Bundle : Type := 
{
  (* Prop 1 - A bundle is a finite portion of a strand space *)
  Nodes : set Node;
  Edges : set Edge;
  NodesSetP : NoDup Nodes;
  EdgesSetP : NoDup Edges;
  ValidEdges:
    (* N is the set of nodes incident with any edge in E *)
    (and (forall x, InPair x Edges -> set_In x Nodes)
    (* membership in Edge is equiv to an actual edge 
      (assuming set membership) *)
    (forall x y, set_In (x,y) Edges <-> x =[Nodes]-> y));
  PredIncl:
    (* Prop 3 - Predececcors on a strand are included *)
    (forall x y, set_In y Nodes -> x ==> y -> x =[Nodes]=> y);
  TxIncl:
    (* Prop 2 - Transmitter is in Bundle *)
    (forall x y, set_In y Nodes -> x --> y -> x -[Nodes]-> y);
  ExistsUniqueTx:
    (* Prop 2 - Rx implies there exists a unique Tx *)
    (forall z m, set_In z Nodes ->
                 sterm(z) = (- m) -> 
                 (* there exists a transmitter *)
                 (exists x, x -[Nodes]-> z)
                 (* Prop 2 - a transmitter is unique *)
                 /\ (forall x y, x --> z ->
                                 y --> z ->
                                 x = y));
  (* Prop 4 - The Bundle is acyclic*)
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

Definition bundle_height (B:Bundle) (s:Strand) (h:nat) : Prop :=
forall n:Node, index n < h ->
               strand n = s ->
               set_In n (Nodes B).

Definition set_minimal (B:Bundle) (N:set Node) (n:Node) : Prop :=
subset N (Nodes B) /\
set_In n N /\ 
forall n', set_In n' N -> ~ n' <{B}< n.

Definition OccursIn (t:Term) (n:Node) : Prop :=
 t <st term(n).
 (* [REF 1] Definition 2.3.5 pg 6
   "An unsigned term t occurs in n iff t is a subterm of the term of n" *)

Definition EntryPoint (n:Node) (tP: Term -> Prop) : Prop := 
tP (term n) 
/\ is_tx n
/\ forall n', n' ==>+ n -> ~ tP (term n').

Definition Origin (t:Term) (n:Node) : Prop :=
EntryPoint n (fun t' => t <st t').

Definition SecretIn (t:Term) (B:Bundle) : Prop :=
forall n, set_In n (Nodes B) ->
          term n <> t.
(* [REF 1] pg 16
   "A value x is secret in a bundle C if for every
    n in C, term(n) <> x." *)

Definition UniqOrigin (t:Term) : Prop :=
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

Fixpoint width (m:Term) : nat :=
match m with
| term_text _ => 1
| term_key _ => 1
| term_encr _  _ => 1
| term_join x y => width x + width y
end.
(* [REF 1] Definition 2.10 *)

(* Meta Strand Space properties/objects *)
(* [REF 1] 
           Page 4 "One may think of a strand space as containing all the 
                   legitimate executions of the protocol expected within 
                   its useful lifetime, together with all the actions that
                   a penetrator might apply to messages contained in those
                   executions."

           Definition 2.2 pg 6 "A strand space over A (set of possible terms) 
           is a set E with a trace mapping tr : E -> list sterm" *)

Variable Protocol : set Strand.
Definition RegularStrand (s:Strand) := set_In s Protocol.
Definition RegularNode (n:Node) := RegularStrand (strand n).
Variable Penetrators : Ensemble Strand.
Definition PenetratorStrand (s:Strand) := In Strand Penetrators s.
Definition PenetratorNode (n:Node) := PenetratorStrand (strand n).
Variable PenetratorModel : Strand -> Prop.
 Hypothesis penetrator_behaviour : 
   forall s, PenetratorStrand s -> PenetratorModel s.

Hypothesis strand_alignment : forall s : Strand, 
RegularStrand s \/ PenetratorStrand s.

(* Hidden Keys, not initially known to penetrators *)
Variable HKeys : set Key.

(* Hidden Texts, not initially known to penetrators (allows for nonces, etc...) *)
Variable HTexts : set Text.

Open Scope list_scope.
Import ListNotations.

Inductive StandardPenetrator : Strand -> Prop :=
| P_M : forall s t, 
          ~ set_In t HTexts ->
          s = [ (+(!t)) ] -> 
          StandardPenetrator s
| P_F : forall s g, 
          s = [(-g)] -> 
          StandardPenetrator s
| P_T : forall s g,
          s = [(-g) ; (+g) ; (+g)] ->
          StandardPenetrator s
| P_C : forall s g h,
          s = [(-g) ; (-h) ; (+g*h)] ->
          StandardPenetrator s
| P_S : forall s g h,
          s = [(-g*h) ; (+g) ; (+h)] ->
          StandardPenetrator s
| P_K : forall s k,
          ~set_In k HKeys ->
          s = [(+ (#k))] ->
          StandardPenetrator s
| P_E : forall s h k,
          s = [(- (#k)) ; (-h) ; (+ {h}^[k])] ->
          StandardPenetrator s
| P_D : forall s h k k',
          Inv k' k ->
          s = [(- (#k')) ; (- {h}^[k]) ; (+h)] ->
          StandardPenetrator s.
(* [REF 1] Definition 3.1
    The set of atomic actions/traces a penetrator
    may perform. *)


Definition term_filter 
           {MP : Term -> Prop}
           (MPdec : forall x, {MP x} + {~ MP x})
           (s : set Node) : set Node :=
  filter (fun n => if MPdec (term n)
                   then true 
                   else false) 
         s.

End SS.

Export SS.