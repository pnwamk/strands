(** * strands.v: Basic Strand Space Definitions *)

(* Created by Andrew Kent (amk.kent@gmail.com) 
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

Require Import List Arith Peano_dec Omega Ensembles Finite_sets.

(* Represent atomic messages, *)
Variable Text : Set.

(* representing kryptographic key *)
Variable Key : Set.
(* TODO - injective, unary operation (inv : key -> key)
          Or in Coq would this make more sense
          instead as  key -> key -> Prop?
          The text notes the ability to handle
          both symmetric and asymmetric keys... *)

(* TODO? For the analysis of the NSL protocol, they 
   include an extension of term/message definitions
   that includes names and public keys which are
   associated with a specific name.*)

(* message or term *)
Inductive Msg : Type :=
| msg_text : Text -> Msg
| msg_app : Msg -> Msg -> Msg 
| msg_crypt : Key -> Msg -> Msg.
(* [REF 1] Section 2.1 pg 5 
           Section 2.3 pg 9 *)
(* [REF 2] pg 4 paragraph 3 (detains of encryption and subterms) *)
Hint Constructors Msg.

(* subterm relationship for messages *)
(* subterm -> larger encapsulating term -> Prop *)
Inductive Subterm : Msg -> Msg -> Prop :=
| st_refl : forall m, Subterm m m
(* | stcryp : forall a g, subterm a g -> subterm a encrpt(g)  *)
| st_app_l : forall st l r, 
               Subterm st l -> Subterm st (msg_app l r)
| st_app_r : forall st l r, 
               Subterm st r -> Subterm st (msg_app l r)
| st_crpyt : forall st t k, 
              Subterm st t -> Subterm st (msg_crypt k t).
(* [REF 1] Definition 2.1 pg 6 and Definition 2.11 *)
Hint Constructors Subterm.

(* signed message, + (tx) or - (rx) *)
Inductive SMsg : Type := 
| tx : Msg -> SMsg
| rx : Msg -> SMsg.
(* [REF 1] Definition 2.1 pg 6 
   They are defined as a pair, w/ the first member being in {+, -} 
   and the second a signed message. *)
Hint Constructors SMsg.

(* strand *)
Definition Strand : Type := list SMsg.
(* [REF 1] First sentence of Abstract: "sequence of events"  
   Haven't hit a better def, and they start using strands
   pretty early so I'm rolling with this. *)

(*
Definition strand_in_set (s:strand) (ss:set strand) : bool := 
  set_mem strand_eq_dec s ss. *)

Definition Strands := Ensemble Strand.
Definition Msgs := Ensemble Msg.
Definition SMsgs := Ensemble SMsg.

(* strand space *)
Inductive StrandSpace : Type :=
| strandspace : Msgs -> Strands -> StrandSpace.
(* [REF 1] Definition 2.2 pg 6 "A strand space over A (set of possible msgs) 
           is a set E with a trace mapping tr : E -> list smsg" *)

Definition SS_msgs (ss:StrandSpace) : Msgs :=
 match ss with
  | strandspace m_set s_set => m_set
 end.

Definition SS_strands (ss:StrandSpace) : Strands :=
 match ss with
  | strandspace m_set s_set => s_set
 end.


(* node in a strand space *)
Definition Node : Type := {n: (prod Strand nat) | (snd n) < (length (fst n))}.
(* [REF 1] Definition 2.3.1 pg 6
   -"A node is a pair <s,i> where s is a strand and i a nat in [0, (length s))"
     NOTE: I changed it to be 0 based instead of 1 based sequences
   -"node <s,i> belongs to strand s"
   -"Every node belongs to a unique strand" *)

Definition Edge : Type := (prod Node Node).
Definition Nodes := Ensemble Node.
Definition Edges := Ensemble Edge.

(* index of a node *)
Definition Node_index (n:Node) : nat :=
  match n with
    | exist npair _ 
      => snd npair
  end.
(* [REF 1] Definition 2.3.2 pg 6
   "If n = <s,i> then index(n) = i." *)

(* strand of a node *)
Definition Node_strand (n:Node) : Strand :=
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

Lemma nth_error_len : forall {X:Type} {l:list X} i,
None = nth_error l i -> (length l) <= i.
Proof.
  intros X l i. generalize dependent l.
  induction i. 

  intros l H.
  unfold nth_error in H.
  unfold error in H.
  destruct l.
  auto. inversion H.

  intros l' H.
  destruct l'.
  simpl; omega.
  inversion H.
  apply IHi in H1.
  simpl. omega. 
Qed.

Theorem Node_smsg_valid : forall (n:Node),
{m:SMsg | Some m = Node_smsg_option n}.
(* exists (m:smsg), Some m = (n_smsg_option n). *)
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
Definition Node_smsg (n:Node) : SMsg :=
 match Node_smsg_valid n with
     | exist m _ => m
 end.

(* unsigned message of a node *)
Fixpoint Node_msg (n:Node) : Msg :=
  match Node_smsg n with
    | tx t => t
    | rx t => t
  end. 
(* [REF 1] Definition 2.3.2 pg 6
   "Define uns_term(n) to be the unsigned part of the ith signed term 
    of the trace of s." *)

(* To reason about the set of nodes in a strand space *)
Definition NodeInSS (n:Node) (ss:StrandSpace) : Prop := 
 In Strand (SS_strands ss) (Node_strand n).
(* [REF 1] Definition 2.3.1 pg 6
   The reference to the "set of nodes (N) in a given strand space." *)

(* Set of all nodes in a strand space *)
Definition NodeSet (ss:StrandSpace) : Type := 
{ns: Nodes | forall n, (NodeInSS n ss)  <-> In Node ns n}.
(* [REF 1] Definition 2.3.1 pg 6
   The set of nodes (in a strand space) is denoted by N. *)

Inductive CommEdge : Node -> Node -> Prop :=
| c_edge :  forall n m, (exists a, (and ((Node_smsg n) = (tx a)) 
                                 ((Node_smsg m) = (rx a))))
                             -> CommEdge n m.
(* [REF 1] Definition 2.3.3 pg 6
   "there is an edge n1 -> n2 iff term(n1) = +a and term(n2) = -a." *)

(* predecessor edge *)
(* node's direct predecessor -> node -> Prop *)
Inductive PredEdge : Node -> Node -> Prop :=
| p_edge : forall i j, Node_strand i = Node_strand j 
                      -> (Node_index i) + 1 = (Node_index j) 
                      -> PredEdge i j.
(* [REF 1] Definition 2.3.4 pg 6
   "When n1= <s,i> and n2=<s,i+1> are members of N (set of node), there is
    an edge n1 => n2." *)

(* predecessor multi edge (not nec. immediate predecessor) *)
(* node's predecessor -> node -> Prop *)
Inductive PredPath : Node -> Node -> Prop :=
| ppath_step : forall i j, PredEdge i j -> PredPath i j
| ppath_path : forall i j k, PredEdge i j -> PredPath j k -> PredPath i k.
(* [REF 1] Definition 2.3.4 pg 6
   "ni =>+ nj means that ni precedes nj (not necessarily immediately) on
    the same strand." *)

(* A Path (traversing either edge Types) of length
   1 or more. *)
Inductive FwdPath : Node -> Node -> Prop :=
| path_comm : forall x y, CommEdge x y -> FwdPath x y
| path_pred : forall x y, PredPath x y -> FwdPath x y
| path_comm_path : forall x y z, CommEdge x y -> FwdPath y z -> FwdPath x z
| path_pred_path : forall x y z, PredPath x y -> FwdPath y z -> FwdPath x z.

Inductive OccursIn : Msg -> Node -> Prop :=
| occurs_in : forall m n, Subterm m (Node_msg n) -> OccursIn m n.
(* [REF 1] Definition 2.3.5 pg  6
   "An unsigned term m occurs in a node n iff m is a subterm of term(n). " *)

(* signifies the origin of a msg. *)
Inductive EntryPoint : Node -> Msgs -> Prop :=
 | entrypoint :  forall n I, 
    (and (exists m, (and ((Node_smsg n) = (tx m)) 
                         (In Msg I m)))
         (forall n', (PredPath n' n) 
                     -> ~(In Msg I (Node_msg n'))))
    -> EntryPoint n I.
(* [REF 1] Definition 2.3.6 pg 6
   "The node n in N is an entry point for I (a set of unsigned terms) iff
    term(n) = +t for some t in I, and whenever n' =>+ n term(n') is not in I."*)

(* where an unsigned term originates, what node *)
Inductive OriginateAt : Msg -> Node -> Prop :=
| orig_at : forall m n, 
             (exists I, (and (EntryPoint n I)
                             (forall m', In Msg I m -> Subterm m m')))
             -> OriginateAt m n.
(* [REF 1] Definition 2.3.7 pg 6
   "An unsigned term t originates on n in N iff n is an entry point for 
    the set I = {t' | t is a subterm of t'}."*)

(* uniquely originating term def, useful for nonces or session keys *)
Inductive UniqOrigin : Msg -> Prop :=
| uniq_orig : forall t, (exists n, 
              (forall n', OriginateAt t n' -> n = n') )
              -> UniqOrigin t.
(* [REF 1] Definition 2.3.8 pg 7 
   "unsigned term t is uniquely originating iff t originates on a unique
    n in N." *)

Inductive InP (X:Type) : Ensemble (X*X) -> X -> Prop :=
| inp_l : forall E x,
           (exists y, In (X*X) E (x,y))
           -> InP X E x
| inp_r : forall E x,
           (exists y, In (X*X) E (y,x))
           -> InP X E x.

Inductive ValidNodes : Nodes -> Prop :=
| vn : forall N, Finite Node N -> ValidNodes N.

Inductive ValidEdges : Nodes -> Edges -> Prop :=
| ve : forall N E,
         (and (Finite Edge E) 
              (forall n, InP Node E n -> In Node N n)) ->
         ValidEdges N E.

Inductive Acyclic : Nodes -> Prop :=
| acyclic : forall N,
 (forall n, (and (In Node N n) 
                (~ FwdPath n n))) -> Acyclic N.

(* Definition bundle : *)

Definition EdgesWitness N2 P :=
 (forall n m, In (Node*Node) N2 (n,m) -> P n m).

(* *)
Inductive Bundle : Nodes -> Edges -> Edges -> Prop :=
| ssbundle : forall (N:Nodes) (CE PE:Edges),
               Finite Node N -> 
               Finite Edge CE -> 
               Finite Edge PE ->
               ValidEdges N CE ->
               ValidEdges N PE ->
               EdgesWitness CE CommEdge ->
               EdgesWitness PE PredEdge ->
               Acyclic N -> 
               Bundle N CE PE.
(* [REF 1] Definition 2.4 pg 7 
    1) The subgraph is finite
    2) If n2 is in Nodes and is a rx-ing message, then there
       is a unique n1 in CE such that n1 transmist that message
       to n2
    3) If n2 is in Nodes and PredEdge n1 n2 then that edge
       is in PE.
    4) The subgraph is acyclic 
    
    -Additionally
     - A strand may send or tx or rx a msg, but not 
       both simultaneously (given by def of SMsg)
     - When a strand rx a msg, there is a unique node 
       tx that msg
     - when a strand transmits a msg, many strands may
       immediately rx that msg
*)
 
