(** * strands2.v: Basic Strand Space Definitions *)

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

Require Import List ListSet Omega ProofIrrelevance Relations.
Require Export util.

(* Represent atomic messages, *)
Variable Text : Set.
Variable text_eq_dec : forall (x y:Text), {x = y} + {x <> y}.
Hint Resolve text_eq_dec.
(* [REF 1] pg 9
   That which "represent[s] the atomic messages." *)

(* representing kryptographic key *)
Variable Key : Set.
(* [REF 1] pg 9 
   "cryptographic keys disjoint from [the atomic messages]" *)
Variable key_eq_dec : forall (x y:Key), {x = y} + {x <> y}.
Hint Resolve key_eq_dec. 
(* TODO: operator inv : Key -> Key. For assymmetric crypto produces the
   inverse, for symmetric is the id function. *)

(* TODO? For the analysis of the NSL protocol, they 
   include an extension of term/message definitions
   that includes names and public keys which are
   associated with a specific name.*)

(* message or term *)
Inductive Msg : Type :=
| msg_text : Text -> Msg
| msg_app : Msg -> Msg -> Msg 
| msg_crypt : Msg -> Key -> Msg.
(* [REF 1] Section 2.1 pg 5 
           Section 2.3 pg 9 *)
(* [REF 2] pg 4 paragraph 3 (detains of encryption and subterms) *)
Hint Constructors Msg.

Definition Msgs := set Msg.

Definition msg_eq_dec : forall x y : Msg,  
  {x = y} + {x <> y}.
Proof.
  decide equality.
Qed.
Hint Resolve msg_eq_dec.


(* subterm relationship for messages *)
(* subterm -> larger encapsulating term -> Prop *)
Inductive Subterm : Msg -> Msg -> Prop :=
| st_refl : forall m, Subterm m m
| st_app_l : forall st l r, 
               Subterm st l -> Subterm st (msg_app l r)
| st_app_r : forall st l r, 
               Subterm st r -> Subterm st (msg_app l r)
| st_crpyt : forall st t k, 
               Subterm st t -> Subterm st (msg_crypt t k).
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

Definition SMsgs := set SMsg.

Definition smsg_eq_dec : forall x y : SMsg,  
  {x = y} + {x <> y}.
Proof.
 intros. decide equality.
Qed. 
Hint Resolve smsg_eq_dec.

(* strand *)
Definition Strand : Type := list SMsg.
(* [REF 1] First sentence of Abstract: "sequence of events"  
   Haven't hit a better def, and they start using strands
   pretty early so I'm rolling with this. *)

Definition strand_eq_dec : forall x y : Strand,  
  {x = y} + {x <> y}.
Proof.
 intros. decide equality.
Qed.
Hint Resolve strand_eq_dec.

Definition Strands := set Strand.

(* strand space *)
Inductive StrandSpace : Type :=
| strandspace : Msgs -> Strands -> StrandSpace.
(* [REF 1] Definition 2.2 pg 6 "A strand space over A (set of possible msgs) 
           is a set E with a trace mapping tr : E -> list smsg" *)
Hint Constructors StrandSpace.

Definition SS_msgs (ss:StrandSpace) : Msgs :=
  match ss with
    | strandspace m_set s_set => m_set
  end.

Definition SS_strands (ss:StrandSpace) : Strands :=
  match ss with
    | strandspace m_set s_set => s_set
  end.


(* node in a strand space *)
Definition Node : Type := {n: (Strand * nat) | (snd n) < (length (fst n))}.
(* [REF 1] Definition 2.3.1 pg 6
   -"A node is a pair <s,i> where s is a strand and i a nat in [0, (length s))"
     NOTE: I changed it to be 0 based instead of 1 based sequences
   -"node <s,i> belongs to strand s"
   -"Every node belongs to a unique strand" *)

Definition node_eq_dec : forall x y : Node,
 {x = y} + {x <> y}.
Proof.
  intros [[xs xn] xp] [[ys yn] yp].
  destruct (strand_eq_dec xs ys) as [EQs | NEQs]; subst.
  destruct (eq_nat_dec xn yn) as [EQn | NEQn]; subst.
  left. rewrite (proof_irrelevance (lt yn (length ys)) xp yp). reflexivity.

  right. intros C. inversion C. auto.
  right. intros C. inversion C. auto.
Qed.

Definition Nodes := set Node.

Definition Edge : Type := (prod Node Node).
Definition Edges := set Edge.

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
  Case "length <= 0".
    intros l H.
    unfold nth_error in H. unfold error in H.
    destruct l. auto. inversion H.
  Case "length <= S i".
    intros l' H.
    destruct l'. simpl; omega.
    inversion H. apply IHi in H1. simpl. omega. 
Qed.

Theorem node_smsg_valid : 
  forall (n:Node), {m:SMsg | Some m = Node_smsg_option n}.
Proof.
  intros n.
  remember (Node_smsg_option n) as funcall.
  destruct n. destruct funcall.  
  exists s. reflexivity.

  unfold Node_smsg_option in Heqfuncall.
  destruct x. simpl in l.
  apply nth_error_len in Heqfuncall. omega.
Qed.

(* signed message of a node *)
Definition Node_smsg (n:Node) : SMsg :=
  match node_smsg_valid n with
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

Lemma node_imp_strand_nonempty : forall s n,
Node_strand n = s ->
length s > 0.
Proof.
  intros s n Hns.
  destruct n. destruct x. destruct n. simpl in l.
  destruct s.
  assert (s0 = nil). auto.
  subst. inversion l. simpl. omega.
  simpl in l. 
  assert (s0 = s). auto.
  rewrite <- H. omega.
Qed.

Inductive CommEdge : relation Node :=
| comm_edge :  forall x y t, ((Node_smsg x = tx t /\
                           Node_smsg y = rx t)
                        /\ Node_strand x <> Node_strand y)
                        -> CommEdge x y.
Hint Constructors CommEdge.
(* [REF 1] Definition 2.3.3 pg 6
   "there is an edge n1 -> n2 iff term(n1) = +a and term(n2) = -a ... 
   recording a potential causal link between those strands**"
  **We take this to mean a causal link between two *different* 
  strands, as this is logical, and fits numerous informal 
  descriptions in the literature such as "A strand (process) 
  may send or receive a message but not both at the 
  same time" and given the majority of transmissions travel 
  close to the speed of light a strand cannot receive
  its own transmission by any reasonable measure. *)

(* A CommEdge between nodes, where the set the nodes belong to is specified. *)
Inductive CommSetEdge : Nodes -> relation Node :=
| comm_sedge : forall N x y,
              In x N ->
              In y N ->
              CommEdge x y ->
              CommSetEdge N x y.
Hint Constructors CommSetEdge.

Theorem comm_edge_imp_neq : forall n m,
 CommEdge n m -> n <> m.
 Proof.
   intros n m Hedge Hneq. subst.
   inversion Hedge as [contra_s contra_i]; subst.
   apply H. reflexivity.
 Qed.  
Hint Resolve comm_edge_imp_neq.

Theorem comm_edge_refl_false : forall m,
 CommEdge m m -> False.
Proof.
  intros m edge.
  apply comm_edge_imp_neq in edge.
  apply edge. reflexivity.
Qed.

Theorem comm_edge_antisymmetry : 
antisymmetric Node CommEdge.
Proof.
  intros n m Hcomm contra.
  inversion Hcomm; subst.
  inversion contra; subst.
  destruct H as [H Hneq_s]. destruct H as [Htx1 Hrx1].
  destruct H0 as [H Hneq_s2]. destruct H as [Htx2 Hrx2].
  rewrite Htx2 in Hrx1. inversion Hrx1.
Qed.
Hint Resolve comm_edge_antisymmetry.

(* strand edge *)
(* Edge representing a node, and the node proceeding it on the same strand. *)
Inductive StrandEdge : relation Node :=
| strand_edge : forall i j, Node_strand i = Node_strand j 
                       -> (Node_index i) + 1 = Node_index j 
                       -> StrandEdge i j.
(* [REF 1] Definition 2.3.4 pg 6
   "When n1= <s,i> and n2=<s,i+1> are members of N (set of node), there is
    an edge n1 => n2." *)

(* An Strand Edge between nodes, where the set the nodes belong to is specified. *)
Inductive StrandSetEdge : Nodes -> relation Node :=
| strand_sedge : forall N x y,
              In x N ->
              In y N ->
              StrandEdge x y ->
              StrandSetEdge N x y.
Hint Constructors StrandSetEdge.

Theorem strand_edge_imp_neq : forall (n m: Node),
StrandEdge n m -> n <> m.
Proof.
  intros n m Hedge Heq.
  subst. inversion Hedge; subst.
  omega.
Qed.
Hint Resolve strand_edge_imp_neq.

Theorem strand_edge_refl_false : forall m,
StrandEdge m m -> False.
Proof.
  intros m edge.
  apply strand_edge_imp_neq in edge.
  apply edge. reflexivity.
Qed.

Theorem strand_edge_antisymmetry :
antisymmetric Node StrandEdge.
Proof.
  intros n m Hpe1 Hpe2.
  destruct Hpe1. destruct Hpe2.
  rewrite <- H0 in H2. omega.
Qed.
Hint Resolve strand_edge_antisymmetry.

(* A Path representing the transitive closure of StrandEdge. *)
Definition StrandPath (l:list Node) : RPath StrandEdge l.

(* A Path representing the transitive closure of PredEdge, starting from x. *)
Definition StrandPath' (l: list Node) (x: Node) : RPath' StrandEdge l x.

(* A Path representing a path of PredEdges from x to y. *)
Definition StrandPath'' (l: list Node) (x y: Node) : RPath'' StrandEdge l x y.

Definition XEdge : relation Node := 
union Node CommEdge StrandEdge.

Inductive XSetEdge : Nodes -> relation Node :=
| x_sedge : forall N x y,
               In x N ->
               In y N ->
               XEdge x y ->
               XSetEdge N x y.

Inductive XEdgeEq : relation Node :=
| x_edge_eq_refl : forall x, XEdgeEq x x
| x_edge_eq_step : forall x y, XEdge x y -> XEdgeEq x y.

Inductive XSetEdgeEq : Nodes -> relation Node :=
| x_sedge_eq : forall N x y,
               In x N ->
               In y N ->
               XEdgeEq x y ->
               XSetEdgeEq N x y.

Theorem x_edge_imp_neq : forall (n m:Node),
XEdge n m -> n <> m.
Proof.
  intros n m Hedge Heq.
  inversion Hedge; subst.
  apply (comm_edge_imp_neq m m); auto.
  apply (strand_edge_imp_neq m m); auto.
Qed.

Theorem x_edge_antisymmetry :
antisymmetric Node XEdge.
Proof.
  intros n m Hss Hcontra.
  inversion Hss; subst. inversion Hcontra; subst.
  apply (comm_edge_antisymmetry n m H) in H0. exact H0.
  assert False.
  inversion H; subst. inversion H0; subst.
  inversion H1. apply H5. symmetry. exact H2.
  inversion H1.
  assert False.
  inversion Hcontra; subst. inversion H; subst.
  inversion H0; subst. inversion H3. apply H5.
  symmetry. exact H1.
  remember (strand_edge_antisymmetry n m H). apply e in H0.  
  remember (strand_edge_imp_neq n m H). 
  contradiction. inversion H0.
Qed.

Definition EdgePath (l:list Node) : RPath XEdge l.

Definition EdgeSetPath (l:list Node) (N: Nodes) : RPath (XSetEdge N) l.

Definition EdgePathEq (l:list Node) : RPath XEdgeEq l.

Definition EdgeSetPathEq (l:list Node) (N: Nodes) : RPath (XSetEdgeEq N) l.

(* Next - Acyclic EdgePath
  previously this was 

Inductive Acyclic_Node : Node -> Prop :=
| acyc_node : forall n,  ~(EdgePath n n) -> Acyclic_Node n.

Inductive Acyclic_Nodes : Nodes -> Prop :=
| acyclic_nodes : forall N,  
                    (forall n, In Node N n -> 
                                Acyclic_Node n) -> Acyclic_Nodes N.

Two questions to answer before proceeding:
  1) Does it Need to be specified as a prop? Can we just have a theorem
     that is provable from just the definition of EdgePath? It seems like
     if an EdgePath had a cycle, you would get a contradiction based on 
     strand indices at a min
  2) How should this be specified? Specifically for this case? More
     Generally for RPaths?

ALSO
 - The RPath definition seems to be okay/working. Is it ideal? Is there some
   obvious problem? Or improvement?

Also ALSO - I would like to prove an equivalence between the natural transitive
 and reflexive-transitive closures we were using originally, and these RPath
 versions if possible. It would be, it feels, very useful to be able to show
 one implies the other and be able to hop back and forth depending on what I'm
 trying to prove (Could be wrong... but this seems reasonable...)

*)