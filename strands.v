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

Require Import Logic List Arith Peano_dec Omega Ensembles.
Require Import Finite_sets_facts Finite_sets Relation_Definitions.
Require Import Relation_Operators.



Require String. Open Scope string_scope.

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





(* Represent atomic messages, *)
Variable Text : Set.
Variable text_eq_dec : forall (x y:Text), {x = y} + {x <> y}.
Hint Resolve text_eq_dec.

(* representing kryptographic key *)
Variable Key : Set.
(* TODO - injective, unary operation (inv : key -> key)
          Or in Coq would this make more sense
          instead as  key -> key -> Prop?
          The text notes the ability to handle
          both symmetric and asymmetric keys... *)
Variable key_eq_dec : forall (x y:Key), {x = y} + {x <> y}.
Hint Resolve key_eq_dec.


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

Definition Strands := Ensemble Strand.
Definition Msgs := Ensemble Msg.
Definition SMsgs := Ensemble SMsg.

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
Inductive Node : Strand -> nat -> Type :=
| node : forall s n, n < length s -> Node s n.

(* Definition Node : Type := {n: (Strand * nat) | (snd n) < (length (fst n))}.*)
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

Theorem node_smsg_valid : forall (n:Node),
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

Definition node_neq_dec : forall x y : Node,
 {x <> y} + {x = y}.
Proof.
  intros [[xs xn] xp] [[ys yn] yp].
  destruct (strand_eq_dec xs ys) as [EQs | NEQs]; subst.
  destruct (eq_nat_dec xn yn) as [EQn | NEQn]; subst.
  right. rewrite (proof_irrelevance (lt yn (length ys)) xp yp). reflexivity.

  left. intros C. inversion C. auto.
  left. intros C. inversion C. auto.
Qed.


Lemma node_imp_strand_nonempty : forall s n,
Node_strand n = s ->
length s > 0.
Proof.
  intros s n Hns.
  destruct n. destruct x.
  destruct n. simpl in l.
  destruct s.
  assert (s0 = nil). auto.
  subst. inversion l.
  simpl. omega.
  simpl in l. 
  assert (s0 = s). auto.
  rewrite <- H.
  omega.
Qed.

Inductive CommEdge : Relation Node :=
| cedge :  forall n m t, ((Node_smsg n = tx t 
                                    /\ Node_smsg m = rx t)
                        /\ Node_strand n <> Node_strand m)
                        -> CommEdge n m.
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
Inductive CommEdge' : Nodes -> Relation Node :=
| cedge_n : forall N x y,
              In Node N x ->
              In Node N y ->
              CommEdge x y ->
              CommEdge' N x y.
Hint Constructors CommEdge'.

(* A CommEdge between Node's, where the set the nodes belong to is specified. 
Inductive CommEdge'' (N:Nodes) : Relation (Node' N) :=
| cedge_n' : forall N x y,
              CommEdge (node' x) (node' y) ->
              CommEdge'' N x y.
Hint Constructors CommEdge''.
*)

Theorem cedge_irreflexivity : forall (x:Node),
~Reflexive Node CommEdge.
Proof.
  intros.
  unfold Reflexive.
  intros contra.
  remember (contra x) as Hfalse.
  inversion Hfalse; subst.
  inversion H as [contra_s contra_i].
  apply contra_i. reflexivity.
Qed.  
Hint Resolve cedge_irreflexivity.

Theorem cedge_imp_neq : forall n m,
 CommEdge n m -> n <> m.
 Proof.
   intros n m Hedge Hneq. subst.
   inversion Hedge as [contra_s contra_i]; subst.
   apply H. reflexivity.
 Qed.  
Hint Resolve cedge_imp_neq.

Theorem cedge_antisymmetry : 
Antisymmetric Node CommEdge.
Proof.
  intros n m Hcomm contra.
  assert False.
  inversion Hcomm; subst.
  inversion contra; subst.
  destruct H as [H Hneq_s].
  destruct H as [Htx1 Hrx1].
  destruct H0 as [H Hneq_s2].
  destruct H as [Htx2 Hrx2].
  rewrite Htx2 in Hrx1. inversion Hrx1.
  inversion H.
Qed.
Hint Resolve cedge_antisymmetry.

(* predecessor edge *)
(* node's direct predecessor -> node -> Prop *)
Inductive PredEdge : Relation Node :=
| pedge : forall i j, Node_strand i = Node_strand j 
                       -> (Node_index i) + 1 = Node_index j 
                       -> PredEdge i j.
(* [REF 1] Definition 2.3.4 pg 6
   "When n1= <s,i> and n2=<s,i+1> are members of N (set of node), there is
    an edge n1 => n2." *)

(* An CommEdge between nodes, where the set the nodes belong to is specified. *)
Inductive PredEdge' : Nodes -> Relation Node :=
| pedge_n : forall N x y,
              In Node N x ->
              In Node N y ->
              PredEdge x y ->
              PredEdge' N x y.
Hint Constructors PredEdge'.

Theorem pedge_irreflexivity : forall (x:Node),
~Reflexive Node PredEdge.
Proof.
  intros.
  unfold Reflexive.
  intros contra.
  remember (contra x) as Hfalse.
  inversion Hfalse; subst. omega. 
Qed.
Hint Resolve pedge_irreflexivity.

Theorem pedge_imp_neq : forall (n m: Node),
PredEdge n m -> n <> m.
Proof.
  intros n m Hedge Heq.
  subst. inversion Hedge; subst.
  omega.
Qed.
Hint Resolve pedge_imp_neq.

Theorem pedge_antisymmetry :
Antisymmetric Node PredEdge.
Proof.
  intros n m Hpe1 Hpe2.
  destruct Hpe1. destruct Hpe2.
  rewrite <- H0 in H2. omega.
Qed.
Hint Resolve pedge_antisymmetry.

(* predecessor multi edge (not nec. immediate predecessor) *)
(* node's predecessor -> node -> Prop *)
Definition PredPath : Relation Node := 
clos_trans Node PredEdge.
 (* [REF 1] Definition 2.3.4 pg 6
   "ni =>+ nj means that ni precedes nj (not necessarily immediately) on
    the same strand." *)

(* An CommEdge between nodes, where the set the nodes belong to is specified. *)
Inductive PredPath' : Nodes -> Relation Node :=
| ppath_n : forall N x y,
              In Node N x ->
              In Node N y ->
              PredPath x y ->
              PredPath' N x y.
Hint Constructors PredPath'.

Definition SSEdge : Relation Node :=
union Node CommEdge PredEdge.

(* An CommEdge between nodes, where the set the nodes belong to is specified. *)
Inductive SSEdge' : Nodes -> Relation Node :=
| ssedge_n : forall N x y,
              In Node N x ->
              In Node N y ->
              SSEdge x y ->
              SSEdge' N x y.
Hint Constructors SSEdge'.


Theorem ssedge_irreflexivity : forall (x:Node),
~Reflexive Node SSEdge.
Proof.
  unfold Reflexive.
  intros x Hss.
  remember (Hss x) as contra.
  inversion contra; subst.
  inversion H; subst. inversion H0. apply H2. reflexivity.
  inversion H; subst. omega.
Qed.
Hint Resolve ssedge_irreflexivity.

Theorem ssedge_imp_neq : forall (n m:Node),
SSEdge n m -> n <> m.
Proof.
  intros n m Hedge Heq.
  inversion Hedge; subst.
  apply (cedge_imp_neq m m); auto.
  apply (pedge_imp_neq m m); auto.
Qed.

Theorem ssedge_antisymmetry :
Antisymmetric Node SSEdge.
Proof.
  intros n m Hss Hcontra.
  inversion Hss; subst. inversion Hcontra; subst.
  apply (cedge_antisymmetry n m H) in H0. exact H0.
  assert False.
  inversion H; subst. inversion H0; subst.
  inversion H1. apply H5. symmetry. exact H2.
  inversion H1.
  assert False.
  inversion Hcontra; subst. inversion H; subst.
  inversion H0; subst. inversion H3. apply H5.
  symmetry. exact H1.
  remember (pedge_antisymmetry n m H). apply e in H0.  
  remember (pedge_imp_neq n m H). 
  contradiction. inversion H0.
Qed.

Theorem ppath_transitivity :
Transitive Node PredPath.
Proof.
  unfold Transitive.
  intros i j k Hij Hjk.
  apply (t_trans Node PredEdge i j k Hij Hjk).
Qed.
Hint Resolve ppath_transitivity.

Inductive OccursIn : Msg -> Node -> Prop :=
| occurs_in : forall m n, Subterm m (Node_msg n) -> OccursIn m n.
(* [REF 1] Definition 2.3.5 pg  6
   "An unsigned term m occurs in a node n iff m is a subterm of term(n). " *)

(* signifies the origin of a msg. *)
Inductive EntryPoint : Node -> Msgs -> Prop :=
| entrypoint :  forall n I, 
                  ((exists m, ((Node_smsg n = tx m) 
                               /\ (In Msg I m)))
                   /\ (forall n', (PredPath n' n) 
                                  -> ~(In Msg I (Node_msg n'))))
                  -> EntryPoint n I.
(* [REF 1] Definition 2.3.6 pg 6
   "The node n in N is an entry point for I (a set of unsigned terms) iff
    term(n) = +t for some t in I, and whenever n' =>+ n term(n') is not in I."*)

(* where an unsigned term originates, what node *)
Inductive OriginateAt : Msg -> Node -> Prop :=
| orig_at : forall m n, 
              (exists I, ((EntryPoint n I)
                          /\ (forall m', In Msg I m -> Subterm m m')))
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

(* In for members of pairs *)
Inductive InP (X:Type) : Ensemble (X*X) -> X -> Prop :=
| inp_l : forall E x,
            (exists y, In (X*X) E (x,y))
            -> InP X E x
| inp_r : forall E x,
            (exists y, In (X*X) E (y,x))
            -> InP X E x.
Hint Constructors InP.

Inductive ValidNodes : Nodes -> Edges-> Prop :=
| vn : forall N E,
         Finite Node N /\
         (forall x, In Node N x ->
                    InP Node E x ) ->
                    ValidNodes N E.


(*Ensures edges are finite, built from nodes in the node set
  and meet the given constraints (Comm or Pred) *)
Inductive ValidEdges : (Node -> Node -> Prop) -> Nodes -> Edges -> Prop :=
| ve : forall (P: Node -> Node -> Prop) N E,
         Finite Edge E 
         /\ (forall n, InP Node E n -> In Node N n)
         /\ (forall n m, In Edge E (n,m) -> (P n m)) ->
         ValidEdges P N E.

(* transitive closure of edges. *)
Definition EdgePath : Relation Node := 
clos_trans Node SSEdge.

Inductive EdgePath' : Nodes -> Relation Node :=
| epath_n : forall N x y,
              In Node N x ->
              In Node N y ->
              EdgePath x y ->
              EdgePath' N x y.
Hint Constructors EdgePath'.

Theorem ppath_imp_epath : forall i j,
PredPath i j -> EdgePath i j.
Proof.
  unfold EdgePath.
  intros i j Hpath.
  induction Hpath.
  constructor. right. exact H.
  apply (t_trans Node SSEdge x y z IHHpath1 IHHpath2).
Qed.  

Theorem epath_transitivity :
Transitive Node EdgePath.
Proof.
  unfold EdgePath.
  intros i j k Hij Hjk.
  apply (t_trans Node SSEdge i j k Hij Hjk).
Qed.

(* transitive reflexive closure of edges. *)
Definition EdgePathEq : Relation Node :=
clos_refl_trans Node SSEdge.

Inductive EdgePathEq' : Nodes -> Relation Node :=
| epatheq_n : forall N x y,
              In Node N x ->
              In Node N y ->
              EdgePathEq x y ->
              EdgePathEq' N x y.
Hint Constructors EdgePathEq'.

Theorem epatheq_opts: forall n m,
EdgePathEq n m -> EdgePath n m \/ n = m.
Proof.
  intros n m Hpatheq.
  induction Hpatheq.
  left. constructor. exact H. 
  right. reflexivity.
  inversion IHHpatheq1.
    inversion IHHpatheq2.
      left. apply (t_trans Node SSEdge x y z H H0). subst.
      left. exact H.
    inversion IHHpatheq2.  
      subst. left. exact H0.
      right. subst. reflexivity.
Qed.

Inductive Acyclic_Node : Node -> Prop :=
| acyc_node : forall n,  ~(EdgePath n n) -> Acyclic_Node n.

Inductive Acyclic_Nodes : Nodes -> Prop :=
| acyclic_nodes : forall N,  
                    (forall n, In Node N n -> 
                                Acyclic_Node n) -> Acyclic_Nodes N.

Theorem acyc_ppath_imp_neq : forall n m,
Acyclic_Node m ->
PredPath n m -> n <> m.
Proof.
  intros n m Hacycm Hpath.
  induction Hpath.
  
  apply pedge_imp_neq. exact H.

  remember (t_trans Node PredEdge x y z Hpath1 Hpath2) as Hxz.
  intros contra.
  destruct Hacycm as [n Hnp].
  apply Hnp. remember (ppath_imp_epath x n Hxz).
  assert (EdgePath n n = EdgePath x n). subst. reflexivity.
  rewrite H. exact e.
Qed.
Hint Resolve acyc_ppath_imp_neq.

Theorem acyc_ppath_asymmetry : forall n m,
Acyclic_Node n ->
PredPath n m -> ~(PredPath m n).
Proof.
  intros n m Hacycn Hpp contra.
  destruct Hacycn.
  apply H.
  remember (ppath_transitivity n m n Hpp contra).
  apply ppath_imp_epath. exact p.
Qed.

Theorem acyc_epath_irreflexivity : forall n m,
Acyclic_Node m ->
EdgePath n m -> n <> m.
Proof.
  intros n m Hacyc Hpath.
  induction Hpath.
  apply ssedge_imp_neq. exact H.
  intros contra.
  remember (t_trans Node SSEdge x y z Hpath1 Hpath2).
  destruct Hacyc.
  apply H.
  assert (EdgePath n n = EdgePath x n).
    rewrite contra. reflexivity.
  rewrite H0. exact c.
Qed.

(* An rx implies the existance of a tx *)
Definition TxExists (N:Nodes) (E:Edges) :=
  (forall y m, Node_smsg y = rx m -> 
               In Node N y ->  
               (exists x, (In Node N x
                           /\ Node_smsg x = tx m
                           /\ CommEdge x y
                           /\ In Edge E (x,y)))).

(* A node can rx a msg from only one tx at a time *)
Definition UniqTx (N:Nodes) :=
  (forall x y z, In Node N x ->
                 In Node N y ->
                 In Node N z ->
                 CommEdge x z ->
                 CommEdge y z ->
                 x = y).

Definition ExistsUniqTx (N:Nodes)  (CE:Edges) :=
  TxExists N CE /\ UniqTx N.

(* predecessor nodes on the same strand are also
    in the node set *)
Definition PredIsMember (N:Nodes) :=
  (forall x y, In Node N y ->
               PredEdge x y ->
               In Node N x).
Hint Unfold PredIsMember.



(* budle definition *)
Inductive Bundle : Nodes -> Edges -> Prop :=
| bundle : forall (N:Nodes) (E:Edges),
               ValidNodes N E ->
               ValidEdges (SSEdge' N) N E ->
               ExistsUniqTx N E ->
               PredIsMember N ->
               Acyclic_Nodes N -> 
               Bundle N E.
(* [REF 1] Definition 2.4 pg 7 
    1) The subgraph is finite
    2) If n2 is in Nodes and is a rx-ing message, then there
       is a unique n1 in CE such that n1 transmist that message
       to n2
    3) If n2 is in Nodes and PredEdge n1 n2 then that edge
       is in PE.
    4) The subgraph is acyclic *)
Hint Constructors Bundle Acyclic_Node Acyclic_Nodes ValidEdges ValidNodes InP.
Hint Constructors PredEdge CommEdge UniqOrigin OriginateAt EntryPoint OccursIn.
Hint Constructors clos_trans clos_refl_trans.
Hint Unfold PredIsMember ExistsUniqTx UniqTx TxExists EdgePath EdgePathEq. 
Hint Unfold PredPath Node Reflexive Antisymmetric Transitive.

Definition Set_Reflexive (X:Type) (E:Ensemble X) (R:Relation X) : Prop :=
forall x, In X E x -> R x x. 

Lemma bundle_edge_reflexivity : forall N E,
Bundle N E ->
Set_Reflexive Node N (EdgePathEq' N).
Proof.
  intros N E B x Hin. auto.
Qed.


Definition Set_Antisymmetric (X:Type) (E:Ensemble X) (R:Relation X) : Prop :=
  forall x y, In X E x ->
              In X E y -> 
              R x y ->
              R y x ->
              x = y. 

Lemma bundle_edge_antisymmetry : forall N E,
Bundle N E ->
Set_Antisymmetric Node N (EdgePathEq' N).
Proof.
  intros N E B x y Hinx Hiny Hxy Hyx.
  destruct Hxy as [N x y Hinx2 Hiny2 Hxy].
  apply epatheq_opts in Hxy.
  destruct Hyx as [N y x Hinx3 Hiny3 Hyx].
  apply epatheq_opts in Hyx.
  destruct B as [N E Hvn Hvce Htx Hpred Hacyc].
  destruct Hacyc as [N Hacycn]. remember (Hacycn x) as Hacycx.
  destruct Hvn as [N E Hnodes]. destruct Hnodes as [Hfin Hin]. 
  apply Hacycx in Hinx. inversion Hinx; subst.
  destruct Hxy.
    destruct Hyx.
      remember (t_trans Node SSEdge x y x H0 H1) as loop.
      contradiction.
      symmetry. exact H1.
    destruct Hyx.
      subst. contradiction.
      exact H0.
Qed.
Hint Resolve bundle_edge_antisymmetry.

Definition Set_Transitive (X:Type) (E:Ensemble X) (R:Relation X) : Prop :=
  forall x y z, In X E x ->
                In X E y -> 
                In X E z ->
                R x y ->
                R y z ->
                R x z. 

Lemma bundle_edge_transitivity : forall N E,
Bundle N E -> Set_Transitive Node N (EdgePathEq' N).
Proof.
  intros N E B x y z Hinx Hiny Hinz Hxy Hyz.
  destruct Hxy as [N x y Hinx1 Hiny1 Hxy].
  destruct Hyz as [N y z Hiny2 Hinz1 Hyz].
  constructor. exact Hinx. exact Hinz.
  apply (rt_trans Node SSEdge x y z Hxy Hyz).
Qed.
Hint Resolve bundle_edge_transitivity.

Definition Set_Order (X:Type) (E:Ensemble X) (R:Relation X) : Prop :=
Set_Reflexive X E R /\ 
Set_Antisymmetric X E R /\
Set_Transitive X E R.

(* Lemma 2.7 [REF 1] : Partial ordering of Bundle via edges *)
Theorem bundle_is_poset : forall N E,
Bundle N E -> 
Set_Order Node N (EdgePathEq' N).
Proof.
  intros N E B.
  split. apply (bundle_edge_reflexivity N E). exact B.
  split. apply (bundle_edge_antisymmetry N E). exact B.
  apply (bundle_edge_transitivity N E). exact B.
Qed.
(* Lemma 2.7 Suppose C is a bundle. 
   Then EdgePathEq for Nodes in C is a partial order, i.e. a reflexive, antisymmetric, 
   transitive relation. Every non-empty subset of the nodes in 
   C has C -minimal members.
*)

(* TEST TEST TEST TEST TEST TEST TEST *)

Inductive subset_minimal : Nodes -> Node -> Prop :=
| subset_min : forall N min,
                 In Node N min ->
                 (forall n, n <> min -> 
                            In Node N min ->
                            ~(EdgePathEq n min)) ->
                 subset_minimal N min.

Theorem finite_set_mem_dec : forall X E e,
(forall (x y:X), ({x = y} + {x <> y})) ->
Finite X E -> 
In X E e \/ ~(In X E e).
Proof.
  intros X E e dec_eq fin.
  induction fin.

  right. intros contra. inversion contra.

  destruct (dec_eq e x).
  
  left. subst. apply Add_intro2.

  inversion IHfin.
    eapply Add_intro1 in H0. left. exact H0.
    right. intro contra. apply Add_inv in contra. 
    inversion contra. apply H0. exact H1. apply n. symmetry. exact H1. 
Qed.

Lemma pred_ex_Sn : forall n c,
Node_index n = S c ->
  exists y, 
    Node_index y = c /\ 
    Node_strand y = Node_strand n.
Proof.
  intros n c n_index.
  inversion n.
  remember (Node_strand n).
  destruct (nth_error s c).

  auto.


Theorem node_smsg_valid : forall (n:Node),
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


Lemma bundle_minimal_ex : forall N E N',
Bundle N E ->
Included Node N' N ->
(exists x, In Node N' x) ->
(exists min, subset_minimal N' min).
Proof.
  intros N E N' B I ExN'.
  
  inversion ExN'.
  remember (Node_smsg x) as x_node.

  induction x_node.
    Case "tx".
    remember (Node_strand x) as x_strand.
    remember (Node_index x) as x_index.
    destruct x_index.
      SCase "index 0".
        exists x.
        constructor. exact H.
        intros n Hneq Hin contraPath. clear I ExN'.
        induction contraPath as [n x edge | |]. 
        (* destruct contraPath as [ x edge n | n x | x ]. *)
          SSCase "n -> x (step)".
          inversion edge.
            SSSCase "CommEdge".
              destruct H0. destruct H0. destruct H0. 
              rewrite <- Heqx_node in H2. inversion H2.
            SSSCase "PredEdge".
              inversion H0; subst. omega.
            SSCase "reflexive".
              apply Hneq. reflexivity.
            SSCase "trans".
              apply IHcontraPath2; auto.
              intro Eqyz. subst. apply IHcontraPath1; auto.  
      SCase "index S n".              
        apply IHx_index.






rewrite Eqyz in contraPath1. subst.
              remember (rt_trans Node SSEdge x y z contraPath1 contraPath2).
              destruct c. 
            

        inversion contraPath.


        intro contraPath.
        unfold subset_minimal.

  case node.
  induction node.
    case tx.
    induction n.
      exists x.


    auto.
  induction x.


(* TEST TEST TEST TEST TEST TEST TEST *)

Inductive subset_min_mem : Nodes -> Edges -> Nodes -> Node -> Prop :=
| has_min_mem : forall N E N' min, 
                  Bundle N E ->
                   Included Node N' N ->
                      In Node N' min -> 
                      (forall n, In Node N' n -> ~(EdgePath n min))
                  -> subset_min_mem N E N' min.
Hint Constructors subset_min_mem.

Lemma bundle_min_member_single : forall N E N',
Bundle N E ->
Included Node N' N ->
(exists x, N' =  Add Node (Empty_set Node) x)  ->
(exists y, subset_min_mem N E N' y).
Proof.
  intros N E N' B HIn Hsingle.
  inversion Hsingle; subst.
  exists x.
  constructor. exact B. exact HIn.
  apply Add_intro2.
  intros y HIny.
  assert (x = y) as Hs.
  apply  (Add_inv Node (Empty_set Node) x y) in HIny.
  inversion HIny. inversion H. exact H.
  intro contra.
  apply (acyc_epath_irreflexivity y y).
  destruct B as [N E Hvn Hve Hutx Hpmem Hacyc].
  destruct Hacyc. auto. subst.
  exact contra.
  reflexivity.
Qed.

Lemma incl_remove_add : forall X x N N',
Included X (Add X N' x) N ->
Included X N' N.
Proof.
  unfold Included.
  intros.
  apply H. unfold Add.
  apply Union_introl.
  exact H0.
Qed.  

Theorem bundle_min_members : forall n x N E N',
Bundle N E ->
Included Node N' N ->
cardinal Node N' (S n) ->
exists min,
In Node N' min ->
In Node N' x ->
 ~(EdgePath' N' x min).
Proof.
  (* Worked here, got stuck, decided to go back and prove for 1 and n -> (n+1)
     when above theorems/lemmas are complete this should be a simple
set of apply
     statements. *)
  induction n as [|n].

  intros x N E N' B I C.
  edestruct bundle_min_member_single as [min SSmm].
   apply B. apply I.
   apply cardinal_invert in C.
   destruct C as [CA [Cx [Ceq [Cnin Ccard]]]].
   exists Cx. rewrite Ceq.
   replace CA with (Empty_set Node). trivial.
   apply cardinal_invert in Ccard. auto.
  exists min.
  intros InN'min InN'x EP.
  inversion_clear SSmm.
  eapply H2. inversion EP; subst. apply H3. 
  destruct EP. exact H5. 

  intros x N E N' B I C.
  apply cardinal_invert in C.
  destruct C as [CA [Cx [Ceq [Cnin Ccard]]]].
  cut (Included Node CA N). intros CI.
  destruct (IHn x N E CA B CI Ccard) as [Imin IH].

   destruct (node_neq_dec Imin Cx).

   (* IF Imin <> Cx, it seems reasonable here to state Imin must be the minimum.
      HOWEVER, if Imin == Cx *)
   exists Imin.

   subst.
   assert (In Node CA Imin) as IminInCA.
     remember (Add_inv Node CA Cx Imin).
     inversion IH.
     apply o in IminInN'.
     inversion IminInN'.
       exact H.
       assert False. apply n0. symmetry. exact H.
       inversion H0.
   apply (IH y) in IminInCA.
     destruct yIn.
     subst.
     assert ((Cx = y) = False).
     apply Add_inv.
     SearchAbout Add.
   apply IH.
   (* Here we're left to prove subgoals:
        a) In Node CA Imin   AND
        b) In Node CA y

      (a) seems only possible if we assume Imin <> Cx (since Imin in N', and N' = CA + {Cx})
      likewise... 
      (b) seems only possible if we assume Imin <> Cx (since y in N', and N' = CA + {Cx})
 

      -- backed up and intro'd the line "" ahead of the assertion that Imin is the min to see
         if that leads to some insights into this whole eq/neq thing

Add_inv:
  forall (U : Type) (A : Ensemble U) (x y : U),
  In U (Add U A x) y -> In U A y \/ x = y

    *)

   

