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

Require Import Logic List Arith Peano_dec Omega Ensembles Finite_sets_facts Finite_sets Relation_Definitions ProofIrrelevance.

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

Theorem node_eq_iff : forall n m,
n = m <-> (Node_strand n = Node_strand m /\ Node_index n = Node_index m).
Proof.
  intros.
  destruct n as [[ns ni] np].
  destruct m as [[ms mi] mp].
  simpl.
  split.

  intros Heq.
  inversion Heq.
  auto.

  intros Heq.
  inversion Heq; subst.
  inversion Heq.
  assert (np = mp). apply proof_irrelevance.
  subst. auto.
Qed.
Hint Resolve node_eq_iff.


Inductive CommEdge : Relation Node :=
| cedge :  forall n m t, ((Node_smsg n = tx t 
                                    /\ Node_smsg m = rx t)
                        /\ Node_strand n <> Node_strand m)
                        -> CommEdge n m.

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
Hint Constructors CommEdge.

Theorem cedge_irreflexivity : forall n m,
CommEdge n m -> n <> m.
Proof.
  intros.
  destruct H. destruct H.
  intros contra. apply node_eq_iff in contra.
  inversion contra as [contra_s contra_i].
  apply H0. auto.
Qed.  
Hint Resolve cedge_irreflexivity.

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

Theorem pedge_irreflexivity : forall n m,
PredEdge n m -> n <> m.
Proof.
  intros.
  destruct H.
  intros contra. apply node_eq_iff in contra.
  inversion contra as [contra_s contra_i].
  rewrite <- H0 in contra_i. 
  destruct (Node_index i). omega.  omega. 
Qed.  
Hint Resolve pedge_irreflexivity.

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
Inductive PredPath : Relation Node :=
| ppath_step : forall i j, PredEdge i j -> PredPath i j
| ppath_path : forall i j k, PredEdge i j -> PredPath j k -> PredPath i k.
 (* [REF 1] Definition 2.3.4 pg 6
   "ni =>+ nj means that ni precedes nj (not necessarily immediately) on
    the same strand." *)
Hint Constructors PredPath.

Inductive SSEdge : Relation Node :=
| ss_cedge : forall n m, CommEdge n m -> SSEdge n m 
| ss_pedge : forall n m, PredEdge n m -> SSEdge n m.
Hint Constructors SSEdge.

Theorem ssedge_irreflexivity : forall (n m: Node),
SSEdge n m -> n <> m.
Proof.
  intros n m Hss.
  inversion Hss; auto.
Qed.
Hint Resolve ssedge_irreflexivity.

Theorem ssedge_antisymmetry :
(Antisymmetric Node SSEdge).
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
  remember (pedge_irreflexivity n m H). 
  contradiction. inversion H0.
Qed.


Theorem ppath_transitivity :
Transitive Node PredPath.
 Proof.
   unfold Transitive.
   intros i j k Hij Hjk.
   induction Hij.
   apply (ppath_path i j k H Hjk).
   apply IHHij in Hjk.
   apply (ppath_path i j k H Hjk).
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
         (forall x, In Node N x /\
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
Inductive EdgePath : Relation Node :=
| epath_edge : forall x y, SSEdge x y -> EdgePath x y
| epath_path : forall x y, PredPath x y -> EdgePath x y
| epath_trans : forall x y z, EdgePath x y -> EdgePath y z -> EdgePath x z.
Hint Constructors EdgePath.

Theorem path_transitivity :
Transitive Node EdgePath.
Proof.
  unfold Transitive.
  intros i j k Hij Hjk.
  induction Hij.
  apply (epath_trans x y k (epath_edge x y H) Hjk).
  apply (epath_trans x y k (epath_path x y H) Hjk).
  apply IHHij1. apply (epath_trans y z k Hij2 Hjk).
Qed.

(* transitive reflexiv closure of edges. *)
Inductive EdgePathEq : Relation Node :=
| patheq_refl : forall x, EdgePathEq x x
| patheq_path : forall x y, EdgePath x y -> EdgePathEq x y.
Hint Constructors EdgePathEq.

Inductive Acyclic_Node : Node -> Prop :=
| acyc_node : forall n,  ~(EdgePath n n) -> Acyclic_Node n.

Inductive Acyclic_Nodes : Nodes -> Prop :=
| acyclic_nodes : forall N,  
                    (forall n, In Node N n -> 
                                Acyclic_Node n) -> Acyclic_Nodes N.

Theorem acyc_ppath_irreflexivity : forall n m,
Acyclic_Node m ->
PredPath n m -> n <> m.
Proof.
  intros n m Hacycm Hpath.
  induction Hpath.
  
  apply pedge_irreflexivity. exact H.

  remember (ppath_path i j k H Hpath) as Hik.
  intros contra.
  destruct Hacycm as [n Hnp].
  apply Hnp. remember (epath_trans i j n (epath_edge i j (ss_pedge i j H)) (epath_path j n Hpath)).
  assert (EdgePath n n = EdgePath i n). subst. reflexivity.
  rewrite H0. exact e.
Qed.
Hint Resolve acyc_ppath_irreflexivity.

Theorem acyc_ppath_asymmetry : forall n m,
Acyclic_Node n ->
PredPath n m -> ~(PredPath m n).
Proof.
  intros n m Hacycn Hpp contra.
  destruct Hacycn.
  apply H.
  remember (ppath_transitivity n m n Hpp contra).
  auto.
Qed.

Theorem acyc_epath_irreflexivity : forall n m,
Acyclic_Node m ->
EdgePath n m -> n <> m.
Proof.
  intros n m Hacyc Hpath.
  induction Hpath.
  apply ssedge_irreflexivity. exact H.
  apply acyc_ppath_irreflexivity. exact Hacyc. exact H.

  destruct Hacyc as [z Hnpath].
  intros contra. subst.
  remember (epath_trans z y z Hpath1 Hpath2).
  contradiction.
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
               ValidEdges SSEdge N E ->
               (* ValidEdges CommEdge N CE ->
               ValidEdges PredEdge N PE -> *)
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
Hint Constructors Bundle Acyclic_Node Acyclic_Nodes EdgePathEq EdgePath ValidEdges ValidNodes InP PredPath
  PredEdge CommEdge UniqOrigin OriginateAt EntryPoint OccursIn.
Hint Unfold PredIsMember ExistsUniqTx UniqTx TxExists Node Reflexive Antisymmetric Transitive.

Inductive NodeInBundle : Node -> Nodes -> Edges -> Prop :=
| node_in_bundle : forall n N E,
Bundle N E -> In Node N n -> NodeInBundle n N E.

Lemma bundle_edge_reflexivity : forall N E,
Bundle N E -> Reflexive Node EdgePathEq.
Proof.
  auto.
Qed.
Hint Resolve bundle_edge_reflexivity.

Lemma bundle_edge_antisymmetry : forall N E,
Bundle N E -> Antisymmetric Node EdgePathEq.
  intros.
  unfold Antisymmetric.
  intros x y Hxy Hyx.
  destruct Hxy. auto.
  destruct Hyx. auto.
  
  destruct H as [N E Hvn Hvce Htx Hpred Hacyc].
  destruct Hacyc.
  remember (path_transitivity y x y H0 H1) as contra.
  remember (H y) as Hyacyc.
  destruct Hvn. clear Hvce Htx Hpred. destruct H2.
  destruct (H3 x). destruct (H3 y). 
  apply Hyacyc in H6.
  assert False. destruct H6. apply H6. assumption.
  inversion H8.
Qed.
Hint Resolve bundle_edge_antisymmetry.

Lemma bundle_edge_transitivity : forall N E,
Bundle N E -> Transitive Node EdgePathEq.
Proof.
  intros N E B x y z Hxy Hyz.
  destruct Hxy.
  assumption.
  destruct Hyz. constructor. assumption.
  remember (path_transitivity x x0 y H H0) as path.
  apply (patheq_path x y path).
Qed.
Hint Resolve bundle_edge_transitivity.

(* Lemma 2.7 [REF 1] : Partial ordering of Bundle via edges *)
Theorem bundle_is_poset : forall N E,
Bundle N E -> 
Order Node EdgePathEq.
Proof.
  constructor.
  apply (bundle_edge_reflexivity N E). assumption.
  apply (bundle_edge_transitivity N E). assumption.
  apply (bundle_edge_antisymmetry N E). assumption.
Qed.
(* Lemma 2.7 Suppose C is a bundle. 
   Then EdgePathEq for Nodes in C is a partial order, i.e. a reflexive, antisymmetric, 
   transitive relation. Every non-empty subset of the nodes in 
   C has C -minimal members.
*)

Inductive subset_min_mem : Nodes -> Edges -> Nodes -> Node -> Prop :=
| has_min_mem : forall N E N' min, 
                  Bundle N E ->
                   Included Node N' N ->
                      In Node N' min -> 
                      (forall n, In Node N' n -> ~(EdgePath n min))
                  -> subset_min_mem N E N' min.
Hint Constructors subset_min_mem.

SearchAbout Ensemble.

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

Lemma node_edge_opt_dec : forall N E n m,
Bundle N E ->
In Node N n ->
In Node N m ->
(~(SSEdge n m) \/ SSEdge n m).
Proof.
  Admitted.
  (* This seems trivially true, and may be useful for proving minimum members
     (showing that for the inductive step where a node is added, either it is 
      the new min (edge new->old_min) or the old min is still a min *)

Lemma incl_add_in : forall X N' N x,
Included X (Add X N' x) N ->
In X N x.
Proof.
  Admitted.
  (* Trivial lemma that I can't find a thm to immediately solve... using it to try and solve min_mem_add... *)

Lemma incl_add_inc : forall X N' N x, 
Included X (Add X N' x) N -> Included X N' N.
Proof.
  Admitted.
  (* Trivial lemma that I can't find a thm to immediately solve... using it to try and solve min_mem_add... *)

Lemma in_incl_in : forall X N' N x,
In X N' x ->
Included X N' N ->
In X N x.
Proof. Admitted.
  (* Trivial lemma that I can't find a thm to immediately solve... using it to try and solve min_mem_add... *)

Lemma min_mem_add : forall N E N' N'' x,
N'' = Add Node N' x ->
Included Node N'' N ->
(exists minN', subset_min_mem N E N' minN') ->
(exists minN'', subset_min_mem N E N'' minN'').
Proof.
  intros N E N' N'' x Hadd HIn Hmin.
  inversion Hmin as [minN' HsubN']; subst.
  inversion HsubN' as [t1 t2 t3 t4 B Hincl HInN' Hnopath]; subst.
  remember (incl_add_inc Node N' N x HIn) as HN'inN.
  remember (node_edge_opt_dec N E x minN' B 
                              (incl_add_in Node N' N x HIn)
                              (in_incl_in Node N' N minN' HInN' Hincl)) as edge_opts.
  
  inversion edge_opts.
  exists minN'.
  constructor; auto.
  (* We know minN' is a min for N'. x as added to make N'', we wish to prove N'' has a min member.
    so things considering at the moment - Well at the moment... trying to show minN' IW IN N'+x... *)

  (* from here we must show minN' is still a min or x is *)
  
  (* x is the added node. We know minN' is the min for N' (assuming defs are correct, few
   more implications than I'd like, feel like some should be assumptions at this point... 
   we need to show x is added, thus x has an edge to other nodes, and if that node
   is minN' then it is the new minimum, else if not minN' is still a min... 
   just discovered Coq.Classes.RelationClasses -- may be of use...
   just found "A relation is a partial order when it's reflexive, anti-symmetric, 
   and transitive. In the Coq standard library it's called just "order" for short." in
   Ben Pierce's book... well that's interesting, wonder if there's something of use
   under just "order"... and I just found Coq.Sets.Partial_Order ---
   okay Library Coq.Sets.Relations_1 has Order which is partial order...

*)





(* Lemma 2.7 [REF 1] : Minimal node existance *)
Theorem bundle_min_members : forall n N E N',
Bundle N E ->
Included Node N' N -> 
cardinal Node N' (n + 1) ->
exists min,
In Node N' min -> 
forall x, In Node N' x -> ~(EdgePath x min).
Proof.
  (* Worked here, got stuck, decided to go back and prove for 1 and n -> (n+1)
     when above theorems/lemmas are complete this should be a simple set of apply
     statements. *)