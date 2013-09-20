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

Require Import Logic List Arith Peano_dec Omega Ensembles.
Require Import Finite_sets_facts Finite_sets Relation_Definitions.
Require Import Relation_Operators strictorder util.

(* atomic messages *)
Variable Text : Set.
Variable eq_text_dec : forall (x y:Text), {x = y} + {x <> y}.
Hint Resolve eq_text_dec.

(* representing kryptographic key *)
Variable Key : Set.
(* TODO - injective, unary operation (inv : key -> key)
          Or in Coq would this make more sense
          instead as  key -> key -> Prop?
          The text notes the ability to handle
          both symmetric and asymmetric keys... *)
Variable eq_key_dec : forall (x y:Key), {x = y} + {x <> y}.
Hint Resolve eq_key_dec.

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
(* [REF 2] pg 4 paragraph 3 (details of encryption and subterms) *)
Hint Constructors Msg.

Definition eq_msg_dec : forall x y : Msg,  
  {x = y} + {x <> y}.
Proof.
  decide equality.
Qed.
Hint Resolve eq_msg_dec.

(* subterm relationship for messages *)
(* subterm -> encompassing term -> Prop *)
Inductive Subterm : Msg -> Msg -> Prop :=
| st_refl : forall m, Subterm m m
(* | stcryp : forall a g, Subterm a g -> Subterm a encrpt(g)  *)
| st_app_l : forall st l r, 
               Subterm st l -> Subterm st (msg_app l r)
| st_app_r : forall st l r, 
               Subterm st r -> Subterm st (msg_app l r)
| st_crpyt : forall st t k, 
               Subterm st t -> Subterm st (msg_crypt k t).
(* [REF 1] Section 2.1 pg 6 and Definition 2.11 *)
Hint Constructors Subterm.

(* signed message, + (tx) or - (rx) *)
Inductive SMsg : Type := 
| tx : Msg -> SMsg
| rx : Msg -> SMsg.
(* [REF 1] Definition 2.1 pg 6 
   They are defined as a pair, w/ the first member being in {+, -} 
   and the second a signed message. *)
Hint Constructors SMsg.

Definition eq_smsg_dec : forall x y : SMsg,  
  {x = y} + {x <> y}.
Proof.
 intros. decide equality.
Qed. 
Hint Resolve eq_smsg_dec.

(* strand *)
Definition Strand : Type := list SMsg.
(* [REF 1] First sentence of Abstract: "sequence of events"  
   Haven't hit a better def, and they start using strands
   pretty early so I'm rolling with this. *)

Definition eq_strand_dec : forall x y : Strand,  
  {x = y} + {x <> y}.
Proof.
 intros. decide equality.
Qed.
Hint Resolve eq_strand_dec.

Definition StrandSet := Ensemble Strand.
Definition MsgSet := Ensemble Msg.
Definition SMsgSet := Ensemble SMsg.

(* strand space *)
Inductive StrandSpace : Type :=
| strandspace : MsgSet -> StrandSet -> StrandSpace.
(* [REF 1] Definition 2.2 pg 6 "A strand space over A (set of possible msgs) 
           is a set E with a trace mapping tr : E -> list smsg" *)
Hint Constructors StrandSpace.

Definition SS_msgset (ss:StrandSpace) : MsgSet :=
  match ss with
    | strandspace m_set s_set => m_set
  end.

Definition SS_strandset (ss:StrandSpace) : StrandSet :=
  match ss with
    | strandspace m_set s_set => s_set
  end.

(* node in a strand space *)
Definition Node : Type := {n: (Strand * nat) | (snd n) < (length (fst n))}.
(* [REF 1] Definition 2.3.1 pg 6
   -"A node is a pair <s,i> where s is a strand and i a nat in [0, (length s))"
     NOTE: changed to be 0 based instead of 1 based sequences
   -"node <s,i> belongs to strand s"
   -"Every node belongs to a unique strand" *)

Definition Edge : Type := (prod Node Node).
Definition NodeSet := Ensemble Node.
Definition EdgeSet := Ensemble Edge.


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

Lemma eq_nodes : forall x y : Node,
Node_index x = Node_index y ->
Node_strand x = Node_strand y ->
x = y.
Proof.
  intros [[xs xn] xp] [[ys yn] yp] eq_index eq_strand.
  simpl in eq_index. simpl in eq_strand. subst.
  rewrite (proof_irrelevance (lt yn (length ys)) xp yp). reflexivity.
Qed.

Lemma node_imp_strand_nonempty : forall s n,
Node_strand n = s ->
length s > 0.
Proof.
  intros s n Hns.
  destruct n. destruct x.
  destruct n. simpl in l.
  destruct s.
  Case "s = []".
    assert (s0 = nil). auto.
  subst. inversion l.
  Case "s = s :: s1".
    simpl. omega.
    simpl in l. 
    assert (s0 = s). auto.
    rewrite <- H.
    omega.
Qed.

Inductive Comm : Relation Node :=
| comm :  forall n m t, ((Node_smsg n = tx t 
                                    /\ Node_smsg m = rx t)
                        /\ Node_strand n <> Node_strand m)
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

(* A CommEdge between nodes, where the set the nodes belong to is specified. *)
Inductive Comm' : NodeSet -> Relation Node :=
| comm' : forall N x y,
              In Node N x ->
              In Node N y ->
              Comm x y ->
              Comm' N x y.
Hint Constructors Comm'.

Lemma comm'_imp_comm : forall N x y,
Comm' N x y -> Comm x y.
Proof.
  intros N x y edge'.
  destruct edge'. exact H1.
Qed.
Hint Resolve comm'_imp_comm.


Theorem comm_irreflexivity : forall n,
~ Comm n n.
Proof.
  intros n contraedge.
  inversion contraedge; subst.
  destruct H as [[txsmsg rxsmsg] strandneq].
  apply strandneq. reflexivity.
Qed.
Hint Resolve comm_irreflexivity.

Theorem comm'_irreflexivity : forall N n,
~ Comm' N n n.
Proof.
  intros N n contra.
  apply comm'_imp_comm in contra.
  eapply comm_irreflexivity.
  exact contra.
Qed.
Hint Resolve comm'_irreflexivity.

Theorem comm_antisymmetry : 
Antisymmetric Node Comm.
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
Hint Resolve comm_antisymmetry.

Theorem comm'_antisymmetry : forall N,
 Antisymmetric Node (Comm' N).
 Proof.
  intros N n m Hcomm contra.
  apply comm_antisymmetry.
  apply (comm'_imp_comm N). exact Hcomm.
  apply (comm'_imp_comm N). exact contra.
Qed.
Hint Resolve comm'_antisymmetry.

(* predecessor edge *)
(* node's direct predecessor -> node -> Prop *)
Inductive Pred : Relation Node :=
| pred : forall i j, Node_strand i = Node_strand j 
                       -> (Node_index i) + 1 = Node_index j 
                       -> Pred i j.
(* [REF 1] Definition 2.3.4 pg 6
   "When n1= <s,i> and n2=<s,i+1> are members of N (set of node), there is
    an edge n1 => n2." *)

(* An CommEdge between nodes, where the set the nodes belong to is specified. *)
Inductive Pred' : NodeSet -> Relation Node :=
| pedge' : forall N x y,
              In Node N x ->
              In Node N y ->
              Pred x y ->
              Pred' N x y.
Hint Constructors Pred'.

Lemma pred'_imp_pred : forall N x y,
Pred' N x y -> Pred x y.
Proof.
  intros N x y edge'.
  destruct edge'. exact H1.
Qed.
Hint Resolve pred'_imp_pred.

Theorem pred_irreflexivity : forall n,
~Pred n n.
Proof.
  intros n edge.
  inversion edge; subst. omega.
Qed.
Hint Resolve pred_irreflexivity.

Theorem pred'_irreflexivity : forall N n,
~ Pred' N n n.
Proof.
  intros N n edge.
  eapply pred_irreflexivity.
  eapply pred'_imp_pred. exact edge.
Qed.
Hint Resolve pred'_irreflexivity.

Theorem pred_antisymmetry :
Antisymmetric Node Pred.
Proof.
  intros n m Hpe1 Hpe2.
  destruct Hpe1. destruct Hpe2.
  rewrite <- H0 in H2. omega.
Qed.
Hint Resolve pred_antisymmetry.

Theorem pred'_antisymmetry : forall N,
Antisymmetric Node (Pred' N).
Proof.
  intros N n m Hpe1 Hpe2.
  apply pred'_imp_pred in Hpe1.
  apply pred'_imp_pred in Hpe2.
  apply pred_antisymmetry; auto.
Qed.
Hint Resolve pred'_antisymmetry.

(* predecessor multi edge (not nec. immediate predecessor) *)
(* node's eventual predecessor -> node -> Prop *)
Definition PredPath : Relation Node := 
clos_trans Node Pred.
 (* [REF 1] Definition 2.3.4 pg 6
   "ni =>+ nj means that ni precedes nj (not necessarily immediately) on
    the same strand." *)
Hint Constructors clos_trans.

(* An PredPath between nodes, where the set the nodes belong to is specified. *)
Definition PredPath' (N: NodeSet) : Relation Node :=
clos_trans Node (Pred' N).

Lemma ppath'_imp_ppath : forall N x y,
PredPath' N x y -> PredPath x y.
Proof.
  intros N x y edge'.
  induction edge'.
  destruct H.
  constructor. exact H1. 
  apply (t_trans Node Pred x y z IHedge'1 IHedge'2).
Qed.
Hint Resolve ppath'_imp_ppath.

Theorem ppath_transitivity :
Transitive Node PredPath.
Proof.
  intros i j k Hij Hjk.
  apply (t_trans Node Pred i j k Hij Hjk).
Qed.
Hint Resolve ppath_transitivity.

Theorem ppath'_transitivity : forall N,
Transitive Node (PredPath' N).
Proof.
  intros N i j k Hij Hjk.
  apply (t_trans Node (Pred' N) i j k Hij Hjk).
Qed.
Hint Resolve ppath'_transitivity.

Definition SSEdge : Relation Node :=
union Node Comm Pred.
Hint Constructors or.

Definition SSEdge' (N:NodeSet) : Relation Node :=
union Node (Comm' N) (Pred' N).

Lemma ssedge'_imp_ssedge : forall N x y,
SSEdge' N x y -> SSEdge x y.
Proof.
  intros N x y edge'.
  destruct edge'.
  left. apply (comm'_imp_comm _ _ _ H).
  right. apply (pred'_imp_pred _ _ _ H).
Qed.
Hint Resolve ssedge'_imp_ssedge.

Theorem ssedge_irreflexivity : forall n,
~SSEdge n n.
Proof.
  intros n Hedge.
  inversion Hedge; subst; auto.
  eapply (comm_irreflexivity); eauto.
  eapply (pred_irreflexivity); eauto.
Qed.
Hint Resolve ssedge_irreflexivity.

Theorem ssedge'_irreflexivity : forall N n,
~SSEdge' N n n.
Proof.
  intros N n Hedge.
  inversion Hedge; subst; auto.
  eapply (comm_irreflexivity); eauto.
  eapply (pred_irreflexivity); eauto.
Qed.
Hint Resolve ssedge'_irreflexivity.

Theorem ssedge_antisymmetry :
Antisymmetric Node SSEdge.
Proof.
  intros n m Hss Hcontra.
  inversion Hss; subst. inversion Hcontra; subst.
  apply (comm_antisymmetry n m H) in H0. exact H0.
  assert False.
  inversion H; subst. inversion H0; subst.
  inversion H1. apply H5. symmetry. exact H2.
  inversion H1.
  assert False.
  inversion Hcontra; subst. inversion H; subst.
  inversion H0; subst. inversion H3. apply H5.
  symmetry. exact H1.
  inversion H; subst. inversion H0; subst.
  omega. inversion H0.
Qed.
Hint Resolve ssedge_antisymmetry.

Theorem ssedge'_antisymmetry : forall N,
Antisymmetric Node (SSEdge' N).
Proof.
  intros N n m Hss Hcontra.
  apply ssedge_antisymmetry.
  apply (ssedge'_imp_ssedge N). exact Hss.
  apply (ssedge'_imp_ssedge N). exact Hcontra.
Qed.
Hint Resolve ssedge'_antisymmetry.
