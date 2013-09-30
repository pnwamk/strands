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
Require Import Relation_Operators util.
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

Theorem node_smsg_valid :
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
| cedge' : forall N x y,
              In Node N x ->
              In Node N y ->
              CommEdge x y ->
              CommEdge' N x y.
Hint Constructors CommEdge'.

Lemma cedge'_imp_cedge : forall N x y,
CommEdge' N x y -> CommEdge x y.
Proof.
  intros N x y edge'.
  destruct edge'. exact H1.
Qed.

Theorem cedge_imp_neq : forall n m,
 CommEdge n m -> n <> m.
 Proof.
   intros n m Hedge Hneq. subst.
   inversion Hedge as [contra_s contra_i]; subst.
   apply H. reflexivity.
 Qed.  
Hint Resolve cedge_imp_neq.

Theorem cedge'_imp_neq : forall N n m,
 CommEdge' N n m -> n <> m.
 Proof.
   intros N n m Hedge Hneq. subst.
   inversion Hedge as [contra_s contra_i]; subst.
   apply cedge_imp_neq in H1. apply H1. reflexivity.
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

Theorem cedge'_antisymmetry : forall N,
 Antisymmetric Node (CommEdge' N).
 Proof.
  intros N n m Hcomm contra.
  apply cedge_antisymmetry.
  apply (cedge'_imp_cedge N). exact Hcomm.
  apply (cedge'_imp_cedge N). exact contra.
Qed.
Hint Resolve cedge'_antisymmetry.

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
| pedge' : forall N x y,
              In Node N x ->
              In Node N y ->
              PredEdge x y ->
              PredEdge' N x y.
Hint Constructors PredEdge'.

Lemma pedge'_imp_pedge : forall N x y,
PredEdge' N x y -> PredEdge x y.
Proof.
  intros N x y edge'.
  destruct edge'. exact H1.
Qed.

Theorem pedge_imp_neq : forall (n m: Node),
PredEdge n m -> n <> m.
Proof.
  intros n m Hedge Heq.
  subst. inversion Hedge; subst.
  omega.
Qed.
Hint Resolve pedge_imp_neq.

Theorem pedge'_imp_neq : forall N (n m: Node),
PredEdge' N n m -> n <> m.
Proof.
  intros N n m Hedge Heq.
  subst. inversion Hedge; subst.
  apply pedge_imp_neq in H1. apply H1. reflexivity.
Qed.
Hint Resolve pedge'_imp_neq.


Theorem pedge_antisymmetry :
Antisymmetric Node PredEdge.
Proof.
  intros n m Hpe1 Hpe2.
  destruct Hpe1. destruct Hpe2.
  rewrite <- H0 in H2. omega.
Qed.
Hint Resolve pedge_antisymmetry.

Theorem pedge'_antisymmetry : forall (N: Nodes),
Antisymmetric Node (PredEdge' N).
Proof.
  intros N n m Hpe1 Hpe2.
  apply pedge'_imp_pedge in Hpe1.
  apply pedge'_imp_pedge in Hpe2.
  apply pedge_antisymmetry; auto.
Qed.
Hint Resolve pedge'_antisymmetry.

(* predecessor multi edge (not nec. immediate predecessor) *)
(* node's predecessor -> node -> Prop *)
Definition PredPath : Relation Node := 
clos_trans Node PredEdge.
 (* [REF 1] Definition 2.3.4 pg 6
   "ni =>+ nj means that ni precedes nj (not necessarily immediately) on
    the same strand." *)

(* An CommEdge between nodes, where the set the nodes belong to is specified. *)
Definition PredPath' (N: Nodes) : Relation Node :=
clos_trans Node (PredEdge' N).

(* TODO predpath properties? *)

Lemma ppath'_imp_ppath : forall N x y,
PredPath' N x y -> PredPath x y.
Proof.
  intros N x y edge'.
  induction edge'.
  destruct H.
  constructor. exact H1. 
  apply (t_trans Node PredEdge x y z IHedge'1 IHedge'2).
Qed.

Definition SSEdge : Relation Node :=
union Node CommEdge PredEdge.

(* An CommEdge between nodes, where the set the nodes belong to is specified. *)
Definition SSEdge' (N:Nodes) : Relation Node :=
union Node (CommEdge' N) (PredEdge' N).

Lemma ssedge'_imp_ssedge : forall N x y,
SSEdge' N x y -> SSEdge x y.
Proof.
  intros N x y edge'.
  destruct edge'.
  left. apply (cedge'_imp_cedge _ _ _ H).
  right. apply (pedge'_imp_pedge _ _ _ H).
Qed.

Theorem ssedge_imp_neq : forall (n m:Node),
SSEdge n m -> n <> m.
Proof.
  intros n m Hedge Heq.
  inversion Hedge; subst.
  apply (cedge_imp_neq m m); auto.
  apply (pedge_imp_neq m m); auto.
Qed.

Theorem ssedge'_imp_neq : forall (N: Nodes) (n m:Node),
SSEdge' N n m -> n <> m.
Proof.
  intros N n m Hedge.
  apply ssedge_imp_neq.
  apply (ssedge'_imp_ssedge N).
  exact Hedge.
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

Theorem ssedge'_antisymmetry : forall (N : Nodes),
Antisymmetric Node (SSEdge' N).
Proof.
  intros N n m Hss Hcontra.
  apply ssedge_antisymmetry.
  apply (ssedge'_imp_ssedge N). exact Hss.
  apply (ssedge'_imp_ssedge N). exact Hcontra.
Qed.


Theorem ppath_transitivity :
Transitive Node PredPath.
Proof.
  intros i j k Hij Hjk.
  apply (t_trans Node PredEdge i j k Hij Hjk).
Qed.
Hint Resolve ppath_transitivity.

Theorem ppath'_transitivity : forall (N : Nodes),
Transitive Node (PredPath' N).
Proof.
  intros N i j k Hij Hjk.
  apply (t_trans Node (PredEdge' N) i j k Hij Hjk).
Qed.
Hint Resolve ppath'_transitivity.

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

Definition EdgePath' (N: Nodes) : Relation Node := 
clos_trans Node (SSEdge' N).

Lemma epath'_imp_epath : forall N x y,
EdgePath' N x y -> EdgePath x y.
Proof.
  intros N x y edge'.
  induction edge'.
  constructor.
  apply (ssedge'_imp_ssedge _ _ _ H).
  apply (t_trans Node SSEdge x y z IHedge'1 IHedge'2).
Qed.

Theorem ppath_imp_epath : forall i j,
PredPath i j -> EdgePath i j.
Proof.
  unfold EdgePath.
  intros i j Hpath.
  induction Hpath.
  constructor. right. exact H.
  apply (t_trans Node SSEdge x y z IHHpath1 IHHpath2).
Qed.  

Theorem ppath'_imp_epath' : forall N i j,
PredPath' N i j -> EdgePath' N i j.
Proof.
  intros N i j Hpath.
  induction Hpath.
  constructor. right. exact H.
  apply (t_trans Node (SSEdge' N) x y z IHHpath1 IHHpath2).
Qed.  

Theorem epath_transitivity :
Transitive Node EdgePath.
Proof.
  unfold EdgePath.
  intros i j k Hij Hjk.
  apply (t_trans Node SSEdge i j k Hij Hjk).
Qed.

Theorem epath'_transitivity : forall (N : Nodes),
Transitive Node (EdgePath' N).
Proof.
  intros N i j k Hij Hjk.
  apply (t_trans Node (SSEdge' N) i j k Hij Hjk).
Qed.

Theorem epath'_imp_in_l : forall N n m,
EdgePath' N n m -> In Node N n.
Proof.
  intros N n m epath'.
  induction  epath'.
  destruct H.
  destruct H. exact H.
  destruct H. exact H.
  exact IHepath'1. 
Qed.

Theorem epath'_imp_in_r : forall N n m,
EdgePath' N n m -> In Node N m.
Proof.
  intros N n m epath'.
  induction  epath'.
  destruct H.
  destruct H. exact H0.
  destruct H. exact H0.
  exact IHepath'2. 
Qed.

(* transitive reflexive closure of edges. *)
Inductive EdgePathEq : Relation Node :=
| epatheq_refl : forall x, EdgePathEq x x
| epatheq_path : forall x y, EdgePath x y -> EdgePathEq x y.

Inductive EdgePathEq' (N : Nodes) : Relation Node :=
| epatheq'_refl : forall x, In Node N x -> EdgePathEq' N x x
| epatheq'_path : forall x y, EdgePath' N x y -> EdgePathEq' N x y.
Hint Constructors EdgePathEq'.

Lemma epatheq'_imp_epatheq : forall N x y,
EdgePathEq' N x y -> EdgePathEq x y.
Proof.
  intros N x y edge'.
  induction edge'.
  constructor.
  constructor.
  apply (epath'_imp_epath _ _ _ H).
Qed.


Theorem epatheq'_imp_in_l : forall N n m,
EdgePathEq' N n m -> In Node N n.
Proof.
  intros N n m epath'.
  induction  epath'.
  exact H. apply (epath'_imp_in_l N x y). exact H.
Qed.

Theorem epatheq'_imp_in_r : forall N n m,
EdgePathEq' N n m -> In Node N m.
Proof.
  intros N n m epath'.
  induction  epath'.
  exact H. apply (epath'_imp_in_r N x y). exact H.
Qed.

Theorem epatheq_opts: forall n m,
EdgePathEq n m -> EdgePath n m \/ n = m.
Proof.
  intros n m Hpatheq.
  induction Hpatheq.
  right. reflexivity.
  left. exact H.
Qed.

Theorem epatheq'_opts: forall N n m,
EdgePathEq' N n m -> EdgePath' N n m \/ n = m.
Proof.
  intros N n m Hpatheq.
  induction Hpatheq.
  right. reflexivity.
  left. exact H.
Qed.


Theorem epatheq_transitivity :
Transitive Node EdgePathEq.
Proof.
  unfold Transitive.
  intros i j k Hij Hjk.
  destruct Hij. exact Hjk.
  destruct Hjk. constructor. exact H.
  constructor.
  apply (t_trans Node SSEdge x x0 y H H0).
Qed.

Theorem epatheq'_transitivity : forall (N : Nodes),
Transitive Node (EdgePathEq' N).
Proof.
  intros N i j k Hij Hjk.
  destruct Hij. exact Hjk.
  destruct Hjk. constructor. exact H.
  constructor.
  apply (t_trans Node (SSEdge' N) x x0 y H H0).
Qed.

Definition Acyclic_Node (n : Node): Prop :=
~(EdgePath n n).

Definition Acyclic_Nodes (N : Nodes) : Prop :=
forall n, In Node N n -> Acyclic_Node n.

Theorem acyc_ppath_asymmetry : forall n m,
Acyclic_Node n ->
PredPath n m -> ~(PredPath m n).
Proof.
  intros n m Hacycn Hpp contra.
  apply Hacycn.
  remember (ppath_transitivity n m n Hpp contra).
  apply ppath_imp_epath. exact p.
Qed.

Theorem acyc_ppath'_asymmetry : forall N n m,
Acyclic_Node n ->
PredPath' N n m -> ~(PredPath' N m n).
Proof.
  intros N n m Hacycn Hpp contra.
  apply Hacycn.
  apply ppath_imp_epath.
  apply (ppath_transitivity n m n).
  apply (ppath'_imp_ppath N).
  exact Hpp. apply (ppath'_imp_ppath N).
  exact contra.
Qed.

Theorem acyc_epath_imp_neq : forall n m,
Acyclic_Node m ->
EdgePath n m -> n <> m.
Proof.
  intros n m Hacyc Hpath.
  induction Hpath.
  apply ssedge_imp_neq. exact H.
  intros contra.
  remember (t_trans Node SSEdge x y z Hpath1 Hpath2).
  apply Hacyc.
  subst x. exact c.
Qed.

Theorem acyc_epath'_imp_neq : forall N n m,
Acyclic_Node m ->
EdgePath' N n m -> n <> m.
Proof.
  intros N n m Hacyc Hpath.
  apply acyc_epath_imp_neq.
  exact Hacyc. apply (epath'_imp_epath N).
  exact Hpath.
Qed.

Definition TxExists := forall y m,
Node_smsg y = rx m ->
(exists x, Node_smsg x = tx m /\ CommEdge x y).

(* An rx implies the existance of a tx *)
Definition TxExistsInSet (N:Nodes) (E:Edges) :=
TxExists /\ 
(forall x y m, Node_smsg y = rx m -> 
               In Node N y ->
               CommEdge x y ->
               (In Node N x /\ In Edge E (x,y))).

(* A node can rx a msg from only one tx at a time *)
Definition UniqTx :=
  (forall x y z, CommEdge x z ->
                 CommEdge y z ->
                 x = y).

Definition ExistsUniqTx (N:Nodes)  (CE:Edges) :=
  TxExistsInSet N CE /\ UniqTx.

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
Hint Constructors Bundle  ValidEdges ValidNodes InP.
Hint Constructors PredEdge CommEdge UniqOrigin OriginateAt EntryPoint OccursIn.
Hint Constructors clos_trans clos_refl_trans.
Hint Unfold PredIsMember ExistsUniqTx UniqTx TxExists EdgePath. 
Hint Unfold PredPath Node Reflexive Antisymmetric Transitive.

Lemma bundle_edge_reflexivity : forall N E,
(forall x, In Node N x) -> (* We only consider set members *)
Bundle N E ->
Reflexive Node (EdgePathEq' N).
Proof.
  intros N E OnlySetMems B x. constructor.
  apply OnlySetMems.
Qed.
(* Looks like I overspoke - I don't think I can merely prove reflexivity for (EdgePathEq' N) =( I
   may need some special definition - I added the qualifier to exlcude non-set members (or assume
   all nodes being considered are nodes. )*)

Lemma bundle_edge_antisymmetry : forall N E,
Bundle N E ->
Antisymmetric Node (EdgePathEq' N).
Proof.
  intros N E B x y Hxy Hyx.
  destruct Hxy as [x HxIn | x y Hxy].
  reflexivity.
  destruct Hyx as [y HyIn | y x Hyx].
  reflexivity.
  remember (epath'_transitivity N x y x Hxy Hyx) as loop.
  remember (acyc_epath'_imp_neq N x x).
  assert False as F.
    apply n.
    destruct B as [N E Hvn Hvce Htx Hpred Hacyc].
    unfold Acyclic_Nodes in Hacyc. 
    apply (Hacyc x). apply (epath'_imp_in_r N x x loop).
    exact loop. reflexivity.
  inversion F.
Qed.
Hint Resolve bundle_edge_antisymmetry.

Lemma bundle_edge_transitivity : forall N E,
Bundle N E -> Transitive Node (EdgePathEq' N).
Proof.
  intros N E B x y z Hxy Hyz.
  apply (epatheq'_transitivity N x y z).
  exact Hxy. exact Hyz.
Qed.
Hint Resolve bundle_edge_transitivity.

(* Lemma 2.7 [REF 1] : Partial ordering of Bundle via edges *)
Theorem bundle_is_poset : forall N E,
(forall x, In Node N x) -> (* Only set members *)
Bundle N E -> 
Order Node (EdgePathEq' N).
Proof.
  intros N E OnlySetMems B.
  split. apply (bundle_edge_reflexivity N E). exact OnlySetMems. exact B.
  apply (bundle_edge_transitivity N E). exact B.
  apply (bundle_edge_antisymmetry N E). exact B.
Qed.
(* Lemma 2.7 Suppose C is a bundle. 
   Then EdgePathEq for Nodes in C is a partial order, i.e. a reflexive, antisymmetric, 
   transitive relation. Every non-empty subset of the nodes in 
   C has C -minimal members.
*)

Inductive subset_minimal : Nodes -> Node -> Prop :=
| subset_min : forall N min,
                 In Node N min ->
                 (forall n, n <> min -> 
                            In Node N n ->
                            ~(EdgePathEq' N n min)) ->
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
 destruct n as [[ns nc] nP].
 simpl in *. subst nc.
 eexists (exist _ (ns,c) _).
 simpl. auto.
Grab Existential Variables.
 simpl. omega.
Qed.

Inductive ReverseSSEdge : Relation Node :=
| rev_ssedge : forall x y, SSEdge x y -> ReverseSSEdge y x.

Inductive ReverseSSEdge' : Nodes -> Relation Node :=
| rev_ssedge' : forall N x y,
                  SSEdge' N x y -> ReverseSSEdge' N y x.

Lemma cedge'_imp_in_l : forall N x y,
CommEdge' N x y -> In Node N x.
Proof.
  intros N x y edge.
  destruct edge. exact H.
Qed.

Lemma cedge'_imp_in_r : forall N x y,
CommEdge' N x y -> In Node N y.
Proof.
  intros N x y edge.
  destruct edge. exact H0.
Qed.

Lemma pedge'_imp_in_l : forall N x y,
PredEdge' N x y -> In Node N x.
Proof.
  intros N x y edge.
  destruct edge. exact H.
Qed.

Lemma pedge'_imp_in_r : forall N x y,
PredEdge' N x y -> In Node N y.
Proof.
  intros N x y edge.
  destruct edge. exact H0.
Qed.

Lemma ssedge'_imp_in_l : forall N x y,
SSEdge' N x y -> In Node N x.
Proof.
  intros N x y edge.
  destruct edge. eapply cedge'_imp_in_l. exact H.
  eapply pedge'_imp_in_l. exact H.
Qed.

Lemma ssedge'_imp_in_r : forall N x y,
SSEdge' N x y -> In Node N y.
Proof.
  intros N x y edge.
  destruct edge. eapply cedge'_imp_in_r. exact H.
  eapply pedge'_imp_in_r. exact H.
Qed.

Lemma rev_ssedge'_imp_in_l : forall N x y,
ReverseSSEdge' N x y -> In Node N x.
Proof.
  intros N x y edge.
  destruct edge. eapply ssedge'_imp_in_r. exact H.
Qed.

Lemma rev_ssedge'_imp_in_r : forall N x y,
ReverseSSEdge' N x y -> In Node N y.
Proof.
  intros N x y edge.
  destruct edge. eapply ssedge'_imp_in_l. exact H.
Qed.

Definition ReversePath : Relation Node := clos_trans Node ReverseSSEdge.

Definition ReversePath' (N : Nodes) : Relation Node := clos_trans Node (ReverseSSEdge' N).

Lemma rev_path'_imp_in_l : forall N x y,
ReversePath' N x y -> In Node N x.
Proof.
  intros N x y edge.
  induction edge. eapply rev_ssedge'_imp_in_l. exact H.
  exact IHedge1.
Qed.

Lemma rev_path'_imp_in_r : forall N x y,
ReversePath' N x y -> In Node N y.
Proof.
  intros N x y edge.
  induction edge. eapply rev_ssedge'_imp_in_r. exact H.
  exact IHedge2.
Qed.

(* transitive reflexive closure of edges. *)
Inductive ReversePathEq : Relation Node :=
| rev_patheq_refl : forall x, ReversePathEq x x
| rev_patheq_path : forall x y, ReversePath x y -> ReversePathEq x y.
Hint Constructors ReversePathEq.

Inductive ReversePathEq' (N : Nodes) : Relation Node :=
| rev_patheq'_refl : forall x, In Node N x -> ReversePathEq' N x x
| rev_patheq'_path : forall x y, ReversePath' N x y -> ReversePathEq' N x y.
Hint Constructors ReversePathEq'.

Lemma rev_patheq'_imp_in_l : forall N x y,
ReversePathEq' N x y -> In Node N x.
Proof.
  intros N x y edge.
  destruct edge. exact H. eapply rev_path'_imp_in_l. exact H.
Qed.

Lemma rev_patheq'_imp_in_r : forall N x y,
ReversePathEq' N x y -> In Node N y.
Proof.
  intros N x y edge.
  destruct edge. exact H. eapply rev_path'_imp_in_r. exact H.
Qed.

Lemma epath_imp_rev_path : forall x y,
EdgePath x y -> ReversePath y x.
Proof.
  intros x y edge.
  induction edge.
  constructor. constructor. exact H.
  apply (t_trans Node ReverseSSEdge z y x IHedge2 IHedge1).
Qed.

Lemma rev_path_imp_epath : forall x y,
ReversePath x y -> EdgePath y x.
Proof.
  intros x y edge.
  induction edge.
  constructor. destruct H. exact H.
  apply (t_trans Node SSEdge z y x IHedge2 IHedge1).
Qed.

Lemma epath'_imp_rev_path' : forall N x y,
EdgePath' N x y -> ReversePath' N y x.
Proof.
  intros N x y edge.
  induction edge.
  constructor. constructor. exact H.
  apply (t_trans Node (ReverseSSEdge' N) z y x IHedge2 IHedge1).
Qed.

Lemma rev_path'_imp_epath' : forall N x y,
ReversePath' N x y -> EdgePath' N y x.
Proof.
  intros N x y edge.
  induction edge.
  constructor. destruct H. exact H.
  apply (t_trans Node (SSEdge' N) z y x IHedge2 IHedge1).
Qed.

Lemma epatheq'_imp_rev_patheq' : forall N x y,
EdgePathEq' N x y -> ReversePathEq' N y x.
Proof.
  intros N x y epatheq'.
  destruct epatheq'.
  constructor. exact H.
  constructor. 
  induction H.
  constructor. constructor. exact H.
  apply (t_trans Node (ReverseSSEdge' N) z y x IHclos_trans2 IHclos_trans1).
Qed.

Lemma rev_patheq'_imp_epatheq' : forall N x y,
ReversePathEq' N x y -> EdgePathEq' N y x.
Proof.
  intros N x y edge.
  induction edge.
  constructor. exact H.
  constructor. apply rev_path'_imp_epath'. exact H.
Qed.

Lemma index_0_imp_no_strand_pred : forall (n : Node),
Node_index n = 0 ->
~ exists p, PredEdge p n. 
Proof.
  intros n index contra.
  destruct contra as [p pnEdge].
  destruct pnEdge.
  rewrite index in H0.
  omega.
Qed.

Lemma node_pred_opts : forall N (n : Node),
 In Node N n ->
 TxExists ->
 (exists p, SSEdge p n) \/ (~ exists p, SSEdge p n).
Proof.
  intros N n nInN txEx. unfold TxExists in txEx.
  remember (Node_index n) as i.
  destruct i.
  Case "index = 0".
    remember (Node_smsg n) as smsg.
    destruct smsg.
    SCase "tx".
      right.
      intros contra.
      destruct contra as [p contraE].
      destruct contraE.
      destruct H as [p n t [[Htx Hrx] strandneq]].
      rewrite Hrx in Heqsmsg. inversion Heqsmsg.
      destruct H as [p n Hstrand Hindex].
      rewrite <- Heqi in Hindex. omega.
    SCase "rx".      
      left.
      symmetry in Heqsmsg. destruct (txEx n m Heqsmsg) as [y [ysmsg yedge]].
      exists y. constructor. 
      exact yedge.
  Case "index = S i".
    left. symmetry in Heqi.
    destruct (pred_ex_Sn n i Heqi) as [p [pindex pstrandeq]].
    exists p.
    right. constructor. exact pstrandeq.
    rewrite pindex. rewrite Heqi.
    omega. 
Qed.

Lemma rev_path_imp_edge : forall N n m,
ReversePath' N n m -> 
exists n', ReverseSSEdge' N n n'.
Proof.
  intros N n m revpath.
  induction revpath.
  exists y. exact H.
  exact IHrevpath1.
Qed.

Lemma uniq_pred : forall x y z,
PredEdge x z ->
PredEdge y z ->
x = y.
Proof.
  intros x y z pexz peyz.
  destruct pexz. destruct peyz.
  apply eq_nodes. omega. rewrite H1.
  exact H.
Qed.

Lemma uniq_pred' : forall N x y z,
PredEdge' N x z ->
PredEdge' N y z ->
x = y.
Proof.
  intros N x y z pexz peyz.
  apply pedge'_imp_pedge in pexz.
  apply pedge'_imp_pedge in peyz.
  apply (uniq_pred x y z); auto.
Qed.

Lemma node_revpath_opts : forall N (n : Node),
 Finite Node N ->
 In Node N n ->
 TxExists ->
 UniqTx ->
 (exists m, In Node N m /\ ReversePath' N n m) \/ 
 (~ exists m, In Node N m /\ ReversePath' N n m).
Proof.
  intros N n Fin nInN txEx uniqTx.
  destruct (node_pred_opts N n nInN txEx) as [expred | nopred].
  Case "pred exists".
    destruct expred as [p pnEdge].
    destruct pnEdge.
    SCase "CommEdge".
      destruct (finite_set_mem_dec Node N p node_eq_dec Fin) as [pIn | pnotIn].
      SSCase "p in N".
        left. exists p. split. exact pIn. constructor. constructor. constructor. 
        constructor. exact pIn. exact nInN. exact H.
      SSCase "p not in N".
        remember (Node_index n) as n_index.
        destruct n_index as [| i].
        SSSCase "Node_index n = 0".
          right. intros contra_ex.
          destruct contra_ex as [m [mInN revpathnm]].
          destruct (rev_path_imp_edge N n m revpathnm) as [n' n'edge].
          destruct n'edge. destruct H0. destruct H0.
          assert (p = x) as eqpx. unfold UniqTx in uniqTx. apply (uniqTx p x y); auto.
          subst x. apply pnotIn. exact H0.
          destruct H0. destruct H2. rewrite <- Heqn_index in H3. omega.
        SSSCase "Node_index n = S i".
          symmetry in Heqn_index.
          destruct (pred_ex_Sn n i Heqn_index) as [n' [n'index n'strand]].
          destruct (finite_set_mem_dec Node N n' node_eq_dec Fin) as [n'In | n'notIn].          
          left. exists n'. split. exact n'In. constructor. constructor. right.
          constructor. exact n'In. exact nInN. constructor. 
          exact n'strand. omega. 
          right. intros contra_ex. destruct contra_ex as [m [mInN mpath]].
          induction mpath. destruct H0. destruct H0. destruct H0.
          assert (p = x) as eqpx. unfold UniqTx in uniqTx. apply (uniqTx p x y); auto.
          subst. apply pnotIn. exact H0. destruct H0. destruct H2.
          assert (n' = i0) as eqn'i0.
            apply eq_nodes. omega. rewrite n'strand. symmetry. exact H2.
          subst. contradiction.
          apply IHmpath1; auto.
          eapply rev_path'_imp_in_r. exact mpath1.
    SCase "PredEdge".
      destruct (finite_set_mem_dec Node N p node_eq_dec Fin) as [pIn | pnotIn].
      SSCase "p in N".
        left. exists p. split. exact pIn. constructor. constructor. right. 
        constructor. exact pIn. exact nInN. exact H.
      SSCase "p not in N".
        remember (Node_smsg n) as nsmsg.
          destruct nsmsg.
          SSSCase "tx".
            right.
            intros contra_ex. destruct contra_ex as [q [mInN revnm]].
            induction revnm. destruct H0. destruct H0. destruct H0.
            destruct H2. destruct H2. destruct H2. rewrite <- Heqnsmsg in H4.
            inversion H4.
            assert (p = x).
              eapply uniq_pred. exact H. eapply pedge'_imp_pedge. exact H0.
            subst p. contradiction.
            apply IHrevnm1. exact nInN. exact H. exact Heqnsmsg.
            eapply rev_path'_imp_in_r. exact revnm1.
          SSSCase "rx".
            symmetry in Heqnsmsg.
            unfold TxExists in txEx. destruct (txEx n m Heqnsmsg) as [x [xTx edgexn]].
            destruct (finite_set_mem_dec Node N x node_eq_dec Fin) as [xInN | xnotInN].
            SSSSCase "x in N".
              left. exists x. split. 
              exact xInN. constructor. constructor. constructor. constructor. exact xInN.
              exact nInN. exact edgexn.
            SSSSCase "x not in N".
              right. intros contra_ex.
              destruct contra_ex as [y [yInN revpathny]].
              destruct (rev_path_imp_edge N n y revpathny) as [n' n'edge].
              destruct n'edge. destruct H0. destruct H0.
              assert (x0 = x) as eqpx. unfold UniqTx in uniqTx. apply (uniqTx x0 x y0); auto.
              subst x0. contradiction.
              destruct H0.
              assert (x0 = p). eapply uniq_pred. exact H2. exact H.
              subst. contradiction.
  Case "pred does not exist".
    right. intros expath. apply nopred.
    destruct expath as [m [mInN mpath]].
    induction mpath. destruct H. destruct H. destruct H.
    exists x. left. exact H1.
    destruct H.
    exists x. right. exact H1.
    apply IHmpath1. exact nInN. exact nopred.
    eapply rev_path'_imp_in_r. exact mpath1.
Qed.

Lemma rev_path_imp_tpath : forall N n,
(exists m, ReversePath' N n m) ->
exists l, TPath' (ReverseSSEdge' N) l n.
Proof.
  intros N n exrevpath.
  destruct exrevpath as [m path].
  induction path.
  Case "single edge".
    exists [x, y].
    constructor; auto.
  Case "x-y y-z".
    destruct IHpath1 as [lx tpathlx].
    exists lx.
    exact tpathlx.
Qed.

Lemma acyc_imp_acyc_rev_path' : forall N x,
Acyclic_Nodes N -> 
In Node N x -> ~(ReversePath' N x x).
Proof.
  intros N x acyc xInN contra.
  apply (acyc x). exact xInN.
  apply (epath'_imp_epath N).
  apply rev_path'_imp_epath'. exact contra.
Qed.  

Lemma irreflexive_revpath_imp_nodup : forall N l,
(forall x, ~(ReversePath' N x x)) ->
TPath (ReverseSSEdge' N) l ->
NoDup l.
Proof.
  intros N l noRevxx tpathl.
  induction l.
  constructor.
  destruct (in_dec node_eq_dec a l) as [Inl | notInl].
  Case "a In l".
    destruct (rest_mem_imp_tpath'' (ReverseSSEdge' N) l a a Inl tpathl) as [laa tpathaa].
    assert False as F. apply (noRevxx a).
    apply (tpath_imp_trans (ReverseSSEdge' N) laa a a tpathaa). inversion F.
  Case "a not In l".
    destruct l.
    constructor. exact notInl. constructor.
    destruct l. constructor. exact notInl. constructor. auto. constructor.
    constructor. exact notInl. apply IHl.
    inversion tpathl; subst. exact H2.
Qed.

Lemma rev_tpath_max_len : forall N n,
Acyclic_Nodes N ->
Finite Node N ->
(exists l, TPath' (ReverseSSEdge' N) l n) ->
(exists lmax, TPath' (ReverseSSEdge' N) lmax n /\
forall l', TPath' (ReverseSSEdge' N) l' n -> length l' <= length lmax).
Proof.
  intros N n Nacyc Nfin extpath.
  destruct extpath as [l tpathl].
  destruct l. inversion tpathl. inversion H0.
  assert (n = n0) as triv_eq. inversion tpathl; subst. simpl in H. inversion H. reflexivity.
  subst n0.
Admitted. (* TODO!! *)

Lemma max_tpath_imp_max_rev_path : forall N n,
(exists lmax, TPath' (ReverseSSEdge' N) lmax n /\
forall l', TPath' (ReverseSSEdge' N) l' n -> length l' <= length lmax) ->
exists y, In Node N y /\
(ReversePathEq' N n y /\ (forall z, ReversePathEq' N y z -> y = z)).
Admitted. (* TODO!! *)

Lemma finite_rev_path_end : forall N n,
Finite Node N ->
Acyclic_Nodes N ->
TxExists ->
UniqTx ->
In Node N n ->
exists y, In Node N y /\
(ReversePathEq' N n y /\ (forall z, ReversePathEq' N y z -> y = z)).
Proof.
  intros N n Hfin Nacyc txEx uniqTx nInN.
  destruct (node_revpath_opts N n Hfin nInN txEx uniqTx) as [Hpath | Hnopath].
  Case "ReversePath Exists".
    destruct Hpath as [m [mInN pathnm]].
    apply max_tpath_imp_max_rev_path.
    apply rev_tpath_max_len.
    exact Nacyc. exact Hfin.
    apply rev_path_imp_tpath.
    exists m. exact pathnm.
  Case "No ReversePath".
    exists n. split. exact nInN. split.
    constructor. exact nInN.
    intros z revpatheqnz.
    destruct revpatheqnz. reflexivity.
    assert False as F.
    apply Hnopath.  exists y.
    split. eapply rev_path'_imp_in_r. exact H. exact H.
    inversion F.
Qed.

Lemma bundle_minimal_ex : forall N E N',
Bundle N E ->
Included Node N' N ->
(exists x, In Node N' x) ->
(exists min, subset_minimal N' min).
Proof.
  intros N E N' B I N'ex.
  destruct N'ex as [x xInN'].
  inversion B as [N'' E' HVN HVE [[txEx txIn] uniqTx] HPredMem Hacyc]. subst.
  destruct HVN as [N E [Hfin HInE]].
  assert (Finite Node N') as HfinN'.
    eapply Finite_downward_closed.
    exact Hfin. exact I.
  assert (Acyclic_Nodes N') as N'acyc.
    unfold Acyclic_Nodes. intros n nInN'. unfold Acyclic_Node.
    apply Hacyc. apply I. exact nInN'.
  destruct (finite_rev_path_end N' x HfinN' N'acyc txEx uniqTx xInN') as [y [yInN' [Hrevxy Hend]]].
  exists y. 
  constructor. exact yInN'. clear xInN' yInN'.
  intros z zneqy zInN' epatheqny.
  apply zneqy. symmetry. apply (Hend z). clear zInN'.
  apply epatheq'_imp_rev_patheq'. exact epatheqny.
Qed.


(*

  -------- Function to find minimal node --------- 
  Is there a previous node in this set of nodes?
  No? It's minimal! return this element
  Yes?
      Recursively call this Fixpoint with this new node
       and with the set of nodes minus this new node 
  -----------------------------------------------

  What is needed for this to work???
   -- option Node function to get a previous Node or None
   -- proofs regarding the fact that this process actualy produces a 
      minimal node


 *)