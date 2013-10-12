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
Require Import CoLoRRelDec CoLoRRelSub.

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
| msg_key  : Key  -> Msg
| msg_join : Msg  -> Msg -> Msg 
| msg_encr : Key  -> Msg -> Msg.
(* [REF 1] Section 2.1 pg 5 
           Section 2.3 pg 9 *)
(* [REF 2] pg 4 paragraph 3 (details of encryption and subterms) *)
Hint Constructors Msg.


Notation "(! x )" := (msg_text x). 
Notation "(# k )" := (msg_key k).
Notation "x * y" := (msg_join x y) (at level 40, left associativity). 
Notation "[ m ]^( k ) " := (msg_encr k m).


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
| st_join_l : forall st l r, 
               Subterm st l -> Subterm st (l*r)
| st_join_r : forall st l r, 
               Subterm st r -> Subterm st (l*r)
| st_encr : forall st t k, 
               Subterm st t -> Subterm st ([t]^(k)).
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

Notation "(+ x )" := (tx x).
Notation "(- x )" := (rx x).

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
Definition KeySet := Ensemble Key.
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

Notation "index( x )" := (Node_index x).

(* strand of a node *)
Definition Node_strand (n:Node) : Strand :=
  match n with
    | exist npair _ 
      => fst npair
  end.
(* [REF 1] Definition 2.3.2 pg 6
   "If n = <s,i> then ... strand(n) = s." *)

Notation "strand( x )" := (Node_strand x).

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

Notation "smsg( x )" := (Node_smsg x).

(* unsigned message of a node *)
Definition Node_msg (n:Node) : Msg :=
  match Node_smsg n with
    | tx t => t
    | rx t => t
  end. 
(* [REF 1] Definition 2.3.2 pg 6
   "Define uns_term(n) to be the unsigned part of the ith signed term 
    of the trace of s." *)

Notation "msg( x )" := (Node_msg x).

Lemma node_smsg_msg_tx : forall n t,
smsg(n) = (+ t) ->
msg(n) = t.
Proof.
  intros n t nsmsg.
  unfold Node_msg. rewrite nsmsg. reflexivity. 
Qed.

Lemma node_smsg_msg_rx : forall n t,
smsg(n) = (- t) ->
msg(n) = t.
Proof.
  intros n t nsmsg.
  unfold Node_msg. rewrite nsmsg. reflexivity. 
Qed.

Definition is_tx (n:Node) : Prop :=
exists t, Node_smsg n = (+ t).

Definition is_rx (n:Node) : Prop :=
exists t, Node_smsg n = (- t).

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
index(x) = index(y) ->
strand(x) = strand(y) ->
x = y.
Proof.
  intros [[xs xn] xp] [[ys yn] yp] eq_index eq_strand.
  simpl in eq_index. simpl in eq_strand. subst.
  rewrite (proof_irrelevance (lt yn (length ys)) xp yp). reflexivity.
Qed.

Lemma node_imp_strand_nonempty : forall s n,
strand(n) = s ->
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

Notation "a --> b" := (Comm a b) (at level 30, right associativity). 

Lemma comm_dec : forall x y,
{x --> y} + {~ x --> y}.
Proof.
  intros x y.
  remember (Node_smsg x) as xsmsg. remember (Node_smsg y) as ysmsg.
  remember (Node_strand x) as xstrand. remember (Node_strand y) as ystrand.
  destruct xsmsg.
  Case "x (tx m)".
    destruct ysmsg.
    SCase "y (tx m0)".
      right. intros contracomm. inversion contracomm; subst.
      destruct H as [[xtx yrx] strandneq].
      rewrite <- Heqysmsg in yrx. inversion yrx.      
    SCase "y (rx m0)".
      destruct (eq_msg_dec m m0) as [msgeq | msgneq].
      SSCase "m = m0".
        destruct (eq_strand_dec xstrand ystrand) as [strandeq | strandneq].
        SSSCase "strands eq".
          right. intros contracomm.
          inversion contracomm; subst. destruct H as [msgs strandsneq].
          apply strandsneq. exact strandeq. 
        SSSCase "strands neq".
          subst m0. left.
          apply (comm x y m). split. split.
          auto. auto. subst. exact strandneq.        
      SSCase "m <> m0".
        right. intros contracomm. inversion contracomm; subst. 
        destruct H as [[xtx yrx] strandneq].
        apply msgneq. rewrite <- Heqxsmsg in xtx.
        rewrite <- Heqysmsg in yrx. inversion xtx; subst. 
        inversion yrx; subst. reflexivity.
  Case "x (rx m)".
    right.
    intros contracomm. inversion contracomm; subst.
    destruct H as [[xtx yrx] strandneq].
    rewrite <- Heqxsmsg in xtx. inversion xtx.
Qed.

Theorem comm_irreflexivity : forall n,
~ n --> n.
Proof.
  intros n contraedge.
  inversion contraedge; subst.
  destruct H as [[txsmsg rxsmsg] strandneq].
  apply strandneq. reflexivity.
Qed.
Hint Resolve comm_irreflexivity.

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

(* successor edge *)
(* node's direct predecessor -> node -> Prop *)
Inductive Successor : relation Node :=
| succ : forall i j, strand(i) = strand(j) 
                       -> index(i) + 1 = index(j) 
                       -> Successor i j.
(* [REF 1] Definition 2.3.4 pg 6
   "When n1= <s,i> and n2=<s,i+1> are members of N (set of node), there is
    an edge n1 => n2." *)

Notation "a ==> b" := (Successor a b)  (at level 30, right associativity). 

Lemma succ_dec : forall x y,
{x ==> y} + {~ x ==> y}.
Proof.
  intros x y.
  remember (Node_index x) as xi. remember (Node_index y) as yi.
  remember (Node_strand x) as xstrand. remember (Node_strand y) as ystrand.
  destruct (eq_strand_dec xstrand ystrand) as [seq | sneq].
  Case "strands eq".
    destruct (eq_nat_dec yi (S xi)) as [succi | wrongi].
    SCase "yi = S xi". left. apply (succ x y). rewrite <- Heqxstrand.
      rewrite <- Heqystrand.  exact seq. omega.
    SCase "yi <> S xi".
      right. intros contrasucc. apply wrongi. inversion contrasucc; subst; omega.
  Case "strands neq".
    right. intros contrasucc. apply sneq. inversion contrasucc; subst; auto.
Qed.  

Theorem succ_irreflexivity : forall n,
~n ==> n.
Proof.
  intros n edge.
  inversion edge; subst. omega.
Qed.
Hint Resolve succ_irreflexivity.

Theorem succ_antisymmetry :
Antisymmetric Node Successor.
Proof.
  intros n m Hpe1 Hpe2.
  destruct Hpe1. destruct Hpe2.
  rewrite <- H0 in H2. omega.
Qed.
Hint Resolve succ_antisymmetry.

(* succecessor multi edge (not nec. immediate succecessor) *)
(* node's eventual succecessor -> node -> Prop *)
Definition StrandPath : relation Node := 
clos_trans Successor.
 (* [REF 1] Definition 2.3.4 pg 6
   "ni =>+ nj means that ni precedes nj (not necessarily immediately) on
    the same strand." *)
Hint Constructors clos_trans.

Notation "a ==>+ b" := (StrandPath a b)  (at level 30, right associativity). 

Lemma spath_imp_eq_strand : forall x y,
x ==>+ y -> strand(x) = strand(y).
Proof.
  intros x y path.
  induction path.
  Case "step".
    destruct H; auto.
  Case "trans".
    rewrite IHpath1.
    rewrite IHpath2.
    reflexivity.
Qed.
Hint Resolve spath_imp_eq_strand.

Lemma spath_imp_index_lt : forall x y,
x ==>+ y -> index(x) < index(y).
Proof.
  intros x y path.
  induction path.
  Case "step". inversion H; subst. omega.
  Case "trans". omega.
Qed.
Hint Resolve spath_imp_index_lt.

Lemma spath_irreflexivity : forall n,
~ n ==>+ n.
Proof.
  intros n contra.
  apply spath_imp_index_lt in contra.
  omega.
Qed.
Hint Resolve spath_irreflexivity.

Theorem spath_transitivity :
Transitive Node StrandPath.
Proof.
  intros i j k Hij Hjk.
  apply (t_trans Node Successor i j k Hij Hjk).
Qed.
Hint Resolve spath_transitivity.

Definition SSEdge : relation Node :=
union Comm Successor.
Hint Constructors or.

Notation "a =-> b" := (SSEdge a b) (at level 30, right associativity). 

Lemma ssedge_dec : forall x y,
{x =-> y} + {~x =-> y}.
Proof.
  intros x y.
  destruct (comm_dec x y) as [cxy | nocxy].
  Case "Comm x y".
    left. left. exact cxy.
  Case "~Comm x y".
    destruct (succ_dec x y) as [pxy | nopxy].
    SCase "Successor x y".
      left. right. exact pxy.
    SCase "~Successor x y".
      right. intros contrass.
       destruct contrass.
       SSCase "false Comm".
         apply nocxy; exact H.
       SSCase "false Successor".
         apply nopxy; exact H.
Qed.

Theorem ssedge_irreflexivity : forall n,
~ n =-> n.
Proof.
  intros n Hedge.
  inversion Hedge; subst; auto.
  eapply (comm_irreflexivity); eauto.
  eapply (succ_irreflexivity); eauto.
Qed.
Hint Resolve ssedge_irreflexivity.

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

(* transitive closure of edges. *)
Definition SSPath : relation Node := 
clos_trans SSEdge.

Notation "a << b" := (SSPath a b) (at level 30, right associativity). 

Theorem spath_imp_sspath : forall i j,
i ==>+ j -> i << j.
Proof.
  unfold SSPath.
  intros i j Hpath.
  induction Hpath.
  constructor. right. exact H.
  apply (t_trans Node SSEdge x y z IHHpath1 IHHpath2).
Qed.  

Theorem sspath_transitivity :
Transitive Node SSPath.
Proof.
  unfold SSPath.
  intros i j k Hij Hjk.
  apply (t_trans Node SSEdge i j k Hij Hjk).
Qed.

(* transitive reflexive closure of edges. *)
Definition SSPathEq : relation Node :=
clos_refl_trans SSEdge.
Hint Constructors clos_refl_trans.

Notation "a <<* b" := (SSPathEq a b) (at level 30, right associativity). 

Theorem sspatheq_opts: forall n m,
n <<* m -> n << m \/ n = m.
Proof.
  intros n m Hpatheq.
  induction Hpatheq.
  left. apply t_step. exact H.
  right. reflexivity.
  destruct IHHpatheq1 as [pathxy | eqxy].
    destruct IHHpatheq2 as [pathyz | eqyz].
      left. eapply t_trans. exact pathxy. exact pathyz.
      subst y. left. exact pathxy.
    destruct IHHpatheq2 as [pathyz | eqyz].
      subst x. left. exact pathyz.
      right. subst. reflexivity.
Qed.

Theorem sspatheq_transitivity :
Transitive Node SSPathEq.
Proof.
  unfold Transitive.
  intros i j k Hij Hjk.
  destruct Hij. 
    eapply rt_trans. eapply rt_step. exact H. 
    exact Hjk. exact Hjk. 
    eapply rt_trans. exact Hij1. eapply rt_trans.
    exact Hij2. exact Hjk.
Qed.

(* In for members of pairs *)
Inductive InPair {X:Type} (E:Ensemble (X*X)) (x:X): Prop :=
| inp_l : (exists y, In (X*X) E (x,y))
          -> InPair E x
| inp_r : (exists y, In (X*X) E (y,x))
          -> InPair E x.
Hint Constructors InPair.

(* * * * * BUNDLE DEFINITION * * * * *)
Inductive ValidEdges (N: NodeSet) (E: EdgeSet) : Prop :=
| validedges :
    (* N is the set of nodes incident with any edge in E *)
    (and (forall x, InPair E x -> In Node N x)
    (* edges and the SSEdge property are equivalent *)
         (forall x y, In Edge E (x,y) <-> x =-> y))
    -> ValidEdges N E.
(* TODO justification *)

Definition ExistsUniqueTx (N:NodeSet) (E:EdgeSet) : Prop :=
  (forall z m, In Node N z ->
              smsg(z) = (- m) -> 
              (* there exists a transmitter *)
              (exists x, (smsg(x) = (+ m)
                          /\ x --> z
                          /\ In Edge E (x,z)))
              (* a transmitter is unique *)
              /\ (forall x y, x --> z ->
                              y --> z ->
                              x = y)).
(* TODO justification *)

Definition Acyclic (N:NodeSet) (E:EdgeSet) : Prop :=
forall x, ~ x << x.
(* TODO justification *)

Definition Bundle (N:NodeSet) (E:EdgeSet) : Prop :=
             Finite Node N /\
             Finite Edge E /\
             ValidEdges N E /\
             ExistsUniqueTx N E /\
             Acyclic N E.

Lemma bundle_ssedge_inclusion : forall N E n m,
Bundle N E ->
n =-> m ->
(In Node N n -> In Node N m) /\ (In Node N m -> In Node N n).
Proof.
  intros N E n m B ssedge. split; intros Hin.
  destruct B as [finN [finE [valE [uniqtx acyc]]]].
  apply valE in ssedge. apply valE. constructor 2.
  exists n. exact ssedge.
  destruct B as [finN [finE [valE [uniqtx acyc]]]].
  apply valE in ssedge. apply valE. constructor 1.
  exists m. exact ssedge.
Qed.

Definition bundle_set (s: ListSet.set Node) (N:NodeSet) : Prop :=
forall x, ListSet.set_In x s <-> In Node N x.
             
Lemma sspath_imp_ssedge_l : forall x y,
x << y ->
exists x', x =-> x'.
Proof.
  intros x y sspath.
  induction sspath.
  exists y. exact H.
  exact IHsspath1.
Qed.  

Lemma sspath_imp_ssedge_r : forall x y,
x << y ->
exists y', y' =->  y.
Proof.
  intros x y sspath.
  induction sspath.
  exists x. exact H.
  exact IHsspath2.
Qed.  

Lemma restricted_to_set : forall N E,
Bundle N E ->
exists s, is_restricted SSEdge s /\
forall x, ListSet.set_In x s <-> In Node N x.
Proof.
  intros N E B.
  destruct B as [finN [finE [valE [uniqtx acyc]]]].
  destruct valE as [[EimpInN EimpSSEdge]].
  destruct (ensemble_imp_set Node eq_node_dec N finN) 
    as [s [inAll [nodup [n [slen scard]]]]].
  exists s.
  split.
  intros x y sspath.
  split.
  apply inAll. apply EimpInN. constructor. exists y. 
  apply EimpSSEdge. exact sspath.
  apply inAll. apply EimpInN. constructor 2. exists x. 
  apply EimpSSEdge. exact sspath.
  exact inAll.
Qed.

Lemma sspath_dec : forall N E s,
Bundle N E ->
bundle_set s N ->
is_restricted SSEdge s ->
forall x y, {x << y} + {~x << y}.
Proof.
  intros N E s B bset restrict.
  destruct B as [finN [finE [valE [uniqtx acyc]]]].
  intros x y.
  remember (restricted_dec_clos_trans_dec 
              eq_node_dec 
              ssedge_dec 
              restrict) as alldec.
  apply alldec.
Qed.

Lemma neq_sspatheq_imp_sspath : forall x y,
x <> y ->
x <<* y ->
x << y.
Proof.
  intros x y neq patheqxy.
  induction patheqxy.
  Case "SSEdge x y".
    apply t_step. exact H.
  Case "x = y". assert False as F. apply neq. reflexivity. inversion F.
  Case "x y z".
    destruct (eq_node_dec y z) as [eqyz | neqyz].
    SCase "y = z". subst y. apply IHpatheqxy1. exact neq.
    SCase "y <> z". 
      destruct (eq_node_dec x y) as [eqxy | neqxy].
      SSCase "x = y". subst x. apply IHpatheqxy2. exact neqyz.
      SSCase "x <> y". eapply t_trans. apply IHpatheqxy1. exact neqxy.
        apply IHpatheqxy2. exact neqyz.
Qed.      

Lemma sspatheq_trans_cycle : forall x y,
x <> y ->
x <<* y ->
y <<* x ->
x << x.
Proof.
  intros x y neq patheqxy patheqyx.
  eapply t_trans.
  Case "path x y".
    eapply neq_sspatheq_imp_sspath. exact neq. exact patheqxy.
  Case "path y x".
    eapply neq_sspatheq_imp_sspath. intros contra. subst.
    apply neq. reflexivity.
    exact patheqyx.
Qed.

Lemma bunble_partial_order : forall N E,
Bundle N E ->
Order Node SSPathEq.
Proof.
  intros N E B.
  split.
  Case "Reflexivity".
    intros x. apply rt_refl. 
  Case "Transitivity".
    intros x y z xy yz.
    eapply rt_trans. exact xy. exact yz.
  Case "AntiSymmetry".
    intros x y xy yz.
    destruct B as [finN [finE [valE [uniqtx acyc]]]].
    destruct (eq_node_dec x y) as [xyeq | xyneq].
    SCase "x = y". exact xyeq.
    SCase "x <> y". 
      assert (x << x) as contraxx.
        eapply sspatheq_trans_cycle. exact xyneq.
        exact xy. exact yz. apply acyc in contraxx. inversion contraxx.
Qed.

Lemma sspath_strict_order : forall N E,
Bundle N E ->
StrictOrder Node SSPath.
Proof.
  intros N E B.
  destruct B as [finN [finE [valE [uniqtx acyc]]]].
  split.
  Case "Irreflexivity".
    intros x. apply acyc.
  Case "Transitivity".
    apply sspath_transitivity.
Qed.

Definition set_minimal (N:NodeSet) (n:Node) : Prop :=
In Node N n /\
(forall x, In Node N x ->
           ~ x << n).

Lemma bundle_subset_minimal : forall N E N',
Bundle N E ->
Included Node N' N ->
N' <> Empty_set Node ->
exists min, set_minimal N' min.
Proof.
  intros N E N' B incl nempty.
  assert (Bundle N E) as bundle. exact B.
  destruct B as [finN [finE [valE [uniqtx acyc]]]].
  assert (Finite Node N') as finN'. eapply Finite_downward_closed.
    exact finN. exact incl.
  destruct (finite_cardinal Node N' finN') as [n card].
  destruct n. inversion card. rewrite H in nempty.
  assert False as F. apply nempty. reflexivity. inversion F.
  destruct (restricted_to_set N E bundle) as [s [restricted setequiv]].
  assert (forall x y, {x << y} + {~ x << y}) as rdec.
  apply (sspath_dec N E s bundle). exact setequiv. exact restricted.  
  destruct (minimal_finite_ensemble_mem 
              Node 
              eq_node_dec 
              SSPath 
              rdec
              (sspath_strict_order N E bundle) 
              N' 
              n 
              card) as [min [minIn nolt]].
  exists min. split. exact minIn. exact nolt.
Qed.

(* Lemma 2.8 - set minimal is tx *)
Lemma minimal_is_tx : forall N E N',
Bundle N E ->
Included Node N' N ->
(forall m m', (In Node N m 
               /\ In Node N m'
               /\ msg(m) = msg(m')) -> (* ADDED in N conditions *)
               (In Node N' m <-> In Node N' m')) ->
forall n, set_minimal N' n ->
is_tx n.
Proof.
  intros N E N' bundle sub incl n setmin.
  remember bundle as B.
  destruct bundle as [finN [finE [valE [uniqtx acyc]]]].
  remember (Node_smsg n) as nsmsg. symmetry in Heqnsmsg.
  destruct nsmsg.
  exists m. exact Heqnsmsg.
  unfold ExistsUniqueTx in uniqtx.
  assert (In Node N n) as nIn. destruct setmin; auto.
  destruct (uniqtx n m nIn Heqnsmsg) as [[ntx [ntxsmsg [commn inE]]] uniq].
  assert False as F. destruct setmin. apply (H0 ntx). eapply incl.
    split. eapply bundle_ssedge_inclusion. exact B. constructor. exact commn.
    exact nIn. split. exact nIn.
    apply node_smsg_msg_rx in Heqnsmsg. apply node_smsg_msg_tx in ntxsmsg.
    rewrite ntxsmsg. symmetry. exact Heqnsmsg. exact H.
    constructor. constructor. exact commn.
  inversion F.
Qed.

Definition OccursIn (t:Msg) (n:Node) : Prop :=
Subterm t msg(n).
 (* [REF 1] Definition 2.3.5 pg 6
   "An unsigned term t occurs in n iff t is a subterm of the term of n" *)

(* As close to paper def as possible *)
Definition EntryPoint (n:Node) (I: Ensemble Msg) : Prop :=
(exists t, In Msg I t /\ smsg(n) = (+ t))
/\ forall n', n' << n -> ~ In Msg I msg(n').
 (* [REF 1] Definition 2.3.6 pg 6
   "Suppose I is a set of unsigned terms. The node n is an entrypoint for I
    iff term(n) = +t for some t in I, and forall n' s.t. n' =>+ n, term(n')
    is not in I." *)

(* As close to paper def as possible *)
Definition Origin_with_Ex_Set (t:Msg) (n:Node) : Prop :=
exists I, (forall t', Subterm t t' <-> In Msg I t')
/\ EntryPoint n I.
 (* [REF 1] Definition 2.3.7 pg 6
   "An unsigned term t originates on n iff n is an entry point
    for the set I = {t' : t is a subterm of t'}" *)

Definition Origin (t:Msg) (n:Node) : Prop :=
is_tx n
/\ Subterm t msg(n)
/\ forall n', n' << n -> ~Subterm t msg(n').

Lemma Origin_imp_strict_defs : forall I t n,
(forall t', Subterm t t' <-> In Msg I t') ->
Origin t n ->
Origin_with_Ex_Set t n.
Proof.
  intros I t n Iprop Orig.
  exists I. split. exact Iprop.
  destruct Orig as [ntx [nsub nosucc]].
  split. exists (Node_msg n).
  split. apply Iprop in nsub. exact nsub.
  destruct ntx. erewrite node_smsg_msg_tx. exact H. exact H.
  intros n' succ contraIn.
  apply nosucc in succ. apply Iprop in contraIn. contradiction.
Qed.

Definition UniqOrigin (t:Msg) : Prop :=
exists n, Origin t n
/\ forall m, Origin t m -> n = m.
 (* [REF 1] Definition 2.3.8 pg 7
   "An unsigned term t is uniquely originating iff t originates on
    a unique n." *)

(* Lemma 2.9 *)
Lemma min_origin : forall N E N' n t,
Bundle N E ->
(forall m, (In Node N m 
           /\ Subterm t msg(m)) <-> 
           In Node N' m) ->
set_minimal N' n ->
Origin t n.
Proof.
  intros N E N' n t bundle N'def nmin.
  remember bundle as B.
  destruct bundle as [finN [finE [valE [uniqtx acyc]]]].
  assert (In Node N' n) as nIn. destruct nmin; auto.
  assert (Subterm t (Node_msg n)) as tsubn.
    apply (N'def n) in nIn. destruct nIn; auto.
  assert (is_tx n) as nistx.
    assert (Included Node N' N) as incl.
      intros x xIn. apply N'def in xIn. destruct xIn; auto.
    apply (minimal_is_tx N E N' B incl).
    intros x y eqmsg.
    destruct eqmsg as [xIn [yIn eqmsg]].
    split; intros Hin.
    Case "m in -> m' in".
      apply N'def in Hin. destruct Hin as [xInN tsubx]. 
      assert (Subterm t (Node_msg y)) as ysubt. rewrite <- eqmsg.
        exact tsubx.
      apply N'def. split. exact yIn. exact ysubt.
    Case "m' in -> m in".
      apply N'def in Hin. destruct Hin as [yInN tsuby].
      apply N'def. split. exact xIn. 
      assert (Subterm t (Node_msg x)) as xsubt. rewrite eqmsg.
        exact tsuby.
      exact xsubt. 
    exact nmin.
  split. exact nistx.
  split. exact tsubn.
  intros n' succn' contrasub.
  assert (In Node N' n') as n'In.
    apply N'def. split.
    destruct valE as [[pairImpN HInEedge]].
    apply pairImpN. left.
    destruct (sspath_imp_ssedge_l n' n succn') as [x n'edge].
    exists x. apply HInEedge. exact n'edge. exact contrasub.
  destruct nmin as [nIn2 noprev]. apply (noprev n'). exact n'In.
  exact succn'.
Qed.

(* Axiom 1 -- provable in this context *)
Theorem free_encryption : forall m1 m2 k1 k2,
[m1]^(k1) = [m2]^(k2) -> m1 = m2 /\ k1 = k2.
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
/\ m * n <> [m']^(k)
/\ (#k) <> m * n
/\ (!t) <> m * n
/\ (#k) <> [m]^(k')
/\ (!t) <> [m]^(k).
Proof.
  intros m m' n n' k k' t;
  split. intros eq. inversion eq; auto. 
  split. intros F. inversion F.
  split. intros F. inversion F.
  split. intros F. inversion F.
  split. intros F. inversion F.
  intros F. inversion F.
Qed.

Fixpoint msg_width (m:Msg) : nat :=
match m with
| msg_text _ => 1
| msg_key _ => 1
| msg_encr _  _ => 1
| msg_join x y => msg_width x + msg_width y
end.
(* [REF 1] Definition 2.10 *)

Notation "width( m )" := (msg_width m).

(* Proposition 2.12 *)
Lemma encr_subterm_imp : forall k k' h h',
k <> k' ->
Subterm [h']^(k') [h]^(k) ->
Subterm [h']^(k') h.
Proof.
  intros k k' h h' kneq st.
  inversion st; subst.
  assert False. apply kneq. reflexivity. contradiction.
  exact H1.
Qed.

Definition PrincipalAlignment := Strand -> Prop.
Variable Regular : PrincipalAlignment.
Variable Inv : relation Key.

Inductive Penetrator : KeySet -> PrincipalAlignment :=
| pM : forall K s g, 
        ~Regular s ->
        s = [(+g)] -> 
        Penetrator K s
| pF : forall K s g, 
        ~Regular s ->
        s = [(-g)] -> 
        Penetrator K s
| pT : forall K s g, 
        ~Regular s ->
        s = [(-g), (+g), (+g)] ->
        Penetrator K s
| pC : forall K s g h, 
        ~Regular s ->
        s = [(-g), (-h), (+g*h)] ->
        Penetrator K s
| pS : forall K s g h, 
        ~Regular s ->
        s = [(-g*h), (+g), (+h)] ->
        Penetrator K s
| pK : forall K s k, 
        ~Regular s ->
        In Key K k ->
        s = [(+ (#k))] ->
        Penetrator K s
| pE : forall K s h k,
        ~Regular s ->
        s = [(- (#k)), (-h), (+ [h]^(k))] ->
        Penetrator K s
| pD : forall K s h k k',
        ~Regular s ->
        Inv k' k ->
        s = [(- (#k')), (- [h]^(k)), (+h)] ->
        Penetrator K s.

