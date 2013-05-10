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

Require Import List ListSet Arith Peano_dec Omega ProofIrrelevance.

(* Represent atomic messages, *)
Variable text : Set.
Variable text_eq_dec : forall (x y:text), {x = y} + {x <> y}.
Hint Resolve text_eq_dec.

(* representing kryptographic key *)
Variable key : Set.
Variable key_eq_dec : forall (x y:key), {x = y} + {x <> y}.
Hint Resolve key_eq_dec.
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
Inductive msg : Type :=
| mtext : text -> msg
| mcons : msg -> msg -> msg 
| mcrypt : key -> msg -> msg.
(* [REF 1] Section 2.1 pg 5 
           Section 2.3 pg 9 *)
(* [REF 2] pg 4 paragraph 3 (detains of encryption and subterms) *)
Hint Constructors msg.


Definition msg_eq_dec : forall x y : msg,  
  {x = y} + {x <> y}.
Proof.
  decide equality.
Qed.
Hint Resolve msg_eq_dec.

Definition msg_in_set (m:msg) (s:set msg) : bool := 
  set_mem msg_eq_dec m s.


(* subterm relationship for messages *)
(* subterm -> larger encapsulating term -> Prop *)
Inductive subterm : msg -> msg -> Prop :=
| strefl : forall m, subterm m m
(* | stcryp : forall a g, subterm a g -> subterm a encrpt(g)  *)
| stcons_l : forall st l r, 
               subterm st l -> subterm st (mcons l r)
| stcons_r : forall st l r, 
               subterm st r -> subterm st (mcons l r)
| stcrpyt : forall st t k, 
              subterm st t -> subterm st (mcrypt k t).
(* [REF 1] Definition 2.1 pg 6 and Definition 2.11 *)
Hint Constructors subterm.

(* signed message, + (tx) or - (rx) *)
Inductive smsg : Type := 
| tx : msg -> smsg
| rx : msg -> smsg.
(* [REF 1] Definition 2.1 pg 6 
   They are defined as a pair, w/ the first member being in {+, -} 
   and the second a signed message. *)
Hint Constructors smsg.

Definition smsg_eq_dec : forall x y : smsg,  
  {x = y} + {x <> y}.
Proof.
 intros. decide equality.
Qed. 
Hint Resolve smsg_eq_dec.

(* strand *)
Definition strand : Type := list smsg.
(* [REF 1] First sentence of Abstract: "sequence of events"  
   Haven't hit a better def, and they start using strands
   pretty early so I'm rolling with this. *)


Definition strand_eq_dec : forall x y : strand,  
  {x = y} + {x <> y}.
Proof.
 intros. decide equality.
Qed.
Hint Resolve strand_eq_dec.

Definition strand_in_set (s:strand) (ss:set strand) : bool := 
  set_mem strand_eq_dec s ss.

(* strand space *)
Inductive sspace : Type :=
| space : set msg -> set strand -> sspace.
(* [REF 1] Definition 2.2 pg 6 "A strand space over A (set of possible msgs) is a set
    E with a trace mapping tr : E -> list smsg *)

Definition ss_msgs (ss:sspace) : set msg :=
 match ss with
  | space m_set s_set => m_set
 end.

Definition ss_strands (ss:sspace) : set strand :=
 match ss with
  | space m_set s_set => s_set
 end.


(* node in a strand space *)
Definition node : Type := {n: (prod strand nat) | (snd n) < (length (fst n))}.
(* [REF 1] Definition 2.3.1 pg 6
   -"A node is a pair <s,i> where s is a strand and i a nat in [0, (length s))"
     NOTE: I changed it to be 0 based instead of 1 based sequences
   -"node <s,i> belongs to strand s"
   -"Every node belongs to a unique strand" *)

(* index of a node *)
Definition n_index (n:node) : nat :=
  match n with
    | exist npair _ 
      => snd npair
  end.
(* [REF 1] Definition 2.3.2 pg 6
   "If n = <s,i> then index(n) = i. *)

(* strand of a node *)
Definition n_strand (n:node) : strand :=
  match n with
    | exist npair _ 
      => fst npair
  end.
(* [REF 1] Definition 2.3.2 pg 6
   "If n = <s,i> then ... strand(n) = s. *)

(* signed message of a node *)
Fixpoint n_smsg_option (n:node) : (option smsg) :=
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

Theorem n_smsg_valid : forall (n:node),
{m:smsg | Some m = n_smsg_option n}.
(* exists (m:smsg), Some m = (n_smsg_option n). *)
Proof.
  intros n.
  remember (n_smsg_option n) as funcall.
  destruct n. destruct funcall.  
  exists s. reflexivity.

  unfold n_smsg_option in Heqfuncall.
  destruct x. simpl in l.
  apply nth_error_len in Heqfuncall.
  omega.
Qed.


Definition n_smsg (n:node) : smsg :=
 match n_smsg_valid n with
     | exist m _ => m
 end.

(* unsigned message of a node *)
Fixpoint n_msg (n:node) : msg :=
  match n_smsg n with
    | tx t => t
    | rx t => t
  end. 
(* [REF 1] Definition 2.3.2 pg 6
   "Define uns_term(n) to be the unsigned part of the ith signed term 
    of the trace of s." *)

Definition node_eq_dec : forall x y : node,
 {x = y} + {x <> y}.
Proof.
  intros [[xs xn] xp] [[ys yn] yp].
  destruct (strand_eq_dec xs ys) as [EQs | NEQs]; subst.
  destruct (eq_nat_dec xn yn) as [EQn | NEQn]; subst.
  left. rewrite (proof_irrelevance (lt yn (length ys)) xp yp). reflexivity.

  right. intros C. inversion C. auto.
  right. intros C. inversion C. auto.
Qed.

Definition node_in_set (n:node) (ns: set node) : bool :=
  set_mem node_eq_dec n ns.

(* To reason about the set of nodes in a strand space *)
Definition node_in_ss (n:node) (ss:sspace) : bool := 
 strand_in_set (n_strand n) (ss_strands ss).
(* [REF 1] Definition 2.3.1 pg 6
   The reference to the "set of nodes (N) in a given strand space." *)

(* Set of all nodes in a strand space *)
Definition nodeset (ss:sspace) : Type := {ns: set node | forall n, (true = node_in_ss n ss) 
                                                                   <-> true = node_in_set n ns}.
(* [REF 1] Definition 2.3.1 pg 6
   The set of nodes (in a strand space) is denoted by N. *)

Inductive comm_E : node -> node -> Prop :=
| commE :  forall n m, (exists a, (and ((n_smsg n) = (tx a)) 
                                 ((n_smsg m) = (rx a))))
                             -> comm_E n m.
(* [REF 1] Definition 2.3.3 pg 6
   "there is an edge n1 -> n2 iff term(n1) = +a and term(n2) = -a." *)

(* predecessor edge *)
(* node's direct predecessor -> node -> Prop *)
Inductive pred_E : node -> node -> Prop :=
| predE : forall i j, n_strand i = n_strand j 
                      -> (n_index i) + 1 = (n_index j) 
                      -> pred_E i j.
(* [REF 1] Definition 2.3.4 pg 6
   "When n1= <s,i> and n2=<s,i+1> are members of N (set of node), there is
    an edge n1 => n2." *)

(* predecessor multi edge (not nec. immediate predecessor) *)
(* node's predecessor -> node -> Prop *)
Inductive predX_E : node -> node -> Prop :=
| predXE1 : forall i j, pred_E i j -> predX_E i j
| predXEX : forall i j k, pred_E i j -> predX_E j k -> predX_E i k.
(* [REF 1] Definition 2.3.4 pg 6
   "ni =>+ nj means that ni precedes nj (not necessarily immediately) on
    the same strand." *)

Inductive occurs_in : msg -> node -> Prop :=
| occursin : forall m n, subterm m (n_msg n) -> occurs_in m n.
(* [REF 1] Definition 2.3.5 pg  6
   "An unsigned term m occurs in a node n iff m is a subterm of term(n). " *)

(* signifies the origin of a msg. *)
Inductive entry_point : node -> set msg -> Prop :=
 | entrypoint :  forall n I, 
    (and (exists m, (and ((n_smsg n) = (tx m)) 
                         (true = msg_in_set m I)))
         (forall n', (predX_E n' n) 
                     -> (false = msg_in_set (n_msg n') I)))
    -> entry_point n I.
(* [REF 1] Definition 2.3.6 pg 6
   "The node n in N is an entry point for I (a set of unsigned terms) iff
    term(n) = +t for some t in I, and whenever n' =>+ n term(n') is not in I."*)

(* where an unsigned term originates, what node *)
Inductive orig_at : msg -> node -> Prop :=
| origat : forall m n, (exists I, (and (entry_point n I)
                   (forall m', true = msg_in_set m' I -> subterm m m')))
-> orig_at m n.
(* [REF 1] Definition 2.3.7 pg 6
   "An unsigned term t originates on n in N iff n is an entry point for 
    the set I = {t' | t is a subterm of t'}."*)

(* uniquely originating term def, useful for nonces or session keys *)
Inductive uniq_orig : msg -> Prop :=
| uniqorg : forall t, (exists n, 
              (forall n', orig_at t n' -> n = n') )
              -> uniq_orig t.
(* [REF 1] Definition 2.3.8 pg 7 
   "unsigned term t is uniquely originating iff t originates on a unique
    n in N." *)


(* Definition bundle : *)