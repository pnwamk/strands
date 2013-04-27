(** * strands.v: Basic Strand Space Definitions *)

(* Created by Andrew Kent (amk.kent@gmail.com) 
   Brigham Young University
 *)

(* Source Material(s): 

Strand Spaces: Proving Security Protocols Correct.
   F. Javier Thayer Fabrega, Jonathan C. Herzog, Joshua D. Guttman. 
   Journal of Computer Security, 7 (1999), pages 191-230.
   http://web.cs.wpi.edu/~guttman/pubs/jcs_strand_spaces.pdf
 *)

Require Import List ListSet Arith Omega.

(* message or term *)
Inductive msg : Type :=
| mterm : msg
| mcons : msg -> msg -> msg. (* added for convenience, looking for 'strict' justification... *)
(* REF Section 2.1 pg 5 *)
(* TODO: Seems there is more structure to a message
         which will be added later (e.g. messages
         being composed of numerous sub pieces) *)

Axiom msg_eq_dec : forall x y : msg,  {x = y} + {x <> y}.

Definition msg_in_set (m:msg) (s:set msg) : bool := set_mem msg_eq_dec m s.

(* subterm relationship for messages *)
(* sub term -> larger encapsulating term -> Prop *)
Inductive subterm : msg -> msg -> Prop :=
| strefl : forall m, subterm m m
(* | stcryp : forall a g, subterm a g -> subterm a encrpt(g)  *)
| stcomp : forall a g h, (or (subterm a g)
                             (subterm a h))
                         -> subterm a (mcons g h).
(* REF Definition 2.1 pg 6 and Definition 2.11 TODO Add more this was a jump ahead
    TODO the definition there reference a (by that point) defined notion
    of encryption - we'll have to come back and add this. *)

(* signed message, + (tx) or - (rx) *)
Inductive smsg : Type := 
| tx : msg -> smsg
| rx : msg -> smsg.
(* REF Definition 2.1 pg 6 
   They are defined as a pair, w/ the first member being in {+, -} 
   and the second a signed message. *)

(* strand *)
Definition strand : Type := list smsg.
(* REF First sentence of Abstract: "sequence of events"  
   Haven't hit a better def, and they start using strands
   pretty early so I'm rolling with this. *)


(* strand space *)
Inductive sspace : Type :=
| space : set msg -> set strand -> sspace.
(* REF Definition 2.2 pg 6 "A strand space over A (set of possible msgs) is a set
    E with a trace mapping tr : E -> list smsg *)



(* node in a strand space *)
Definition node : Type := {n: (prod strand nat) | (snd n) < (length (fst n))}.
(* REF Definition 2.3.1 pg 6
   -"A node is a pair <s,i> where s is a strand and i a nat in [0, (length s))"
     NOTE: I changed it to be 0 based instead of 1 based sequences
   -"node <s,i> belongs to strand s"
   -"Every node belongs to a unique strand" *)

(* Definition node_eq : TODO ? *)



(* index of a node *)
Definition n_index (n:node) : nat :=
  match n with
    | exist npair _ 
      => snd npair
  end.
(* REF Definition 2.3.2 pg 6
   "If n = <s,i> then index(n) = i. *)

(* strand of a node *)
Definition n_strand (n:node) : strand :=
  match n with
    | exist npair _ 
      => fst npair
  end.
(* REF Definition 2.3.2 pg 6
   "If n = <s,i> then ... strand(n) = s. *)

(* signed message of a node *)
Fixpoint n_smsg (n:node) : smsg :=
  match n with
    | exist npair p 
      =>  nth (snd npair) (fst npair)  (tx mterm) (* TODO default term... ? *)
  end. 
(* REF Definition 2.3.2 pg 6
   "Define term(n) to be the ith signed term of the trace of s." *)

(* unsigned message of a node *)
Fixpoint n_msg (n:node) : msg :=
  match n with
    | exist npair p 
      => match  nth (snd npair) (fst npair)  (tx mterm) with  (* TODO default term... ? *)
           | tx t => t
           | rx t => t
         end
  end. 
(* REF Definition 2.3.2 pg 6
   "Define uns_term(n) to be the unsigned part of the ith signed term 
    of the trace of s." *)



(* communication or sending edge *)
Axiom comm_E : node -> node -> Prop.
Definition comm_E_iff : Prop :=
  forall n m, comm_E n m 
              <-> exists a, (and ((n_smsg n) = (tx a)) 
                                 ((n_smsg m) = (rx a))).
(* REF Definition 2.3.3 pg 6
   "there is an edge n1 -> n2 iff term(n1) = +a and term(n2) = -a." *)



(* predecessor edge *)
(* node's direct predecessor -> node -> Prop *)
Inductive pred_E : node -> node -> Prop :=
| predE : forall i j, n_strand i = n_strand j 
                      -> (n_index i) + 1 = (n_index j) 
                      -> pred_E i j.
(* REF Definition 2.3.4 pg 6
   "When n1= <s,i> and n2=<s,i+1> are members of N (set of node), there is
    an edge n1 => n2." *)

(* predecessor multi edge (not nec. immediate predecessor) *)
(* node's predecessor -> node -> Prop *)
Inductive predX_E : node -> node -> Prop :=
| predXE1 : forall i j, pred_E i j -> predX_E i j
| predXEX : forall i j k, pred_E i j -> predX_E j k -> predX_E i k.
(* REF Definition 2.3.4 pg 6
   "ni =>+ nj means that ni precedes nj (not necessarily immediately) on
    the same strand." *)



(* the notion that a msg occurs in a node (based on subterm's def) *)
Axiom occurs_in : msg -> node -> Prop.
Definition occurs_in_iff : Prop :=
  forall m n, occurs_in m n <-> subterm m (n_msg n).
(* REF Definition 2.3.5 pg  6
   "An unsigned term m occurs in a node n iff m is a subterm of term(n). " *)

(* signifies the origin of a msg. *)
Axiom entry_point : node -> set msg -> Prop.
Definition entry_point_iff : 
  forall n I, entry_point n I 
              <-> (and (exists m, (and ((n_smsg n) = (tx m)) 
                                       (true = msg_in_set m I)))
                       (forall n', (predX_E n' n) 
                                   -> (false = msg_in_set (n_msg n') I))).
(* REF Definition 2.3.6 pg 6
   "The node n in N is an entry point for I (a set of unsigned terms) iff
    term(n) = +t for some t in I, and whenever n' =>+ n term(n') is not in I."*)

(* where an unsigned term originates, what node *)
Axiom origin_on : msg -> node -> Prop.
Definition origin_on_iff :
forall t n, origin_on t n
<-> exists I, (and (entry_point n I)
                   (forall t', true = msg_in_set t' I -> subterm t t')).
(* REF Definition 2.3.7 pg 6
   "An unsigned term t originates on n in N iff n is an entry point for 
    the set I = {t' | t is a subterm of t'}."*)

(* uniquely originating term def, useful for nonces or session keys *)
Axiom uniq_origin : msg -> Prop.
Definition uniq_origin_iff :
forall t, uniq_origin t 
          <-> exists n, forall n', origin_on t n' -> n = n'.
(* REF Definition 2.3.8 pg 7 
   "unsigned term t is uniquely originating iff t originates on a unique
    n in N." *)


