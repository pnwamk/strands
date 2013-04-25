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

Require Import List.
Require Import ListSet.

(* message or term *)
Inductive msg : Type :=
 | mterm : msg.
(* | mcons : msg -> msg -> msg ? *)
(* REF Section 2.1 pg 5 *)
(* TODO: Seems there is more structure to a message
         which will be added later (e.g. messages
         being composed of numerous sub pieces) *)

(* subterm relationship for messages *)
(* sub term -> larger encapsulating term -> Prop *)
Definition subterm := msg -> msg -> Prop.
(* REF Section 2.1 pg 5 
   TODO is further defined in section 2.3 *)

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
(* tx -> rx -> Prop *)
Inductive comm_E : node -> node -> Prop :=
 | commE : forall n m, (exists a, 
                            (and ((n_smsg n) = (tx a)) 
                                 ((n_smsg m) = (rx a))))
                        -> comm_E n m.
(* REF Definition 2.3.3 pg 6
   "there is an edge n1 -> n2 iff term(n1) = +a and term(n2) = -a." *)

(* a comm_E implies the tx and rx of a message a*)
Definition comm_E_imp : Prop :=
forall n m, comm_E n m 
              -> exists a, (and ((n_smsg n) = (tx a)) 
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

