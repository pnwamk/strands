(** * strands.v: Basic Strand Space Definitions *)

(* Created         20130418   Andrew Kent (amk.kent@gmail.com) 
   Last Modified   20130424   Andrew Kent (amk.kent@gmail.com)
   
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

Definition subterm := msg -> msg -> Prop.
(* REF Section 2.1 pg 5 
   TODO is further defined in section 2.3 *)

(* signed msg, + (tx) or - (rx) *)
Inductive smsg : Type := 
 | tx : msg -> smsg
 | rx : msg -> smsg.
(* REF Definition 2.1 pg 6 
   They are defined as a pair, w/ the first member being in {+, -} 
   and the second a signed message. *)

Definition strand : Type := list smsg.
(* REF First sentence of Abstract: "sequence of events"  
   Haven't hit a better def, and they start using strands
   pretty early so I'm rolling with this. *)


(* strand space *)
(* Definition sspace : Set strand  *)
Inductive sspace : Type :=
  | space : set msg -> set strand -> sspace.
(* REF Definition 2.2 pg 6 "A strand space over A (set of possible msgs) is a set
    E with a trace mapping tr : E -> list smsg *)

Definition node : Type := {n: (prod strand nat) | (snd n) < (length (fst n))}.
(* REF Definition 2.3.1 pg 6
   -"A node is a pair <s,i> where s is a strand and i a nat in [0, (length s))"
     NOTE: I changed it to be 0 based instead of 1 based sequences
   -"node <s,i> belongs to strand s"
   -"Every node belongs to a unique strand" *)

Definition n_index (n:node) : nat :=
match n with
 | exist npair _ 
   => snd npair
end.
(* REF Definition 2.3.2 pg 6
   "If n = <s,i> then index(n) = i. *)

Definition n_strand (n:node) : strand :=
match n with
 | exist npair _ 
   => fst npair
end.
(* REF Definition 2.3.2 pg 6
   "If n = <s,i> then ... strand(n) = s. *)


Fixpoint n_smsg (n:node) : smsg :=
match n with
 | exist npair p 
   =>  nth (snd npair) (fst npair)  (tx mterm) (* TODO default term... ? *)
end. 
(* REF Definition 2.3.2 pg 6
   "Define term(n) to be the ith signed term of the trace of s." *)


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

