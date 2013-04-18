(** * strands.v: Basic Strand Space Definitions *)

(* Created         20130418   Andrew Kent (amk.kent@gmail.com) 
   Last Modified   20130418   Andrew Kent (amk.kent@gmail.com)
   
*)

(* Source Material(s): 

Strand Spaces: Proving Security Protocols Correct.
   F. Javier Thayer Fabrega, Jonathan C. Herzog, Joshua D. Guttman. 
   Journal of Computer Security, 7 (1999), pages 191-230.
   http://web.cs.wpi.edu/~guttman/pubs/jcs_strand_spaces.pdf
 *)

Require Import List.

Inductive term : Type :=
 | termc.

Inductive msg : Type :=
 | munit : term -> msg (* single *)
 | mcons : term -> msg -> msg. (* n-tuple *)

Check (mcons termc (mcons termc (munit termc))).


Notation "x :: l" := (mcons x l) (at level 60, right associativity).
Notation "[ x ]" := (munit x).
Notation "[ x , .. , y ]" := (mcons x .. (munit y) ..). 
