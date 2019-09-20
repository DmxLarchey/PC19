(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

Set Implicit Arguments.

Fact rev_inj X (l m : list X) : rev l = rev m -> l = m.
Proof. intros H; rewrite <- (rev_involutive l), H, rev_involutive; trivial. Qed.
