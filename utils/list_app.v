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

Definition app_split { X : Type } (l1 l2 r1 r2 : list X) : 
   l1++r1 = l2++r2 -> (exists m, l2 = l1++m /\ r1 = m++r2) 
                   \/ (exists m, l1 = l2++m /\ r2 = m++r1).
Proof.
  revert l2 r1 r2.
  induction l1 as [ | x l1 Hl1 ].
  left; exists l2; auto.
  intros [ | y l2 ] r1 r2 H.
  right; exists (x::l1); auto.
  simpl in H; injection H; clear H; intros H ?; subst.
  apply Hl1 in H.
  destruct H as [ (m & H1 & H2) | (m & H1 & H2) ].
  left; exists m; subst; auto.
  right; exists m; subst; auto.
Qed.
