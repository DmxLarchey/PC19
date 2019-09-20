
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega List Permutation.

Set Implicit Arguments.

Reserved Notation "x '~p' y" (at level 70, no associativity).

Infix "~p" := (@Permutation _).

Section perm.

  Variable (X : Type).

  Implicit Type (l : list X).

  Fact perm_refl l : l ~p l.
  Proof. apply Permutation_refl. Qed.

  Fact perm_sym l1 l2 : l1 ~p l2 -> l2 ~p l1.
  Proof. apply Permutation_sym. Qed.

  Fact perm_trans l1 l2 l3 : l1 ~p l2 -> l2 ~p l3 -> l1 ~p l3.
  Proof. apply Permutation_trans. Qed.

  Fact perm_length l1 l2 : l1 ~p l2 -> length l1 = length l2.
  Proof. apply Permutation_length. Qed.

  Fact perm_cons x l m : l ~p m -> x::l ~p x::m.
  Proof. apply perm_skip. Qed.

  Fact perm_middle x l r : x::l++r ~p l++x::r.
  Proof. apply Permutation_middle. Qed.

  Fact perm_special x k l r : k ~p l++r -> x::k ~p l++x::r.
  Proof. apply Permutation_cons_app. Qed.

  Fact perm_app_comm l m : l ++ m ~p m ++ l.
  Proof. apply Permutation_app_comm. Qed.

  Fact perm_app l1 l2 r1 r2 : l1 ~p l2 -> r1 ~p r2 -> l1++r1 ~p l2++r2.
  Proof. apply Permutation_app. Qed.

  Fact perm_incl l m : l ~p m -> incl l m.
  Proof. intros H ? ?; apply Permutation_in with (1 := H); trivial. Qed.

End perm.

Hint Constructors Permutation.
Hint Resolve perm_special perm_refl perm_app.
