(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Bool List Permutation Arith Omega Extraction.

Require Import list_utils perm_utils.

Set Implicit Arguments.

Section halve.

  Variable X : Type.

  Implicit Type m : list X.

  Fixpoint halve m :=
    match m with 
      | nil  => (nil,nil)
      | x::k => let (l,r) := halve k in (x::r,l)
    end.

  Fixpoint halve_spec m : let (l,r) := halve m 
                      in m ~p l++r 
                      /\ length r <= length l <= 1 + length r. 
  Proof.
    destruct m as [ | x [ | y m ] ]; simpl.
    + split; auto; constructor.
    + split; auto; repeat constructor.
    + specialize (halve_spec m).
      destruct (halve m).
      destruct halve_spec; simpl; auto; split; auto; omega.
  Qed.

  Definition halve_full m : { c : _ * _ | let (l,r) := c in m ~p l++r /\ length r <= length l <= 1 + length r }. 
  Proof. exists (halve m); apply halve_spec. Defined.

  Extraction Inline halve_full.

  Fact halve_two x y m : let (l,r) := halve m in halve (x::y::m) = (x::l,y::r).
  Proof. simpl; destruct (halve m); auto. Qed.

End halve.

Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction halve.

Section halve_tail.

  Variable X : Type.

  Implicit Type m : list X.

  Fixpoint halve_tail l r m :=
    match m with 
      | nil  => (l,r)
      | x::k => halve_tail (r) (x::l) k
    end.

  Fact halve_tail_two l r x y m : halve_tail l r (x::y::m) = halve_tail (x::l) (y::r) m.
  Proof. trivial. Qed.

  Fixpoint even n := 
    match n with 0 => true | S n => negb (even n) end.

  Fixpoint halve_tail_spec l r m : 
            let (l1,r1) := halve m            in 
            let (l2,r2) := halve_tail l r m 
            in   (even (length m) = true  -> l2 = rev l1++l /\ r2 = rev r1++r)
              /\ (even (length m) = false -> l2 = rev r1++r /\ r2 = rev l1++l).
  Proof.
    destruct m as [ | x [ | y m ] ]; simpl; try (split; auto; discriminate).
    specialize (halve_tail_spec (x::l) (y::r) m).
    simpl; destruct (halve m) as (l1,r1).
    destruct (halve_tail (x::l) (y::r) m) as (l2,r2).
    repeat rewrite negb_involutive.
    simpl; repeat rewrite app_ass; simpl; auto.
  Qed.

  Definition halve_tail_full m : 
          { c : _ * _ | let (l,r) := c 
                        in m ~p l++r 
                        /\ ( length r <= length l <= 1 + length r
                          \/ length l <= length r <= 1 + length l ) }. 
  Proof.
    exists (halve_tail nil nil m).
    generalize (halve_spec m) (halve_tail_spec nil nil m).
    destruct (halve m) as (l1,r1).
    destruct (halve_tail nil nil m) as (l2,r2); simpl.
    repeat rewrite <- app_nil_end.
    intros (H1 & H2) (H3 & H4).
    destruct (even (length m)).
    + destruct H3; subst; auto.
      repeat rewrite rev_length.
      split; try tauto.
      apply perm_trans with (1 := H1).
      apply Permutation_app; apply Permutation_rev.
    + destruct H4; subst; auto.
      repeat rewrite rev_length.
      split; try tauto.
      apply perm_trans with (1 := H1).
      apply perm_trans with (1 := Permutation_app_comm _ _).
      apply Permutation_app; apply Permutation_rev.
  Defined.

  Extraction Inline halve_tail_full.

End halve_tail.

Recursive Extraction halve_tail_full.