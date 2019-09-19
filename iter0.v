(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Extraction Lia.

Set Implicit Arguments.

Fixpoint iter X (f : X -> X) n x :=
  match n with 0 => x | S n => iter f n (f x) end.

Section iter0.

  Variable f : nat -> nat.

  Inductive g_iter0 : nat -> list nat -> Prop :=
   | in_git0_0 : g_iter0 0 nil
   | in_git0_1 : forall n l, n <> 0 -> g_iter0 (f n) l -> g_iter0 n (n::l).

  Fact g_iter0_fun n l m : g_iter0 n l -> g_iter0 n m -> l = m.
  Proof.
    intros H; revert H m.
    induction 1; inversion 1; subst; f_equal; auto; lia.
  Qed.

  Unset Elimination Schemes. 

  Inductive bar : nat -> Prop :=
    | in_bar_0 : bar 0
    | in_bar_1 : forall n, bar (f n) -> bar n.

  Set Elimination Schemes.

  Let ex_bar n : (exists k, iter f k n = 0) -> bar n.
  Proof.
    intros (k & Hk); revert n Hk.
    induction k as [ | k IHk ]; simpl; intros n Hk.
    + subst; constructor 1.
    + constructor 2; apply IHk; trivial.
  Qed. 

  Section iter0.

    Let Fixpoint loop n (H : bar n) : sig (g_iter0 n).
    Proof.
      refine(match n as n' return n = n' -> _ with 
        | 0   => fun _ => exist _ nil _
        | S m => fun E => let (r,Hr) := loop (f n) _ in exist _ (n::r) _
      end eq_refl).
      1-2: cycle 1.
      + destruct H; trivial; discriminate.
      + subst; constructor 1.
      + subst; constructor 2; auto.
    Defined.

    Definition iter0 n Hn := proj1_sig (loop (@ex_bar n Hn)).

    Fact iter0_spec n Hn : g_iter0 n (iter0 n Hn).
    Proof. apply (proj2_sig _). Qed.

  End iter0.

  Fact iter0_fix_0 H : iter0 0 H = nil.
  Proof.
    apply g_iter0_fun with (1 := iter0_spec _ _).
    constructor.
  Qed.

  Fact iter0_S n : (exists k, iter f k n = 0) 
                 -> n <> 0 
                 -> exists k, iter f k (f n) = 0.
  Proof.
    intros ([|k] & Hk) H.
    + simpl in Hk; lia.
    + exists k; auto.
  Qed.

  Fact iter0_fix_1 n H H' : n <> 0 -> iter0 n H = n::iter0 (f n) H'.
  Proof.
    intros H1.
    apply g_iter0_fun with (1 := iter0_spec _ _).
    constructor 2; auto.
    apply iter0_spec.
  Qed.

End iter0.

Extract Inductive list => "list" [ "[]" "(::)" ].

Recursive Extraction iter0.


    