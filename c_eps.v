(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Lia Extraction.

Set Implicit Arguments.

Section nat_rev_ind.

  Variables (P : nat -> Prop)
            (HP : forall n, P (S n) -> P n).

  Theorem nat_rev_ind x y : x <= y -> P y -> P x.
  Proof. induction 1; auto. Qed.

End nat_rev_ind.

Section Decidable_Minimization.

  Variable (P : nat -> Prop)
           (P_dec : forall n, { P n } + { ~ P n }).

  Local Inductive bar n : Prop :=
    | in_bar_0 : P n -> bar n
    | in_bar_1 : bar (S n) -> bar n.

  Local Fact exists_bar n : (exists i, n <= i /\ P i) -> bar n.
  Proof.
    intros (i & H1 & H2).
    apply in_bar_0 in H2.
    revert n i H1 H2. 
    apply nat_rev_ind.
    apply in_bar_1.
  Qed.

  Section Constructive_Epsilon.

    Let Fixpoint loop n (Hn : bar n) : { i | P i }.
    Proof.
      refine (
        match P_dec n with
          | left H  => exist _ n _
          | right H => let (m,Hm) := loop (S n) _
                       in  exist _ m _
        end).
      + trivial.
      + inversion Hn.
        * destruct H; assumption.
        * assumption.
      + trivial.
    Qed.

    Print loop.

(*

    Fact bar_eq_domain n : bar n <-> exists i, n <= i /\ P i.
    Proof.
      split.
      + intros Hn.
        destruct (@loop n Hn) as (i & Hi).
        exists i; auto.
      + apply exists_bar.
    Qed.

*)

    Definition constructive_epsilon : (exists x, P x) -> { x | P x }.
    Proof.
      intros H. 
      refine (let (x,Hx) := @loop 0 _  in  exist _ x _ ).
      + apply exists_bar. 
        destruct H as (i & Hi); exists i; split; auto; lia.
      + tauto.
    Defined.

  End Constructive_Epsilon.

  Section Unbounded_Min.

    Let Fixpoint loop n (Hn : bar n) : { m | P m /\ forall i, P i -> i < n \/ m <= i }.
    Proof.
      refine (match P_dec n with
        | left H  => exist _ n _
        | right H => let (m,Hm) := loop (S n) _
                     in  exist _ m _
      end).
      1-2: cycle 1.
      * inversion Hn; auto; tauto.
      * split; auto; intros; lia.
      * destruct Hm as (H1 & H2); split; auto.
        intros i Hi.
        destruct (eq_nat_dec i n).
        + subst; tauto.
        + apply H2 in Hi; lia.
    Qed.

    Definition unb_dec_min : ex P -> { m | P m /\ forall i, P i -> m <= i }.
    Proof.
      intros H.
      refine (let (m,Hm) := @loop 0 _ in exist _ m _).
      + apply exists_bar; auto.
        destruct H as (i & Hi); exists i; split; auto; lia.
      + destruct Hm as (H1 & H2).
        split; auto.
        intros i Hi; apply H2 in Hi; lia.
    Defined.

  End Unbounded_Min.

End Decidable_Minimization.

Extract Inductive sumbool => "bool" [ "true" "false" ].

Check constructive_epsilon.
Extraction constructive_epsilon.

Check unb_dec_min.
Extraction unb_dec_min.


  

