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

(** Extraction if the Tortoise and the Hare:

    let rec th_rec eq f x y = if eq x y then 0 else th_rec eq f (f x) (f (f y))

    let th eq f x = th_rec eq f (f x) (f (f x))

    We already now the semantics we want. As output of
      th_rec, we want n such that f^n x = f^2n y

  *)  

Fixpoint iter X (f : X -> X) n x := match n with 0 => x | S n => iter f n (f x) end.

Section Tortoise_Hare.

  Variable (X : Type) 
           (eqX_dec : forall x y : X, { x = y } + { x <> y })
           (f : X -> X).

  (* We describe the domain by an accessibility predicate 
     fun x y => Acc R (x,y) where R tracks recursive sub-calls *)

  Inductive rec_call : X*X -> X*X -> Prop :=
    | in_rec_call : forall x y, x <> y -> rec_call (f x,f (f y)) (x,y).

  Definition d_th_rec x y := Acc rec_call (x,y).

  Fixpoint th_rec x y (H : d_th_rec x y) : { n | iter f n x = iter f (2*n) y }.
  Proof.
    refine (match eqX_dec x y with
           | left  E => exist _ 0 _
           | right D => let (n,Hn) := th_rec (f x) (f (f y)) _
                        in exist _ (S n) _
      end).
    1-2:cycle 1.
    * destruct H; apply H; constructor; auto.
    * trivial.
    * replace (2 * S n) with (S (S (2*n))) by lia; trivial.
  Defined.

  Local Fact d_th_rec_sufficiency x y : (exists n, iter f n x = iter f (2*n) y) -> d_th_rec x y.
  Proof.
    unfold d_th_rec.
    intros (n & Hn).
    revert x y Hn; induction n as [ | n IHn ].
    + simpl; intros; constructor.
      inversion 1; subst; tauto.
    + intros x y.
      replace (2 * S n) with (S (S (2*n))) by lia.
      intros H; constructor.
      inversion 1; subst.
      apply IHn, H.
  Qed.

  Definition th x : (exists n, 0 < n /\ iter f n x = iter f (2*n) x)
                 -> { n | 0 < n /\ iter f n x = iter f (2*n) x }.
  Proof.
    intros H.
    refine (let (n,Hn) := @th_rec (f x) (f (f x)) _
            in  exist _ (S n) _).
    + apply d_th_rec_sufficiency.
      destruct H as ([ | n ] & H1 & H2); try lia.
      exists n.
      replace (2 * S n) with (S (S (2*n))) in H2 by lia.
      simpl in H2; rewrite H2; f_equal; lia.
    + split; [ | replace (2 * S n) with (S (S (2*n))) ]; trivial; lia.
  Defined.

End Tortoise_Hare.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].

Recursive Extraction th.
