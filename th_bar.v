(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Lia Extraction.

Require Import c_eps.

Set Implicit Arguments.

(** Extraction if the Tortoise and the Hare:

    let rec th_rec eq f x y = if eq x y then 0 else th_rec eq f (f x) (f (f y))

    let th eq f x = th_rec eq f (f x) (f (f x))

    We already now the semantics we want. As output of
      th_rec, we want n such that f^n x = f^2n y

  *)  

Fixpoint iter X (f : X -> X) n x := match n with 0 => x | S n => iter f n (f x) end.



Section with_constructive_epsilon.
  Variable (X : Type) 
           (eqX_dec : forall x y : X, { x = y } + { x <> y })
           (f : X -> X) (x0 : X).

  Let Q n := 0 < n /\ iter f n x0 = iter f (2*n) x0.

  Let Qdec n : { Q n } + { ~ Q n }.
  Proof.
    unfold Q.
    case_eq n.
    + intros; right; subst; lia.
    + intros m Hn.
      destruct (eqX_dec (iter f n x0) (iter f (2*n) x0)) as [ H | H ].
      * left; subst; split; auto; lia.
      * right; intros []; destruct H; subst; auto.
  Qed.

  Definition th_eps  : (exists n, 0 < n /\ iter f n x0 = iter f (2*n) x0)
                    -> { n | 0 < n /\ iter f n x0 = iter f (2*n) x0 }.
  Proof.
    apply constructive_epsilon with (1 := Qdec).
  Defined.

End with_constructive_epsilon.

Extract Inductive sumbool => "bool" [ "true" "false" ].

Extraction Inline constructive_epsilon.

Recursive Extraction th_eps.

Section Tortoise_Hare.

  Variable (X : Type) 
           (eqX_dec : forall x y : X, { x = y } + { x <> y })
           (f : X -> X).

  (* We describe the domain by a bar inductive predicate *)

  Inductive bar (t h : X) : Prop :=
    | in_bar_0 : t = h -> bar t h
    | in_bar_1 : bar (f t) (f (f h)) -> bar t h.

  Definition d_th_rec := bar.

  Fixpoint th_rec t h (H : bar t h) : { n | iter f n t = iter f (2*n) h }.
  Proof.
    refine (match eqX_dec t h with
           | left  E => exist _ 0 _
           | right D => let (n,Hn) := th_rec (f t) (f (f h)) _
                        in exist _ (S n) _
      end).
    1-2:cycle 1.
    * inversion H.
      + destruct D; auto.
      + trivial.
    * trivial.
    * replace (2 * S n) with (S (S (2*n))) by lia; trivial.
  Defined.

  Local Fact d_th_rec_sufficiency t h : (exists n, iter f n t = iter f (2*n) h) -> bar t h.
  Proof.
    unfold d_th_rec.
    intros (n & Hn).
    revert t h Hn; induction n as [ | n IHn ].
    + simpl; intros; constructor 1; auto.
    + intros t h.
      replace (2 * S n) with (S (S (2*n))) by lia.
      intros H; constructor 2.
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

  Section th_tail.

    Let Fixpoint loop n t h (H : bar t h) : { k | n <= k /\ iter f (k-n) t = iter f (2*(k-n)) h }.
    Proof.
      refine (match eqX_dec t h with
             | left  E => exist _ n _
             | right D => let (k,Hk) := loop (S n) (f t) (f (f h)) _
                          in exist _ k _
      end).
      1-2:cycle 1.
      * inversion H.
        + destruct D; auto.
        + trivial.
      * replace (n-n) with 0 by lia; simpl; auto.
      * destruct Hk as (H1 & H2).
        replace (k-n) with (S (k - S n)) at 1 by lia.
        replace (2*(k-n)) with (S (S (2*(k-S n)))) by lia.
        split; auto; lia.
    Qed.
   
    Definition th_tail x0 : (exists n, 0 < n /\ iter f n x0 = iter f (2*n) x0)
                         -> { n | 0 < n /\ iter f n x0 = iter f (2*n) x0 }.
    Proof.
      intros H.
      refine (let (n,Hn) := @loop 1 (f x0) (f (f x0)) _
              in  exist _ n _).
      + apply d_th_rec_sufficiency.
        destruct H as ([ | n ] & H1 & H2); try lia.
        exists n.
        replace (2 * S n) with (S (S (2*n))) in H2 by lia.
        simpl in H2; rewrite H2; f_equal; lia.
      + destruct Hn as (H1 & H2).
        replace n with (S (n-1)) at 2 by lia.
        replace (2*n) with (S (S (2*(n-1)))) by lia.
        auto.
    Defined.
 
  End th_tail.

End Tortoise_Hare.

Recursive Extraction th th_tail.
