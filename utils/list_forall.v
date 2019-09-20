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

Section Forall.

  Variable (X : Type) (P : X -> Prop).

  Fact Forall_cons_inv x l : Forall P (x::l) <-> P x /\ Forall P l.
  Proof. 
    split.
    + inversion 1; auto.
    + constructor; tauto.
  Qed.

  Fact Forall_app_inv l m : Forall P (l++m) <-> Forall P l /\ Forall P m.
  Proof.
    induction l; simpl; try (repeat split; auto; tauto).
    do 2 rewrite Forall_cons_inv; tauto.
  Qed.

  Let Forall_rec_1 l : Forall P l -> Forall P (rev l).
  Proof.
    induction 1; simpl; auto.
    apply Forall_app_inv; simpl; auto.
  Qed.

  Fact Forall_rev l : Forall P (rev l) <-> Forall P l.
  Proof.
    split; auto.
    rewrite <- (rev_involutive l) at 2.
    apply Forall_rec_1.
  Qed.

End Forall.

Fact Forall2_lft_nil_inv X Y (R : X -> Y -> Prop) m : Forall2 R nil m -> m = nil.
Proof. inversion 1; auto. Qed.
  
Fact Forall2_lft_cons_inv X Y (R : X -> Y -> Prop) x l m : Forall2 R (x::l) m -> exists y m', m = y::m' /\ R x y /\ Forall2 R l m'.
Proof. inversion 1; subst; exists y, l'; auto. Qed.

Tactic Notation "inv" "Forall2" "nil" := 
  repeat match goal with H: Forall2 _ nil ?m |- _ => apply Forall2_lft_nil_inv in H; try discriminate; subst m end.
  
Tactic Notation "inv" "Forall2" "in" hyp(H) "with" ident(x) ident(m) := apply Forall2_lft_cons_inv in H; destruct H as (x & m & ? & ? & ?); subst.

Fact Forall2_fun X Y (R : X -> Y -> Prop) l : (forall x, In x l -> forall y1 y2, R x y1 -> R x y2 -> y1 = y2) 
                                            -> forall m1 m2, Forall2 R l m1 -> Forall2 R l m2 -> m1 = m2.
Proof.
  induction l as [ | t l IHl ]; intros Hl l1 l2 H1 H2.
  inv Forall2 nil; auto.
  inv Forall2 in H1 with x1 m1.
  inv Forall2 in H2 with x2 m2.
  f_equal.
  apply Hl with t; simpl; auto.
  apply IHl; auto.
  intros ? ? ? ?; apply Hl; right; auto.
Qed.

Fact Forall2_mono X Y (R S : X -> Y -> Prop) : (forall x y, R x y -> S x y) -> forall l m, Forall2 R l m -> Forall2 S l m.
Proof. induction 2; simpl; auto. Qed.




