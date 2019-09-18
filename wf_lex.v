(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Wellfounded.

Require Import wf_incl.

Set Implicit Arguments.

Section lex_sincl.

  Variable (X Y : Type) (f : X -> list Y) (R : X -> X -> Prop) (HR : well_founded R).

  Definition lex_sincl (x1 x2 : X) := sincl (f x1) (f x2) \/ incl (f x1) (f x2) /\ R x1 x2.

  Let lex_prop l : forall x, incl (f x) l -> Acc lex_sincl x.
  Proof.
    induction l as [ l IHl ] using (well_founded_induction wf_sincl).
    induction x as [ x IHx ] using (well_founded_induction HR).
    intros Hx.
    constructor.
    intros y [ (H1 & z & H2 & H3) | (H1 & H2) ].
    apply IHl with (f y).
    split. 
    intros ? ?; apply Hx, H1; trivial.
    exists z; split; auto.
    apply incl_refl.
    apply IHx; auto.
    revert Hx; apply incl_tran; auto.
  Qed.

  Theorem wf_lex_sincl : well_founded lex_sincl.
  Proof.
    intros x; apply lex_prop with (f x), incl_refl.
  Qed.

End lex_sincl.

Section lex_sincl_measure.

  Variable (X Y : Type) (f : X -> list Y) (m : X -> nat). 

  Definition lex_sincl_measure (x1 x2 : X) := sincl (f x1) (f x2) \/ incl (f x1) (f x2) /\ m x1 < m x2.
  
  Corollary wf_lex_sincl_measure : well_founded lex_sincl_measure.
  Proof.
    apply wf_lex_sincl with (R := fun x y => m x < m y), wf_inverse_image, lt_wf.
  Qed.

End lex_sincl_measure.

    
