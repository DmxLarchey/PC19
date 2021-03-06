(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Extraction.

(** Autogenerated False_rect uses singleton elimination (SE) *)

Check False_rect.
Print False_rect.
Recursive Extraction False_rect.

Extract Inductive unit => "unit" [ "()" ].

(** But we can build False_elim without SE *)

Section False_elim_Acc.

  Variable (X : Type).

  Let R : unit -> unit -> Prop := fun _ _ => True.

  Theorem False_elim0 : False -> X.
  Proof.
    intros C.
    apply Fix_F with (P := fun _ => X) (R := R) (x := tt). 
    + intros x H; apply (H tt), I.
    + destruct C.
  Defined.

End False_elim_Acc.

Check False_elim0.
Print False_elim0.
Recursive Extraction False_elim0.

Section False_elim_inline_Fix_F.

  Variable (X : Type).

  Let R : unit -> unit -> Prop := fun _ _ => True.

  Let loop : forall x, Acc R x -> X.
  Proof.
    refine (fix loop x Hx := loop tt _).
    destruct Hx; apply H, I.
  Defined.

  Theorem False_elim1 : False -> X.
  Proof.
    intros C; apply (loop tt).
    destruct C.
  Defined.

End False_elim_inline_Fix_F.

Check False_elim1.
Print False_elim1.
Recursive Extraction False_elim1.

Fixpoint False_elim2 X (C : False) : X := False_elim2 X (match C with end).

Check False_elim2.
Print False_elim2.
Recursive Extraction False_elim2.

Definition False_elim3 X : False -> X.
Proof.
  generalize tt.
  exact (fix loop (_ : unit) (C : False) : X := loop tt (match C with end)).
Defined.

Check False_elim3.
Print False_elim3.
Recursive Extraction False_elim3. 

Fixpoint False_elim4 X Y (x : X) (C : False) : Y := 
   False_elim4 _ _ x (match C with end).

Check False_elim4.
Print False_elim4.
Recursive Extraction False_elim4.


