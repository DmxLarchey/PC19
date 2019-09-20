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

Section In_dec.

  (** in_dec/In_dec already exists in Coq List library 
      but this one extracts a bit better *)

  Variable (X : Type) (eqX_dec : forall x y : X, { x = y } + { x <> y }) (x : X).
  
  Definition In_dec : forall l, { In x l } + { ~ In x l }.
  Proof.
    refine (fix loop l := match l with
      | nil   => right _
      | y::l => match eqX_dec y x with 
        | left  E => left _
        | right D => match loop l with
          | left H  => left _
          | right H => right _
        end
      end
    end); simpl; tauto.
  Defined.

End In_dec.

Section In_app.

  Variable (X : Type).

  Implicit Type (l : list X).

  Fact In_app_inv x l m : In x (l++m) <-> In x l \/ In x m.
  Proof.
    split.
    + apply in_app_or.
    + apply in_or_app.
  Qed.

End In_app.


