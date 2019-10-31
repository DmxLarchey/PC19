(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Extraction.

Require Import acc_irr.

Set Implicit Arguments.

(** First a small vector library *)

Section vec.

  Variable X : Type.

  Inductive vec : nat -> Type :=
    | vec_nil  : vec 0
    | vec_cons : forall n, X -> vec n -> vec (S n).

  Variable x : X.

  Fixpoint in_vec n (v : vec n) : Prop :=
    match v with
      | vec_nil      => False
      | vec_cons y v => x = y \/ in_vec v
    end.

End vec.

Arguments vec_nil {X}.

Section vec_map.

  Variable (X Y : Type).

  Fixpoint vec_map (f : X -> Y) n (v : vec X n) : vec Y n :=
    match v with 
      | vec_nil      => vec_nil
      | vec_cons x v => vec_cons (f x) (vec_map f v)
    end.

  Fixpoint vec_in_map n v : (forall x, @in_vec X x n v -> Y) -> vec Y n.
  Proof.
    refine (match v with
      | vec_nil      => fun _ => vec_nil
      | vec_cons x v => fun f => vec_cons (f x _) (@vec_in_map _ v _)
    end).
    + left; auto.
    + intros y Hy; apply (f y); right; auto.
  Defined.

  Fact vec_in_map_vec_map_eq f n v : @vec_in_map n v (fun x _ => f x) = vec_map f v.
  Proof. induction v; simpl; f_equal; auto. Qed.

  Fact vec_in_map_ext n v f g : (forall x Hx, @f x Hx = @g x Hx) 
                             -> @vec_in_map n v f = vec_in_map v g.
  Proof. revert f g; induction v; simpl; intros; f_equal; auto. Qed.

End vec_map.

Fixpoint vec_sum n (v : vec nat n) :=
  match v with 
    | vec_nil      => 0
    | vec_cons x v => x+vec_sum v
  end.

(** Then first order terms with signature *)

Section first_order_terms.

  Variable (sym : Set)             (* a type of symbols *)
           (sym_ar : sym -> nat).  (* arities for symbols *)

  Unset Elimination Schemes.       (* we do not want the autogen recursors *)

  (** The Type of first order terms over signature s *)

  Inductive fo_term : Set :=
    | in_fot : forall s, vec fo_term (sym_ar s) -> fo_term.

  Set Elimination Schemes.

  Section fo_term_rect.

    (** We build a Type level dependent recursor together with
        a fixpoint equation *)

    Let sub_fo_term x t := match t with @in_fot s v => in_vec x v end.  

    (** This proof has to be carefully crafted for guardness *)
 
    Let Fixpoint Acc_sub_fo_term t : Acc sub_fo_term t.
    Proof.
      destruct t as [ s v ].
      constructor 1; simpl.
      intros x.
      revert v; generalize (sym_ar s).
      induction v as [ | n y w IHw ].
      + destruct 1.
      + intros [ H | H ].
        * rewrite H; apply Acc_sub_fo_term.
        * apply IHw, H.
    Qed.

    (** This is a Type level (_rect) dependent recursor with induction
        hypothesis using Prop level in_vec *) 

    Variable (P : fo_term -> Type)
             (IHP : forall s v, (forall t, in_vec t v -> P t) -> P (@in_fot s v)).

    Let Fixpoint Fix_IHP t (Ht : Acc sub_fo_term t) { struct Ht } : P t :=
      match t as t' return Acc sub_fo_term t'-> P t' with
        | @in_fot s v => fun Ht => @IHP s v (fun x Hx => @Fix_IHP x (Acc_inv Ht _ Hx))
      end Ht.

    Let Fix_IHP_fix t Ht :
        @Fix_IHP t Ht 
      = match t as t' return Acc sub_fo_term t' -> _ with 
          @in_fot s v => fun Ht' => @IHP s v (fun y H => Fix_IHP (Acc_inv Ht' H)) 
        end Ht.
    Proof. destruct Ht; reflexivity. Qed.

    Definition fo_term_rect t : P t.
    Proof. apply Fix_IHP with (1 := Acc_sub_fo_term t). Defined.

    Hypothesis IHP_ext : forall s v f g, (forall y H, f y H = g y H) -> @IHP s v f = IHP v g.

    Let Fix_IHP_Acc_irr : forall t f g, @Fix_IHP t f = Fix_IHP g.
    Proof.
      apply Acc_irrelevance.
      intros [] f g H; apply IHP_ext; auto.
    Qed.

    Theorem fo_term_rect_fix s v : 
            fo_term_rect (@in_fot s v) = @IHP s v (fun t _ => fo_term_rect t).
    Proof.
      unfold fo_term_rect at 1.
      rewrite Fix_IHP_fix.
      apply IHP_ext.
      intros; apply Fix_IHP_Acc_irr.
    Qed.

  End fo_term_rect.

  Section fo_term_recursion.

    (** We specialize the general recursor to fixed output type.
        The fixpoint equation does not require extensionality anymore *)

    Variable (X : Type)
             (F : forall s, vec fo_term (sym_ar s) -> vec X (sym_ar s) -> X).

    Definition fo_term_recursion : fo_term -> X.
    Proof.
      induction 1 as [ s v IHv ].
      apply (@F s v).
      apply vec_in_map with (1 := IHv).
    Defined.

    Theorem fo_term_recursion_fix s v :
      fo_term_recursion (@in_fot s v) = F v (vec_map fo_term_recursion v).
    Proof.
      unfold fo_term_recursion at 1.
      rewrite fo_term_rect_fix; f_equal.
      + rewrite vec_in_map_vec_map_eq; auto.
      + intros; f_equal; apply vec_in_map_ext; auto.
    Qed.

  End fo_term_recursion.

  Check fo_term_rect_fix.
  Check fo_term_recursion_fix.

  (** We can now define eg the size of terms easily with the
      corresponding fixpoint equation *)

  Definition fo_term_size : fo_term -> nat.
  Proof.
    apply fo_term_recursion.
    intros s _ v.
    exact (1+vec_sum v).
  Defined.
  
  Fact fo_term_size_fix s v :
       fo_term_size (@in_fot s v) = 1 + vec_sum (vec_map fo_term_size v).
  Proof. apply fo_term_recursion_fix. Qed.

  Check fo_term_size_fix.
 
End first_order_terms.

