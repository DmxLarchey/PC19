(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Extraction.

Require Import measure_ind.

Set Implicit Arguments.

(** Several ways to define simple interleaving in Coq
    to get the algorithm defined by the two equations

      itl [] m = m
      itl (x::l) m = x::itl m l

   as following extracted code in OCaml

     let rec itl l m = match l with
       | []   -> m
       | x::l -> x::itl m l 

   1) first itl_s is a functional equivalent by structural induction
      but of course with a different algorithm
   2) itl gives the correct algorithm but with hard correctness proof
   3) itl_paired follows the same recursive pattern but with paired
      arguments
   4) itl_f gives the correct algo. with simple correctness proof
   5) itl_g gives the correct algo. with simple and delayed correctness proof

 *)

Section interleave.

  Variable X : Type.

  Implicit Type l m : list X.

  Section interleave_struct.

    (** First an easily definable functional equivalent
        of itl, by structural induction on l *)

    Fixpoint itl_s l m := 
      match l, m with
        | nil,  _    => m
        | _::_, nil  => l 
        | x::l, y::m => x::y::itl_s l m 
      end.

    (** And we show itl_s satisfies the fixpoint equations of itl *)

    Fact itl_s_fix0 m : itl_s nil m = m.
    Proof. trivial. Qed.

    Fact itl_s_fix1 x l m : itl_s (x::l) m = x::itl_s m l.
    Proof.
      revert x.
      induction on l m as IH with measure (length l + length m).
      intros x; destruct m as [ | y m ]; trivial.
      simpl itl_s at 1; f_equal.
      symmetry; apply IH; simpl; lia.
    Qed. 

  End interleave_struct.

  Section interleave_measure.

    (** Now by induction on the measure |l|+|m| *)

    Definition itl l m : list X.
    Proof.
      induction on l m as itl with measure (length l + length m).
      revert itl; refine (match l with
        | nil  => fun _   => m
        | x::l => fun itl => x::itl m l _
      end).
      simpl; lia.  (** the measure decreases *)
    Defined.

    (** Showing that itl_mes is ext-equal to itl_s 
        is possible but NOT EASY because
        you have to use and thus prove the fixpoint 
        equation for measure_double_rect... 

        see measure_ind.v for this non-trivial proof *)

    Let itl_fix l m : 
        itl l m = match l with 
          | nil  => m
          | x::l => x::itl m l
        end.
    Proof.
      unfold itl at 1.
      rewrite measure_double_rect_fix.
      + destruct l; simpl; trivial.
      + (* Proof that the functor is extensional 
           beware that the functor contains proofs
           automated with lia hence it is ugly *)
        clear l m.
        intros [ | x l ] m H1 H2 H; auto.
        rewrite H; trivial.
    Qed.

    Fact itl_fix0 m : itl nil m = m.
    Proof. rewrite itl_fix; trivial. Qed.

    Fact itl_fix1 x l m : itl (x::l) m = x::itl m l.
    Proof. rewrite itl_fix; trivial. Qed.

    (** Once the fixpoint equations are established, the
        proof is immediate *)

    Lemma itl_itl_s_eq l m : itl l m = itl_s l m.
    Proof.
      induction on l m as IH with measure (length l + length m).
      destruct l as [ | x l ].
      + rewrite itl_s_fix0, itl_fix0; trivial.
      + rewrite itl_s_fix1, itl_fix1; f_equal.
        apply IH; simpl; lia.
    Qed.
  
  End interleave_measure.

  Section interleave_measure_paired.

    (** Now by induction on the measure |l|+|m| but with paired arguments *)

    Definition itl_paired l m : list X.
    Proof.
      paired induction on l m as itl_mes with measure (length l + length m).
      revert itl_mes; refine (match l with
        | nil  => fun _       => m
        | x::l => fun itl_mes => x::itl_mes m l _
      end).
      simpl; lia.  (** the measure decreases *)
    Defined.

  End interleave_measure_paired.

  Section interleave_measure_full.

    (** Using dependent full specification allows for easy avoidance
        of the fixpoint equation of measure_double_rect *)

    Local Definition itl_full l m : { k | k = itl_s l m }.
    Proof.
      induction on l m as loop with measure (length l + length m).
      revert loop; refine (match l with
        | nil  => fun _    => exist _ m _
        | x::l => fun loop => let (k,Hk) := loop m l _
                              in  exist _ (x::k) _ 
      end).
      1,2: cycle 1.
      + simpl; lia.
      + rewrite itl_s_fix0; trivial.
      + rewrite Hk, itl_s_fix1; trivial.
    Defined.

    Extraction Inline itl_full.

    Definition itl_f l m := proj1_sig (itl_full l m).
    
    Fact itl_f_itl_s_eq l m : itl_f l m = itl_s l m.
    Proof. apply (proj2_sig (itl_full _ _)). Qed.

  End interleave_measure_full.

  Section interleave_without_knowledge_of_semantics.

    (** We implement interleave without knowledge of semantics 
        and show correctness afterwards *)

    (** We use the graph (an always definable relation) to specify
        the algorithm *)

    Inductive itl_graph : list X -> list X -> list X -> Prop := 
      | in_itl_g0 : forall m, itl_graph nil m m
      | in_itl_g1 : forall x l m r, itl_graph m l r -> itl_graph (x::l) m (x::r).

    (** The graph is a functional relation by combined induction/inversion *)

    Fact itl_graph_fun l m r1 r2 : itl_graph l m r1 -> itl_graph l m r2 -> r1 = r2.
    Proof.
      intros H1; revert H1 r2.
      induction 1; inversion 1; f_equal; auto.
    Qed.

    (** We use more proving style for this the code.
        Thus is just to show that programming with tactics 
        is just fine *)

    Local Definition itl_g_full l m : { k | itl_graph l m k }.
    Proof.
      induction on l m as loop with measure (length l + length m).
      destruct l as [ | x l ].
      + exists m; constructor.
      + refine (let (k,Hk) := loop m l _ in _). 
        (* destruct (loop m l) instead of 
           refine would introduce a 
           parasitic "let in" the extracted code *)
        * simpl; lia.
        * exists (x::k).
          constructor; trivial.
    Defined.

    Extraction Inline itl_g_full.

    Definition itl_g l m := proj1_sig (itl_g_full l m).
    
    Fact itl_g_spec l m : itl_graph l m (itl_g l m).
    Proof. apply (proj2_sig _). Qed.

    (** We can show correctness after the definition using the graph *)

    Lemma itl_s_g_eq l m : itl_g l m = itl_s l m.
    Proof. 
      apply itl_graph_fun with l m.
      * apply itl_g_spec.
      * induction on l m as IH with measure (length l + length m).
        destruct l as [ | x l ].
        + rewrite itl_s_fix0; constructor.
        + rewrite itl_s_fix1; constructor.
          apply IH; simpl; lia.
    Qed.

  End interleave_without_knowledge_of_semantics.

End interleave.

Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Recursive Extraction itl_s itl itl_paired itl_f itl_g.

     

