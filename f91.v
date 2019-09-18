(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Lia Extraction.

Require Import measure_ind.

(** let rec f91 n = if n > 100 then n-10 else f91 (f91 (n+11)) *)

Set Implicit Arguments.

(** Replace a <? b = true with a < b and a <? b = false with a >= b *)

Tactic Notation "simpl" "ltb" "in" hyp(E) :=
  match type of E with
    | _ <? _ = true  => rewrite Nat.ltb_lt in E
    | _ <? _ = false => rewrite Nat.ltb_ge in E
  end.

Section F91.

  (** This definition of f91 assumes the knowledge of the semantics *)

  Definition sem91 m p := 100 < m /\ p = m - 10 \/ m <= 100 /\ p = 91.

  (** And also how to structure the domain inductively *)

  Definition f91_sem_full m : { p | sem91 m p }.
  Proof.
    induction on m as f91 with measure (101-m).
    refine (match 100 <? m as r return 100 <? m = r -> _ with
      | false => fun E => 
        let (r,Hr) := f91 (m+11) _ in 
        let (n,Hn) := f91 r _ 
        in exist _ n _
      | true => fun E =>
           exist _ (m-10) _
    end eq_refl); unfold sem91 in *; simpl ltb in E; lia.
  Defined.

  Extraction Inline f91_sem_full.

  Definition f91_sem n := proj1_sig (f91_sem_full n).

  Fact f91_sem_spec n : 100 < n  /\ f91_sem n = n-10
                     \/ n <= 100 /\ f91_sem n = 91.
  Proof. apply (proj2_sig (f91_sem_full _)). Qed.

End F91.

Extraction f91_sem.

Section f91_via_simulated_induction_recursion.

  (** Let us extract f91 via simulated induction/recursion w/o
      a priori knowledge of the semantics

     Inductive d_f91 : nat -> Prop :=
       | d_f91_0 : forall n, 100 < n  -> d_f91 n
       | d_f91_1 : forall n, n <= 100 -> forall D, d_f91 (f91 (n+11) D) -> d_f91 n
     with Fixpoint f91 n (D : d_f91 n) := match D with
       | d_f91_0 n _       => n - 10
       | d_f91_1 n _ D1 D2 => f91 (f91 (n+11) D1) D2
     end.

  *) 

  Local Inductive g91 : nat -> nat -> Prop :=
    | in_g91_0 : forall n,        100 < n  -> g91 n (n-10)
    | in_g91_1 : forall n fn11 r, n <= 100 -> g91 (n+11) fn11 -> g91 fn11 r -> g91 n r. 
    
  Local Fact g91_fun x y1 y2 : g91 x y1 -> g91 x y2 -> y1 = y2.
  Proof.
    intros H; revert H y2.
    induction 1 as [ x D1 | x fn11 r D1 H2 IH2 H3 IH3 ]; inversion 1; subst; auto; try lia.
    apply IH2 in H1; subst.
    apply IH3; auto.
  Qed.

  (* We define the domain as an inductive bar predicate, using the graph *)

  Unset Elimination Schemes.

  Inductive d91 (n : nat) : Prop :=
    | in_d91_0 : 100 < n  -> d91 n
    | in_d91_1 : n <= 100 -> d91 (n+11) 
                          -> (forall x, g91 (n+11) x -> d91 x)
                          -> d91 n.

  Set Elimination Schemes.

  (* d91 contains all the domain of g91 *)

  Fact g91_d91 n : (exists r, g91 n r) -> d91 n.
  Proof.
    intros (r & Hr); revert Hr.
    induction 1 as [ n Hn | n fn11 r Hn H1 IH1 H2 IH2 ].
    * constructor 1; trivial.
    * constructor 2; auto.
      intros x Hx.
      rewrite (g91_fun Hx H1); trivial.
  Qed.

  (* the inductive structure of d91 allows to
     define f91 *)

  Section f91.

    Let f91_full : forall x, d91 x -> sig (g91 x).
    Proof.
      refine (fix loop n Hn { struct Hn } := 
        match 100 <? n as r return 100 <? n = r -> _ with 
          | true  => fun H => exist _ (n-10) _  
          | false => fun H => let (f1,H1) := @loop (n+11) _ in
                              let (f2,H2) := @loop f1 _
                              in   exist _ f2 _
        end eq_refl); simpl ltb in H.
      2,3: inversion Hn; auto; exfalso; lia.
      + constructor; auto.
      + constructor 2 with f1; auto.
    Qed.

    Definition f91 x D := proj1_sig (@f91_full x D).
    Local Fact f91_spec x D : g91 x (@f91 x D).
    Proof. apply (proj2_sig _). Qed.

  End f91.

  (* d91 is indeed an(other) inductive characterization of the 
     domain of g91. *)

  Theorem d91_g91_eq n : d91 n <-> ex (g91 n).
  Proof.
    split.
    + intros Hn.
      exists (f91 Hn).
      apply f91_spec.
    + apply g91_d91.
  Qed.

  (* To study f91, we can proceed by simulating the induction-recursion
     scheme of f91 *) 

  (* Two constructors for the domain *)

  Fact d91_0 n : 100 < n -> d91 n.
  Proof.
    constructor 1; auto.
  Qed.
  
  Fact d91_1 n : n <= 100 -> forall D, d91 (@f91 (n+11) D) -> d91 n.
  Proof.
    intros H D HD.
    constructor 2; auto.
    intros x Hx.
    rewrite (g91_fun Hx (f91_spec D)); trivial.
  Qed.

  (* The induction/recursion principle *)
  
  Section d91_rect.

    Variable P : forall x, d91 x -> Type.

    Hypothesis HPi : forall n D1 D2, @P n D1 -> @P n D2.
    Hypothesis HP0 : forall n Hn, P (@d91_0 n Hn).
    Hypothesis HP1 : forall n Hn D1 (_ : P D1) D2 (_ : P D2), P (@d91_1 n Hn D1 D2).

    Fixpoint d91_rect n (D : d91 n) : P D.
    Proof.
      destruct (le_lt_dec n 100) as [ H | H ].
      all: cycle 1.
      + apply HPi with (D1 := d91_0 H), HP0.
      + assert (D1 : d91 (n+11)).
        { inversion D; trivial; exfalso; lia. }
        assert (D2 : d91 (f91 D1)).
        { inversion D; try (exfalso; lia).
          apply H2, f91_spec. }
        apply HPi with (1 := HP1 H (d91_rect _ D1) (d91_rect _ D2)).
    Qed.
    
  End d91_rect.

  Definition d91_rec (P : forall x, d91 x -> Set) := d91_rect P.
  Definition d91_ind (P : forall x, d91 x -> Prop) := d91_rect P.

  (* Proof irrelevance for the domain argument *)
  
  Fact f91_pirr n D1 D2 : @f91 n D1 = @f91 n D2.
  Proof. apply g91_fun with n; apply f91_spec. Qed.

  (* And the two fixpoint equations for f91 *)  

  Fact f91_fix_0 n Hn : f91 (@d91_0 n Hn) = n - 10.
  Proof.
    apply g91_fun with n.
    apply f91_spec.
    constructor 1; auto.
  Qed.

  Fact f91_fix_1 n Hn D1 D2 : @f91 n (@d91_1 n Hn D1 D2) = @f91 (@f91 (n+11) D1) D2.
  Proof.
    apply g91_fun with n.
    apply f91_spec.
    constructor 2 with (f91 D1); try apply f91_spec; auto.
  Qed.
  
End f91_via_simulated_induction_recursion.

Extraction f91.

Section f91_termination_and_correctness.

  (** Using the inductive/recursive scheme, we can study 
      the partial correctness and termination of f91 *)

  (* Because f91 is nested, we need partial correctness
     before we can prove termination *)

  Theorem f91_partially_correct n (Dn : d91 n) : sem91 n (f91 Dn).
  Proof.
    induction Dn as [ n D1 D2 IH | n Hn | n Hn D1 IH1 D2 IH2 ].
    + rewrite (f91_pirr _ D1); trivial.
    + rewrite f91_fix_0; red; lia.
    + rewrite f91_fix_1; red in IH1, IH2 |- *; lia.
  Qed.

  (* Now that we have the semantics over the domain, we can
     show total correctness, ie termination or totality of
     the domain *)

  Theorem f91_terminates n : d91 n.
  Proof.
    induction on n as IH with measure (101-n).
    destruct (le_lt_dec n 100) as [ H | H ].
    + assert (D1 : d91 (n+11)) by (apply IH; lia).
      apply d91_1 with D1; auto.
      apply IH.
      generalize (f91_partially_correct D1); intros S.
      red in S; lia.
    + apply d91_0; auto.
  Qed.

  Definition f91_total n := @f91 _ (f91_terminates n).

End f91_termination_and_correctness.

Extraction Inline f91.

Extraction f91_total.

