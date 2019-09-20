(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation Arith Lia Extraction.

Require Import measure_ind list_utils perm_utils sorted halve merge.

Set Implicit Arguments.

Section merge_sort.

  Variable (X : Type) (R : X -> X -> Prop) 
           (cmp : forall x y, { R x y } + { R y x })
           (Rtran : forall x y z, R x y -> R y z -> R x z).

  Section non_tail_rec.

    Let merge_sort_full m : { k | m ~p k /\ sorted R k }.
    Proof.
      induction on m as loop with measure (length m).
      refine (let (p,Hp) := halve_full m in 
            match p as p' return p = p' ->  _ with
              | (l,r) => fun Ep => 
              match r as r' return r = r' -> _ with
                | nil   => fun Er => exist _ m _
                | x::r' => fun Er => 
              let (l',G1) := loop l _ in
              let (r',G3) := loop r _ in 
              let (k,G)   := merge cmp Rtran (l := l') (m := r') _ _ 
              in  exist _ k _
              end eq_refl
            end eq_refl); subst; destruct Hp as (H1 & H2); try tauto.
      1-3: cycle 1.
      + apply Permutation_length in H1.
        rewrite app_length in H1; simpl in *; lia.
      + apply Permutation_length in H1.
        rewrite app_length in H1; simpl in *; lia.
      + destruct m as [ | x [ | y m ] ]; auto.
        rewrite <- app_nil_end in H1.
        apply Permutation_length in H1; simpl in *; exfalso; lia.
      + split; try tauto.
        apply proj1 in G.
        apply proj1 in G1.
        apply Permutation_trans with (1 := H1),
              Permutation_sym, 
              Permutation_trans with (1 := G),
              Permutation_sym, Permutation_app; tauto.
    Defined.

    Definition merge_sort m := proj1_sig (merge_sort_full m).

    Fact merge_sort_correct : sorting_algo R merge_sort.
    Proof. intro; unfold merge_sort; apply (@proj2_sig _). Qed.

  End non_tail_rec.

  Section with_tail_rec.

    Let merge_sort_tail_full m : { k | m ~p k /\ sorted R k }.
    Proof.
      induction on m as loop with measure (length m).
      refine (
        match m as m' return m = m' -> _ with
          | nil       => fun Em => exist _ m _
          | x::nil    => fun Em => exist _ m _
          | x::y::m'  => fun Em => 
            let (p,Hp) := halve_tail_full m in 
            match p as p' return p = p' ->  _ with
              | (l,r) => fun Ep => 
              let (l',G1) := loop l _ in
              let (r',G3) := loop r _ in 
              let (k,G)   := merge_tail cmp Rtran (l := l') (m := r') _ _ 
              in  exist _ k _
            end eq_refl
        end eq_refl); subst; auto; try tauto; destruct Hp as (H1 & H2).
      + apply Permutation_length in H1.
        rewrite app_length in H1.
        rewrite H1; simpl in H1 |- *; lia.
      + apply Permutation_length in H1.
        rewrite app_length in H1.
        rewrite H1; simpl in H1 |- *; lia.
      + clear loop l0 H2.
        destruct G1 as (G1 & G2).
        destruct G3 as (G3 & G4).
        destruct G as (G5 & G6).
        split; auto.
        apply perm_trans with (1 := H1), Permutation_sym.
        apply perm_trans with (1 := G5), Permutation_sym.
        apply Permutation_app; auto.
    Qed.

    Definition merge_sort_tail m := proj1_sig (merge_sort_tail_full m).

    Fact merge_sort_tail_correct : sorting_algo R merge_sort_tail.
    Proof. intro; unfold merge_sort_tail; apply (@proj2_sig _). Qed.

  End with_tail_rec.

End merge_sort.

Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive sumbool => "bool" [ "true" "false" ]. 

Recursive Extraction merge_sort.

Recursive Extraction merge_sort_tail.





