(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Lia List Permutation.

Require Import measure_ind.

Set Implicit Arguments.

Infix "~p" := (@Permutation _) (at level 80).

Section incl.

  Variable X : Type.
  
  Implicit Type l : list X.
  
  Fact incl_cons_linv l m x : incl (x::m) l -> In x l /\ incl m l.
  Proof.
    intros H; split.
    apply H; left; auto.
    intros ? ?; apply H; right; auto.
  Qed.

  Fact incl_app_rinv l m p : incl m (l++p) -> exists m1 m2, m ~p m1++m2 /\ incl m1 l /\ incl m2 p.
  Proof.
    induction m as [ | x m IHm ].
    exists nil, nil; simpl; repeat split; auto; intros ? [].
    intros H.
    apply incl_cons_linv in H.
    destruct H as (H1 & H2).
    destruct (IHm H2) as (m1 & m2 & H3 & H4 & H5).
    apply in_app_or in H1; destruct H1 as [ H1 | H1 ].
    exists (x::m1), m2; repeat split; auto.
    constructor 2; auto.
    intros ? [ ? | ? ]; subst; auto.
    exists m1, (x::m2); repeat split; auto.
    apply Permutation_cons_app; auto.
    intros ? [ ? | ? ]; subst; auto.
  Qed.
  
  Fact incl_cons_rinv x l m : incl m (x::l) -> exists m1 m2, m ~p m1 ++ m2 /\ (forall a, In a m1 -> a = x) /\ incl m2 l.
  Proof.
    intros H.
    apply (@incl_app_rinv (x::nil) _ l) in H.
    destruct H as (m1 & m2 & H1 & H2 & H3).
    exists m1, m2; repeat split; auto.
    intros a Ha; apply H2 in Ha; destruct Ha as [ | [] ]; auto.
  Qed.
  
End incl.

Section Permutation_tools.

  Variable X : Type.
  
  Implicit Types (l : list X).
  
  Theorem Permutation_In_inv l1 l2: l1 ~p l2 -> forall x, In x l1 -> exists l, exists r, l2 = l++x::r.
  Proof.
    intros H x Hx.
    apply in_split.
    apply Permutation_in with (1 := H).
    auto.
  Qed.
  
  Fact perm_in_head x l : In x l -> exists m, l ~p x::m.
  Proof.
    induction l as [ | y l IHl ].
    destruct 1.
    intros [ ? | H ]; subst.
    exists l; apply Permutation_refl.
    destruct (IHl H) as (m & Hm).
    exists (y::m).
    apply Permutation_trans with (2 := perm_swap _ _ _).
    constructor 2; auto.
  Qed.

End Permutation_tools.

Definition list_prefix X (ll : list X) n : n <= length ll -> { l : _ & { r | ll = l++r /\ length l = n } }.
Proof.
  revert n; induction ll as [ | x ll IH ].
  intros [ | n ] Hn; exists nil, nil; split; auto.
  exfalso; simpl in Hn; lia.
  intros [ | n ] Hn.
  exists nil, (x::ll); auto.
  simpl in Hn.
  destruct (IH n) as (l & r & H1 & H2).
  lia.
  subst.
  exists (x::l), r; auto.
Qed.

Section finite_php.

  (** That proof DOES NOT rely on decidable equality *)

  Variable (X : Type).

  Implicit Types (l m : list X).
  
  Inductive list_has_dup : list X -> Prop :=
    | in_list_hd0 : forall l x, In x l -> list_has_dup (x::l)
    | in_list_hd1 : forall l x, list_has_dup l -> list_has_dup (x::l).
  
  Fact list_has_dup_cons_inv x l : list_has_dup (x::l) -> In x l \/ list_has_dup l.
  Proof. inversion 1; subst; auto. Qed.
  
  Fact list_has_dup_app_left l m : list_has_dup m -> list_has_dup (l++m).
  Proof. induction l; simpl; auto; constructor 2; auto. Qed.
  
  Fact list_has_dup_app_right l m : list_has_dup l -> list_has_dup (l++m).
  Proof. 
    induction 1; simpl.
    constructor 1; apply in_or_app; left; auto.
    constructor 2; auto.
  Qed.

  Fact list_has_dup_equiv l : list_has_dup l <-> exists x aa bb cc, l = aa++x::bb++x::cc.
  Proof.
    split.

    induction 1 as [ l x Hx | l x Hl (y & aa & bb & cc & IHl) ].

    apply in_split in Hx.
    destruct Hx as (bb & cc & ?); subst.
    exists x, nil, bb, cc; auto.

    exists y, (x::aa), bb, cc; subst; auto.

    intros (x & aa & bb & cc & ?); subst.
    apply list_has_dup_app_left.
    constructor 1.
    apply in_or_app; simpl; auto.
  Qed.
  
  Fact list_hd_eq_perm l m : l ~p m -> list_has_dup l -> list_has_dup m.
  Proof.
    induction 1 as [ | x l m H1 IH1 | x y l | ]; auto.
    intros H.
    apply list_has_dup_cons_inv in H.
    destruct H as [ H | H ].
    apply Permutation_in with (1 := H1) in H.
    
    apply in_list_hd0; auto.
    apply in_list_hd1; auto.
    intros H.
    apply list_has_dup_cons_inv in H.
    destruct H as [ [ H | H ] | H ]; subst.
    apply in_list_hd0; left; auto.
    apply in_list_hd1, in_list_hd0; auto.
    apply list_has_dup_cons_inv in H.
    destruct H as [ H | H ].
    apply in_list_hd0; right; auto.
    do 2 apply in_list_hd1; auto.
  Qed.
  
  Fact incl_right_cons_choose x l m : incl m (x::l) -> In x m \/ incl m l.
  Proof.
    intros H.
    apply incl_cons_rinv in H.
    destruct H as ( m1 & m2 & H1 & H2 & H3 ); simpl in H1.
    destruct m1 as [ | y m1 ].
    right.
    intros u H; apply H3; revert H.
    apply Permutation_in; auto.
    left.
    apply Permutation_in with (1 := Permutation_sym H1).
    rewrite (H2 y); left; auto.
  Qed.
  
  Fact repeat_choice_two (x : X) m : (forall a, In a m -> a = x) -> (exists m', m = x::x::m') \/ m = nil \/ m = x::nil.
  Proof.
    intros H.
    destruct m as [ | a [ | b m ] ].
    right; left; auto.
    right; right; rewrite (H a); auto; left; auto.
    left; rewrite (H a), (H b).
    exists m; auto.
    right; left; auto.
    left; auto.
  Qed.

  Fact incl_right_cons_incl_or_lhd_or_perm m x l : incl m (x::l) -> incl m l 
                                                                 \/ list_has_dup m 
                                                                 \/ exists m', m ~p x::m' /\ incl m' l.
  Proof.
    intros H.
    apply incl_cons_rinv in H.
    destruct H as (m1 & m2 & H1 & H2 & H3).
    destruct (repeat_choice_two _ H2) as [ (m3 & H4) | [ H4 | H4 ] ]; 
      subst m1; simpl in H1; clear H2.
    
    apply Permutation_sym in H1.
    right; left.
    apply list_hd_eq_perm with (1 := H1).
    apply in_list_hd0; left; auto.
    
    left.
    intros ? H; apply H3; revert H.
    apply Permutation_in; auto.
    
    right; right.
    exists m2; auto.
  Qed.
 
  Fact length_le_and_incl_implies_dup_or_perm l :  
               forall m, length l <= length m 
                      -> incl m l 
                      -> list_has_dup m \/ m ~p l.
  Proof.
    induction on l as IHl with measure (length l).
    destruct l as [ | x l ].
    + intros [ | x ] _ H.
      * right; auto.
      * specialize (H x); simpl in H; contradict H; left; auto.
    + intros [ | y m ] H1 H2.
      * apply le_Sn_0 in H1; destruct H1.
      * simpl in H1; apply le_S_n in H1.
        apply incl_cons_linv in H2. 
        destruct H2 as [ [ H3 | H3 ] H4 ].
        - subst y.
          apply incl_right_cons_choose in H4.
          destruct H4 as [ H4 | H4 ].
          ++ left; apply in_list_hd0; auto.
          ++ destruct IHl with (3 := H4); auto.
             left; apply in_list_hd1; auto.
        - apply incl_right_cons_incl_or_lhd_or_perm in H4.
          destruct H4 as [ H4 | [ H4 | (m' & H4 & H5) ] ].
          ++ destruct IHl with (3 := H4) as [ H5 | H5 ]; auto.
             ** left; apply in_list_hd1; auto.
             ** left; apply in_list_hd0; revert H3.
                apply Permutation_in, Permutation_sym; auto.
          ++ left; apply in_list_hd1; auto.
          ++ apply Permutation_sym in H4.
             apply perm_in_head in H3.
             destruct H3 as (l' & Hl').
             assert (incl m' (y::l')) as H6.
             { intros ? ?; apply Permutation_in with (1 := Hl'), H5; auto. }
             clear H5.
             apply incl_right_cons_choose in H6.
             destruct H6 as [ H6 | H6 ].
             ** left; apply in_list_hd0, Permutation_in with (1 := H4); right; auto.
             ** apply IHl in H6.
                -- destruct H6 as [ H6 | H6 ].
                   +++ left; apply list_hd_eq_perm in H4; apply in_list_hd1; auto.
                   +++ right.
                       apply Permutation_trans with (y::x::m').
                       *** apply perm_skip, Permutation_sym; auto.
                       *** apply Permutation_trans with (1 := perm_swap _ _ _),
                           perm_skip, Permutation_sym,
                           Permutation_trans with (1 := Hl'),
                           perm_skip, Permutation_sym; auto.
                -- apply Permutation_length in Hl'; simpl in Hl' |- *; lia.
                -- apply Permutation_length in Hl'.
                   apply Permutation_length in H4.
                   simpl in Hl', H4; lia.
  Qed.
  
  Theorem finite_pigeon_hole l m : length l < length m -> incl m l -> list_has_dup m.
  Proof.
    intros H1 H2.
    destruct (@length_le_and_incl_implies_dup_or_perm l m) as [ | H5 ]; 
      auto; [ | apply Permutation_length in H5 ]; lia.
  Qed.

End finite_php.
