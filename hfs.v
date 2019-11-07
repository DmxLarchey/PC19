(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Eqdep_dec Lia Bool Max Wellfounded.

Require Import acc_irr measure_ind wf_finite wf_chains.

Section btree.

  Reserved Notation "⌞ x ⌟" (at level 0).
  Reserved Notation "x ∙ y" (at level 2, right associativity).
  Reserved Notation "x ≈ y" (at level 70, no associativity).
  Reserved Notation "x ≉ y" (at level 70, no associativity).
  Reserved Notation "x ≾ y" (at level 70, no associativity).
  Reserved Notation "x ∊ y" (at level 70, no associativity).
  Reserved Notation "x ⋷ y" (at level 70, no associativity).
  Reserved Notation "x ≺ y" (at level 70, no associativity).

  (* ⌞ ⌟ ε ∙ ≈ ≉ ∊ ⋷  ≾ ≺ *)

  Inductive bt : Set := bt_leaf | bt_node : bt -> bt -> bt.

  Notation ε := bt_leaf.
  Infix "∙" := bt_node.

  Fact bt_eq_dec (s t : bt) : { s = t } + { s <> t }.
  Proof. decide equality. Qed.

  Fixpoint bt_depth t :=
    match t with
      | ε   => 0
      | r∙s => max (S ⌞r⌟) ⌞s⌟
    end
  where "⌞ t ⌟" := (bt_depth t).

  (* ⌞ ⌟ ε ∙ ≈ *)

  Inductive bt_equiv : bt -> bt -> Prop :=
    | in_bte_refl : forall s,             s ≈ s
    | in_bte_sym  : forall s t,           s ≈ t
                                       -> t ≈ s
    | in_bte_tran : forall r s t,         r ≈ s
                                       -> s ≈ t
                                       -> r ≈ t
    | in_bte_cntr : forall s t,       s∙s∙t ≈ s∙t
    | in_bte_comm : forall s t u,     s∙t∙u ≈ t∙s∙u
    | in_bte_cngr : forall s s' t t',     s ≈ s'
                                       -> t ≈ t'
                                   ->   s∙t ≈ s'∙t'
  where "s ≈ t" := (bt_equiv s t).

  Notation bte_trans := in_bte_tran.
 
  Hint Constructors bt_equiv.

  Notation "s ≉ t" := (~ s ≈ t).

  Fact bte_leaf_eq s t : s ≈ t -> (s = ε <-> t = ε).
  Proof.
    induction 1; try tauto; split; discriminate.
  Qed.

  Fact bte_discr s t : s∙t ≉ ε.
  Proof. 
   intros H; apply bte_leaf_eq in H.
   generalize (proj2 H eq_refl); discriminate.
  Qed.

  Fact bte_inv_0 s : s ≈ ε <-> s = ε.
  Proof.
    split.
    + intros H; destruct s; auto.
      apply bte_discr in H; tauto.
    + intros ->; auto.
  Qed.

  Notation "s ∊ t" := (s∙t ≈ t).

  (* ⌞ ⌟ ε ∙ ≈  ∊ ⋷  *)

  Inductive bt_restr_mem : bt -> bt -> Prop :=
    | in_btrm_0 : forall s t,    s ⋷ s∙t
    | in_btrm_1 : forall s t u,  s ⋷ u
                             ->  s ⋷ t∙u
  where "s ⋷ t" := (bt_restr_mem s t).

  Hint Constructors bt_restr_mem.

  Fact btrm_inv u s t : u ⋷ s∙t <-> u = s \/ u ⋷ t.
  Proof.
    split.
    + inversion 1; auto.
    + intros [ <- | ]; constructor; auto.
  Qed.

  Notation "s ≾ t" := (forall u, u ⋷ s -> exists v, v ⋷ t /\ u ≈ v).

  Fact bt_rincl_refl s : s ≾ s.
  Proof. intros u; exists u; auto. Qed.

  Fact bt_rincl_trans r s t : r ≾ s -> s ≾ t -> r ≾ t.
  Proof.
    intros H1 H2 u Hu.
    destruct H1 with (1 := Hu) as (v & Hv & H3).
    destruct H2 with (1 := Hv) as (w & ? & ?).
    exists w; split; auto.
    apply bte_trans with v; auto.
  Qed.

  Hint Resolve bt_rincl_refl bt_rincl_trans.

  Lemma bte_rincl s t : s ≈ t -> s ≾ t.
  Proof.
    intros H.
    assert (s ≾ t /\ t ≾ s) as K; [ | apply K ].
    induction H as [ s | s t H IH | r s t H1 [] H2 [] | s t | s t u | s s' t t' H1 [H2 H3] H4 [H5 H6] ]; auto; try tauto.
    + split; apply bt_rincl_trans with s; auto.
    + split; intros u; rewrite btrm_inv; intros [ <- | ]; exists u; auto.
    + split; intros v; rewrite btrm_inv; intros [ <- | ]; exists v; auto;
        revert H; rewrite btrm_inv; intros [ <- | ]; auto.
    + split.
      * intros u; rewrite btrm_inv.
        intros [ <- | ].
        - exists s'; auto.
        - destruct (H5 _ H) as (v & ? & ?); exists v; auto.
      * intros u; rewrite btrm_inv.
        intros [ <- | ].
        - exists s; auto.
        - destruct (H6 _ H) as (v & ? & ?); exists v; auto.
  Qed.
 
  Fact btrm_btm s t : s ⋷ t -> s ∊ t.
  Proof.
    induction 1 as [ | s t u ]; try (constructor; auto; fail).
    constructor; apply bte_trans with (t∙s∙u); auto.
  Qed.

  Hint Resolve btrm_btm.

  Fact btm_congr_l s t u : s ≈ t -> s ∊ u -> t ∊ u.
  Proof.
    intros H1 H2.
    apply bte_trans with (2 := H2); auto.
  Qed.

  Fact btm_congr_r s t u : s ≈ t -> u ∊ s -> u ∊ t.
  Proof.
    intros H1 H2.
    apply bte_trans with (2 := H1),
          bte_trans with (2 := H2); auto.
  Qed.

  Fact btm_inv_0 s : s ∊ ε <-> False.
  Proof. split; try tauto; apply bte_discr. Qed.

  Fact btm_inv u s t : u ∊ s∙t <-> u ≈ s \/ u ∊ t.
  Proof.
    split.
    + intros H.
      destruct (@bte_rincl _ _ H u) as (v & H1 & ?); auto.
      revert H1; rewrite btrm_inv; intros [ <- | ]; auto.
      right; apply bte_trans with (v∙t); auto.
    + intros [ H | H ].
      * apply btm_congr_l with s; auto.
      * apply bte_trans with (1 := in_bte_comm _ _ _); auto.
  Qed.

  Inductive bt_lt : bt -> bt -> Prop :=
    | in_btlt_0 : forall s t,                   ε ≺ s∙t 
    | in_btlt_1 : forall s s' t t', s ≺ s' -> s∙t ≺ s'∙t'
    | in_btlt_2 : forall s t t',    t ≺ t' -> s∙t ≺ s∙t'
  where "s ≺ t" := (bt_lt s t).

  Hint Constructors bt_lt.

  Fact bt_lt_inv s t : s ≺ t -> s = ε /\ (exists u v, t = u∙v)
                             \/ (exists u u' v v', s = u∙v /\ t = u'∙v' /\ u ≺ u')
                             \/ (exists u v v', s = u∙v /\ t = u∙v' /\ v ≺ v').
  Proof.
    destruct 1.
    + left; split; auto; exists s, t; auto.
    + right; left; exists s, s', t, t'; auto.
    + do 2 right; exists s, t, t'; auto.
  Qed.

  Fact bt_lt_node_inv s t u : s∙t ≺ u -> (exists s' t', u = s'∙t' /\ s ≺ s')
                                      \/ (exists t', u = s∙t' /\ t ≺ t').
  Proof. 
    inversion 1.
    + left; exists s', t'; auto.
    + right; exists t'; auto.
 Qed.

  Fact bt_lt_irrefl s : ~ s ≺ s.
  Proof.
    intros H.
    assert (forall t, s ≺ t -> s <> t) as D; [ | apply D in H; destruct H; auto ].
    clear H; induction 1 as [ s t | s s' t H IH | s t t' H IH ]; try discriminate.
    all: contradict IH; inversion IH; auto.
  Qed.

  Fact bt_lt_trans r s t : r ≺ s -> s ≺ t -> r ≺ t.
  Proof.
    intros H1; revert H1 t.
    induction 1 as [ s t | s s' t t' H IH | s t t' H IH ]; intros u.
    + inversion 1; auto.
    + intros H1; apply bt_lt_node_inv in H1.
      destruct H1 as [ (v & w & -> & ?) | (v & -> & ?) ];
        constructor; auto.
    + intros H1; apply bt_lt_node_inv in H1.
      destruct H1 as [ (v & w & -> & ?) | (v & -> & ?) ].
      * constructor; auto.
      * constructor 3; auto.
  Qed.
  
  Fact bt_lt_eq_lt_dec s t : { s ≺ t } + { s = t } + { t ≺ s }.
  Proof.
    revert t; induction s as [ | s1 H1 s2 H2 ]; intros [ | t1 t2 ]; auto.
    destruct (H1 t1) as [ [ H3 | H3 ] | H3 ]; auto.
    subst; destruct (H2 t2) as [ [] | ]; subst; auto.
  Qed.

  Reserved Notation "x †" (at level 1).
  Reserved Notation "x → y" (at level 3, right associativity).

  Fixpoint bt_insert s t : bt :=
    match t with
      | ε   => s∙ε
      | t∙u => match bt_lt_eq_lt_dec s t with
        | inleft (left _)  => s∙t∙u
        | inleft (right _) => t∙u
        | inright _        => t∙(s→u)
      end
    end
  where "s → t" := (bt_insert s t).

  Fact bt_lt_eq_lt_dec_refl s : exists H, bt_lt_eq_lt_dec s s = inleft (right H).
  Proof.
    destruct (bt_lt_eq_lt_dec s s) as [ [ C | H ] | C ].
    1,3: exfalso; revert C; apply bt_lt_irrefl.
    exists H; auto.
  Qed.

  Ltac bt_lt_eq H := match goal with |- context [bt_lt_eq_lt_dec ?x ?x] 
         => destruct (bt_lt_eq_lt_dec_refl x) as (H & ->)
    end.

  Fact bt_insert_leaf s : s→ε = s∙ε.
  Proof. reflexivity. Qed.

  Fact bt_insert_eq s t : s→s∙t = s∙t.
  Proof.
    simpl; bt_lt_eq H; auto.
  Qed.

  Fact bt_insert_lt s t u : s ≺ t -> s→t∙u = s∙t∙u.
  Proof.
    intros H; simpl.
    destruct (bt_lt_eq_lt_dec s t) as [ [C|C] | C ]; auto.
    + contradict H; subst; apply bt_lt_irrefl.
    + destruct (@bt_lt_irrefl s); apply bt_lt_trans with t; auto.
  Qed.

  Fact bt_insert_gt s t u : t ≺ s -> s→t∙u = t∙(s→u).
  Proof.
    intros H; simpl.
    destruct (bt_lt_eq_lt_dec s t) as [ [C|C] | C ]; auto.
    + destruct (@bt_lt_irrefl s); apply bt_lt_trans with t; auto.
    + contradict H; subst; apply bt_lt_irrefl.
  Qed.

  Fact bt_insert_equiv s t : s→t ≈ s∙t.
  Proof.
    induction t as [ | t Ht u Hu ]; simpl; auto.
    destruct (bt_lt_eq_lt_dec s t) as [ [] | ]; subst; auto.
    apply bte_trans with (t∙s∙u); auto.
  Qed.

  Fixpoint bt_norm t :=
    match t with
      | ε   => ε
      | s∙t => s† → t†
    end
  where "t †" := (bt_norm t).

  Hint Resolve bt_insert_equiv.
  
  Fact bt_norm_eq t : t† ≈ t.
  Proof.
    induction t as [ | s ? t ? ]; simpl; auto.
    apply bte_trans with (s†∙t†); auto.
  Qed.

  Opaque bt_insert.

  Tactic Notation "rew" "bt" "insert" := 
    repeat match goal with 
      |             |- context[_→ε]     => rewrite bt_insert_leaf
      |             |- context[?x→?x∙_] => rewrite bt_insert_eq
      | H : ?x ≺ ?y |- context[?x→?y∙_] => rewrite bt_insert_lt with (1 := H)
      | H : ?x ≺ ?y |- context[?y→?x∙_] => rewrite bt_insert_gt with (1 := H)
    end.

  Tactic Notation "bt" "insert" "case" hyp(x) hyp(y) :=
    destruct (bt_lt_eq_lt_dec x y) as [ [|] | ]; subst; rew bt insert; auto.

  Tactic Notation "bt" "lt" "trans" constr(t) := apply bt_lt_trans with t; auto.

  Tactic Notation "bt" "lt" "cycle" :=
    match goal with
      | H1 : ?x ≺ ?x |- _  => destruct (@bt_lt_irrefl x); auto
      | H1 : ?x ≺ ?y, 
        H2 : ?y ≺ ?x |- _  => destruct (@bt_lt_irrefl x); bt lt trans y
      | H1 : ?x ≺ ?y,
        H2 : ?y ≺ ?z,
        H3 : ?z ≺ ?x |- _  => destruct (@bt_lt_irrefl x); bt lt trans y; bt lt trans z
    end.

  Fact bt_insert_cntr s t : s→s→t = s→t.
  Proof.
    induction t as [ | t1 IH1 t2 IH2 ]; rew bt insert; auto.
    bt insert case s t1; f_equal; auto.
  Qed.

  Fact bt_insert_comm s t u : s→t→u = t→s→u.
  Proof.
    induction u as [ | u1 IH1 u2 IH2 ]. 
    + rew bt insert; bt insert case s t.
    + bt insert case t u1; 
      bt insert case s u1; 
      bt insert case s t; 
      try bt lt cycle; 
      f_equal; auto.
  Qed.

  Hint Resolve bt_insert_cntr bt_insert_comm bt_norm_eq.

  Theorem bte_norm_iff s t : s ≈ t <-> s† = t†.
  Proof.
    split.
    + induction 1; simpl; auto.
      * transitivity s†; auto.
      * f_equal; auto.
    + intros H.
      apply bte_trans with s †; auto.
      rewrite H; auto.
  Qed.

  Theorem bt_norm_idem s : s†† = s†.
  Proof. apply bte_norm_iff; auto. Qed.

  Fact bte_dec s t : { s ≈ t } + { s ≉ t }.
  Proof.
    destruct (bt_eq_dec s† t†) as [ H | H ];
    rewrite <- bte_norm_iff in H; auto.
  Qed.

  Opaque max.

  Fact bte_depth_eq s t : s ≈ t -> ⌞s⌟ = ⌞t⌟.
  Proof.
    induction 1; simpl; auto.
    + transitivity ⌞s⌟; auto.
    + rewrite max_assoc, max_idempotent; auto.
    + rewrite max_assoc, (max_comm (S _)), max_assoc; auto.
  Qed.

  Fact btm_depth s t : s ∊ t -> ⌞s⌟ < ⌞t⌟.
  Proof.
    intros H; apply bte_depth_eq in H; simpl in H.
    rewrite <- H.
    apply lt_le_trans with (1 := lt_n_Sn _).
    apply le_max_l.
  Qed.

  (** bt is well-founded for membership *)

  Theorem btm_wf : well_founded (fun s t => s ∊ t).
  Proof.
    apply wf_incl with (1 := btm_depth).
    apply wf_inverse_image, lt_wf.
  Qed.

  Fact btm_chain_depth n s t : chain (fun s t => s ∊ t) n s t -> n+⌞s⌟ <= ⌞t⌟.
  Proof.
    induction 1 as [ | n s t u H1 H2 IH2 ]; auto.
    apply le_trans with (2 := IH2).
    apply btm_depth in H1; lia.
  Qed.

  Fact bt_chain_congr_r n s t t' : t ≈ t' 
                                -> chain (fun s t => s ∊ t) (S n) s t
                                -> chain (fun s t => s ∊ t) (S n) s t'.
  Proof.
    intros H1 H2.
    apply chain_snoc_inv in H2.
    destruct H2 as (y & H2 & H3).
    apply chain_snoc with y; auto.
    revert H3; apply btm_congr_r; auto.
  Qed.
 
  Fact chain_list_comp u l s t : l <> nil
                              -> chain_list (fun s t => s ∊ t) l s t
                              -> chain_list (fun s t => s ∊ t) l s (u∙t).
  Proof.
    rewrite <- (rev_involutive l).
    generalize (rev l); clear l; intros l Hl.
    destruct l as [ | x l ].
    { destruct Hl; auto. }
    clear Hl.
    simpl; intros H.
    apply chain_list_app_inv in H.
    destruct H as (v & H1 & H2).
    apply chain_list_app with v; auto.
    apply chain_list_cons_inv in H2.
    destruct H2 as (-> & k & H2 & H3).
    apply chain_list_nil_inv in H3; subst k.
    constructor 2 with (u∙t); auto.
    + apply btm_inv; auto.
    + constructor.
  Qed.

  Fact chain_comp n u s t : chain (fun s t => s ∊ t) (S n) s t
                         -> chain (fun s t => s ∊ t) (S n) s (u∙t).
  Proof.
    intros H.
    apply chain_chain_list in H.
    destruct H as (l & H1 & H2).
    rewrite H2. 
    apply chain_list_chain.
    apply chain_list_comp; auto.
    destruct l; discriminate.
  Qed.

  Fact btm_depth_chain t : { l | chain_list (fun s t => s ∊ t) l ε t /\ length l = ⌞t⌟ }.
  Proof.
    induction t as [ | s (ls & H1 & H2) t (lt & H3 & H4) ].
    + exists nil; simpl; split; auto; constructor.
    + destruct (le_lt_dec (S ⌞s⌟) ⌞t⌟) as [ H | H ].
      * exists lt; simpl; split.
        - apply chain_list_comp; auto.
          destruct lt; try discriminate; simpl in *; lia.
        - rewrite max_r; auto.
      * exists (ls++s::nil); split.
        - apply chain_list_app with (1 := H1).
          constructor 2 with (s∙t); auto.
          constructor.
        - rewrite app_length; simpl.
          rewrite max_l; lia.
  Qed.
  
  (* Up to ≈, membership in t is finite *)

  Theorem btm_finite_t t : { l | forall s, s ∊ t <-> exists s', s ≈ s' /\ In s' l }.
  Proof.
    induction t as [ | s (ls & Hs) t (lt & Ht) ].
    + exists nil; intros s.
      rewrite btm_inv_0; simpl; firstorder.
    + exists (s::lt); intros u.
      rewrite btm_inv; simpl; rewrite Ht.
      split.
      * intros [ H | (s' & H1 & H2) ].
        - exists s; auto.
        - exists s'; auto.
      * intros (s' & H1 & [ H2 | H2 ]); subst; auto.
        right; exists s'; auto.
  Qed.

  Fixpoint bt_cup s t := 
    match s with 
      | ε   => t
      | x∙s => x∙(bt_cup s t)
    end.

  Theorem bt_cup_spec x s t : x ∊ bt_cup s t <-> x ∊ s \/ x ∊ t.
  Proof.
    revert x; induction s as [ | y Hy s Hs ]; intros x; simpl.
    + rewrite btm_inv_0; tauto.
    + rewrite btm_inv, btm_inv, Hs; tauto.
  Qed.

 Fixpoint bt_ct t := 
    match t with 
      | ε   => ε
      | s∙t => s∙(bt_cup (bt_ct s) (bt_ct t))
    end.

  Fact bt_ct_congr_l u v t : u ≈ v -> u ∊ bt_ct t -> v ∊ bt_ct t.
  Proof.
    revert u v; induction t; simpl; intros ? ? ?; apply btm_congr_l; auto.
  Qed.

  Fact bt_ct_congr_r u s t : s ≈ t -> u ∊ bt_ct s <-> u ∊ bt_ct t.
  Proof.
    intros H; revert H u. 
    induction 1 as [ | s t | r s t H1 IH1 H2 IH2 | s t | s t u 
                   | s s' t t' H1 IH1 H2 IH2 ]; intros v; try tauto.
    + symmetry; auto.
    + rewrite IH1; auto.
    + simpl; repeat (rewrite btm_inv || rewrite bt_cup_spec); tauto.
    + simpl; repeat (rewrite btm_inv || rewrite bt_cup_spec); tauto.
    + simpl; repeat (rewrite btm_inv || rewrite bt_cup_spec).
      rewrite IH1, IH2; split; intros [ H | [] ]; auto; left.
      * apply bte_trans with s; auto.
      * apply bte_trans with s'; auto.
  Qed.

  Let bt_chain_inv_0_rec n x y : chain (fun s t => s ∊ t) n x y -> y = ε -> n = 0 /\ x = ε.
  Proof.
    induction 1 as [ | n x y z H1 H2 IH2 ]; auto.
    intros ->; destruct IH2 as (_ & ->); auto.
    apply bte_discr in H1; tauto.
  Qed.

  Fact bt_chain_inv_0 n x : chain (fun s t => s ∊ t) n x ε -> n = 0 /\ x = ε.
  Proof. intros H; apply bt_chain_inv_0_rec in H; auto. Qed.

  Theorem bt_ct_spec t x : x ∊ bt_ct t <-> exists n, chain (fun s t => s ∊ t) (S n) x t.
  Proof.
    revert x; induction t as [ | s Hs t Ht ]; intros x; simpl.
    + rewrite btm_inv_0; split; try tauto.
      intros (n & Hn).
      apply chain_inv_S in Hn.
      destruct Hn as (y & H1 & H2).
      apply bt_chain_inv_0 in H2.
      destruct H2 as (_ & ->).
      apply bte_discr in H1; tauto.
    + rewrite btm_inv, bt_cup_spec, Hs, Ht.
      split.
      * intros [ H | [ (n & H) | (n & H) ] ].
        - exists 0.
          constructor 2 with (s∙t).
          ++ apply btm_inv; auto.
          ++ constructor.
        - exists (S n).
          apply chain_snoc with s; auto.
        - exists n; apply chain_comp; auto.
      * intros (n & H).
        apply chain_snoc_inv in H.
        destruct H as (y & H1 & H2).
        apply btm_inv in H2.
        destruct H2 as [ H2 | H2 ].
        - destruct n as [ | n ].
          ++ apply chain_inv_0 in H1; subst; auto.
          ++ right; left; exists n.
             revert H1; apply bt_chain_congr_r; auto.
        - right; right; exists n.
          apply chain_snoc with y; auto.
  Qed.

  Notation "x ⊆ y" := (forall u, u ∊ x -> u ∊ y) (at level 70).

  Fact bt_ct_incr t : t ⊆ bt_ct t.
  Proof.
    intro; induction t; simpl; auto.
    rewrite btm_inv, btm_inv, bt_cup_spec; tauto.
  Qed.

  Fact bt_ct_mono s t : s ⊆ t -> bt_ct s ⊆ bt_ct t.
  Proof.
    intros H x.
    do 2 rewrite bt_ct_spec.
    intros (n & Hn).
    apply chain_snoc_inv in Hn.
    destruct Hn as (y & H1 & H2).
    exists n; apply chain_snoc with y; auto.
  Qed.

  Hint Resolve bt_ct_incr bt_ct_mono.

  Definition bt_transitive t := forall u v, u ∊ v -> v ∊ t -> u ∊ t.

  Theorem bt_ct_trans t : bt_transitive (bt_ct t).
  Proof.
    induction t as [ | s Hs t Ht ]; simpl; intros u v H1 H2.
    + apply btm_inv_0 in H2; tauto.
    + apply btm_inv in H2.
      rewrite bt_cup_spec in H2.
      rewrite btm_inv, bt_cup_spec.
      destruct H2 as [ H2 | [ H2 | H2 ] ].
      * right; left; apply bt_ct_congr_r with (1 := H2); auto.
      * right; left; revert H2; apply Hs; auto.
      * right; right; revert H2; apply Ht; auto.
  Qed.

  Hint Resolve bt_ct_trans.

  Fact bt_trans_chain n x y t : bt_transitive t -> chain (fun s t => s ∊ t) n x y -> y ∊ t -> x ∊ t. 
  Proof.
    intros Ht; induction 1 as [ | n x y z H1 H2 IH2 ]; auto.
    intros H; apply Ht with (1 := H1); auto.
  Qed.

  Fact bt_ct_idem t : bt_ct (bt_ct t) ⊆ bt_ct t.
  Proof.
    intros x; rewrite bt_ct_spec.
    intros (n & Hn).
    apply chain_snoc_inv in Hn.
    destruct Hn as (y & H1 & H2).
    revert H1 H2.
    apply bt_trans_chain; auto.
  Qed.

  (** We have computed the transitive closure, spec'ed and proved finite *)  

  Section HF_struct.

    Fact HF_cntr s t : s∙s∙t ≈ s∙t.
    Proof. auto. Qed.

    Fact HF_comm s t u : s∙t∙u ≈ t∙s∙u. 
    Proof. auto. Qed.

    Fact HF_empty s t : s∙t ≉ ε. 
    Proof. apply bte_discr. Qed.

    Fact HF_choice s t u : s∙t∙u ≈ t∙u -> s ≈ t \/ s∙u ≈ u.
    Proof. apply btm_inv. Qed.

    Variable P : bt -> Type.

    Hypothesis (HP0 : forall s t, s ≈ t -> P s -> P t)
               (HP1 : P ε)
               (HP2 : forall s t, P s -> P t -> P (s∙t)).

    Theorem HF_rect : forall t, P t.
    Proof. apply bt_rect; auto. Qed.

  End HF_struct.

End btree.