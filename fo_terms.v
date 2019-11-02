(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Eqdep_dec Lia.

Require Import acc_irr.

Set Implicit Arguments.

Ltac msplit n := 
  match n with 
    | 0    => idtac 
    | S ?n => split; [ | msplit n ]
   end.

Section le_lt_pirr.

  (** lt and lt are proof irrelevant *)

  (* a dependent induction principle for le *)
  
  Scheme le_indd := Induction for le Sort Prop.

  Theorem le_pirr x y (H1 H2 : x <= y) : H1 = H2.
  Proof.
    revert H2.
    induction H1 as [ | m H1 IH ] using le_indd; intro H2.

    change (le_n x) with (eq_rect _ (fun n' => x <= n') (le_n x) _ eq_refl).
    generalize (eq_refl x).
    pattern x at 2 4 6 10, H2. 
    case H2; [intro E | intros m l E].
    rewrite UIP_dec with (p1 := E) (p2 := eq_refl); auto.
    apply eq_nat_dec.
    contradiction (le_Sn_n m); subst; auto.
    
    change (le_S x m H1) with (eq_rect _ (fun n' => x <= n') (le_S x m H1) _ eq_refl).
    generalize (eq_refl (S m)).
    pattern (S m) at 1 3 4 6, H2.
    case H2; [intro E | intros p H3 E].
    contradiction (le_Sn_n m); subst; auto.
    injection E; intro; subst.
    rewrite (IH H3).
    rewrite UIP_dec with (p1 := E) (p2 := eq_refl); auto.
    apply eq_nat_dec.
  Qed.

  Fact lt_pirr x y (H1 H2 : x < y) : H1 = H2.
  Proof. simpl; intros; apply le_pirr. Qed.

End le_lt_pirr.

(** First a small vector library *)

Section vec.

  Variable X : Type.

  Inductive vec : nat -> Type :=
    | vec_nil  : vec 0
    | vec_cons : forall n, X -> vec n -> vec (S n).

  Definition vec_head n (v : vec (S n)) := match v with @vec_cons _ x _ => x end.
  Definition vec_tail n (v : vec (S n)) := match v with @vec_cons _ _ w => w end.

  Let vec_head_tail_type n : vec n -> Prop := 
    match n with
      | 0   => fun v => v = vec_nil
      | S n => fun v => v = vec_cons (vec_head v) (vec_tail v)
    end.

  Let vec_head_tail_prop n v :  @vec_head_tail_type n v.
  Proof. induction v; simpl; auto. Qed.

  Fact vec_0_nil (v : vec 0) : v = vec_nil.
  Proof. apply (vec_head_tail_prop v). Qed.

  Fact vec_head_tail n (v : vec (S n)) : v = vec_cons (vec_head v) (vec_tail v).
  Proof. apply (vec_head_tail_prop v). Qed.

  Fixpoint vec2list n (v : vec n) :=
    match v with
      | vec_nil      => nil
      | vec_cons x v => x::vec2list v
    end.

  Fixpoint list2vec (l : list X) : vec (length l) := 
    match l with 
      | nil  => vec_nil
      | x::l => vec_cons x (list2vec l)
    end.

  Fact vec2list_length n v : length (@vec2list n v) = n.
  Proof. induction v; simpl; f_equal; auto. Defined.

  Fact list2vec_iso l : vec2list (list2vec l) = l.
  Proof. induction l; simpl; f_equal; auto. Qed.

  (* The other part needs a transport *)

  Fact vec2list_iso n v : list2vec (@vec2list n v) = eq_rect_r _ v (vec2list_length v).
  Proof. 
    induction v; simpl; f_equal; auto.
    rewrite IHv; unfold eq_rect_r; simpl.
    generalize (length (vec2list v)) (vec2list_length v); intros; subst.
    cbv; auto.
  Qed.

  Variable x : X.

  Fixpoint in_vec n (v : vec n) : Prop :=
    match v with
      | vec_nil      => False
      | vec_cons y v => y = x \/ in_vec v
    end.

  Fact in_vec_list n v : @in_vec n v <-> In x (vec2list v).
  Proof.
    induction v; simpl; tauto.
  Qed.

End vec.

Arguments vec_nil {X}.

Tactic Notation "vec" "split" hyp(v) "with" ident(n) :=
  rewrite (vec_head_tail v); generalize (vec_head v) (vec_tail v); clear v; intros n v.

Tactic Notation "vec" "nil" hyp(v) := rewrite (vec_0_nil v).

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

  Fact vec_map_ext f g n v : (forall x, in_vec x v -> f x = g x) 
                          -> @vec_map f n v = vec_map g v.
  Proof.
    intros H.
    do 2 rewrite <- vec_in_map_vec_map_eq.
    apply vec_in_map_ext, H.
  Qed.

  Fact vec2list_vec_map (f : X -> Y) n v : vec2list (@vec_map f n v) = map f (vec2list v).
  Proof. induction v; simpl; f_equal; auto. Qed.

End vec_map.

Fact vec_map_map X Y Z (f : X -> Y) (g : Y -> Z) n (v : vec _ n) :
          vec_map g (vec_map f v) = vec_map (fun x => g (f x)) v.
Proof. induction v; simpl; f_equal; auto. Qed. 

Fixpoint vec_sum n (v : vec nat n) :=
  match v with 
    | vec_nil      => 0
    | vec_cons x v => x+vec_sum v
  end.

Section list_in_map.

  Variable (X Y : Type).

  Fixpoint list_in_map l : (forall x, @In X x l -> Y) -> list Y.
  Proof.
    refine (match l with
      | nil  => fun _ => nil
      | x::l => fun f => f x _ :: @list_in_map l _
    end).
    + left; auto.
    + intros y Hy; apply (f y); right; auto.
  Defined.

  Theorem In_list_in_map l f x (Hx : In x l) : In (f x Hx) (list_in_map l f).
  Proof.
    revert f x Hx.
    induction l as [ | x l IHl ]; intros f y Hy.
    + destruct Hy.
    + destruct Hy as [ -> | Hy ].
      * left; auto.
      * right.
        apply (IHl (fun z Hz => f z (or_intror Hz))).
  Qed.

End list_in_map.

Section list_dec.

  Variable (X : Type) (P Q : X -> Prop) (H : forall x, { P x } + { Q x }).
  
  Theorem list_dec l : { x | In x l /\ P x } + { forall x, In x l -> Q x }.
  Proof.
    induction l as [ | x l IHl ].
    + right; intros _ [].
    + destruct (H x) as [ Hx | Hx ].
      1: { left; exists x; simpl; auto. }
      destruct IHl as [ (y & H1 & H2) | H1 ].
      * left; exists y; split; auto; right; auto.
      * right; intros ? [ -> | ? ]; auto.
  Qed.

End list_dec.

Section finite.

  Definition finite_t X := { lX | forall x : X, In x lX }.

  Theorem fin_length n : { ll | forall l : list bool, length l < n <-> In l ll }.
  Proof. 
    induction n as [ | n (ll & Hll) ].
    + exists nil; intros; split; try lia; intros [].
    + exists (nil :: map (cons true) ll ++ map (cons false) ll).
      intros [ | [] l ]; simpl.
      * split; auto; lia.
      * split. 
        - right; apply in_or_app; left; apply in_map_iff.
          exists l; split; auto; apply Hll; lia.
        - intros [ H | H ]; try discriminate.
          apply in_app_or in H; destruct H as [ H | H ];
            apply in_map_iff in H; destruct H as (m & H1 & H2);
            apply Hll in H2; inversion H1; subst; try lia.
      * split.
        - right; apply in_or_app; right; apply in_map_iff.
          exists l; split; auto; apply Hll; lia.
        - intros [ H | H ]; try discriminate.
          apply in_app_or in H; destruct H as [ H | H ];
            apply in_map_iff in H; destruct H as (m & H1 & H2);
            apply Hll in H2; inversion H1; subst; try lia.
  Qed.

  Theorem finite_t_bool_list n : finite_t { l : list bool | length l < n }.
  Proof.
    destruct (fin_length n) as (ll & Hll).
    set (f (l : list bool) (H : In l ll) := exist (fun l => length l < n) l (proj2 (Hll l) H)).
    exists (list_in_map _ f).
    intros (l & Hl).
    generalize Hl; intros H.
    apply Hll in Hl.
    replace (exist _ l H) with (f l Hl).
    + apply In_list_in_map.
    + unfold f; f_equal; apply lt_pirr.
  Qed.

  Theorem finite_t_option X : finite_t X -> finite_t (option X).
  Proof.
    intros (lX & HX).
    exists (None :: map Some lX).
    intros [x|]; simpl; auto.
    right; apply in_map_iff; exists x; auto.
  Qed.

End finite.

(** Then first order terms with signature *)

Section first_order_terms.

  Variable (var sym : Set)         (* a type of variables and symbols *)
           (sym_ar : sym -> nat).  (* arities for symbols *)

  Unset Elimination Schemes.       (* we do not want the autogen recursors *)

  (** The Type of first order terms over signature s *)

  Inductive fo_term : Set :=
    | in_var : var -> fo_term
    | in_fot : forall s, vec fo_term (sym_ar s) -> fo_term.

  Set Elimination Schemes.

  Section fo_term_rect.

    (** We build a Type level dependent recursor together with
        a fixpoint equation *)

    Let sub_fo_term x t := 
      match t with 
        | in_var _    => False 
        | @in_fot s v => in_vec x v 
      end.  

    (** This proof has to be carefully crafted for guardness *)
 
    Let Fixpoint Acc_sub_fo_term t : Acc sub_fo_term t.
    Proof.
      destruct t as [ x | s v ]; constructor 1; simpl.
      + intros _ [].
      + intros x.
        revert v; generalize (sym_ar s).
        induction v as [ | n y w IHw ].
        * destruct 1.
        * intros [ H | H ].
          - rewrite <- H; apply Acc_sub_fo_term.
          - apply IHw, H.
    Qed.

    (** This is a Type level (_rect) dependent recursor with induction
        hypothesis using Prop level in_vec *) 

    Variable (P   : fo_term -> Type)
             (HP0 : forall x, P (in_var x))
             (IHP : forall s v, (forall t, in_vec t v -> P t) -> P (@in_fot s v)).

    Let Fixpoint Fix_IHP t (Ht : Acc sub_fo_term t) { struct Ht } : P t :=
      match t as t' return Acc sub_fo_term t'-> P t' with
        | in_var x    => fun _  => HP0 x
        | @in_fot s v => fun Ht => @IHP s v (fun x Hx => @Fix_IHP x (Acc_inv Ht _ Hx))
      end Ht.

    Let Fix_IHP_fix t Ht :
        @Fix_IHP t Ht 
      = match t as t' return Acc sub_fo_term t' -> _ with 
          | in_var x    => fun _   => HP0 x
          | @in_fot s v => fun Ht' => @IHP s v (fun y H => Fix_IHP (Acc_inv Ht' H)) 
        end Ht.
    Proof. destruct Ht; reflexivity. Qed.

    Definition fo_term_rect t : P t.
    Proof. apply Fix_IHP with (1 := Acc_sub_fo_term t). Defined.

    Hypothesis IHP_ext : forall s v f g, (forall y H, f y H = g y H) -> @IHP s v f = IHP v g.

    Let Fix_IHP_Acc_irr : forall t f g, @Fix_IHP t f = Fix_IHP g.
    Proof.
      apply Acc_irrelevance.
      intros [] f g H; auto; apply IHP_ext; auto.
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

  Definition fo_term_rec (P : _ -> Set) := @fo_term_rect P.
  Definition fo_term_ind (P : _ -> Prop) := @fo_term_rect P.

  Section fo_term_recursion.

    (** We specialize the general recursor to fixed output type.
        The fixpoint equation does not require extensionality anymore *)

    Variable (X : Type)
             (F0 : var -> X)
             (F  : forall s, vec fo_term (sym_ar s) -> vec X (sym_ar s) -> X).

    Definition fo_term_recursion : fo_term -> X.
    Proof.
      induction 1 as [ x | s v IHv ].
      + exact (F0 x).
      + apply (@F s v).
        apply vec_in_map with (1 := IHv).
    Defined.

    Theorem fo_term_recursion_fix_0 x :
      fo_term_recursion (in_var x) = F0 x.
    Proof. reflexivity. Qed.

    Theorem fo_term_recursion_fix_1 s v :
      fo_term_recursion (@in_fot s v) = F v (vec_map fo_term_recursion v).
    Proof.
      unfold fo_term_recursion at 1.
      rewrite fo_term_rect_fix; f_equal.
      + rewrite vec_in_map_vec_map_eq; auto.
      + intros; f_equal; apply vec_in_map_ext; auto.
    Qed.

  End fo_term_recursion.

  Check fo_term_rect_fix.
  Check fo_term_recursion_fix_0.
  Check fo_term_recursion_fix_1.

  (** We can now define eg the size of terms easily with the
      corresponding fixpoint equation *)

  Section fo_size_dep.

    Variable cost : sym -> nat.

    Definition fo_term_size : fo_term -> nat.
    Proof.
      apply fo_term_recursion.
      + intros _; exact 1.
      + intros s _ v.
        exact (cost s+vec_sum v).
    Defined.

    Fact fo_term_size_fix_0 x : 
         fo_term_size (in_var x) = 1.
    Proof. apply fo_term_recursion_fix_0. Qed.
  
    Fact fo_term_size_fix_1 s v :
         fo_term_size (@in_fot s v) = cost s + vec_sum (vec_map fo_term_size v).
    Proof. apply fo_term_recursion_fix_1. Qed.

  End fo_size_dep.

  Check fo_term_size_fix_1.

  Definition fo_term_vars : fo_term -> list var.
  Proof.
    apply fo_term_recursion.
    + intros x; exact (x::nil).
    + intros s _ w.
      apply vec2list in w.
      revert w; apply concat.
  Defined.

  Fact fo_term_vars_fix_0 x : fo_term_vars (in_var x) = x :: nil.
  Proof. apply fo_term_recursion_fix_0. Qed.

  Fact fo_term_vars_fix_2 s v : fo_term_vars (@in_fot s v) = concat (vec2list (vec_map fo_term_vars v)).
  Proof. apply fo_term_recursion_fix_1. Qed.

  Fact fo_term_vars_fix_1 s v : fo_term_vars (@in_fot s v) = flat_map fo_term_vars (vec2list v).
  Proof.
    rewrite fo_term_vars_fix_2, vec2list_vec_map, <- flat_map_concat_map; auto.
  Qed.
 
End first_order_terms.

Arguments in_var { var sym sym_ar }.

Create HintDb fo_term_db.
Tactic Notation "rew" "fot" := autorewrite with fo_term_db.

Hint Rewrite fo_term_vars_fix_0 fo_term_vars_fix_1 : fo_term_db. 

Section fo_term_subst.

  Variable (sym : Set) (sym_ar : sym -> nat)
           (X Y : Set).

  Section subst.

    Variable (f : X -> fo_term Y sym_ar).

    Definition fo_term_subst : fo_term X sym_ar -> fo_term Y sym_ar.
    Proof.
      apply fo_term_recursion.
      + apply f.
      + intros s _ w; exact (in_fot s w).
    Defined.

    Fact fo_term_subst_fix_0 x : 
         fo_term_subst (in_var x) = f x.
    Proof. apply fo_term_recursion_fix_0. Qed.

    Fact fo_term_subst_fix_1 s v : 
         fo_term_subst (in_fot s v) = in_fot s (vec_map fo_term_subst v).
    Proof. apply fo_term_recursion_fix_1. Qed.

  End subst.

  Section map.

    Variable (f : X -> Y).

    Definition fo_term_map : fo_term X sym_ar -> fo_term Y sym_ar.
    Proof.
      apply fo_term_recursion.
      + intros x; exact (in_var (f x)).
      + intros s _ w; exact (in_fot s w).
    Defined.

    Fact fo_term_map_fix_0 x : 
         fo_term_map (in_var x) = in_var (f x).
    Proof. apply fo_term_recursion_fix_0. Qed.

    Fact fo_term_map_fix_1 s v : 
         fo_term_map (in_fot s v) = in_fot s (vec_map fo_term_map v).
    Proof. apply fo_term_recursion_fix_1. Qed.

  End map.

  Global Opaque fo_term_map fo_term_subst.

  Global Hint Rewrite fo_term_subst_fix_0 fo_term_subst_fix_1
               fo_term_map_fix_0 fo_term_map_fix_1 : fo_term_db.

  Fact fo_term_subst_map f t : fo_term_subst (fun x => in_var (f x)) t 
                             = fo_term_map f t.
  Proof. induction t; rew fot; f_equal. Qed.

  Fact fo_term_subst_ext f g t : (forall x, In x (fo_term_vars t) -> f x = g x)
                               -> fo_term_subst f t = fo_term_subst g t.
  Proof.
    induction t as [ | s v IHv ]; intros Hfg; rew fot.
    + apply Hfg; rew fot; simpl; auto.
    + f_equal; apply vec_map_ext.
      intros; apply IHv; auto.
      intros y Hy; apply Hfg; rew fot. 
      apply in_flat_map; exists x.
      rewrite <- in_vec_list; tauto.
  Qed.

  Fact fo_term_map_ext f g t : (forall x, In x (fo_term_vars t) -> f x = g x)
                             -> fo_term_map f t = fo_term_map g t.
  Proof.
    intros Hfg. 
    do 2 rewrite <- fo_term_subst_map.
    apply fo_term_subst_ext.
    intros; f_equal; auto.
  Qed.

End fo_term_subst.

Opaque fo_term_map fo_term_subst.

Hint Rewrite fo_term_subst_fix_0 fo_term_subst_fix_1
             fo_term_map_fix_0 fo_term_map_fix_1 : fo_term_db.

Section fo_subst_comp.

  Variables (sym : Set) (sym_ar : sym -> nat) (X Y Z : Set) 
            (f : X -> fo_term Y sym_ar) 
            (g : Y -> fo_term Z sym_ar).

  Fact fo_term_subst_comp t :
         fo_term_subst g (fo_term_subst f t)
       = fo_term_subst (fun x => fo_term_subst g (f x)) t.
  Proof.
    induction t; rew fot; auto; rew fot.
    rewrite vec_map_map; f_equal.
    apply vec_map_ext; auto.
  Qed.

End fo_subst_comp.

Definition env_lift K (phi : nat -> K) k n :=
  match n with
    | 0   => k
    | S n => phi n
  end.

Arguments env_lift K phi k n /.
Local Notation "phi ↑ k" := (env_lift phi k) (at level 0).

Section fol.

  Variable (fol_sym : Set) (fol_sym_ar : fol_sym -> nat)
           (fol_pred : Set) (fol_pred_ar : fol_pred -> nat). 

  Inductive fol_bop := fol_conj | fol_disj | fol_imp.
  Inductive fol_qop := fol_ex | fol_fa.

  Inductive fol_form : Set :=
    | fol_false : fol_form
    | fol_atom  : forall p, vec (fo_term nat fol_sym_ar) (fol_pred_ar p) -> fol_form
    | fol_bin   : fol_bop -> fol_form -> fol_form -> fol_form
    | fol_quant : fol_qop -> fol_form -> fol_form.

  Notation 𝕋 := (fo_term nat fol_sym_ar).
  Notation 𝔽 := fol_form.

  (* Notation ⟦ ⟧ ⟪ ⟫ φ ψ σ ρ ↑ ⦃ ⦄ ⇡*)

  Definition fo_term_subst_lift (σ : nat -> 𝕋) n :=
    match n with 
      | 0   => in_var 0
      | S n => fo_term_map S (fo_term_subst σ (in_var n))
    end.

  Arguments fo_term_subst_lift σ n /.

  Local Notation "⇡ σ" := (fo_term_subst_lift σ) (at level 0).

  Local Reserved Notation "t '⦃' σ '⦄'" (at level 0).

  Fixpoint fol_subst σ A :=
    match A with
      | fol_false     => fol_false
      | @fol_atom p v => fol_atom (vec_map (fo_term_subst σ) v)
      | fol_bin c A B => fol_bin c (A⦃σ⦄) (B⦃σ⦄)
      | fol_quant q A => fol_quant q (A⦃⇡σ⦄) 
    end
  where "A ⦃ σ ⦄" := (fol_subst σ A).

  Fact fol_subst_ext σ ρ : (forall n, σ n = ρ n) -> forall A, A⦃σ⦄ = A⦃ρ⦄.
  Proof.
    intros Hfg A; revert A σ ρ Hfg. 
    induction A as [ | p v | c A IHA B IHB | q A IHA ]; intros f g Hfg; simpl; f_equal; auto.
    + apply vec_map_ext; intros; apply fo_term_subst_ext; intros; auto.
    + apply IHA. intros [ | n ]; simpl; rew fot; f_equal; auto.
  Qed.

  (** This theorem is the important one that shows substitutions do compose 
      hence De Bruijn notation are handled correctly by substitutions *)

  Fact fol_subst_subst σ ρ A : (A⦃σ⦄)⦃ρ⦄ = A⦃fun n => fo_term_subst ρ (σ n)⦄.
  Proof.
    revert σ ρ; induction A as [ | p v | b A IHA B IHB | q A IHA ]; simpl; intros f g; auto.
    + f_equal.
      rewrite vec_map_map.
      apply vec_map_ext.
      intros; rew fot. rewrite fo_term_subst_comp.
      apply fo_term_subst_ext.
      intros; rew fot; auto.
    + f_equal; auto.
    + f_equal.
      rewrite IHA; auto.
      apply fol_subst_ext.
      intros [ | n ]; rew fot; simpl; rew fot; simpl; auto.
      do 2 rewrite <- fo_term_subst_map, fo_term_subst_comp.
      apply fo_term_subst_ext.
      intros; rew fot; rewrite fo_term_subst_map; simpl; rew fot; auto.
  Qed.

  Section semantics.

    Variable (X : Type) (sem_sym  : forall s, vec X (fol_sym_ar s) -> X)
                        (sem_pred : forall s, vec X (fol_pred_ar s) -> Prop).

    Implicit Type φ : nat -> X.

    Definition fot_sem φ : 𝕋 -> X.
    Proof.
      apply fo_term_recursion.
      + exact φ.
      + intros s _ w; exact (sem_sym w).
    Defined.

    Local Notation "'⟦' t '⟧'" := (fun φ => @fot_sem φ t) (at level 0).

    (* Notation ⟦ ⟧ ⟪ ⟫ φ ψ σ 𝕋 𝔽 *)

    Fact fot_sem_fix_0 φ n : ⟦in_var n⟧ φ = φ n.
    Proof. apply fo_term_recursion_fix_0. Qed.

    Fact fot_sem_fix_1 φ s v : ⟦in_fot s v⟧ φ = sem_sym (vec_map (fun t => ⟦t⟧ φ) v).
    Proof. apply fo_term_recursion_fix_1. Qed.

    Hint Rewrite fot_sem_fix_0 fot_sem_fix_1 : fo_term_db.

    Fact fot_sem_ext φ ψ : (forall n, φ n = ψ n) -> forall t, ⟦t⟧ φ = ⟦t⟧ ψ.
    Proof.
      induction t; rew fot; f_equal; auto.
      apply vec_map_ext; intros; auto.
    Qed.

    Fact fot_sem_subst φ σ t : ⟦fo_term_subst σ t⟧ φ = ⟦t⟧ (fun n => ⟦σ n⟧ φ).
    Proof.
      induction t; rew fot; f_equal; auto.
      rewrite vec_map_map.
      apply vec_map_ext; intros; auto.
    Qed.

    Definition fol_bin_sem b :=
      match b with
        | fol_conj => and
        | fol_disj => or
        | fol_imp  => fun A B => A -> B
      end.

    Arguments fol_bin_sem b /.

    Fact fol_bin_sem_dec b A B : { A } + { ~ A } -> { B } + { ~ B } 
                              -> { fol_bin_sem b A B }
                               + { ~ fol_bin_sem b A B }.
    Proof.
      revert b; intros [] HA HB; simpl; tauto.
    Qed.

    Definition fol_quant_sem K q (P : K -> Prop) :=
      match q with
        | fol_ex => ex P
        | fol_fa => forall x, P x 
      end.

    Arguments fol_quant_sem K q P /.

    Fact fol_quant_sem_equiv K (P Q : K -> Prop) : 
              (forall k, P k <-> Q k) 
            -> forall q, fol_quant_sem q P <-> fol_quant_sem q Q.
    Proof.
      intros H []; simpl.
      + split; intros (k & ?); exists k; apply H; auto.
      + split; intros ? k; apply H; auto. 
    Qed.

    Fact fol_quant_sem_dec lX (HX : forall x : X, In x lX) q (P : X -> Prop) : 
              (forall x, { P x } + { ~ P x }) -> { fol_quant_sem q P } + { ~ fol_quant_sem q P }.
    Proof.
      revert q; intros [] H; simpl.
      + destruct list_dec with (1 := H) (l := lX)
          as [ (x & H1 & H2) | H1 ].
        * left; firstorder.
        * right; intros (y & Hy).
          apply (H1 y); auto.
      + destruct list_dec with (P := fun x => ~ P x) (Q := P) (l := lX)
          as [ (x & H1 & H2) | H1 ].
        * firstorder.
        * right; contradict H2; auto.
        * left; intros x; apply H1; auto.
    Qed.

    (* Notation ⟦ ⟧ ⟪ ⟫ φ ψ σ ↑ *)

    Local Reserved Notation "'⟪' f '⟫'" (at level 0).

    Fixpoint fol_sem φ A : Prop :=
      match A with
        | fol_false     => False
        | fol_atom v    => sem_pred (vec_map (fun t => ⟦t⟧ φ) v)
        | fol_bin b A B => fol_bin_sem b (⟪A⟫ φ) (⟪B⟫ φ) 
        | fol_quant q A => fol_quant_sem q (fun x => ⟪A⟫ (φ↑x))
      end
    where "⟪ A ⟫" := (fun φ => fol_sem φ A).

    Definition fol_big_disj := fold_right (fol_bin fol_disj) fol_false.

    Fact fol_sem_big_disj lf φ : ⟪ fol_big_disj lf ⟫ φ <-> exists f, In f lf /\ ⟪ f ⟫ φ.
    Proof.
      induction lf as [ | f lf IHlf ]; simpl.
      + split; try tauto; intros ( ? & [] & _).
      + rewrite IHlf.
        split.
        * intros [ H | (g & H1 & H2) ].
          - exists f; auto.
          - exists g; auto.
        * intros (g & [ <- | Hg ] & ?); auto.
          right; exists g; auto.
    Qed.

    Fact fol_sem_ext φ ψ : (forall n, φ n = ψ n) -> forall A, ⟪A⟫ φ <-> ⟪A⟫ ψ.
    Proof.
      intros H A; revert A φ ψ H.
      induction A as [ | p v | b A IHA B IHB | q A IHA ]; simpl; intros phi psy H; try tauto.
      + match goal with | |- sem_pred ?x <-> sem_pred ?y => replace x with y; try tauto end.
        apply vec_map_ext; intros; apply fot_sem_ext; auto.
      + destruct b; rewrite (IHA _ _ H), (IHB _ _ H); tauto.
      + destruct q.
        * split; intros (x & Hx); exists x; revert Hx; apply IHA;
            intros [ | n ]; simpl; auto.
        * split; intros H1 x; generalize (H1 x); clear H1; apply IHA;
           intros [ | n ]; simpl; auto.
    Qed.

    (* Notation ⟦ ⟧ ⟪ ⟫ φ ψ σ ↑ ⦃ ⦄*)

    (** Semantics commutes with substitutions ... good *)

    Theorem fol_sem_subst φ σ A : ⟪ A⦃σ⦄ ⟫ φ <-> ⟪A⟫ (fun n => ⟦σ n⟧ φ).
    Proof.
      revert φ σ; induction A as [ | p v | b A IHA B IHB | q A IHA ]; simpl; intros phi f; try tauto.
      + match goal with | |- sem_pred ?x <-> sem_pred ?y => replace x with y; try tauto end.
        rewrite vec_map_map; apply vec_map_ext.
        intros; rewrite fot_sem_subst; auto.
      + destruct b; rewrite (IHA phi f), (IHB phi f); tauto.
      + apply fol_quant_sem_equiv; intros x. 
        rewrite IHA; apply fol_sem_ext; intros [ | n ].
        - simpl; rew fot; simpl; auto.
        - unfold fo_term_subst_lift.
          rewrite <- fo_term_subst_map, fo_term_subst_comp.
          rewrite fot_sem_subst; simpl; rew fot.
          rewrite fot_sem_subst; apply fot_sem_ext.
          intros; cbv; auto.
    Qed.

    Section decidable.

      (** For the semantics relation to be decidable over a finite domain,
         it is necessary and SUFFICIENT that the sem_pred relation is decidable
         or equivalently, each predicate is interpreted as a map: vec X _ -> bool *)

      Variable (lX : list X) (HX : forall x : X, In x lX).
      Variable (Hpred : forall s v, { @sem_pred s v } + { ~ sem_pred v }).

      Theorem fol_sem_dec A φ : { ⟪A⟫ φ } + { ~ ⟪A⟫ φ }.
      Proof.
        revert φ.
        induction A as [ | p v | b A IHA B IHB | q A IHA ]; intros phi.
        + simpl; tauto.
        + simpl; apply Hpred.
        + simpl fol_sem; apply fol_bin_sem_dec; auto.
        + simpl fol_sem; apply fol_quant_sem_dec with (1 := HX); auto.
      Qed.

    End decidable.

  End semantics.

  Definition fo_form_fin_SAT (A : 𝔽) := 
       exists X s_sym s_pred l φ, @fol_sem X s_sym s_pred φ A
                              /\  forall x : X, In x l.

End fol.

Hint Rewrite fo_term_vars_fix_0 fo_term_vars_fix_1  
             fo_term_subst_fix_0 fo_term_subst_fix_1
             fot_sem_fix_0 fot_sem_fix_1 : fo_term_db.

Section pcp_hand.

  Variable (X : Type) (lc : list (list X * list X)).

  Inductive pcp_hand : list X -> list X -> Prop :=
    | in_pcph_0 : forall x y, In (x,y) lc -> pcp_hand x y
    | in_pcph_1 : forall x y u l, In (x,y) lc -> pcp_hand u l -> pcp_hand (x++u) (y++l).

  (** Any hand is either a card or of the for x++p/y++q where
      x/y is a non-void card and p/q is a hand *)

  Lemma pcp_hand_inv p q : 
       pcp_hand p q -> In (p,q) lc 
                    \/ exists x y p' q', In (x,y) lc /\ pcp_hand p' q' 
                                      /\ p = x++p' /\ q = y++q' 
                        /\  (x <> nil /\ y = nil  
                          \/ x = nil /\ y <> nil
                          \/ x <> nil /\ y <> nil ).
  Proof.
    induction 1 as [ x y H | x y p q H1 H2 IH2 ].
    + left; auto. 
    + destruct x as [ | a x ]; [ destruct y as [ | b y ] | ].
      * simpl; auto.
      * right; exists nil, (b::y), p, q; simpl; msplit 4; auto.
        right; left; split; auto; discriminate.
      * right; exists (a::x), y, p, q; simpl; msplit 4; auto.
        destruct y.
        - left; split; auto; discriminate.
        - right; right; split; discriminate.
  Qed.

  Definition PCP := exists l, pcp_hand l l.

End pcp_hand.

Tactic Notation "solve" "ite" :=
      match goal with _ : ?x < ?y |- context[if le_lt_dec ?y ?x then _ else _]
        => let G := fresh in destruct (le_lt_dec y x) as [ G | _ ]; [ exfalso; lia | ]
      end.

Section bpcp.

  Variable lc : list (list bool * list bool).

  Inductive m_sym := fb : bool -> m_sym | fe | fs.

  Definition a_sym s := 
    match s with
      | fb _ => 1
      | _   => 0
    end.

  Inductive m_pred := p_P | p_lt | p_eq.

  Definition a_pred (p : m_pred) := 2.

  Arguments a_sym s /.
  Arguments a_pred p /.

  Notation term := (fo_term nat a_sym).

  Notation form := (fol_form a_sym a_pred).

  Infix "⤑" := (fol_bin fol_imp) (at level 62, right associativity).
  Infix "⟑" := (fol_bin fol_conj) (at level 60, right associativity).
  Infix "⟇" := (fol_bin fol_disj) (at level 61, right associativity).
  Notation "∀" := (fol_quant fol_fa).
  Notation "∃" := (fol_quant fol_ex).

  Infix "##" := (vec_cons) (at level 65, right associativity).
  Notation "£" := (@in_var nat _ a_sym).
  Notation ø := (vec_nil).
 
  Notation e := (in_fot fe ø).
  Notation "∗" := (in_fot fs ø).
  Notation "⊥" := (fol_false a_sym a_pred).

  Notation "¬" := (fun x => x ⤑ ⊥).
  Notation 𝓟  := (fun x y => fol_atom a_pred p_P (x##y##ø)).
  Notation "x ≡ y" := (fol_atom a_pred p_eq (x##y##ø)) (at level 59).
  Notation "x ≺ y" := (fol_atom a_pred p_lt (x##y##ø)) (at level 59).

  Notation f_ := (fun b x => @in_fot _ _ a_sym (fb b) (x##ø)).

  Fixpoint lb_app (l : list bool) (t : term) : term :=
    match l with 
      | nil  => t
      | b::l => f_ b (lb_app l t)
    end.

  Notation lb2term := (fun l => lb_app l e).

  Definition phi_P := ∀ (∀ (𝓟  (£1) (£0) ⤑ ¬ (£1 ≡ ∗) ⟑ ¬ (£0 ≡ ∗))).

  Definition lt_irrefl := ∀ (¬ (£0 ≺ £0)).
  Definition lt_trans := ∀(∀(∀(£2 ≺ £1 ⤑ £1 ≺ £0 ⤑ £2 ≺ £0))).
  Definition phi_lt := lt_irrefl ⟑ lt_trans.

  Definition eq_neq (b : bool) := ∀(¬(f_ b (£0) ≡ e)).
  Definition eq_inj (b : bool) := ∀(∀( ¬(f_ b (£1) ≡ ∗) ⤑ f_ b (£1) ≡ f_ b (£0) ⤑ £1 ≡ £0)).
  Definition eq_real := ∀(∀(f_ true (£1) ≡ f_ false (£0) ⤑ f_ true (£1) ≡ ∗
                                                         ⟑ f_ false (£0) ≡ ∗)).
  Definition phi_eq := eq_neq true ⟑ eq_neq false 
                     ⟑ eq_inj true ⟑ eq_inj false 
                     ⟑ eq_real.

  Definition lt_pair (u v x y : term) := (u ≺ x ⟑ v ≡ y) ⟇ (v ≺ y ⟑ u ≡ x) ⟇ (u ≺ x ⟑ v ≺ y).

  Definition lt_simul (c : list bool * list bool) := 
    let (s,t) := c 
    in   (£1 ≡ lb2term s ⟑ £0 ≡ lb2term t)
       ⟇ ∃(∃(𝓟 (£1) (£0) ⟑ £3 ≡ lb_app s (£1) ⟑ £2 ≡ lb_app t (£0) ⟑ lt_pair (£1) (£0) (£3) (£2) )).

  Definition phi_simul := ∀(∀(𝓟 (£1) (£0) ⤑ fol_big_disj (map lt_simul lc))).

  Definition phi_R := phi_P ⟑ phi_lt ⟑ phi_eq ⟑ phi_simul ⟑ ∃(𝓟 (£0) (£0)).

  Section BPCP_fin_sat.

    Variable (l : list bool) (Hl : pcp_hand lc l l). 

    Let n := length l.

    Let X := option { m : list bool | length m < S n }.
    Let fin_X : finite_t X.
    Proof. apply finite_t_option, finite_t_bool_list. Qed.

    Let lX := proj1_sig fin_X.
    Let HlX : forall p, In p lX.
    Proof. apply (proj2_sig fin_X). Qed.

    Let sem_sym : forall s, vec X (a_sym s) -> X.
    Proof.
      intros []; simpl.
      + intros v.
        case_eq (vec_head v).
        * intros (m & Hm) H.
          destruct (le_lt_dec n (length m)) as [ | H1 ].
          - right.
          - left; exists (b::m); apply lt_n_S, H1.
        * right.
      + left; exists nil; apply lt_0_Sn.
      + right.
    Defined.

    Let sem_pred : forall p, vec X (a_pred p) -> Prop.
    Proof.
      intros []; simpl; intros v.
      + destruct (vec_head v) as [ (s & Hs) | ].
        2: exact False.
        destruct (vec_head (vec_tail v)) as [ (t & Ht) | ].
        2: exact False.
        exact (pcp_hand lc s t).
      + destruct (vec_head v) as [ (s & Hs) | ].
        2: exact False.
        destruct (vec_head (vec_tail v)) as [ (t & Ht) | ].
        2: exact False.
        exact (s <> t /\ exists u, u++s = t).
      + exact (vec_head v = vec_head (vec_tail v)).
    Defined.

    Notation "⟦ t ⟧" := (fun φ => fot_sem sem_sym φ t).

    Let fot_sem_lb_app lb t φ : 
      match ⟦ t ⟧ φ with
        | Some (exist _ m Hm) =>   
          match le_lt_dec (S n) (length lb + length m) with
            | left _  => ⟦ lb_app lb t ⟧ φ = None
            | right _ => exists H, ⟦ lb_app lb t ⟧ φ = Some (exist _ (lb++m) H)
          end
        | None => ⟦ lb_app lb t ⟧ φ = None
      end.
    Proof.
      induction lb as [ | x lb IH ]; simpl lb_app.
      + destruct (⟦ t ⟧ φ) as [ (m & Hm) | ]; auto.
        simpl plus; solve ite; simpl; exists Hm; auto.
      + destruct (⟦ t ⟧ φ) as [ (m & Hm) | ]; auto.
        2: { rew fot; simpl vec_map; rewrite IH; simpl; auto. }
        simpl plus.
        destruct (le_lt_dec (S n) (length lb + length m)) as [ H1 | H1 ].
        * destruct (le_lt_dec (S n) (S (length lb+length m))) as [ H2 | H2 ].
          2: exfalso; lia.
          rew fot; simpl vec_map; rewrite IH; auto.
        * destruct IH as (H2 & IH).
          destruct (le_lt_dec (S n) (S (length lb+length m))) as [ H3 | H3 ].
          - rew fot; simpl vec_map; rewrite IH; simpl.
            destruct (le_lt_dec n (length (lb++m))) as [ | C ]; auto.
            exfalso; rewrite app_length in C; lia.
          - assert (length ((x::lb)++m) < S n) as H4.
            { simpl; rewrite app_length; auto. }
            exists H4; rew fot; simpl vec_map.
            rewrite IH; simpl.
            destruct (le_lt_dec n (length (lb++m))) as [ H5 | H5 ].
            ++ exfalso; rewrite app_length in H5; lia.
            ++ do 2 f_equal; apply lt_pirr.
    Qed.

    Let fot_sem_lb_app_Some lb t φ lt Ht (H : length (lb++lt) < S n) : 
           ⟦ t ⟧ φ = Some (exist _ lt Ht) -> ⟦ lb_app lb t ⟧ φ = Some (exist _ (lb++lt) H).
    Proof.
      intros H1.
      generalize (fot_sem_lb_app lb t φ); rew fot; simpl vec_map; rewrite H1.
      rewrite <- app_length; solve ite.
      intros (G & ->); do 2 f_equal; apply lt_pirr.
    Qed.

    Let fot_sem_lb_app_e lb φ (H : length lb < S n) : ⟦ lb_app lb e ⟧ φ = Some (exist _ lb H).
    Proof.
      revert H.
      rewrite (app_nil_end lb); intros H.
      rewrite <- app_nil_end at 1. 
      apply fot_sem_lb_app_Some with (Ht := lt_0_Sn _).
      rew fot; simpl; auto.
    Qed.

    Let φ : nat -> X := fun _ => None.

    Notation "⟪ A ⟫" := (fol_sem sem_sym sem_pred φ A).

    Let sem_phi_P : ⟪ phi_P ⟫.
    Proof.
      simpl; intros [ (x & Hx) | ] [ (y & Hy) | ]; simpl;
      unfold env_lift; simpl; rew fot; unfold sem_sym in |- *; simpl; try tauto.
      intros _; split; intros ?; discriminate.
    Qed.

    Let sem_phi_lt : ⟪ phi_lt ⟫.
    Proof.
      simpl; split.
      + intros [ (x & Hx) | ]; simpl; auto.
        intros ( [] & _ ); auto.
      + intros [ (x & Hx) | ] [ (y & Hy) | ] [ (z & Hz) | ]; simpl; try tauto.
        intros (H1 & H2) (H3 & H4); split.
        * intros ->.
          destruct H2 as (a & <-).
          destruct H4 as (b & H4).
          destruct b as [ | u b ].
          - destruct a as [ | v a ].
            ++ destruct H3; auto.
            ++ apply f_equal with (f := @length _) in H4.
               simpl in H4; rewrite app_length in H4; lia.
          - apply f_equal with (f := @length _) in H4.
            simpl in H4; do 2 rewrite app_length in H4; lia.
        * clear H1 H3; revert H2 H4.
          intros (a & <-) (b & <-).
          exists (b++a); rewrite app_ass; auto.
    Qed.

    Let sem_phi_eq : ⟪ phi_eq ⟫.
    Proof.
      simpl; msplit 4.
      1,2: intros [ (x & Hx) | ]; simpl; rew fot; unfold sem_sym; simpl; try discriminate;
          destruct (le_lt_dec n (length x)) as [ | ]; try discriminate.
      1,2: intros [ (x & Hx) | ] [ (y & Hy) | ]; simpl; rew fot; simpl; auto;
          try destruct (le_lt_dec n (length x)) as [ | ]; try destruct (le_lt_dec n (length y)) as [ | ];
          try discriminate; try tauto;
          inversion 2; subst; repeat f_equal; apply lt_pirr.
      intros [ (x & Hx) | ] [ (y & Hy) | ]; simpl; rew fot; simpl; auto;
          try destruct (le_lt_dec n (length x)) as [ | ]; try destruct (le_lt_dec n (length y)) as [ | ];
          try discriminate; try tauto.
    Qed.

    Opaque le_lt_dec.

    Let list_app_head_not_nil K (u v : list K) : u <> nil -> v <> u++v.
    Proof.
      intros H; contradict H.
      destruct u as [ | a u ]; auto; exfalso.
      apply f_equal with (f := @length _) in H.
      revert H; simpl; rewrite app_length; lia.
    Qed.

    Let sem_phi_simul : ⟪ phi_simul ⟫.
    Proof.
      simpl.
      intros x y.
      rewrite fol_sem_big_disj.
      revert x y.
      intros [ (x' & Hx) | ] [ (y' & Hy) | ]; simpl; rew fot; try tauto.
      intros H.
      apply pcp_hand_inv in H.
      destruct H as [ H | (x & y & p & q & H1 & H2 & -> & -> & H) ].
      + exists (lt_simul (x',y')); split.
        * apply in_map_iff; exists (x',y'); auto.
        * unfold lt_simul; simpl; left; split.
          - rew fot.
            rewrite fot_sem_lb_app_e with (H := Hx).
            simpl; auto.
          - rew fot.
            rewrite fot_sem_lb_app_e with (H := Hy).
            simpl; auto.
      + exists (lt_simul (x,y)); split.
        * apply in_map_iff; exists (x,y); split; auto.
        * unfold lt_simul; right.          
          exists (⟦lb_app p e⟧ φ), (⟦lb_app q e⟧ φ).
          assert (length p < S n) as H5 by (rewrite app_length in Hx; lia).
          assert (length q < S n) as H6 by (rewrite app_length in Hy; lia).
          rewrite fot_sem_lb_app_e with (H := H5).
          rewrite fot_sem_lb_app_e with (H := H6).
          simpl; msplit 3; auto.
          - rew fot.
            rewrite fot_sem_lb_app_Some with (lt0 := p) (Ht := H5) (H := Hx).
            ++ simpl; auto.
            ++ rew fot; simpl; auto.
          - rew fot.
            rewrite fot_sem_lb_app_Some with (lt0 := q) (Ht := H6) (H := Hy).
            ++ simpl; auto.
            ++ rew fot; simpl; auto.
          - destruct H as [ (G1 & G2) | [ (G1 & G2) | (G1 & G2) ] ].
            ++ left; split.
               ** split.
                  -- revert G1; apply list_app_head_not_nil.
                  -- exists x; auto.
               ** rew fot; simpl; subst; do 2 f_equal; apply lt_pirr.
            ++ right; left; split.
               ** split.
                  -- revert G2; apply list_app_head_not_nil.
                  -- exists y; auto.
               ** rew fot; simpl; subst; do 2 f_equal; apply lt_pirr.
            ++ do 2 right; split.
               ** split.
                  -- revert G1; apply list_app_head_not_nil.
                  -- exists x; auto.
               ** split.
                  -- revert G2; apply list_app_head_not_nil.
                  -- exists y; auto.
    Qed.

    Let sem_phi_solvable :  ⟪ ∃(𝓟 (£0) (£0)) ⟫.
    Proof.
      simpl.
      exists (Some (exist _ l (lt_n_Sn _))); simpl; auto.
    Qed.

    Theorem BPCP_sat : fo_form_fin_SAT phi_R.
    Proof.
      exists X, sem_sym, sem_pred, lX, φ; split; auto.
      unfold phi_R; repeat (split; auto).
    Qed.

  End BPCP_fin_sat.

  Check BPCP_sat.

End bpcp.





    


