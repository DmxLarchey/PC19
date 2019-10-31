(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

Require Import acc_irr.

Set Implicit Arguments.

(** First a small vector library *)

Section vec.

  Variable X : Type.

  Inductive vec : nat -> Type :=
    | vec_nil  : vec 0
    | vec_cons : forall n, X -> vec n -> vec (S n).

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

Fixpoint vec_sum n (v : vec nat n) :=
  match v with 
    | vec_nil      => 0
    | vec_cons x v => x+vec_sum v
  end.

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


  

