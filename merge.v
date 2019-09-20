(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation Arith Omega Extraction.

Require Import measure_ind list_utils perm_utils sorted.

Set Implicit Arguments.

Section merge.

  Variable (X : Type) (R : X -> X -> Prop) 
           (cmp : forall x y, { R x y } + { R y x })
           (Rtran : forall x y z, R x y -> R y z -> R x z).

  Definition merge l m : sorted R l -> sorted R m -> { k | k ~p l++m /\ sorted R k }.
  Proof.
    induction on l m as merge with measure (length l+length m); intros Hl Hm.
    refine (match l as l' return l = l' -> _ with 
      | nil   => fun El => exist _ m _
      | x::l' => fun El => 
      match m as m' return m = m' -> _ with
        | nil   => fun Em => exist _ l _
        | y::m' => fun Em => 
        match cmp x y with
          | left  H => let (k,G) := merge l' m _ _ _ in exist _ (x::k) _
          | right H => let (k,G) := merge l m' _ _ _ in exist _ (y::k) _
        end
      end eq_refl
    end eq_refl); auto.
    1-2,5 : cycle 1.

    1,2: subst; simpl; omega.

    + rewrite <- app_nil_end; subst; simpl; auto.
    + revert Hl; subst; apply sorted_inv_sorted; auto.
    + destruct G as [ G1 G2 ]; split.
      * simpl; apply perm_cons; subst; auto.
      * apply sorted_cons; auto; split; auto.
        apply perm_incl in G1.
        apply lb_incl with (1 := G1), lb_app.
        subst.
        rewrite sorted_cons in Hl; auto.
        rewrite sorted_cons in Hm; auto.
        rewrite lb_cons.
        repeat split; try tauto.
        apply proj2 in Hm.
        revert Hm; apply lb_mono; auto.
    + subst; rewrite sorted_cons in Hm; tauto.
    + destruct G as [ G1 G2 ]; split.
      * simpl.
        apply perm_trans with (1 := perm_cons _ G1); subst; simpl.
        apply perm_trans with (1 := perm_swap _ _ _), perm_cons.
        apply Permutation_middle.
      * apply sorted_cons; auto; split; auto.
        apply perm_incl in G1.
        apply lb_incl with (1 := G1), lb_app.
        subst.
        rewrite sorted_cons in Hl; auto.
        rewrite sorted_cons in Hm; auto.
        rewrite lb_cons.
        repeat split; try tauto.
        apply proj2 in Hl.
        revert Hl; apply lb_mono; auto.
  Defined.

End merge.

Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction merge.

Section rev_tail.

  Variable (X : Type).

  Fixpoint rev_tail (a l : list X) : { m | m = rev l ++ a }.
  Proof.
    refine (match l with 
      | nil   => exist _ a _
      | x::l' => let (r,Hr) := rev_tail (x::a) l' in exist _ r _
    end); auto.
    simpl; rewrite app_ass; auto.
  Defined.

End rev_tail.

Section merge_tail.

  Variable (X : Type) (R : X -> X -> Prop) 
           (cmp : forall x y, { R x y } + { R y x })
           (Rtran : forall x y z, R x y -> R y z -> R x z).

  (* let merge_tail cmp l m :=
       let rec loop a l m :=
         match l,m with
           | nil,   _     => rev_tail a m
           | _::_, nil    => rev_tail a l
           | x::l', y::m' => let (z,l1,m1) = if cmp x y then (x,l',m) else (y,l,m') 
                             in  loop (z::a) l1 m1
       in rev_tail nil (loop nil l m) *)

  Local Definition mt_loop l m :   forall a,
                   sorted R (rev a) 
                -> lu R a (l++m)
                -> sorted R l 
                -> sorted R m 
                -> { k | k ~p l++m++a /\ sorted R (rev k) }.
  Proof.
    induction on l m as loop with measure (length l+length m); intros a Ha1 Ha2 Hl Hm.
    refine (match l as l' return l = l' -> _ with 
      | nil   => fun El => let (k,Hk) := rev_tail a m in exist _ k _
      | x::l' => fun El => 
      match m as m' return m = m' -> _ with
        | nil   => fun Em =>  let (k,Hk) := rev_tail a l in exist _ k _
        | y::m' => fun Em => 
        let c := match cmp x y with
          | left  H => (x,l',m)
          | right H => (y,l,m')
        end in match c as c' return c = c' -> _ with (z,l1,m1) => fun Ec =>
                 let (k,G) := loop l1 m1 _ (z::a) _ _ _ _
                 in  exist _ k _ 
               end eq_refl
      end eq_refl
    end eq_refl); auto.
    1-3 : cycle 2.
    + unfold c in Ec.
      destruct (cmp x y); inversion  Ec; subst; simpl; omega.
    + split; subst k; simpl.
      * apply Permutation_app; auto.
        apply Permutation_sym, Permutation_rev.
      * rewrite rev_app_distr, rev_involutive.
        apply sorted_app; auto.
        repeat split; auto.
        apply Forall_rev; subst; auto.
    + split.
      * rewrite Hk, <- El; simpl.
        apply Permutation_app; auto.
        apply Permutation_sym, Permutation_rev.
      * rewrite Hk, rev_app_distr, rev_involutive.
        apply sorted_app; auto.
        repeat split; auto.
        subst m; rewrite <- app_nil_end in Ha2.
        apply Forall_rev; auto.
    + unfold c in Ec.
      destruct (cmp x y); inversion  Ec; subst z l1 m1; simpl; 
        apply sorted_app; auto; repeat split; auto.
      * apply Forall_rev, lu_spec.
        rewrite lu_spec, El in Ha2.
        intros u v Hu [ Hv | [] ]; subst v.
        apply Ha2; simpl; auto.
      * apply Forall_rev, lu_spec.
        rewrite lu_spec, Em in Ha2.
        intros u v Hu [ Hv | [] ]; subst v.
        apply Ha2; simpl; auto.
        apply in_or_app; right; simpl; auto.
    + unfold c in Ec.
      destruct (cmp x y); inversion  Ec; subst z l1 m1; simpl; auto.
      * apply lu_cons_l.
        - revert Ha2; apply lu_incl; auto.
          ++ apply incl_refl.
          ++ rewrite El; simpl; apply incl_tl, incl_refl.
        - rewrite Em, sorted_cons in Hm; auto.
          destruct Hm as [ Hm1 Hm2 ].
          rewrite El, sorted_cons in Hl; auto.
          destruct Hl as [ Hl1 Hl2 ].
          apply lb_app; split; auto.
          rewrite Em; apply lb_cons; split; auto.
          revert Hm2; apply lb_mono; auto.
      * apply lu_cons_l.
        - revert Ha2; apply lu_incl; auto.
          ++ apply incl_refl.
          ++ rewrite Em; simpl.
             apply incl_app.
             ** apply incl_appl, incl_refl.
             ** apply incl_appr, incl_tl, incl_refl.
        - rewrite Em, sorted_cons in Hm; auto.
          destruct Hm as [ Hm1 Hm2 ].
          rewrite El, sorted_cons in Hl; auto.
          destruct Hl as [ Hl1 Hl2 ].
          apply lb_app; split; auto.
          rewrite El; apply lb_cons; split; auto.
          revert Hl2; apply lb_mono; auto.
    + unfold c in Ec.
      destruct (cmp x y); inversion  Ec; subst z l1 m1; simpl; auto.
      subst l; apply sorted_cons in Hl; tauto.
    + unfold c in Ec.
      destruct (cmp x y); inversion  Ec; subst z l1 m1; simpl; auto.
      subst m; apply sorted_cons in Hm; tauto.
    + destruct G as [ G1 G2 ]; split; auto.
      unfold c in Ec.
      destruct (cmp x y); inversion  Ec; subst z l1 m1; simpl.
      * apply perm_trans with (1 := G1), Permutation_sym.
        rewrite (app_assoc l' m), Em.
        apply perm_trans with (2 := perm_middle _ _ _).
        repeat rewrite app_ass; auto.
      * apply perm_trans with (1 := G1), Permutation_sym.
        rewrite El; simpl.
        apply perm_cons, Permutation_app; auto.
  Qed.

  Extraction Inline mt_loop.

  Definition merge_tail l m : sorted R l -> sorted R m -> { k | k ~p l++m /\ sorted R k }.
  Proof.
    intros Hl Hm.
    refine (let (k,Hk) := @mt_loop _ _ nil _ _ Hl Hm in 
            let (r,Hr) := rev_tail nil k 
            in   exist _ r _).
    + simpl; auto.
    + apply lu_nil_l.
    + rewrite <- app_nil_end in *.
      subst.
      destruct Hk as [ Hk ? ]; split; auto.
      apply perm_trans with (2 := Hk), perm_sym.
      apply Permutation_rev.
  Defined.

End merge_tail.

Extract Inductive sumbool => "bool" [ "true" "false" ].

Recursive Extraction merge_tail.
