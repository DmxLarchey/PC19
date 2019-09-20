(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith List.

Require Import list_utils perm_utils.

Set Implicit Arguments.

Section sorted.

  Variable (X : Type) (R : X -> X -> Prop)
           (Rtran : forall x y z, R x y -> R y z -> R x z).

  (* ub l x means that every element in l is lower than x *)

  Definition ub l x := Forall (fun y => R y x) l.

  Fact ub_mono l x y : R x y -> ub l x -> ub l y.
  Proof.
    unfold ub; do 2 rewrite Forall_forall.
    intros H ? ? ?; apply Rtran with (2 := H); auto.
  Qed.

  Fact ub_nil x : ub nil x.
  Proof. constructor. Qed.

  Fact ub_incl l l' x : incl l l' -> ub l' x -> ub l x.
  Proof.
    unfold ub; do 2 rewrite Forall_forall; unfold incl; firstorder.
  Qed.

  Fact ub_cons x l y : ub (x::l) y <-> R x y /\ ub l y.
  Proof. apply Forall_cons_inv. Qed.

  Fact ub_app l1 l2 x : ub (l1++l2) x <-> ub l1 x /\ ub l2 x.
  Proof. apply Forall_app_inv. Qed.

  (* lower bound : every element in l is greater than x *)

  Definition lb m x := Forall (R x) m.

  Fact lb_mono m x y : R x y -> lb m y -> lb m x.
  Proof.
    unfold lb; do 2 rewrite Forall_forall.
    intros H ? ? ?; apply Rtran with (1 := H); auto.
  Qed.

  Fact lb_nil x : lb nil x.
  Proof. constructor. Qed.

  Fact lb_incl l l' x : incl l l' -> lb l' x -> lb l x.
  Proof.
    unfold lb; do 2 rewrite Forall_forall; unfold incl; firstorder.
  Qed.

  Fact lb_cons x l y : lb (x::l) y <-> R y x /\ lb l y.
  Proof. apply Forall_cons_inv. Qed.

  Fact lb_app l1 l2 x : lb (l1++l2) x <-> lb l1 x /\ lb l2 x.
  Proof. apply Forall_app_inv. Qed.

  Definition lu l m := Forall (lb m) l.

  Fact lu_spec l m : lu l m  <-> forall x y, In x l -> In y m -> R x y.
  Proof.
    unfold lu, lb.
    rewrite Forall_forall.
    split.
    + intros H x y Hx; revert y.
      rewrite <- Forall_forall; auto.
    + intros H ? ?; rewrite Forall_forall; auto.
  Qed.

  Fact lu_middle l x m : ub l x -> lb m x -> lu l m.
  Proof.
    unfold ub, lb; do 2 rewrite Forall_forall; rewrite lu_spec.
    intros; apply Rtran with x; auto.
  Qed. 

  Fact lu_In l l' x m : In x m -> incl l l' -> lu l' m -> ub l x.
  Proof.
    unfold incl, ub; rewrite lu_spec, Forall_forall; firstorder.
  Qed. 

  Fact lu_incl l l' m m' : incl l l'
                        -> incl m m' 
                        -> lu l' m' 
                        -> lu l m.
  Proof.
    do 2 rewrite lu_spec; unfold incl; firstorder.
  Qed.

  Fact lu_nil_l l : lu nil l.
  Proof. apply lu_spec; intros ? ? []. Qed.

  Fact lu_nil_l_inv l : lu nil l <-> True.
  Proof. split; auto; intro; apply lu_nil_l. Qed.

  Fact lu_nil_r l : lu l nil.
  Proof. apply lu_spec; intros ? ? _ []. Qed.

  Hint Immediate lu_nil_l lu_nil_r.

  Fact lu_app_l l1 l2 r : lu (l1++l2) r <-> lu l1 r /\ lu l2 r.
  Proof. apply Forall_app_inv. Qed.

  Fact lu_app_r l r1 r2 : lu l (r1++r2) <-> lu l r1 /\ lu l r2.
  Proof. 
    do 3 rewrite lu_spec; split.
    + intros H; split; intros ? ? ? ?; apply H; auto; apply In_app_inv; auto.
    + intros (H1 & H2) x y; rewrite In_app_inv; firstorder.
  Qed.

  Fact lu_cons_r l x r : lu l r -> ub l x -> lu l (x::r).
  Proof.
    unfold ub; rewrite lu_spec, lu_spec, Forall_forall; simpl; firstorder.
    subst; auto.
  Qed.

  Fact lu_cons r l x : lu (x::l) r <-> lb r x /\ lu l r.
  Proof. apply Forall_cons_inv. Qed.

  Fact lu_cons_l x l r : lu l r -> lb r x -> lu (x::l) r.
  Proof. rewrite lu_cons; tauto. Qed.

  Fact lu_cons_lr x y : R x y -> lu (x::nil) (y::nil).
  Proof.
    intros; apply lu_cons_r; repeat constructor; auto.
  Qed.

  Hint Resolve lu_cons_l lu_cons_r lu_cons_lr. 

  Fact lu_xchg l1 l2 m : lu (l1++m) l2 -> lu l1 m -> lu l1 (m++l2).
  Proof.
    rewrite lu_app_l, lu_app_r.
    intros (?&?); split; auto.
  Qed.

  Fact lu_insert x m l1 l2 : lu (m++x::nil) (l1++l2)
                          -> ub m x 
                          -> lu m (l1++x::l2).
  Proof.
    intros H1 H2.
    apply lu_incl with (l' := m) (m' := (x::nil)++l1++l2).
    + red; auto.
    + intro; simpl; repeat rewrite In_app_inv; simpl; tauto.
    + apply lu_xchg; auto.
  Qed.

  (* ll is sorted iff whenever it is split into l++r, the elements of l are lower than those of r *)

  Definition sorted ll := forall l r, ll = l++r -> lu l r.

  Proposition sorted_nil : sorted nil.
  Proof. intros [|] [|]; try discriminate 1; constructor. Qed.

  Proposition sorted_one x : sorted (x::nil).
  Proof. intros [|? []] [] H; try discriminate H; auto. Qed.

  Hint Resolve sorted_nil sorted_one.

  Fact sorted_nil_inv : sorted nil <-> True.
  Proof. split; auto. Qed.

  Fact sorted_one_inv x : sorted (x::nil) <-> True.
  Proof. split; auto. Qed.

  Section sorted_app.

    Let sorted_app_1 l r : sorted (l++r) -> sorted l /\ sorted r /\ lu l r. 
    Proof.
      unfold sorted.
      intros H; split; [ | split ]; auto.
      + intros l1 l2 ?; subst.
        specialize (H l1 (l2++r)).
        rewrite lu_app_r in H; apply H.
        rewrite app_ass; auto.
      + intros r1 r2 ?; subst.
        specialize (H (l++r1) r2).
        rewrite lu_app_l in H; apply H.
        rewrite app_ass; auto.
    Qed.

    Let sorted_app_2 l r : sorted l /\ sorted r /\ lu l r -> sorted (l++r). 
    Proof.
      intros (H1 & H2 & H3) l1 r1 H.
      apply app_split in H;
      destruct H as [ (m & M1 & M2) 
                    | (m & M1 & M2) ]; subst.
      + rewrite lu_app_r in H3.
        apply sorted_app_1 in H2.
        apply lu_app_l; tauto.
      + apply lu_xchg; auto.
    Qed.

    Fact sorted_app l r : sorted (l++r) <-> sorted l /\ sorted r /\ lu l r.
    Proof. split; auto. Qed.

  End sorted_app.

  Proposition sorted_cons x l : sorted (x::l) <-> sorted l /\ lb l x.
  Proof.
    cutrewrite (x::l = (x::nil)++l); auto.
    rewrite sorted_app, sorted_one_inv, lu_cons, lu_nil_l_inv; tauto.
  Qed.

  Hint Resolve sorted_nil sorted_one sorted_cons.

  Proposition sorted_inv_lb x l : sorted (x::l) -> lb l x.
  Proof. rewrite sorted_cons; tauto. Qed.

  Proposition sorted_inv_sorted x l : sorted (x::l) -> sorted l.
  Proof. rewrite sorted_cons; tauto. Qed.

  Hint Resolve sorted_inv_sorted sorted_inv_lb.

  Theorem quick_sorted l x m : 
      sorted l -> ub l x -> lb m x -> sorted m -> sorted (l++x::m).
  Proof.
    intros.
    apply sorted_app; repeat split; auto.
    apply sorted_cons; split; auto.
    apply lu_cons_r; auto.
    apply lu_middle with (x := x); auto.
  Qed.

  Section merge.

    Let merge_perm_1 (x y : nat) l m k : k ~p l++y::m -> x::k ~p x::l++y::m.
    Proof. intro; auto. Qed.

    Let merge_perm_2 (x y : nat) l m k : k ~p x::l++m -> y::k ~p x::l++y::m.
    Proof.
      intros H. 
      apply perm_special with (l := x::l),
            perm_trans with (1 := H), perm_refl. 
    Qed.

    Theorem merge_sorted x y l m k : R x y 
                              -> sorted (x::l) 
                              -> sorted (y::m) 
                              -> sorted k 
                              -> k ~p l++y::m 
                              -> sorted (x::k).
    Proof.
      intros H1 H2 H3 H4 H5.
      apply sorted_cons; split; auto.
      apply lb_incl with (l++y::m).
      * apply perm_incl; auto.
      * rewrite lb_app.
        apply sorted_inv_lb in H2.
        apply sorted_inv_lb in H3.
        split; auto.
        apply lb_cons; split; auto.
        revert H3; apply lb_mono; auto.
    Qed.

  End merge.

End sorted.

Hint Immediate lu_nil_l lu_nil_r ub_nil lb_nil.
Hint Resolve lu_cons_l lu_cons_r lu_cons_lr
             sorted_nil sorted_one sorted_cons
             sorted_inv_sorted sorted_inv_lb.

Section sorting_algo.

  Variable (X : Type) (R : X -> X -> Prop) (f : list X -> list X).
  
  Definition sorting_algo := forall l, l ~p f l /\ sorted R (f l).

End sorting_algo.

