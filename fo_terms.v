(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Eqdep_dec Lia Bool.

Require Import acc_irr measure_ind wf_finite.

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
  Definition finite X := exists lX, forall x : X, In x lX.

  Fact finite_t_finite X : finite_t X -> finite X.
  Proof. intros (l & ?); exists l; auto. Qed.

  Definition fin_t X (P : X -> Prop) := { l | forall x, P x <-> In x l }.
  Definition fin X (P : X -> Prop) := exists l, forall x, P x <-> In x l.

  Fact fin_t_fin X P : @fin_t X P -> fin P.
  Proof. intros (l & ?); exists l; auto. Qed.

  Fact finite_t_fin_t_eq X : (finite_t X -> fin_t (fun _ : X => True))
                           * (fin_t (fun _ : X => True) -> finite_t X).
  Proof.
    split; intros (l & ?); exists l; firstorder.
  Qed.

  Fact fin_t_map X Y (f : X -> Y) (P Q : _ -> Prop) : 
             (forall y, Q y <-> exists x, f x = y /\ P x)
          -> @fin_t X P
          -> @fin_t Y Q.
  Proof.
    intros H (lP & HP).
    exists (map f lP).
    intros x; rewrite in_map_iff, H.
    firstorder.
  Qed.

  Fixpoint list_prod X Y (l : list X) (m : list Y) :=
    match l with
      | nil  => nil
      | x::l => map (fun y => (x,y)) m ++ list_prod l m
    end.

  Fact list_prod_spec X Y l m c : In c (@list_prod X Y l m) <-> In (fst c) l /\ In (snd c) m.
  Proof.
    revert c; induction l as [ | x l IHl ]; intros c; simpl; try tauto.
    rewrite in_app_iff, IHl, in_map_iff; simpl.
    split.
    + intros [ (y & <- & ?) | (? & ?) ]; simpl; auto.
    + intros ([ -> | ] & ? ); destruct c; simpl; firstorder.
  Qed.

  Fact fin_t_prod X Y (P Q : _ -> Prop) : 
         @fin_t X P -> @fin_t Y Q -> fin_t (fun c => P (fst c) /\ Q (snd c)).
  Proof.
    intros (l & Hl) (m & Hm).
    exists (list_prod l m); intro; rewrite list_prod_spec, Hl, Hm; tauto.
  Qed.

  Fact finite_prod X Y : finite X -> finite Y -> finite (X*Y).
  Proof.
    intros (l & Hl) (m & Hm); exists (list_prod l m).
    intros []; apply list_prod_spec; auto.
  Qed.

  Fact fin_t_sum X Y (P Q : _ -> Prop) :
         @fin_t X P -> @fin_t Y Q -> fin_t (fun z : X + Y => match z with inl x => P x | inr y => Q y end).
  Proof.
    intros (l & Hl) (m & Hm).
    exists (map inl l ++ map inr m).
    intros z; rewrite in_app_iff, in_map_iff, in_map_iff.
    destruct z as [ x | y ]; [ rewrite Hl | rewrite Hm ].
    + split.
      * left; exists x; auto.
      * intros [ (z & E & ?) | (z & C & _) ]; try discriminate; inversion E; subst; auto.
    + split.
      * right; exists y; auto.
      * intros [ (z & C & _) | (z & E & ?) ]; try discriminate; inversion E; subst; auto.
  Qed.

  Fact finite_t_unit : finite_t unit.
  Proof. exists (tt::nil); intros []; simpl; auto. Qed.

  Fact finite_t_bool : finite_t bool.
  Proof. exists (true::false::nil); intros []; simpl; auto. Qed.

  Theorem fin_t_length X n : finite_t X -> fin_t (fun l => @length X l < n).
  Proof.
    intros HX.
    apply finite_t_fin_t_eq in HX.
    generalize finite_t_unit; intros H1.
    apply finite_t_fin_t_eq in H1.
    induction n as [ | n IHn ].
    + exists nil; intros; split; try lia; intros [].
    + generalize (fin_t_sum H1 (fin_t_prod HX IHn)).
      apply fin_t_map with (f := fun c => match c with
        | inl _     => nil
        | inr (x,l) => x::l
      end).
      intros [ | x l ]; simpl.
      * split; try lia; exists (inl tt); auto.
      * split.
        - intros Hl; exists (inr (x,l)); simpl; msplit 2; auto; lia.
        - intros ([ [] | (y,m) ] & E & H); try discriminate.
          simpl in *; inversion E; subst; lia.
  Qed.

  Theorem finite_t_list X n : finite_t X -> finite_t { l : list X | length l < n }.
  Proof.
    intros H; apply (fin_t_length n) in H; revert H; intros (l & Hl).
    assert (forall x, In x l -> length x < n) as f by (intro; apply Hl).
    set (g x Hx := exist (fun x => length x < n) x (f x Hx)).
    exists (list_in_map l g).
    intros (x & Hx).
    assert (G : In x l) by (revert Hx; apply Hl).
    assert (E : Hx = f _ G) by apply lt_pirr.
    subst Hx; apply In_list_in_map with (f := g).
  Qed.

  Theorem finite_t_option X : finite_t X -> finite_t (option X).
  Proof.
    intros (lX & HX).
    exists (None :: map Some lX).
    intros [x|]; simpl; auto.
    right; apply in_map_iff; exists x; auto.
  Qed.

  Section dec.

    Variable (X : Type) (P : X -> Prop) (Pdec : forall x, { P x } + { ~ P x }).
    
    Theorem fin_t_dec Q : @fin_t X Q -> fin_t (fun x => P x /\ Q x).
    Proof.
      intros (l & Hl).
      exists (filter (fun x => if Pdec x then true else false) l).
      intros x; rewrite filter_In, <- Hl.
      destruct (Pdec x); try tauto.
      split; try tauto.
      intros []; discriminate.
    Qed.

  End dec.

  Section list_reif.

    Variable (X Y : Type) (eqX_dec : forall x y : X, { x = y } + { x <> y })
             (R : X -> Y -> Prop).
    
    Theorem list_reif (l : list X) :
            (forall x, In x l -> exists y, R x y)
         -> exists f, forall x (Hx : In x l), R x (f x Hx).
    Proof.
      induction l as [ | x l IHl ]; intros Hl.
      + exists (fun x (Hx : @In X x nil) => False_rect Y Hx).
        intros _ [].
      + destruct (Hl x) as (y & Hy); simpl; auto.
        destruct IHl as (f & Hf).
        * intros; apply Hl; simpl; auto.
        * assert (forall z, In z (x::l) -> x <> z -> In z l) as H1.
          { intros z [ -> | ] ?; tauto. }
          exists (fun z Hz => 
            match eqX_dec x z with
              | left   _ => y
              | right  H => f z (H1 _ Hz H)
            end).
          intros z Hz.
          destruct (eqX_dec x z); subst; auto.
    Qed.  
 
  End list_reif.

  (** Will be useful to reify total relations into actual functions
      over finite and discrete domains *)

  Theorem finite_reif X Y R : (forall x y : X, { x = y } + { x <> y })
                           -> finite X
                           -> (forall x : X, exists y : Y, R x y)
                           -> exists f, forall x, R x (f x).
  Proof.
    intros H1 (l & H2) H3.
    destruct list_reif with (1 := H1) (R := R) (l := l)
      as (f & Hf).
    + intros; auto.
    + exists (fun x => f x (H2 x)).
      intros; auto.
  Qed.

End finite.

Section dec.

  Variable (X : Type).

  Theorem exists_dec_fin_t 
           (P Q : X -> Prop) 
           (Pdec : forall x, { P x } + { ~ P x }) 
           (HQ : fin_t Q)
           (HPQ : forall x, P x -> Q x) :
           { exists x, P x } + { ~ exists x, P x }.
  Proof.
    generalize (fin_t_dec _ Pdec HQ); intros ([ | x l ] & Hl).
    + right; intros (x & Hx); apply (Hl x); split; auto.
    + left; exists x; apply Hl; simpl; auto.
  Qed.

  Variable (eqX_dec : forall x y : X, { x = y } + { x <> y }).

  Fact is_a_head_dec (l t : list X) : { x | l = t++x } + { ~ exists x, l = t++x }.
  Proof.
    revert t.
    induction l as [ | a l IHl ].
    + intros [ | t ]. 
      * left; exists nil; auto.
      * right; intros ([ | ] & ?); discriminate.
    + intros [ | b t ].
      * left; exists (a::l); auto.
      * destruct (eqX_dec a b) as [ -> | C ].
        - destruct (IHl t) as [ H | C ].
          ++ left; destruct H as (x & ->).
              exists x; auto.
          ++ right; contradict C; destruct C as (x & E).
             exists x; inversion E; subst; auto.
        - right; contradict C; destruct C as (? & E); inversion E; auto.
  Qed.
 
  Fact is_a_tail_dec (l t : list X) : { exists x, x++t = l } + { ~ exists x, x++t = l }.
  Proof.
    destruct (is_a_head_dec (rev l) (rev t)) as [ H | H ].
    + left; destruct H as (x & Hx).
      exists (rev x).
      apply f_equal with (f := @rev _) in Hx.
      rewrite rev_app_distr in Hx.
      do 2 rewrite rev_involutive in Hx; auto.
    + right; contradict H.
      destruct H as (x & Hx); exists (rev x); subst.
      apply rev_app_distr.
  Qed.

End dec.

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

  Section pcp_induction.

    Implicit Type (l m : list X).

    (** Notice that we could downgrade strict_suffix to Prop because
        a and b could be computed from the knowledge of there existence *)

    Definition strict_suffix x y l m := { a : _ & { b | (a <> nil \/ b <> nil) /\ l = a++x /\ m = b++y } }.
    
    Variable (P : list X -> list X -> Type)
             (IHP : forall l m, (forall l' m', strict_suffix l' m' l m -> P l' m') -> P l m).

    Theorem pcp_induction l m : P l m.
    Proof.
      induction on l m as IH with measure (length l + length m).
      apply IHP.
      intros l' m' (x & y & H & -> & ->).
      apply IH.
      do 2 rewrite app_length.
      destruct x; destruct y; simpl; try lia.
      destruct H as [ [] | [] ]; auto.
    Qed.

  End pcp_induction.
    
  Section bounded_dec.

    (** It is possible to decide pcp_hand, when equality is decidable
        of course *)
  
    Variable eqX_dec : forall x y : X, { x = y } + { x <> y }.

    Let eqlX_dec : forall l m : list X, { l = m } + { l <> m }.
    Proof. apply list_eq_dec; auto. Qed.

    Let eqXX_dec : forall p q : list X * list X, { p = q } + { p <> q }.
    Proof. decide equality; auto. Qed.

    (** Replaced induction on length p + length with strict suffix pair induction *)

    Theorem pcp_hand_dec p q : { pcp_hand p q } + { ~ pcp_hand p q }.
    Proof.
      revert p q; apply pcp_induction; intros p q dec.

      set (P (c : list X * list X) := let (x,y) := c 
           in exists d, p = x++fst d /\ q = y++snd d /\ pcp_hand (fst d) (snd d) /\ (x <> nil \/ y <> nil)).
      assert (forall c, { P c } + { ~ P c }) as Pdec.
      { intros (x,y); simpl.
        assert ( { x = nil /\ y = nil } + { x <> nil \/ y <> nil } ) as H.
        1: { destruct (eqlX_dec x nil); destruct (eqlX_dec y nil); tauto. }
        destruct H as [ (H1 & H2) | Hxy ].
        1: { right; intros ((? & ?) & ?); tauto. }
        destruct (is_a_head_dec eqX_dec p x) as [ (p' & Hp') | Hp ].
        2: { right; contradict Hp; revert Hp. 
             intros ((p',?) & E & _); exists p'; auto. }
        destruct (is_a_head_dec eqX_dec q y) as [ (q' & Hq') | Hq ].
        2: { right; contradict Hq; revert Hq. 
             intros ((?,q') & _ & E & _); exists q'; auto. }
        destruct (dec p' q') as [ H' | H' ].
        + exists x, y; auto.
        + left; exists (p',q'); auto.
        + right; contradict H'; revert H'.
          intros ((u,v) & -> & -> & C & _); simpl in *.
          apply app_inv_head in Hp'.
          apply app_inv_head in Hq'.
          subst; auto. }

      destruct list_dec with (1 := Pdec) (l := lc)
        as [ ((x,y) & H1 & H) | H ]; unfold P in H.
      + left.
        destruct H as ((p',q') & -> & -> & H & _); simpl in *.
        constructor 2; auto.
      + destruct In_dec with (1 := eqXX_dec) (a := (p,q)) (l := lc)
          as [ H2 | H2 ].
        * left; constructor 1; auto.
        * right; contradict H2.
          apply pcp_hand_inv in H2.
          destruct H2 as [ | (x & y & p' & q' & H2 & H3 & -> & -> & H4) ]; auto.
          destruct H with (1 := H2).
          exists (p', q'); msplit 3; tauto.
    Qed.

  End bounded_dec.

End pcp_hand.

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

    Fact fot_sem_ext t φ ψ : (forall n, In n (fo_term_vars t) -> φ n = ψ n) 
                           -> ⟦t⟧ φ = ⟦t⟧ ψ.
    Proof.
      revert φ ψ; induction t as [ n | s v IHv ]; intros phi psy H; rew fot.
      + apply H; simpl; auto.
      + f_equal; apply vec_map_ext.
        intros x Hx; apply IHv; auto.
        intros n Hn; apply H; rew fot.
        apply in_flat_map. 
        exists x; split; auto.
        apply in_vec_list; auto.
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

      (** REMARK: not requiring the sem_pred relation to be decidable
          would allow hiding uncomputability inside the model which
          would be kind of cheating. The semantic relation should be
          decidable, only the (finite) satisfiability relation should 
          be undec *)

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

  Fact lb_app_app l m t : lb_app (l++m) t = lb_app l (lb_app m t).
  Proof. induction l; simpl; auto; do 2 f_equal; auto. Qed.

  Fact fot_vars_lb_app l t : fo_term_vars (lb_app l t) = fo_term_vars t.
  Proof.
    induction l as [ | x l IHl ]; simpl; rew fot; auto.
    simpl; rewrite <- app_nil_end; auto.
  Qed.

  Notation lb2term := (fun l => lb_app l e).

  Definition phi_P := ∀ (∀ (𝓟  (£1) (£0) ⤑ ¬ (£1 ≡ ∗) ⟑ ¬ (£0 ≡ ∗))).

  Definition lt_irrefl := ∀ (¬ (£0 ≺ £0)).
  Definition lt_trans := ∀(∀(∀(£2 ≺ £1 ⤑ £1 ≺ £0 ⤑ £2 ≺ £0))).
  Definition phi_lt := lt_irrefl ⟑ lt_trans.

  Definition eq_neq (b : bool) := ∀(¬(f_ b (£0) ≡ e)).
  Definition eq_inj (b : bool) := ∀(∀( ¬(f_ b (£1) ≡ ∗) ⤑ f_ b (£1) ≡ f_ b (£0) ⤑ £1 ≡ £0)).
  Definition eq_real := ∀(∀(f_ true (£1) ≡ f_ false (£0) ⤑ f_ true (£1) ≡ ∗
                                                         ⟑ f_ false (£0) ≡ ∗)).
  Definition eq_undef b := f_ b ∗ ≡ ∗.  (* Dominik forgot that one in his draft *)

  Definition phi_eq := eq_neq true ⟑ eq_neq false 
                     ⟑ eq_inj true ⟑ eq_inj false 
                     ⟑ eq_undef true ⟑ eq_undef false
                     ⟑ eq_real.

  Definition eq_equiv := (∀(£0 ≡ £0)) 
                       ⟑ (∀(∀(£0 ≡ £1 ⤑ £1 ≡ £0)))
                       ⟑ (∀(∀(∀(£0 ≡ £1 ⤑ £1 ≡ £2 ⤑ £0 ≡ £2)))).
 
  Definition eq_congr_f b := ∀(∀(£0 ≡ £1 ⤑ f_ b (£0) ≡ f_ b (£1))).
  Definition eq_congr_pred p := ∀(∀(∀(∀(£0 ≡ £1 ⤑ £2 ≡ £3 ⤑ fol_atom a_pred p (£0##£2##ø)
                                                                                                                    ⤑ fol_atom a_pred p (£1##£3##ø))))).

  Definition eq_congr := eq_congr_f true 
                       ⟑ eq_congr_f false
                       ⟑ eq_congr_pred p_P
                       ⟑ eq_congr_pred p_lt
                       ⟑ eq_equiv.

  Definition lt_pair (u v x y : term) := (u ≺ x ⟑ v ≡ y) ⟇ (v ≺ y ⟑ u ≡ x) ⟇ (u ≺ x ⟑ v ≺ y).

  Definition lt_simul (c : list bool * list bool) := 
    let (s,t) := c 
    in   (£1 ≡ lb2term s ⟑ £0 ≡ lb2term t)
       ⟇ ∃(∃(𝓟 (£1) (£0) ⟑ £3 ≡ lb_app s (£1) ⟑ £2 ≡ lb_app t (£0) ⟑ lt_pair (£1) (£0) (£3) (£2) )).

  Definition phi_simul := ∀(∀(𝓟 (£1) (£0) ⤑ fol_big_disj (map lt_simul lc))).

  Definition phi_R := phi_P ⟑ phi_lt ⟑ phi_eq 
                    ⟑ phi_simul ⟑ eq_congr
                    ⟑ ∃(𝓟 (£0) (£0)).

  Section BPCP_fin_sat.

    (** This model is decidable because pcp_hand is decidable *)

    Variable (l : list bool) (Hl : pcp_hand lc l l). 

    Let n := length l.

    Let X := option { m : list bool | length m < S n }.
    Let fin_X : finite_t X.
    Proof. apply finite_t_option, finite_t_list, finite_t_bool. Qed.

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

    (** This model has decidable sem_pred *)

    Let sem_pred_dec : forall p v, { @sem_pred p v } + { ~ sem_pred v }.
    Proof.
      intros []; simpl; intros v; vec split v with x; vec split v with y; vec nil v; clear v; simpl;
        revert x y; intros [ (x & Hx) | ] [ (y & Hy) | ]; simpl; try tauto.
      + apply pcp_hand_dec, bool_dec.
      + destruct (list_eq_dec bool_dec x y);
        destruct (is_a_tail_dec bool_dec y x); tauto.
      + destruct (list_eq_dec bool_dec x y) as [ | C ]; [ left | right ].
        * subst; repeat f_equal; apply lt_pirr.
        * contradict C; inversion C; auto.
      + right; discriminate.
      + right; discriminate.
    Qed.

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

    Notation "⟪ A ⟫" := (fun φ => fol_sem sem_sym sem_pred φ A).

    Let sem_fol_dec A φ : { ⟪A⟫ φ } + { ~ ⟪A⟫ φ }.
    Proof.
      apply fol_sem_dec with (lX := lX); auto.
    Qed.

    Let φ : nat -> X := fun _ => None.

    Let sem_phi_P : ⟪ phi_P ⟫ φ.
    Proof.
      simpl; intros [ (x & Hx) | ] [ (y & Hy) | ]; simpl;
      unfold env_lift; simpl; rew fot; unfold sem_sym in |- *; simpl; try tauto.
      intros _; split; intros ?; discriminate.
    Qed.

    Let sem_phi_lt : ⟪ phi_lt ⟫ φ.
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

    Let sem_phi_eq : ⟪ phi_eq ⟫ φ.
    Proof.
      simpl; msplit 6.
      1,2: intros [ (x & Hx) | ]; simpl; rew fot; unfold sem_sym; simpl; try discriminate;
          destruct (le_lt_dec n (length x)) as [ | ]; try discriminate.
      1,2: intros [ (x & Hx) | ] [ (y & Hy) | ]; simpl; rew fot; simpl; auto;
          try destruct (le_lt_dec n (length x)) as [ | ]; try destruct (le_lt_dec n (length y)) as [ | ];
          try discriminate; try tauto;
          inversion 2; subst; repeat f_equal; apply lt_pirr.
      1,2: rew fot; simpl; auto.
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

    Let sem_phi_simul : ⟪ phi_simul ⟫ φ.
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

    Tactic Notation "solve" "congr" int(a) int(b) :=
      do a intros [(?&?)|]; simpl; rew fot; simpl; auto; try discriminate; do b inversion 1; auto.

    Let sem_eq_congr : ⟪ eq_congr ⟫ φ.
    Proof.
      msplit 6; simpl; auto.
      + solve congr 2 1.
      + solve congr 2 1.
      + solve congr 4 2.
      + solve congr 4 2.
      + solve congr 3 0; intros H1 H2; rewrite H1; auto.
    Qed.

    Let sem_phi_solvable : ⟪ ∃(𝓟 (£0) (£0)) ⟫ φ.
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

  Section fin_sat_BPCP.

    Variable (X : Type)
             (HX : finite X)
             (sem_sym  : forall s, vec X (a_sym s) -> X)
             (sem_pred : forall s, vec X (a_pred s) -> Prop).

    Notation "⟦ t ⟧" := (fun φ => fot_sem sem_sym φ t).
    Notation "⟪ A ⟫" := (fun φ => fol_sem sem_sym sem_pred φ A).

    Fact fot_sem_lb_app l t φ : ⟦ lb_app l t ⟧ φ = ⟦ lb_app l (£0) ⟧ (φ ↑ (⟦t⟧φ)).
    Proof.
      revert φ; induction l as [ | b l IHl ]; intros phi; simpl.
      + unfold env_lift; rew fot; auto.
      + rew fot; f_equal; simpl; f_equal; auto.
    Qed.

    Variable (φ : nat -> X) (model : ⟪ phi_R ⟫ φ).

    Notation ε := (@sem_sym fe ø).
    Notation "⋇" := (@sem_sym fs ø).
    Let f b x := (@sem_sym (fb b) (x##ø)).

    Let P x y := @sem_pred p_P (x##y##ø).
    Notation "x ⪡ y" := (@sem_pred p_lt (x##y##ø)) (at level 70).
    Notation "x ≋ y" := (@sem_pred p_eq (x##y##ø)) (at level 70).

    Let lt_pair u v x y    := (  u ⪡ x /\ v ≋ y
                                \/ v ⪡ y /\ u ≋ x
                                \/ u ⪡ x /\ v ⪡ y ).

    (** The axiom interpreted directly gives us properties of the model *)

    Let HP x y : P x y -> ~ x ≋ ⋇ /\ ~ y ≋ ⋇.
    Proof. apply model. Qed.

    Let Hfb_1 b x : ~ f b x ≋ ε.
    Proof. destruct b; apply model. Qed.

    Let Hfb_2 b x y : ~ f b x ≋ ⋇ -> f b x ≋ f b y -> x ≋ y.
    Proof. destruct b; revert x y; apply model. Qed.

    Let Hfb_3 x y : f true x ≋ f false y -> f true x ≋ ⋇ /\ f false y ≋ ⋇.
    Proof. apply model. Qed.

    Let Hfb_4 b : f b ⋇ ≋ ⋇.
    Proof. 
      destruct model as (_ & _ & H & _).
      destruct H as (_ & _ & _ & _ & H1 & H2 & _ ).
      destruct b; auto.
    Qed.

    Let Hlt_irrefl x : ~ x ⪡ x.
    Proof. apply model. Qed.
  
    Let Hlt_trans x y z : x ⪡ y -> y ⪡ z -> x ⪡ z.
    Proof. apply model. Qed.

    Let Heq_refl x : x ≋ x.
    Proof. revert x; apply model. Qed.
  
    Let Heq_sym x y : x ≋ y -> y ≋ x.
    Proof. apply model. Qed.

    Let Heq_trans x y z : x ≋ y -> y ≋ z -> x ≋ z.
    Proof. apply model. Qed.

    Let Heq_congr_1 b x y : x ≋ y -> f b x ≋ f b y.
    Proof. destruct b; apply model. Qed.

    Let Heq_congr_2 x y x' y' : x ≋ x' -> y ≋ y' -> P x y -> P x' y'.
    Proof. apply model. Qed.

    Let Heq_congr_3 x y x' y' : x ≋ x' -> y ≋ y' -> x ⪡ y -> x' ⪡ y'.
    Proof. apply model. Qed.
   
    Let sb_app l x := ⟦ lb_app l (£0) ⟧ (φ↑x).

    Let Hsimul x y : P x y -> exists s t, In (s,t) lc 
                                     /\ ( x ≋ sb_app s ε /\ y ≋ sb_app t ε
                                      \/  exists u v, P u v /\ x ≋ sb_app s u /\ y ≋ sb_app t v
                                                   /\ lt_pair u v x y ).
    Proof.
      intros H.
      destruct model as (_ & _ & _ & Hmodel & _).
      apply Hmodel in H.
      clear Hmodel.
      apply fol_sem_big_disj in H.
      destruct H as (c & Hc & H).
      rewrite in_map_iff in Hc.
      destruct Hc as ((s,t) & <- & Hst).
      exists s, t; split; auto.
      unfold sb_app; simpl; rew fot.
      destruct H as [ (H1 & H2) | (u & v & H1 & H2 & H3 & H4) ].
      + left; split.
        * revert H1; simpl; rew fot; unfold env_lift; simpl.
          match goal with |- ?a -> ?b => cut (a=b); [ intros -> | ]; auto end.
          do 2 f_equal.
          rewrite fot_sem_lb_app; rew fot; simpl; f_equal.
          apply fot_sem_ext.
          rewrite fot_vars_lb_app; simpl.
          intros ? [ <- | [] ]; auto.
        * revert H2; simpl; rew fot; unfold env_lift; simpl.
          match goal with |- ?a -> ?b => cut (a=b); [ intros -> | ]; auto end.
          do 2 f_equal.
          rewrite fot_sem_lb_app; rew fot; simpl; f_equal.
          apply fot_sem_ext.
          rewrite fot_vars_lb_app; simpl.
          intros ? [ <- | [] ]; auto.
      + right; exists u, v; msplit 3.
        * apply H1.
        * revert H2; simpl; rew fot; unfold env_lift; simpl.
          match goal with |- ?a -> ?b => cut (a=b); [ intros -> | ]; auto end.
          do 2 f_equal.
          rewrite fot_sem_lb_app; rew fot; simpl; f_equal.
          apply fot_sem_ext.
          rewrite fot_vars_lb_app; simpl.
          intros ? [ <- | [] ]; auto.
        * revert H3; simpl; rew fot; unfold env_lift; simpl.
          match goal with |- ?a -> ?b => cut (a=b); [ intros -> | ]; auto end.
          do 2 f_equal.
          rewrite fot_sem_lb_app; rew fot; simpl; f_equal.
          apply fot_sem_ext.
          rewrite fot_vars_lb_app; simpl.
          intros ? [ <- | [] ]; auto.
        * apply H4.
    Qed.

    Let P_refl : exists x, P x x.
    Proof. apply model. Qed.

    (* Ok we have all the ops in the model ... let us prove some real stuff *)

    Let Hfb_5 b x : x ≋ ⋇ -> f b x ≋ ⋇.
    Proof. 
      intros H; apply Heq_congr_1 with (b := b) in H.
      apply Heq_trans with (1 := H), Hfb_4.
    Qed.

    Let sb_app_congr_1 l x y : x ≋ y -> sb_app l x ≋ sb_app l y.
    Proof.
      intros H; unfold sb_app.
      induction l as [ | b l IHl ]; simpl; rew fot.
      + unfold env_lift; auto.
      + apply Heq_congr_1; auto.
    Qed.

    Let sb_app_fb b l x : sb_app (b::l) x = f b (sb_app l x).
    Proof. auto. Qed.

    Let sb_app_nil x : sb_app nil x = x.
    Proof. auto. Qed.

    Let sb_app_inj l m : ~ sb_app l ε ≋ ⋇ -> sb_app l ε ≋ sb_app m ε -> l = m.
    Proof.
      revert m; induction l as [ | [] l IH ]; intros [ | [] m ] H E; auto.
      + rewrite sb_app_fb, sb_app_nil in E.
        apply Heq_sym, Hfb_1 in E; tauto.
      + rewrite sb_app_fb, sb_app_nil in E.
        apply Heq_sym, Hfb_1 in E; tauto.
      + rewrite sb_app_fb, sb_app_nil in E.
        apply Hfb_1 in E; tauto.
      + do 2 rewrite sb_app_fb in E.
        apply Hfb_2 in E.
        * f_equal; apply IH; auto.
          contradict H.
          rewrite sb_app_fb.
          apply Hfb_5; auto.
        * intros C; apply H.
          rewrite sb_app_fb; auto.
      + do 2 rewrite sb_app_fb in E.
        apply Hfb_3 in E.
        destruct H.
        rewrite sb_app_fb; tauto.
      + rewrite sb_app_fb, sb_app_nil in E.
        apply Hfb_1 in E; tauto.
      + do 2 rewrite sb_app_fb in E. 
        apply Heq_sym, Hfb_3 in E; tauto.
      + do 2 rewrite sb_app_fb in E.
        apply Hfb_2 in E.
        * f_equal; apply IH; auto.
          contradict H.
          rewrite sb_app_fb.
          apply Hfb_5; auto.
        * intros C; apply H.
          rewrite sb_app_fb; auto.
    Qed.

    Let sb_app_congr l m x y z : x ≋ sb_app l y -> y ≋ sb_app m z -> x ≋ sb_app (l++m) z.
    Proof.
      intros H1 H2.
      unfold sb_app.
      rewrite lb_app_app, fot_sem_lb_app.
      apply (sb_app_congr_1 l) in H2.
      apply Heq_trans with (1 := H1).
      apply Heq_trans with (1 := H2).
      unfold sb_app.
      match goal with |- ?a ≋ ?b => cut (a=b); [ intros -> | ]; auto end.
      apply fot_sem_ext.
      intros n; rewrite fot_vars_lb_app; simpl; intros [ <- | [] ].
      auto.
    Qed. 

    Ltac mysolve :=
      match goal with 
        | H1 : ?x ⪡ ?y, H2 : ?y ⪡ ?z |- ?x ⪡ ?z => revert H2; apply Hlt_trans
        | H1 : ?x ≋ ?y, H2 : ?y ⪡ ?z |- ?x ⪡ ?z => revert H2; apply Heq_congr_3
        | H1 : ?x ⪡ ?y, H2 : ?y ≋ ?z |- ?x ⪡ ?z => revert H1; apply Heq_congr_3
        | H1 : ?x ≋ ?y, H2 : ?y ≋ ?z |- ?x ≋ ?z => revert H2; apply Heq_trans
      end; auto.

    Let Hlt_wf : well_founded (fun p q => match p, q with (u,v), (x,y) => lt_pair u v x y end).
    Proof. 
      apply wf_strict_order_finite; auto.
      + apply finite_prod; auto.
      + intros (x,y) [ (H1 & H2) | [ (H1 & H2) | (H1 & H2) ] ].
        all: revert H1; apply Hlt_irrefl.
      + intros (x1,x2) (y1,y2) (z1,z2); unfold lt_pair; simpl.
        intros [ (H1 & H2) | [ (H1 & H2) | (H1 & H2) ] ]
               [ (G1 & G2) | [ (G1 & G2) | (G1 & G2) ] ].
        1: left; split; mysolve.
        4: right; left; split; mysolve.
        all: right; right; split; mysolve.
    Qed.

    Let P_implies_pcp_hand c : match c with (x,y) => 
           P x y -> exists s t, x ≋ sb_app s ε /\ y ≋ sb_app t ε /\ pcp_hand lc s t 
         end.
    Proof.
      induction c as [ (x,y) IH ] using (well_founded_induction Hlt_wf).
      intros Hxy.
      apply Hsimul in Hxy.
      destruct Hxy as (s & t & Hst & [ (H1 & H2) | H ]).
      + exists s, t; msplit 2; auto; constructor 1; auto.
      + destruct H as (u & v & H1 & H2 & H3 & H4).
        destruct (IH (u,v)) with (2 := H1)
          as (s' & t' & G1 & G2 & G3); auto.
        exists (s++s'), (t++t'); msplit 2.
        * apply sb_app_congr with (1 := H2); auto.
        * apply sb_app_congr with (1 := H3); auto.
        * constructor 2; auto.
    Qed.  

    Theorem model_implies_pcp_hand : exists s, pcp_hand lc s s.
    Proof.
      destruct P_refl as (x & Hx).
      destruct (P_implies_pcp_hand (x,x)) with (1 := Hx)
        as (s & t & H1 & H2 & H3).
      apply HP in Hx.
      replace t with s in H3.
      + exists s; auto.
      + apply sb_app_inj.
        * intros H; destruct Hx as [ [] _ ].
          apply Heq_trans with (1 := H1); auto.
        * apply Heq_trans with (2 := H2); auto.
    Qed.

  End fin_sat_BPCP.

  Theorem fin_sat_BPCP : fo_form_fin_SAT phi_R -> exists l, pcp_hand lc l l.
  Proof.
    intros (X & sem_sym & sem_pred & l & phi & M & F).
    apply model_implies_pcp_hand 
      with (sem_sym := sem_sym) 
           (sem_pred := sem_pred) 
           (φ := phi); auto.
    exists l; auto.
  Qed.

End bpcp.

Section reduction.

  Definition BPCP_input := list (list bool * list bool).
  Definition FIN_SAT_input := fol_form a_sym a_pred.

  Definition BPCP_problem (lc : BPCP_input) := exists l, pcp_hand lc l l.
  Definition FIN_SAT_problem (A : FIN_SAT_input) := fo_form_fin_SAT A.
 
  Theorem BPCP_FIN_SAT : exists f, forall x : BPCP_input, BPCP_problem x <-> FIN_SAT_problem (f x).
  Proof.
    exists phi_R; intros lc; split.
    + intros (l & Hl); revert Hl; apply BPCP_sat.
    + apply fin_sat_BPCP.
  Qed.

End reduction.

Check BPCP_FIN_SAT.
Print Assumptions BPCP_FIN_SAT.






    


