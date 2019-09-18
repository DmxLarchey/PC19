(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Bool List Extraction.

(** The correctness proof on this one needs complex induction principles *)

Require Import php wf_incl.

Set Implicit Arguments.

(* This is Depth First Search as in Krauss (2009)

   http://www21.in.tum.de/%7Ekrauss/function/function.pdf

   let rec x ∈ v = 
     match v with
       | []   -> false
       | y::w -> if y=x then true else x ∈ w

   let rec dfs v l =
     match l with
       | []   -> v
       | x::l -> if x ∈ v then dfs v l else dfs (x::v) (succs x ++ l)
     
  where succs : α -> α list
  and       ∈ : α -> α list -> bool
  and     dfs : α list -> α list -> α list

  Termination over a infinite domain is ensured by the
  existence of a finite invariant, ie closed under
  succs (see below).
  
  Defining dfs by naive well-founded induction is going to be
  particularily difficult ...
  
  It works much better via accessibility predicates to get 
  a simulated Inductive/Recursive definition of a partial 
  function: forall v l, d_dfs v l -> list X.
  
  Termination (represented by d_dfs v l) is delayed afterwards 
  where it is much easier to establish.

  Inductive d_dfs : list X -> list X -> Prop :=
    | d_dfs_0 : forall v,                                              d_dfs v nil
    | d_dfs_1 : forall v x l,   In x v -> d_dfs     v            l  -> d_dfs v (x::l)
    | d_dfs_2 : forall v x l, ~ In x v -> d_dfs (x::v) (succs x++l) -> d_dfs v (x::l)
  with Fixpoint dfs v l (D : d_dfs v l) : list X := match D with
    | d_dfs_0 v         => v
    | d_dfs_1 v x l _ D => dfs v l D
    | d_dfs_2 v x l _ D => dfs (x::v) (succs x++l) D
  end.

*)

Section In_bool.

  (** in_dec/In_dec already exists in Coq List library 
      but this one extracts to bool(eans) *)

  Variable (X : Type) (eqX_bool : forall x y : X, { b | x = y <-> b = true }) (x : X).

  (* The intended extracted code for In_bool

     let rec x ∈ v = 
     match v with
       | []   -> false
       | y::w -> if y=x then true else x ∈ w

     where  ∈ : α -> α list -> bool
     and    eqX_bool : α -> α -> bool implements decidable equality test
  *)

  Fixpoint In_bool l : { b | In x l <-> b = true }.
  Proof.
    refine (match l with
      | nil  => exist _ false _
      | y::m => let (b,Hb)   := eqX_bool y x in
                let (b',Hb') := In_bool m in exist _ (b || b') _
    end); subst; simpl.
    + split; try discriminate; tauto.
    + rewrite Hb, Hb', orb_true_iff; tauto.
  Defined.

End In_bool.

Extract Inductive bool => "bool" [ "true" "false" ].
Extraction NoInline orb.

Recursive Extraction In_bool.

Section dfs.

  Variables (X : Type) (eqX_bool : forall x y : X, { b | x = y <-> b = true }).
  Variable  (succs : X -> list X).
  
  (* This is the graph of dfs 

     let rec dfs v l' =
       match l' with
         | []   -> v
         | x::l -> if x ∈ v then dfs v l else dfs (x::v) (succs x ++ l)

     where succs : α -> α list
     and       ∈ : α -> α list -> bool
     and     dfs : α list -> α list -> α list
   *)
  
  Inductive g_dfs : list X -> list X -> list X -> Prop := 
    | in_gdfs_0 : forall v, g_dfs v nil v
    | in_gdfs_1 : forall v x l m,   In x v -> g_dfs v l m -> g_dfs v (x::l) m
    | in_gdfs_2 : forall v x l m, ~ In x v -> g_dfs (x::v) (succs x++l) m -> g_dfs v (x::l) m.

  (* We show that the graph is functional/deterministic *)

  Fact g_dfs_fun v l m1 m2 : g_dfs v l m1 -> g_dfs v l m2 -> m1 = m2.
  Proof.
    intros H; revert H m2.
    induction 1 as [ v | v x l m H1 H2 IH2 | v x l m H1 H2 IH2 ].
    + inversion 1; auto.
    + inversion 1; subst.
      * apply IH2; auto.
      * tauto.
    + inversion 1; subst.
      * tauto.
      * apply IH2; auto.
  Qed.

  (* We define the domain d_dfs as an accessibility predicate

                Acc sub_call (v,l)

     and characterize the relations between recursive sub-calls 
     by the two following rules. The first rule reads
     as: if there is a call a (v,x::l) and x∈v then there
         is a sub-call on (v,l) 

     let rec dfs v l' =
       match l' with
         | []   -> v
         | x::l -> if x ∈ v then dfs v l else dfs (x::v) (succs x ++ l)

  *) 

  Inductive sub_call : (list X * list X) -> (list X * list X) -> Prop := 
    | in_R_0 : forall v x l,   In x v -> sub_call (v,l) (v,x::l)
    | in_R_1 : forall v x l, ~ In x v -> sub_call (x::v,succs x++l) (v,x::l).

  (* The domain d_dfs is the set of pair (v,l) where every sequence
     of recursive sub-calls starting from (v,l) is finite, ie
     accessible in inductive terms *)

  Definition d_dfs v l := (Acc sub_call (v,l)).

  Section dfs.

    (* We separate the computational content from the logical
       content using the handy refine tactic. *)

    Let dfs_full : forall v l, d_dfs v l -> sig (g_dfs v l).
    Proof.
      refine (fix loop v l Dvl { struct Dvl } := 
        match l as l' return d_dfs v l' -> sig (g_dfs v l') with
          | nil   => fun _ =>                                            exist _ v _
          | x::l' => fun D => let (b,Hb) := In_bool eqX_bool x v 
                              in match b as b' return b = b' -> _ with 
            | true  => fun E => let (m,Hm) := loop v l' _                   in  exist _ m _
            | false => fun E => let (m,Hm) := loop (x::v) (succs x ++ l') _ in  exist _ m _
          end eq_refl
        end Dvl); subst.
      3,4: cycle 1.
      1-3: cycle 1.
      * destruct D as [ D ]; apply D; constructor 1; tauto.
      * destruct D as [ D ]; apply D; constructor 2; rewrite Hb; discriminate.
      * constructor 1.
      * constructor 2; tauto.
      * constructor 3; auto; rewrite Hb; discriminate.
    Qed.
    
    (* We get the dfs and its specification by projection.
       Notice that the specification is for the moment
       given by the graph *)
       
    Definition dfs v l D := proj1_sig (@dfs_full v l D).

    Fact dfs_spec v l D : g_dfs v l (@dfs v l D).
    Proof. apply (proj2_sig _). Qed.

  End dfs.

  Arguments dfs : clear implicits.

  (* The graph g_dfs and dfs_spec are enough to characterizes 
     dfs but we rather avoid exposing g_dfs directly to the user 
     and transform the specification of d_dfs/dfs into a simulated 
     inductive/recursive definition.
      
     We get something which could be defined by 
  
     Inductive d_dfs : list X -> list X -> Prop :=
       | d_dfs_0 : forall v,                                              d_dfs v nil
       | d_dfs_1 : forall v x l,   In x v -> d_dfs     v            l  -> d_dfs v (x::l)
       | d_dfs_2 : forall v x l, ~ In x v -> d_dfs (x::v) (succs x++l) -> d_dfs v (x::l)
     with Fixpoint dfs v l (D : d_dfs v l) : list X :=
       match D with
         | d_dfs_0 v         => v
         | d_dfs_1 v x l H D => dfs D
         | d_dfs_2 v x l H D => dfs D
       end.

     Notice that domain constructors d_dfs_[012] do not depend on
     dfs in this particular case, so this is a degenerate case of
     induction/recursion.
    
  *)
 
  Fact d_dfs_0 v : d_dfs v nil.
  Proof. constructor; inversion 1. Qed.

  Fact d_dfs_1 v x l : In x v -> d_dfs v l -> d_dfs v (x::l).
  Proof. constructor; inversion 1; tauto. Qed.

  Fact d_dfs_2 v x l : ~ In x v -> d_dfs (x::v) (succs x ++ l) -> d_dfs v (x::l).
  Proof. constructor; inversion 1; tauto. Qed.

  Theorem d_dfs_g_dfs v l : d_dfs v l <-> exists m, g_dfs v l m.
  Proof.
    split.
    + intros D; exists (dfs v l D); apply dfs_spec.
    + intros (r & Hr); revert Hr.
      induction 1 as [ v | v x l m H1 H2 IH2 | v x l m H1 H2 IH2 ].
      * apply d_dfs_0.
      * apply d_dfs_1; auto.
      * apply d_dfs_2; auto.
  Qed.

  (* This one is more convenient for proving *)

  Fact eqX_dec (x y : X) : { x = y } + { x <> y }.
  Proof.
    destruct (eqX_bool x y) as ([|] & Hb).
    + left; tauto.
    + right; rewrite Hb; discriminate.
  Qed.

  (* Now the depdendent induction principle for the domain *)

  Section d_dfs_rect.
  
    (* Notice HPi which restricts the induction principle to
       proof irrelevant predicates ... no big deal because
       dfs is proof irrelevant anyway 

       The code of d_dfs_rect is very similar to dfs_full
       but we do not need to control it tighly since we do
       not extract it *)

    Variables (P : forall v l, d_dfs v l -> Type)
              (HPi : forall v l D1 D2, @P v l D1 -> @P v l D2)
              (HP0 : forall v, P (d_dfs_0 v))
              (HP1 : forall v x l H1 D, P D -> P (@d_dfs_1 v x l H1 D))
              (HP2 : forall v x l H1 D, P D -> P (@d_dfs_2 v x l H1 D)).

    Fixpoint d_dfs_rect v l D { struct D } : @P v l D.
    Proof.
      destruct l as [ | x l ].
      + apply HPi with (1 := HP0 _).
      + destruct (In_dec eqX_dec x v) as [ H | H ].
        * assert (H1 : d_dfs v l).
          { destruct D as [ D ].
            apply D; constructor; trivial. }
          apply HPi with (1 := HP1 _ H (d_dfs_rect _ _ H1)).
        * assert (H1 : d_dfs (x::v) (succs x++l)).
          { destruct D as [ D ].
            apply D; constructor; trivial. }
          apply HPi with (1 := HP2 _ H (d_dfs_rect _ _ H1)).
    Qed.

  End d_dfs_rect.
  
  (* We want to see the otherwise implicit arguments because
     these are those which matter for computation *)

  (* dfs is proof irrelevant *)

  Fact dfs_pirr v l D1 D2 : dfs v l D1 = dfs v l D2.
  Proof. apply g_dfs_fun with v l; apply dfs_spec. Qed.
  
  (* Fixpoint equations corresponding to the above I/R definition *)

  Fact dfs_fix_0 v : dfs v nil (d_dfs_0 v) = v.
  Proof. apply g_dfs_fun with v nil; [ | constructor 1 ]; apply dfs_spec. Qed.
 
  Fact dfs_fix_1 v x l H D : dfs v (x::l) (d_dfs_1 _ H D) 
                           = dfs v l D.
  Proof. apply g_dfs_fun with v (x::l); [ | constructor 2; auto ]; apply dfs_spec. Qed.

  Fact dfs_fix_2 v x l H D : dfs v (x::l) (d_dfs_2 _ H D) 
                           = dfs (x::v) (succs x++l) D.
  Proof. apply g_dfs_fun with v (x::l); [ | constructor 3; auto ]; apply dfs_spec. Qed.

  Section d_dfs_ind.
  
    (* We can retrieve an non-dependent induction principle for dfs 
       which is very similar to the induction principle of g_dfs *)
  
    Variables (P : list X -> list X -> list X -> Prop)
              (HP1 : forall v, P v nil v)
              (HP2 : forall v x l r,   In x v -> P v l r -> P v (x::l) r)
              (HP3 : forall v x l r, ~ In x v -> P (x::v) (succs x ++ l) r -> P v (x::l) r).

    Theorem d_dfs_ind v l D : P v l (dfs v l D).
    Proof.
      induction D as [ v l D1 D2 | | | ] using d_dfs_rect.
      rewrite (dfs_pirr _ D1); auto.
      rewrite dfs_fix_0; auto.
      rewrite dfs_fix_1; auto.
      rewrite dfs_fix_2; auto.
    Qed.
 
  End d_dfs_ind.

  (****************************************************
       Specification of g_dfs/dfs by IR is finished
   ****************************************************)
  
  (** Let us establish the partial correctness of dfs *)
 
  (* dfs computes a finite invariant *) 

  Definition dfs_invariant_t v l (i : list X) := 
          incl v i /\ incl l i
       /\ forall x, In x i -> In x v \/ incl (succs x) i.

  (* when defined, dfs v l produces an invariant i as a finite list :
       a) which contains v 
       b) which contains l
       c) and any succs-image of x ∈ i\v belongs to i 

     and this invariant is the least for that property *) 

  Theorem dfs_invariant v l D : dfs_invariant_t v l (dfs v l D)
                   /\ forall i, dfs_invariant_t v l i -> incl (dfs v l D) i.
  Proof.
    pattern v, l, (dfs v l D); revert v l D; apply d_dfs_ind;
      [ intros v | intros v x l H1 D ID1 | intros v x l H1 D ID1 ];
      unfold dfs_invariant_t in * |- *; unfold incl in *.

    (* first constructor for dfs _ nil *)

    + simpl; tauto.
    
    (* second constructor for dfs v (x::_) where x ∈ v *) 

    + destruct ID1 as ((H2 & H3 & H4) & H5).
      repeat split; simpl; try tauto.
      * intros y [ [] | ? ]; auto.
      * intros ? (? & ? & ?); apply H5; auto.
 
    (* third constructor for dfs v (x::_) where x ∉ v *) 

    + destruct ID1 as ((H2 & H3 & H4) & H5).
      repeat split; auto.
      * intros y Hy; apply H2; right; auto.
      * intros y [ | ]; subst.
        - apply H2; simpl; auto.
        - apply H3, in_or_app; simpl; auto.
      * intros y Hy.
        apply H4 in Hy.
        destruct Hy as [ [ | ] | ]; auto; subst; right.
        intros ? ?; apply H3, in_or_app; simpl; auto.
      * intros P (G1 & G2 & G3).
        apply H5.
        repeat split; auto.  
        - intros ? [|]; subst; auto; apply G2; simpl; auto.
        - intros y Hy.
          apply in_app_or in Hy; destruct Hy; 
            [ destruct (G3 x); auto | ]; [ | destruct H1; auto | ];
            apply G2; simpl; tauto.
        - intros ? Hy; destruct (G3 _ Hy); simpl; auto.
  Qed.

  (* dfs contains no duplicated value, unless there is one in v 
     hence dfs is also minimal w.r.t. cardinality *)

  Fact dfs_no_dup v l D : list_has_dup (dfs v l D) -> list_has_dup v.
  Proof.
    induction D as [ v l D1 D2 
                   | v 
                   | v x l H1 D ID1 
                   | v x l H1 D ID1 ] using d_dfs_rect.

    * rewrite (dfs_pirr _ D1); auto.
    * rewrite dfs_fix_0; auto.
    * rewrite dfs_fix_1; auto.
    * rewrite dfs_fix_2.
      intros H; specialize (ID1 H).
      apply list_has_dup_cons_inv in ID1; tauto.
  Qed.

  (* Hence dfs v l cannot terminate unless such a finite invariant exists
     (because that is what it computes ...) 
     Let us show that this condition is also sufficient *)

  Theorem d_dfs_domain v l : d_dfs v l <-> exists i, dfs_invariant_t v l i.
  Proof.
    split.
    + (* The direct implication is trivially derived from partial correctness *)
      intros D; exists (dfs v l D); apply dfs_invariant.
    + (* The reverse implication is more complicated, much more ...
         We proceed by lexicographic product 
           a) strict inclusion bounded by i for v
           b) structural induction for l *)
      intros (i & H1 & H2 & H3).
      revert v H1 l H2 H3.
      (* Induction on v using upper-bounded strict inclusion as well-founded relation *)
      induction v as [ v IHv ] using (well_founded_induction (wf_rincl_fin i)); intros Hv.
      (* Structural induction on l *)
      induction l as [ | x l IHl ]; intros Hl H.
      * (* dfs v nil *)
        apply d_dfs_0.
      * destruct (In_dec eqX_dec x v) as [ Hx | Hx ].
        - (* dfs v (x::_) where x ∈ v *) 
          clear IHv.
          apply d_dfs_1; auto.
          (* Induction on l *)
          apply IHl; auto.
          intros ? ?; apply Hl; right; auto.
        - (* dfs v (x::_) where x ∉ v *) 
          clear IHl.
          apply d_dfs_2; auto.
          assert (Hx' : In x i) by (apply Hl; left; auto).
          (* Induction on v *)
          apply IHv.
          ++ split.
             ** right; auto.
             ** exists x; repeat split; auto; left; auto.
          ++ intros y [ ? | ? ]; subst; auto.
          ++ intros y Hy.
             apply in_app_or in Hy.
             destruct Hy as [ Hy | Hy ].
             ** apply H in Hx'.
                destruct Hx' as [ Hx' | Hx' ].
                -- tauto.
                -- apply Hx'; auto.
             ** apply Hl; right; auto.
          ++ intros y Hy.
             apply H in Hy; simpl; tauto.
  Qed.

  (* Using the domain characterized by invariants, 
     monotonicity properties are easy to establish ... 
     it is much harder with d_dfs based induction. *)

  Fact d_dfs_mono v v' l l' : incl v v' -> incl l' (v'++l) -> d_dfs v l -> d_dfs v' l'.
  Proof.
    intros H1 H2.
    do 2 rewrite d_dfs_domain.
    intros (lP & H3 & H4 & H5).
    exists (v'++lP); repeat split; auto.
    + intros ? ?; apply in_or_app; left; auto.
    + intros x Hx; apply in_or_app.
      apply H2, in_app_or in Hx.
      destruct Hx; auto.
    + intros x Hx.
      apply in_app_or in Hx.
      destruct Hx as [ Hx | Hx ]; auto.
      apply H5 in Hx.
      destruct Hx as [ Hx | Hx ].
      * left; apply H1; auto.
      * right.
        intros ? ?; apply in_or_app; right; auto.
  Qed.
  
  (* dfs is usually called as dfs nil l. 
     In that case, the invariant is simpler 

     It is list containing l and closed under succs
   *)
  
  Definition dfs_nil_invariant_t l inv := incl l inv /\ forall x, In x inv -> incl (succs x) inv.

  (* Partial correctness of dfs nil: it computes the minimal invariant *)

  Corollary dfs_nil_invariant l D : dfs_nil_invariant_t l (@dfs nil l D)
                           /\ forall inv, dfs_nil_invariant_t l inv -> incl (dfs nil l D) inv.
  Proof.
    generalize (dfs_invariant D); intros ((_ & H2 & H3) & H4).
    repeat split; auto.
    + intros x Hx.
      destruct (H3 _ Hx) as [ [] | ]; auto.
    + intros inv (G1 & G2); apply H4.
      repeat split; auto.
      intros _ [].
  Qed.

  (* "Total" correctedness: dfs terminates provided an invariant exists *)

  Corollary d_dfs_nil_domain l : d_dfs nil l <-> ex (dfs_nil_invariant_t l). 
  Proof.
    split.
    + intros D; exists (dfs _ _ D); apply dfs_nil_invariant.
    + rewrite d_dfs_domain.
      intros (inv & H1 & H2).
      exists inv; split; auto.
      intros _ [].
  Qed.

  Section finite_domain.

    (* In particular, if X is finite then dfs terminate *)
 
    Hypothesis (HX : exists lX, forall x : X, In x lX).

    Fact d_dfs_total v l : d_dfs v l.
    Proof. 
      apply d_dfs_domain.
      destruct HX as (lX & H1).
      exists lX; repeat split; unfold incl; auto.
    Qed.

  End finite_domain.

End dfs.

Check d_dfs.
Print Assumptions d_dfs.

Check dfs.
Print Assumptions dfs.

Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Recursive Extraction dfs.

Check d_dfs_total.
Print Assumptions d_dfs_total.
