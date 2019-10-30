(**************************************************************)
(*   Copyright Dominique Larchey-Wendling    [*]              *)
(*             Jean-François Monin           [+]              *)
(*                                                            *)
(*            [*] Affiliation LORIA -- CNRS                   *)
(*            [+] Affiliation VERIMAG - Univ. Grenoble-Alpes  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** From verify.rwth-aachen.de/giesl/papers/ibn96-30.ps

    orig. algo from https://arxiv.org/ftp/cs/papers/9301/9301103.pdf

   type Ω = α | ω of Ω * Ω * Ω

   let rec nm e = match e with
     | α                => α
     | ω (α,y,z)        => ω (α,nm y,nm z)
     | ω (ω(a,b,c),y,z) => nm (ω (a,nm(ω(b,y,z)),nm(ω(c,y,z)))

  We simulate the following Inductive/Recursive definition

  Inductive 𝔻 : Ω -> Prop :=
    | d_nm_0 : 𝔻 α
    | d_nm_1 : forall y z, 𝔻 y -> 𝔻 z -> 𝔻 (ω α y z)
    | d_nm_2 : forall a b c y z (Db : 𝔻 (ω b y z)) (Dc : 𝔻 (ω c y z)),
\                      𝔻 (ω a (nm (ω b y z) D1) (nm (ω c y z) D2))
\                   -> 𝔻 (ω (ω a b c) y z)
  with Fixpoint nm e (De : 𝔻 e) : Ω :=
    match De with
      | d_nm_0 => α
      | d_nm_1 y z Dy Dz => ω α (nm y Dy) (nm z Dz)
      | d_nm_2 a b c y z Db Dc Da => nm (ω a (nm (ω b y z) Db) (nm (ω c y z) Dc)) Da
    end.
*)

Require Import Arith Lia Wellfounded Extraction.

Require Import measure_ind.

Tactic Notation "eq" "goal" "with" hyp(H) := 
  match goal with 
    |- ?b => match type of H with ?t => replace b with t; auto end 
  end.

Set Implicit Arguments.

Inductive cexpr : Set := At : cexpr | If : cexpr -> cexpr -> cexpr -> cexpr.

Notation α := At.
Notation ω := If.
Notation Ω := cexpr.

Section nm_def.

  Reserved Notation "x '~~>' y" (at level 70, no associativity).
  
  Inductive 𝔾 : Ω -> Ω -> Prop :=
    | in_gnm_0 :           α ~~> α

    | in_gnm_1 y ny z nz :
                         y   ~~>     ny
                  ->       z ~~>        nz
                  -> ω α y z ~~> ω α ny nz

    | in_gnm_2 : forall a b c y z nb nc na,
                             ω b y z ~~> nb
                  ->         ω c y z ~~> nc
                  ->       ω a nb nc ~~> na
                  -> ω (ω a b c) y z ~~> na
  where "x ~~> y" := (𝔾 x y).

  Ltac inv_ind := match goal with 
      | H: forall x : _, ?t ~~> x -> ?y = x, 
        G: ?t ~~> ?z                         
       |- _ => apply H in G; subst 
    end.

  Local Fact 𝔾_fun e n1 n2 : e ~~> n1 -> e ~~> n2 -> n1 = n2.
  Proof.
    intros H; revert H n2.
    induction 1 as [ 
                   | y ny z nz H1 IH1 H2 IH2
                   | u v w y z na nb nc H1 IH1 H2 IH2 H3 IH3 ]; inversion 1; subst; auto.
    + f_equal; auto.
    + repeat inv_ind; auto.
  Qed.
  
  Unset Elimination Schemes.

  Inductive d_nm : Ω -> Prop :=
    | in_dnm_0 :                   d_nm α
    | in_dnm_1 : forall y z,       d_nm y 
                                -> d_nm z 
                                -> d_nm (ω α y z)
    | in_dnm_2 : forall a b c y z,
                                   d_nm (ω b y z) 
                                -> d_nm (ω c y z) 
                 -> (forall nb nc, ω b y z ~~> nb  
                                -> ω c y z ~~> nc 
                                -> d_nm (ω a nb nc))
                                -> d_nm (ω (ω a b c) y z).
  
  Notation 𝔻 := d_nm.

  Set Elimination Schemes.

  Section nm_def.

    Let nm_full : forall e, 𝔻 e -> { n | e ~~> n }.
    Proof.
      refine(fix loop e De := match e as e' return 𝔻 e' -> sig (𝔾 e') with
        | α               => fun _ => 
                         exist _ α _

        | ω α y z         => fun D => 
          let (ny,Dy) := loop y _ in
          let (nz,Dz) := loop z _ in
                         exist _ (ω α ny nz) _

        | ω (ω a b c) y z => fun D =>
          let (nb,Db) := loop (ω b y z)   _ in
          let (nc,Dc) := loop (ω c y z)   _ in
          let (na,Da) := loop (ω a nb nc) _ in
                         exist _ na _
      end De).
      2-3,5-7: inversion D; auto.
      + constructor 1.
      + constructor 2; auto.
      + constructor 3 with nb nc; auto.
    Qed.

    Definition nm e (D : 𝔻 e) := proj1_sig (@nm_full e D).
    
    Fact nm_spec e D : 𝔾 e (@nm e D). 
    Proof. apply (proj2_sig _). Qed.
  
  End nm_def.
  
  Arguments nm e D : clear implicits.
  
  Fact d_nm_0 : 𝔻 α.
  Proof. constructor; auto. Qed.

  Fact d_nm_1 y z : 𝔻 y -> 𝔻 z -> 𝔻 (ω α y z).
  Proof. constructor; auto. Qed.

  Fact d_nm_2 a b c y z Db Dc : 𝔻 (ω a (nm (ω b y z) Db) (nm (ω c y z) Dc)) 
                             -> 𝔻 (ω (ω a b c) y z).
  Proof. 
    constructor 3; auto.
    intros; eq goal with H; do 2 f_equal;
    apply 𝔾_fun with (1 := nm_spec _); trivial.
  Qed.

  Hint Resolve nm_spec.

  Section d_nm_rect.

    Variables (P : forall e, 𝔻 e -> Type)
              (HPi : forall e D1 D2, @P e D1 -> @P e D2)
              (HP0 : P d_nm_0)
              (HP1 : forall y z D1 (_ : P D1) D2 (_ : P D2), P (@d_nm_1 y z D1 D2))
              (HP2 : forall a b c y z D1 (_ : P D1) D2 (_ : P D2) D3 (_ : P D3), P (@d_nm_2 a b c y z D1 D2 D3)).
  
    Fixpoint d_nm_rect e (De : 𝔻 e) : @P e De.
    Proof.
      destruct e as [ | [ | a b c ] y z ].
      + apply HPi with (1 := HP0).
      + refine (HPi _ (HP1 (d_nm_rect y _) 
                           (d_nm_rect z _))); 
          inversion De; trivial.
      + assert (𝔻 (ω b y z)) as Db by (inversion De; trivial).
        assert (𝔻 (ω c y z)) as Dc by (inversion De; trivial).
        refine (HPi _ (HP2 (d_nm_rect (ω b y z) Db)
                           (d_nm_rect (ω c y z) Dc) 
                           (d_nm_rect (ω a _ _) _))). (** dependancies here *)
        inversion De; auto.
    Qed.

  End d_nm_rect.

  Definition d_nm_ind (P : forall e, 𝔻 e -> Prop) := @d_nm_rect P. 

  Fact nm_pirr e D1 D2 : nm e D1 = nm e D2.
  Proof. apply 𝔾_fun with e; auto. Qed.

  Fact nm_fix_0 : nm α d_nm_0 = α.
  Proof. apply 𝔾_fun with α; [ | constructor ]; auto. Qed.

  Fact nm_fix_1 y z D1 D2 : nm (ω α y z) (d_nm_1 D1 D2) = ω α (nm y D1) (nm z D2).
  Proof. apply 𝔾_fun with (ω α y z); [ | constructor ]; auto. Qed.

  Fact nm_fix_2 u v w y z D1 D2 D3 : 
            nm (ω (ω u v w) y z) (d_nm_2 D1 D2 D3) 
          = nm (ω u (nm (ω v y z) D1) (nm (ω w y z) D2)) D3.
  Proof. 
    apply 𝔾_fun with (ω (ω u v w) y z); auto.
    constructor 3 with (nm _ D1) (nm _ D2); auto.
  Qed.
   
End nm_def.

Arguments nm e D : clear implicits.

Create HintDb nm_fix_db.
Hint Rewrite nm_fix_0 nm_fix_1 nm_fix_2 : nm_fix_db.

Ltac nm_pirr := 
  match goal with 
    [ |- context f [nm ?e _] ] => 
    match goal with 
      _: context[nm e ?D] |- _ => rewrite (nm_pirr _ D) 
    end 
  end.

Ltac nm_rewrite := autorewrite with nm_fix_db.

Tactic Notation "nm" "auto" := try nm_pirr; nm_rewrite; auto.

Check nm_spec.
Print Assumptions nm_spec.

Recursive Extraction nm.

(* Now we show the partial correctness of nm, 
   independently of its termination *)

(** normal forms only have atoms as boolean condition 
    ie. b in if b then _ else _ *)

Inductive normal : Ω -> Prop :=
  | in_normal_0 :             normal α
  | in_normal_1 : forall y z, normal y 
                           -> normal z 
                           -> normal (ω α y z).

Notation ℕ := normal.

(** nm produces normal forms *)

Theorem nm_normal e D : ℕ (nm e D).
Proof.
  induction D.
  all: nm auto; constructor; auto.
Qed.

(** equiv is the congruence generated by 

   ω (ω a b c) y z ~e ω a (ω b y z) (ω c y z) 

  *)

Reserved Notation "x '~Ω' y" (at level 70, no associativity).

Inductive equiv : Ω -> Ω -> Prop :=
  | in_eq_0 : forall u v w y z, ω (ω u v w) y z ~Ω ω u (ω v y z) (ω w y z)
  | in_eq_1 : forall x x' y y' z z', x ~Ω x' -> y ~Ω y' -> z ~Ω z'-> ω x y z ~Ω ω x' y' z'
  | in_eq_2 : α ~Ω α
  | in_eq_3 : forall x y z, x ~Ω y -> y ~Ω z -> x ~Ω z
where "x ~Ω y" := (equiv x y).

Hint Constructors equiv.

Fact equiv_refl e : e ~Ω e.   Proof. induction e; auto. Qed.

Hint Resolve equiv_refl.

Notation equiv_trans := in_eq_3.

(** nm preserves equivalence *)

Fact nm_equiv e D : e ~Ω nm e D.
Proof.
  induction D as [ e D1 D2 
                 | 
                 | y z D1 ID1 D2 ID2 
                 | u v w y z D1 ID1 D2 ID2 D3 ID3 ].
  all: nm auto.
  apply equiv_trans with (2 := ID3),
        equiv_trans with (1 := in_eq_0 _ _ _ _ _); auto.
Qed.

(** Using the simulated IR definition of 

            𝔻 : Ω -> Prop and nm : forall e, 𝔻 e -> Ω

    we show totality of 𝔻: 
 
      a) we define a measure [.] : Ω -> nat by structural induction

      b) we show that nm preserves the measure, ie

           forall e (De : 𝔻 e), [nm e De] <= [e]

         by dependent induction on De : 𝔻 e

      c) we show that 𝔻 is total
      
           forall e, 𝔻 e 
           
         by induction on [e] : nat
*)

Section ce_size.

  Let c x y z := x * (1+y+z).

  (* The next properties are sufficient for the measure *)

  Let c_mono x x' y y' z z' : x <= x' -> y <= y' -> z <= z' -> c x y z <= c x' y' z'.
  Proof. intros; simpl; apply mult_le_compat; lia. Qed.

  Let c_smono_1 x x' y z : x < x' -> c x y z < c x' y z.
  Proof. intro; simpl; apply mult_lt_compat_r; lia. Qed.

  Let c_inc_1 x y z : x <= c x y z.
  Proof. unfold c; rewrite <- Nat.mul_1_r at 1; apply mult_le_compat; lia. Qed.

  Let c_sinc_1 x y z : 0 < x -> 0 < y + z -> x < c x y z.
  Proof. intros ? ?; unfold c; rewrite <- Nat.mul_1_r at 1; apply mult_lt_compat_l; lia. Qed.

  Let c_sinc_2 x y z : 0 < x -> y < c x y z.
  Proof. intros ?; unfold c, lt; rewrite <- Nat.mul_1_l at 1; apply mult_le_compat; lia. Qed.

  Let c_sinc_3 x y z : 0 < x -> z < c x y z.
  Proof. intros ?; unfold c, lt; rewrite <- Nat.mul_1_l at 1; apply mult_le_compat; lia. Qed.

  Let c_special a u v y z : 0 < a -> 0 < y + z -> c a (c u y z) (c v y z) < c (c a u v) y z.
  Proof.
    unfold c; intros ? ?.
    rewrite <- mult_assoc.
    apply mult_lt_compat_l; auto.
    simpl.
    generalize (S (y + z)); intros n.
    rewrite mult_plus_distr_r; lia.
  Qed.

  Reserved Notation "'[' e ']'" (at level 0).

  (** This is the decreasing measure *)

  Fixpoint ce_size e :=
    match e with
      | α => 1
      | ω x y z => c [x] [y] [z]
    end
  where "[ e ]" := (ce_size e).

  (* Some elementary properties of the measure *)

  Local Fact ce_size_mono x x' y y' z z' : 
     [x] <= [x'] -> [y] <= [y'] -> [z] <= [z'] -> [ω x y z] <= [ω x' y' z'].
  Proof. apply c_mono. Qed.

  Local Fact ce_size_smono_1 x x' y z : [x] < [x'] -> [ω x y z] < [ω x' y z].
  Proof. apply c_smono_1. Qed.

  Local Fact ce_size_ge_1 e : 1 <= [e].
  Proof.
    induction e as [ | x Hx y _  z _ ]; auto.
    apply le_trans with (1 := Hx), c_inc_1.
  Qed.

  Hint Resolve ce_size_ge_1.

  Local Fact ce_size_sub_1 x y z : [x] < [ω x y z].
  Proof. simpl; apply c_sinc_1; auto; generalize (ce_size_ge_1 y); lia. Qed.

  Local Fact ce_size_sub_2 x y z : [y] < [ω x y z].
  Proof. simpl; apply c_sinc_2; auto. Qed.

  Local Fact ce_size_sub_3 x y z : [z] < [ω x y z].
  Proof. simpl; apply c_sinc_3; auto. Qed.

  (* The special properties that makes it a suitable measure for induction *)

  Local Fact ce_size_special a u v y z : [ω a (ω u y z) (ω v y z)] < [ω (ω a u v) y z].
  Proof. simpl; apply c_special; auto; generalize (ce_size_ge_1 y); lia. Qed.

End ce_size.

(* No we finish with the termination/totality of nm *)

Section d_nm_total.

  Notation 𝔻 := d_nm.
  Notation "'[' e ']'" := (ce_size e) (at level 0).

  Hint Resolve ce_size_sub_2 ce_size_sub_3 ce_size_mono ce_size_smono_1.
  
  (** nm preserves the measure *)

  Local Fact nm_dec e D : [nm e D] <= [e].
  Proof.
    induction D as [ e D1 D2 | | y z D1 ID1 D2 ID2 | u v w y z D1 ID1 D2 ID2 D3 ID3 ]; nm auto.
    apply le_trans with (1 := ID3),
          le_trans with (2 := ce_size_special _ _ _ _ _); auto.
  Qed.

  Hint Resolve nm_dec.

  (** Termination/totality by induction on [e] *)

  Theorem d_nm_total e : 𝔻 e.
  Proof.
    induction on e as IHe with measure [e].
    destruct e as [ | [ | u v w ] y z ].
    + apply d_nm_0.
    + apply d_nm_1; apply IHe; simpl; lia.
    + assert (D1 : 𝔻 (ω v y z)) by auto.
      assert (D2 : 𝔻 (ω w y z)) by auto.
      apply d_nm_2 with D1 D2.
      apply IHe, le_lt_trans with (2 := ce_size_special _ _ _ _ _); auto.
  Qed.
  
End d_nm_total.

(** We can finish with a fully specified term defining a total function 
    which computes a normal form *)

Hint Resolve nm_equiv nm_normal.

Definition nm_total e : { ne | e ~Ω ne /\ ℕ ne }.
Proof.
  exists (nm _ (d_nm_total e)); auto.
Defined.

Extraction Inline nm.

Recursive Extraction nm_total.

Print inhabited.


