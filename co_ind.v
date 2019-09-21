Require Import Arith Nat Lia List Extraction.

Set Implicit Arguments.

Section snoc_ind.

  Variable (X : Type) (P : list X -> Type).

  Hypothesis HP0 : P nil.
  Hypothesis HP1 : forall l x, P l -> P (l++x::nil).

  Definition list_snoc_rect l : P l.
  Proof.
    rewrite <- (rev_involutive l).
    set (Q l := P (rev l)).
    change (Q (rev l)).
    generalize (rev l).
    clear l; intros l.
    unfold Q; clear Q.

    induction l as [ | x l IHl ].
    + apply HP0.
    + simpl; apply HP1; auto.
  Qed.

End snoc_ind.
 
Inductive pos3 := ZZ | OO | TT.

Definition pos3_nat p :=
  match p with
    | ZZ => 0
    | OO => 1
    | TT => 2
  end.

Fact pos3_nat_le p : pos3_nat p <= 2.
Proof. destruct p; auto. Qed.

(*

1 2 3 4 5 6 7 8 9 a b c d e f
  1   2   3   4   5   6   7
      1       2       3   
              1

N []   = 1 
N l++x = 2*N l + (x-1)

*)

Fixpoint N_rec a l :=
  match l with
    | nil  => a 
    | x::l => N_rec (2*a+(pos3_nat x)-1) l
  end.

Definition N l := N_rec 1 l.

Fact N_nil : N nil = 1.
Proof. trivial. Qed.

Fixpoint N_app a l m : N_rec a (l++m) = N_rec (N_rec a l) m.
Proof. destruct l; simpl; auto. Qed.
  
Fact N_snoc l x : N (l++x::nil) = 2*N l+pos3_nat x-1.
Proof.
  unfold N; rewrite N_app; simpl; auto.
Qed.

Fact N_bound l : 1 <= N l <= 2^(1+length l)-1.
Proof.
  induction l as [ | l x IHl ] using list_snoc_rect.
  + rewrite N_nil; simpl; lia.
  + rewrite N_snoc, app_length; simpl length.
    generalize (pos3_nat_le x).
    replace (1+(length l+1)) with (S (1+length l)) by lia.
    rewrite Nat.pow_succ_r'.
    lia.
Qed.

Eval compute in N (ZZ::OO::TT::nil).
Eval compute in N (TT::TT::TT::nil).

Fact N_ZZ l : N (ZZ::l) < 2*2^(length l).
Proof.
  induction l as [ | l x IHl ] using list_snoc_rect.
  + cbv; auto.
  + change (ZZ::l++x::nil) with ((ZZ::l)++x::nil).
    rewrite N_snoc, app_length.
    simpl length.
    rewrite Nat.pow_add_r.
    revert IHl.
    generalize (pos3_nat x) (N (ZZ::l)) (2^length l) (pos3_nat_le x).
    intros a b c H1 H2; simpl; lia.
Qed.

Fact N_OO l : 2^(length l) < N (OO::l) < 3*2^(length l).
Proof.
  induction l as [ | l x IHl ] using list_snoc_rect.
  + cbv; auto.
  + change (OO::l++x::nil) with ((OO::l)++x::nil).
    rewrite N_snoc, app_length.
    simpl length.
    rewrite Nat.pow_add_r.
    revert IHl.
    generalize (pos3_nat x) (N (OO::l)) (2^length l) (pos3_nat_le x).
    intros a b c H1 H2; simpl; lia.
Qed.

Fact N_TT l : 2*2^(length l) < N (TT::l).
Proof.
  induction l as [ | l x IHl ] using list_snoc_rect.
  + cbv; auto.
  + change (TT::l++x::nil) with ((TT::l)++x::nil).
    rewrite N_snoc, app_length.
    simpl length.
    rewrite Nat.pow_add_r.
    revert IHl.
    generalize (pos3_nat x) (N (TT::l)) (2^length l) (pos3_nat_le x).
    intros a b c H1 H2; simpl; lia.
Qed.

CoInductive stream := lcons : pos3 -> stream -> stream.

CoFixpoint lcst x := lcons x (lcst x).

Fixpoint prefix n s := 
  match n, s with 
    | 0  , _         => nil
    | S n, lcons x s => x::prefix n s
  end.

Fixpoint ltail n s :=
  match n, s with 
    | 0  , s         => s
    | S n, lcons x s => ltail n s
  end.

Fixpoint lapp l s :=
  match l with
    | nil  => s
    | x::l => lcons x (lapp l s)
  end.

Fact ltail_cst n x : ltail n (lcst x) = lcst x.
Proof.
  induction n; auto.
Qed.

Fact prefix_ltail n s : lapp (prefix n s) (ltail n s) = s.
Proof.
  revert s; induction n as [ | n IHn ]; intros s; auto.
  destruct s as [ x s ]; simpl; f_equal; auto.
Qed.

Fact prefix_add n m s : prefix (n+m) s = prefix n s ++ prefix m (ltail n s).
Proof.
  revert s; induction n as [ | n IHn ]; intros s; auto.
  destruct s; simpl; f_equal; auto.
Qed.

Fact prefix_length n s : length (prefix n s) = n.
Proof.
  revert s; induction n as [ | n IHn ]; intros []; simpl; f_equal; auto.
Qed.

Fact pow2_ge_1 n : 1 <= 2^n.
Proof.
  change 1 with (2^0).
  apply Nat.pow_le_mono_r_iff; simpl; lia.
Qed.

Eval compute in N (prefix 3 (lcst TT)).

Fact N_ZZZ n : N (prefix n (lcst ZZ)) = 1.
Proof.
  induction n; auto.
Qed.

Fact N_OOO n : N (prefix n (lcst OO)) = 2^n.
Proof.
  induction n as [ | n IHn ]; auto.
  replace (S n) with (n+1) by lia.
  rewrite prefix_add, ltail_cst.
  simpl prefix; rewrite N_snoc, IHn.
  simpl pos3_nat.
  rewrite Nat.pow_add_r; simpl; lia.
Qed.

Fact N_TTT n : N (prefix n (lcst TT)) = 2*2^n-1.
Proof.
  induction n as [ | n IHn ]; auto.
  replace (S n) with (n+1) by lia.
  rewrite prefix_add, ltail_cst.
  simpl prefix; rewrite N_snoc, IHn.
  simpl pos3_nat.
  rewrite Nat.pow_add_r.
  generalize (2^n) (pow2_ge_1 n).
  intros; simpl; lia.
Qed.

(** Every stream s represents a real which is the limit 
    of fun n => N (prefix n s) / 2*2^n) 

    ZZZ = lcst ZZ ~~~> 0
    OOO = lcst OO ~~~> 1/2
    TTT = lcst TT ~~~> 1

*)

(** Looking at the first value in the stream s allows to
    position s either in [ 0 .. 3/4 ] or in [ 1/4 .. 1 ] *)

Theorem stream_choose s : { m : _ & (forall n, m <= n -> N (prefix n s) <= 3*2^(n-1))
                                  + (forall n, m <= n -> 2^(n-1) <= N (prefix n s))  }%type.
Proof.
  destruct s as [ [] s ].
  + exists 1; left; intros n Hn.
    replace n with (1+(n-1)) at 1 by lia. 
    generalize (n-1); intros a; clear n Hn.
    simpl prefix.
    generalize (N_ZZ (prefix a s)).
    rewrite prefix_length; lia.
  + exists 1; left; intros n Hn.
    replace n with (1+(n-1)) at 1 by lia. 
    generalize (n-1); intros a; clear n Hn.
    simpl prefix.
    generalize (N_OO (prefix a s)).
    rewrite prefix_length; lia.
  + exists 1; right; intros n Hn.
    replace n with (1+(n-1)) at 2 by lia. 
    generalize (n-1); intros a; clear n Hn.
    simpl prefix.
    generalize (N_TT (prefix a s)).
    rewrite prefix_length; lia.
Qed.

Recursive Extraction stream_choose.

Section on_the_fly_update.

  Variable f : pos3 * pos3 * pos3 -> pos3 * pos3 * pos3.

  CoFixpoint otf_update s := 
    match s with lcons a (lcons b (lcons c s)) => 
      match f (a,b,c) with
        | (x,y,z) =>  lcons x (otf_update (lcons y (lcons z s)))
      end
    end.

End on_the_fly_update.

Recursive Extraction otf_update.






