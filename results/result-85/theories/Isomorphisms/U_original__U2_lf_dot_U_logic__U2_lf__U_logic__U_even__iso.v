From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Require Import Stdlib.Logic.ProofIrrelevance.

From IsomorphismChecker Require Export Isomorphisms.nat__iso Isomorphisms.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.

Monomorphic Definition imported_Original_LF__DOT__Logic_LF_Logic_Even : imported_nat -> SProp := Imported.Original_LF__DOT__Logic_LF_Logic_Even.

Definition Even_orig := Original.LF_DOT_Logic.LF.Logic.Even.
Definition Even_imp := Imported.Original_LF__DOT__Logic_LF_Logic_Even.

(* Convert Prop proof irrelevance to SProp eq *)
Definition prop_proof_irrel_to_seq : forall (P : Prop) (p1 p2 : P), IsomorphismDefinitions.eq p1 p2 :=
  fun P p1 p2 =>
    match proof_irrelevance P p1 p2 in (_ = p) return IsomorphismDefinitions.eq p1 p with
    | Logic.eq_refl => IsomorphismDefinitions.eq_refl
    end.

(* Helper: convert Logic.eq to Imported.Corelib_Init_Logic_eq *)
Definition logic_eq_to_imported_eq {A : Type} {x y : A} (H : @Logic.eq A x y) : Imported.Corelib_Init_Logic_eq A x y :=
  match H in (@Logic.eq _ _ z) return Imported.Corelib_Init_Logic_eq A x z with
  | Logic.eq_refl => Imported.Corelib_Init_Logic_eq_refl A x
  end.

(* Helper: convert Imported.Corelib_Init_Logic_eq to Logic.eq *)
Definition imported_eq_to_logic_eq {A : Type} {x y : A} (H : Imported.Corelib_Init_Logic_eq A x y) : @Logic.eq A x y :=
  match H in (Imported.Corelib_Init_Logic_eq _ _ z) return @Logic.eq A x z with
  | Imported.Corelib_Init_Logic_eq_refl _ _ => Logic.eq_refl
  end.

(* Prove double commutes with nat_to_imported *)
Fixpoint double_iso_lemma (n : Datatypes.nat) : 
  @Logic.eq Imported.nat (nat_to_imported (Original.LF_DOT_Induction.LF.Induction.double n)) (Imported.Original_LF__DOT__Induction_LF_Induction_double (nat_to_imported n)) :=
  match n return @Logic.eq Imported.nat (nat_to_imported (Original.LF_DOT_Induction.LF.Induction.double n)) (Imported.Original_LF__DOT__Induction_LF_Induction_double (nat_to_imported n)) with
  | O => Logic.eq_refl
  | Datatypes.S n' => 
    match double_iso_lemma n' in (@Logic.eq _ _ m) 
      return @Logic.eq Imported.nat (Imported.nat_S (Imported.nat_S (nat_to_imported (Original.LF_DOT_Induction.LF.Induction.double n')))) 
             (Imported.nat_S (Imported.nat_S m)) 
    with
    | Logic.eq_refl => Logic.eq_refl
    end
  end.

(* Round trip lemma *)
Fixpoint nat_round_trip (n : Datatypes.nat) : @Logic.eq Datatypes.nat (imported_to_nat (nat_to_imported n)) n :=
  match n return @Logic.eq Datatypes.nat (imported_to_nat (nat_to_imported n)) n with
  | O => Logic.eq_refl
  | Datatypes.S n' => 
    match nat_round_trip n' in (@Logic.eq _ _ m) 
      return @Logic.eq Datatypes.nat (Datatypes.S (imported_to_nat (nat_to_imported n'))) (Datatypes.S m) 
    with
    | Logic.eq_refl => Logic.eq_refl
    end
  end.

(* Prove double commutes in both directions *)
Fixpoint double_imported_std (m : Imported.nat) : 
  @Logic.eq Datatypes.nat 
    (imported_to_nat (Imported.Original_LF__DOT__Induction_LF_Induction_double m))
    (Original.LF_DOT_Induction.LF.Induction.double (imported_to_nat m)) :=
  match m return @Logic.eq Datatypes.nat 
    (imported_to_nat (Imported.Original_LF__DOT__Induction_LF_Induction_double m))
    (Original.LF_DOT_Induction.LF.Induction.double (imported_to_nat m)) with
  | Imported.nat_O => Logic.eq_refl
  | Imported.nat_S m' => 
    match double_imported_std m' in (@Logic.eq _ _ k) 
      return @Logic.eq Datatypes.nat 
        (Datatypes.S (Datatypes.S (imported_to_nat (Imported.Original_LF__DOT__Induction_LF_Induction_double m'))))
        (Datatypes.S (Datatypes.S k))
    with
    | Logic.eq_refl => Logic.eq_refl
    end
  end.

(* Direction: original -> imported *)
Definition Even_to (x1 : nat) (x2 : imported_nat) 
  (Hx : IsomorphismDefinitions.eq (nat_to_imported x1) x2)
  (H : Even_orig x1) : Even_imp x2.
Proof.
  unfold Even_orig, Original.LF_DOT_Logic.LF.Logic.Even in H.
  destruct H as [k Hk].
  unfold Even_imp, Imported.Original_LF__DOT__Logic_LF_Logic_Even.
  apply (Imported.ex_intro Imported.nat 
           (fun n => Imported.Corelib_Init_Logic_eq Imported.nat x2 (Imported.Original_LF__DOT__Induction_LF_Induction_double n))
           (nat_to_imported k)).
  destruct Hx.
  apply logic_eq_to_imported_eq.
  (* Use eq_srect_r to transport the proof along Hk, converting Hk to SProp eq first *)
  exact (eq_srect_r (fun y => @Logic.eq Imported.nat (nat_to_imported y) (Imported.Original_LF__DOT__Induction_LF_Induction_double (nat_to_imported k))) 
                    (double_iso_lemma k) (seq_of_eq Hk)).
Defined.

(* Direction: imported -> original (via SInhabited) *)
Lemma Even_from_SInhabited_core (x1 : nat) (H : Even_imp (nat_to_imported x1)) : SInhabited (Even_orig x1).
Proof.
  unfold Even_imp, Imported.Original_LF__DOT__Logic_LF_Logic_Even in H.
  apply (Imported.ex_indl Imported.nat 
           (fun n => Imported.Corelib_Init_Logic_eq Imported.nat (nat_to_imported x1) (Imported.Original_LF__DOT__Induction_LF_Induction_double n))
           (fun _ => SInhabited (Even_orig x1))).
  - intros m Hm.
    apply sinhabits.
    unfold Even_orig, Original.LF_DOT_Logic.LF.Logic.Even.
    exists (imported_to_nat m).
    pose proof (imported_eq_to_logic_eq Hm) as Hm'.
    transitivity (imported_to_nat (nat_to_imported x1)).
    + symmetry. apply nat_round_trip.
    + transitivity (imported_to_nat (Imported.Original_LF__DOT__Induction_LF_Induction_double m)).
      * f_equal. exact Hm'.
      * apply double_imported_std.
  - exact H.
Defined.

Definition Even_from (x1 : nat) (x2 : imported_nat) 
  (Hx : IsomorphismDefinitions.eq (nat_to_imported x1) x2)
  (H : Even_imp x2) : Even_orig x1.
Proof.
  apply sinhabitant.
  apply Even_from_SInhabited_core.
  destruct Hx.
  exact H.
Defined.

Monomorphic Instance Original_LF__DOT__Logic_LF_Logic_Even_iso : (forall (x1 : nat) (x2 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x1 x2), Iso (Original.LF_DOT_Logic.LF.Logic.Even x1) (imported_Original_LF__DOT__Logic_LF_Logic_Even x2)).
Proof.
  intros x1 x2 Hx.
  destruct Hx as [Hx]. simpl in Hx.
  unfold imported_Original_LF__DOT__Logic_LF_Logic_Even.
  refine {|
    to := @Even_to x1 x2 Hx;
    from := @Even_from x1 x2 Hx;
    to_from := fun _ => IsomorphismDefinitions.eq_refl;
    from_to := _
  |}.
  intro e.
  apply prop_proof_irrel_to_seq.
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.Even := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_Even := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.Even Original_LF__DOT__Logic_LF_Logic_Even_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.Even Imported.Original_LF__DOT__Logic_LF_Logic_Even Original_LF__DOT__Logic_LF_Logic_Even_iso := {}.
