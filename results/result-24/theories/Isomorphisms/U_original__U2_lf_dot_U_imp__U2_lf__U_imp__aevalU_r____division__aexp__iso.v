From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
#[local] Set Printing Coercions.

From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Monomorphic Definition imported_Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp : Type := Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp.

Fixpoint aexp_to (x : Original.LF_DOT_Imp.LF.Imp.aevalR_division.aexp) : imported_Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp :=
  match x with
  | Original.LF_DOT_Imp.LF.Imp.aevalR_division.ANum n => Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_ANum (to nat_iso n)
  | Original.LF_DOT_Imp.LF.Imp.aevalR_division.APlus a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_APlus (aexp_to a1) (aexp_to a2)
  | Original.LF_DOT_Imp.LF.Imp.aevalR_division.AMinus a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_AMinus (aexp_to a1) (aexp_to a2)
  | Original.LF_DOT_Imp.LF.Imp.aevalR_division.AMult a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_AMult (aexp_to a1) (aexp_to a2)
  | Original.LF_DOT_Imp.LF.Imp.aevalR_division.ADiv a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_ADiv (aexp_to a1) (aexp_to a2)
  end.

Fixpoint aexp_from (x : imported_Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp) : Original.LF_DOT_Imp.LF.Imp.aevalR_division.aexp :=
  match x with
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_ANum n => Original.LF_DOT_Imp.LF.Imp.aevalR_division.ANum (from nat_iso n)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_APlus a1 a2 => Original.LF_DOT_Imp.LF.Imp.aevalR_division.APlus (aexp_from a1) (aexp_from a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_AMinus a1 a2 => Original.LF_DOT_Imp.LF.Imp.aevalR_division.AMinus (aexp_from a1) (aexp_from a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_AMult a1 a2 => Original.LF_DOT_Imp.LF.Imp.aevalR_division.AMult (aexp_from a1) (aexp_from a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_ADiv a1 a2 => Original.LF_DOT_Imp.LF.Imp.aevalR_division.ADiv (aexp_from a1) (aexp_from a2)
  end.

Monomorphic Instance Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_iso : Iso Original.LF_DOT_Imp.LF.Imp.aevalR_division.aexp imported_Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp.
Proof.
  refine (Build_Iso aexp_to aexp_from _ _).
  - intro x. induction x; simpl.
    + exact (f_equal Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_ANum (to_from nat_iso _)).
    + exact (f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_APlus IHx1 IHx2).
    + exact (f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_AMinus IHx1 IHx2).
    + exact (f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_AMult IHx1 IHx2).
    + exact (f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_ADiv IHx1 IHx2).
  - intro x. induction x; simpl.
    + exact (f_equal Original.LF_DOT_Imp.LF.Imp.aevalR_division.ANum (from_to nat_iso _)).
    + exact (f_equal2 Original.LF_DOT_Imp.LF.Imp.aevalR_division.APlus IHx1 IHx2).
    + exact (f_equal2 Original.LF_DOT_Imp.LF.Imp.aevalR_division.AMinus IHx1 IHx2).
    + exact (f_equal2 Original.LF_DOT_Imp.LF.Imp.aevalR_division.AMult IHx1 IHx2).
    + exact (f_equal2 Original.LF_DOT_Imp.LF.Imp.aevalR_division.ADiv IHx1 IHx2).
Defined.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.aevalR_division.aexp := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.aevalR_division.aexp Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.aevalR_division.aexp Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_iso := {}.
