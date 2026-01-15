From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.

From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Monomorphic Definition imported_Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp : Type := Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp.

Fixpoint aexp_to (a : Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp) : imported_Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp :=
  match a with
  | Original.LF_DOT_Imp.LF.Imp.aevalR_extended.AAny => Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_AAny
  | Original.LF_DOT_Imp.LF.Imp.aevalR_extended.ANum n => Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_ANum (nat_iso n)
  | Original.LF_DOT_Imp.LF.Imp.aevalR_extended.APlus a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_APlus (aexp_to a1) (aexp_to a2)
  | Original.LF_DOT_Imp.LF.Imp.aevalR_extended.AMinus a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_AMinus (aexp_to a1) (aexp_to a2)
  | Original.LF_DOT_Imp.LF.Imp.aevalR_extended.AMult a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_AMult (aexp_to a1) (aexp_to a2)
  end.

Fixpoint aexp_from (a : imported_Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp) : Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp :=
  match a with
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_AAny => Original.LF_DOT_Imp.LF.Imp.aevalR_extended.AAny
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_ANum n => Original.LF_DOT_Imp.LF.Imp.aevalR_extended.ANum (from nat_iso n)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_APlus a1 a2 => Original.LF_DOT_Imp.LF.Imp.aevalR_extended.APlus (aexp_from a1) (aexp_from a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_AMinus a1 a2 => Original.LF_DOT_Imp.LF.Imp.aevalR_extended.AMinus (aexp_from a1) (aexp_from a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_AMult a1 a2 => Original.LF_DOT_Imp.LF.Imp.aevalR_extended.AMult (aexp_from a1) (aexp_from a2)
  end.

Lemma aexp_to_from_aux : forall a, Logic.eq (aexp_to (aexp_from a)) a.
Proof.
  fix IH 1. destruct a; cbn -[to from]; try reflexivity.
  - f_equal. apply eq_of_seq. apply to_from.
  - f_equal; apply IH.
  - f_equal; apply IH.
  - f_equal; apply IH.
Defined.

Lemma aexp_to_from : forall a, IsomorphismDefinitions.eq (aexp_to (aexp_from a)) a.
Proof. intro. apply IsoEq.seq_of_eq. apply aexp_to_from_aux. Defined.

Lemma aexp_from_to_aux : forall a, Logic.eq (aexp_from (aexp_to a)) a.
Proof.
  fix IH 1. destruct a; cbn -[to from]; try reflexivity.
  - f_equal. apply eq_of_seq. apply from_to.
  - f_equal; apply IH.
  - f_equal; apply IH.
  - f_equal; apply IH.
Defined.

Lemma aexp_from_to : forall a, IsomorphismDefinitions.eq (aexp_from (aexp_to a)) a.
Proof. intro. apply IsoEq.seq_of_eq. apply aexp_from_to_aux. Defined.

Monomorphic Instance Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_iso : Iso Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp imported_Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp.
Proof.
  exact (@Build_Iso _ _ aexp_to aexp_from aexp_to_from aexp_from_to).
Defined.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_iso := {}.