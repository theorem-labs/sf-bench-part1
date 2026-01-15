From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


Monomorphic Definition imported_Original_LF__DOT__ImpParser_LF_ImpParser_optionE : Type -> Type := Imported.Original_LF__DOT__ImpParser_LF_ImpParser_optionE.
Monomorphic Instance Original_LF__DOT__ImpParser_LF_ImpParser_optionE_iso : forall x1 x2 : Type, Iso x1 x2 -> Iso (Original.LF_DOT_ImpParser.LF.ImpParser.optionE x1) (imported_Original_LF__DOT__ImpParser_LF_ImpParser_optionE x2).
Admitted.
Instance: KnownConstant Original.LF_DOT_ImpParser.LF.ImpParser.optionE := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__ImpParser_LF_ImpParser_optionE := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_ImpParser.LF.ImpParser.optionE Original_LF__DOT__ImpParser_LF_ImpParser_optionE_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ImpParser.LF.ImpParser.optionE Imported.Original_LF__DOT__ImpParser_LF_ImpParser_optionE Original_LF__DOT__ImpParser_LF_ImpParser_optionE_iso := {}.