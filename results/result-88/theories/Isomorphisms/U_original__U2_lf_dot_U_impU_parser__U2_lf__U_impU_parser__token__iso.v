From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


Monomorphic Definition imported_Original_LF__DOT__ImpParser_LF_ImpParser_token : Type := Imported.Original_LF__DOT__ImpParser_LF_ImpParser_token.
Monomorphic Instance Original_LF__DOT__ImpParser_LF_ImpParser_token_iso : Iso Original.LF_DOT_ImpParser.LF.ImpParser.token imported_Original_LF__DOT__ImpParser_LF_ImpParser_token.
Admitted.
Instance: KnownConstant Original.LF_DOT_ImpParser.LF.ImpParser.token := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__ImpParser_LF_ImpParser_token := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_ImpParser.LF.ImpParser.token Original_LF__DOT__ImpParser_LF_ImpParser_token_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ImpParser.LF.ImpParser.token Imported.Original_LF__DOT__ImpParser_LF_ImpParser_token Original_LF__DOT__ImpParser_LF_ImpParser_token_iso := {}.