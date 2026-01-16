From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


Monomorphic Definition imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp : Type -> Type := Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp.
Monomorphic Instance Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso : forall x1 x2 : Type, Iso x1 x2 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x2).
Admitted.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.reg_exp := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.reg_exp Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.reg_exp Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso := {}.