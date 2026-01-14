From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U_false__iso.

(* not is exported from Lean as Original_LF__DOT__Logic_LF_Logic_not *)
Definition imported_Original_LF__DOT__Logic_LF_Logic_not : SProp -> SProp := Imported.Original_LF__DOT__Logic_LF_Logic_not.
Instance Original_LF__DOT__Logic_LF_Logic_not_iso : forall (x1 : Prop) (x2 : SProp), Iso x1 x2 -> Iso (Original.LF_DOT_Logic.LF.Logic.not x1) (imported_Original_LF__DOT__Logic_LF_Logic_not x2)
  := fun (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) => IsoArrow hx (relax_Iso_Ts_Ps Original_False_iso).

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.not := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_not := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.not Original_LF__DOT__Logic_LF_Logic_not_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.not Imported.Original_LF__DOT__Logic_LF_Logic_not Original_LF__DOT__Logic_LF_Logic_not_iso := {}.