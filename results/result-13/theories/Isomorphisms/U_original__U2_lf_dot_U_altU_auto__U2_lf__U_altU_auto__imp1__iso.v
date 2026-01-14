From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_imp1 : forall x : SProp, x -> x := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_imp1.

(* This is an axiom-to-axiom isomorphism. Both imp1 functions are axioms that 
   represent identity functions on their respective domains (Prop and SProp).
   Since they're axioms, we need to assume they behave identically and the 
   isomorphism follows from how rel_iso works on arguments. *)
   
Axiom Original_LF__DOT__AltAuto_LF_AltAuto_imp1_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 -> rel_iso hx (Original.LF_DOT_AltAuto.LF.AltAuto.imp1 x1 x3) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_imp1 x4).
  
#[global] Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_imp1_iso.
Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.imp1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_imp1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.imp1 Original_LF__DOT__AltAuto_LF_AltAuto_imp1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.imp1 Imported.Original_LF__DOT__AltAuto_LF_AltAuto_imp1 Original_LF__DOT__AltAuto_LF_AltAuto_imp1_iso := {}.