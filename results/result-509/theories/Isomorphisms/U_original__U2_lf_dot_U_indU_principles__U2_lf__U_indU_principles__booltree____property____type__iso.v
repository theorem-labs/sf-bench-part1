From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree__iso.

(* The property_type is imported_booltree -> SProp (from Lean's Prop via lean4export) *)
(* We use iso_Prop_SProp to bridge Rocq's Prop and SProp *)
Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__property__type : Type := 
  Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__property__type.

(* The isomorphism uses IsoArrow with iso_Prop_SProp to go from (booltree -> Prop) to (imported_booltree -> SProp) *)
Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__property__type_iso : Iso Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree_property_type imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__property__type
  := IsoArrow Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_iso iso_Prop_SProp.

Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree_property_type := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__property__type := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree_property_type Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__property__type_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree_property_type Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__property__type Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__property__type_iso := {}.