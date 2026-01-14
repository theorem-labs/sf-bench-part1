From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.or__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_or__commut : forall x x0 : SProp, imported_or x x0 -> imported_or x0 x := Imported.Original_LF__DOT__Logic_LF_Logic_or__commut.

(* This isomorphism is about the axiom or_commut. Since both Original.or_commut
   and Imported.Original_LF__DOT__Logic_LF_Logic_or__commut are axioms,
   this isomorphism is itself axiomatic. The allowed axioms list includes
   Original_LF__DOT__Logic_LF_Logic_or__commut_iso, so we can admit this. *)
Instance Original_LF__DOT__Logic_LF_Logic_or__commut_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : x1 \/ x3) (x6 : imported_or x2 x4),
  rel_iso (relax_Iso_Ts_Ps (or_iso hx hx0)) x5 x6 ->
  rel_iso (relax_Iso_Ts_Ps (or_iso hx0 hx)) (Original.LF_DOT_Logic.LF.Logic.or_commut x1 x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_or__commut x6).
Admitted.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.or_commut := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_or__commut := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.or_commut Original_LF__DOT__Logic_LF_Logic_or__commut_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.or_commut Imported.Original_LF__DOT__Logic_LF_Logic_or__commut Original_LF__DOT__Logic_LF_Logic_or__commut_iso := {}.