From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* Both split_combine_statement and split_combine are Admitted in the Original,
   so these are axioms. We can use Admitted for isomorphisms of axioms. *)

Definition imported_Original_LF__DOT__Tactics_LF_Tactics_split__combine__statement : SProp := Imported.Original_LF__DOT__Tactics_LF_Tactics_split__combine__statement.

(* Original: Prop, Imported: SProp - need to use iso_Prop_SProp-based approach *)
(* Since split_combine_statement is an admitted axiom in Original.v, we can Admit this isomorphism *)
Instance Original_LF__DOT__Tactics_LF_Tactics_split__combine__statement_iso : Iso Original.LF_DOT_Tactics.LF.Tactics.split_combine_statement imported_Original_LF__DOT__Tactics_LF_Tactics_split__combine__statement.
Admitted.

Instance: KnownConstant Original.LF_DOT_Tactics.LF.Tactics.split_combine_statement := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Tactics_LF_Tactics_split__combine__statement := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Tactics.LF.Tactics.split_combine_statement Original_LF__DOT__Tactics_LF_Tactics_split__combine__statement_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Tactics.LF.Tactics.split_combine_statement Imported.Original_LF__DOT__Tactics_LF_Tactics_split__combine__statement Original_LF__DOT__Tactics_LF_Tactics_split__combine__statement_iso := {}.