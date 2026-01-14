From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False : SProp := Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False.

(* Both are empty types (False), so we can create an isomorphism *)
(* We use the sind principle from Original (eliminates into SProp) and recl from Imported *)
Definition to_imported : Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.False -> imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False :=
  Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.False_sind _.

Definition from_imported : imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False -> Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.False :=
  fun x => Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False_recl (fun _ => Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.False) x.

Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False_iso : Iso Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.False imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False.
Proof.
  unshelve econstructor.
  - exact to_imported.
  - exact from_imported.
  - intro x. apply Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False_indl.
  - intro x. destruct x.
Defined.
Instance: KnownConstant Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.False Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.False Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False_iso := {}.