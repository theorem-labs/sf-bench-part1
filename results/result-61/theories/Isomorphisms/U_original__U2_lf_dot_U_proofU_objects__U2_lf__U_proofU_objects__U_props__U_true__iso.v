From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True : SProp := Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True.

(* Define the isomorphism between Original.True and Imported.True *)
(* Both are unit types (single constructor with no arguments) *)
Definition to_True : Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.True -> imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True :=
  fun _ => Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True_I.

Definition from_True : imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True -> Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.True :=
  fun _ => Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.I.

Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True_iso : Iso Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.True imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True.
Proof.
  refine (Build_Iso to_True from_True _ _).
  - (* to_from: for all y, to(from(y)) = y *)
    (* Since imported_True is SProp, all inhabitants are equal *)
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: for all x, from(to(x)) = x *)
    intro x. destruct x. apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.True Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.True Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True_iso := {}.