From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.and__iso Isomorphisms.iff__iso.

Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm' : forall x x0 : SProp, imported_iff (imported_and x x0) (imported_and x0 x) := Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm'.

Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm'_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4),
  rel_iso (relax_Iso_Ts_Ps (iff_iso (and_iso hx hx0) (and_iso hx0 hx))) (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.and_comm' x1 x3)
    (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm' x2 x4).
Proof.
  intros x1 x2 hx x3 x4 hx0.
  (* The result types are in SProp, so we just need to show they are structurally the same *)
  unfold rel_iso, relax_Iso_Ts_Ps.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.and_comm' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.and_comm' Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.and_comm' Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm' Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm'_iso := {}.