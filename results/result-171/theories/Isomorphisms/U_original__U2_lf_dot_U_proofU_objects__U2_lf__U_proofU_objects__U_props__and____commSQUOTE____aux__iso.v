From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.and__iso.

Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm'__aux : forall x x0 : SProp, imported_and x x0 -> imported_and x0 x := Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm'__aux.

Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm'__aux_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : x1 /\ x3) (x6 : imported_and x2 x4),
  rel_iso (relax_Iso_Ts_Ps (and_iso hx hx0)) x5 x6 ->
  rel_iso (relax_Iso_Ts_Ps (and_iso hx0 hx)) (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.and_comm'_aux x1 x3 x5)
    (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm'__aux x6).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 Hrel.
  (* rel_iso requires proving the two are isomorphic via the and_iso *)
  (* The statement says: applying and_comm'_aux to x5 is isomorphic to applying it to x6 *)
  (* Since we're in SProp, we just need the result types to be isomorphic *)
  unfold rel_iso, relax_Iso_Ts_Ps.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.and_comm'_aux := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm'__aux := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.and_comm'_aux Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm'__aux_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.and_comm'_aux Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm'__aux Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm'__aux_iso := {}.