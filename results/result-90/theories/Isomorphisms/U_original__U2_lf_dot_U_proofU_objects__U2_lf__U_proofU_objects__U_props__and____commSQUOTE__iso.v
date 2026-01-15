From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.and__iso Isomorphisms.iff__iso Isomorphisms.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__and____commSQUOTE____aux__iso.

(* and_comm' : P /\ Q <-> Q /\ P *)
(* Built from and_comm'_aux applied twice *)

Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__commSQUOTE : forall x x0 : SProp, imported_iff (imported_and x x0) (imported_and x0 x) := Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__commSQUOTE.

Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__commSQUOTE_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4),
  rel_iso (relax_Iso_Ts_Ps (iff_iso (and_iso hx hx0) (and_iso hx0 hx))) (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.and_comm' x1 x3)
    (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__commSQUOTE x2 x4).
Proof.
  intros x1 x2 hx x3 x4 hx0.
  constructor.
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.and_comm' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__commSQUOTE := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.and_comm' Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__commSQUOTE_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.and_comm' Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__commSQUOTE Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__commSQUOTE_iso := {}.

(* Aliases for checker compatibility *)
Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm' := imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__commSQUOTE.
Definition Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm'_iso := Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__commSQUOTE_iso.