From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__U_true__iso.

Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_p__implies__true : forall x : Type, x -> imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True := Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_p__implies__true.

(* This is an axiom in both systems, so we need to prove that the axioms are compatible.
   Since both sides are axioms (Admitted), and both return True/imported_True,
   and all inhabitants of True/SProp are equal, we can prove rel_iso *)
Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_p__implies__true_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 ->
  rel_iso Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True_iso (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.p_implies_true x1 x3)
    (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_p__implies__true x4).
Proof.
  intros x1 x2 hx x3 x4 Hrel.
  (* rel_iso is: eq (to (from y)) y, and we need eq (to_True ...) ... *)
  (* Since the target is SProp, all elements are equal *)
  unfold rel_iso.
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.p_implies_true := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_p__implies__true := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.p_implies_true Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_p__implies__true_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.p_implies_true Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_p__implies__true Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_p__implies__true_iso := {}.