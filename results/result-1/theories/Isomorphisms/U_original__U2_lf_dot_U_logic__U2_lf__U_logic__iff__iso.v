From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.
From Stdlib Require Import ProofIrrelevance.


Monomorphic Definition imported_Original_LF__DOT__Logic_LF_Logic_iff : SProp -> SProp -> SProp := Imported.Original_LF__DOT__Logic_LF_Logic_iff.

Monomorphic Instance Original_LF__DOT__Logic_LF_Logic_iff_iso : forall (x1 : Prop) (x2 : SProp), Iso x1 x2 -> forall (x3 : Prop) (x4 : SProp), Iso x3 x4 -> Iso (Original.LF_DOT_Logic.LF.Logic.iff x1 x3) (imported_Original_LF__DOT__Logic_LF_Logic_iff x2 x4).
Proof.
  intros x1 x2 hx x3 x4 hx0.
  unfold Original.LF_DOT_Logic.LF.Logic.iff, imported_Original_LF__DOT__Logic_LF_Logic_iff, Imported.Original_LF__DOT__Logic_LF_Logic_iff.
  unshelve econstructor.
  - (* to *)
    intros [H1 H2].
    exact (Imported.iff_mk x2 x4 (fun a => hx0.(to) (H1 (hx.(from) a))) (fun b => hx.(to) (H2 (hx0.(from) b)))).
  - (* from *)
    intros H.
    split.
    + intros a. exact (hx0.(from) (Imported.mp _ _ H (hx.(to) a))).
    + intros b. exact (hx.(from) (Imported.mpr _ _ H (hx0.(to) b))).
  - intros x. apply IsomorphismDefinitions.eq_refl.
  - intros x. apply (IsoEq.seq_of_peq_t (proof_irrelevance _ _ _)).
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.iff := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_iff := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.iff Original_LF__DOT__Logic_LF_Logic_iff_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.iff Imported.Original_LF__DOT__Logic_LF_Logic_iff Original_LF__DOT__Logic_LF_Logic_iff_iso := {}.