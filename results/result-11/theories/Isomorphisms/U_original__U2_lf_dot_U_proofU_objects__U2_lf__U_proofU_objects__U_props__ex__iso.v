From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

Monomorphic Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex : forall x : Type, (x -> SProp) -> SProp := (@Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex).

Monomorphic Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1 -> Prop) (x4 : x2 -> SProp),
  (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 x5) (x4 x6)) ->
  Iso (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex x3) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex x4).
Proof.
  intros x1 x2 hx x3 x4 HP.
  apply relax_Iso_Ps_Ts.
  unshelve eapply Build_Iso.
  - (* to *)
    intro h. destruct h as [x Hx].
    exact (Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex_ex_intro x2 x4 (to hx x) (to (HP x (to hx x) (rel_iso_refl hx x)) Hx)).
  - (* from *)
    intro h. apply sinhabitant. destruct h as [x Hx].
    exact (sinhabits (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex_intro x3 (from hx x) (from (HP (from hx x) x (rel_iso_unsym (rel_iso_refl (iso_sym hx) x))) Hx))).
  - (* to_from *)
    intro h. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro h. apply seq_of_peq. apply ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex) := {}.
Instance: KnownConstant (@Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex) := {}.
Instance: IsoStatementProofFor (@Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex) Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex) (@Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex) Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex_iso := {}.
