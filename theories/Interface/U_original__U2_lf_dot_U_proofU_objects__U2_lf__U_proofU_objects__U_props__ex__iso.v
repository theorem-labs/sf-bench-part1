From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

Module Export CodeBlocks.

End CodeBlocks.

Module Type Args. End Args.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex : forall x : Type, (x -> SProp) -> SProp.
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1 -> Prop) (x4 : x2 -> SProp),
  (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 x5) (x4 x6)) ->
  Iso (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex x3) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex x4).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex) ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex) imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex_iso; constructor : typeclass_instances.


End Interface.