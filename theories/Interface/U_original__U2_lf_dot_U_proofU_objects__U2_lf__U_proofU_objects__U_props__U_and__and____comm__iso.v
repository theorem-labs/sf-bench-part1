From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.and__iso Interface.iff__iso.

Module Export CodeBlocks.

  Export (hints) Interface.and__iso Interface.iff__iso.

  Export Interface.and__iso.CodeBlocks Interface.iff__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.and__iso.Interface <+ Interface.iff__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_And_and__comm : forall x x0 : SProp, imported_iff (imported_and x x0) (imported_and x0 x).
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_And_and__comm_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4),
  rel_iso (relax_Iso_Ts_Ps (iff_iso (and_iso hx hx0) (and_iso hx0 hx))) (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.And.and_comm x1 x3)
    (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_And_and__comm x2 x4).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_And_and__comm_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.And.and_comm ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_And_and__comm_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.And.and_comm imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_And_and__comm ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_And_and__comm_iso; constructor : typeclass_instances.


End Interface.