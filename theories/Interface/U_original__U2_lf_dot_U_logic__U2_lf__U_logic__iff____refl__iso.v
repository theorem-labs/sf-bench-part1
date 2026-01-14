From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.iff__iso.

Module Export CodeBlocks.

  Export (hints) Interface.iff__iso.

  Export Interface.iff__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.iff__iso.Args <+ Interface.iff__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_iff__refl : forall x : SProp, imported_iff x x.
Parameter Original_LF__DOT__Logic_LF_Logic_iff__refl_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2), rel_iso (iff_iso hx hx) (Original.LF_DOT_Logic.LF.Logic.iff_refl x1) (imported_Original_LF__DOT__Logic_LF_Logic_iff__refl x2).
Existing Instance Original_LF__DOT__Logic_LF_Logic_iff__refl_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.iff_refl ?x) => unify x Original_LF__DOT__Logic_LF_Logic_iff__refl_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.iff_refl imported_Original_LF__DOT__Logic_LF_Logic_iff__refl ?x) => unify x Original_LF__DOT__Logic_LF_Logic_iff__refl_iso; constructor : typeclass_instances.


End Interface.