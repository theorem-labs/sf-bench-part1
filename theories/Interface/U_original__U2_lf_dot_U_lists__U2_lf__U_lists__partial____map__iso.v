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

Parameter imported_Original_LF__DOT__Lists_LF_Lists_partial__map : Type.
Parameter Original_LF__DOT__Lists_LF_Lists_partial__map_iso : Iso Original.LF_DOT_Lists.LF.Lists.partial_map imported_Original_LF__DOT__Lists_LF_Lists_partial__map.
Existing Instance Original_LF__DOT__Lists_LF_Lists_partial__map_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.partial_map ?x) => unify x Original_LF__DOT__Lists_LF_Lists_partial__map_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.partial_map imported_Original_LF__DOT__Lists_LF_Lists_partial__map ?x) => unify x Original_LF__DOT__Lists_LF_Lists_partial__map_iso; constructor : typeclass_instances.


End Interface.