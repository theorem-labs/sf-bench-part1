From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_string__string__iso Interface.bool__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_string__string__iso Interface.bool__iso.

  Export Interface.U_string__string__iso.CodeBlocks Interface.bool__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_string__string__iso.Interface <+ Interface.bool__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Maps_LF_Maps_examplemap : imported_String_string -> imported_bool.
Parameter Original_LF__DOT__Maps_LF_Maps_examplemap_iso : forall (x1 : String.string) (x2 : imported_String_string),
  rel_iso String_string_iso x1 x2 -> rel_iso bool_iso (Original.LF_DOT_Maps.LF.Maps.examplemap x1) (imported_Original_LF__DOT__Maps_LF_Maps_examplemap x2).
Existing Instance Original_LF__DOT__Maps_LF_Maps_examplemap_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Maps.LF.Maps.examplemap ?x) => unify x Original_LF__DOT__Maps_LF_Maps_examplemap_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Maps.LF.Maps.examplemap imported_Original_LF__DOT__Maps_LF_Maps_examplemap ?x) => unify x Original_LF__DOT__Maps_LF_Maps_examplemap_iso; constructor : typeclass_instances.


End Interface.