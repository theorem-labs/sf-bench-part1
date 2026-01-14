From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.option__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__partial____map__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.option__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__partial____map__iso.

  Export Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.option__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__partial____map__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.option__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__partial____map__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Maps_LF_Maps_update : forall x : Type, (imported_String_string -> imported_option x) -> imported_String_string -> x -> imported_String_string -> imported_option x.
Parameter Original_LF__DOT__Maps_LF_Maps_update_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Maps.LF.Maps.partial_map x1) (x4 : imported_String_string -> imported_option x2),
  (forall (x5 : String.string) (x6 : imported_String_string), rel_iso String_string_iso x5 x6 -> rel_iso (option_iso hx) (x3 x5) (x4 x6)) ->
  forall (x5 : String.string) (x6 : imported_String_string),
  rel_iso String_string_iso x5 x6 ->
  forall (x7 : x1) (x8 : x2),
  rel_iso hx x7 x8 ->
  forall (x9 : String.string) (x10 : imported_String_string),
  rel_iso String_string_iso x9 x10 -> rel_iso (option_iso hx) (Original.LF_DOT_Maps.LF.Maps.update x3 x5 x7 x9) (imported_Original_LF__DOT__Maps_LF_Maps_update x4 x6 x8 x10).
Existing Instance Original_LF__DOT__Maps_LF_Maps_update_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_Maps.LF.Maps.update) ?x) => unify x Original_LF__DOT__Maps_LF_Maps_update_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_Maps.LF.Maps.update) imported_Original_LF__DOT__Maps_LF_Maps_update ?x) => unify x Original_LF__DOT__Maps_LF_Maps_update_iso; constructor : typeclass_instances.


End Interface.