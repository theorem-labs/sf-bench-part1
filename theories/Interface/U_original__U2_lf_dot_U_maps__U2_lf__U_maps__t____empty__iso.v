From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.

  Export Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Maps_LF_Maps_t__empty : forall x : Type, x -> imported_String_string -> x.
Parameter Original_LF__DOT__Maps_LF_Maps_t__empty_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 ->
  forall (x5 : String.string) (x6 : imported_String_string),
  rel_iso String_string_iso x5 x6 -> rel_iso hx (Original.LF_DOT_Maps.LF.Maps.t_empty x3 x5) (imported_Original_LF__DOT__Maps_LF_Maps_t__empty x4 x6).
Existing Instance Original_LF__DOT__Maps_LF_Maps_t__empty_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_Maps.LF.Maps.t_empty) ?x) => unify x Original_LF__DOT__Maps_LF_Maps_t__empty_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_Maps.LF.Maps.t_empty) imported_Original_LF__DOT__Maps_LF_Maps_t__empty ?x) => unify x Original_LF__DOT__Maps_LF_Maps_t__empty_iso; constructor : typeclass_instances.


End Interface.