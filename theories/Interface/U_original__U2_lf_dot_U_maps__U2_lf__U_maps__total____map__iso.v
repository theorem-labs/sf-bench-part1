From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_string__string__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_string__string__iso.

  Export Interface.U_string__string__iso.CodeBlocks.

#[export] Instance: MustUnfold Original.LF_DOT_Maps.LF.Maps.total_map := {}.

End CodeBlocks.

Module Type Args := Interface.U_string__string__iso.Args <+ Interface.U_string__string__iso.Interface.

Module Type Interface (Import args : Args).

Definition imported_Original_LF__DOT__Maps_LF_Maps_total__map : Type -> Type
  := fun x : Type => imported_String_string -> x.
Definition Original_LF__DOT__Maps_LF_Maps_total__map_iso : forall x1 x2 : Type, Iso x1 x2 -> Iso (Original.LF_DOT_Maps.LF.Maps.total_map x1) (imported_Original_LF__DOT__Maps_LF_Maps_total__map x2)
  := fun (x1 x2 : Type) (hx : Iso x1 x2) => IsoArrow String_string_iso hx.
Existing Instance Original_LF__DOT__Maps_LF_Maps_total__map_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Maps.LF.Maps.total_map ?x) => unify x Original_LF__DOT__Maps_LF_Maps_total__map_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Maps.LF.Maps.total_map imported_Original_LF__DOT__Maps_LF_Maps_total__map ?x) => unify x Original_LF__DOT__Maps_LF_Maps_total__map_iso; constructor : typeclass_instances.


End Interface.