From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso.

  Export Interface.nat__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Args <+ Interface.nat__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Auto_LF_Auto_is__fortytwo : imported_nat -> SProp.
Parameter Original_LF__DOT__Auto_LF_Auto_is__fortytwo_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> Iso (Original.LF_DOT_Auto.LF.Auto.is_fortytwo x1) (imported_Original_LF__DOT__Auto_LF_Auto_is__fortytwo x2).
Existing Instance Original_LF__DOT__Auto_LF_Auto_is__fortytwo_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Auto.LF.Auto.is_fortytwo ?x) => unify x Original_LF__DOT__Auto_LF_Auto_is__fortytwo_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Auto.LF.Auto.is_fortytwo imported_Original_LF__DOT__Auto_LF_Auto_is__fortytwo ?x) => unify x Original_LF__DOT__Auto_LF_Auto_is__fortytwo_iso; constructor : typeclass_instances.


End Interface.