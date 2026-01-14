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

Parameter imported_Original_LF__DOT__Induction_LF_Induction_double : imported_nat -> imported_nat.
Parameter Original_LF__DOT__Induction_LF_Induction_double_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> rel_iso nat_iso (Original.LF_DOT_Induction.LF.Induction.double x1) (imported_Original_LF__DOT__Induction_LF_Induction_double x2).
Existing Instance Original_LF__DOT__Induction_LF_Induction_double_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Induction.LF.Induction.double ?x) => unify x Original_LF__DOT__Induction_LF_Induction_double_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Induction.LF.Induction.double imported_Original_LF__DOT__Induction_LF_Induction_double ?x) => unify x Original_LF__DOT__Induction_LF_Induction_double_iso; constructor : typeclass_instances.


End Interface.