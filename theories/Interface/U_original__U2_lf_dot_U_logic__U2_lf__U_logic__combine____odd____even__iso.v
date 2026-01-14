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

Parameter imported_Original_LF__DOT__Logic_LF_Logic_combine__odd__even : (imported_nat -> SProp) -> (imported_nat -> SProp) -> imported_nat -> SProp.
Parameter Original_LF__DOT__Logic_LF_Logic_combine__odd__even_iso : forall (x1 : nat -> Prop) (x2 : imported_nat -> SProp),
  (forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (x1 x3) (x2 x4)) ->
  forall (x3 : nat -> Prop) (x4 : imported_nat -> SProp),
  (forall (x5 : nat) (x6 : imported_nat), rel_iso nat_iso x5 x6 -> Iso (x3 x5) (x4 x6)) ->
  forall (x5 : nat) (x6 : imported_nat),
  rel_iso nat_iso x5 x6 -> Iso (Original.LF_DOT_Logic.LF.Logic.combine_odd_even x1 x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_combine__odd__even x2 x4 x6).
Existing Instance Original_LF__DOT__Logic_LF_Logic_combine__odd__even_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.combine_odd_even ?x) => unify x Original_LF__DOT__Logic_LF_Logic_combine__odd__even_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.combine_odd_even imported_Original_LF__DOT__Logic_LF_Logic_combine__odd__even ?x) => unify x Original_LF__DOT__Logic_LF_Logic_combine__odd__even_iso; constructor : typeclass_instances.


End Interface.