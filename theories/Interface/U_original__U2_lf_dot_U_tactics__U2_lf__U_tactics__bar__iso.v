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

Parameter imported_Original_LF__DOT__Tactics_LF_Tactics_bar : imported_nat -> imported_nat.
Parameter Original_LF__DOT__Tactics_LF_Tactics_bar_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> rel_iso nat_iso (Original.LF_DOT_Tactics.LF.Tactics.bar x1) (imported_Original_LF__DOT__Tactics_LF_Tactics_bar x2).
Existing Instance Original_LF__DOT__Tactics_LF_Tactics_bar_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Tactics.LF.Tactics.bar ?x) => unify x Original_LF__DOT__Tactics_LF_Tactics_bar_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Tactics.LF.Tactics.bar imported_Original_LF__DOT__Tactics_LF_Tactics_bar ?x) => unify x Original_LF__DOT__Tactics_LF_Tactics_bar_iso; constructor : typeclass_instances.


End Interface.