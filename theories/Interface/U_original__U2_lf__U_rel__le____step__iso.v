From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso Interface.U_s__iso Interface.le__iso Interface.lt__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso Interface.U_s__iso Interface.le__iso Interface.lt__iso.

  Export Interface.nat__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.le__iso.CodeBlocks Interface.lt__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.le__iso.Interface <+ Interface.lt__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF_Rel_le__step : forall x x0 x1 : imported_nat, imported_lt x x0 -> imported_le x0 (imported_S x1) -> imported_le x x1.
Parameter Original_LF_Rel_le__step_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : x1 < x3) (x8 : imported_lt x2 x4),
  rel_iso (lt_iso hx hx0) x7 x8 ->
  forall (x9 : x3 <= S x5) (x10 : imported_le x4 (imported_S x6)),
  rel_iso (le_iso hx0 (S_iso hx1)) x9 x10 -> rel_iso (le_iso hx hx1) (Original.LF.Rel.le_step x1 x3 x5 x7 x9) (imported_Original_LF_Rel_le__step x8 x10).
Existing Instance Original_LF_Rel_le__step_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF.Rel.le_step ?x) => unify x Original_LF_Rel_le__step_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF.Rel.le_step imported_Original_LF_Rel_le__step ?x) => unify x Original_LF_Rel_le__step_iso; constructor : typeclass_instances.


End Interface.