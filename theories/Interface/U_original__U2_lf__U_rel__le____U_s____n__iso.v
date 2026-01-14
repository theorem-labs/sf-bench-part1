From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso Interface.U_s__iso Interface.le__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso Interface.U_s__iso Interface.le__iso.

  Export Interface.nat__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.le__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.le__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF_Rel_le__S__n : forall x x0 : imported_nat, imported_le (imported_S x) (imported_S x0) -> imported_le x x0.
Parameter Original_LF_Rel_le__S__n_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : S x1 <= S x3)
    (x6 : imported_le (imported_S x2) (imported_S x4)),
  rel_iso (le_iso (S_iso hx) (S_iso hx0)) x5 x6 -> rel_iso (le_iso hx hx0) (Original.LF.Rel.le_S_n x1 x3 x5) (imported_Original_LF_Rel_le__S__n x6).
Existing Instance Original_LF_Rel_le__S__n_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF.Rel.le_S_n ?x) => unify x Original_LF_Rel_le__S__n_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF.Rel.le_S_n imported_Original_LF_Rel_le__S__n ?x) => unify x Original_LF_Rel_le__S__n_iso; constructor : typeclass_instances.


End Interface.