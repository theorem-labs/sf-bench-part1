From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.nat__iso Interface.U_s__iso Interface.le__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.nat__iso Interface.U_s__iso Interface.le__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.le__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.le__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF_Rel_le__Sn__n : forall x : imported_nat, imported_le (imported_S x) x -> imported_False.
Parameter Original_LF_Rel_le__Sn__n_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : S x1 <= x1) (x4 : imported_le (imported_S x2) x2),
  rel_iso (le_iso (S_iso hx) hx) x3 x4 -> rel_iso False_iso (Original.LF.Rel.le_Sn_n x1 x3) (imported_Original_LF_Rel_le__Sn__n x4).
Existing Instance Original_LF_Rel_le__Sn__n_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF.Rel.le_Sn_n ?x) => unify x Original_LF_Rel_le__Sn__n_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF.Rel.le_Sn_n imported_Original_LF_Rel_le__Sn__n ?x) => unify x Original_LF_Rel_le__Sn__n_iso; constructor : typeclass_instances.


End Interface.