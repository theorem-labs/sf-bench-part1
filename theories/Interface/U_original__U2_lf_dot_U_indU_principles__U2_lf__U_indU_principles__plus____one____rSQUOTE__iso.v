From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__add__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__add__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_nat__add__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_nat__add__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_plus__one__r' : forall x : imported_nat, imported_Corelib_Init_Logic_eq (imported_Nat_add x (imported_S imported_0)) (imported_S x).
Parameter Original_LF__DOT__IndPrinciples_LF_IndPrinciples_plus__one__r'_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso (Corelib_Init_Logic_eq_iso (Nat_add_iso hx (S_iso _0_iso)) (S_iso hx)) (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.plus_one_r' x1)
    (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_plus__one__r' x2).
Existing Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_plus__one__r'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.plus_one_r' ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_plus__one__r'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.plus_one_r' imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_plus__one__r' ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_plus__one__r'_iso; constructor : typeclass_instances.


End Interface.