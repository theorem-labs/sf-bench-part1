From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__add__iso Interface.U_nat__pred__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__add__iso Interface.U_nat__pred__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_nat__add__iso.CodeBlocks Interface.U_nat__pred__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_nat__add__iso.Interface <+ Interface.U_nat__pred__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_function__equality__ex1 : imported_Corelib_Init_Logic_eq (fun x2 : imported_nat => imported_Nat_add (imported_S (imported_S (imported_S imported_0))) x2)
    (fun x2 : imported_nat => imported_Nat_add (imported_Nat_pred (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0))))) x2).
Parameter Original_LF__DOT__Logic_LF_Logic_function__equality__ex1_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (IsoFunND (fun x : nat => 3 + x) (fun x2 : imported_nat => imported_Nat_add (imported_S (imported_S (imported_S imported_0))) x2)
          (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) => Nat_add_iso (S_iso (S_iso (S_iso _0_iso))) hx))
       (IsoFunND (fun x : nat => Nat.pred 4 + x) (fun x2 : imported_nat => imported_Nat_add (imported_Nat_pred (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0))))) x2)
          (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) => Nat_add_iso (Nat_pred_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso))))) hx)))
    Original.LF_DOT_Logic.LF.Logic.function_equality_ex1 imported_Original_LF__DOT__Logic_LF_Logic_function__equality__ex1.
Existing Instance Original_LF__DOT__Logic_LF_Logic_function__equality__ex1_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.function_equality_ex1 ?x) => unify x Original_LF__DOT__Logic_LF_Logic_function__equality__ex1_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.function_equality_ex1 imported_Original_LF__DOT__Logic_LF_Logic_function__equality__ex1 ?x) => unify x Original_LF__DOT__Logic_LF_Logic_function__equality__ex1_iso; constructor : typeclass_instances.


End Interface.