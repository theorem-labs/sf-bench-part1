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

Parameter imported_Original_LF__DOT__AltAuto_LF_AltAuto_sat__ex1 : imported_Corelib_Init_Logic_eq (imported_Nat_add (imported_S imported_0) (imported_S imported_0)) (imported_S (imported_S imported_0)).
Parameter Original_LF__DOT__AltAuto_LF_AltAuto_sat__ex1_iso : rel_iso (Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso _0_iso) (S_iso _0_iso)) (S_iso (S_iso _0_iso))) Original.LF_DOT_AltAuto.LF.AltAuto.sat_ex1
    imported_Original_LF__DOT__AltAuto_LF_AltAuto_sat__ex1.
Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_sat__ex1_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.sat_ex1 ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_sat__ex1_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.sat_ex1 imported_Original_LF__DOT__AltAuto_LF_AltAuto_sat__ex1 ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_sat__ex1_iso; constructor : typeclass_instances.


End Interface.