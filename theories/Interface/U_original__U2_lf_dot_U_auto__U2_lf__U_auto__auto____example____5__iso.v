From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Auto_LF_Auto_auto__example__5 : imported_Corelib_Init_Logic_eq (imported_S (imported_S imported_0)) (imported_S (imported_S imported_0)).
Parameter Original_LF__DOT__Auto_LF_Auto_auto__example__5_iso : rel_iso (Corelib_Init_Logic_eq_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) Original.LF_DOT_Auto.LF.Auto.auto_example_5 imported_Original_LF__DOT__Auto_LF_Auto_auto__example__5.
Existing Instance Original_LF__DOT__Auto_LF_Auto_auto__example__5_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Auto.LF.Auto.auto_example_5 ?x) => unify x Original_LF__DOT__Auto_LF_Auto_auto__example__5_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Auto.LF.Auto.auto_example_5 imported_Original_LF__DOT__Auto_LF_Auto_auto__example__5 ?x) => unify x Original_LF__DOT__Auto_LF_Auto_auto__example__5_iso; constructor : typeclass_instances.


End Interface.