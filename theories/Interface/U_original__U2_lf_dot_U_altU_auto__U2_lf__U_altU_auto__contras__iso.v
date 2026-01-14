From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__AltAuto_LF_AltAuto_contras : forall x : SProp, x -> (x -> imported_False) -> imported_Corelib_Init_Logic_eq imported_0 (imported_S imported_0).
Parameter Original_LF__DOT__AltAuto_LF_AltAuto_contras_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 ->
  forall (x5 : ~ x1) (x6 : x2 -> imported_False),
  (forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> rel_iso False_iso (x5 x7) (x6 x8)) ->
  rel_iso (Corelib_Init_Logic_eq_iso _0_iso (S_iso _0_iso)) (Original.LF_DOT_AltAuto.LF.AltAuto.contras x1 x3 x5) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_contras x4 x6).
Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_contras_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.contras ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_contras_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.contras imported_Original_LF__DOT__AltAuto_LF_AltAuto_contras ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_contras_iso; constructor : typeclass_instances.


End Interface.