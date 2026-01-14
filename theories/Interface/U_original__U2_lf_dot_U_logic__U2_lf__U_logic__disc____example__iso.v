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

Parameter imported_Original_LF__DOT__Logic_LF_Logic_disc__example : forall x : imported_nat, imported_Corelib_Init_Logic_eq imported_0 (imported_S x) -> imported_False.
Parameter Original_LF__DOT__Logic_LF_Logic_disc__example_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : 0 = S x1) (x4 : imported_Corelib_Init_Logic_eq imported_0 (imported_S x2)),
  rel_iso (Corelib_Init_Logic_eq_iso _0_iso (S_iso hx)) x3 x4 -> rel_iso False_iso (Original.LF_DOT_Logic.LF.Logic.disc_example x1 x3) (imported_Original_LF__DOT__Logic_LF_Logic_disc__example x4).
Existing Instance Original_LF__DOT__Logic_LF_Logic_disc__example_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.disc_example ?x) => unify x Original_LF__DOT__Logic_LF_Logic_disc__example_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.disc_example imported_Original_LF__DOT__Logic_LF_Logic_disc__example ?x) => unify x Original_LF__DOT__Logic_LF_Logic_disc__example_iso; constructor : typeclass_instances.


End Interface.