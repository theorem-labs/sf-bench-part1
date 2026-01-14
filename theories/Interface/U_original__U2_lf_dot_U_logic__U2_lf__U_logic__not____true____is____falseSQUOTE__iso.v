From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_not__true__is__false' : forall x : imported_Original_LF__DOT__Basics_LF_Basics_bool,
  (imported_Corelib_Init_Logic_eq x imported_Original_LF__DOT__Basics_LF_Basics_true -> imported_False) -> imported_Corelib_Init_Logic_eq x imported_Original_LF__DOT__Basics_LF_Basics_false.
Parameter Original_LF__DOT__Logic_LF_Logic_not__true__is__false'_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.bool) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (hx : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x1 x2)
    (x3 : x1 <> Original.LF_DOT_Basics.LF.Basics.true) (x4 : imported_Corelib_Init_Logic_eq x2 imported_Original_LF__DOT__Basics_LF_Basics_true -> imported_False),
  (forall (x5 : x1 = Original.LF_DOT_Basics.LF.Basics.true) (x6 : imported_Corelib_Init_Logic_eq x2 imported_Original_LF__DOT__Basics_LF_Basics_true),
   rel_iso (Corelib_Init_Logic_eq_iso hx Original_LF__DOT__Basics_LF_Basics_true_iso) x5 x6 -> rel_iso False_iso (x3 x5) (x4 x6)) ->
  rel_iso (Corelib_Init_Logic_eq_iso hx Original_LF__DOT__Basics_LF_Basics_false_iso) (Original.LF_DOT_Logic.LF.Logic.not_true_is_false' x1 x3)
    (imported_Original_LF__DOT__Logic_LF_Logic_not__true__is__false' x4).
Existing Instance Original_LF__DOT__Logic_LF_Logic_not__true__is__false'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.not_true_is_false' ?x) => unify x Original_LF__DOT__Logic_LF_Logic_not__true__is__false'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.not_true_is_false' imported_Original_LF__DOT__Logic_LF_Logic_not__true__is__false' ?x) => unify x Original_LF__DOT__Logic_LF_Logic_not__true__is__false'_iso; constructor : typeclass_instances.


End Interface.