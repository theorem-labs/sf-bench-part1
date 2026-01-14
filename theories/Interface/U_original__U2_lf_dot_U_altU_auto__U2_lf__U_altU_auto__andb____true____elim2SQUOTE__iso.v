From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__andb__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__andb__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__andb__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__andb__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__AltAuto_LF_AltAuto_andb__true__elim2' : forall x x0 : imported_Original_LF__DOT__Basics_LF_Basics_bool,
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_andb x x0) imported_Original_LF__DOT__Basics_LF_Basics_true ->
  imported_Corelib_Init_Logic_eq x0 imported_Original_LF__DOT__Basics_LF_Basics_true.
Parameter Original_LF__DOT__AltAuto_LF_AltAuto_andb__true__elim2'_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.bool) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (hx : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x1 x2)
    (x3 : Original.LF_DOT_Basics.LF.Basics.bool) (x4 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (hx0 : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x3 x4)
    (x5 : Original.LF_DOT_Basics.LF.Basics.andb x1 x3 = Original.LF_DOT_Basics.LF.Basics.true)
    (x6 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_andb x2 x4) imported_Original_LF__DOT__Basics_LF_Basics_true),
  rel_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_andb_iso hx hx0) Original_LF__DOT__Basics_LF_Basics_true_iso) x5 x6 ->
  rel_iso (Corelib_Init_Logic_eq_iso hx0 Original_LF__DOT__Basics_LF_Basics_true_iso) (Original.LF_DOT_AltAuto.LF.AltAuto.andb_true_elim2' x1 x3 x5)
    (imported_Original_LF__DOT__AltAuto_LF_AltAuto_andb__true__elim2' x6).
Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_andb__true__elim2'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.andb_true_elim2' ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_andb__true__elim2'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.andb_true_elim2' imported_Original_LF__DOT__AltAuto_LF_AltAuto_andb__true__elim2' ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_andb__true__elim2'_iso; constructor : typeclass_instances.


End Interface.