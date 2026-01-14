From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.iff__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.iff__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.iff__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.iff__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_reflect__iff : forall (x : SProp) (x0 : imported_Original_LF__DOT__Basics_LF_Basics_bool),
  imported_Original_LF__DOT__IndProp_LF_IndProp_reflect x x0 -> imported_iff x (imported_Corelib_Init_Logic_eq x0 imported_Original_LF__DOT__Basics_LF_Basics_true).
Parameter Original_LF__DOT__IndProp_LF_IndProp_reflect__iff_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Basics.LF.Basics.bool) (x4 : imported_Original_LF__DOT__Basics_LF_Basics_bool)
    (hx0 : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x3 x4) (x5 : Original.LF_DOT_IndProp.LF.IndProp.reflect x1 x3) (x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_reflect x2 x4),
  rel_iso
    {|
      to := Original_LF__DOT__IndProp_LF_IndProp_reflect_iso hx hx0;
      from := from (Original_LF__DOT__IndProp_LF_IndProp_reflect_iso hx hx0);
      to_from := fun x : imported_Original_LF__DOT__IndProp_LF_IndProp_reflect x2 x4 => to_from (Original_LF__DOT__IndProp_LF_IndProp_reflect_iso hx hx0) x;
      from_to := fun x : Original.LF_DOT_IndProp.LF.IndProp.reflect x1 x3 => seq_p_of_t (from_to (Original_LF__DOT__IndProp_LF_IndProp_reflect_iso hx hx0) x)
    |} x5 x6 ->
  rel_iso
    {|
      to := iff_iso hx (Corelib_Init_Logic_eq_iso hx0 Original_LF__DOT__Basics_LF_Basics_true_iso);
      from := from (iff_iso hx (Corelib_Init_Logic_eq_iso hx0 Original_LF__DOT__Basics_LF_Basics_true_iso));
      to_from :=
        fun x : imported_iff x2 (imported_Corelib_Init_Logic_eq x4 imported_Original_LF__DOT__Basics_LF_Basics_true) =>
        to_from (iff_iso hx (Corelib_Init_Logic_eq_iso hx0 Original_LF__DOT__Basics_LF_Basics_true_iso)) x;
      from_to := fun x : x1 <-> x3 = Original.LF_DOT_Basics.LF.Basics.true => seq_p_of_t (from_to (iff_iso hx (Corelib_Init_Logic_eq_iso hx0 Original_LF__DOT__Basics_LF_Basics_true_iso)) x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.reflect_iff x1 x3 x5) (imported_Original_LF__DOT__IndProp_LF_IndProp_reflect__iff x6).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_reflect__iff_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.reflect_iff ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_reflect__iff_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.reflect_iff imported_Original_LF__DOT__IndProp_LF_IndProp_reflect__iff ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_reflect__iff_iso; constructor : typeclass_instances.


End Interface.