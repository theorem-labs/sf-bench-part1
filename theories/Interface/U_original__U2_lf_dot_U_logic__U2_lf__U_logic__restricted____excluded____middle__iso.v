From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.iff__iso Interface.or__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.iff__iso Interface.or__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.iff__iso.CodeBlocks Interface.or__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.iff__iso.Interface <+ Interface.or__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_restricted__excluded__middle : forall (x : SProp) (x0 : imported_Original_LF__DOT__Basics_LF_Basics_bool),
  imported_iff x (imported_Corelib_Init_Logic_eq x0 imported_Original_LF__DOT__Basics_LF_Basics_true) -> imported_or x (x -> imported_False).
Parameter Original_LF__DOT__Logic_LF_Logic_restricted__excluded__middle_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Basics.LF.Basics.bool) (x4 : imported_Original_LF__DOT__Basics_LF_Basics_bool)
    (hx0 : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x3 x4) (x5 : x1 <-> x3 = Original.LF_DOT_Basics.LF.Basics.true)
    (x6 : imported_iff x2 (imported_Corelib_Init_Logic_eq x4 imported_Original_LF__DOT__Basics_LF_Basics_true)),
  rel_iso
    {|
      to := iff_iso hx (Corelib_Init_Logic_eq_iso hx0 Original_LF__DOT__Basics_LF_Basics_true_iso);
      from := from (iff_iso hx (Corelib_Init_Logic_eq_iso hx0 Original_LF__DOT__Basics_LF_Basics_true_iso));
      to_from :=
        fun x : imported_iff x2 (imported_Corelib_Init_Logic_eq x4 imported_Original_LF__DOT__Basics_LF_Basics_true) =>
        to_from (iff_iso hx (Corelib_Init_Logic_eq_iso hx0 Original_LF__DOT__Basics_LF_Basics_true_iso)) x;
      from_to := fun x : x1 <-> x3 = Original.LF_DOT_Basics.LF.Basics.true => seq_p_of_t (from_to (iff_iso hx (Corelib_Init_Logic_eq_iso hx0 Original_LF__DOT__Basics_LF_Basics_true_iso)) x)
    |} x5 x6 ->
  rel_iso
    {|
      to := or_iso hx (IsoArrow hx False_iso);
      from := from (or_iso hx (IsoArrow hx False_iso));
      to_from := fun x : imported_or x2 (x2 -> imported_False) => to_from (or_iso hx (IsoArrow hx False_iso)) x;
      from_to := fun x : x1 \/ ~ x1 => seq_p_of_t (from_to (or_iso hx (IsoArrow hx False_iso)) x)
    |} (Original.LF_DOT_Logic.LF.Logic.restricted_excluded_middle x1 x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_restricted__excluded__middle x6).
Existing Instance Original_LF__DOT__Logic_LF_Logic_restricted__excluded__middle_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.restricted_excluded_middle ?x) => unify x Original_LF__DOT__Logic_LF_Logic_restricted__excluded__middle_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.restricted_excluded_middle imported_Original_LF__DOT__Logic_LF_Logic_restricted__excluded__middle ?x) => unify x Original_LF__DOT__Logic_LF_Logic_restricted__excluded__middle_iso; constructor : typeclass_instances.


End Interface.