From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.iff__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__even__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.iff__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__even__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.iff__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__even__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.iff__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__even__iso.Interface <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_even__bool__prop : forall x : imported_nat,
  imported_iff (imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_even x) imported_Original_LF__DOT__Basics_LF_Basics_true)
    (imported_Original_LF__DOT__Logic_LF_Logic_Even x).
Parameter Original_LF__DOT__Logic_LF_Logic_even__bool__prop_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso
    {|
      to := iff_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_even_iso hx) Original_LF__DOT__Basics_LF_Basics_true_iso) (Original_LF__DOT__Logic_LF_Logic_Even_iso hx);
      from := from (iff_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_even_iso hx) Original_LF__DOT__Basics_LF_Basics_true_iso) (Original_LF__DOT__Logic_LF_Logic_Even_iso hx));
      to_from :=
        fun
          x : imported_iff (imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_even x2) imported_Original_LF__DOT__Basics_LF_Basics_true)
                (imported_Original_LF__DOT__Logic_LF_Logic_Even x2) =>
        to_from (iff_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_even_iso hx) Original_LF__DOT__Basics_LF_Basics_true_iso) (Original_LF__DOT__Logic_LF_Logic_Even_iso hx)) x;
      from_to :=
        fun x : Original.LF_DOT_Basics.LF.Basics.even x1 = Original.LF_DOT_Basics.LF.Basics.true <-> Original.LF_DOT_Logic.LF.Logic.Even x1 =>
        seq_p_of_t
          (from_to (iff_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_even_iso hx) Original_LF__DOT__Basics_LF_Basics_true_iso) (Original_LF__DOT__Logic_LF_Logic_Even_iso hx)) x)
    |} (Original.LF_DOT_Logic.LF.Logic.even_bool_prop x1) (imported_Original_LF__DOT__Logic_LF_Logic_even__bool__prop x2).
Existing Instance Original_LF__DOT__Logic_LF_Logic_even__bool__prop_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.even_bool_prop ?x) => unify x Original_LF__DOT__Logic_LF_Logic_even__bool__prop_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.even_bool_prop imported_Original_LF__DOT__Logic_LF_Logic_even__bool__prop ?x) => unify x Original_LF__DOT__Logic_LF_Logic_even__bool__prop_iso; constructor : typeclass_instances.


End Interface.