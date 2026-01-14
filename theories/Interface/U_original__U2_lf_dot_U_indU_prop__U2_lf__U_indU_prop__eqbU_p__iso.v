From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__eqb__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__eqb__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__eqb__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__eqb__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_eqbP : forall x x0 : imported_nat, imported_Original_LF__DOT__IndProp_LF_IndProp_reflect (imported_Corelib_Init_Logic_eq x x0) (imported_Original_LF__DOT__Basics_LF_Basics_eqb x x0).
Parameter Original_LF__DOT__IndProp_LF_IndProp_eqbP_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4),
  rel_iso
    {|
      to := Original_LF__DOT__IndProp_LF_IndProp_reflect_iso (Corelib_Init_Logic_eq_iso hx hx0) (Original_LF__DOT__Basics_LF_Basics_eqb_iso hx hx0);
      from := from (Original_LF__DOT__IndProp_LF_IndProp_reflect_iso (Corelib_Init_Logic_eq_iso hx hx0) (Original_LF__DOT__Basics_LF_Basics_eqb_iso hx hx0));
      to_from :=
        fun x : imported_Original_LF__DOT__IndProp_LF_IndProp_reflect (imported_Corelib_Init_Logic_eq x2 x4) (imported_Original_LF__DOT__Basics_LF_Basics_eqb x2 x4) =>
        to_from (Original_LF__DOT__IndProp_LF_IndProp_reflect_iso (Corelib_Init_Logic_eq_iso hx hx0) (Original_LF__DOT__Basics_LF_Basics_eqb_iso hx hx0)) x;
      from_to :=
        fun x : Original.LF_DOT_IndProp.LF.IndProp.reflect (x1 = x3) (Original.LF_DOT_Basics.LF.Basics.eqb x1 x3) =>
        seq_p_of_t (from_to (Original_LF__DOT__IndProp_LF_IndProp_reflect_iso (Corelib_Init_Logic_eq_iso hx hx0) (Original_LF__DOT__Basics_LF_Basics_eqb_iso hx hx0)) x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.eqbP x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_eqbP x2 x4).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_eqbP_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.eqbP ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_eqbP_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.eqbP imported_Original_LF__DOT__IndProp_LF_IndProp_eqbP ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_eqbP_iso; constructor : typeclass_instances.


End Interface.