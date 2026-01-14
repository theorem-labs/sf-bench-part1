From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__negb__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__doit3times__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__negb__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__doit3times__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__negb__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__doit3times__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__negb__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__doit3times__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_test__doit3times' : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Poly_LF_Poly_doit3times (fun x : imported_Original_LF__DOT__Basics_LF_Basics_bool => imported_Original_LF__DOT__Basics_LF_Basics_negb x)
       imported_Original_LF__DOT__Basics_LF_Basics_true)
    imported_Original_LF__DOT__Basics_LF_Basics_false.
Parameter Original_LF__DOT__Poly_LF_Poly_test__doit3times'_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (unwrap_sprop
          (Original_LF__DOT__Poly_LF_Poly_doit3times_iso Original_LF__DOT__Basics_LF_Basics_bool_iso Original.LF_DOT_Basics.LF.Basics.negb
             (fun x : imported_Original_LF__DOT__Basics_LF_Basics_bool => imported_Original_LF__DOT__Basics_LF_Basics_negb x)
             (fun (x1 : Original.LF_DOT_Basics.LF.Basics.bool) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (hx : rel_iso_sort Original_LF__DOT__Basics_LF_Basics_bool_iso x1 x2) =>
              {| unwrap_sprop := Original_LF__DOT__Basics_LF_Basics_negb_iso (unwrap_sprop hx) |})
             Original.LF_DOT_Basics.LF.Basics.true imported_Original_LF__DOT__Basics_LF_Basics_true {| unwrap_sprop := Original_LF__DOT__Basics_LF_Basics_true_iso |}))
       Original_LF__DOT__Basics_LF_Basics_false_iso)
    Original.LF_DOT_Poly.LF.Poly.test_doit3times' imported_Original_LF__DOT__Poly_LF_Poly_test__doit3times'.
Existing Instance Original_LF__DOT__Poly_LF_Poly_test__doit3times'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.test_doit3times' ?x) => unify x Original_LF__DOT__Poly_LF_Poly_test__doit3times'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.test_doit3times' imported_Original_LF__DOT__Poly_LF_Poly_test__doit3times' ?x) => unify x Original_LF__DOT__Poly_LF_Poly_test__doit3times'_iso; constructor : typeclass_instances.


End Interface.