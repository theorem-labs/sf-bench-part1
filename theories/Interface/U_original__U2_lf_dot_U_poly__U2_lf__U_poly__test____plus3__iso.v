From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__plus3__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__plus3__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__plus3__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__plus3__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_test__plus3 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_plus3 (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))))
    (imported_S (imported_S (imported_S (iterate1 imported_S 4 imported_0)))).
Parameter Original_LF__DOT__Poly_LF_Poly_test__plus3_iso : rel_iso
    (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Poly_LF_Poly_plus3_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso)))))
       (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 4 0 imported_0 _0_iso)))))
    Original.LF_DOT_Poly.LF.Poly.test_plus3 imported_Original_LF__DOT__Poly_LF_Poly_test__plus3.
Existing Instance Original_LF__DOT__Poly_LF_Poly_test__plus3_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.test_plus3 ?x) => unify x Original_LF__DOT__Poly_LF_Poly_test__plus3_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.test_plus3 imported_Original_LF__DOT__Poly_LF_Poly_test__plus3 ?x) => unify x Original_LF__DOT__Poly_LF_Poly_test__plus3_iso; constructor : typeclass_instances.


End Interface.