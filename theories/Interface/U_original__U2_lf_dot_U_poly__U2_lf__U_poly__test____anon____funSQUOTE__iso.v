From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__doit3times__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__mul__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__doit3times__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__mul__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__doit3times__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_nat__mul__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__doit3times__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_nat__mul__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_test__anon__fun' : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_doit3times (fun x : imported_nat => imported_Nat_mul x x) (imported_S (imported_S imported_0)))
    (imported_S (imported_S (imported_S (iterate1 imported_S 253 imported_0)))).
Parameter Original_LF__DOT__Poly_LF_Poly_test__anon__fun'_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (unwrap_sprop
          (Original_LF__DOT__Poly_LF_Poly_doit3times_iso nat_iso (fun n : nat => n * n) (fun x : imported_nat => imported_Nat_mul x x)
             (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso_sort nat_iso x1 x2) => {| unwrap_sprop := Nat_mul_iso (unwrap_sprop hx) (unwrap_sprop hx) |}) 2 (imported_S (imported_S imported_0))
             {| unwrap_sprop := S_iso (S_iso _0_iso) |}))
       (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 253 0 imported_0 _0_iso)))))
    Original.LF_DOT_Poly.LF.Poly.test_anon_fun' imported_Original_LF__DOT__Poly_LF_Poly_test__anon__fun'.
Existing Instance Original_LF__DOT__Poly_LF_Poly_test__anon__fun'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.test_anon_fun' ?x) => unify x Original_LF__DOT__Poly_LF_Poly_test__anon__fun'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.test_anon_fun' imported_Original_LF__DOT__Poly_LF_Poly_test__anon__fun' ?x) => unify x Original_LF__DOT__Poly_LF_Poly_test__anon__fun'_iso; constructor : typeclass_instances.


End Interface.