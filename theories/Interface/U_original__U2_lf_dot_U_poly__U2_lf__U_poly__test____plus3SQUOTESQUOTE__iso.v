From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__doit3times__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__plus__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__doit3times__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__plus__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__doit3times__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__plus__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__doit3times__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__plus__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_test__plus3'' : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Poly_LF_Poly_doit3times (fun x : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_plus (imported_S (imported_S (imported_S imported_0))) x) imported_0)
    (imported_S (imported_S (imported_S (iterate1 imported_S 6 imported_0)))).
Parameter Original_LF__DOT__Poly_LF_Poly_test__plus3''_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (unwrap_sprop
          (Original_LF__DOT__Poly_LF_Poly_doit3times_iso nat_iso (Original.LF_DOT_Basics.LF.Basics.plus 3)
             (fun x : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_plus (imported_S (imported_S (imported_S imported_0))) x)
             (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso_sort nat_iso x1 x2) =>
              {| unwrap_sprop := Original_LF__DOT__Basics_LF_Basics_plus_iso (S_iso (S_iso (S_iso _0_iso))) (unwrap_sprop hx) |})
             0 imported_0 {| unwrap_sprop := _0_iso |}))
       (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 6 0 imported_0 _0_iso)))))
    Original.LF_DOT_Poly.LF.Poly.test_plus3'' imported_Original_LF__DOT__Poly_LF_Poly_test__plus3''.
Existing Instance Original_LF__DOT__Poly_LF_Poly_test__plus3''_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.test_plus3'' ?x) => unify x Original_LF__DOT__Poly_LF_Poly_test__plus3''_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.test_plus3'' imported_Original_LF__DOT__Poly_LF_Poly_test__plus3'' ?x) => unify x Original_LF__DOT__Poly_LF_Poly_test__plus3''_iso; constructor : typeclass_instances.


End Interface.