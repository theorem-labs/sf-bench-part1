From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__pair__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__partition__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__odd__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__pair__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__partition__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__odd__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__pair__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__partition__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__odd__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__pair__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__partition__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__odd__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_test__partition1 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Poly_LF_Poly_partition (fun x : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_odd x)
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
             (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0)))
                (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0))))
                   (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (iterate1 imported_S 2 imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))))))
    (imported_Original_LF__DOT__Poly_LF_Poly_pair
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0)))
             (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (iterate1 imported_S 2 imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))))
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))).
Parameter Original_LF__DOT__Poly_LF_Poly_test__partition1_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__Poly_LF_Poly_partition_iso Original.LF_DOT_Basics.LF.Basics.odd (fun x : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_odd x)
          (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) => Original_LF__DOT__Basics_LF_Basics_odd_iso hx)
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso)
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso)))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso))))
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 2 0 imported_0 _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))))))
       (Original_LF__DOT__Poly_LF_Poly_pair_iso
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso)
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso)))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 2 0 imported_0 _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))))
    Original.LF_DOT_Poly.LF.Poly.test_partition1 imported_Original_LF__DOT__Poly_LF_Poly_test__partition1.
Existing Instance Original_LF__DOT__Poly_LF_Poly_test__partition1_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.test_partition1 ?x) => unify x Original_LF__DOT__Poly_LF_Poly_test__partition1_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.test_partition1 imported_Original_LF__DOT__Poly_LF_Poly_test__partition1 ?x) => unify x Original_LF__DOT__Poly_LF_Poly_test__partition1_iso; constructor : typeclass_instances.


End Interface.