From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__pair__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__split__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__pair__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__split__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__pair__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__split__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__pair__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__split__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_test__split : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Poly_LF_Poly_split
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_Original_LF__DOT__Poly_LF_Poly_pair (imported_S imported_0) imported_Original_LF__DOT__Basics_LF_Basics_false)
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_Original_LF__DOT__Poly_LF_Poly_pair (imported_S (imported_S imported_0)) imported_Original_LF__DOT__Basics_LF_Basics_false)
             (imported_Original_LF__DOT__Poly_LF_Poly_nil (imported_Original_LF__DOT__Poly_LF_Poly_prod imported_nat imported_Original_LF__DOT__Basics_LF_Basics_bool)))))
    (imported_Original_LF__DOT__Poly_LF_Poly_pair
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0)) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))
       (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_Original_LF__DOT__Basics_LF_Basics_false
          (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_Original_LF__DOT__Basics_LF_Basics_false
             (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_Original_LF__DOT__Basics_LF_Basics_bool)))).
Parameter Original_LF__DOT__Poly_LF_Poly_test__split_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__Poly_LF_Poly_split_iso
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_pair_iso (S_iso _0_iso) Original_LF__DOT__Basics_LF_Basics_false_iso)
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_pair_iso (S_iso (S_iso _0_iso)) Original_LF__DOT__Basics_LF_Basics_false_iso)
                (Original_LF__DOT__Poly_LF_Poly_nil_iso (Original_LF__DOT__Poly_LF_Poly_prod_iso nat_iso Original_LF__DOT__Basics_LF_Basics_bool_iso)))))
       (Original_LF__DOT__Poly_LF_Poly_pair_iso
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso) (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso)) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))
          (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_false_iso
             (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_false_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Original_LF__DOT__Basics_LF_Basics_bool_iso)))))
    Original.LF_DOT_Poly.LF.Poly.test_split imported_Original_LF__DOT__Poly_LF_Poly_test__split.
Existing Instance Original_LF__DOT__Poly_LF_Poly_test__split_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.test_split ?x) => unify x Original_LF__DOT__Poly_LF_Poly_test__split_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.test_split imported_Original_LF__DOT__Poly_LF_Poly_test__split ?x) => unify x Original_LF__DOT__Poly_LF_Poly_test__split_iso; constructor : typeclass_instances.


End Interface.