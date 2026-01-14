From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__andb__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__fold__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__andb__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__fold__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__andb__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__fold__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__andb__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__fold__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_fold__example1 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Poly_LF_Poly_fold (fun x x0 : imported_Original_LF__DOT__Basics_LF_Basics_bool => imported_Original_LF__DOT__Basics_LF_Basics_andb x x0)
       (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_Original_LF__DOT__Basics_LF_Basics_true
          (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_Original_LF__DOT__Basics_LF_Basics_true
             (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_Original_LF__DOT__Basics_LF_Basics_false
                (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_Original_LF__DOT__Basics_LF_Basics_true
                   (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_Original_LF__DOT__Basics_LF_Basics_bool)))))
       imported_Original_LF__DOT__Basics_LF_Basics_true)
    imported_Original_LF__DOT__Basics_LF_Basics_false.
Parameter Original_LF__DOT__Poly_LF_Poly_fold__example1_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (unwrap_sprop
          (Original_LF__DOT__Poly_LF_Poly_fold_iso Original_LF__DOT__Basics_LF_Basics_bool_iso Original.LF_DOT_Basics.LF.Basics.andb
             (fun x x0 : imported_Original_LF__DOT__Basics_LF_Basics_bool => imported_Original_LF__DOT__Basics_LF_Basics_andb x x0)
             (fun (x1 : Original.LF_DOT_Basics.LF.Basics.bool) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (hx : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x1 x2)
                (x3 : Original.LF_DOT_Basics.LF.Basics.bool) (x4 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (hx0 : rel_iso_sort Original_LF__DOT__Basics_LF_Basics_bool_iso x3 x4) =>
              {| unwrap_sprop := Original_LF__DOT__Basics_LF_Basics_andb_iso hx (unwrap_sprop hx0) |})
             (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_true_iso
                (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_true_iso
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_false_iso
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_true_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Original_LF__DOT__Basics_LF_Basics_bool_iso)))))
             Original.LF_DOT_Basics.LF.Basics.true imported_Original_LF__DOT__Basics_LF_Basics_true {| unwrap_sprop := Original_LF__DOT__Basics_LF_Basics_true_iso |}))
       Original_LF__DOT__Basics_LF_Basics_false_iso)
    Original.LF_DOT_Poly.LF.Poly.fold_example1 imported_Original_LF__DOT__Poly_LF_Poly_fold__example1.
Existing Instance Original_LF__DOT__Poly_LF_Poly_fold__example1_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.fold_example1 ?x) => unify x Original_LF__DOT__Poly_LF_Poly_fold__example1_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.fold_example1 imported_Original_LF__DOT__Poly_LF_Poly_fold__example1 ?x) => unify x Original_LF__DOT__Poly_LF_Poly_fold__example1_iso; constructor : typeclass_instances.


End Interface.