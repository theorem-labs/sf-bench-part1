From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__fold__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__fold__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__fold__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__fold__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_fold__example3 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Poly_LF_Poly_fold (fun x x0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat => imported_Original_LF__DOT__Poly_LF_Poly_app x x0)
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)
             (imported_Original_LF__DOT__Poly_LF_Poly_cons
                (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
                   (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))
                (imported_Original_LF__DOT__Poly_LF_Poly_cons
                   (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))
                   (imported_Original_LF__DOT__Poly_LF_Poly_nil (imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat))))))
       (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))
    (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0)))
             (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))))).
Parameter Original_LF__DOT__Poly_LF_Poly_fold__example3_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (unwrap_sprop
          (Original_LF__DOT__Poly_LF_Poly_fold_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) Original.LF_DOT_Poly.LF.Poly.app
             (fun x x0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat => imported_Original_LF__DOT__Poly_LF_Poly_app x x0)
             (fun (x1 : Original.LF_DOT_Poly.LF.Poly.list nat) (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat) (hx : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x1 x2)
                (x3 : Original.LF_DOT_Poly.LF.Poly.list nat) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat)
                (hx0 : rel_iso_sort (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x3 x4) =>
              {| unwrap_sprop := Original_LF__DOT__Poly_LF_Poly_app_iso hx (unwrap_sprop hx0) |})
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
                         (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso
                         (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                         (Original_LF__DOT__Poly_LF_Poly_nil_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso))))))
             Original.LF_DOT_Poly.LF.Poly.nil (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat) {| unwrap_sprop := Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso |}))
       (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso)
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso)))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))))
    Original.LF_DOT_Poly.LF.Poly.fold_example3 imported_Original_LF__DOT__Poly_LF_Poly_fold__example3.
Existing Instance Original_LF__DOT__Poly_LF_Poly_fold__example3_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.fold_example3 ?x) => unify x Original_LF__DOT__Poly_LF_Poly_fold__example3_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.fold_example3 imported_Original_LF__DOT__Poly_LF_Poly_fold__example3 ?x) => unify x Original_LF__DOT__Poly_LF_Poly_fold__example3_iso; constructor : typeclass_instances.


End Interface.