From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.ex__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.ex__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.ex__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.ex__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_in__split : forall (x : Type) (x0 : x) (x1 : imported_Original_LF__DOT__Poly_LF_Poly_list x),
  imported_Original_LF__DOT__Logic_LF_Logic_In x0 x1 ->
  imported_ex
    (fun H : imported_Original_LF__DOT__Poly_LF_Poly_list x =>
     imported_ex
       (fun H0 : imported_Original_LF__DOT__Poly_LF_Poly_list x =>
        imported_Corelib_Init_Logic_eq x1 (imported_Original_LF__DOT__Poly_LF_Poly_app H (imported_Original_LF__DOT__Poly_LF_Poly_cons x0 H0)))).
Parameter Original_LF__DOT__IndProp_LF_IndProp_in__split_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (hx0 : rel_iso hx x3 x4) (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
    (hx1 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6) (x7 : Original.LF_DOT_Logic.LF.Logic.In x3 x5) (x8 : imported_Original_LF__DOT__Logic_LF_Logic_In x4 x6),
  rel_iso (relax_Iso_Ts_Ps (Original_LF__DOT__Logic_LF_Logic_In_iso hx0 hx1)) x7 x8 ->
  rel_iso
    (relax_Iso_Ts_Ps
       (ex_iso (fun l1 : Original.LF_DOT_Poly.LF.Poly.list x1 => exists l2 : Original.LF_DOT_Poly.LF.Poly.list x1, x5 = Original.LF_DOT_Poly.LF.Poly.app l1 (Original.LF_DOT_Poly.LF.Poly.cons x3 l2))
          (fun H : imported_Original_LF__DOT__Poly_LF_Poly_list x2 =>
           imported_ex
             (fun H0 : imported_Original_LF__DOT__Poly_LF_Poly_list x2 =>
              imported_Corelib_Init_Logic_eq x6 (imported_Original_LF__DOT__Poly_LF_Poly_app H (imported_Original_LF__DOT__Poly_LF_Poly_cons x4 H0))))
          (fun (x9 : Original.LF_DOT_Poly.LF.Poly.list x1) (x10 : imported_Original_LF__DOT__Poly_LF_Poly_list x2) (hx3 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x9 x10) =>
           ex_iso (fun l2 : Original.LF_DOT_Poly.LF.Poly.list x1 => x5 = Original.LF_DOT_Poly.LF.Poly.app x9 (Original.LF_DOT_Poly.LF.Poly.cons x3 l2))
             (fun H : imported_Original_LF__DOT__Poly_LF_Poly_list x2 =>
              imported_Corelib_Init_Logic_eq x6 (imported_Original_LF__DOT__Poly_LF_Poly_app x10 (imported_Original_LF__DOT__Poly_LF_Poly_cons x4 H)))
             (fun (x11 : Original.LF_DOT_Poly.LF.Poly.list x1) (x12 : imported_Original_LF__DOT__Poly_LF_Poly_list x2) (hx4 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x11 x12) =>
              Corelib_Init_Logic_eq_iso hx1 (Original_LF__DOT__Poly_LF_Poly_app_iso hx3 (Original_LF__DOT__Poly_LF_Poly_cons_iso hx0 hx4))))))
    (Original.LF_DOT_IndProp.LF.IndProp.in_split x1 x3 x5 x7) (imported_Original_LF__DOT__IndProp_LF_IndProp_in__split x8).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_in__split_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.in_split ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_in__split_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.in_split imported_Original_LF__DOT__IndProp_LF_IndProp_in__split ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_in__split_iso; constructor : typeclass_instances.


End Interface.