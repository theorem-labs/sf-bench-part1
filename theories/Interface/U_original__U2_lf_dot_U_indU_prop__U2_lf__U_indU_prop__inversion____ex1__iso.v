From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_inversion__ex1 : forall x x0 x1 : imported_nat,
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_cons x (imported_Original_LF__DOT__Poly_LF_Poly_cons x0 (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))
    (imported_Original_LF__DOT__Poly_LF_Poly_cons x1 (imported_Original_LF__DOT__Poly_LF_Poly_cons x1 (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))) ->
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_cons x (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))
    (imported_Original_LF__DOT__Poly_LF_Poly_cons x0 (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)).
Parameter Original_LF__DOT__IndProp_LF_IndProp_inversion__ex1_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : Original.LF_DOT_Poly.LF.Poly.cons x1 (Original.LF_DOT_Poly.LF.Poly.cons x3 Original.LF_DOT_Poly.LF.Poly.nil) =
          Original.LF_DOT_Poly.LF.Poly.cons x5 (Original.LF_DOT_Poly.LF.Poly.cons x5 Original.LF_DOT_Poly.LF.Poly.nil))
    (x8 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_cons x2 (imported_Original_LF__DOT__Poly_LF_Poly_cons x4 (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))
            (imported_Original_LF__DOT__Poly_LF_Poly_cons x6 (imported_Original_LF__DOT__Poly_LF_Poly_cons x6 (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))),
  rel_iso
    (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso hx (Original_LF__DOT__Poly_LF_Poly_cons_iso hx0 (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))
       (Original_LF__DOT__Poly_LF_Poly_cons_iso hx1 (Original_LF__DOT__Poly_LF_Poly_cons_iso hx1 (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))
    x7 x8 ->
  rel_iso
    (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso hx (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
       (Original_LF__DOT__Poly_LF_Poly_cons_iso hx0 (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))
    (Original.LF_DOT_IndProp.LF.IndProp.inversion_ex1 x1 x3 x5 x7) (imported_Original_LF__DOT__IndProp_LF_IndProp_inversion__ex1 x8).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_inversion__ex1_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.inversion_ex1 ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_inversion__ex1_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.inversion_ex1 imported_Original_LF__DOT__IndProp_LF_IndProp_inversion__ex1 ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_inversion__ex1_iso; constructor : typeclass_instances.


End Interface.