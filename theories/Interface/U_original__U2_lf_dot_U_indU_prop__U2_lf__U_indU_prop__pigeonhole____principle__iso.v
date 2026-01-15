From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__repeats__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__length__iso Interface.lt__iso Interface.or__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__excluded____middle__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__repeats__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__length__iso Interface.lt__iso Interface.or__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__excluded____middle__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__repeats__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__length__iso.CodeBlocks Interface.lt__iso.CodeBlocks Interface.or__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__excluded____middle__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__repeats__iso.Interface <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__length__iso.Interface <+ Interface.lt__iso.Interface <+ Interface.or__iso.Interface <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__excluded____middle__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_pigeonhole__principle : (forall x : SProp, imported_or x (x -> imported_False)) ->
  forall (x0 : Type) (x1 x2 : imported_Original_LF__DOT__Poly_LF_Poly_list x0),
  (forall x : x0, imported_Original_LF__DOT__Logic_LF_Logic_In x x1 -> imported_Original_LF__DOT__Logic_LF_Logic_In x x2) ->
  imported_lt (imported_Original_LF__DOT__Poly_LF_Poly_length x2) (imported_Original_LF__DOT__Poly_LF_Poly_length x1) -> imported_Original_LF__DOT__IndProp_LF_IndProp_repeats x1.
Parameter Original_LF__DOT__IndProp_LF_IndProp_pigeonhole__principle_iso : forall (x1 : Original.LF_DOT_Logic.LF.Logic.excluded_middle) (x2 : forall x : SProp, imported_or x (x -> imported_False)),
  (forall (x3 : Prop) (x4 : SProp) (hx : Iso x3 x4), rel_iso (relax_Iso_Ts_Ps (or_iso hx (IsoArrow hx False_iso))) (x1 x3) (x2 x4)) ->
  forall (x3 x4 : Type) (hx0 : Iso x3 x4) (x5 : Original.LF_DOT_Poly.LF.Poly.list x3) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x4)
    (hx1 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx0) x5 x6) (x7 : Original.LF_DOT_Poly.LF.Poly.list x3) (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list x4)
    (hx2 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx0) x7 x8) (x9 : forall x : x3, Original.LF_DOT_Logic.LF.Logic.In x x5 -> Original.LF_DOT_Logic.LF.Logic.In x x7)
    (x10 : forall x : x4, imported_Original_LF__DOT__Logic_LF_Logic_In x x6 -> imported_Original_LF__DOT__Logic_LF_Logic_In x x8),
  (forall (x11 : x3) (x12 : x4) (hx3 : rel_iso hx0 x11 x12) (x13 : Original.LF_DOT_Logic.LF.Logic.In x11 x5) (x14 : imported_Original_LF__DOT__Logic_LF_Logic_In x12 x6),
   rel_iso (relax_Iso_Ts_Ps (Original_LF__DOT__Logic_LF_Logic_In_iso hx3 hx1)) x13 x14 -> rel_iso (relax_Iso_Ts_Ps (Original_LF__DOT__Logic_LF_Logic_In_iso hx3 hx2)) (x9 x11 x13) (x10 x12 x14)) ->
  forall (x11 : Original.LF_DOT_Poly.LF.Poly.length x7 < Original.LF_DOT_Poly.LF.Poly.length x5)
    (x12 : imported_lt (imported_Original_LF__DOT__Poly_LF_Poly_length x8) (imported_Original_LF__DOT__Poly_LF_Poly_length x6)),
  rel_iso (relax_Iso_Ts_Ps (lt_iso (Original_LF__DOT__Poly_LF_Poly_length_iso hx2) (Original_LF__DOT__Poly_LF_Poly_length_iso hx1))) x11 x12 ->
  rel_iso (relax_Iso_Ts_Ps (Original_LF__DOT__IndProp_LF_IndProp_repeats_iso hx1)) (Original.LF_DOT_IndProp.LF.IndProp.pigeonhole_principle x1 x3 x5 x7 x9 x11)
    (imported_Original_LF__DOT__IndProp_LF_IndProp_pigeonhole__principle x2 x10 x12).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_pigeonhole__principle_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.pigeonhole_principle ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_pigeonhole__principle_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.pigeonhole_principle imported_Original_LF__DOT__IndProp_LF_IndProp_pigeonhole__principle ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_pigeonhole__principle_iso; constructor : typeclass_instances.


End Interface.