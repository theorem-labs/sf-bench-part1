From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Args <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_pal : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_list x -> SProp.
Parameter Original_LF__DOT__IndProp_LF_IndProp_pal_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.pal x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_pal x4).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_pal_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_IndProp.LF.IndProp.pal) ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_pal_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_IndProp.LF.IndProp.pal) imported_Original_LF__DOT__IndProp_LF_IndProp_pal ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_pal_iso; constructor : typeclass_instances.


End Interface.