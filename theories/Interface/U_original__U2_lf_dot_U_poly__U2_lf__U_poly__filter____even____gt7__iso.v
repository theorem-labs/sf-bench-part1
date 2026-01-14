From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.nat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.nat__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.nat__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.nat__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_filter__even__gt7 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat -> imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat.
Parameter Original_LF__DOT__Poly_LF_Poly_filter__even__gt7_iso : forall (x1 : Original.LF_DOT_Poly.LF.Poly.list nat) (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x1 x2 ->
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) (Original.LF_DOT_Poly.LF.Poly.filter_even_gt7 x1) (imported_Original_LF__DOT__Poly_LF_Poly_filter__even__gt7 x2).
Existing Instance Original_LF__DOT__Poly_LF_Poly_filter__even__gt7_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.filter_even_gt7 ?x) => unify x Original_LF__DOT__Poly_LF_Poly_filter__even__gt7_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.filter_even_gt7 imported_Original_LF__DOT__Poly_LF_Poly_filter__even__gt7 ?x) => unify x Original_LF__DOT__Poly_LF_Poly_filter__even__gt7_iso; constructor : typeclass_instances.


End Interface.