From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_filter : forall x : Type, (x -> imported_Original_LF__DOT__Basics_LF_Basics_bool) -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x.
Parameter Original_LF__DOT__Poly_LF_Poly_filter_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1 -> Original.LF_DOT_Basics.LF.Basics.bool) (x4 : x2 -> imported_Original_LF__DOT__Basics_LF_Basics_bool),
  (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (x3 x5) (x4 x6)) ->
  forall (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6 ->
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Poly.LF.Poly.filter x3 x5) (imported_Original_LF__DOT__Poly_LF_Poly_filter x4 x6).
Existing Instance Original_LF__DOT__Poly_LF_Poly_filter_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.filter) ?x) => unify x Original_LF__DOT__Poly_LF_Poly_filter_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.filter) imported_Original_LF__DOT__Poly_LF_Poly_filter ?x) => unify x Original_LF__DOT__Poly_LF_Poly_filter_iso; constructor : typeclass_instances.


End Interface.