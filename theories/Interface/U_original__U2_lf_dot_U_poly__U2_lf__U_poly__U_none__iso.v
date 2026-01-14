From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__option__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__option__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__option__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__option__iso.Args <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__option__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_None : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_option x.
Parameter Original_LF__DOT__Poly_LF_Poly_None_iso : forall (x1 x2 : Type) (hx : Iso x1 x2), rel_iso (Original_LF__DOT__Poly_LF_Poly_option_iso hx) Original.LF_DOT_Poly.LF.Poly.None (imported_Original_LF__DOT__Poly_LF_Poly_None x2).
Existing Instance Original_LF__DOT__Poly_LF_Poly_None_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.None) ?x) => unify x Original_LF__DOT__Poly_LF_Poly_None_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.None) imported_Original_LF__DOT__Poly_LF_Poly_None ?x) => unify x Original_LF__DOT__Poly_LF_Poly_None_iso; constructor : typeclass_instances.


End Interface.