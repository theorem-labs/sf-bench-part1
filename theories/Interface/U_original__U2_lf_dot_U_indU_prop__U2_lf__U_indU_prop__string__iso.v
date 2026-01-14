From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks.

#[export] Instance: MustUnfold Original.LF_DOT_IndProp.LF.IndProp.string := {}.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface.

Module Type Interface (Import args : Args).

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_string : Type
  := imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii.
Definition Original_LF__DOT__IndProp_LF_IndProp_string_iso : Iso Original.LF_DOT_IndProp.LF.IndProp.string imported_Original_LF__DOT__IndProp_LF_IndProp_string
  := Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso.
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_string_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.string ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_string_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.string imported_Original_LF__DOT__IndProp_LF_IndProp_string ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_string_iso; constructor : typeclass_instances.


End Interface.