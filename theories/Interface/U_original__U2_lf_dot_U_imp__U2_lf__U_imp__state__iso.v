From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.nat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.nat__iso.

  Export Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.nat__iso.CodeBlocks.

#[export] Instance: MustUnfold Original.LF_DOT_Imp.LF.Imp.state := {}.

End CodeBlocks.

Module Type Args := Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.nat__iso.Interface.

Module Type Interface (Import args : Args).

Definition imported_Original_LF__DOT__Imp_LF_Imp_state : Type
  := imported_Original_LF__DOT__Maps_LF_Maps_total__map imported_nat.
Definition Original_LF__DOT__Imp_LF_Imp_state_iso : Iso Original.LF_DOT_Imp.LF.Imp.state imported_Original_LF__DOT__Imp_LF_Imp_state
  := Original_LF__DOT__Maps_LF_Maps_total__map_iso nat_iso.
Existing Instance Original_LF__DOT__Imp_LF_Imp_state_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.state ?x) => unify x Original_LF__DOT__Imp_LF_Imp_state_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.state imported_Original_LF__DOT__Imp_LF_Imp_state ?x) => unify x Original_LF__DOT__Imp_LF_Imp_state_iso; constructor : typeclass_instances.


End Interface.