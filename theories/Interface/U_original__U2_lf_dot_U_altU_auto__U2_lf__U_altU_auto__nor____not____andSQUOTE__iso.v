From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__nor__iso Interface.and__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__nor__iso Interface.and__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__nor__iso.CodeBlocks Interface.and__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__nor__iso.Interface <+ Interface.and__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__and' : forall x x0 : SProp, imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor x x0 -> imported_and x x0 -> imported_False.
Parameter Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__and'_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : Original.LF_DOT_AltAuto.LF.AltAuto.nor x1 x3)
    (x6 : imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor x2 x4),
  rel_iso (Original_LF__DOT__AltAuto_LF_AltAuto_nor_iso hx hx0) x5 x6 ->
  forall (x7 : x1 /\ x3) (x8 : imported_and x2 x4),
  rel_iso (and_iso hx hx0) x7 x8 -> rel_iso False_iso (Original.LF_DOT_AltAuto.LF.AltAuto.nor_not_and' x1 x3 x5 x7) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__and' x6 x8).
Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__and'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.nor_not_and' ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__and'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.nor_not_and' imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__and' ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__and'_iso; constructor : typeclass_instances.


End Interface.