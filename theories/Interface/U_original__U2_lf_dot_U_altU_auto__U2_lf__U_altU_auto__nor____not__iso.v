From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__nor__iso Interface.iff__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__nor__iso Interface.iff__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__nor__iso.CodeBlocks Interface.iff__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__nor__iso.Interface <+ Interface.iff__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor__not : forall x : SProp, imported_iff (imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor x x) (x -> imported_False).
Parameter Original_LF__DOT__AltAuto_LF_AltAuto_nor__not_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2),
  rel_iso
    {|
      to := iff_iso (Original_LF__DOT__AltAuto_LF_AltAuto_nor_iso hx hx) (IsoArrow hx False_iso);
      from := from (iff_iso (Original_LF__DOT__AltAuto_LF_AltAuto_nor_iso hx hx) (IsoArrow hx False_iso));
      to_from :=
        fun x : imported_iff (imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor x2 x2) (x2 -> imported_False) =>
        to_from (iff_iso (Original_LF__DOT__AltAuto_LF_AltAuto_nor_iso hx hx) (IsoArrow hx False_iso)) x;
      from_to := fun x : Original.LF_DOT_AltAuto.LF.AltAuto.nor x1 x1 <-> ~ x1 => seq_p_of_t (from_to (iff_iso (Original_LF__DOT__AltAuto_LF_AltAuto_nor_iso hx hx) (IsoArrow hx False_iso)) x)
    |} (Original.LF_DOT_AltAuto.LF.AltAuto.nor_not x1) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor__not x2).
Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_nor__not_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.nor_not ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_nor__not_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.nor_not imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor__not ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_nor__not_iso; constructor : typeclass_instances.


End Interface.