From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__nor__iso Interface.iff__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__nor__iso Interface.iff__iso.

  Export Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__nor__iso.CodeBlocks Interface.iff__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__nor__iso.Interface <+ Interface.iff__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor__comm' : forall x x0 : SProp, imported_iff (imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor x x0) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor x0 x).
Parameter Original_LF__DOT__AltAuto_LF_AltAuto_nor__comm'_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4),
  rel_iso
    {|
      to := iff_iso (Original_LF__DOT__AltAuto_LF_AltAuto_nor_iso hx hx0) (Original_LF__DOT__AltAuto_LF_AltAuto_nor_iso hx0 hx);
      from := from (iff_iso (Original_LF__DOT__AltAuto_LF_AltAuto_nor_iso hx hx0) (Original_LF__DOT__AltAuto_LF_AltAuto_nor_iso hx0 hx));
      to_from :=
        fun x : imported_iff (imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor x2 x4) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor x4 x2) =>
        to_from (iff_iso (Original_LF__DOT__AltAuto_LF_AltAuto_nor_iso hx hx0) (Original_LF__DOT__AltAuto_LF_AltAuto_nor_iso hx0 hx)) x;
      from_to :=
        fun x : Original.LF_DOT_AltAuto.LF.AltAuto.nor x1 x3 <-> Original.LF_DOT_AltAuto.LF.AltAuto.nor x3 x1 =>
        seq_p_of_t (from_to (iff_iso (Original_LF__DOT__AltAuto_LF_AltAuto_nor_iso hx hx0) (Original_LF__DOT__AltAuto_LF_AltAuto_nor_iso hx0 hx)) x)
    |} (Original.LF_DOT_AltAuto.LF.AltAuto.nor_comm' x1 x3) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor__comm' x2 x4).
Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_nor__comm'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.nor_comm' ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_nor__comm'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.nor_comm' imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor__comm' ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_nor__comm'_iso; constructor : typeclass_instances.


End Interface.