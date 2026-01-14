From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____empty__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____empty__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____empty__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____empty__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.false__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Maps_LF_Maps_t__apply__empty : forall (x : Type) (x0 : imported_String_string) (x1 : x), imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Maps_LF_Maps_t__empty x1 x0) x1.
Parameter Original_LF__DOT__Maps_LF_Maps_t__apply__empty_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : String.string) (x4 : imported_String_string) (hx0 : rel_iso String_string_iso x3 x4) (x5 : x1) (x6 : x2) (hx1 : rel_iso hx x5 x6),
  rel_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Maps_LF_Maps_t__empty_iso hx1 hx0) hx1) (Original.LF_DOT_Maps.LF.Maps.t_apply_empty x1 x3 x5)
    (imported_Original_LF__DOT__Maps_LF_Maps_t__apply__empty x4 x6).
Existing Instance Original_LF__DOT__Maps_LF_Maps_t__apply__empty_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Maps.LF.Maps.t_apply_empty ?x) => unify x Original_LF__DOT__Maps_LF_Maps_t__apply__empty_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Maps.LF.Maps.t_apply_empty imported_Original_LF__DOT__Maps_LF_Maps_t__apply__empty ?x) => unify x Original_LF__DOT__Maps_LF_Maps_t__apply__empty_iso; constructor : typeclass_instances.


End Interface.