From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.option__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__partial____map__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update__iso Interface.U_some__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.option__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__partial____map__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update__iso Interface.U_some__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.option__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__partial____map__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update__iso.CodeBlocks Interface.U_some__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.false__iso.Interface <+ Interface.option__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__partial____map__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update__iso.Interface <+ Interface.U_some__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Maps_LF_Maps_update__eq : forall (x : Type) (x0 : imported_String_string -> imported_option x) (x1 : imported_String_string) (x2 : x),
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Maps_LF_Maps_update (fun x3 : imported_String_string => x0 x3) x1 x2 x1) (imported_Some x2).
Parameter Original_LF__DOT__Maps_LF_Maps_update__eq_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Maps.LF.Maps.partial_map x1) (x4 : imported_String_string -> imported_option x2)
    (hx0 : forall (x5 : String.string) (x6 : imported_String_string), rel_iso String_string_iso x5 x6 -> rel_iso (option_iso hx) (x3 x5) (x4 x6)) (x5 : String.string) (x6 : imported_String_string)
    (hx1 : rel_iso String_string_iso x5 x6) (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8),
  rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__Maps_LF_Maps_update_iso x3 (fun x : imported_String_string => x4 x)
          (fun (x9 : String.string) (x10 : imported_String_string) (hx3 : rel_iso String_string_iso x9 x10) => hx0 x9 x10 hx3) hx1 hx2 hx1)
       (Some_iso hx2))
    (Original.LF_DOT_Maps.LF.Maps.update_eq x1 x3 x5 x7) (imported_Original_LF__DOT__Maps_LF_Maps_update__eq x4 x6 x8).
Existing Instance Original_LF__DOT__Maps_LF_Maps_update__eq_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Maps.LF.Maps.update_eq ?x) => unify x Original_LF__DOT__Maps_LF_Maps_update__eq_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Maps.LF.Maps.update_eq imported_Original_LF__DOT__Maps_LF_Maps_update__eq ?x) => unify x Original_LF__DOT__Maps_LF_Maps_update__eq_iso; constructor : typeclass_instances.


End Interface.