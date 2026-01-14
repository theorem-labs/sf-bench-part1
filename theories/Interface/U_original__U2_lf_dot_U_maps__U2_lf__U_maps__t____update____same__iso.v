From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.false__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Maps_LF_Maps_t__update__same : forall (x : Type) (x0 : imported_String_string -> x) (x1 : imported_String_string),
  imported_Corelib_Init_Logic_eq (fun x8 : imported_String_string => imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun x2 : imported_String_string => x0 x2) x1 (x0 x1) x8)
    (fun x8 : imported_String_string => x0 x8).
Parameter Original_LF__DOT__Maps_LF_Maps_t__update__same_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Maps.LF.Maps.total_map x1) (x4 : imported_String_string -> x2)
    (hx0 : forall (x5 : String.string) (x6 : imported_String_string), rel_iso String_string_iso x5 x6 -> rel_iso hx (x3 x5) (x4 x6)) (x5 : String.string) (x6 : imported_String_string)
    (hx1 : rel_iso String_string_iso x5 x6),
  rel_iso
    (Corelib_Init_Logic_eq_iso
       (IsoFunND (Original.LF_DOT_Maps.LF.Maps.t_update x3 x5 (x3 x5))
          (fun x8 : imported_String_string => imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun x : imported_String_string => x4 x) x6 (x4 x6) x8)
          (fun (x7 : String.string) (x8 : imported_String_string) (hx2 : rel_iso String_string_iso x7 x8) =>
           unwrap_sprop
             (Original_LF__DOT__Maps_LF_Maps_t__update_iso hx x3 (fun x : imported_String_string => x4 x)
                (fun (x9 : String.string) (x10 : imported_String_string) (hx3 : rel_iso String_string_iso x9 x10) => {| unwrap_sprop := hx0 x9 x10 hx3 |}) hx1 (x3 x5) (x4 x6)
                {| unwrap_sprop := hx0 x5 x6 hx1 |} hx2)))
       (IsoFunND x3 (fun x8 : imported_String_string => x4 x8) (fun (x7 : String.string) (x8 : imported_String_string) (hx2 : rel_iso String_string_iso x7 x8) => hx0 x7 x8 hx2)))
    (Original.LF_DOT_Maps.LF.Maps.t_update_same x1 x3 x5) (imported_Original_LF__DOT__Maps_LF_Maps_t__update__same x4 x6).
Existing Instance Original_LF__DOT__Maps_LF_Maps_t__update__same_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Maps.LF.Maps.t_update_same ?x) => unify x Original_LF__DOT__Maps_LF_Maps_t__update__same_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Maps.LF.Maps.t_update_same imported_Original_LF__DOT__Maps_LF_Maps_t__update__same ?x) => unify x Original_LF__DOT__Maps_LF_Maps_t__update__same_iso; constructor : typeclass_instances.


End Interface.