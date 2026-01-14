From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_false__iso Interface.U_logic__not__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.option__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__partial____map__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_false__iso Interface.U_logic__not__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.option__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__partial____map__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.option__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__partial____map__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.false__iso.Interface <+ Interface.option__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__partial____map__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Maps_LF_Maps_update__permute : forall (x : Type) (x0 : imported_String_string -> imported_option x) (x1 x2 : imported_String_string) (x3 x4 : x),
  (imported_Corelib_Init_Logic_eq x2 x1 -> imported_False) ->
  imported_Corelib_Init_Logic_eq
    (fun x16 : imported_String_string =>
     imported_Original_LF__DOT__Maps_LF_Maps_update (fun x5 : imported_String_string => imported_Original_LF__DOT__Maps_LF_Maps_update (fun x6 : imported_String_string => x0 x6) x2 x4 x5) x1 x3 x16)
    (fun x16 : imported_String_string =>
     imported_Original_LF__DOT__Maps_LF_Maps_update (fun x5 : imported_String_string => imported_Original_LF__DOT__Maps_LF_Maps_update (fun x6 : imported_String_string => x0 x6) x1 x3 x5) x2 x4 x16).
Parameter Original_LF__DOT__Maps_LF_Maps_update__permute_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Maps.LF.Maps.partial_map x1) (x4 : imported_String_string -> imported_option x2)
    (hx0 : forall (x5 : String.string) (x6 : imported_String_string), rel_iso String_string_iso x5 x6 -> rel_iso (option_iso hx) (x3 x5) (x4 x6)) (x5 : String.string) (x6 : imported_String_string)
    (hx1 : rel_iso String_string_iso x5 x6) (x7 : String.string) (x8 : imported_String_string) (hx2 : rel_iso String_string_iso x7 x8) (x9 : x1) (x10 : x2) (hx3 : rel_iso hx x9 x10) 
    (x11 : x1) (x12 : x2) (hx4 : rel_iso hx x11 x12) (x13 : x7 <> x5) (x14 : imported_Corelib_Init_Logic_eq x8 x6 -> imported_False),
  (forall (x15 : x7 = x5) (x16 : imported_Corelib_Init_Logic_eq x8 x6), rel_iso (Corelib_Init_Logic_eq_iso hx2 hx1) x15 x16 -> rel_iso False_iso (x13 x15) (x14 x16)) ->
  rel_iso
    (Corelib_Init_Logic_eq_iso
       (IsoFunND (Original.LF_DOT_Maps.LF.Maps.update (Original.LF_DOT_Maps.LF.Maps.update x3 x7 x11) x5 x9)
          (fun x16 : imported_String_string =>
           imported_Original_LF__DOT__Maps_LF_Maps_update (fun x : imported_String_string => imported_Original_LF__DOT__Maps_LF_Maps_update (fun x0 : imported_String_string => x4 x0) x8 x12 x) x6 x10
             x16)
          (fun (x15 : String.string) (x16 : imported_String_string) (hx6 : rel_iso String_string_iso x15 x16) =>
           Original_LF__DOT__Maps_LF_Maps_update_iso (Original.LF_DOT_Maps.LF.Maps.update x3 x7 x11)
             (fun x : imported_String_string => imported_Original_LF__DOT__Maps_LF_Maps_update (fun x0 : imported_String_string => x4 x0) x8 x12 x)
             (fun (x17 : String.string) (x18 : imported_String_string) (hx7 : rel_iso String_string_iso x17 x18) =>
              Original_LF__DOT__Maps_LF_Maps_update_iso x3 (fun x : imported_String_string => x4 x)
                (fun (x19 : String.string) (x20 : imported_String_string) (hx8 : rel_iso String_string_iso x19 x20) => hx0 x19 x20 hx8) hx2 hx4 hx7)
             hx1 hx3 hx6))
       (IsoFunND (Original.LF_DOT_Maps.LF.Maps.update (Original.LF_DOT_Maps.LF.Maps.update x3 x5 x9) x7 x11)
          (fun x16 : imported_String_string =>
           imported_Original_LF__DOT__Maps_LF_Maps_update (fun x : imported_String_string => imported_Original_LF__DOT__Maps_LF_Maps_update (fun x0 : imported_String_string => x4 x0) x6 x10 x) x8 x12
             x16)
          (fun (x15 : String.string) (x16 : imported_String_string) (hx6 : rel_iso String_string_iso x15 x16) =>
           Original_LF__DOT__Maps_LF_Maps_update_iso (Original.LF_DOT_Maps.LF.Maps.update x3 x5 x9)
             (fun x : imported_String_string => imported_Original_LF__DOT__Maps_LF_Maps_update (fun x0 : imported_String_string => x4 x0) x6 x10 x)
             (fun (x17 : String.string) (x18 : imported_String_string) (hx7 : rel_iso String_string_iso x17 x18) =>
              Original_LF__DOT__Maps_LF_Maps_update_iso x3 (fun x : imported_String_string => x4 x)
                (fun (x19 : String.string) (x20 : imported_String_string) (hx8 : rel_iso String_string_iso x19 x20) => hx0 x19 x20 hx8) hx1 hx3 hx7)
             hx2 hx4 hx6)))
    (Original.LF_DOT_Maps.LF.Maps.update_permute x1 x3 x5 x7 x9 x11 x13) (imported_Original_LF__DOT__Maps_LF_Maps_update__permute x4 x10 x12 x14).
Existing Instance Original_LF__DOT__Maps_LF_Maps_update__permute_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Maps.LF.Maps.update_permute ?x) => unify x Original_LF__DOT__Maps_LF_Maps_update__permute_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Maps.LF.Maps.update_permute imported_Original_LF__DOT__Maps_LF_Maps_update__permute ?x) => unify x Original_LF__DOT__Maps_LF_Maps_update__permute_iso; constructor : typeclass_instances.


End Interface.