From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_string__string__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplemapSQUOTE__iso Interface.false__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_string__string__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplemapSQUOTE__iso Interface.false__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplemapSQUOTE__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplemapSQUOTE__iso.Interface <+ Interface.false__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Maps_LF_Maps_update__example2 : @imported_Corelib_Init_Logic_eq imported_bool
    (imported_Original_LF__DOT__Maps_LF_Maps_examplemap'
       (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string imported_String_EmptyString
          imported_String_String
          (String.String (Ascii.Ascii false true true false false true true false)
             (String.String (Ascii.Ascii true true true true false true true false) (String.String (Ascii.Ascii true true true true false true true false) String.EmptyString)))))
    imported_true.
Parameter Original_LF__DOT__Maps_LF_Maps_update__example2_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Maps_LF_Maps_examplemap'_iso
             (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                (String.String (Ascii.Ascii false true true false false true true false)
                   (String.String (Ascii.Ascii true true true true false true true false) (String.String (Ascii.Ascii true true true true false true true false) String.EmptyString)))))
          true_iso;
      from :=
        from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Maps_LF_Maps_examplemap'_iso
                (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                   (String.String (Ascii.Ascii false true true false false true true false)
                      (String.String (Ascii.Ascii true true true true false true true false) (String.String (Ascii.Ascii true true true true false true true false) String.EmptyString)))))
             true_iso);
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq
                (imported_Original_LF__DOT__Maps_LF_Maps_examplemap'
                   (StringOptimizations.imported_string
                      (String.String (Ascii.Ascii false true true false false true true false)
                         (String.String (Ascii.Ascii true true true true false true true false) (String.String (Ascii.Ascii true true true true false true true false) String.EmptyString)))))
                imported_true =>
        to_from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Maps_LF_Maps_examplemap'_iso
                (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                   (String.String (Ascii.Ascii false true true false false true true false)
                      (String.String (Ascii.Ascii true true true true false true true false) (String.String (Ascii.Ascii true true true true false true true false) String.EmptyString)))))
             true_iso)
          x;
      from_to :=
        fun
          x : Original.LF_DOT_Maps.LF.Maps.examplemap'
                (String.String (Ascii.Ascii false true true false false true true false)
                   (String.String (Ascii.Ascii true true true true false true true false) (String.String (Ascii.Ascii true true true true false true true false) String.EmptyString))) =
              true =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__Maps_LF_Maps_examplemap'_iso
                   (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                      (String.String (Ascii.Ascii false true true false false true true false)
                         (String.String (Ascii.Ascii true true true true false true true false) (String.String (Ascii.Ascii true true true true false true true false) String.EmptyString)))))
                true_iso)
             x)
    |} Original.LF_DOT_Maps.LF.Maps.update_example2 imported_Original_LF__DOT__Maps_LF_Maps_update__example2.
Existing Instance Original_LF__DOT__Maps_LF_Maps_update__example2_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Maps.LF.Maps.update_example2 ?x) => unify x Original_LF__DOT__Maps_LF_Maps_update__example2_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Maps.LF.Maps.update_example2 imported_Original_LF__DOT__Maps_LF_Maps_update__example2 ?x) => unify x Original_LF__DOT__Maps_LF_Maps_update__example2_iso; constructor : typeclass_instances.


End Interface.