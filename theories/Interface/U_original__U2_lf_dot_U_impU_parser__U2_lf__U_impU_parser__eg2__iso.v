From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__U_someU_e__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_amult__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_band__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_beq__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_ble__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_bnot__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_cif__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_cseq__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_cskip__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_cwhile__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__parse__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aid__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_casgn__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_anum__iso Interface.U_s__iso Interface.__0__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__U_someU_e__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_amult__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_band__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_beq__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_ble__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_bnot__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_cif__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_cseq__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_cskip__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_cwhile__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__parse__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aid__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_casgn__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_anum__iso Interface.U_s__iso Interface.__0__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__U_someU_e__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_amult__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_band__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_beq__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_ble__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_bnot__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_cif__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_cseq__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_cskip__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_cwhile__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__parse__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aid__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_casgn__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_anum__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso.Interface <+ Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__U_someU_e__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_amult__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_band__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_beq__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_ble__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_bnot__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_cif__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_cseq__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_cskip__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_cwhile__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__parse__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aid__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_casgn__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.false__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_anum__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ImpParser_LF_ImpParser_eg2 : @imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__ImpParser_LF_ImpParser_optionE imported_Original_LF__DOT__Imp_LF_Imp_com)
    (imported_Original_LF__DOT__ImpParser_LF_ImpParser_parse
       (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string imported_String_EmptyString
          imported_String_String
          (String.String (Ascii.Ascii false true false true false false false false)
             (String.String (Ascii.Ascii false false false false false true false false)
                (String.String (Ascii.Ascii false false false false false true false false)
                   (String.String (Ascii.Ascii true true false false true true true false)
                      (String.String (Ascii.Ascii true true false true false true true false)
                         (String.String (Ascii.Ascii true false false true false true true false)
                            (String.String (Ascii.Ascii false false false false true true true false)
                               (String.String (Ascii.Ascii true true false true true true false false)
                                  (String.String (Ascii.Ascii false true false true false false false false)
                                     (String.String (Ascii.Ascii false false false false false true false false)
                                        (String.String (Ascii.Ascii false false false false false true false false)
                                           (String.String (Ascii.Ascii false true false true true true true false)
                                              (String.String (Ascii.Ascii false true false true true true false false)
                                                 (String.String (Ascii.Ascii true false true true true true false false)
                                                    (String.String (Ascii.Ascii false false false true true true true false)
                                                       (String.String (Ascii.Ascii false true false true false true false false)
                                                          (String.String (Ascii.Ascii true false false true true true true false)
                                                             (String.String (Ascii.Ascii false true false true false true false false)
                                                                (String.String (Ascii.Ascii false false false true false true false false)
                                                                   (String.String (Ascii.Ascii false false false true true true true false)
                                                                      (String.String (Ascii.Ascii false true false true false true false false)
                                                                         (String.String (Ascii.Ascii false false false true true true true false)
                                                                            (String.String (Ascii.Ascii true false false true false true false false)
                                                                               (String.String (Ascii.Ascii true true false true true true false false)
                                                                                  (String.String (Ascii.Ascii false true false true false false false false)
                                                                                     (String.String (Ascii.Ascii false false false false false true false false)
                                                                                        (String.String (Ascii.Ascii false false false false false true false false)
                                                                                           (String.String (Ascii.Ascii true true true false true true true false)
                                                                                              (String.String (Ascii.Ascii false false false true false true true false)
                                                                                                 (String.String (Ascii.Ascii true false false true false true true false)
                                                                                                    (String.String (Ascii.Ascii false false true true false true true false)
                                                                                                       (String.String (Ascii.Ascii true false true false false true true false)
                                                                                                          (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                             (String.String (Ascii.Ascii false false false true true true true false)
                                                                                                                (String.String (Ascii.Ascii true false true true true true false false)
                                                                                                                   (String.String (Ascii.Ascii false false false true true true true false)
                                                                                                                      (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                                         (String.String (Ascii.Ascii false false true false false true true false)
                                                                                                                            (String.String (Ascii.Ascii true true true true false true true false)
                                                                                                                               (String.String
                                                                                                                                  (Ascii.Ascii false true false true false false false false)
                                                                                                                                  (String.String
                                                                                                                                     (Ascii.Ascii false false false false false true false false)
                                                                                                                                     (String.String
                                                                                                                                        (Ascii.Ascii false false false false false true false false)
                                                                                                                                        (String.String
                                                                                                                                           (Ascii.Ascii false false false false false true false false)
                                                                                                                                           (String.String
                                                                                                                                              (Ascii.Ascii false false false false false true false
                                                                                                                                                 false)
                                                                                                                                              (String.String
                                                                                                                                                 (Ascii.Ascii true false false true false true true
                                                                                                                                                    false)
                                                                                                                                                 (String.String
                                                                                                                                                    (Ascii.Ascii false true true false false true true
                                                                                                                                                       false)
                                                                                                                                                    (String.String
                                                                                                                                                       (Ascii.Ascii false false false false false true
                                                                                                                                                          false false)
                                                                                                                                                       (String.String
                                                                                                                                                          (Ascii.Ascii false false false true false
                                                                                                                                                             true false false)
                                                                                                                                                          (String.String
                                                                                                                                                             (Ascii.Ascii false true false true true
                                                                                                                                                                true true false)
                                                                                                                                                             (String.String
                                                                                                                                                                (Ascii.Ascii false false false false
                                                                                                                                                                   false true false false)
                                                                                                                                                                (String.String
                                                                                                                                                                   (Ascii.Ascii false false true true
                                                                                                                                                                      true true false false)
                                                                                                                                                                   (String.String
                                                                                                                                                                      (Ascii.Ascii true false true true
                                                                                                                                                                         true true false false)
                                                                                                                                                                      (String.String
                                                                                                                                                                         (Ascii.Ascii false false false
                                                                                                                                                                          false false true false false)
                                                                                                                                                                         (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          false false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          false false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          false true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true false true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false) String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (@imported_Original_LF__DOT__ImpParser_LF_ImpParser_SomeE imported_Original_LF__DOT__Imp_LF_Imp_com
       (imported_Original_LF__DOT__Imp_LF_Imp_CSeq imported_Original_LF__DOT__Imp_LF_Imp_CSkip
          (imported_Original_LF__DOT__Imp_LF_Imp_CSeq
             (imported_Original_LF__DOT__Imp_LF_Imp_CAsgn
                (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string imported_String_EmptyString
                   imported_String_String (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString))
                (imported_Original_LF__DOT__Imp_LF_Imp_AMult
                   (imported_Original_LF__DOT__Imp_LF_Imp_AMult
                      (imported_Original_LF__DOT__Imp_LF_Imp_AId
                         (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string imported_String_EmptyString
                            imported_String_String (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                      (imported_Original_LF__DOT__Imp_LF_Imp_AId
                         (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string imported_String_EmptyString
                            imported_String_String (String.String (Ascii.Ascii true false false true true true true false) String.EmptyString))))
                   (imported_Original_LF__DOT__Imp_LF_Imp_AMult
                      (imported_Original_LF__DOT__Imp_LF_Imp_AId
                         (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string imported_String_EmptyString
                            imported_String_String (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                      (imported_Original_LF__DOT__Imp_LF_Imp_AId
                         (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string imported_String_EmptyString
                            imported_String_String (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))))))
             (imported_Original_LF__DOT__Imp_LF_Imp_CSeq
                (imported_Original_LF__DOT__Imp_LF_Imp_CWhile
                   (imported_Original_LF__DOT__Imp_LF_Imp_BEq
                      (imported_Original_LF__DOT__Imp_LF_Imp_AId
                         (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string imported_String_EmptyString
                            imported_String_String (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                      (imported_Original_LF__DOT__Imp_LF_Imp_AId
                         (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string imported_String_EmptyString
                            imported_String_String (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))))
                   (imported_Original_LF__DOT__Imp_LF_Imp_CSeq
                      (imported_Original_LF__DOT__Imp_LF_Imp_CIf
                         (imported_Original_LF__DOT__Imp_LF_Imp_BAnd
                            (imported_Original_LF__DOT__Imp_LF_Imp_BLe
                               (imported_Original_LF__DOT__Imp_LF_Imp_AId
                                  (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string
                                     imported_String_EmptyString imported_String_String (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))
                               (imported_Original_LF__DOT__Imp_LF_Imp_AMult
                                  (imported_Original_LF__DOT__Imp_LF_Imp_AId
                                     (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string
                                        imported_String_EmptyString imported_String_String (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))
                                  (imported_Original_LF__DOT__Imp_LF_Imp_AId
                                     (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string
                                        imported_String_EmptyString imported_String_String (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))))
                            (imported_Original_LF__DOT__Imp_LF_Imp_BNot
                               (imported_Original_LF__DOT__Imp_LF_Imp_BEq
                                  (imported_Original_LF__DOT__Imp_LF_Imp_AId
                                     (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string
                                        imported_String_EmptyString imported_String_String (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                                  (imported_Original_LF__DOT__Imp_LF_Imp_ANum (imported_S (imported_S imported_0))))))
                         (imported_Original_LF__DOT__Imp_LF_Imp_CSeq
                            (imported_Original_LF__DOT__Imp_LF_Imp_CAsgn
                               (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string
                                  imported_String_EmptyString imported_String_String (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))
                               (imported_Original_LF__DOT__Imp_LF_Imp_AId
                                  (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string
                                     imported_String_EmptyString imported_String_String (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString))))
                            (imported_Original_LF__DOT__Imp_LF_Imp_CAsgn
                               (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string
                                  imported_String_EmptyString imported_String_String (String.String (Ascii.Ascii true false false true true true true false) String.EmptyString))
                               (imported_Original_LF__DOT__Imp_LF_Imp_AId
                                  (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string
                                     imported_String_EmptyString imported_String_String (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))))
                         imported_Original_LF__DOT__Imp_LF_Imp_CSkip)
                      imported_Original_LF__DOT__Imp_LF_Imp_CSkip))
                (imported_Original_LF__DOT__Imp_LF_Imp_CAsgn
                   (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string imported_String_EmptyString
                      imported_String_String (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))
                   (imported_Original_LF__DOT__Imp_LF_Imp_AId
                      (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string imported_String_EmptyString
                         imported_String_String (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))))))).
Parameter Original_LF__DOT__ImpParser_LF_ImpParser_eg2_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__ImpParser_LF_ImpParser_parse_iso
             (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                (String.String (Ascii.Ascii false true false true false false false false)
                   (String.String (Ascii.Ascii false false false false false true false false)
                      (String.String (Ascii.Ascii false false false false false true false false)
                         (String.String (Ascii.Ascii true true false false true true true false)
                            (String.String (Ascii.Ascii true true false true false true true false)
                               (String.String (Ascii.Ascii true false false true false true true false)
                                  (String.String (Ascii.Ascii false false false false true true true false)
                                     (String.String (Ascii.Ascii true true false true true true false false)
                                        (String.String (Ascii.Ascii false true false true false false false false)
                                           (String.String (Ascii.Ascii false false false false false true false false)
                                              (String.String (Ascii.Ascii false false false false false true false false)
                                                 (String.String (Ascii.Ascii false true false true true true true false)
                                                    (String.String (Ascii.Ascii false true false true true true false false)
                                                       (String.String (Ascii.Ascii true false true true true true false false)
                                                          (String.String (Ascii.Ascii false false false true true true true false)
                                                             (String.String (Ascii.Ascii false true false true false true false false)
                                                                (String.String (Ascii.Ascii true false false true true true true false)
                                                                   (String.String (Ascii.Ascii false true false true false true false false)
                                                                      (String.String (Ascii.Ascii false false false true false true false false)
                                                                         (String.String (Ascii.Ascii false false false true true true true false)
                                                                            (String.String (Ascii.Ascii false true false true false true false false)
                                                                               (String.String (Ascii.Ascii false false false true true true true false)
                                                                                  (String.String (Ascii.Ascii true false false true false true false false)
                                                                                     (String.String (Ascii.Ascii true true false true true true false false)
                                                                                        (String.String (Ascii.Ascii false true false true false false false false)
                                                                                           (String.String (Ascii.Ascii false false false false false true false false)
                                                                                              (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                 (String.String (Ascii.Ascii true true true false true true true false)
                                                                                                    (String.String (Ascii.Ascii false false false true false true true false)
                                                                                                       (String.String (Ascii.Ascii true false false true false true true false)
                                                                                                          (String.String (Ascii.Ascii false false true true false true true false)
                                                                                                             (String.String (Ascii.Ascii true false true false false true true false)
                                                                                                                (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                                   (String.String (Ascii.Ascii false false false true true true true false)
                                                                                                                      (String.String (Ascii.Ascii true false true true true true false false)
                                                                                                                         (String.String (Ascii.Ascii false false false true true true true false)
                                                                                                                            (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                                               (String.String
                                                                                                                                  (Ascii.Ascii false false true false false true true false)
                                                                                                                                  (String.String
                                                                                                                                     (Ascii.Ascii true true true true false true true false)
                                                                                                                                     (String.String
                                                                                                                                        (Ascii.Ascii false true false true false false false false)
                                                                                                                                        (String.String
                                                                                                                                           (Ascii.Ascii false false false false false true false false)
                                                                                                                                           (String.String
                                                                                                                                              (Ascii.Ascii false false false false false true false
                                                                                                                                                 false)
                                                                                                                                              (String.String
                                                                                                                                                 (Ascii.Ascii false false false false false true false
                                                                                                                                                    false)
                                                                                                                                                 (String.String
                                                                                                                                                    (Ascii.Ascii false false false false false true
                                                                                                                                                       false false)
                                                                                                                                                    (String.String
                                                                                                                                                       (Ascii.Ascii true false false true false true
                                                                                                                                                          true false)
                                                                                                                                                       (String.String
                                                                                                                                                          (Ascii.Ascii false true true false false true
                                                                                                                                                             true false)
                                                                                                                                                          (String.String
                                                                                                                                                             (Ascii.Ascii false false false false false
                                                                                                                                                                true false false)
                                                                                                                                                             (String.String
                                                                                                                                                                (Ascii.Ascii false false false true
                                                                                                                                                                   false true false false)
                                                                                                                                                                (String.String
                                                                                                                                                                   (Ascii.Ascii false true false true
                                                                                                                                                                      true true true false)
                                                                                                                                                                   (String.String
                                                                                                                                                                      (Ascii.Ascii false false false
                                                                                                                                                                         false false true false false)
                                                                                                                                                                      (String.String
                                                                                                                                                                         (Ascii.Ascii false false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                         (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          false false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          false false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          false true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true false true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false) String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          (Original_LF__DOT__ImpParser_LF_ImpParser_SomeE_iso
             (Original_LF__DOT__Imp_LF_Imp_CSeq_iso Original_LF__DOT__Imp_LF_Imp_CSkip_iso
                (Original_LF__DOT__Imp_LF_Imp_CSeq_iso
                   (Original_LF__DOT__Imp_LF_Imp_CAsgn_iso
                      (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                         (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString))
                      (Original_LF__DOT__Imp_LF_Imp_AMult_iso
                         (Original_LF__DOT__Imp_LF_Imp_AMult_iso
                            (Original_LF__DOT__Imp_LF_Imp_AId_iso
                               (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                  (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                            (Original_LF__DOT__Imp_LF_Imp_AId_iso
                               (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                  (String.String (Ascii.Ascii true false false true true true true false) String.EmptyString))))
                         (Original_LF__DOT__Imp_LF_Imp_AMult_iso
                            (Original_LF__DOT__Imp_LF_Imp_AId_iso
                               (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                  (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                            (Original_LF__DOT__Imp_LF_Imp_AId_iso
                               (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                  (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))))))
                   (Original_LF__DOT__Imp_LF_Imp_CSeq_iso
                      (Original_LF__DOT__Imp_LF_Imp_CWhile_iso
                         (Original_LF__DOT__Imp_LF_Imp_BEq_iso
                            (Original_LF__DOT__Imp_LF_Imp_AId_iso
                               (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                  (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                            (Original_LF__DOT__Imp_LF_Imp_AId_iso
                               (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                  (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))))
                         (Original_LF__DOT__Imp_LF_Imp_CSeq_iso
                            (Original_LF__DOT__Imp_LF_Imp_CIf_iso
                               (Original_LF__DOT__Imp_LF_Imp_BAnd_iso
                                  (Original_LF__DOT__Imp_LF_Imp_BLe_iso
                                     (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                        (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                           (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))
                                     (Original_LF__DOT__Imp_LF_Imp_AMult_iso
                                        (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                           (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                              (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))
                                        (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                           (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                              (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))))
                                  (Original_LF__DOT__Imp_LF_Imp_BNot_iso
                                     (Original_LF__DOT__Imp_LF_Imp_BEq_iso
                                        (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                           (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                              (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                                        (Original_LF__DOT__Imp_LF_Imp_ANum_iso (S_iso (S_iso _0_iso))))))
                               (Original_LF__DOT__Imp_LF_Imp_CSeq_iso
                                  (Original_LF__DOT__Imp_LF_Imp_CAsgn_iso
                                     (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                        (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))
                                     (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                        (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                           (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString))))
                                  (Original_LF__DOT__Imp_LF_Imp_CAsgn_iso
                                     (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                        (String.String (Ascii.Ascii true false false true true true true false) String.EmptyString))
                                     (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                        (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                           (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))))
                               Original_LF__DOT__Imp_LF_Imp_CSkip_iso)
                            Original_LF__DOT__Imp_LF_Imp_CSkip_iso))
                      (Original_LF__DOT__Imp_LF_Imp_CAsgn_iso
                         (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                            (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))
                         (Original_LF__DOT__Imp_LF_Imp_AId_iso
                            (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                               (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString))))))));
      from :=
        from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__ImpParser_LF_ImpParser_parse_iso
                (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                   (String.String (Ascii.Ascii false true false true false false false false)
                      (String.String (Ascii.Ascii false false false false false true false false)
                         (String.String (Ascii.Ascii false false false false false true false false)
                            (String.String (Ascii.Ascii true true false false true true true false)
                               (String.String (Ascii.Ascii true true false true false true true false)
                                  (String.String (Ascii.Ascii true false false true false true true false)
                                     (String.String (Ascii.Ascii false false false false true true true false)
                                        (String.String (Ascii.Ascii true true false true true true false false)
                                           (String.String (Ascii.Ascii false true false true false false false false)
                                              (String.String (Ascii.Ascii false false false false false true false false)
                                                 (String.String (Ascii.Ascii false false false false false true false false)
                                                    (String.String (Ascii.Ascii false true false true true true true false)
                                                       (String.String (Ascii.Ascii false true false true true true false false)
                                                          (String.String (Ascii.Ascii true false true true true true false false)
                                                             (String.String (Ascii.Ascii false false false true true true true false)
                                                                (String.String (Ascii.Ascii false true false true false true false false)
                                                                   (String.String (Ascii.Ascii true false false true true true true false)
                                                                      (String.String (Ascii.Ascii false true false true false true false false)
                                                                         (String.String (Ascii.Ascii false false false true false true false false)
                                                                            (String.String (Ascii.Ascii false false false true true true true false)
                                                                               (String.String (Ascii.Ascii false true false true false true false false)
                                                                                  (String.String (Ascii.Ascii false false false true true true true false)
                                                                                     (String.String (Ascii.Ascii true false false true false true false false)
                                                                                        (String.String (Ascii.Ascii true true false true true true false false)
                                                                                           (String.String (Ascii.Ascii false true false true false false false false)
                                                                                              (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                 (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                    (String.String (Ascii.Ascii true true true false true true true false)
                                                                                                       (String.String (Ascii.Ascii false false false true false true true false)
                                                                                                          (String.String (Ascii.Ascii true false false true false true true false)
                                                                                                             (String.String (Ascii.Ascii false false true true false true true false)
                                                                                                                (String.String (Ascii.Ascii true false true false false true true false)
                                                                                                                   (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                                      (String.String (Ascii.Ascii false false false true true true true false)
                                                                                                                         (String.String (Ascii.Ascii true false true true true true false false)
                                                                                                                            (String.String (Ascii.Ascii false false false true true true true false)
                                                                                                                               (String.String
                                                                                                                                  (Ascii.Ascii false false false false false true false false)
                                                                                                                                  (String.String
                                                                                                                                     (Ascii.Ascii false false true false false true true false)
                                                                                                                                     (String.String
                                                                                                                                        (Ascii.Ascii true true true true false true true false)
                                                                                                                                        (String.String
                                                                                                                                           (Ascii.Ascii false true false true false false false false)
                                                                                                                                           (String.String
                                                                                                                                              (Ascii.Ascii false false false false false true false
                                                                                                                                                 false)
                                                                                                                                              (String.String
                                                                                                                                                 (Ascii.Ascii false false false false false true false
                                                                                                                                                    false)
                                                                                                                                                 (String.String
                                                                                                                                                    (Ascii.Ascii false false false false false true
                                                                                                                                                       false false)
                                                                                                                                                    (String.String
                                                                                                                                                       (Ascii.Ascii false false false false false true
                                                                                                                                                          false false)
                                                                                                                                                       (String.String
                                                                                                                                                          (Ascii.Ascii true false false true false true
                                                                                                                                                             true false)
                                                                                                                                                          (String.String
                                                                                                                                                             (Ascii.Ascii false true true false false
                                                                                                                                                                true true false)
                                                                                                                                                             (String.String
                                                                                                                                                                (Ascii.Ascii false false false false
                                                                                                                                                                   false true false false)
                                                                                                                                                                (String.String
                                                                                                                                                                   (Ascii.Ascii false false false true
                                                                                                                                                                      false true false false)
                                                                                                                                                                   (String.String
                                                                                                                                                                      (Ascii.Ascii false true false
                                                                                                                                                                         true true true true false)
                                                                                                                                                                      (String.String
                                                                                                                                                                         (Ascii.Ascii false false false
                                                                                                                                                                          false false true false false)
                                                                                                                                                                         (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          false false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          false false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          false true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true false true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false) String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
             (Original_LF__DOT__ImpParser_LF_ImpParser_SomeE_iso
                (Original_LF__DOT__Imp_LF_Imp_CSeq_iso Original_LF__DOT__Imp_LF_Imp_CSkip_iso
                   (Original_LF__DOT__Imp_LF_Imp_CSeq_iso
                      (Original_LF__DOT__Imp_LF_Imp_CAsgn_iso
                         (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                            (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString))
                         (Original_LF__DOT__Imp_LF_Imp_AMult_iso
                            (Original_LF__DOT__Imp_LF_Imp_AMult_iso
                               (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                  (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                     (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                               (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                  (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                     (String.String (Ascii.Ascii true false false true true true true false) String.EmptyString))))
                            (Original_LF__DOT__Imp_LF_Imp_AMult_iso
                               (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                  (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                     (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                               (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                  (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                     (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))))))
                      (Original_LF__DOT__Imp_LF_Imp_CSeq_iso
                         (Original_LF__DOT__Imp_LF_Imp_CWhile_iso
                            (Original_LF__DOT__Imp_LF_Imp_BEq_iso
                               (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                  (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                     (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                               (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                  (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                     (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))))
                            (Original_LF__DOT__Imp_LF_Imp_CSeq_iso
                               (Original_LF__DOT__Imp_LF_Imp_CIf_iso
                                  (Original_LF__DOT__Imp_LF_Imp_BAnd_iso
                                     (Original_LF__DOT__Imp_LF_Imp_BLe_iso
                                        (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                           (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                              (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))
                                        (Original_LF__DOT__Imp_LF_Imp_AMult_iso
                                           (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                              (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                                 (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))
                                           (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                              (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                                 (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))))
                                     (Original_LF__DOT__Imp_LF_Imp_BNot_iso
                                        (Original_LF__DOT__Imp_LF_Imp_BEq_iso
                                           (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                              (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                                 (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                                           (Original_LF__DOT__Imp_LF_Imp_ANum_iso (S_iso (S_iso _0_iso))))))
                                  (Original_LF__DOT__Imp_LF_Imp_CSeq_iso
                                     (Original_LF__DOT__Imp_LF_Imp_CAsgn_iso
                                        (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                           (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))
                                        (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                           (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                              (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString))))
                                     (Original_LF__DOT__Imp_LF_Imp_CAsgn_iso
                                        (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                           (String.String (Ascii.Ascii true false false true true true true false) String.EmptyString))
                                        (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                           (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                              (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))))
                                  Original_LF__DOT__Imp_LF_Imp_CSkip_iso)
                               Original_LF__DOT__Imp_LF_Imp_CSkip_iso))
                         (Original_LF__DOT__Imp_LF_Imp_CAsgn_iso
                            (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                               (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))
                            (Original_LF__DOT__Imp_LF_Imp_AId_iso
                               (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                  (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))))))));
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq
                (imported_Original_LF__DOT__ImpParser_LF_ImpParser_parse
                   (StringOptimizations.imported_string
                      (String.String (Ascii.Ascii false true false true false false false false)
                         (String.String (Ascii.Ascii false false false false false true false false)
                            (String.String (Ascii.Ascii false false false false false true false false)
                               (String.String (Ascii.Ascii true true false false true true true false)
                                  (String.String (Ascii.Ascii true true false true false true true false)
                                     (String.String (Ascii.Ascii true false false true false true true false)
                                        (String.String (Ascii.Ascii false false false false true true true false)
                                           (String.String (Ascii.Ascii true true false true true true false false)
                                              (String.String (Ascii.Ascii false true false true false false false false)
                                                 (String.String (Ascii.Ascii false false false false false true false false)
                                                    (String.String (Ascii.Ascii false false false false false true false false)
                                                       (String.String (Ascii.Ascii false true false true true true true false)
                                                          (String.String (Ascii.Ascii false true false true true true false false)
                                                             (String.String (Ascii.Ascii true false true true true true false false)
                                                                (String.String (Ascii.Ascii false false false true true true true false)
                                                                   (String.String (Ascii.Ascii false true false true false true false false)
                                                                      (String.String (Ascii.Ascii true false false true true true true false)
                                                                         (String.String (Ascii.Ascii false true false true false true false false)
                                                                            (String.String (Ascii.Ascii false false false true false true false false)
                                                                               (String.String (Ascii.Ascii false false false true true true true false)
                                                                                  (String.String (Ascii.Ascii false true false true false true false false)
                                                                                     (String.String (Ascii.Ascii false false false true true true true false)
                                                                                        (String.String (Ascii.Ascii true false false true false true false false)
                                                                                           (String.String (Ascii.Ascii true true false true true true false false)
                                                                                              (String.String (Ascii.Ascii false true false true false false false false)
                                                                                                 (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                    (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                       (String.String (Ascii.Ascii true true true false true true true false)
                                                                                                          (String.String (Ascii.Ascii false false false true false true true false)
                                                                                                             (String.String (Ascii.Ascii true false false true false true true false)
                                                                                                                (String.String (Ascii.Ascii false false true true false true true false)
                                                                                                                   (String.String (Ascii.Ascii true false true false false true true false)
                                                                                                                      (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                                         (String.String (Ascii.Ascii false false false true true true true false)
                                                                                                                            (String.String (Ascii.Ascii true false true true true true false false)
                                                                                                                               (String.String (Ascii.Ascii false false false true true true true false)
                                                                                                                                  (String.String
                                                                                                                                     (Ascii.Ascii false false false false false true false false)
                                                                                                                                     (String.String
                                                                                                                                        (Ascii.Ascii false false true false false true true false)
                                                                                                                                        (String.String
                                                                                                                                           (Ascii.Ascii true true true true false true true false)
                                                                                                                                           (String.String
                                                                                                                                              (Ascii.Ascii false true false true false false false
                                                                                                                                                 false)
                                                                                                                                              (String.String
                                                                                                                                                 (Ascii.Ascii false false false false false true false
                                                                                                                                                    false)
                                                                                                                                                 (String.String
                                                                                                                                                    (Ascii.Ascii false false false false false true
                                                                                                                                                       false false)
                                                                                                                                                    (String.String
                                                                                                                                                       (Ascii.Ascii false false false false false true
                                                                                                                                                          false false)
                                                                                                                                                       (String.String
                                                                                                                                                          (Ascii.Ascii false false false false false
                                                                                                                                                             true false false)
                                                                                                                                                          (String.String
                                                                                                                                                             (Ascii.Ascii true false false true false
                                                                                                                                                                true true false)
                                                                                                                                                             (String.String
                                                                                                                                                                (Ascii.Ascii false true true false
                                                                                                                                                                   false true true false)
                                                                                                                                                                (String.String
                                                                                                                                                                   (Ascii.Ascii false false false false
                                                                                                                                                                      false true false false)
                                                                                                                                                                   (String.String
                                                                                                                                                                      (Ascii.Ascii false false false
                                                                                                                                                                         true false true false false)
                                                                                                                                                                      (String.String
                                                                                                                                                                         (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                         (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          false false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          false false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          false true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true false true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false) String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                (imported_Original_LF__DOT__ImpParser_LF_ImpParser_SomeE
                   (imported_Original_LF__DOT__Imp_LF_Imp_CSeq imported_Original_LF__DOT__Imp_LF_Imp_CSkip
                      (imported_Original_LF__DOT__Imp_LF_Imp_CSeq
                         (imported_Original_LF__DOT__Imp_LF_Imp_CAsgn (StringOptimizations.imported_string (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString))
                            (imported_Original_LF__DOT__Imp_LF_Imp_AMult
                               (imported_Original_LF__DOT__Imp_LF_Imp_AMult
                                  (imported_Original_LF__DOT__Imp_LF_Imp_AId
                                     (StringOptimizations.imported_string (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                                  (imported_Original_LF__DOT__Imp_LF_Imp_AId
                                     (StringOptimizations.imported_string (String.String (Ascii.Ascii true false false true true true true false) String.EmptyString))))
                               (imported_Original_LF__DOT__Imp_LF_Imp_AMult
                                  (imported_Original_LF__DOT__Imp_LF_Imp_AId
                                     (StringOptimizations.imported_string (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                                  (imported_Original_LF__DOT__Imp_LF_Imp_AId
                                     (StringOptimizations.imported_string (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))))))
                         (imported_Original_LF__DOT__Imp_LF_Imp_CSeq
                            (imported_Original_LF__DOT__Imp_LF_Imp_CWhile
                               (imported_Original_LF__DOT__Imp_LF_Imp_BEq
                                  (imported_Original_LF__DOT__Imp_LF_Imp_AId
                                     (StringOptimizations.imported_string (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                                  (imported_Original_LF__DOT__Imp_LF_Imp_AId
                                     (StringOptimizations.imported_string (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))))
                               (imported_Original_LF__DOT__Imp_LF_Imp_CSeq
                                  (imported_Original_LF__DOT__Imp_LF_Imp_CIf
                                     (imported_Original_LF__DOT__Imp_LF_Imp_BAnd
                                        (imported_Original_LF__DOT__Imp_LF_Imp_BLe
                                           (imported_Original_LF__DOT__Imp_LF_Imp_AId
                                              (StringOptimizations.imported_string (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))
                                           (imported_Original_LF__DOT__Imp_LF_Imp_AMult
                                              (imported_Original_LF__DOT__Imp_LF_Imp_AId
                                                 (StringOptimizations.imported_string (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))
                                              (imported_Original_LF__DOT__Imp_LF_Imp_AId
                                                 (StringOptimizations.imported_string (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))))
                                        (imported_Original_LF__DOT__Imp_LF_Imp_BNot
                                           (imported_Original_LF__DOT__Imp_LF_Imp_BEq
                                              (imported_Original_LF__DOT__Imp_LF_Imp_AId
                                                 (StringOptimizations.imported_string (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                                              (imported_Original_LF__DOT__Imp_LF_Imp_ANum (imported_S (imported_S imported_0))))))
                                     (imported_Original_LF__DOT__Imp_LF_Imp_CSeq
                                        (imported_Original_LF__DOT__Imp_LF_Imp_CAsgn
                                           (StringOptimizations.imported_string (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))
                                           (imported_Original_LF__DOT__Imp_LF_Imp_AId
                                              (StringOptimizations.imported_string (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString))))
                                        (imported_Original_LF__DOT__Imp_LF_Imp_CAsgn
                                           (StringOptimizations.imported_string (String.String (Ascii.Ascii true false false true true true true false) String.EmptyString))
                                           (imported_Original_LF__DOT__Imp_LF_Imp_AId
                                              (StringOptimizations.imported_string (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))))
                                     imported_Original_LF__DOT__Imp_LF_Imp_CSkip)
                                  imported_Original_LF__DOT__Imp_LF_Imp_CSkip))
                            (imported_Original_LF__DOT__Imp_LF_Imp_CAsgn
                               (StringOptimizations.imported_string (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))
                               (imported_Original_LF__DOT__Imp_LF_Imp_AId
                                  (StringOptimizations.imported_string (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))))))) =>
        to_from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__ImpParser_LF_ImpParser_parse_iso
                (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                   (String.String (Ascii.Ascii false true false true false false false false)
                      (String.String (Ascii.Ascii false false false false false true false false)
                         (String.String (Ascii.Ascii false false false false false true false false)
                            (String.String (Ascii.Ascii true true false false true true true false)
                               (String.String (Ascii.Ascii true true false true false true true false)
                                  (String.String (Ascii.Ascii true false false true false true true false)
                                     (String.String (Ascii.Ascii false false false false true true true false)
                                        (String.String (Ascii.Ascii true true false true true true false false)
                                           (String.String (Ascii.Ascii false true false true false false false false)
                                              (String.String (Ascii.Ascii false false false false false true false false)
                                                 (String.String (Ascii.Ascii false false false false false true false false)
                                                    (String.String (Ascii.Ascii false true false true true true true false)
                                                       (String.String (Ascii.Ascii false true false true true true false false)
                                                          (String.String (Ascii.Ascii true false true true true true false false)
                                                             (String.String (Ascii.Ascii false false false true true true true false)
                                                                (String.String (Ascii.Ascii false true false true false true false false)
                                                                   (String.String (Ascii.Ascii true false false true true true true false)
                                                                      (String.String (Ascii.Ascii false true false true false true false false)
                                                                         (String.String (Ascii.Ascii false false false true false true false false)
                                                                            (String.String (Ascii.Ascii false false false true true true true false)
                                                                               (String.String (Ascii.Ascii false true false true false true false false)
                                                                                  (String.String (Ascii.Ascii false false false true true true true false)
                                                                                     (String.String (Ascii.Ascii true false false true false true false false)
                                                                                        (String.String (Ascii.Ascii true true false true true true false false)
                                                                                           (String.String (Ascii.Ascii false true false true false false false false)
                                                                                              (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                 (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                    (String.String (Ascii.Ascii true true true false true true true false)
                                                                                                       (String.String (Ascii.Ascii false false false true false true true false)
                                                                                                          (String.String (Ascii.Ascii true false false true false true true false)
                                                                                                             (String.String (Ascii.Ascii false false true true false true true false)
                                                                                                                (String.String (Ascii.Ascii true false true false false true true false)
                                                                                                                   (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                                      (String.String (Ascii.Ascii false false false true true true true false)
                                                                                                                         (String.String (Ascii.Ascii true false true true true true false false)
                                                                                                                            (String.String (Ascii.Ascii false false false true true true true false)
                                                                                                                               (String.String
                                                                                                                                  (Ascii.Ascii false false false false false true false false)
                                                                                                                                  (String.String
                                                                                                                                     (Ascii.Ascii false false true false false true true false)
                                                                                                                                     (String.String
                                                                                                                                        (Ascii.Ascii true true true true false true true false)
                                                                                                                                        (String.String
                                                                                                                                           (Ascii.Ascii false true false true false false false false)
                                                                                                                                           (String.String
                                                                                                                                              (Ascii.Ascii false false false false false true false
                                                                                                                                                 false)
                                                                                                                                              (String.String
                                                                                                                                                 (Ascii.Ascii false false false false false true false
                                                                                                                                                    false)
                                                                                                                                                 (String.String
                                                                                                                                                    (Ascii.Ascii false false false false false true
                                                                                                                                                       false false)
                                                                                                                                                    (String.String
                                                                                                                                                       (Ascii.Ascii false false false false false true
                                                                                                                                                          false false)
                                                                                                                                                       (String.String
                                                                                                                                                          (Ascii.Ascii true false false true false true
                                                                                                                                                             true false)
                                                                                                                                                          (String.String
                                                                                                                                                             (Ascii.Ascii false true true false false
                                                                                                                                                                true true false)
                                                                                                                                                             (String.String
                                                                                                                                                                (Ascii.Ascii false false false false
                                                                                                                                                                   false true false false)
                                                                                                                                                                (String.String
                                                                                                                                                                   (Ascii.Ascii false false false true
                                                                                                                                                                      false true false false)
                                                                                                                                                                   (String.String
                                                                                                                                                                      (Ascii.Ascii false true false
                                                                                                                                                                         true true true true false)
                                                                                                                                                                      (String.String
                                                                                                                                                                         (Ascii.Ascii false false false
                                                                                                                                                                          false false true false false)
                                                                                                                                                                         (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          false false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          false false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          false true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true false true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false) String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
             (Original_LF__DOT__ImpParser_LF_ImpParser_SomeE_iso
                (Original_LF__DOT__Imp_LF_Imp_CSeq_iso Original_LF__DOT__Imp_LF_Imp_CSkip_iso
                   (Original_LF__DOT__Imp_LF_Imp_CSeq_iso
                      (Original_LF__DOT__Imp_LF_Imp_CAsgn_iso
                         (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                            (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString))
                         (Original_LF__DOT__Imp_LF_Imp_AMult_iso
                            (Original_LF__DOT__Imp_LF_Imp_AMult_iso
                               (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                  (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                     (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                               (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                  (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                     (String.String (Ascii.Ascii true false false true true true true false) String.EmptyString))))
                            (Original_LF__DOT__Imp_LF_Imp_AMult_iso
                               (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                  (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                     (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                               (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                  (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                     (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))))))
                      (Original_LF__DOT__Imp_LF_Imp_CSeq_iso
                         (Original_LF__DOT__Imp_LF_Imp_CWhile_iso
                            (Original_LF__DOT__Imp_LF_Imp_BEq_iso
                               (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                  (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                     (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                               (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                  (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                     (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))))
                            (Original_LF__DOT__Imp_LF_Imp_CSeq_iso
                               (Original_LF__DOT__Imp_LF_Imp_CIf_iso
                                  (Original_LF__DOT__Imp_LF_Imp_BAnd_iso
                                     (Original_LF__DOT__Imp_LF_Imp_BLe_iso
                                        (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                           (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                              (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))
                                        (Original_LF__DOT__Imp_LF_Imp_AMult_iso
                                           (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                              (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                                 (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))
                                           (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                              (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                                 (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))))
                                     (Original_LF__DOT__Imp_LF_Imp_BNot_iso
                                        (Original_LF__DOT__Imp_LF_Imp_BEq_iso
                                           (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                              (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                                 (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                                           (Original_LF__DOT__Imp_LF_Imp_ANum_iso (S_iso (S_iso _0_iso))))))
                                  (Original_LF__DOT__Imp_LF_Imp_CSeq_iso
                                     (Original_LF__DOT__Imp_LF_Imp_CAsgn_iso
                                        (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                           (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))
                                        (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                           (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                              (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString))))
                                     (Original_LF__DOT__Imp_LF_Imp_CAsgn_iso
                                        (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                           (String.String (Ascii.Ascii true false false true true true true false) String.EmptyString))
                                        (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                           (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                              (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))))
                                  Original_LF__DOT__Imp_LF_Imp_CSkip_iso)
                               Original_LF__DOT__Imp_LF_Imp_CSkip_iso))
                         (Original_LF__DOT__Imp_LF_Imp_CAsgn_iso
                            (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                               (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))
                            (Original_LF__DOT__Imp_LF_Imp_AId_iso
                               (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                  (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))))))))
          x;
      from_to :=
        fun
          x : Original.LF_DOT_ImpParser.LF.ImpParser.parse
                (String.String (Ascii.Ascii false true false true false false false false)
                   (String.String (Ascii.Ascii false false false false false true false false)
                      (String.String (Ascii.Ascii false false false false false true false false)
                         (String.String (Ascii.Ascii true true false false true true true false)
                            (String.String (Ascii.Ascii true true false true false true true false)
                               (String.String (Ascii.Ascii true false false true false true true false)
                                  (String.String (Ascii.Ascii false false false false true true true false)
                                     (String.String (Ascii.Ascii true true false true true true false false)
                                        (String.String (Ascii.Ascii false true false true false false false false)
                                           (String.String (Ascii.Ascii false false false false false true false false)
                                              (String.String (Ascii.Ascii false false false false false true false false)
                                                 (String.String (Ascii.Ascii false true false true true true true false)
                                                    (String.String (Ascii.Ascii false true false true true true false false)
                                                       (String.String (Ascii.Ascii true false true true true true false false)
                                                          (String.String (Ascii.Ascii false false false true true true true false)
                                                             (String.String (Ascii.Ascii false true false true false true false false)
                                                                (String.String (Ascii.Ascii true false false true true true true false)
                                                                   (String.String (Ascii.Ascii false true false true false true false false)
                                                                      (String.String (Ascii.Ascii false false false true false true false false)
                                                                         (String.String (Ascii.Ascii false false false true true true true false)
                                                                            (String.String (Ascii.Ascii false true false true false true false false)
                                                                               (String.String (Ascii.Ascii false false false true true true true false)
                                                                                  (String.String (Ascii.Ascii true false false true false true false false)
                                                                                     (String.String (Ascii.Ascii true true false true true true false false)
                                                                                        (String.String (Ascii.Ascii false true false true false false false false)
                                                                                           (String.String (Ascii.Ascii false false false false false true false false)
                                                                                              (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                 (String.String (Ascii.Ascii true true true false true true true false)
                                                                                                    (String.String (Ascii.Ascii false false false true false true true false)
                                                                                                       (String.String (Ascii.Ascii true false false true false true true false)
                                                                                                          (String.String (Ascii.Ascii false false true true false true true false)
                                                                                                             (String.String (Ascii.Ascii true false true false false true true false)
                                                                                                                (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                                   (String.String (Ascii.Ascii false false false true true true true false)
                                                                                                                      (String.String (Ascii.Ascii true false true true true true false false)
                                                                                                                         (String.String (Ascii.Ascii false false false true true true true false)
                                                                                                                            (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                                               (String.String
                                                                                                                                  (Ascii.Ascii false false true false false true true false)
                                                                                                                                  (String.String
                                                                                                                                     (Ascii.Ascii true true true true false true true false)
                                                                                                                                     (String.String
                                                                                                                                        (Ascii.Ascii false true false true false false false false)
                                                                                                                                        (String.String
                                                                                                                                           (Ascii.Ascii false false false false false true false false)
                                                                                                                                           (String.String
                                                                                                                                              (Ascii.Ascii false false false false false true false
                                                                                                                                                 false)
                                                                                                                                              (String.String
                                                                                                                                                 (Ascii.Ascii false false false false false true false
                                                                                                                                                    false)
                                                                                                                                                 (String.String
                                                                                                                                                    (Ascii.Ascii false false false false false true
                                                                                                                                                       false false)
                                                                                                                                                    (String.String
                                                                                                                                                       (Ascii.Ascii true false false true false true
                                                                                                                                                          true false)
                                                                                                                                                       (String.String
                                                                                                                                                          (Ascii.Ascii false true true false false true
                                                                                                                                                             true false)
                                                                                                                                                          (String.String
                                                                                                                                                             (Ascii.Ascii false false false false false
                                                                                                                                                                true false false)
                                                                                                                                                             (String.String
                                                                                                                                                                (Ascii.Ascii false false false true
                                                                                                                                                                   false true false false)
                                                                                                                                                                (String.String
                                                                                                                                                                   (Ascii.Ascii false true false true
                                                                                                                                                                      true true true false)
                                                                                                                                                                   (String.String
                                                                                                                                                                      (Ascii.Ascii false false false
                                                                                                                                                                         false false true false false)
                                                                                                                                                                      (String.String
                                                                                                                                                                         (Ascii.Ascii false false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                         (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          false false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          false false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          false true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true false true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false) String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) =
              Original.LF_DOT_ImpParser.LF.ImpParser.SomeE
                (Original.LF_DOT_Imp.LF.Imp.CSeq Original.LF_DOT_Imp.LF.Imp.CSkip
                   (Original.LF_DOT_Imp.LF.Imp.CSeq
                      (Original.LF_DOT_Imp.LF.Imp.CAsgn (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)
                         (Original.LF_DOT_Imp.LF.Imp.AMult
                            (Original.LF_DOT_Imp.LF.Imp.AMult (Original.LF_DOT_Imp.LF.Imp.AId (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))
                               (Original.LF_DOT_Imp.LF.Imp.AId (String.String (Ascii.Ascii true false false true true true true false) String.EmptyString)))
                            (Original.LF_DOT_Imp.LF.Imp.AMult (Original.LF_DOT_Imp.LF.Imp.AId (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))
                               (Original.LF_DOT_Imp.LF.Imp.AId (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))))
                      (Original.LF_DOT_Imp.LF.Imp.CSeq
                         (Original.LF_DOT_Imp.LF.Imp.CWhile
                            (Original.LF_DOT_Imp.LF.Imp.BEq (Original.LF_DOT_Imp.LF.Imp.AId (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))
                               (Original.LF_DOT_Imp.LF.Imp.AId (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                            (Original.LF_DOT_Imp.LF.Imp.CSeq
                               (Original.LF_DOT_Imp.LF.Imp.CIf
                                  (Original.LF_DOT_Imp.LF.Imp.BAnd
                                     (Original.LF_DOT_Imp.LF.Imp.BLe (Original.LF_DOT_Imp.LF.Imp.AId (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString))
                                        (Original.LF_DOT_Imp.LF.Imp.AMult (Original.LF_DOT_Imp.LF.Imp.AId (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString))
                                           (Original.LF_DOT_Imp.LF.Imp.AId (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString))))
                                     (Original.LF_DOT_Imp.LF.Imp.BNot
                                        (Original.LF_DOT_Imp.LF.Imp.BEq (Original.LF_DOT_Imp.LF.Imp.AId (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))
                                           (Original.LF_DOT_Imp.LF.Imp.ANum 2))))
                                  (Original.LF_DOT_Imp.LF.Imp.CSeq
                                     (Original.LF_DOT_Imp.LF.Imp.CAsgn (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)
                                        (Original.LF_DOT_Imp.LF.Imp.AId (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))
                                     (Original.LF_DOT_Imp.LF.Imp.CAsgn (String.String (Ascii.Ascii true false false true true true true false) String.EmptyString)
                                        (Original.LF_DOT_Imp.LF.Imp.AId (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString))))
                                  Original.LF_DOT_Imp.LF.Imp.CSkip)
                               Original.LF_DOT_Imp.LF.Imp.CSkip))
                         (Original.LF_DOT_Imp.LF.Imp.CAsgn (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)
                            (Original.LF_DOT_Imp.LF.Imp.AId (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))))) =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__ImpParser_LF_ImpParser_parse_iso
                   (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                      (String.String (Ascii.Ascii false true false true false false false false)
                         (String.String (Ascii.Ascii false false false false false true false false)
                            (String.String (Ascii.Ascii false false false false false true false false)
                               (String.String (Ascii.Ascii true true false false true true true false)
                                  (String.String (Ascii.Ascii true true false true false true true false)
                                     (String.String (Ascii.Ascii true false false true false true true false)
                                        (String.String (Ascii.Ascii false false false false true true true false)
                                           (String.String (Ascii.Ascii true true false true true true false false)
                                              (String.String (Ascii.Ascii false true false true false false false false)
                                                 (String.String (Ascii.Ascii false false false false false true false false)
                                                    (String.String (Ascii.Ascii false false false false false true false false)
                                                       (String.String (Ascii.Ascii false true false true true true true false)
                                                          (String.String (Ascii.Ascii false true false true true true false false)
                                                             (String.String (Ascii.Ascii true false true true true true false false)
                                                                (String.String (Ascii.Ascii false false false true true true true false)
                                                                   (String.String (Ascii.Ascii false true false true false true false false)
                                                                      (String.String (Ascii.Ascii true false false true true true true false)
                                                                         (String.String (Ascii.Ascii false true false true false true false false)
                                                                            (String.String (Ascii.Ascii false false false true false true false false)
                                                                               (String.String (Ascii.Ascii false false false true true true true false)
                                                                                  (String.String (Ascii.Ascii false true false true false true false false)
                                                                                     (String.String (Ascii.Ascii false false false true true true true false)
                                                                                        (String.String (Ascii.Ascii true false false true false true false false)
                                                                                           (String.String (Ascii.Ascii true true false true true true false false)
                                                                                              (String.String (Ascii.Ascii false true false true false false false false)
                                                                                                 (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                    (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                       (String.String (Ascii.Ascii true true true false true true true false)
                                                                                                          (String.String (Ascii.Ascii false false false true false true true false)
                                                                                                             (String.String (Ascii.Ascii true false false true false true true false)
                                                                                                                (String.String (Ascii.Ascii false false true true false true true false)
                                                                                                                   (String.String (Ascii.Ascii true false true false false true true false)
                                                                                                                      (String.String (Ascii.Ascii false false false false false true false false)
                                                                                                                         (String.String (Ascii.Ascii false false false true true true true false)
                                                                                                                            (String.String (Ascii.Ascii true false true true true true false false)
                                                                                                                               (String.String (Ascii.Ascii false false false true true true true false)
                                                                                                                                  (String.String
                                                                                                                                     (Ascii.Ascii false false false false false true false false)
                                                                                                                                     (String.String
                                                                                                                                        (Ascii.Ascii false false true false false true true false)
                                                                                                                                        (String.String
                                                                                                                                           (Ascii.Ascii true true true true false true true false)
                                                                                                                                           (String.String
                                                                                                                                              (Ascii.Ascii false true false true false false false
                                                                                                                                                 false)
                                                                                                                                              (String.String
                                                                                                                                                 (Ascii.Ascii false false false false false true false
                                                                                                                                                    false)
                                                                                                                                                 (String.String
                                                                                                                                                    (Ascii.Ascii false false false false false true
                                                                                                                                                       false false)
                                                                                                                                                    (String.String
                                                                                                                                                       (Ascii.Ascii false false false false false true
                                                                                                                                                          false false)
                                                                                                                                                       (String.String
                                                                                                                                                          (Ascii.Ascii false false false false false
                                                                                                                                                             true false false)
                                                                                                                                                          (String.String
                                                                                                                                                             (Ascii.Ascii true false false true false
                                                                                                                                                                true true false)
                                                                                                                                                             (String.String
                                                                                                                                                                (Ascii.Ascii false true true false
                                                                                                                                                                   false true true false)
                                                                                                                                                                (String.String
                                                                                                                                                                   (Ascii.Ascii false false false false
                                                                                                                                                                      false true false false)
                                                                                                                                                                   (String.String
                                                                                                                                                                      (Ascii.Ascii false false false
                                                                                                                                                                         true false true false false)
                                                                                                                                                                      (String.String
                                                                                                                                                                         (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                         (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          false false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          false false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          false true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true false true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          false true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false false
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true true
                                                                                                                                                                          true false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false true
                                                                                                                                                                          false false true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true false false false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false true true true true
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii true false true
                                                                                                                                                                          true true true false false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false true false
                                                                                                                                                                          true true true true false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false)
                                                                                                                                                                          (String.String
                                                                                                                                                                          (Ascii.Ascii false false
                                                                                                                                                                          false false false true false
                                                                                                                                                                          false) String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                (Original_LF__DOT__ImpParser_LF_ImpParser_SomeE_iso
                   (Original_LF__DOT__Imp_LF_Imp_CSeq_iso Original_LF__DOT__Imp_LF_Imp_CSkip_iso
                      (Original_LF__DOT__Imp_LF_Imp_CSeq_iso
                         (Original_LF__DOT__Imp_LF_Imp_CAsgn_iso
                            (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                               (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString))
                            (Original_LF__DOT__Imp_LF_Imp_AMult_iso
                               (Original_LF__DOT__Imp_LF_Imp_AMult_iso
                                  (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                     (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                        (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                                  (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                     (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                        (String.String (Ascii.Ascii true false false true true true true false) String.EmptyString))))
                               (Original_LF__DOT__Imp_LF_Imp_AMult_iso
                                  (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                     (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                        (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                                  (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                     (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                        (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))))))
                         (Original_LF__DOT__Imp_LF_Imp_CSeq_iso
                            (Original_LF__DOT__Imp_LF_Imp_CWhile_iso
                               (Original_LF__DOT__Imp_LF_Imp_BEq_iso
                                  (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                     (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                        (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                                  (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                     (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                        (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))))
                               (Original_LF__DOT__Imp_LF_Imp_CSeq_iso
                                  (Original_LF__DOT__Imp_LF_Imp_CIf_iso
                                     (Original_LF__DOT__Imp_LF_Imp_BAnd_iso
                                        (Original_LF__DOT__Imp_LF_Imp_BLe_iso
                                           (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                              (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                                 (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))
                                           (Original_LF__DOT__Imp_LF_Imp_AMult_iso
                                              (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                                 (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                                    (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))
                                              (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                                 (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                                    (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))))
                                        (Original_LF__DOT__Imp_LF_Imp_BNot_iso
                                           (Original_LF__DOT__Imp_LF_Imp_BEq_iso
                                              (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                                 (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                                    (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString)))
                                              (Original_LF__DOT__Imp_LF_Imp_ANum_iso (S_iso (S_iso _0_iso))))))
                                     (Original_LF__DOT__Imp_LF_Imp_CSeq_iso
                                        (Original_LF__DOT__Imp_LF_Imp_CAsgn_iso
                                           (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                              (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))
                                           (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                              (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                                 (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString))))
                                        (Original_LF__DOT__Imp_LF_Imp_CAsgn_iso
                                           (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                              (String.String (Ascii.Ascii true false false true true true true false) String.EmptyString))
                                           (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                              (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                                 (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))))
                                     Original_LF__DOT__Imp_LF_Imp_CSkip_iso)
                                  Original_LF__DOT__Imp_LF_Imp_CSkip_iso))
                            (Original_LF__DOT__Imp_LF_Imp_CAsgn_iso
                               (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                  (String.String (Ascii.Ascii false false false true true true true false) String.EmptyString))
                               (Original_LF__DOT__Imp_LF_Imp_AId_iso
                                  (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                     (String.String (Ascii.Ascii false true false true true true true false) String.EmptyString)))))))))
             x)
    |} Original.LF_DOT_ImpParser.LF.ImpParser.eg2 imported_Original_LF__DOT__ImpParser_LF_ImpParser_eg2.
Existing Instance Original_LF__DOT__ImpParser_LF_ImpParser_eg2_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ImpParser.LF.ImpParser.eg2 ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_eg2_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ImpParser.LF.ImpParser.eg2 imported_Original_LF__DOT__ImpParser_LF_ImpParser_eg2 ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_eg2_iso; constructor : typeclass_instances.


End Interface.