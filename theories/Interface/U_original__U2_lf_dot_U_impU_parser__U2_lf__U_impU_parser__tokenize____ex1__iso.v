From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_string__string__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.list__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__tokenize__iso Interface.cons__iso Interface.nil__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_string__string__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.list__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__tokenize__iso Interface.cons__iso Interface.nil__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__tokenize__iso.CodeBlocks Interface.cons__iso.CodeBlocks Interface.nil__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.false__iso.Interface <+ Interface.list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__tokenize__iso.Interface <+ Interface.cons__iso.Interface <+ Interface.nil__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__ex1 : @imported_Corelib_Init_Logic_eq (imported_list imported_String_string)
    (imported_Original_LF__DOT__ImpParser_LF_ImpParser_tokenize
       (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string imported_String_EmptyString
          imported_String_String
          (String.String (Ascii.Ascii true false false false false true true false)
             (String.String (Ascii.Ascii false true false false false true true false)
                (String.String (Ascii.Ascii true true false false false true true false)
                   (String.String (Ascii.Ascii true false false false true true false false)
                      (String.String (Ascii.Ascii false true false false true true false false)
                         (String.String (Ascii.Ascii true false true true true true false false)
                            (String.String (Ascii.Ascii true true false false true true false false)
                               (String.String (Ascii.Ascii false false false false false true false false)
                                  (String.String (Ascii.Ascii false false false false false true false false)
                                     (String.String (Ascii.Ascii false true false false true true false false)
                                        (String.String (Ascii.Ascii false true false false true true false false)
                                           (String.String (Ascii.Ascii true true false false true true false false)
                                              (String.String (Ascii.Ascii false true false true false true false false)
                                                 (String.String (Ascii.Ascii false false false true false true false false)
                                                    (String.String (Ascii.Ascii true true false false true true false false)
                                                       (String.String (Ascii.Ascii true true false true false true false false)
                                                          (String.String (Ascii.Ascii false false false true false true false false)
                                                             (String.String (Ascii.Ascii true false false false false true true false)
                                                                (String.String (Ascii.Ascii true true false true false true false false)
                                                                   (String.String (Ascii.Ascii true true false false false true true false)
                                                                      (String.String (Ascii.Ascii true false false true false true false false)
                                                                         (String.String (Ascii.Ascii true false false true false true false false) String.EmptyString))))))))))))))))))))))))
    (@imported_cons imported_String_string
       (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string imported_String_EmptyString
          imported_String_String
          (String.String (Ascii.Ascii true false false false false true true false)
             (String.String (Ascii.Ascii false true false false false true true false) (String.String (Ascii.Ascii true true false false false true true false) String.EmptyString))))
       (@imported_cons imported_String_string
          (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string imported_String_EmptyString
             imported_String_String
             (String.String (Ascii.Ascii true false false false true true false false) (String.String (Ascii.Ascii false true false false true true false false) String.EmptyString)))
          (@imported_cons imported_String_string
             (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string imported_String_EmptyString
                imported_String_String (String.String (Ascii.Ascii true false true true true true false false) String.EmptyString))
             (@imported_cons imported_String_string
                (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string imported_String_EmptyString
                   imported_String_String (String.String (Ascii.Ascii true true false false true true false false) String.EmptyString))
                (@imported_cons imported_String_string
                   (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string imported_String_EmptyString
                      imported_String_String
                      (String.String (Ascii.Ascii false true false false true true false false)
                         (String.String (Ascii.Ascii false true false false true true false false) (String.String (Ascii.Ascii true true false false true true false false) String.EmptyString))))
                   (@imported_cons imported_String_string
                      (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string imported_String_EmptyString
                         imported_String_String (String.String (Ascii.Ascii false true false true false true false false) String.EmptyString))
                      (@imported_cons imported_String_string
                         (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string imported_String_EmptyString
                            imported_String_String (String.String (Ascii.Ascii false false false true false true false false) String.EmptyString))
                         (@imported_cons imported_String_string
                            (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string
                               imported_String_EmptyString imported_String_String (String.String (Ascii.Ascii true true false false true true false false) String.EmptyString))
                            (@imported_cons imported_String_string
                               (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string
                                  imported_String_EmptyString imported_String_String (String.String (Ascii.Ascii true true false true false true false false) String.EmptyString))
                               (@imported_cons imported_String_string
                                  (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string
                                     imported_String_EmptyString imported_String_String (String.String (Ascii.Ascii false false false true false true false false) String.EmptyString))
                                  (@imported_cons imported_String_string
                                     (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string
                                        imported_String_EmptyString imported_String_String (String.String (Ascii.Ascii true false false false false true true false) String.EmptyString))
                                     (@imported_cons imported_String_string
                                        (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string
                                           imported_String_EmptyString imported_String_String (String.String (Ascii.Ascii true true false true false true false false) String.EmptyString))
                                        (@imported_cons imported_String_string
                                           (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string
                                              imported_String_EmptyString imported_String_String (String.String (Ascii.Ascii true true false false false true true false) String.EmptyString))
                                           (@imported_cons imported_String_string
                                              (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string
                                                 imported_String_EmptyString imported_String_String (String.String (Ascii.Ascii true false false true false true false false) String.EmptyString))
                                              (@imported_cons imported_String_string
                                                 (@StringOptimizations.imported_string imported_bool imported_true imported_false imported_Ascii_ascii imported_Ascii_Ascii imported_String_string
                                                    imported_String_EmptyString imported_String_String (String.String (Ascii.Ascii true false false true false true false false) String.EmptyString))
                                                 (imported_nil imported_String_string)))))))))))))))).
Parameter Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__ex1_iso : rel_iso
    (relax_Iso_Ts_Ps
       (Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize_iso
             (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                (String.String (Ascii.Ascii true false false false false true true false)
                   (String.String (Ascii.Ascii false true false false false true true false)
                      (String.String (Ascii.Ascii true true false false false true true false)
                         (String.String (Ascii.Ascii true false false false true true false false)
                            (String.String (Ascii.Ascii false true false false true true false false)
                               (String.String (Ascii.Ascii true false true true true true false false)
                                  (String.String (Ascii.Ascii true true false false true true false false)
                                     (String.String (Ascii.Ascii false false false false false true false false)
                                        (String.String (Ascii.Ascii false false false false false true false false)
                                           (String.String (Ascii.Ascii false true false false true true false false)
                                              (String.String (Ascii.Ascii false true false false true true false false)
                                                 (String.String (Ascii.Ascii true true false false true true false false)
                                                    (String.String (Ascii.Ascii false true false true false true false false)
                                                       (String.String (Ascii.Ascii false false false true false true false false)
                                                          (String.String (Ascii.Ascii true true false false true true false false)
                                                             (String.String (Ascii.Ascii true true false true false true false false)
                                                                (String.String (Ascii.Ascii false false false true false true false false)
                                                                   (String.String (Ascii.Ascii true false false false false true true false)
                                                                      (String.String (Ascii.Ascii true true false true false true false false)
                                                                         (String.String (Ascii.Ascii true true false false false true true false)
                                                                            (String.String (Ascii.Ascii true false false true false true false false)
                                                                               (String.String (Ascii.Ascii true false false true false true false false) String.EmptyString))))))))))))))))))))))))
          (cons_iso
             (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                (String.String (Ascii.Ascii true false false false false true true false)
                   (String.String (Ascii.Ascii false true false false false true true false) (String.String (Ascii.Ascii true true false false false true true false) String.EmptyString))))
             (cons_iso
                (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                   (String.String (Ascii.Ascii true false false false true true false false) (String.String (Ascii.Ascii false true false false true true false false) String.EmptyString)))
                (cons_iso
                   (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                      (String.String (Ascii.Ascii true false true true true true false false) String.EmptyString))
                   (cons_iso
                      (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                         (String.String (Ascii.Ascii true true false false true true false false) String.EmptyString))
                      (cons_iso
                         (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                            (String.String (Ascii.Ascii false true false false true true false false)
                               (String.String (Ascii.Ascii false true false false true true false false) (String.String (Ascii.Ascii true true false false true true false false) String.EmptyString))))
                         (cons_iso
                            (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                               (String.String (Ascii.Ascii false true false true false true false false) String.EmptyString))
                            (cons_iso
                               (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                  (String.String (Ascii.Ascii false false false true false true false false) String.EmptyString))
                               (cons_iso
                                  (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                     (String.String (Ascii.Ascii true true false false true true false false) String.EmptyString))
                                  (cons_iso
                                     (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                        (String.String (Ascii.Ascii true true false true false true false false) String.EmptyString))
                                     (cons_iso
                                        (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                           (String.String (Ascii.Ascii false false false true false true false false) String.EmptyString))
                                        (cons_iso
                                           (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                              (String.String (Ascii.Ascii true false false false false true true false) String.EmptyString))
                                           (cons_iso
                                              (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                                 (String.String (Ascii.Ascii true true false true false true false false) String.EmptyString))
                                              (cons_iso
                                                 (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                                    (String.String (Ascii.Ascii true true false false false true true false) String.EmptyString))
                                                 (cons_iso
                                                    (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                                       (String.String (Ascii.Ascii true false false true false true false false) String.EmptyString))
                                                    (cons_iso
                                                       (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                                                          (String.String (Ascii.Ascii true false false true false true false false) String.EmptyString))
                                                       (nil_iso String_string_iso))))))))))))))))))
    Original.LF_DOT_ImpParser.LF.ImpParser.tokenize_ex1 imported_Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__ex1.
Existing Instance Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__ex1_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ImpParser.LF.ImpParser.tokenize_ex1 ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__ex1_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ImpParser.LF.ImpParser.tokenize_ex1 imported_Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__ex1 ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__ex1_iso; constructor : typeclass_instances.


End Interface.