From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib Require Import String List.
Import ListNotations.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

(* Required exports *)
From IsomorphismChecker Require Export Isomorphisms.list__iso Isomorphisms.U_string__string__iso Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.cons__iso Isomorphisms.nil__iso Isomorphisms.U_ascii__U_ascii__iso Isomorphisms.U_string__U_string__iso Isomorphisms.U_string__U_emptyU_string__iso Isomorphisms.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__tokenize__iso Isomorphisms.U_ascii__ascii__iso Isomorphisms.bool__iso Isomorphisms.true__iso Isomorphisms.false__iso.

(* tokenize_ex1 is Admitted in Original.v *)
(* The Lean-exported definition has a type that's not definitionally equal to what
   the Interface expects (explicit constructors vs StringOptimizations.imported_string).
   This checker will fail due to this type mismatch. *)

Definition imported_Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__ex1 :=
  Imported.Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__ex1.

(* This Definition will fail to type-check because the Iso type expects the imported
   term to have a different type than what it actually has. We use Admitted anyway. *)
Definition Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__ex1_iso :
  rel_iso
    (relax_Iso_Ts_Ps
       (Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize_iso
             (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso
                "abc12=3  223*(3+(a+c))"))
          (cons_iso
             (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso "abc")
             (cons_iso
                (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso "12")
                (cons_iso
                   (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso "=")
                   (cons_iso
                      (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso "3")
                      (cons_iso
                         (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso "223")
                         (cons_iso
                            (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso "*")
                            (cons_iso
                               (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso "(")
                               (cons_iso
                                  (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso "3")
                                  (cons_iso
                                     (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso "+")
                                     (cons_iso
                                        (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso "(")
                                        (cons_iso
                                           (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso "a")
                                           (cons_iso
                                              (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso "+")
                                              (cons_iso
                                                 (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso "c")
                                                 (cons_iso
                                                    (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso ")")
                                                    (cons_iso
                                                       (StringOptimizations.imported_string_iso true_iso false_iso Ascii_Ascii_iso String_EmptyString_iso String_String_iso ")")
                                                       (nil_iso String_string_iso))))))))))))))))))
    Original.LF_DOT_ImpParser.LF.ImpParser.tokenize_ex1
    imported_Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__ex1.
Admitted.

Instance: KnownConstant Original.LF_DOT_ImpParser.LF.ImpParser.tokenize_ex1 := {}.
Instance: KnownConstant (@imported_Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__ex1) := {}.
Instance: IsoStatementProofFor Original.LF_DOT_ImpParser.LF.ImpParser.tokenize_ex1 Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__ex1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ImpParser.LF.ImpParser.tokenize_ex1 imported_Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__ex1 Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__ex1_iso := {}.
