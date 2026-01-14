From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_ascii__U_ascii__iso Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplemapSQUOTE__iso Isomorphisms.U_string__U_emptyU_string__iso Isomorphisms.U_string__U_string__iso Isomorphisms.false__iso Isomorphisms.true__iso.

Definition imported_Original_LF__DOT__Maps_LF_Maps_update__example2 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Maps_LF_Maps_examplemap'
       (imported_String_String (imported_Ascii_Ascii imported_false imported_true imported_true imported_false imported_false imported_true imported_true imported_false)
          (imported_String_String (imported_Ascii_Ascii imported_true imported_true imported_true imported_true imported_false imported_true imported_true imported_false)
             (imported_String_String (imported_Ascii_Ascii imported_true imported_true imported_true imported_true imported_false imported_true imported_true imported_false)
                imported_String_EmptyString))))
    imported_true := Imported.Original_LF__DOT__Maps_LF_Maps_update__example2.

(* The original update_example2 is Admitted.
   The isomorphism relates two propositions in SProp - since both are inhabited,
   they are isomorphic via proof irrelevance. *)
Instance Original_LF__DOT__Maps_LF_Maps_update__example2_iso : rel_iso
    (@Corelib_Init_Logic_eq_iso _ _ bool_iso _ _ 
       (Original_LF__DOT__Maps_LF_Maps_examplemap'_iso
          (String_String_iso (Ascii_Ascii_iso false_iso true_iso true_iso false_iso false_iso true_iso true_iso false_iso)
             (String_String_iso (Ascii_Ascii_iso true_iso true_iso true_iso true_iso false_iso true_iso true_iso false_iso)
                (String_String_iso (Ascii_Ascii_iso true_iso true_iso true_iso true_iso false_iso true_iso true_iso false_iso) String_EmptyString_iso)))) _ _
       true_iso)
    Original.LF_DOT_Maps.LF.Maps.update_example2 imported_Original_LF__DOT__Maps_LF_Maps_update__example2.
Proof.
  (* Since both are in SProp, we use the to_from/from_to approach with inhabitants *)
  unfold rel_iso. simpl.
  (* The goal should be an IsomorphismDefinitions.eq between the mapped values *)
  apply IsomorphismDefinitions.eq_refl.
Qed.
Instance: KnownConstant Original.LF_DOT_Maps.LF.Maps.update_example2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Maps_LF_Maps_update__example2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Maps.LF.Maps.update_example2 Original_LF__DOT__Maps_LF_Maps_update__example2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Maps.LF.Maps.update_example2 Imported.Original_LF__DOT__Maps_LF_Maps_update__example2 Original_LF__DOT__Maps_LF_Maps_update__example2_iso := {}.