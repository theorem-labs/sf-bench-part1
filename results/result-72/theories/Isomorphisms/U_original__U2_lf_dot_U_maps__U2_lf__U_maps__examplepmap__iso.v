From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_string__string__iso Isomorphisms.bool__iso Isomorphisms.option__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update__iso Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__empty__iso.

Monomorphic Definition imported_Original_LF__DOT__Maps_LF_Maps_examplepmap : imported_String_string -> imported_option imported_bool := Imported.Original_LF__DOT__Maps_LF_Maps_examplepmap.

(* Define the string constants *)
Definition Church_str : String.string :=
  String.String (Ascii.Ascii true true false false false false true false)
     (String.String (Ascii.Ascii false false false true false true true false)
        (String.String (Ascii.Ascii true false true false true true true false)
           (String.String (Ascii.Ascii false true false false true true true false)
              (String.String (Ascii.Ascii true true false false false true true false)
                 (String.String (Ascii.Ascii false false false true false true true false)
                    String.EmptyString))))).

Definition Turing_str : String.string :=
  String.String (Ascii.Ascii false false true false true false true false)
     (String.String (Ascii.Ascii true false true false true true true false)
        (String.String (Ascii.Ascii false true false false true true true false)
           (String.String (Ascii.Ascii true false false true false true true false)
              (String.String (Ascii.Ascii false true true true false true true false)
                 (String.String (Ascii.Ascii true true true false false true true false)
                    String.EmptyString))))).

Lemma Church_str_iso : rel_iso String_string_iso Church_str Imported.string_Church.
Proof. constructor. apply IsomorphismDefinitions.eq_refl. Qed.

Lemma Turing_str_iso : rel_iso String_string_iso Turing_str Imported.string_Turing.
Proof. constructor. apply IsomorphismDefinitions.eq_refl. Qed.

Lemma bool_false_iso : rel_iso bool_iso false Imported.mybool_myfalse.
Proof. constructor. apply IsomorphismDefinitions.eq_refl. Qed.

Lemma bool_true_iso : rel_iso bool_iso true Imported.mybool_mytrue.
Proof. constructor. apply IsomorphismDefinitions.eq_refl. Qed.

(* Helper lemma for the inner update *)
Lemma inner_pmap_iso : forall x5 x6, rel_iso String_string_iso x5 x6 ->
  rel_iso (option_iso bool_iso)
    (Original.LF_DOT_Maps.LF.Maps.update Original.LF_DOT_Maps.LF.Maps.empty Turing_str false x5)
    (Imported.Original_LF__DOT__Maps_LF_Maps_update Imported.mybool
       (Imported.Original_LF__DOT__Maps_LF_Maps_empty Imported.mybool)
       Imported.string_Turing Imported.mybool_myfalse x6).
Proof.
  intros x5 x6 Hx.
  apply (Original_LF__DOT__Maps_LF_Maps_update_iso 
    Original.LF_DOT_Maps.LF.Maps.empty
    (Imported.Original_LF__DOT__Maps_LF_Maps_empty Imported.mybool)).
  - intros x7 x8 Hx7. apply Original_LF__DOT__Maps_LF_Maps_empty_iso. exact Hx7.
  - exact Turing_str_iso.
  - apply bool_false_iso.
  - exact Hx.
Qed.

Monomorphic Instance Original_LF__DOT__Maps_LF_Maps_examplepmap_iso : forall (x1 : String.string) (x2 : imported_String_string),
  rel_iso String_string_iso x1 x2 -> rel_iso (option_iso bool_iso) (Original.LF_DOT_Maps.LF.Maps.examplepmap x1) (imported_Original_LF__DOT__Maps_LF_Maps_examplepmap x2).
Proof.
  intros x1 x2 Hx.
  unfold Original.LF_DOT_Maps.LF.Maps.examplepmap, imported_Original_LF__DOT__Maps_LF_Maps_examplepmap.
  unfold Imported.Original_LF__DOT__Maps_LF_Maps_examplepmap.
  
  change (String.String (Ascii.Ascii false false true false true false true false)
     (String.String (Ascii.Ascii true false true false true true true false)
        (String.String (Ascii.Ascii false true false false true true true false)
           (String.String (Ascii.Ascii true false false true false true true false)
              (String.String (Ascii.Ascii false true true true false true true false)
                 (String.String (Ascii.Ascii true true true false false true true false)
                    String.EmptyString))))))
  with Turing_str.
  change (String.String (Ascii.Ascii true true false false false false true false)
     (String.String (Ascii.Ascii false false false true false true true false)
        (String.String (Ascii.Ascii true false true false true true true false)
           (String.String (Ascii.Ascii false true false false true true true false)
              (String.String (Ascii.Ascii true true false false false true true false)
                 (String.String (Ascii.Ascii false false false true false true true false)
                    String.EmptyString))))))
  with Church_str.
  
  apply (Original_LF__DOT__Maps_LF_Maps_update_iso
    (Original.LF_DOT_Maps.LF.Maps.update Original.LF_DOT_Maps.LF.Maps.empty Turing_str false)
    (Imported.Original_LF__DOT__Maps_LF_Maps_update Imported.mybool
       (Imported.Original_LF__DOT__Maps_LF_Maps_empty Imported.mybool)
       Imported.string_Turing Imported.mybool_myfalse)).
  - exact inner_pmap_iso.
  - exact Church_str_iso.
  - apply bool_true_iso.
  - exact Hx.
Defined.
Instance: KnownConstant Original.LF_DOT_Maps.LF.Maps.examplepmap := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Maps_LF_Maps_examplepmap := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Maps.LF.Maps.examplepmap Original_LF__DOT__Maps_LF_Maps_examplepmap_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Maps.LF.Maps.examplepmap Imported.Original_LF__DOT__Maps_LF_Maps_examplepmap Original_LF__DOT__Maps_LF_Maps_examplepmap_iso := {}.