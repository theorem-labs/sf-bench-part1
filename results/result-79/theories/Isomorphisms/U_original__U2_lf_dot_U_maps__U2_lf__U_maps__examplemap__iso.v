From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_string__string__iso Isomorphisms.bool__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____empty__iso.

Monomorphic Definition imported_Original_LF__DOT__Maps_LF_Maps_examplemap : imported_String_string -> imported_bool := Imported.Original_LF__DOT__Maps_LF_Maps_examplemap.

(* Define the string constants - "foo" and "bar" *)
Definition foo_str : String.string := 
  String.String (Ascii.Ascii false true true false false true true false)
    (String.String (Ascii.Ascii true true true true false true true false)
      (String.String (Ascii.Ascii true true true true false true true false) String.EmptyString)).

Definition bar_str : String.string :=
  String.String (Ascii.Ascii false true false false false true true false)
    (String.String (Ascii.Ascii true false false false false true true false)
      (String.String (Ascii.Ascii false true false false true true true false) String.EmptyString)).

Lemma foo_str_iso : rel_iso String_string_iso foo_str Imported.string_foo.
Proof. constructor. apply IsomorphismDefinitions.eq_refl. Qed.

Lemma bar_str_iso : rel_iso String_string_iso bar_str Imported.string_bar.
Proof. constructor. apply IsomorphismDefinitions.eq_refl. Qed.

Lemma bool_false_iso : rel_iso bool_iso false Imported.mybool_myfalse.
Proof. constructor. apply IsomorphismDefinitions.eq_refl. Qed.

Lemma bool_true_iso : rel_iso bool_iso true Imported.mybool_mytrue.
Proof. constructor. apply IsomorphismDefinitions.eq_refl. Qed.

(* Helper lemma for the empty map - using rel_iso_sort *)
Lemma empty_map_iso_sort : forall x5 x6, rel_iso String_string_iso x5 x6 ->
  @rel_iso_sort false _ _ bool_iso (Original.LF_DOT_Maps.LF.Maps.t_empty false x5)
    (Imported.Original_LF__DOT__Maps_LF_Maps_t__empty Imported.mybool Imported.mybool_myfalse x6).
Proof.
  intros x5 x6 Hx.
  constructor.
  apply Original_LF__DOT__Maps_LF_Maps_t__empty_iso.
  - apply bool_false_iso.
  - exact Hx.
Qed.

(* Helper lemma for the inner update - using rel_iso_sort *)
Lemma inner_map_iso_sort : forall x5 x6, rel_iso String_string_iso x5 x6 ->
  @rel_iso_sort false _ _ bool_iso
    (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_empty false) foo_str true x5)
    (Imported.Original_LF__DOT__Maps_LF_Maps_t__update Imported.mybool
       (Imported.Original_LF__DOT__Maps_LF_Maps_t__empty Imported.mybool Imported.mybool_myfalse)
       Imported.string_foo Imported.mybool_mytrue x6).
Proof.
  intros x5 x6 Hx.
  apply (Original_LF__DOT__Maps_LF_Maps_t__update_iso bool_iso 
    (Original.LF_DOT_Maps.LF.Maps.t_empty false)
    (Imported.Original_LF__DOT__Maps_LF_Maps_t__empty Imported.mybool Imported.mybool_myfalse)).
  - intros x7 x8 Hx7. apply empty_map_iso_sort. exact Hx7.
  - exact foo_str_iso.
  - constructor. apply bool_true_iso.
  - exact Hx.
Qed.

Monomorphic Instance Original_LF__DOT__Maps_LF_Maps_examplemap_iso : forall (x1 : String.string) (x2 : imported_String_string),
  rel_iso String_string_iso x1 x2 -> rel_iso bool_iso (Original.LF_DOT_Maps.LF.Maps.examplemap x1) (imported_Original_LF__DOT__Maps_LF_Maps_examplemap x2).
Proof.
  intros x1 x2 Hx.
  unfold Original.LF_DOT_Maps.LF.Maps.examplemap, imported_Original_LF__DOT__Maps_LF_Maps_examplemap.
  unfold Imported.Original_LF__DOT__Maps_LF_Maps_examplemap.
  
  change (String.String (Ascii.Ascii false true true false false true true false)
     (String.String (Ascii.Ascii true true true true false true true false)
        (String.String (Ascii.Ascii true true true true false true true false) String.EmptyString)))
  with foo_str.
  change (String.String (Ascii.Ascii false true false false false true true false)
     (String.String (Ascii.Ascii true false false false false true true false)
        (String.String (Ascii.Ascii false true false false true true true false) String.EmptyString)))
  with bar_str.
  
  apply unwrap_sprop.
  apply (Original_LF__DOT__Maps_LF_Maps_t__update_iso bool_iso
    (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_empty false) foo_str true)
    (Imported.Original_LF__DOT__Maps_LF_Maps_t__update Imported.mybool
       (Imported.Original_LF__DOT__Maps_LF_Maps_t__empty Imported.mybool Imported.mybool_myfalse)
       Imported.string_foo Imported.mybool_mytrue)).
  - exact inner_map_iso_sort.
  - exact bar_str_iso.
  - constructor. apply bool_true_iso.
  - exact Hx.
Defined.
Instance: KnownConstant Original.LF_DOT_Maps.LF.Maps.examplemap := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Maps_LF_Maps_examplemap := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Maps.LF.Maps.examplemap Original_LF__DOT__Maps_LF_Maps_examplemap_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Maps.LF.Maps.examplemap Imported.Original_LF__DOT__Maps_LF_Maps_examplemap Original_LF__DOT__Maps_LF_Maps_examplemap_iso := {}.