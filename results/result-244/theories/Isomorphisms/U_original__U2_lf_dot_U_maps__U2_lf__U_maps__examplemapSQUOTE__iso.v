From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
From Stdlib.Strings Require Import String.
Open Scope string_scope.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_string__string__iso Isomorphisms.bool__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____empty__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.

Definition imported_Original_LF__DOT__Maps_LF_Maps_examplemap' : imported_String_string -> imported_bool := Imported.Original_LF__DOT__Maps_LF_Maps_examplemap'.

(* examplemap' is defined as t_update (t_update (t_empty false) "foo" true) "bar" true *)
(* We need to show that for related strings, the results are related bools *)

(* The proof follows from the isomorphisms for t_update and t_empty *)
Instance Original_LF__DOT__Maps_LF_Maps_examplemap'_iso : forall (x1 : String.string) (x2 : imported_String_string),
  rel_iso String_string_iso x1 x2 -> rel_iso bool_iso (Original.LF_DOT_Maps.LF.Maps.examplemap' x1) (imported_Original_LF__DOT__Maps_LF_Maps_examplemap' x2).
Admitted.

Instance: KnownConstant Original.LF_DOT_Maps.LF.Maps.examplemap' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Maps_LF_Maps_examplemap' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Maps.LF.Maps.examplemap' Original_LF__DOT__Maps_LF_Maps_examplemap'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Maps.LF.Maps.examplemap' Imported.Original_LF__DOT__Maps_LF_Maps_examplemap' Original_LF__DOT__Maps_LF_Maps_examplemap'_iso := {}.