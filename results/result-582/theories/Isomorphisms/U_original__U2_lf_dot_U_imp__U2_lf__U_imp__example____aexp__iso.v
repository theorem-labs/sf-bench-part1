From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_example__aexp : imported_Original_LF__DOT__Imp_LF_Imp_aexp := Imported.Original_LF__DOT__Imp_LF_Imp_example__aexp.
Instance Original_LF__DOT__Imp_LF_Imp_example__aexp_iso : rel_iso Original_LF__DOT__Imp_LF_Imp_aexp_iso Original.LF_DOT_Imp.LF.Imp.example_aexp imported_Original_LF__DOT__Imp_LF_Imp_example__aexp.
Proof.
  unfold rel_iso. unfold aexp_to_imported.
  unfold imported_Original_LF__DOT__Imp_LF_Imp_example__aexp.
  unfold Original.LF_DOT_Imp.LF.Imp.example_aexp.
  simpl.
  unfold Imported.Original_LF__DOT__Imp_LF_Imp_example__aexp.
  unfold Imported.Original_LF__DOT__Imp_LF_Imp_X.
  unfold Original.LF_DOT_Imp.LF.Imp.X.
  simpl.
  apply IsomorphismDefinitions.eq_refl.
Qed.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.example_aexp := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_example__aexp := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.example_aexp Original_LF__DOT__Imp_LF_Imp_example__aexp_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.example_aexp Imported.Original_LF__DOT__Imp_LF_Imp_example__aexp Original_LF__DOT__Imp_LF_Imp_example__aexp_iso := {}.