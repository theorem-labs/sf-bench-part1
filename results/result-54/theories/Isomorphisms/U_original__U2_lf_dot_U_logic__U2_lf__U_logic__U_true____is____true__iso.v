From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_True__is__true : imported_True := Imported.Original_LF__DOT__Logic_LF_Logic_True__is__true.
Instance Original_LF__DOT__Logic_LF_Logic_True__is__true_iso : rel_iso {| to := True_iso; from := from True_iso; to_from := fun x : imported_True => to_from True_iso x; from_to := fun x : True => seq_p_of_t (from_to True_iso x) |}
    Original.LF_DOT_Logic.LF.Logic.True_is_true imported_Original_LF__DOT__Logic_LF_Logic_True__is__true.
Proof.
  unfold rel_iso. simpl.
  apply IsomorphismDefinitions.eq_refl.
Qed.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.True_is_true := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_True__is__true := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.True_is_true Original_LF__DOT__Logic_LF_Logic_True__is__true_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.True_is_true Imported.Original_LF__DOT__Logic_LF_Logic_True__is__true Original_LF__DOT__Logic_LF_Logic_True__is__true_iso := {}.