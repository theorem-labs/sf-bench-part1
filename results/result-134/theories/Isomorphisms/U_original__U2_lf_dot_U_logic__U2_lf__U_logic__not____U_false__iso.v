From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_logic__not__iso Isomorphisms.U_original__U_false__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_not__False : imported_Original_False -> imported_False := Imported.Original_LF__DOT__Logic_LF_Logic_not__False.
Instance Original_LF__DOT__Logic_LF_Logic_not__False_iso : forall (x1 : Original.False) (x2 : imported_Original_False),
  rel_iso
    {|
      to := Original_False_iso;
      from := from Original_False_iso;
      to_from := fun x : imported_Original_False => to_from Original_False_iso x;
      from_to := fun x : Original.False => seq_p_of_t (from_to Original_False_iso x)
    |} x1 x2 ->
  rel_iso {| to := False_iso; from := from False_iso; to_from := fun x : imported_False => to_from False_iso x; from_to := fun x : False => seq_p_of_t (from_to False_iso x) |}
    (Original.LF_DOT_Logic.LF.Logic.not_False x1) (imported_Original_LF__DOT__Logic_LF_Logic_not__False x2).
Proof.
  intros x1 x2 Hrel.
  (* x1 is of type Original.False which is an empty type *)
  destruct x1.
Qed.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.not_False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_not__False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.not_False Original_LF__DOT__Logic_LF_Logic_not__False_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.not_False Imported.Original_LF__DOT__Logic_LF_Logic_not__False Original_LF__DOT__Logic_LF_Logic_not__False_iso := {}.