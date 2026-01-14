From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.and__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_proj1 : forall x x0 : SProp, imported_and x x0 -> x := Imported.Original_LF__DOT__Logic_LF_Logic_proj1.
Instance Original_LF__DOT__Logic_LF_Logic_proj1_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : x1 /\ x3) (x6 : imported_and x2 x4),
  rel_iso
    {|
      to := and_iso hx hx0; from := from (and_iso hx hx0); to_from := fun x : imported_and x2 x4 => to_from (and_iso hx hx0) x; from_to := fun x : x1 /\ x3 => seq_p_of_t (from_to (and_iso hx hx0) x)
    |} x5 x6 ->
  rel_iso hx (Original.LF_DOT_Logic.LF.Logic.proj1 x1 x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_proj1 x6).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 Hrel.
  (* rel_iso hx a b = IsomorphismDefinitions.eq (to hx a) b *)
  (* Both sides are in SProp x2, so any two inhabitants are equal *)
  unfold rel_iso.
  exact IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.proj1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_proj1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.proj1 Original_LF__DOT__Logic_LF_Logic_proj1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.proj1 Imported.Original_LF__DOT__Logic_LF_Logic_proj1 Original_LF__DOT__Logic_LF_Logic_proj1_iso := {}.