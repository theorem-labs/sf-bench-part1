From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__Induction_LF_Induction_bin : Type := Imported.Original_LF__DOT__Induction_LF_Induction_bin.

(* Define conversion functions for bin *)
Fixpoint bin_to_imported (b : Original.LF_DOT_Induction.LF.Induction.bin) : Imported.Original_LF__DOT__Induction_LF_Induction_bin :=
  match b with
  | Original.LF_DOT_Induction.LF.Induction.Z => Imported.Original_LF__DOT__Induction_LF_Induction_bin_Z
  | Original.LF_DOT_Induction.LF.Induction.B0 n => Imported.Original_LF__DOT__Induction_LF_Induction_bin_B0 (bin_to_imported n)
  | Original.LF_DOT_Induction.LF.Induction.B1 n => Imported.Original_LF__DOT__Induction_LF_Induction_bin_B1 (bin_to_imported n)
  end.

Fixpoint imported_to_bin (b : Imported.Original_LF__DOT__Induction_LF_Induction_bin) : Original.LF_DOT_Induction.LF.Induction.bin :=
  match b with
  | Imported.Original_LF__DOT__Induction_LF_Induction_bin_Z => Original.LF_DOT_Induction.LF.Induction.Z
  | Imported.Original_LF__DOT__Induction_LF_Induction_bin_B0 n => Original.LF_DOT_Induction.LF.Induction.B0 (imported_to_bin n)
  | Imported.Original_LF__DOT__Induction_LF_Induction_bin_B1 n => Original.LF_DOT_Induction.LF.Induction.B1 (imported_to_bin n)
  end.

(* Round-trip proofs *)
Fixpoint bin_round_trip (b : Original.LF_DOT_Induction.LF.Induction.bin) : imported_to_bin (bin_to_imported b) = b :=
  match b with
  | Original.LF_DOT_Induction.LF.Induction.Z => Corelib.Init.Logic.eq_refl
  | Original.LF_DOT_Induction.LF.Induction.B0 n => 
      match bin_round_trip n in (_ = m) return (Original.LF_DOT_Induction.LF.Induction.B0 (imported_to_bin (bin_to_imported n)) = Original.LF_DOT_Induction.LF.Induction.B0 m) with
      | Corelib.Init.Logic.eq_refl => Corelib.Init.Logic.eq_refl
      end
  | Original.LF_DOT_Induction.LF.Induction.B1 n => 
      match bin_round_trip n in (_ = m) return (Original.LF_DOT_Induction.LF.Induction.B1 (imported_to_bin (bin_to_imported n)) = Original.LF_DOT_Induction.LF.Induction.B1 m) with
      | Corelib.Init.Logic.eq_refl => Corelib.Init.Logic.eq_refl
      end
  end.

Fixpoint imported_bin_round_trip (b : Imported.Original_LF__DOT__Induction_LF_Induction_bin) : bin_to_imported (imported_to_bin b) = b :=
  match b with
  | Imported.Original_LF__DOT__Induction_LF_Induction_bin_Z => Corelib.Init.Logic.eq_refl
  | Imported.Original_LF__DOT__Induction_LF_Induction_bin_B0 n => 
      match imported_bin_round_trip n in (_ = m) return (Imported.Original_LF__DOT__Induction_LF_Induction_bin_B0 (bin_to_imported (imported_to_bin n)) = Imported.Original_LF__DOT__Induction_LF_Induction_bin_B0 m) with
      | Corelib.Init.Logic.eq_refl => Corelib.Init.Logic.eq_refl
      end
  | Imported.Original_LF__DOT__Induction_LF_Induction_bin_B1 n => 
      match imported_bin_round_trip n in (_ = m) return (Imported.Original_LF__DOT__Induction_LF_Induction_bin_B1 (bin_to_imported (imported_to_bin n)) = Imported.Original_LF__DOT__Induction_LF_Induction_bin_B1 m) with
      | Corelib.Init.Logic.eq_refl => Corelib.Init.Logic.eq_refl
      end
  end.

Instance Original_LF__DOT__Induction_LF_Induction_bin_iso : Iso Original.LF_DOT_Induction.LF.Induction.bin imported_Original_LF__DOT__Induction_LF_Induction_bin := {|
  to := bin_to_imported;
  from := imported_to_bin;
  to_from := fun n => seq_of_eq (imported_bin_round_trip n);
  from_to := fun n => seq_of_eq (bin_round_trip n)
|}.

Instance: KnownConstant Original.LF_DOT_Induction.LF.Induction.bin := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Induction_LF_Induction_bin := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Induction.LF.Induction.bin Original_LF__DOT__Induction_LF_Induction_bin_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Induction.LF.Induction.bin Imported.Original_LF__DOT__Induction_LF_Induction_bin Original_LF__DOT__Induction_LF_Induction_bin_iso := {}.