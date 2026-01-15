From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_tupleU_playground__bit__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble : Type := Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble.

Definition bit_to_imported (b : Original.LF_DOT_Basics.LF.Basics.TuplePlayground.bit) : Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit :=
  match b with
  | Original.LF_DOT_Basics.LF.Basics.TuplePlayground.B0 => Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit_B0
  | Original.LF_DOT_Basics.LF.Basics.TuplePlayground.B1 => Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit_B1
  end.

Definition imported_to_bit (b : Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit) : Original.LF_DOT_Basics.LF.Basics.TuplePlayground.bit :=
  match b with
  | Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit_B0 => Original.LF_DOT_Basics.LF.Basics.TuplePlayground.B0
  | Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit_B1 => Original.LF_DOT_Basics.LF.Basics.TuplePlayground.B1
  end.

Instance Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble_iso : Iso Original.LF_DOT_Basics.LF.Basics.TuplePlayground.nybble imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble.
Proof.
  apply Build_Iso with
    (to := fun n => match n with
                   | Original.LF_DOT_Basics.LF.Basics.TuplePlayground.bits b0 b1 b2 b3 => 
                     Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble_bits
                       (bit_to_imported b0) (bit_to_imported b1) (bit_to_imported b2) (bit_to_imported b3)
                   end)
    (from := fun n => Original.LF_DOT_Basics.LF.Basics.TuplePlayground.bits 
                     (imported_to_bit (Imported.a____at___Solution__hyg1057 n)) 
                     (imported_to_bit (Imported.a____at___Solution__hyg1059 n))
                     (imported_to_bit (Imported.a____at___Solution__hyg1061 n)) 
                     (imported_to_bit (Imported.a____at___Solution__hyg1063 n))).
  - intros x; destruct x; destruct a____at___Solution__hyg1057, a____at___Solution__hyg1059, a____at___Solution__hyg1061, a____at___Solution__hyg1063; apply IsomorphismDefinitions.eq_refl.
  - intros x; destruct x as [b0 b1 b2 b3]; destruct b0, b1, b2, b3; apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.TuplePlayground.nybble := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.TuplePlayground.nybble Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.TuplePlayground.nybble Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble_iso := {}.