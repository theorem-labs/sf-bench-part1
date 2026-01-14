From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

Definition imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit : Type := Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit.

Definition bit_to_imported (b : Original.LF_DOT_Basics.LF.Basics.TuplePlayground.bit) : imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit :=
  match b with
  | Original.LF_DOT_Basics.LF.Basics.TuplePlayground.B1 => Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit_B1
  | Original.LF_DOT_Basics.LF.Basics.TuplePlayground.B0 => Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit_B0
  end.

Definition bit_from_imported (b : imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit) : Original.LF_DOT_Basics.LF.Basics.TuplePlayground.bit :=
  match b with
  | Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit_B1 => Original.LF_DOT_Basics.LF.Basics.TuplePlayground.B1
  | Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit_B0 => Original.LF_DOT_Basics.LF.Basics.TuplePlayground.B0
  end.

Lemma bit_to_from : forall x : imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit,
  IsomorphismDefinitions.eq (bit_to_imported (bit_from_imported x)) x.
Proof.
  intro x. destruct x; apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma bit_from_to : forall x : Original.LF_DOT_Basics.LF.Basics.TuplePlayground.bit,
  IsomorphismDefinitions.eq (bit_from_imported (bit_to_imported x)) x.
Proof.
  intro x. destruct x; apply IsomorphismDefinitions.eq_refl.
Qed.

Instance Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit_iso : Iso Original.LF_DOT_Basics.LF.Basics.TuplePlayground.bit imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit :=
  Build_Iso bit_to_imported bit_from_imported bit_to_from bit_from_to.

Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.TuplePlayground.bit := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.TuplePlayground.bit Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.TuplePlayground.bit Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit_iso := {}.