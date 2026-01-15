From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_s__iso.

(* Helper: show rel_iso between 42 and Imported.nat42 *)
Lemma nat42_iso_v2 : rel_iso nat_iso 42%nat Imported.nat42.
Proof.
  constructor. simpl.
  native_compute. apply IsomorphismDefinitions.eq_refl.
Defined.

Monomorphic Definition imported_Original_LF__DOT__Auto_LF_Auto_is__fortytwo : imported_nat -> SProp := Imported.Original_LF__DOT__Auto_LF_Auto_is__fortytwo.

Monomorphic Instance Original_LF__DOT__Auto_LF_Auto_is__fortytwo_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> Iso (Original.LF_DOT_Auto.LF.Auto.is_fortytwo x1) (imported_Original_LF__DOT__Auto_LF_Auto_is__fortytwo x2).
Proof.
  intros x1 x2 Hx.
  unfold Original.LF_DOT_Auto.LF.Auto.is_fortytwo.
  unfold imported_Original_LF__DOT__Auto_LF_Auto_is__fortytwo.
  change (Imported.Corelib_Init_Logic_eq Imported.nat x2 Imported.nat42) with (imported_Corelib_Init_Logic_eq x2 Imported.nat42).
  exact (@Corelib_Init_Logic_eq_iso nat imported_nat nat_iso x1 x2 Hx 42%nat Imported.nat42 nat42_iso_v2).
Defined.
Instance: KnownConstant Original.LF_DOT_Auto.LF.Auto.is_fortytwo := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Auto_LF_Auto_is__fortytwo := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Auto.LF.Auto.is_fortytwo Original_LF__DOT__Auto_LF_Auto_is__fortytwo_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Auto.LF.Auto.is_fortytwo Imported.Original_LF__DOT__Auto_LF_Auto_is__fortytwo Original_LF__DOT__Auto_LF_Auto_is__fortytwo_iso := {}.