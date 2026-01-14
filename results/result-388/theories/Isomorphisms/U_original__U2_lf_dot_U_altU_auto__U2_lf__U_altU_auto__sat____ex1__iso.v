From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_sat__ex1 : imported_Corelib_Init_Logic_eq (imported_Nat_add (imported_S imported_0) (imported_S imported_0)) (imported_S (imported_S imported_0)) := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_sat__ex1.

(* The isomorphism for the sat_ex1 theorem *)
(* Since sat_ex1 is admitted in Original.v, we can use the axioms to build this *)
Instance Original_LF__DOT__AltAuto_LF_AltAuto_sat__ex1_iso : rel_iso
    (Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso _0_iso) (S_iso _0_iso)) (S_iso (S_iso _0_iso)))
    Original.LF_DOT_AltAuto.LF.AltAuto.sat_ex1 
    imported_Original_LF__DOT__AltAuto_LF_AltAuto_sat__ex1.
Proof.
  unfold rel_iso, imported_Original_LF__DOT__AltAuto_LF_AltAuto_sat__ex1.
  simpl.
  (* The goal is in SProp, so it's trivially satisfied *)
  exact (IsomorphismDefinitions.eq_refl _).
Defined.
Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.sat_ex1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_sat__ex1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.sat_ex1 Original_LF__DOT__AltAuto_LF_AltAuto_sat__ex1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.sat_ex1 Imported.Original_LF__DOT__AltAuto_LF_AltAuto_sat__ex1 Original_LF__DOT__AltAuto_LF_AltAuto_sat__ex1_iso := {}.