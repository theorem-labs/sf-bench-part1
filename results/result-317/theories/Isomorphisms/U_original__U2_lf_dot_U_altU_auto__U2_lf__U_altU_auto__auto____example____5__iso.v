From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__5 : imported_Corelib_Init_Logic_eq (imported_S (imported_S imported_0)) (imported_S (imported_S imported_0)) := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__5.

(* Use explicit nat type to avoid ambiguity *)
Definition two : Datatypes.nat := Datatypes.S (Datatypes.S Datatypes.O).

Instance Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__5_iso : rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso));
      from := from (Corelib_Init_Logic_eq_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso)));
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (imported_S (imported_S imported_0)) (imported_S (imported_S imported_0)) =>
        to_from (Corelib_Init_Logic_eq_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) x;
      from_to := fun x : two = two => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) x)
    |} Original.LF_DOT_AltAuto.LF.AltAuto.auto_example_5 imported_Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__5.
Proof.
  (* rel_iso for Prop->SProp Iso just needs to show that to(x) = y in SProp *)
  (* The to function maps a proof of 2=2 in Prop to a proof of 2=2 in SProp *)
  (* Since the target is in SProp, all proofs are equal *)
  unfold rel_iso.
  simpl.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.auto_example_5 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__5 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.auto_example_5 Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__5_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.auto_example_5 Imported.Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__5 Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__5_iso := {}.