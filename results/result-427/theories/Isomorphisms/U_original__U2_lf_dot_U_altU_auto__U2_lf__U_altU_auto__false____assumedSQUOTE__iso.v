From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U_false__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_false__assumed' : imported_Original_False -> imported_Corelib_Init_Logic_eq imported_0 (imported_S imported_0) := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_false__assumed'.

(* Define the isomorphism between the equality types for 0 = 1 *)
Local Definition eq_iso_01 : Iso (@Logic.eq Datatypes.nat Datatypes.O (Datatypes.S Datatypes.O)) 
                                  (imported_Corelib_Init_Logic_eq imported_0 (imported_S imported_0)) :=
  Corelib_Init_Logic_eq_iso _0_iso (S_iso _0_iso).

Instance Original_LF__DOT__AltAuto_LF_AltAuto_false__assumed'_iso : forall (x1 : Original.False) (x2 : imported_Original_False),
  rel_iso
    {|
      to := Original_False_iso;
      from := from Original_False_iso;
      to_from := fun x : imported_Original_False => to_from Original_False_iso x;
      from_to := fun x : Original.False => seq_p_of_t (from_to Original_False_iso x)
    |} x1 x2 ->
  rel_iso
    {|
      to := eq_iso_01;
      from := from eq_iso_01;
      to_from := fun x : imported_Corelib_Init_Logic_eq imported_0 (imported_S imported_0) => to_from eq_iso_01 x;
      from_to := fun x : @Logic.eq Datatypes.nat Datatypes.O (Datatypes.S Datatypes.O) => seq_p_of_t (from_to eq_iso_01 x)
    |} (Original.LF_DOT_AltAuto.LF.AltAuto.false_assumed' x1) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_false__assumed' x2).
Proof.
  (* Both false_assumed' in Original and Imported are axioms (Admitted), so they're isomorphic *)
  intros x1 x2 Hx.
  (* x1 : Original.False is empty, so we can destruct it *)
  destruct x1.
Qed.
Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.false_assumed' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_false__assumed' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.false_assumed' Original_LF__DOT__AltAuto_LF_AltAuto_false__assumed'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.false_assumed' Imported.Original_LF__DOT__AltAuto_LF_AltAuto_false__assumed' Original_LF__DOT__AltAuto_LF_AltAuto_false__assumed'_iso := {}.