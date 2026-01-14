From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U_false__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_false__assumed : imported_Original_False -> imported_Corelib_Init_Logic_eq imported_0 (imported_S imported_0) := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_false__assumed.
Instance Original_LF__DOT__AltAuto_LF_AltAuto_false__assumed_iso : forall (x1 : Original.False) (x2 : imported_Original_False),
  rel_iso
    {|
      to := Original_False_iso;
      from := from Original_False_iso;
      to_from := fun x : imported_Original_False => to_from Original_False_iso x;
      from_to := fun x : Original.False => seq_p_of_t (from_to Original_False_iso x)
    |} x1 x2 ->
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso _0_iso (S_iso _0_iso);
      from := from (Corelib_Init_Logic_eq_iso _0_iso (S_iso _0_iso));
      to_from := fun x : imported_Corelib_Init_Logic_eq imported_0 (imported_S imported_0) => to_from (Corelib_Init_Logic_eq_iso _0_iso (S_iso _0_iso)) x;
      from_to := fun x : (0%nat = 1%nat) => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso _0_iso (S_iso _0_iso)) x)
    |} (Original.LF_DOT_AltAuto.LF.AltAuto.false_assumed x1) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_false__assumed x2).
Proof.
  (* This is an axiom isomorphism - both sides are axioms *)
  intros x1 x2 Hx.
  (* Both Original.LF_DOT_AltAuto.LF.AltAuto.false_assumed and imported_Original_LF__DOT__AltAuto_LF_AltAuto_false__assumed are axioms,
     and we're showing an isomorphism between their results. Since both return 
     proof-irrelevant equality statements (one in Prop, one in SProp), we can 
     use the allowed axiom approach. *)
  destruct x1. (* Original.False has no constructors, so this closes the goal *)
Defined.
Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.false_assumed := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_false__assumed := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.false_assumed Original_LF__DOT__AltAuto_LF_AltAuto_false__assumed_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.false_assumed Imported.Original_LF__DOT__AltAuto_LF_AltAuto_false__assumed Original_LF__DOT__AltAuto_LF_AltAuto_false__assumed_iso := {}.