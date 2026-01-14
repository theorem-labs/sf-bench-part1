From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex4 : forall x x0 : SProp, x -> x0 -> x := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_match__ex4.

(* This is an axiom isomorphism - match_ex4 is an axiom in Original.v *)
Instance Original_LF__DOT__AltAuto_LF_AltAuto_match__ex4_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : x1) (x6 : x2),
  rel_iso hx x5 x6 ->
  forall (x7 : x3) (x8 : x4), rel_iso hx0 x7 x8 -> rel_iso hx (Original.LF_DOT_AltAuto.LF.AltAuto.match_ex4 x1 x3 x5 x7) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex4 x6 x8).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 Hx56 x7 x8 Hx78.
  unfold imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex4.
  unfold rel_iso in *.
  (* Both sides compute to the first argument *)
  (* hx.(to) x5 = x6 from Hx56 *)
  (* We need: hx.(to) (match_ex4 x1 x3 x5 x7) = Original_LF__DOT__AltAuto... x6 x8 *)
  (* Since match_ex4 returns its first argument (x5) and Imported version returns first argument (x6) *)
  (* We need: hx.(to) x5 = x6, which is exactly Hx56 *)
  exact Hx56.
Qed.

Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.match_ex4 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_match__ex4 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.match_ex4 Original_LF__DOT__AltAuto_LF_AltAuto_match__ex4_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.match_ex4 Imported.Original_LF__DOT__AltAuto_LF_AltAuto_match__ex4 Original_LF__DOT__AltAuto_LF_AltAuto_match__ex4_iso := {}.