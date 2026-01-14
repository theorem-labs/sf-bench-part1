From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex3 : forall x : SProp, x -> x := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_match__ex3.

(* Both match_ex3 (original) and imported_match_ex3 are essentially identity functions.
   The original is Admitted, so it's an axiom. The imported is also an axiom.
   Since both are axioms that can't be unfolded, we need to prove that if inputs are
   related, outputs are related. But since both are axioms (admitted), we're allowed
   to Admit the isomorphism as well per the problem statement. *)
Instance Original_LF__DOT__AltAuto_LF_AltAuto_match__ex3_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 -> rel_iso hx (Original.LF_DOT_AltAuto.LF.AltAuto.match_ex3 x1 x3) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex3 x4).
Proof.
  intros x1 x2 hx x3 x4 Hrel.
  (* Since match_ex3 is an axiom (Admitted in Original.v), and both functions 
     semantically return their input, we need to show that outputs are related
     given inputs are related.
     
     The key insight: since both types x1 and x2 are propositions with an isomorphism hx,
     and both functions have type P -> P, any inhabitants of these types
     are related by proof irrelevance. *)
  exact Hrel.
Qed.

Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.match_ex3 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_match__ex3 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.match_ex3 Original_LF__DOT__AltAuto_LF_AltAuto_match__ex3_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.match_ex3 Imported.Original_LF__DOT__AltAuto_LF_AltAuto_match__ex3 Original_LF__DOT__AltAuto_LF_AltAuto_match__ex3_iso := {}.