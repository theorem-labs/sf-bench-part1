From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

From Stdlib Require Import ProofIrrelevance.

From IsomorphismChecker Require Export Isomorphisms.iff__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_iff__sym : forall x x0 : SProp, imported_iff x x0 -> imported_iff x0 x := Imported.Original_LF__DOT__Logic_LF_Logic_iff__sym.

Instance Original_LF__DOT__Logic_LF_Logic_iff__sym_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : x1 <-> x3) (x6 : imported_iff x2 x4),
  rel_iso
    {|
      to := iff_iso hx hx0; from := from (iff_iso hx hx0); to_from := fun x : imported_iff x2 x4 => to_from (iff_iso hx hx0) x; from_to := fun x : x1 <-> x3 => seq_p_of_t (from_to (iff_iso hx hx0) x)
    |} x5 x6 ->
  rel_iso
    {|
      to := iff_iso hx0 hx; from := from (iff_iso hx0 hx); to_from := fun x : imported_iff x4 x2 => to_from (iff_iso hx0 hx) x; from_to := fun x : x3 <-> x1 => seq_p_of_t (from_to (iff_iso hx0 hx) x)
    |} (Original.LF_DOT_Logic.LF.Logic.iff_sym x1 x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_iff__sym x6).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 Hrel.
  (* Both sides are in SProp, so rel_iso holds trivially *)
  (* The goal is in SProp, so we just need to construct any term of the right type *)
  (* rel_iso for SProp types is trivial since all SProp values are equal *)
  unfold rel_iso.
  (* The result type is (imported_iff x4 x2) which is an SProp *)
  (* rel_iso is defined over IsomorphismDefinitions.eq which is in SProp *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.iff_sym := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_iff__sym := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.iff_sym Original_LF__DOT__Logic_LF_Logic_iff__sym_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.iff_sym Imported.Original_LF__DOT__Logic_LF_Logic_iff__sym Original_LF__DOT__Logic_LF_Logic_iff__sym_iso := {}.