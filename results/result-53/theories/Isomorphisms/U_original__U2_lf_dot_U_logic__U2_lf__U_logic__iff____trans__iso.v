From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.iff__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_iff__trans : forall x x0 x1 : SProp, imported_iff x x0 -> imported_iff x0 x1 -> imported_iff x x1 := Imported.Original_LF__DOT__Logic_LF_Logic_iff__trans.

(* Since both iff_trans (Original and Imported) are axioms and the result type is in SProp,
   the isomorphism holds trivially. Both sides produce SProp values and SProp has
   proof irrelevance built in. *)
Instance Original_LF__DOT__Logic_LF_Logic_iff__trans_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : Prop) (x6 : SProp) (hx1 : Iso x5 x6) (x7 : x1 <-> x3) (x8 : imported_iff x2 x4),
  rel_iso
    {|
      to := iff_iso hx hx0; from := from (iff_iso hx hx0); to_from := fun x : imported_iff x2 x4 => to_from (iff_iso hx hx0) x; from_to := fun x : x1 <-> x3 => seq_p_of_t (from_to (iff_iso hx hx0) x)
    |} x7 x8 ->
  forall (x9 : x3 <-> x5) (x10 : imported_iff x4 x6),
  rel_iso
    {|
      to := iff_iso hx0 hx1;
      from := from (iff_iso hx0 hx1);
      to_from := fun x : imported_iff x4 x6 => to_from (iff_iso hx0 hx1) x;
      from_to := fun x : x3 <-> x5 => seq_p_of_t (from_to (iff_iso hx0 hx1) x)
    |} x9 x10 ->
  rel_iso
    {|
      to := iff_iso hx hx1; from := from (iff_iso hx hx1); to_from := fun x : imported_iff x2 x6 => to_from (iff_iso hx hx1) x; from_to := fun x : x1 <-> x5 => seq_p_of_t (from_to (iff_iso hx hx1) x)
    |} (Original.LF_DOT_Logic.LF.Logic.iff_trans x1 x3 x5 x7 x9) (imported_Original_LF__DOT__Logic_LF_Logic_iff__trans x8 x10).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 hx1 x7 x8 H78 x9 x10 H910.
  unfold rel_iso. simpl.
  (* The goal is to show:
     to (iff_iso hx hx1) (iff_trans x1 x3 x5 x7 x9) = imported_Original_LF__DOT__Logic_LF_Logic_iff__trans x8 x10
     Both sides are in SProp (imported_iff x2 x6), so they are equal by SProp proof irrelevance *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.iff_trans := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_iff__trans := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.iff_trans Original_LF__DOT__Logic_LF_Logic_iff__trans_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.iff_trans Imported.Original_LF__DOT__Logic_LF_Logic_iff__trans Original_LF__DOT__Logic_LF_Logic_iff__trans_iso := {}.