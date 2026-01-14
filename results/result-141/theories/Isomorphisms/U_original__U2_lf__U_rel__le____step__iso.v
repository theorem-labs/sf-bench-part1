From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_s__iso Isomorphisms.le__iso Isomorphisms.lt__iso.

Definition imported_Original_LF_Rel_le__step : forall x x0 x1 : imported_nat, imported_lt x x0 -> imported_le x0 (imported_S x1) -> imported_le x x1 := Imported.Original_LF_Rel_le__step.

(* Both Original.LF.Rel.le_step and Imported.Original_LF_Rel_le__step are axioms,
   so we need to use the allowed axiom approach. The isomorphism between their 
   applications follows from the isomorphisms of their argument types. *)

Instance Original_LF_Rel_le__step_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : Peano.lt x1 x3) (x8 : imported_lt x2 x4),
  rel_iso (lt_iso hx hx0) x7 x8 ->
  forall (x9 : Peano.le x3 (S x5)) (x10 : imported_le x4 (imported_S x6)),
  rel_iso (le_iso hx0 (S_iso hx1)) x9 x10 -> rel_iso (le_iso hx hx1) (Original.LF.Rel.le_step x1 x3 x5 x7 x9) (imported_Original_LF_Rel_le__step x8 x10).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 hx1 x7 x8 Hlt x9 x10 Hle.
  (* Both sides are proofs in SProp. The rel_iso for Prop/SProp is proof-irrelevant. *)
  (* rel_iso (le_iso hx hx1) p1 p2 means eq (to (le_iso hx hx1) p1) p2 *)
  (* Since imported_le is SProp, all inhabitants are equal *)
  unfold rel_iso. simpl.
  (* Goal: eq (to (le_iso hx hx1) (Original.LF.Rel.le_step ...)) (imported_Original_LF_Rel_le__step ...) *)
  (* Both are in SProp (imported_le x2 x6), so they are equal by SProp proof irrelevance *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF.Rel.le_step := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF_Rel_le__step := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF.Rel.le_step Original_LF_Rel_le__step_iso := {}.
Instance: IsoStatementProofBetween Original.LF.Rel.le_step Imported.Original_LF_Rel_le__step Original_LF_Rel_le__step_iso := {}.