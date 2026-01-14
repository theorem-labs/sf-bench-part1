From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_add1 : imported_nat -> imported_nat := Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_add1.

Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_add1_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> rel_iso nat_iso (Original.LF_DOT_ProofObjects.LF.ProofObjects.add1 x1) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_add1 x2).
Proof.
  intros x1 x2 H.
  unfold rel_iso in *.
  unfold Original.LF_DOT_ProofObjects.LF.ProofObjects.add1.
  unfold imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_add1.
  unfold Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_add1.
  simpl.
  (* H : IsomorphismDefinitions.eq (nat_to_imported x1) x2 *)
  (* Goal : IsomorphismDefinitions.eq (Imported.nat_S (nat_to_imported x1)) (Imported.nat_S x2) *)
  apply (IsoEq.f_equal Imported.nat_S).
  exact H.
Defined.
Instance: KnownConstant Original.LF_DOT_ProofObjects.LF.ProofObjects.add1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_add1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.add1 Original_LF__DOT__ProofObjects_LF_ProofObjects_add1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.add1 Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_add1 Original_LF__DOT__ProofObjects_LF_ProofObjects_add1_iso := {}.