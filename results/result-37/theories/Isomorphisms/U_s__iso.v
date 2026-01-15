From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)



From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_S : imported_nat -> imported_nat := Imported.S.
Instance S_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> rel_iso nat_iso (S x1) (imported_S x2).
Proof.
  intros x1 x2 H.
  unfold imported_S.
  destruct H as [H].
  constructor.
  simpl.
  (* to nat_iso (S x1) = nat_to_imported (S x1) = Imported.nat_S (nat_to_imported x1) *)
  (* H says: nat_to_imported x1 = x2 *)
  (* We need: Imported.nat_S (nat_to_imported x1) = Imported.S x2 *)
  (* Imported.S = Imported.nat_S by definition *)
  apply (IsoEq.f_equal Imported.nat_S H).
Defined.
Instance: KnownConstant S := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.S := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor S S_iso := {}.
Instance: IsoStatementProofBetween S Imported.S S_iso := {}.