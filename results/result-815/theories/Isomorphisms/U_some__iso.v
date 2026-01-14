From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.option__iso.

Definition imported_Some : forall x : Type, x -> imported_option x := (@Imported.Some).

(* rel_iso for option_iso is: eq (to (option_iso hx) x) y 
   where to (option_iso hx) = option_to_imported (to hx)
   So we need: eq (option_to_imported (to hx) (Some x3)) (imported_Some x4)
   which is: eq (Imported.option_Some (to hx x3)) (Imported.option_Some x4)
   
   From rel_iso hx x3 x4, we have: eq (to hx x3) x4
   So we can use f_equal to get the result.
*)
Instance Some_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> rel_iso (option_iso hx) (Some x3) (imported_Some x4).
Proof.
  intros x1 x2 hx x3 x4 Hrel.
  unfold rel_iso in *.
  simpl.
  unfold option_to_imported, imported_Some.
  (* Hrel : eq (to hx x3) x4 *)
  (* Goal: eq (Imported.option_Some x2 (to hx x3)) (Imported.option_Some x2 x4) *)
  exact (IsoEq.f_equal (Imported.option_Some x2) Hrel).
Defined.
Instance: KnownConstant (@Some) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Some) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Some) Some_iso := {}.
Instance: IsoStatementProofBetween (@Some) (@Imported.Some) Some_iso := {}.