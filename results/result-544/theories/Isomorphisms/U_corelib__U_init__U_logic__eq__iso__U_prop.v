From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib.Logic Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq_Prop).

(* Use iso_SInhabited to bridge Prop and SProp *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  (* x3 = x5 is in Prop, Corelib_Init_Logic_eq_Prop x2 x4 x6 is in SProp *)
  (* Since x2 : SProp, all its elements are definitionally equal *)
  
  (* First establish x3 = x5 using the fact that from (to x3) = from (to x5) *)
  pose proof (from_to hx x3) as Hft3.
  pose proof (from_to hx x5) as Hft5.
  apply eq_of_seq in Hft3.
  apply eq_of_seq in Hft5.
  
  (* x3 = from (to x3), x5 = from (to x5), and to x3 = to x5 since they're in SProp *)
  assert (Heq : x3 = x5).
  { rewrite <- Hft3, <- Hft5. reflexivity. }
  
  (* Construct the iso using Heq *)
  refine {|
    to := fun _ => Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4;
    from := fun _ => Heq;
    to_from := fun _ => IsomorphismDefinitions.eq_refl;
    from_to := fun _ => seq_of_eq (proof_irrelevance _ _ _)
  |}.
Defined.
Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
