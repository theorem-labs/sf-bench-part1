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

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  
  (* First prove x3 = x5 using that x2 : SProp implies all inhabitants are equal *)
  assert (H_x3_eq_x5 : x3 = x5).
  {
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    apply eq_of_seq in Hft3.
    apply eq_of_seq in Hft5.
    rewrite <- Hft3, <- Hft5.
    (* to hx x3 : x2 and to hx x5 : x2, where x2 : SProp *)
    (* So to hx x3 = to hx x5 definitionally *)
    reflexivity.
  }
  
  (* Now build the iso using that both sides are inhabited *)
  refine {|
    to := fun _ => Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4;
    from := fun _ => H_x3_eq_x5;
    to_from := _;
    from_to := _
  |}.
  - intros e. apply IsomorphismDefinitions.eq_refl.
  - intros e. apply seq_of_eq. apply proof_irrelevance.
Defined.
Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
