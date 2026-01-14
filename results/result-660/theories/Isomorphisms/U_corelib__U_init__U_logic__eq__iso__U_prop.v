From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* The Lean export produces eq_Prop for when the type argument is SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop/SProp equality, both sides are proof irrelevant *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* Both sides are singleton types by proof irrelevance *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 in Prop -> x4 = x6 in SProp *)
    intro Heq.
    destruct Heq.
    destruct H34. (* x4 = to hx x3 so x4 = x4 *)
    apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: x4 = x6 in SProp -> x3 = x5 in Prop *)
    intro Heq.
    pose proof (from_to hx x3) as Hrt3.
    pose proof (from_to hx x5) as Hrt5.
    destruct Hrt3. destruct Hrt5.
    apply (Imported.Corelib_Init_Logic_eq_Prop_recl x2 (to hx x3) (fun y _ => from hx (to hx x3) = from hx y) Logic.eq_refl (to hx x5) Heq).
  - (* to_from: SProp proof irrelevance is automatic *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: Use proof irrelevance *)
    intro Heq.
    destruct Heq.
    match goal with
    | |- IsomorphismDefinitions.eq ?x ?y => 
        pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ x y) as Hirr;
        destruct Hirr; apply IsomorphismDefinitions.eq_refl
    end.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
