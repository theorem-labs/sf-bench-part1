From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* The imported eq_Prop is for SProp, not Prop, due to import conversion *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* The isomorphism is from x1 : Type (the coercion of Prop) to x2 : SProp *)
Definition eq_iso_to_Prop {x1 : Type} {x2 : SProp} (hx : Iso x1 x2) (x3 x5 : x1) 
  (Heq : x3 = x5) : Imported.Corelib_Init_Logic_eq_Prop x2 (to hx x3) (to hx x5).
Proof.
  destruct Heq.
  apply Imported.Corelib_Init_Logic_eq_Prop_refl.
Defined.

Definition eq_iso_from_Prop {x1 : Type} {x2 : SProp} (hx : Iso x1 x2) (x3 x5 : x1) 
  (Heq : Imported.Corelib_Init_Logic_eq_Prop x2 (to hx x3) (to hx x5)) : x3 = x5.
Proof.
  pose proof (from_to hx x3) as Hrt3.
  pose proof (from_to hx x5) as Hrt5.
  destruct Hrt3. destruct Hrt5.
  apply (Imported.Corelib_Init_Logic_eq_Prop_recl x2 (to hx x3) (fun y _ => from hx (to hx x3) = from hx y) Logic.eq_refl (to hx x5) Heq).
Defined.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  unshelve eapply Build_Iso.
  - intro Heq. exact (@eq_iso_to_Prop x1 x2 hx x3 x5 Heq).
  - intro Heq. exact (@eq_iso_from_Prop x1 x2 hx x3 x5 Heq).
  - intro Heq. apply IsomorphismDefinitions.eq_refl.
  - intro Heq.
    destruct Heq.
    match goal with
    | |- IsomorphismDefinitions.eq ?x ?y => 
        pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ x y) as Hirr;
        destruct Hirr; apply IsomorphismDefinitions.eq_refl
    end.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
