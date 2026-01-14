From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* The Lean export produces eq_Prop for SProp arguments *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop/SProp arguments, the isomorphism is between:
   - Original: eq (on Type, but used with Prop which gets promoted to Type)  
   - Imported: Corelib_Init_Logic_eq_Prop (SProp -> SProp -> SProp)
   
   But wait - the original eq is for Type, not SProp. Looking at the interface,
   it expects: forall (x1 : Type) (x2 : SProp) ...
   So x1 is a Type (Prop) and x2 is its SProp equivalent.
*)

Definition eq_iso_Prop_to {x1 : Type} {x2 : SProp} (hx : Iso x1 x2) (x3 x5 : x1) 
  (Heq : x3 = x5) : Imported.Corelib_Init_Logic_eq_Prop x2 (to hx x3) (to hx x5).
Proof.
  destruct Heq.
  apply Imported.Corelib_Init_Logic_eq_Prop_refl.
Defined.

Definition eq_iso_Prop_from {x1 : Type} {x2 : SProp} (hx : Iso x1 x2) (x3 x5 : x1) 
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
  - (* to: eq in Type -> eq in SProp *)
    intro Heq.
    exact (@eq_iso_Prop_to x1 x2 hx x3 x5 Heq).
  - (* from: eq in SProp -> eq in Type *)
    intro Heq.
    exact (@eq_iso_Prop_from x1 x2 hx x3 x5 Heq).
  - (* to_from: SProp proof irrelevance is automatic *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: Need to show eq_iso_from (eq_iso_to Heq) = Heq *)
    intro Heq.
    destruct Heq.
    unfold eq_iso_Prop_from, eq_iso_Prop_to.
    match goal with
    | |- IsomorphismDefinitions.eq ?x ?y => 
        pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ x y) as Hirr;
        destruct Hirr; apply IsomorphismDefinitions.eq_refl
    end.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
