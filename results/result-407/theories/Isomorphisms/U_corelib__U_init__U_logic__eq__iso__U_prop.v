From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For the Prop version, both sides are already SProp, so the isomorphism is simpler *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> imported eq_Prop in SProp *)
    intro Heq.
    destruct Heq.
    (* We need to prove x4 = x6 in imported_Corelib_Init_Logic_eq_Prop *)
    (* Both x4 and x6 are in x2 : SProp, so they're definitionally equal *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  - (* from: imported eq_Prop in SProp -> eq in Prop *)
    intro Heq.
    (* x4 and x6 are in SProp x2, so any two elements are equal *)
    (* We need to prove x3 = x5 in Prop *)
    (* Use from_to to get from(hx x3) = x3 and from(hx x5) = x5 *)
    pose (Hfrom3 := from_to hx x3).
    pose (Hfrom5 := from_to hx x5).
    (* We use that x2 : SProp, so any two elements are equal *)
    (* Actually, we can derive x3 = x5 from the fact that hx x3 and hx x5 are both in SProp *)
    exact (eq_of_seq (eq_trans (eq_sym Hfrom3) Hfrom5)).
  - (* to_from: both are SProp, definitionally equal *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: use UIP for Prop equality *)
    intro Heq.
    destruct Heq.
    apply sUIPt.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
