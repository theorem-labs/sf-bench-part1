From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

(* Prop version of equality isomorphism: forall x : SProp, x -> x -> SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For SProp arguments, both source and target are SProp, so all proofs are equal *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> imported eq_Prop in SProp *)
    intro Heq.
    destruct Heq.
    (* Need to show x4 = x6 in SProp, but x4 and x6 are in x2 : SProp *)
    (* Since x2 is SProp, all its elements are equal *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  - (* from: imported eq_Prop in SProp -> eq in Prop *)
    intro Heq.
    (* x3 = x5 in Prop *)
    (* We use the fact that hx : Iso x1 x2 with x2 : SProp *)
    (* H34 : hx x3 = x4, H56 : hx x5 = x6, both in SProp *)
    (* Since target is SProp, from(x4) = from(x6) as x4 = x6 in SProp *)
    pose (Hfrom34 := from_to hx x3). (* eq (from hx (hx x3)) x3 *)
    pose (Hfrom56 := from_to hx x5). (* eq (from hx (hx x5)) x5 *)
    (* Since x2 is SProp, hx x3 = hx x5 definitionally in SProp *)
    (* Thus from(hx x3) = from(hx x5) *)
    (* And by from_to: from(hx x3) = x3, from(hx x5) = x5 *)
    (* So x3 = x5 *)
    pose (step := IsoEq.eq_trans (IsoEq.eq_sym Hfrom34) Hfrom56).
    exact (IsoEq.eq_of_seq step).
  - (* to_from: both are SProp, they're definitionally equal *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: use UIP for Prop equality *)
    intro Heq.
    destruct Heq.
    apply sUIPt.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
