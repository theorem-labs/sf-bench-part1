From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* The Imported.Corelib_Init_Logic_eq_Prop is now in SProp (since we defined it as Prop in Lean) *)
(* It has type: forall A : SProp, A -> A -> SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop (x : SProp) (a b : x) : SProp := Imported.Corelib_Init_Logic_eq_Prop x a b.

(* When the domain is SProp, there's only one element up to proof irrelevance, 
   so equality in SProp is trivially inhabited *)
(* Isomorphism for equality specialized to Prop/SProp *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), 
  rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> 
  Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* This is an isomorphism between (x3 = x5) in Prop and eq_Prop x4 x6 in SProp *)
  (* Since x2 : SProp, all elements of x2 are equal by proof irrelevance *)
  (* But we're comparing in the Prop world with standard equality *)
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> eq_Prop in SProp *)
    intro Heq.
    destruct Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    (* In SProp, x4 = x6 by proof irrelevance, so we can use refl *)
    (* Use the SProp-specific refl constructor *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  - (* from: eq_Prop in SProp -> eq in Prop *)
    intro Heq.
    (* We need to show x3 = x5 *)
    (* rel_iso hx x3 x4 means IsomorphismDefinitions.eq (to hx x3) x4 *)
    (* rel_iso hx x5 x6 means IsomorphismDefinitions.eq (to hx x5) x6 *)
    (* Heq: Imported.Corelib_Init_Logic_eq x4 x6, i.e. x4 = x6 in SProp sense *)
    pose proof (from_to hx x3) as Hx3.  (* eq (from hx (to hx x3)) x3 *)
    pose proof (from_to hx x5) as Hx5.  (* eq (from hx (to hx x5)) x5 *)
    (* But to hx x3 and to hx x5 are both in x2 : SProp, so they're equal! *)
    (* In fact, to hx x3 = x4 and to hx x5 = x6 by the rel_iso hypotheses *)
    (* And x4 = x6 in SProp by proof irrelevance *)
    (* Actually, (to hx x3) = (to hx x5) because SProp has proof irrelevance *)
    (* So from hx (to hx x3) = from hx (to hx x5), hence x3 = x5 *)
    apply IsoEq.eq_of_seq.
    apply (IsoEq.eq_trans (IsoEq.eq_sym Hx3)).
    (* from hx (to hx x3) = from hx (to hx x5) *)
    (* This follows because to hx x3 = to hx x5 (both in SProp) *)
    exact Hx5.
  - (* to_from *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    destruct Heq.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
