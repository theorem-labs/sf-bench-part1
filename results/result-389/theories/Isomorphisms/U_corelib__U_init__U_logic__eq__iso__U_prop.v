From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Isomorphism for equality on SProp (Props mapped to SProps) *)
(* Source: x3 = x5 in Prop, Target: imported eq in SProp *)
(* Since x2 is SProp, all its inhabitants are equal, so both source and target are trivially inhabited or uninhabited *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* rel_iso hx x3 x4 means hx x3 = x4 in SProp
     rel_iso hx x5 x6 means hx x5 = x6 in SProp
     Since x2 is SProp, x4 and x6 are definitionally equal. *)
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> imported eq in SProp *)
    intro Heq.
    (* In SProp, all elements are equal, so imported_eq x4 x6 is trivially true *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  - (* from: imported eq in SProp -> eq in Prop *)
    intro Heq.
    (* We need to show x3 = x5. Since hx is an isomorphism:
       hx x3 = x4, hx x5 = x6, and x4 = x6 (by SProp definitional equality)
       So hx x3 = hx x5, hence by isomorphism x3 = x5 *)
    (* Since x2 is SProp, to hx x3 and to hx x5 are definitionally equal *)
    (* Use from_to to get x3 = from (to x3) = from (to x5) = x5 *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    (* In SProp, to x3 = to x5 definitionally, so from (to x3) = from (to x5) *)
    (* Thus x3 = from (to x3) = from (to x5) = x5 *)
    exact (eq_of_seq (eq_trans (eq_sym Hft3) Hft5)).
  - (* to_from: SProp equality is proof-irrelevant *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: UIP for Prop equality *)
    intro Heq.
    destruct Heq.
    apply sUIPt.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
