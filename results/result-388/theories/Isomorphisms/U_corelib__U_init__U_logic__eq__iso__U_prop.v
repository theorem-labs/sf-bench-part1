From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* This is an isomorphism between Prop eq (on Prop) and SProp eq (on SProp) *)
(* For Prop values, we map from x1 : Type (interpreted as Prop) to x2 : SProp *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* Since x2 is in SProp, all terms of type x2 are definitionally equal *)
  (* So x4 and x6 are definitionally equal, and so is the SProp eq between them *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 *)
    intro Heq.
    (* x4 and x6 are in SProp, so they are definitionally equal *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  - (* from: Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 -> x3 = x5 *)
    intro Heq.
    (* Use the iso to get back *)
    destruct H34. destruct H56.
    (* from_to gives us that from (to x) = x *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    destruct Hft3. destruct Hft5.
    reflexivity.
  - (* to_from: in SProp, so trivial *)
    intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to: need proof irrelevance *)
    intro Heq.
    (* After destructing H34 and H56, we need to show the constructed eq = Heq *)
    (* This requires proof irrelevance *)
    apply (seq_of_eq).
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
