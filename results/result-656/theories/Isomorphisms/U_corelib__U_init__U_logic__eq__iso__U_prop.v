From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Isomorphism for equality on Prop/SProp *)
(* The domain is Type on the left (Prop) and SProp on the right *)
(* Note: In Rocq, Prop is a subset of Type, so we use Type for the left side *)
#[local] Unset Universe Polymorphism.
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), 
  rel_iso hx x3 x4 -> 
  forall (x5 : x1) (x6 : x2), 
  rel_iso hx x5 x6 -> 
  Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  (* Goal: Iso (x3 = x5) (Imported.Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5)) *)
  unshelve eapply Build_Iso.
  - (* to: (x3 = x5) -> imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq. subst x5. apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> (x3 = x5) *)
    intro Heq.
    (* Use the recl eliminator for SProp equality *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    destruct Hft3. destruct Hft5.
    reflexivity.
  - (* to_from: in SProp, always trivial *)
    intro. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: use UIP/proof irrelevance *)
    intro Heq.
    (* Heq : x3 = x5 in Prop. After round-trip we get a potentially different proof.
       But all proofs of x3 = x5 are equal by proof irrelevance. *)
    set (roundtrip := (fun Heq0 : imported_Corelib_Init_Logic_eq_Prop (hx x3) (hx x5) =>
          match from_to hx x3 in (IsomorphismDefinitions.eq _ x) return (x = x5) with
          | IsomorphismDefinitions.eq_refl =>
              match from_to hx x5 in (IsomorphismDefinitions.eq _ x) return (from hx (hx x3) = x) with
              | IsomorphismDefinitions.eq_refl => Logic.eq_refl
              end
          end)
       ((fun Heq0 : x3 = x5 =>
         Logic.eq_sind
           (fun x50 : x1 =>
            imported_Corelib_Init_Logic_eq_Prop (hx x3) (hx x50))
           (Imported.Corelib_Init_Logic_eq_Prop_refl x2 (hx x3)) Heq0)
          Heq)).
    pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance (x3 = x5) roundtrip Heq) as PI.
    rewrite <- PI.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
