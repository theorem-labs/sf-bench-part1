From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Use imported Corelib_Init_Logic_eq_Prop which is now in SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop-valued types, x3 = x5 is a Prop and imported_eq_Prop x4 x6 is an SProp *)
(* Since x2 is SProp, all elements of x2 are definitionally equal *)
(* So imported_Corelib_Init_Logic_eq_Prop x4 x6 is always trivially inhabited *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> eq in SProp *)
    intro Heq.
    (* x3 = x5, need to prove imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    subst x5.
    (* Since x4 and x6 are in SProp x2, they're definitionally equal! *)
    (* x4 : x2 and x6 : x2 where x2 : SProp, so x4 ≡ x6 definitionally *)
    apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: eq in SProp -> eq in Prop *)
    intro Heq.
    (* We need to prove x3 = x5 from the SProp equality *)
    (* Since x2 is SProp, both from hx x4 and from hx x6 return the same thing *)
    (* from_to tells us x3 = from hx (to hx x3) and x5 = from hx (to hx x5) *)
    (* Since x2 is SProp, to hx x3 and to hx x5 are definitionally equal *)
    (* Therefore from hx (to hx x3) = from hx (to hx x5), giving us x3 = x5 *)
    transitivity (from hx (to hx x3)).
    + symmetry. apply eq_of_seq. apply (from_to hx).
    + transitivity (from hx (to hx x5)).
      * reflexivity. (* In SProp, to hx x3 ≡ to hx x5 definitionally *)
      * apply eq_of_seq. apply (from_to hx).
  - (* to_from - SProp terms are definitionally equal *)
    intro Heq; apply IsomorphismDefinitions.eq_refl.
  - (* from_to - use Prop proof irrelevance *)
    intro Heq.
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
