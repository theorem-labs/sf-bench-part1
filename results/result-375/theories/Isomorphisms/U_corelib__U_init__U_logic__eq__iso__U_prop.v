From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop is now in SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Define the to/from functions for the eq iso Prop version *)
Definition eq_iso_to_Prop (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : IsomorphismDefinitions.eq (to hx x3) x4) (x5 : x1) (x6 : x2) (H56 : IsomorphismDefinitions.eq (to hx x5) x6)
  : x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop x4 x6.
Proof.
  intro Heq.
  destruct H34. destruct H56. destruct Heq.
  exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
Defined.

Definition eq_iso_from_Prop (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : IsomorphismDefinitions.eq (to hx x3) x4) (x5 : x1) (x6 : x2) (H56 : IsomorphismDefinitions.eq (to hx x5) x6)
  : imported_Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5.
Proof.
  intro Hseq.
  destruct H34. destruct H56.
  (* Since x2 : SProp, all elements of x2 are equal. So to hx x3 = to hx x5 in SProp.
     We need to show x3 = x5. Since hx is an isomorphism, we have:
     x3 = from hx (to hx x3) = from hx (to hx x5) = x5 *)
  transitivity (from hx (to hx x3)).
  - symmetry. apply eq_of_seq. exact (from_to hx x3).
  - transitivity (from hx (to hx x5)).
    + reflexivity. (* In SProp, to hx x3 = to hx x5 definitionally *)
    + apply eq_of_seq. exact (from_to hx x5).
Defined.

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  + exact (@eq_iso_to_Prop x1 x2 hx x3 x4 H34 x5 x6 H56).
  + exact (@eq_iso_from_Prop x1 x2 hx x3 x4 H34 x5 x6 H56).
  + (* to_from *)
    intro Hseq.
    reflexivity.
  + (* from_to *)
    intro Heq.
    (* Both sides are in Prop, use proof irrelevance *)
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
