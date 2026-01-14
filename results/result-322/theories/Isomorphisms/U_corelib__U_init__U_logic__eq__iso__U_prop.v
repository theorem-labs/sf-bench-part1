From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
From Stdlib Require Import ProofIrrelevance.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For SProp types, equality is trivial since all values are equal *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  - (* to *)
    intro Heq.
    destruct Heq.
    destruct H34.
    destruct H56.
    apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from *)
    intro Heq.
    destruct H34.
    destruct H56.
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    destruct Hft3.
    destruct Hft5.
    (* x2 is in SProp, so all elements are equal *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_recl x2 (to hx x3) 
           (fun z _ => from hx (to hx x3) = from hx z) 
           Logic.eq_refl (to hx x5) Heq).
  - (* to_from - result is in SProp *)
    intro Heq.
    exact IsomorphismDefinitions.eq_refl.
  - (* from_to - need to show from (to Heq) = Heq for equality in Prop *)
    intro Heq.
    apply seq_of_eq.
    apply proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
