From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* This isomorphism is between Prop eq on Prop types and SProp eq on SProp types *)
(* The interface says: x1 : Type, x2 : SProp, but the HList sorts indicates x1 is actually Prop *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  unshelve eapply Build_Iso.
  - intro Heq. subst x5. apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - intro Heq.
    (* x4 and x6 are in x2 which is SProp, and they are related to x3, x5 *)
    (* We can derive x3 = x5 from the isomorphism *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    (* Since x4 = to hx x3 and x6 = to hx x5, and both are in SProp (x2) *)
    (* For SProp equality, the recursor gives us a transport mechanism *)
    pose proof (@Imported.Corelib_Init_Logic_eq_Prop_recl x2 (to hx x3) 
      (fun y _ => from hx (to hx x3) = from hx y) 
      (Corelib.Init.Logic.eq_refl (from hx (to hx x3))) 
      (to hx x5) Heq) as Hfrom_eq.
    destruct Hft3. destruct Hft5.
    exact Hfrom_eq.
  - intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - intro Heq.
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
