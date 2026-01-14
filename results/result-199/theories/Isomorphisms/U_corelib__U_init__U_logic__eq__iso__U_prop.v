From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper: proof irrelevance for Prop eq expressed in SProp eq *)
(* We use the fact that Stdlib.Logic.ProofIrrelevance.proof_irrelevance is allowed *)
Lemma prop_eq_proof_irrel_local {A : Type} {x y : A} (p q : x = y) : IsomorphismDefinitions.eq p q.
Proof.
  pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ p q) as H.
  destruct H. exact (IsomorphismDefinitions.eq_refl _).
Defined.

(* Iso between Prop eq and SProp eq for SProp types *)
(* For SProp types, we need an isomorphism between (x3 = x5) and imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
(* Since everything is in SProp, proof irrelevance makes this trivial *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq. subst x5. apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> x3 = x5 *)
    intro Heq.
    (* Use the eliminator for Corelib_Init_Logic_eq_Prop *)
    pose proof (Imported.Corelib_Init_Logic_eq_Prop_recl x2 (to hx x3) (fun z _ => from hx (to hx x3) = from hx z) (Corelib.Init.Logic.eq_refl _) (to hx x5) Heq) as H.
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    destruct Hft3. destruct Hft5.
    exact H.
  - (* to_from - SProp proof, so trivial *)
    intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to - Prop equality with proof irrelevance *)
    intro Heq.
    apply prop_eq_proof_irrel_local.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
