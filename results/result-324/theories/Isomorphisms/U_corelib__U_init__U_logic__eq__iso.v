From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq.

(* Since we need equality in Type but imported gives us SProp, we need to handle this carefully *)
Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* This is a cross-universe isomorphism between Type and SProp *)
  (* We need to use the fact that both represent the same equality concept *)
  unshelve eapply Build_Iso.
  - (* to: eq in Type -> eq in SProp *)
    intro Heq.
    destruct Heq.
    destruct H34 as [Hto34 Hfrom34].
    destruct H56 as [Hto56 Hfrom56].
    rewrite <- Hto34 in Hto56.
    rewrite Hto56.
    apply Imported.Corelib_Init_Logic_eq_refl.
  - (* from: eq in SProp -> eq in Type *)
    intro Heq.
    destruct H34 as [Hto34 Hfrom34].
    destruct H56 as [Hto56 Hfrom56].
    (* Use SProp elimination *)
    destruct Heq using Imported.Corelib_Init_Logic_eq_sind.
    rewrite <- Hfrom34 in Hfrom56.
    rewrite Hfrom56.
    reflexivity.
  - (* to_from *)
    intro Heq.
    (* SProp proof irrelevance *)
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
  - (* from_to *)
    intro Heq.
    destruct Heq.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.
