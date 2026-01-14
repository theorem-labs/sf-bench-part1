From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop is now in SProp (defined in Prop in Lean) *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper: we need to build an Iso between a Prop and a specific SProp.
   The idea: both (x3 = x5) : Prop and imported_Corelib_Init_Logic_eq_Prop x4 x6 : SProp
   are proof-irrelevant. We use SInhabited to bridge them. *)

Definition Prop_to_SProp_iso (P : Prop) (S : SProp) 
  (to_S : P -> S) (from_P : S -> P) : Iso P S.
Proof.
  unshelve eapply Build_Iso.
  - exact to_S.
  - exact from_P.
  - intro s. apply IsomorphismDefinitions.eq_refl. (* SProp proof irrelevance *)
  - intro p. apply seq_of_eq. apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

(* For SProp, both the domain (x3 = x5 : Prop) and codomain (imported_Corelib_Init_Logic_eq_Prop x4 x6 : SProp) 
   are proof-irrelevant propositions. *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  apply Prop_to_SProp_iso.
  - intro Heq. 
    destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - intro Hseq. 
    destruct H34. destruct H56.
    (* We need x3 = x5, given Hseq : imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    (* Since x2 : SProp and to hx x3, to hx x5 : x2, all elements of x2 are equal *)
    (* So to hx x3 = to hx x5, and by iso injectivity, x3 = x5 *)
    rewrite <- (from_to hx x3).
    rewrite <- (from_to hx x5).
    reflexivity.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
