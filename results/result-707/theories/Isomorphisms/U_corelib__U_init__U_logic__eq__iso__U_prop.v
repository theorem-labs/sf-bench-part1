From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop : forall A : SProp, A -> A -> SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For SProp types, the from direction uses that from hx : x2 -> x1 and the Iso guarantees from_to *)
Lemma from_iso_eq {x1 : Type} {x2 : SProp} (hx : Iso x1 x2) (x3 x5 : x1)
  : x3 = x5.
Proof.
  (* In SProp, all inhabitants are definitionally equal, so to hx x3 = to hx x5 *)
  (* And from_to gives us from hx (to hx x3) = x3 etc. *)
  transitivity (from hx (to hx x3)).
  - symmetry. apply from_to_tseq.
  - transitivity (from hx (to hx x5)).
    + reflexivity. (* SProp definitional equality since to hx x3 : x2 and to hx x5 : x2 are definitionally equal *)
    + apply from_to_tseq.
Defined.

(* For Prop arguments, when we map Type -> SProp *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop x2 x4 x6 *)
    intro Heq. 
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ x4).
  - (* from: imported_Corelib_Init_Logic_eq_Prop x2 x4 x6 -> x3 = x5 *)
    intro Hseq.
    exact (from_iso_eq hx x3 x5).
  - (* to_from *)
    intro Hseq. reflexivity.
  - (* from_to *)
    intro Heq. 
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
