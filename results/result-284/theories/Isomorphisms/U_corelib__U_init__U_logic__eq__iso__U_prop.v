From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib.Logic Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq_Prop).

(* For equality on Prop/SProp, we can use a simpler construction *)
(* Since x2 is SProp, the equality is trivial - all proofs in SProp are equal *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 h34 x5 x6 h56.
  unshelve econstructor.
  - (* to *)
    intro H. destruct H.
    (* We need Corelib_Init_Logic_eq_Prop x4 x4, but x4 : x2 which is SProp *)
    (* In SProp, all inhabitants are equal, so we can use refl *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  - (* from *)
    intro H.
    (* We need x3 = x5 in Prop *)
    (* Since x2 is SProp, from hx is constant - from x4 = from x6 *)
    (* Use the round-trip property: x3 = from (to x3) and x5 = from (to x5) *)
    (* And since x4 = x6 in SProp (they are equal), from x4 = from x6 *)
    pose proof (from_to hx x3) as FT3.
    pose proof (from_to hx x5) as FT5.
    (* Both from (to x3) = x3 and from (to x5) = x5 *)
    (* But in SProp, to x3 = x4 = x6 = to x5, so from (to x3) = from (to x5) *)
    (* Therefore x3 = x5 *)
    transitivity (from hx (to hx x3)).
    + symmetry. exact (eq_of_seq FT3).
    + transitivity (from hx (to hx x5)).
      * reflexivity. (* In SProp, to x3 = to x5 since x4 = x6 *)
      * exact (eq_of_seq FT5).
  - (* to_from *)
    intro. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro x.
    apply seq_of_eq.
    apply proof_irrelevance.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}. 
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
