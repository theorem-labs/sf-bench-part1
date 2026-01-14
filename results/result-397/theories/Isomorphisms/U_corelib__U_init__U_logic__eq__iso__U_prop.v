From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop for Prop arguments *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For the Prop version, we need isomorphisms between Types (actually Prop) and SProp *)
(* The key insight: both x3=x5 in Prop and imported_Corelib_Init_Logic_eq_Prop x4 x6 in SProp 
   are essentially propositions - either empty or singleton. We build an Iso between them. *)

(* Helper: Given an SProp equality, produce a Prop equality by eliminating into Prop *)
(* We need to use the from function of the iso and the fact that from is injective *)
Definition from_imported_eq_prop_to_from_eq {x1 : Type} {x2 : SProp} (hx : Iso x1 x2) (x3 x5 : x1)
  (Hseq : Imported.Corelib_Init_Logic_eq_Prop x2 (to hx x3) (to hx x5)) : x3 = x5.
Proof.
  (* We rewrite using from_to *)
  rewrite <- (from_to hx x3).
  rewrite <- (from_to hx x5).
  (* Now we need from hx (to hx x3) = from hx (to hx x5) *)
  (* Which follows from to hx x3 = to hx x5 via f_equal *)
  (* But we have Hseq in SProp, so destruct it first *)
  destruct Hseq.
  (* Now to hx x3 and to hx x5 are definitionally equal, so from hx applied gives same result *)
  reflexivity.
Defined.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  + (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq. destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  + (* from: imported_Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5 *)
    intro Hseq.
    destruct H34. destruct H56.
    (* Hseq : Imported.Corelib_Init_Logic_eq_Prop x2 (to hx x3) (to hx x5) *)
    exact (from_imported_eq_prop_to_from_eq hx x3 x5 Hseq).
  + (* to_from *)
    intro Hseq.
    reflexivity.
  + (* from_to *)
    intro Heq.
    destruct H34. destruct H56. destruct Heq.
    simpl.
    (* Both sides are proofs of x3 = x3 in Prop, use proof irrelevance *)
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
