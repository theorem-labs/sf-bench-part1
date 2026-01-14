From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

(* Standalone version for Prop *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Key lemma: from an Iso to SProp, from applied to any two SProp elements gives equal results *)
(* Because SProp is proof-irrelevant, from x4 = from x6 for any x4 x6 : x2 when x2 : SProp *)
Lemma from_SProp_equal : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x4 x6 : x2),
  from hx x4 = from hx x6.
Proof.
  intros x1 x2 hx x4 x6.
  reflexivity. (* SProp proof irrelevance makes x4 = x6 definitionally *)
Qed.

(* For Type -> SProp isomorphisms where the Type is actually Prop *)
(* The signature must match the interface: x1 : Type *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  - intro Heq.
    destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - intro Hseq.
    (* We have H34 : to hx x3 = x4 and H56 : to hx x5 = x6 in seq (SProp equality) *)
    (* We need x3 = x5 *)
    (* Use: x3 = from (to x3) = from x4 and x5 = from (to x5) = from x6 *)
    (* And from x4 = from x6 by SProp irrelevance *)
    destruct H34. destruct H56.
    (* Now we need from (to hx x3) = from (to hx x5) which follows from from_to *)
    (* Use eq_of_seq to convert SProp equality to Logic.eq *)
    transitivity (from hx (to hx x3)).
    + symmetry. apply eq_of_seq. exact (from_to hx x3).
    + transitivity (from hx (to hx x5)).
      * apply from_SProp_equal.
      * apply eq_of_seq. exact (from_to hx x5).
  - intro Hseq.
    reflexivity.
  - intro Heq.
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
