From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Use imported Corelib_Init_Logic_eq_Prop which is now in SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For SProp equality, when x2 : SProp, all its inhabitants are definitionally equal.
   This means the imported_Corelib_Init_Logic_eq_Prop x4 x6 is always true (inhabited).
   For the forward direction, we can always construct the SProp equality.
   For the backward direction, we can use the from_to properties. *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* Source is Prop (x3 = x5), target is SProp (imported_Corelib_Init_Logic_eq_Prop x4 x6) *)
  (* Since x4, x6 : x2 where x2 : SProp, x4 and x6 are definitionally equal! *)
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> eq_Prop in SProp *)
    intro Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    (* Since x4, x6 : x2 : SProp, we have x4 ≡ x6, so Corelib_Init_Logic_eq_Prop x4 x6 is refl *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  - (* from: eq_Prop in SProp -> eq in Prop *)
    intro Heq.
    unfold rel_iso in H34, H56.
    simpl in H34, H56.
    (* H34 : to hx x3 = x4, H56 : to hx x5 = x6 in IsomorphismDefinitions.eq (SProp) *)
    (* Since x4, x6 : x2 : SProp are definitionally equal, to hx x3 = to hx x5 *)
    (* Use from_to both ways *)
    transitivity (from hx (to hx x3)).
    + symmetry. apply eq_of_seq. apply (from_to hx).
    + transitivity (from hx (to hx x5)).
      * (* Since x2 : SProp, to hx x3 : x2 and to hx x5 : x2 are definitionally equal *)
        reflexivity.
      * apply eq_of_seq. apply (from_to hx).
  - (* to_from - SProp terms are definitionally equal *)
    intro Heq; apply IsomorphismDefinitions.eq_refl.
  - (* from_to - use Prop proof irrelevance *)
    intro Heq.
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
