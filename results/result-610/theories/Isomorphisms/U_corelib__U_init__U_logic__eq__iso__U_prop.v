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

(* For Prop-level equality, source is (x3=x5 : Prop), target is in SProp *)
(* Key insight: If hx : Iso x1 x2 where x2 : SProp, then x1 is a subsingleton
   because from hx (to hx x3) = x3 and from hx (to hx x5) = x5,
   but to hx x3 and to hx x5 are the same element (since x2 is SProp),
   so x3 = x5. *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unshelve eapply Build_Iso.
  - (* to: (x3 = x5) -> imported_eq_Prop x4 x6 *)
    intro Heq. subst x5.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    unfold rel_iso in H34, H56. simpl in H34, H56.
    destruct H34. destruct H56.
    apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: imported_eq_Prop x4 x6 -> (x3 = x5) *)
    intros _.
    (* Since x2 is SProp, to hx x3 and to hx x5 are definitionally equal *)
    (* So from hx (to hx x3) = from hx (to hx x5) *)
    (* But from_to gives: from hx (to hx x) = x *)
    transitivity (from hx (to hx x3)).
    + symmetry. apply eq_of_seq. apply (from_to hx).
    + transitivity (from hx (to hx x5)).
      * reflexivity. (* to hx x3 = to hx x5 in SProp by definitional equality *)
      * apply eq_of_seq. apply (from_to hx).
  - intro Heq. apply IsomorphismDefinitions.eq_refl.
  - intro Heq. apply seq_of_eq. apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
