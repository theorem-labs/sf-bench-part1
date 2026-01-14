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

(* When the first type argument is a Prop mapped to SProp, we need to show:
   Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6)
   where x3 = x5 is Prop and the imported eq is SProp. *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq.
    subst x5.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    unfold rel_iso in H34, H56.
    simpl in H34, H56.
    (* H34 : to hx x3 = x4 (in SProp), H56 : to hx x3 = x6 (in SProp) *)
    (* Both are in SProp, so we can destruct them *)
    destruct H34. destruct H56.
    apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: imported_Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5 *)
    intro Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop in Heq.
    unfold rel_iso in H34, H56.
    simpl in H34, H56.
    (* Heq : Imported.Corelib_Init_Logic_eq_Prop x4 x6 *)
    destruct Heq.
    (* Now x4 = x6 (in SProp sense), but we know:
       H34 : to hx x3 = x4, H56 : to hx x5 = x4 *)
    (* We need to show x3 = x5 in Prop. Use from_to. *)
    assert (Hinj : x3 = x5).
    { transitivity (from hx (to hx x3)).
      - symmetry. apply eq_of_seq. apply (from_to hx).
      - transitivity (from hx (to hx x5)).
        + (* from hx (to hx x3) = from hx (to hx x5) *)
          (* Use f_equal (from IsoEq) which works with SProp eq, then convert to Prop eq *)
          apply eq_of_seq. apply f_equal.
          (* Show to hx x3 = to hx x5 in SProp *)
          eapply eq_trans. exact H34. apply eq_sym. exact H56.
        + apply eq_of_seq. apply (from_to hx).
    }
    exact Hinj.
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
