From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.
(* Note: Don't import U_corelib__U_init__U_logic__eq__iso to avoid circular dependency *)

(* Imported.Corelib_Init_Logic_eq_Prop is now in SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper to extract eq from Imported.Corelib_Init_Logic_eq_Prop *)
Definition seq_prop_to_eq {A : SProp} {x y : A} (H : Imported.Corelib_Init_Logic_eq_Prop A x y) : IsomorphismDefinitions.eq x y :=
  match H with Imported.Corelib_Init_Logic_eq_Prop_refl _ _ => IsomorphismDefinitions.eq_refl end.

(* For Prop-level equality, both sides are propositions *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  - (* to : (x3 = x5) -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq.
    destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - (* from : imported_Corelib_Init_Logic_eq_Prop x4 x6 -> (x3 = x5) *)
    intro Hseq.
    destruct H34. destruct H56.
    (* The SProp equality Hseq tells us x4 = x6 in SProp *)
    (* Since hx is an Iso and to hx x3 = x4, to hx x5 = x6, and x4 = x6 (from Hseq), *)
    (* we can derive x3 = x5 using injectivity of hx *)
    pose proof (seq_prop_to_eq Hseq) as Hseq'.
    (* Hseq' : to hx x3 = to hx x5 in SProp *)
    (* Use from_to to get back to x1 *)
    assert (from hx (to hx x3) = from hx (to hx x5)) as Hfrom.
    { destruct Hseq'. reflexivity. }
    rewrite !from_to_tseq in Hfrom.
    exact Hfrom.
  - (* to_from *)
    intro Hseq.
    (* Both sides are in SProp, so equality is trivial *)
    reflexivity.
  - (* from_to *)
    intro Heq.
    destruct H34. destruct H56. destruct Heq.
    simpl.
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
