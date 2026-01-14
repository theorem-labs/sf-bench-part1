From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
From Stdlib Require Import Logic.Eqdep_dec.
Typeclasses Opaque rel_iso.

(* Use proof irrelevance to handle all equality proofs *)
Lemma eq_proofs_equal : forall (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intros A x y p q.
  apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Qed.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop types (which are SProp in import), build the isomorphism manually *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq. destruct H34, H56, Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - (* from: imported_Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5 *)
    intro Hseq.
    destruct H34, H56.
    (* Both x3 and x5 get mapped to the same element in x2 (SProp).
       Since from_to gives us from (to x) = x, and the imported eq
       tells us to x3 = to x5 in SProp, we can derive x3 = x5 in Type. *)
    assert (Hfrom: from hx (to hx x3) = from hx (to hx x5)).
    { f_equal. destruct Hseq. reflexivity. }
    rewrite !from_to in Hfrom.
    exact Hfrom.
  - (* to_from *)
    intro Hseq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    destruct H34, H56, Heq.
    simpl.
    rewrite (@eq_proofs_equal x1 x3 x3 _ Logic.eq_refl).
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
