From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper: When we have Iso x1 x2 with x2 : SProp, all elements of x1 are equal
   because SProp has definitional proof irrelevance *)
Lemma sprop_iso_collapse : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 x5 : x1),
  x3 = x5.
Proof.
  intros x1 x2 hx x3 x5.
  assert (H: from hx (to hx x3) = from hx (to hx x5)) by reflexivity.
  rewrite <- (eq_of_seq (from_to hx x3)).
  rewrite <- (eq_of_seq (from_to hx x5)).
  exact H.
Qed.

(* For SProp equality, we need a special isomorphism since x1 is Type but x2 is SProp *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* Since x2 : SProp, all elements of x1 are equal by sprop_iso_collapse *)
  (* So (x3 = x5) is always True, and imported_Corelib_Init_Logic_eq_Prop x4 x6 is also always True *)
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> eq in SProp *)
    intro Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    (* In SProp, all proofs are equal, so x4 = x6 definitionally *)
    apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: eq in SProp -> eq in Prop *)
    intro Heq.
    (* x3 = x5 because all elements of x1 collapse when x2 : SProp *)
    exact (@sprop_iso_collapse x1 x2 hx x3 x5).
  - (* to_from - SProp terms are definitionally equal *)
    intro Heq; apply IsomorphismDefinitions.eq_refl.
  - (* from_to - use Prop proof irrelevance *)
    intro Heq.
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.
