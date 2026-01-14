From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper lemma for proof irrelevance in SProp *)
Lemma prop_eq_proof_irrel_sprop {A : Type} {x y : A} (p q : x = y) : IsomorphismDefinitions.eq p q.
Proof.
  pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ p q) as H.
  destruct H. exact (IsomorphismDefinitions.eq_refl _).
Defined.

(* This is an isomorphism between Prop eq (when domain is Prop) and SProp eq *)
(* The source (x3 = x5) is in Prop, and the target is in SProp *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
   rel_iso hx x3 x4 ->
   forall (x5 : x1) (x6 : x2),
   rel_iso hx x5 x6 -> Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq. subst x5. apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> x3 = x5 *)
    intro Heq.
    (* Key insight: since x2 : SProp, all values of x2 are definitionally equal *)
    (* So to hx x3 = to hx x5 definitionally, hence from hx (to hx x3) = from hx (to hx x5) *)
    (* And by from_to, x3 = from hx (to hx x3) and x5 = from hx (to hx x5) *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    destruct Hft3. destruct Hft5.
    (* Now goal is: from hx (to hx x3) = from hx (to hx x5) *)
    (* Since x2 : SProp, to hx x3 = to hx x5 definitionally *)
    reflexivity.
  - (* to_from: for SProp, this is trivial *)
    intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to: use proof irrelevance for Prop equalities *)
    intro Heq.
    apply prop_eq_proof_irrel_sprop.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
