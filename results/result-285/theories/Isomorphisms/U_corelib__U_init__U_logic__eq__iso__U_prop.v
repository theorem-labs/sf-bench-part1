From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* For Prop arguments, we need a different version of eq *)
(* The imported Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp *)

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := 
  Imported.Corelib_Init_Logic_eq_Prop.

(* Helper: proof irrelevance for Prop eq expressed in SProp eq *)
Lemma prop_eq_proof_irrel_local {A : Type} {x y : A} (p q : x = y) : IsomorphismDefinitions.eq p q.
Proof.
  pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ p q) as H.
  destruct H. exact (IsomorphismDefinitions.eq_refl _).
Defined.

(* Iso between Prop eq (at sort Prop) and SProp eq *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* Since x2 is SProp, the elements are proof-irrelevant *)
  (* In SProp, all values of the same type are equal, so x4 = x6 automatically *)
  (* So imported_Corelib_Init_Logic_eq_Prop x4 x6 is always inhabited by refl *)
  destruct H34. destruct H56.
  (* Now x4 = to hx x3 and x6 = to hx x5 *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 (to hx x3)).
  - (* from: imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> x3 = x5 *)
    intro Heq.
    (* to hx x3 and to hx x5 are both in x2 : SProp, so they're definitionally equal *)
    (* Use from_to: from hx (to hx x3) = x3, from hx (to hx x5) = x5 *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    destruct Hft3. destruct Hft5.
    (* Now goal is from hx (to hx x3) = from hx (to hx x5) *)
    (* Since to hx x3 and to hx x5 are both in x2 : SProp, they're equal *)
    reflexivity.
  - (* to_from *)
    intro x. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to *)
    intro x.
    apply prop_eq_proof_irrel_local.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) imported_Corelib_Init_Logic_eq_Prop Corelib_Init_Logic_eq_iso_Prop := {}.
