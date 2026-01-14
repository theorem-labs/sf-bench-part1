From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper: proof irrelevance for Prop eq expressed in SProp eq *)
Lemma prop_eq_proof_irrel' {A : Type} {x y : A} (p q : x = y) : IsomorphismDefinitions.eq p q.
Proof.
  pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ p q) as H.
  destruct H. exact (IsomorphismDefinitions.eq_refl _).
Defined.

(* Isomorphism for eq on SProp types *)
(* When hx : Iso x1 x2 with x2 : SProp, then x4 and x6 are in SProp so definitionally equal *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* Destruct H34 and H56 first to simplify *)
  destruct H34. destruct H56.
  (* Now x4 = to hx x3 and x6 = to hx x5 (both in SProp x2) *)
  (* Goal: Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5)) *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq. subst x5. apply Imported.Corelib_Init_Logic_eq_Prop_refl0.
  - (* from: imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> x3 = x5 *)
    intro Heq.
    (* We know from_to hx x3 : x3 = from (to hx x3) and similarly for x5 *)
    (* Since x2 is SProp, to hx x3 and to hx x5 are definitionally equal *)
    (* So from hx (to hx x3) = from hx (to hx x5) definitionally *)
    (* Using roundtrip: x3 = from (to hx x3) = from (to hx x5) = x5 *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    destruct Hft3.
    destruct Hft5.
    (* Now x3 = from hx (to hx x3) and x5 = from hx (to hx x5) *)
    (* And to hx x3 =_SProp to hx x5 (definitionally in SProp) *)
    (* So from hx (to hx x3) =_SProp from hx (to hx x5) *)
    reflexivity.
  - (* to_from: for SProp, all proofs are equal *)
    intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to *)
    intro Heq.
    apply prop_eq_proof_irrel'.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
