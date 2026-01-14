From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Local copy of proof irrelevance lemma *)
Local Lemma prop_eq_proof_irrel {A : Type} {x y : A} (p q : x = y) : IsomorphismDefinitions.eq p q.
Proof.
  pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ p q) as H.
  destruct H. exact (IsomorphismDefinitions.eq_refl _).
Defined.

(* Isomorphism for eq at Prop/SProp level *)
(* When the first type argument is a Prop (maps to SProp), we need this version *)
(* Since x2 : SProp, all inhabitants of x2 are definitionally equal (SProp proof irrelevance) *)
(* So both (x3 = x5 : Prop) and (imported_Corelib_Init_Logic_eq_Prop x4 x6 : SProp) are singletons *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  (* Since x2 is SProp, (to hx x3) and (to hx x5) are equal by SProp proof irrelevance *)
  (* So imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) is inhabited *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> Imported.Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq. apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: Imported.Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> x3 = x5 *)
    intro Heq.
    (* Use proof irrelevance for Props *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    destruct Hft3. destruct Hft5.
    (* x3 and x5 are both in x1, and from hx (to hx xi) = xi *)
    (* Since x2 : SProp, (to hx x3) = (to hx x5) definitionally *)
    (* Therefore from hx (to hx x3) = from hx (to hx x5) *)
    exact (Corelib.Init.Logic.eq_refl _).
  - (* to_from *)
    intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to *)
    intro Heq.
    apply prop_eq_proof_irrel.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
