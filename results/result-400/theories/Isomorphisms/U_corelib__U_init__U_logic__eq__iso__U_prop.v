From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper: proof irrelevance for Prop eq expressed in SProp eq *)
Lemma prop_eq_proof_irrel_local {A : Type} {x y : A} (p q : x = y) : IsomorphismDefinitions.eq p q.
Proof.
  pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ p q) as H.
  destruct H. exact (IsomorphismDefinitions.eq_refl _).
Defined.

(* Iso between Prop eq (with Prop/SProp arguments) and SProp eq *)
(* When x1 : Type and x2 : SProp have an iso, x3 = x5 in x1 should be iso to 
   imported_Corelib_Init_Logic_eq_Prop in x2. Since all values in SProp are proof
   irrelevant, both sides are either inhabited or not, so we can build an iso. *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq. subst x5. apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> x3 = x5 *)
    intro Heq.
    (* We need to convert from SProp equality to Prop equality *)
    (* Use from_to to get the relationship between from (to x) and x *)
    pose proof (from_to_tseq hx x3) as Hft3.
    pose proof (from_to_tseq hx x5) as Hft5.
    (* Use recl to extract equality info from SProp eq *)
    pose proof (Imported.Corelib_Init_Logic_eq_Prop_recl x2 (hx x3) (fun z _ => from hx (hx x3) = from hx z) Logic.eq_refl (hx x5) Heq) as H.
    (* Now H : from hx (hx x3) = from hx (hx x5) *)
    (* Use from_to to rewrite *)
    rewrite Hft3 in H. rewrite Hft5 in H. exact H.
  - (* to_from *)
    intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to *)
    intro Heq.
    (* Both sides are proofs of x3 = x5, use proof irrelevance *)
    apply prop_eq_proof_irrel_local.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
