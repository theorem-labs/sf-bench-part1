From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For SProp, equality proofs are always trivially equal *)
(* This isomorphism is between (x3 = x5) : Prop and (imported_Corelib_Init_Logic_eq_Prop x4 x6) : SProp *)
(* where x1 : Type, x2 : SProp, and x3, x5 : x1, x4, x6 : x2 *)
(* The key insight: Since x2 is SProp, any two values x4 x6 : x2 are indistinguishable. *)
(* Therefore, `from hx` applied to any SProp value gives the same result. *)
(* So x3 = from hx x4 = from hx x6 = x5. This makes (x3 = x5) provable. *)

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  (* Now we need: Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5)) *)
  (* Since x2 : SProp, (to hx x3) and (to hx x5) are indistinguishable in x2 *)
  (* Hence from hx (to hx x3) = from hx (to hx x5) definitionally *)
  (* Combined with from_to, x3 = from hx (to hx x3) = from hx (to hx x5) = x5 *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq. subst x5. exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 (to hx x3)).
  - (* from: imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> x3 = x5 *)
    intro H.
    (* Use from_to to connect x3 and x5 via from hx *)
    (* from_to hx x3 : eq (from hx (to hx x3)) x3 (SProp eq) *)
    (* from_to hx x5 : eq (from hx (to hx x5)) x5 (SProp eq) *)
    (* Convert to Prop eq using eq_of_seq *)
    pose proof (eq_of_seq (from_to hx x3)) as H3. (* from hx (to hx x3) = x3 *)
    pose proof (eq_of_seq (from_to hx x5)) as H5. (* from hx (to hx x5) = x5 *)
    (* Since (to hx x3) and (to hx x5) are in x2 : SProp, they are definitionally equal *)
    (* So from hx (to hx x3) = from hx (to hx x5) definitionally *)
    (* Thus: x3 = from hx (to hx x3) = from hx (to hx x5) = x5 *)
    rewrite <- H3. rewrite <- H5.
    exact Corelib.Init.Logic.eq_refl.
  - (* to_from: in SProp, trivially equal *)
    intro H. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to: proof irrelevance for Prop eq *)
    intro Heq.
    (* Use proof irrelevance: any two proofs of x3 = x5 are equal *)
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
