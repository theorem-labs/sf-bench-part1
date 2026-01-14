From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop is for SProp equality: forall A : SProp, A -> A -> SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For equality at Prop/SProp level: we directly construct the isomorphism *)

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  (* We need to show Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6) *)
  unshelve eapply Build_Iso.
  + (* to: (x3 = x5) -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq.
    destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  + (* from: imported_Corelib_Init_Logic_eq_Prop x4 x6 -> (x3 = x5) *)
    intro Hseq.
    destruct H34. destruct H56.
    (* Now: Hseq : imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    destruct Hseq.
    (* After destruct Hseq, (to hx x3) and (to hx x5) are unified in SProp *)
    (* But goal x3 = x5 uses Logic.eq (renamed to Lean.eq in this context) *)
    (* Use the roundtrip property: x3 = from hx (to hx x3) = from hx (to hx x5) = x5 *)
    (* Since to hx x3 = to hx x5 after destruct, we need from hx applied to both *)
    exact (Logic.eq_trans 
             (Logic.eq_sym (IsoEq.eq_of_seq (from_to hx x3)))
             (IsoEq.eq_of_seq (from_to hx x5))).
  + intro. apply IsomorphismDefinitions.eq_refl.
  + intro Heq.
    (* The goal is an SProp equality: eq (from (to Heq)) Heq *)
    (* Since both sides are in Prop (x3 = x5), use proof irrelevance *)
    apply seq_of_peq_t.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
