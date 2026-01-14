From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* For SProp variant - required by Interface *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := Imported.Corelib_Init_Logic_eq_Prop.

(* Helper to convert IsomorphismDefinitions.eq to Logic.eq *)
Lemma iso_eq_to_eq : forall (A : Type) (x y : A), IsomorphismDefinitions.eq x y -> x = y.
Proof. intros A x y H. destruct H. reflexivity. Qed.

(* Use proof irrelevance to handle all equality proofs *)
Lemma eq_proofs_equal : forall (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intros A x y p q.
  apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Qed.

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unfold rel_iso in H34, H56.
  destruct H34. destruct H56.
  (* Since x2 : SProp, (to hx x3) and (to hx x5) are definitionally equal in SProp *)
  (* Hence from hx (to hx x3) = from hx (to hx x5) *)
  assert (Heq : x3 = x5).
  { 
    pose proof (from_to hx x3) as H1.
    pose proof (from_to hx x5) as H2.
    apply iso_eq_to_eq in H1. apply iso_eq_to_eq in H2.
    rewrite <- H1. rewrite <- H2.
    reflexivity. (* Works because x2 : SProp makes to hx x3 = to hx x5 definitionally *)
  }
  rewrite Heq.
  unshelve eapply Build_Iso.
  { intro H. exact (Imported.Corelib_Init_Logic_eq_refl_Prop x2 (to hx x5)). }
  { intro H. reflexivity. }
  { intro H. apply IsomorphismDefinitions.eq_refl. }
  { intro H.
    (* Need: eq eq_refl H where H : x5 = x5 *)
    (* Use proof irrelevance: all proofs of x5 = x5 are equal *)
    rewrite (@eq_proofs_equal x1 x5 x5 Logic.eq_refl H).
    apply IsomorphismDefinitions.eq_refl. }
Defined.

Instance: KnownConstant imported_Corelib_Init_Logic_eq_Prop := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) imported_Corelib_Init_Logic_eq_Prop Corelib_Init_Logic_eq_iso_Prop := {}.
