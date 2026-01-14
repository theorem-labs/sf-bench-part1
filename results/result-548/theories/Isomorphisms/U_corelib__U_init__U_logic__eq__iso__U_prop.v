From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib.Logic Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* For Prop types (which become SProp after import), we need a version that works with SProp directly. *)

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp :=
  (@Imported.Corelib_Init_Logic_eq_Prop).

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
    rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unfold rel_iso in *.
  simpl in *.
  
  (* Since x4 and x6 are in SProp x2, they are definitionally equal *)
  (* So Corelib_Init_Logic_eq_Prop x2 x4 x6 is the same as Corelib_Init_Logic_eq_Prop x2 x4 x4 *)
  (* which is inhabited by refl *)
  
  assert (from_proof : x3 = x5).
  { pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    apply eq_of_seq in Hft3.
    apply eq_of_seq in Hft5.
    rewrite <- Hft3, <- Hft5.
    reflexivity. (* to x3 and to x5 are in SProp x2, so definitionally equal *) }
  
  refine {|
    to := fun e => Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4;
    from := fun e => from_proof;
    to_from := _;
    from_to := _
  |}.
  - intros e. apply IsomorphismDefinitions.eq_refl.
  - intros e. apply seq_of_eq. apply proof_irrelevance.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
