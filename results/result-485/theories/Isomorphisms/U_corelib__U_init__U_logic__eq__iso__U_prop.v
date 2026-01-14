From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* For SProp types, equality is trivial since all SProp values are definitionally equal *)
(* We need Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp *)

(* Define imported_Corelib_Init_Logic_eq_Prop - the checker expects this to equal Imported.Corelib_Init_Logic_eq_Prop *)
(* We define it to match what the checker expects *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall (x : SProp), x -> x -> SProp :=
  @Imported.Corelib_Init_Logic_eq_Prop.

(* The isomorphism between Coq equality on elements of a Type that maps to SProp
   and the imported SProp equality *)
Instance Corelib_Init_Logic_eq_iso_Prop : 
  forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) 
         (x3 : x1) (x4 : x2) (_ : rel_iso hx x3 x4) 
         (x5 : x1) (x6 : x2) (_ : rel_iso hx x5 x6),
  Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unshelve eapply Build_Iso.
  - (* to : x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    (* In SProp, all elements are equal, so we just need eq_refl *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - (* from : imported_Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5 *)
    intro Hseq.
    (* x4 and x6 are elements of x2 : SProp, so we need to derive x3 = x5 *)
    (* Since x2 is SProp, all elements of x2 are definitionally equal *)
    (* Therefore to hx x3 = to hx x5 (definitionally in SProp) *)
    (* We use from_to to conclude *)
    rewrite <- (from_to hx x3).
    rewrite <- (from_to hx x5).
    (* Now both sides use from hx (to hx _), and since x2 is SProp,
       to hx x3 = to hx x5 definitionally *)
    reflexivity.
  - (* to_from *)
    intro s. reflexivity.
  - (* from_to *)
    intro e.
    apply seq_of_eq.
    (* Use proof irrelevance for equality proofs *)
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
