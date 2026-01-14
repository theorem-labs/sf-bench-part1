From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
From Stdlib.Logic Require Import ProofIrrelevance.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* We define imported_Corelib_Init_Logic_eq_Prop as the Imported version which is now in SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper: derive x3 = x5 from the isomorphism when x2 : SProp *)
Definition derive_eq_from_sprop {x1 : Type} {x2 : SProp} (hx : Iso x1 x2) 
    (x3 x5 : x1) : x3 = x5.
Proof.
  (* In SProp, to hx x3 and to hx x5 are definitionally equal *)
  (* So from hx (to hx x3) = from hx (to hx x5) definitionally *)
  (* And we have from_to : from (to x) = x *)
  pose proof (from_to hx x3) as H3.
  pose proof (from_to hx x5) as H5.
  (* Since to hx x3 and to hx x5 are in SProp x2, they're definitionally equal *)
  (* So from hx (to hx x3) = from hx (to hx x5) *)
  assert (Heq : from hx (to hx x3) = from hx (to hx x5)) by reflexivity.
  (* Now transport using H3 and H5 *)
  rewrite H3 in Heq.
  rewrite H5 in Heq.
  exact Heq.
Defined.

(* For SProp equality on SProp types *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 Hx34 x5 x6 Hx56.
  unfold imported_Corelib_Init_Logic_eq_Prop, rel_iso in *.
  (* x4 and x6 are both in x2 : SProp. 
     By definitional proof irrelevance in SProp, x4 = x6.
     Therefore Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 is inhabited by refl. *)
  apply Build_Iso with
    (to := fun (H : x3 = x5) => Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4)
    (from := fun _ => derive_eq_from_sprop hx x3 x5).
  - intro. apply IsomorphismDefinitions.eq_refl.
  - intro x. 
    (* Need to show: IsomorphismDefinitions.eq (derive_eq_from_sprop hx x3 x5) x *)
    (* Both are proofs of x3 = x5, which is a Prop. Use proof irrelevance lifted to SProp *)
    apply seq_of_peq_t.
    apply proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@imported_Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@imported_Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
