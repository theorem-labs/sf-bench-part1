From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
From Stdlib.Logic Require Import ProofIrrelevance.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* We define imported_Corelib_Init_Logic_eq_Prop as the Imported version which is in SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := 
  fun x a b => Imported.Corelib_Init_Logic_eq_Prop x a b.

(* For Prop types, build the isomorphism directly *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 Hx34 x5 x6 Hx56.
  unfold imported_Corelib_Init_Logic_eq_Prop, rel_iso in *.
  unshelve eapply Build_Iso.
  - (* to *)
    intro H. destruct H.
    exact (match eq_trans (eq_sym Hx34) Hx56 in IsomorphismDefinitions.eq _ z 
           return Imported.Corelib_Init_Logic_eq_Prop x2 x4 z with
           | IsomorphismDefinitions.eq_refl => Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4
           end).
  - (* from *)
    intro H. destruct H.
    (* Now x4 = x6, and we have Hx34: to hx x3 ≡ x4 and Hx56: to hx x5 ≡ x4 *)
    pose proof (from_to_tseq hx x3) as H3.
    pose proof (from_to_tseq hx x5) as H5.
    rewrite <- H3, <- H5.
    (* Goal: from hx (to hx x3) = from hx (to hx x5) *)
    (* In SProp, all elements are equal, so to hx x3 and to hx x5 are definitionally equal *)
    reflexivity.
  - intro. apply IsomorphismDefinitions.eq_refl.
  - intro x. apply seq_of_eq. apply proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@imported_Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@imported_Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
