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

(* For Prop types, we need to handle the fact that the Iso target is SProp *)
(* The interface expects: Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6) *)
(* where x1 : Type, x2 : SProp, x3 x5 : x1, x4 x6 : x2 *)

(* Helper: if to hx x3 = x4 and to hx x5 = x6 (in SProp), and x3 = x5 (in Prop),
   then we can derive Corelib_Init_Logic_eq_Prop x4 x6.
   This is because x3 = x5 implies to hx x3 = to hx x5, 
   and combined with the relations we get x4 = x6. *)

Definition sprop_eq_to_prop_eq {A : Type} {x y : A} (H : IsomorphismDefinitions.eq x y) : x = y :=
  match H with IsomorphismDefinitions.eq_refl => Corelib.Init.Logic.eq_refl end.

Definition prop_eq_to_sprop_eq' {A : Type} {x y : A} (H : x = y) : IsomorphismDefinitions.eq x y :=
  match H with Corelib.Init.Logic.eq_refl => IsomorphismDefinitions.eq_refl end.

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), 
    rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> 
    Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 Hx34 x5 x6 Hx56.
  unfold imported_Corelib_Init_Logic_eq_Prop, rel_iso in *.
  unshelve eapply Build_Iso.
  - (* to: (x3 = x5) -> Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 *)
    intro H. destruct H.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  - (* from: Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 -> (x3 = x5) *)
    intro H.
    pose proof (sprop_eq_to_prop_eq (from_to hx x3)) as Hrt3.
    pose proof (sprop_eq_to_prop_eq (from_to hx x5)) as Hrt5.
    transitivity (from hx (to hx x3)).
    + symmetry. exact Hrt3.
    + exact Hrt5.
  - intro x. apply IsomorphismDefinitions.eq_refl.
  - intro x.
    (* Need: eq (from_proof (to_proof x)) x where both are proofs of x3 = x5 *)
    (* Use proof irrelevance lifted to SProp *)
    apply seq_of_eq.
    apply proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@imported_Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@imported_Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
