From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop is for SProp-indexed equality *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop types, we use proof irrelevance *)
From Stdlib Require Import Logic.ProofIrrelevance.

(* Helper to extract Type equality from imported SProp equality *)
Definition imported_eq_Prop_to_eq {A : SProp} {x y : A} 
  (H : Imported.Corelib_Init_Logic_eq_Prop A x y) : IsomorphismDefinitions.eq x y :=
  match H with
  | Imported.Corelib_Init_Logic_eq_Prop_refl _ _ => IsomorphismDefinitions.eq_refl
  end.

(* The isomorphism between (x3 = x5) : Prop and imported_Corelib_Init_Logic_eq_Prop x4 x6 : SProp *)
(* Since one is Prop and one is SProp, we need to use SInhabited machinery *)

(* Key insight: If we have an Iso x1 x2 where x2 : SProp, then x1 must be 
   a type where all elements are equal (since SProp values are proof-irrelevant).
   This means for x3, x5 : x1, we have x3 = x5 iff the iso images are equal in SProp.
   But since SProp is proof-irrelevant, all inhabitants of SProp are equal.
   So if x1 has any two elements, they must be equal!
   
   Actually, this only holds when the iso exists - which means x1 and x2 are 
   isomorphic, and x2 is SProp (so all its inhabitants are equal).
   Therefore x1 must also have at most one element (up to equality).
*)

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 ->
  Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  - (* to: (x3 = x5) -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq.
    destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - (* from: imported_Corelib_Init_Logic_eq_Prop x4 x6 -> (x3 = x5) *)
    intro Hseq.
    destruct H34. destruct H56.
    (* Since x2 : SProp, all inhabitants of x2 are equal *)
    (* to hx x3 and to hx x5 are both in x2, hence equal in SProp *)
    (* This means from hx (to hx x3) = from hx (to hx x5) *)
    (* By from_to: x3 = from hx (to hx x3) and x5 = from hx (to hx x5) *)
    (* So x3 = x5 *)
    rewrite <- (from_to hx x3).
    rewrite <- (from_to hx x5).
    (* Now we need: from hx (to hx x3) = from hx (to hx x5) *)
    (* This follows from the fact that to hx x3 and to hx x5 are in SProp *)
    (* and SProp eliminates into Prop via the from_to proof *)
    reflexivity.
  - (* to_from *)
    intro Hseq. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    destruct H34. destruct H56. destruct Heq.
    apply seq_of_eq.
    apply proof_irrelevance.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
