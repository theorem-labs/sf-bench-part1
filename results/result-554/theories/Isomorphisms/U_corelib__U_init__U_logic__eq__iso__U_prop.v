From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop/SProp arguments, both the domain and codomain are in the "propositional"
   universe. We can build an isomorphism using proof that:
   - (x3 = x5) is a Prop
   - imported_Corelib_Init_Logic_eq_Prop x4 x6 is SProp
   Both are essentially the same logical content, so we use iso_of_rel_iso_iso_sort_PropSProp_P *)

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  (* Now x4 = to hx x3 and x6 = to hx x5 *)
  (* Goal: Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5)) *)
  
  (* Build the isomorphism directly *)
  unshelve eapply Build_Iso.
  - (* to: (x3 = x5) -> imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq. subst x5.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ (to hx x3)).
  - (* from: imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> (x3 = x5) *)
    intro Heq.
    (* Use from_to to show injectivity of 'to' *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    destruct Hft3. destruct Hft5.
    reflexivity.
  - (* to_from: this is in SProp, so definitionally equal *)
    intro x. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to: use proof irrelevance for Prop equalities *)
    intro x.
    set (lhs := (let Hft3 := from_to hx x3 in
                 let Hft5 := from_to hx x5 in
                 match Hft3 in (IsomorphismDefinitions.eq _ y) return (y = x5) with
                 | IsomorphismDefinitions.eq_refl =>
                     match Hft5 in (IsomorphismDefinitions.eq _ z) return (from hx (to hx x3) = z) with
                     | IsomorphismDefinitions.eq_refl => Logic.eq_refl
                     end
                 end)).
    pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance (x3 = x5) lhs x) as H.
    destruct H. exact (IsomorphismDefinitions.eq_refl _).
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
