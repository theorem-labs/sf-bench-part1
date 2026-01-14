From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* For SProp-based equality, both sides are in SProp, so everything is trivial *)
(* The imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp *)

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := 
  @Imported.Corelib_Init_Logic_eq_Prop.

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  (* We need Iso (x3 = x5) (Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6) *)
  (* Both are SProp, so we use SProp-level proof irrelevance *)
  apply Build_Iso with
    (to := fun _ => Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4)
    (from := fun _ => 
      (* We need to show x3 = x5 given that both map to SProp elements *)
      (* Use that hx is an iso between x1 and SProp x2 *)
      (* from_to hx x3 : from(to(x3)) = x3, from_to hx x5 : from(to(x5)) = x5 *)
      (* Since x2 is SProp, to(x3) = to(x5) definitionally in SProp *)
      (* Therefore from(to(x3)) = from(to(x5)) *)
      (* Combined with from_to, we get x3 = x5 *)
      let ft3 := from_to hx x3 in
      let ft5 := from_to hx x5 in
      eq_of_seq (eq_trans (eq_sym ft3) ft5)).
  - intro x; apply IsomorphismDefinitions.eq_refl.
  - intro x; apply sUIPt.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) imported_Corelib_Init_Logic_eq_Prop Corelib_Init_Logic_eq_iso_Prop := {}.
