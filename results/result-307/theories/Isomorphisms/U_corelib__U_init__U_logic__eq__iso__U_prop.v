From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Corelib_Init_Logic_eq_Prop in Imported is in SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Forward map *)
Definition eq_forward_Prop (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) 
  (Hx34 : IsomorphismDefinitions.eq (to hx x3) x4) (x5 : x1) (x6 : x2)
  (Hx56 : IsomorphismDefinitions.eq (to hx x5) x6) 
  (pf : x3 = x5) : Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 :=
  eq_srect (fun z => Imported.Corelib_Init_Logic_eq_Prop x2 x4 z) 
    (eq_srect (fun z => Imported.Corelib_Init_Logic_eq_Prop x2 z (to hx x5))
      (match pf in (_ = z) return Imported.Corelib_Init_Logic_eq_Prop x2 (to hx x3) (to hx z) with
       | Logic.eq_refl => Imported.Corelib_Init_Logic_eq_Prop_refl x2 (to hx x3)
       end)
      Hx34)
    Hx56.

(* Backward map *)
Definition eq_backward_Prop (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) 
  (Hx34 : IsomorphismDefinitions.eq (to hx x3) x4) (x5 : x1) (x6 : x2)
  (Hx56 : IsomorphismDefinitions.eq (to hx x5) x6)
  (pf : Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6) : x3 = x5.
Proof.
  pose (H34' := eq_srect (fun z => IsomorphismDefinitions.eq (from hx z) x3) (from_to hx x3) Hx34).
  pose (H56' := eq_srect (fun z => IsomorphismDefinitions.eq (from hx z) x5) (from_to hx x5) Hx56).
  destruct pf.
  pose (step1 := eq_srect (fun z => from hx x4 = z) Logic.eq_refl H56').
  exact (eq_srect (fun z => z = x5) step1 H34').
Defined.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 Hx34 x5 x6 Hx56.
  unfold rel_iso in *.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  exact (Build_Iso 
    (@eq_forward_Prop x1 x2 hx x3 x4 Hx34 x5 x6 Hx56) 
    (@eq_backward_Prop x1 x2 hx x3 x4 Hx34 x5 x6 Hx56)
    (fun _ => IsomorphismDefinitions.eq_refl)
    (fun e => sUIPt _ e)).
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
