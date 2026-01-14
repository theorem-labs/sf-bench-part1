From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq.

Definition to_fn (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (Hx34 : eq (hx x3) x4) 
    (x5 : x1) (x6 : x2) (Hx56 : eq (hx x5) x6) 
    (H : x3 = x5) : Imported.Corelib_Init_Logic_eq x2 x4 x6.
Proof.
  subst x5.
  pose proof (Imported.Corelib_Init_Logic_eq_refl x2 (hx x3)) as base.
  pose proof (@IsomorphismDefinitions.eq_sind x2 (hx x3) (fun y _ => Imported.Corelib_Init_Logic_eq x2 y (hx x3)) base x4 Hx34) as step1.
  exact (@IsomorphismDefinitions.eq_sind x2 (hx x3) (fun y _ => Imported.Corelib_Init_Logic_eq x2 x4 y) step1 x6 Hx56).
Defined.

Definition from_fn (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (Hx34 : eq (hx x3) x4) 
    (x5 : x1) (x6 : x2) (Hx56 : eq (hx x5) x6) 
    (H : Imported.Corelib_Init_Logic_eq x2 x4 x6) : x3 = x5.
Proof.
  destruct H.
  pose proof (from_to hx x3) as ft3.
  pose proof (from_to hx x5) as ft5.
  apply eq_of_seq in ft3.
  apply eq_of_seq in ft5.
  apply eq_of_seq in Hx34.
  apply eq_of_seq in Hx56.
  rewrite <- ft3. rewrite <- ft5.
  f_equal.
  transitivity x4; [exact Hx34 | symmetry; exact Hx56].
Defined.

Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 Hx34 x5 x6 Hx56.
  unfold imported_Corelib_Init_Logic_eq, rel_iso in *.
  refine (Build_Iso
    (@to_fn x1 x2 hx x3 x4 Hx34 x5 x6 Hx56)
    (@from_fn x1 x2 hx x3 x4 Hx34 x5 x6 Hx56)
    _ _).
  intro x. exact IsomorphismDefinitions.eq_refl.
  intro x. apply sUIPt.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.
