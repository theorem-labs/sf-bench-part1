From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq.

Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 Hx34 x5 x6 Hx56.
  unfold imported_Corelib_Init_Logic_eq, rel_iso in *.
  
  (* to_fn: (x3 = x5) -> Imported.Corelib_Init_Logic_eq x2 x4 x6 *)
  pose (to_fn := fun (H : x3 = x5) =>
    eq_srect (fun y => Imported.Corelib_Init_Logic_eq x2 x4 y)
      (eq_srect (fun y => Imported.Corelib_Init_Logic_eq x2 y (hx x5))
        (match H in (_ = z) return Imported.Corelib_Init_Logic_eq x2 (hx x3) (hx z) with
         | Logic.eq_refl => Imported.Corelib_Init_Logic_eq_refl x2 (hx x3)
         end)
        Hx34)
      Hx56).
  
  (* eq1: from hx x4 = x3 *)
  pose (eq1_helper := f_equal (from hx) Hx34).
  pose (eq1 := eq_of_seq (eq_trans (eq_sym eq1_helper) (from_to hx x3))).
  
  (* eq2: from hx x6 = x5 *)
  pose (eq2_helper := f_equal (from hx) Hx56).
  pose (eq2 := eq_of_seq (eq_trans (eq_sym eq2_helper) (from_to hx x5))).
  
  (* from_fn: Imported.Corelib_Init_Logic_eq x2 x4 x6 -> (x3 = x5) *)
  pose (from_fn := fun (H : Imported.Corelib_Init_Logic_eq x2 x4 x6) =>
    let H' : from hx x4 = from hx x6 := 
      match H in Imported.Corelib_Init_Logic_eq _ _ b return from hx x4 = from hx b with
      | Imported.Corelib_Init_Logic_eq_refl _ _ => Logic.eq_refl
      end
    in
    Logic.eq_trans (Logic.eq_sym eq1) (Logic.eq_trans H' eq2)).
  
  refine (@Build_Iso (x3 = x5) (Imported.Corelib_Init_Logic_eq x2 x4 x6) 
           to_fn from_fn _ _).
  (* to_from *)
  intro x. exact IsomorphismDefinitions.eq_refl.
  (* from_to *)
  intro x. exact (sUIPt _ _).
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.
