From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_logic__not__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_disc__example := Imported.Original_LF__DOT__Logic_LF_Logic_disc__example.

(* The imported function has type: forall n : Imported.nat, Imported.Logic_not (Imported.Corelib_Init_Logic_eq Imported.nat Imported.nat_O (Imported.nat_S n))
   which is: forall n : Imported.nat, Imported.Corelib_Init_Logic_eq Imported.nat Imported.nat_O (Imported.nat_S n) -> Imported.MyFalse *)

Instance Original_LF__DOT__Logic_LF_Logic_disc__example_iso : forall (x1 : Datatypes.nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : Datatypes.O = Datatypes.S x1) (x4 : imported_Corelib_Init_Logic_eq imported_0 (imported_S x2)),
  rel_iso (Corelib_Init_Logic_eq_iso _0_iso (S_iso hx)) x3 x4 -> rel_iso False_iso (Original.LF_DOT_Logic.LF.Logic.disc_example x1 x3) (@imported_Original_LF__DOT__Logic_LF_Logic_disc__example x2 x4).
Proof.
  intros x1 x2 hx x3 x4 hx0.
  discriminate x3.
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.disc_example := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_disc__example := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.disc_example Original_LF__DOT__Logic_LF_Logic_disc__example_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.disc_example Imported.Original_LF__DOT__Logic_LF_Logic_disc__example Original_LF__DOT__Logic_LF_Logic_disc__example_iso := {}.
