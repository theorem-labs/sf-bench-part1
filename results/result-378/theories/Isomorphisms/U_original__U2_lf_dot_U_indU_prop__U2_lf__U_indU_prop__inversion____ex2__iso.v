From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_inversion__ex2 : forall x : imported_nat,
  imported_Corelib_Init_Logic_eq (imported_S x) imported_0 ->
  imported_Corelib_Init_Logic_eq (imported_Nat_add (imported_S (imported_S imported_0)) (imported_S (imported_S imported_0)))
    (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))) := Imported.Original_LF__DOT__IndProp_LF_IndProp_inversion__ex2.
Instance Original_LF__DOT__IndProp_LF_IndProp_inversion__ex2_iso : forall (x1 : Datatypes.nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : Datatypes.S x1 = Datatypes.O) (x4 : imported_Corelib_Init_Logic_eq (imported_S x2) imported_0),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (S_iso hx) _0_iso;
      from := from (Corelib_Init_Logic_eq_iso (S_iso hx) _0_iso);
      to_from := fun x : imported_Corelib_Init_Logic_eq (imported_S x2) imported_0 => to_from (Corelib_Init_Logic_eq_iso (S_iso hx) _0_iso) x;
      from_to := fun x : Datatypes.S x1 = Datatypes.O => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (S_iso hx) _0_iso) x)
    |} x3 x4 ->
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))));
      from := from (Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))));
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq (imported_Nat_add (imported_S (imported_S imported_0)) (imported_S (imported_S imported_0)))
                (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))) =>
        to_from (Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))) x;
      from_to := fun x : Datatypes.S (Datatypes.S Datatypes.O) + Datatypes.S (Datatypes.S Datatypes.O) = Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S Datatypes.O)))) => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))) x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.inversion_ex2 x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_inversion__ex2 x4).
Admitted.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.inversion_ex2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_inversion__ex2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.inversion_ex2 Original_LF__DOT__IndProp_LF_IndProp_inversion__ex2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.inversion_ex2 Imported.Original_LF__DOT__IndProp_LF_IndProp_inversion__ex2 Original_LF__DOT__IndProp_LF_IndProp_inversion__ex2_iso := {}.