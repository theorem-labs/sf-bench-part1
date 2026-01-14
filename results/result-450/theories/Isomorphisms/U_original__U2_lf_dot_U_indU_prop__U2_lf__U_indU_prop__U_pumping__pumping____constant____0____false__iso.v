From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_pumping__pumping____constant__iso Isomorphisms.__0__iso Isomorphisms.U_original__U_false__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__0__false : forall (x : Type) (x0 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x),
  imported_Corelib_Init_Logic_eq (@imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant x x0) imported_0 -> imported_Original_False := Imported.Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__0__false.
Instance Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__0__false_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1) (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x2)
    (hx0 : rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) x3 x4) (x5 : Original.LF_DOT_IndProp.LF.IndProp.Pumping.pumping_constant x3 = Datatypes.O)
    (x6 : imported_Corelib_Init_Logic_eq (@imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant x2 x4) imported_0),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant_iso hx0) _0_iso;
      from := from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant_iso hx0) _0_iso);
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (@imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant x2 x4) imported_0 =>
        to_from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant_iso hx0) _0_iso) x;
      from_to :=
        fun x : Original.LF_DOT_IndProp.LF.IndProp.Pumping.pumping_constant x3 = Datatypes.O =>
        seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant_iso hx0) _0_iso) x)
    |} x5 x6 ->
  rel_iso
    {|
      to := Original_False_iso;
      from := from Original_False_iso;
      to_from := fun x : imported_Original_False => to_from Original_False_iso x;
      from_to := fun x : Original.False => seq_p_of_t (from_to Original_False_iso x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.Pumping.pumping_constant_0_false x1 x3 x5) (@imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__0__false x2 x4 x6).
Admitted.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.Pumping.pumping_constant_0_false := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__0__false := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.Pumping.pumping_constant_0_false Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__0__false_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.Pumping.pumping_constant_0_false Imported.Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__0__false Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__0__false_iso := {}.