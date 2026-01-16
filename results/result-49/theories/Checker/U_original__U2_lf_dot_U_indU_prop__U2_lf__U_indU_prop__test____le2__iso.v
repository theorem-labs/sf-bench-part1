From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____le2__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____le2__iso.
From IsomorphismChecker Require Checker.nat__iso Checker.U_s__iso Checker.__0__iso Checker.le__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____le2__iso.Args := Checker.nat__iso.Checker <+ Checker.U_s__iso.Checker <+ Checker.__0__iso.Checker <+ Checker.le__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____le2__iso.imported_Original_LF__DOT__IndProp_LF_IndProp_test__le2 Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____le2__iso.Original_LF__DOT__IndProp_LF_IndProp_test__le2_iso ].

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____le2__iso.Interface args
  with Definition imported_Original_LF__DOT__IndProp_LF_IndProp_test__le2 := Imported.Original_LF__DOT__IndProp_LF_IndProp_test__le2.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_test__le2 := Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____le2__iso.imported_Original_LF__DOT__IndProp_LF_IndProp_test__le2.
Definition Original_LF__DOT__IndProp_LF_IndProp_test__le2_iso := Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____le2__iso.Original_LF__DOT__IndProp_LF_IndProp_test__le2_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__IndProp_LF_IndProp_test__le2_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.