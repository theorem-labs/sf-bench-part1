From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_o____le____n__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_o____le____n__iso.
From IsomorphismChecker Require Checker.nat__iso Checker.__0__iso Checker.le__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_o____le____n__iso.Args := Checker.nat__iso.Checker <+ Checker.__0__iso.Checker <+ Checker.le__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_o____le____n__iso.imported_Original_LF__DOT__IndProp_LF_IndProp_O__le__n Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_o____le____n__iso.Original_LF__DOT__IndProp_LF_IndProp_O__le__n_iso ].

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_o____le____n__iso.Interface args
  with Definition imported_Original_LF__DOT__IndProp_LF_IndProp_O__le__n := Imported.Original_LF__DOT__IndProp_LF_IndProp_O__le__n.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_O__le__n := Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_o____le____n__iso.imported_Original_LF__DOT__IndProp_LF_IndProp_O__le__n.
Definition Original_LF__DOT__IndProp_LF_IndProp_O__le__n_iso := Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_o____le____n__iso.Original_LF__DOT__IndProp_LF_IndProp_O__le__n_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__IndProp_LF_IndProp_O__le__n_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.