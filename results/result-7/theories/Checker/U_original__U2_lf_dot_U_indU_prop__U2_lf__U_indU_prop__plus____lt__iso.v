From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__plus____lt__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__plus____lt__iso.
From IsomorphismChecker Require Checker.and__iso Checker.nat__iso Checker.U_nat__add__iso Checker.lt__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__plus____lt__iso.Args := Checker.and__iso.Checker <+ Checker.nat__iso.Checker <+ Checker.U_nat__add__iso.Checker <+ Checker.lt__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__plus____lt__iso.imported_Original_LF__DOT__IndProp_LF_IndProp_plus__lt Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__plus____lt__iso.Original_LF__DOT__IndProp_LF_IndProp_plus__lt_iso ].

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__plus____lt__iso.Interface args
  with Definition imported_Original_LF__DOT__IndProp_LF_IndProp_plus__lt := Imported.Original_LF__DOT__IndProp_LF_IndProp_plus__lt.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_plus__lt := Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__plus____lt__iso.imported_Original_LF__DOT__IndProp_LF_IndProp_plus__lt.
Definition Original_LF__DOT__IndProp_LF_IndProp_plus__lt_iso := Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__plus____lt__iso.Original_LF__DOT__IndProp_LF_IndProp_plus__lt_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__IndProp_LF_IndProp_plus__lt_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.