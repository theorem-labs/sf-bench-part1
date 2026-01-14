From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le____inversion__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le____inversion__iso.
From IsomorphismChecker Require Checker.U_true__iso Checker.U_corelib__U_init__U_logic__eq__iso Checker.and__iso Checker.ex__iso Checker.nat__iso Checker.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_leU_playground__le__iso Checker.U_s__iso Checker.or__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le____inversion__iso.Args := Checker.U_true__iso.Checker <+ Checker.U_corelib__U_init__U_logic__eq__iso.Checker <+ Checker.and__iso.Checker <+ Checker.ex__iso.Checker <+ Checker.nat__iso.Checker <+ Checker.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_leU_playground__le__iso.Checker <+ Checker.U_s__iso.Checker <+ Checker.or__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le____inversion__iso.Interface args
  with Definition imported_Original_LF__DOT__IndProp_LF_IndProp_le__inversion := Imported.Original_LF__DOT__IndProp_LF_IndProp_le__inversion.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_le__inversion := Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le____inversion__iso.imported_Original_LF__DOT__IndProp_LF_IndProp_le__inversion.
Definition Original_LF__DOT__IndProp_LF_IndProp_le__inversion_iso := Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le____inversion__iso.Original_LF__DOT__IndProp_LF_IndProp_le__inversion_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__IndProp_LF_IndProp_le__inversion_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.