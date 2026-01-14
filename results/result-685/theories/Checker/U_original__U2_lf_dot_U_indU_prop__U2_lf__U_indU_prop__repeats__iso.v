From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__repeats__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__repeats__iso.
From IsomorphismChecker Require Checker.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__repeats__iso.Args := Checker.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Args <+ Checker.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__repeats__iso.Interface args
  with Definition imported_Original_LF__DOT__IndProp_LF_IndProp_repeats := (@Imported.Original_LF__DOT__IndProp_LF_IndProp_repeats).

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_repeats := Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__repeats__iso.imported_Original_LF__DOT__IndProp_LF_IndProp_repeats.
Definition Original_LF__DOT__IndProp_LF_IndProp_repeats_iso := Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__repeats__iso.Original_LF__DOT__IndProp_LF_IndProp_repeats_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__IndProp_LF_IndProp_repeats_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.