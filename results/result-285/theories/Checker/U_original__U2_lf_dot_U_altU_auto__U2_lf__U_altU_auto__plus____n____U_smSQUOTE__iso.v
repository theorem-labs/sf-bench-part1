From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__plus____n____U_smSQUOTE__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__plus____n____U_smSQUOTE__iso.
From IsomorphismChecker Require Checker.U_true__iso Checker.U_corelib__U_init__U_logic__eq__iso Checker.nat__iso Checker.U_nat__add__iso Checker.U_s__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__plus____n____U_smSQUOTE__iso.Args := Checker.U_true__iso.Checker <+ Checker.U_corelib__U_init__U_logic__eq__iso.Checker <+ Checker.nat__iso.Checker <+ Checker.U_nat__add__iso.Checker <+ Checker.U_s__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__plus____n____U_smSQUOTE__iso.Interface args
  with Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_plus__n__Sm' := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_plus__n__Sm'.

Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_plus__n__Sm' := Isomorphisms.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__plus____n____U_smSQUOTE__iso.imported_Original_LF__DOT__AltAuto_LF_AltAuto_plus__n__Sm'.
Definition Original_LF__DOT__AltAuto_LF_AltAuto_plus__n__Sm'_iso := Isomorphisms.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__plus____n____U_smSQUOTE__iso.Original_LF__DOT__AltAuto_LF_AltAuto_plus__n__Sm'_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__AltAuto_LF_AltAuto_plus__n__Sm'_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.