From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__trans____example1SQUOTE__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__trans____example1SQUOTE__iso.
From IsomorphismChecker Require Checker.nat__iso Checker.U_nat__add__iso Checker.U_nat__mul__iso Checker.U_s__iso Checker.__0__iso Checker.le__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__trans____example1SQUOTE__iso.Args := Checker.nat__iso.Checker <+ Checker.U_nat__add__iso.Checker <+ Checker.U_nat__mul__iso.Checker <+ Checker.U_s__iso.Checker <+ Checker.__0__iso.Checker <+ Checker.le__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__trans____example1SQUOTE__iso.Interface args
  with Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1' := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1'.

Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1' := Isomorphisms.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__trans____example1SQUOTE__iso.imported_Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1'.
Definition Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1'_iso := Isomorphisms.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__trans____example1SQUOTE__iso.Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1'_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1'_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.