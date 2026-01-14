From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__four____is____U_even__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__four____is____U_even__iso.
From IsomorphismChecker Require Checker.nat__iso Checker.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso Checker.U_s__iso Checker.__0__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__four____is____U_even__iso.Args := Checker.nat__iso.Checker <+ Checker.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso.Checker <+ Checker.U_s__iso.Checker <+ Checker.__0__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__four____is____U_even__iso.Interface args
  with Definition imported_Original_LF__DOT__Logic_LF_Logic_four__is__Even := Imported.Original_LF__DOT__Logic_LF_Logic_four__is__Even.

Definition imported_Original_LF__DOT__Logic_LF_Logic_four__is__Even := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__four____is____U_even__iso.imported_Original_LF__DOT__Logic_LF_Logic_four__is__Even.
Definition Original_LF__DOT__Logic_LF_Logic_four__is__Even_iso := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__four____is____U_even__iso.Original_LF__DOT__Logic_LF_Logic_four__is__Even_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Logic_LF_Logic_four__is__Even_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.