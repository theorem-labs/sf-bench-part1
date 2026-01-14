From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__not____even____1001SQUOTE__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__not____even____1001SQUOTE__iso.
From IsomorphismChecker Require Checker.U_false__iso Checker.U_logic__not__iso Checker.nat__iso Checker.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso Checker.U_s__iso Checker.__0__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__not____even____1001SQUOTE__iso.Args := Checker.U_false__iso.Checker <+ Checker.U_logic__not__iso.Checker <+ Checker.nat__iso.Checker <+ Checker.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso.Checker <+ Checker.U_s__iso.Checker <+ Checker.__0__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__not____even____1001SQUOTE__iso.Interface args
  with Definition imported_Original_LF__DOT__Logic_LF_Logic_not__even__1001' := Imported.Original_LF__DOT__Logic_LF_Logic_not__even__1001'.

Definition imported_Original_LF__DOT__Logic_LF_Logic_not__even__1001' := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__not____even____1001SQUOTE__iso.imported_Original_LF__DOT__Logic_LF_Logic_not__even__1001'.
Definition Original_LF__DOT__Logic_LF_Logic_not__even__1001'_iso := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__not____even____1001SQUOTE__iso.Original_LF__DOT__Logic_LF_Logic_not__even__1001'_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Logic_LF_Logic_not__even__1001'_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.