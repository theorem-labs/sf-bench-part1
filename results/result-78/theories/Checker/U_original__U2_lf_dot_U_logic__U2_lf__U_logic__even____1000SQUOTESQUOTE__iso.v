From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__even____1000SQUOTESQUOTE__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__even____1000SQUOTESQUOTE__iso.
From IsomorphismChecker Require Checker.nat__iso Checker.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso Checker.U_s__iso Checker.__0__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__even____1000SQUOTESQUOTE__iso.Args := Checker.nat__iso.Checker <+ Checker.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso.Checker <+ Checker.U_s__iso.Checker <+ Checker.__0__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__even____1000SQUOTESQUOTE__iso.imported_Original_LF__DOT__Logic_LF_Logic_even__1000'' Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__even____1000SQUOTESQUOTE__iso.Original_LF__DOT__Logic_LF_Logic_even__1000''_iso ].

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__even____1000SQUOTESQUOTE__iso.Interface args
  with Definition imported_Original_LF__DOT__Logic_LF_Logic_even__1000'' := Imported.Original_LF__DOT__Logic_LF_Logic_even__1000''.

Definition imported_Original_LF__DOT__Logic_LF_Logic_even__1000'' := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__even____1000SQUOTESQUOTE__iso.imported_Original_LF__DOT__Logic_LF_Logic_even__1000''.
Definition Original_LF__DOT__Logic_LF_Logic_even__1000''_iso := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__even____1000SQUOTESQUOTE__iso.Original_LF__DOT__Logic_LF_Logic_even__1000''_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Logic_LF_Logic_even__1000''_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.