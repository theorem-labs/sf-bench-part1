From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__or____commut__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__or____commut__iso.
From IsomorphismChecker Require Checker.or__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__or____commut__iso.Args := Checker.or__iso.Args <+ Checker.or__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__or____commut__iso.imported_Original_LF__DOT__Logic_LF_Logic_or__commut Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__or____commut__iso.Original_LF__DOT__Logic_LF_Logic_or__commut_iso ].

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__or____commut__iso.Interface args
  with Definition imported_Original_LF__DOT__Logic_LF_Logic_or__commut := Imported.Original_LF__DOT__Logic_LF_Logic_or__commut.

Definition imported_Original_LF__DOT__Logic_LF_Logic_or__commut := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__or____commut__iso.imported_Original_LF__DOT__Logic_LF_Logic_or__commut.
Definition Original_LF__DOT__Logic_LF_Logic_or__commut_iso := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__or____commut__iso.Original_LF__DOT__Logic_LF_Logic_or__commut_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Logic_LF_Logic_or__commut_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.