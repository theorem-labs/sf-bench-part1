From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__contrapositive__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__contrapositive__iso.
From IsomorphismChecker Require Checker.U_false__iso Checker.U_logic__not__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__contrapositive__iso.Args := Checker.U_false__iso.Checker <+ Checker.U_logic__not__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__contrapositive__iso.Interface args
  with Definition imported_Original_LF__DOT__Logic_LF_Logic_contrapositive := Imported.Original_LF__DOT__Logic_LF_Logic_contrapositive.

Definition imported_Original_LF__DOT__Logic_LF_Logic_contrapositive := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__contrapositive__iso.imported_Original_LF__DOT__Logic_LF_Logic_contrapositive.
Definition Original_LF__DOT__Logic_LF_Logic_contrapositive_iso := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__contrapositive__iso.Original_LF__DOT__Logic_LF_Logic_contrapositive_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Logic_LF_Logic_contrapositive_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.