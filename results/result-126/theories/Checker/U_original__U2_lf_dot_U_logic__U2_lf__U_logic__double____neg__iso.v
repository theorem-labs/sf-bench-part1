From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__double____neg__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__double____neg__iso.
From IsomorphismChecker Require Checker.U_false__iso Checker.U_logic__not__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__double____neg__iso.Args := Checker.U_false__iso.Checker <+ Checker.U_logic__not__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__double____neg__iso.Interface args
  with Definition imported_Original_LF__DOT__Logic_LF_Logic_double__neg := Imported.Original_LF__DOT__Logic_LF_Logic_double__neg.

Definition imported_Original_LF__DOT__Logic_LF_Logic_double__neg := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__double____neg__iso.imported_Original_LF__DOT__Logic_LF_Logic_double__neg.
Definition Original_LF__DOT__Logic_LF_Logic_double__neg_iso := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__double____neg__iso.Original_LF__DOT__Logic_LF_Logic_double__neg_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Logic_LF_Logic_double__neg_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.