From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__apply____iff____example1__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__apply____iff____example1__iso.
From IsomorphismChecker Require Checker.iff__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__apply____iff____example1__iso.Args := Checker.iff__iso.Args <+ Checker.iff__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__apply____iff____example1__iso.Interface args
  with Definition imported_Original_LF__DOT__Logic_LF_Logic_apply__iff__example1 := Imported.Original_LF__DOT__Logic_LF_Logic_apply__iff__example1.

Definition imported_Original_LF__DOT__Logic_LF_Logic_apply__iff__example1 := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__apply____iff____example1__iso.imported_Original_LF__DOT__Logic_LF_Logic_apply__iff__example1.
Definition Original_LF__DOT__Logic_LF_Logic_apply__iff__example1_iso := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__apply____iff____example1__iso.Original_LF__DOT__Logic_LF_Logic_apply__iff__example1_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Logic_LF_Logic_apply__iff__example1_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.