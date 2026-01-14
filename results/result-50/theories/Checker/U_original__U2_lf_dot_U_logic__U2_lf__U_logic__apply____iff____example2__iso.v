From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__apply____iff____example2__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__apply____iff____example2__iso.
From IsomorphismChecker Require Checker.iff__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__apply____iff____example2__iso.Args := Checker.iff__iso.Args <+ Checker.iff__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__apply____iff____example2__iso.Interface args
  with Definition imported_Original_LF__DOT__Logic_LF_Logic_apply__iff__example2 := Imported.Original_LF__DOT__Logic_LF_Logic_apply__iff__example2.

Definition imported_Original_LF__DOT__Logic_LF_Logic_apply__iff__example2 := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__apply____iff____example2__iso.imported_Original_LF__DOT__Logic_LF_Logic_apply__iff__example2.
Definition Original_LF__DOT__Logic_LF_Logic_apply__iff__example2_iso := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__apply____iff____example2__iso.Original_LF__DOT__Logic_LF_Logic_apply__iff__example2_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Logic_LF_Logic_apply__iff__example2_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.