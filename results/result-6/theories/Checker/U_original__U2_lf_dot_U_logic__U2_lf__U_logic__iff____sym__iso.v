From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__iff____sym__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__iff____sym__iso.
From IsomorphismChecker Require Checker.iff__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__iff____sym__iso.Args := Checker.iff__iso.Args <+ Checker.iff__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__iff____sym__iso.imported_Original_LF__DOT__Logic_LF_Logic_iff__sym Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__iff____sym__iso.Original_LF__DOT__Logic_LF_Logic_iff__sym_iso ].

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__iff____sym__iso.Interface args
  with Definition imported_Original_LF__DOT__Logic_LF_Logic_iff__sym := Imported.Original_LF__DOT__Logic_LF_Logic_iff__sym.

Definition imported_Original_LF__DOT__Logic_LF_Logic_iff__sym := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__iff____sym__iso.imported_Original_LF__DOT__Logic_LF_Logic_iff__sym.
Definition Original_LF__DOT__Logic_LF_Logic_iff__sym_iso := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__iff____sym__iso.Original_LF__DOT__Logic_LF_Logic_iff__sym_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Logic_LF_Logic_iff__sym_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.