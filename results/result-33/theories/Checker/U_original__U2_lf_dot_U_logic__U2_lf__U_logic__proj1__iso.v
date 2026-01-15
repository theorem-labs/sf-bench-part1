From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__proj1__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__proj1__iso.
From IsomorphismChecker Require Checker.and__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__proj1__iso.Args := Checker.and__iso.Args <+ Checker.and__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__proj1__iso.imported_Original_LF__DOT__Logic_LF_Logic_proj1 Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__proj1__iso.Original_LF__DOT__Logic_LF_Logic_proj1_iso ].

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__proj1__iso.Interface args
  with Definition imported_Original_LF__DOT__Logic_LF_Logic_proj1 := Imported.Original_LF__DOT__Logic_LF_Logic_proj1.

Definition imported_Original_LF__DOT__Logic_LF_Logic_proj1 := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__proj1__iso.imported_Original_LF__DOT__Logic_LF_Logic_proj1.
Definition Original_LF__DOT__Logic_LF_Logic_proj1_iso := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__proj1__iso.Original_LF__DOT__Logic_LF_Logic_proj1_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Logic_LF_Logic_proj1_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.