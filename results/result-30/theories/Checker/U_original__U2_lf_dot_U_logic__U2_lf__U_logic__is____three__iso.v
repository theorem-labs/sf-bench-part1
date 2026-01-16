From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__is____three__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__is____three__iso.
From IsomorphismChecker Require Checker.nat__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__is____three__iso.Args := Checker.nat__iso.Args <+ Checker.nat__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__is____three__iso.imported_Original_LF__DOT__Logic_LF_Logic_is__three Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__is____three__iso.Original_LF__DOT__Logic_LF_Logic_is__three_iso ].

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__is____three__iso.Interface args
  with Definition imported_Original_LF__DOT__Logic_LF_Logic_is__three := Imported.Original_LF__DOT__Logic_LF_Logic_is__three.

Definition imported_Original_LF__DOT__Logic_LF_Logic_is__three := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__is____three__iso.imported_Original_LF__DOT__Logic_LF_Logic_is__three.
Definition Original_LF__DOT__Logic_LF_Logic_is__three_iso := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__is____three__iso.Original_LF__DOT__Logic_LF_Logic_is__three_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Logic_LF_Logic_is__three_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.