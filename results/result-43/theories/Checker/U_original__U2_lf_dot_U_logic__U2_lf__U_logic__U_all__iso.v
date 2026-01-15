From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_all__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_all__iso.
From IsomorphismChecker Require Checker.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_all__iso.Args := Checker.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Args <+ Checker.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_all__iso.imported_Original_LF__DOT__Logic_LF_Logic_All Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_all__iso.Original_LF__DOT__Logic_LF_Logic_All_iso ].

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_all__iso.Interface args
  with Definition imported_Original_LF__DOT__Logic_LF_Logic_All := (@Imported.Original_LF__DOT__Logic_LF_Logic_All).

Definition imported_Original_LF__DOT__Logic_LF_Logic_All := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_all__iso.imported_Original_LF__DOT__Logic_LF_Logic_All.
Definition Original_LF__DOT__Logic_LF_Logic_All_iso := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_all__iso.Original_LF__DOT__Logic_LF_Logic_All_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Logic_LF_Logic_All_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.