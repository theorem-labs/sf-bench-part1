From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__listSQUOTE__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__listSQUOTE__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__listSQUOTE__iso.Args. End Args.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__listSQUOTE__iso.Interface args
  with Definition imported_Original_LF__DOT__Poly_LF_Poly_list' := (@Imported.Original_LF__DOT__Poly_LF_Poly_list').

Definition imported_Original_LF__DOT__Poly_LF_Poly_list' := Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__listSQUOTE__iso.imported_Original_LF__DOT__Poly_LF_Poly_list'.
Definition Original_LF__DOT__Poly_LF_Poly_list'_iso := Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__listSQUOTE__iso.Original_LF__DOT__Poly_LF_Poly_list'_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Poly_LF_Poly_list'_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.