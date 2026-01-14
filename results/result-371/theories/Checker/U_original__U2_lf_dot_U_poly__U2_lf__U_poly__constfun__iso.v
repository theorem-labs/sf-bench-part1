From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__constfun__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__constfun__iso.
From IsomorphismChecker Require Checker.nat__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__constfun__iso.Args := Checker.nat__iso.Args <+ Checker.nat__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__constfun__iso.Interface args
  with Definition imported_Original_LF__DOT__Poly_LF_Poly_constfun := (@Imported.Original_LF__DOT__Poly_LF_Poly_constfun).

Definition imported_Original_LF__DOT__Poly_LF_Poly_constfun := Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__constfun__iso.imported_Original_LF__DOT__Poly_LF_Poly_constfun.
Definition Original_LF__DOT__Poly_LF_Poly_constfun_iso := Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__constfun__iso.Original_LF__DOT__Poly_LF_Poly_constfun_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Poly_LF_Poly_constfun_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.