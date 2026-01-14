From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__eqb____list__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__eqb____list__iso.
From IsomorphismChecker Require Checker.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Checker.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__eqb____list__iso.Args := Checker.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Checker <+ Checker.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__eqb____list__iso.Interface args
  with Definition imported_Original_LF__DOT__Logic_LF_Logic_eqb__list := (@Imported.Original_LF__DOT__Logic_LF_Logic_eqb__list).

Definition imported_Original_LF__DOT__Logic_LF_Logic_eqb__list := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__eqb____list__iso.imported_Original_LF__DOT__Logic_LF_Logic_eqb__list.
Definition Original_LF__DOT__Logic_LF_Logic_eqb__list_iso := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__eqb____list__iso.Original_LF__DOT__Logic_LF_Logic_eqb__list_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Logic_LF_Logic_eqb__list_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.