From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__eqb____id__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__eqb____id__iso.
From IsomorphismChecker Require Checker.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Checker.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__id__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__eqb____id__iso.Args := Checker.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Checker <+ Checker.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__id__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__eqb____id__iso.Interface args
  with Definition imported_Original_LF__DOT__Lists_LF_Lists_eqb__id := Imported.Original_LF__DOT__Lists_LF_Lists_eqb__id.

Definition imported_Original_LF__DOT__Lists_LF_Lists_eqb__id := Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__eqb____id__iso.imported_Original_LF__DOT__Lists_LF_Lists_eqb__id.
Definition Original_LF__DOT__Lists_LF_Lists_eqb__id_iso := Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__eqb____id__iso.Original_LF__DOT__Lists_LF_Lists_eqb__id_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Lists_LF_Lists_eqb__id_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.