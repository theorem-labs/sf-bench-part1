From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__id__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__id__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__id__iso.Args. End Args.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__id__iso.Interface args
  with Definition imported_Original_LF__DOT__Lists_LF_Lists_id := Imported.Original_LF__DOT__Lists_LF_Lists_id.

Definition imported_Original_LF__DOT__Lists_LF_Lists_id := Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__id__iso.imported_Original_LF__DOT__Lists_LF_Lists_id.
Definition Original_LF__DOT__Lists_LF_Lists_id_iso := Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__id__iso.Original_LF__DOT__Lists_LF_Lists_id_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Lists_LF_Lists_id_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.