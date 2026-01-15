From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplepmap__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplepmap__iso.
From IsomorphismChecker Require Checker.U_string__string__iso Checker.bool__iso Checker.option__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplepmap__iso.Args := Checker.U_string__string__iso.Checker <+ Checker.bool__iso.Checker <+ Checker.option__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplepmap__iso.imported_Original_LF__DOT__Maps_LF_Maps_examplepmap Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplepmap__iso.Original_LF__DOT__Maps_LF_Maps_examplepmap_iso ].

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplepmap__iso.Interface args
  with Definition imported_Original_LF__DOT__Maps_LF_Maps_examplepmap := Imported.Original_LF__DOT__Maps_LF_Maps_examplepmap.

Definition imported_Original_LF__DOT__Maps_LF_Maps_examplepmap := Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplepmap__iso.imported_Original_LF__DOT__Maps_LF_Maps_examplepmap.
Definition Original_LF__DOT__Maps_LF_Maps_examplepmap_iso := Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplepmap__iso.Original_LF__DOT__Maps_LF_Maps_examplepmap_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Maps_LF_Maps_examplepmap_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.