From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__silly2____eauto__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__silly2____eauto__iso.
From IsomorphismChecker Require Checker.ex__iso Checker.nat__iso Checker.U_s__iso Checker.__0__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__silly2____eauto__iso.Args := Checker.ex__iso.Checker <+ Checker.nat__iso.Checker <+ Checker.U_s__iso.Checker <+ Checker.__0__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__silly2____eauto__iso.imported_Original_LF__DOT__Auto_LF_Auto_silly2__eauto Isomorphisms.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__silly2____eauto__iso.Original_LF__DOT__Auto_LF_Auto_silly2__eauto_iso ].

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__silly2____eauto__iso.Interface args
  with Definition imported_Original_LF__DOT__Auto_LF_Auto_silly2__eauto := Imported.Original_LF__DOT__Auto_LF_Auto_silly2__eauto.

Definition imported_Original_LF__DOT__Auto_LF_Auto_silly2__eauto := Isomorphisms.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__silly2____eauto__iso.imported_Original_LF__DOT__Auto_LF_Auto_silly2__eauto.
Definition Original_LF__DOT__Auto_LF_Auto_silly2__eauto_iso := Isomorphisms.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__silly2____eauto__iso.Original_LF__DOT__Auto_LF_Auto_silly2__eauto_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Auto_LF_Auto_silly2__eauto_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.