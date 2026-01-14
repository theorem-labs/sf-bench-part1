From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf__U_rel__le____U_sn____le__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf__U_rel__le____U_sn____le__iso.
From IsomorphismChecker Require Checker.nat__iso Checker.U_s__iso Checker.le__iso.

Module Type Args <: Interface.U_original__U2_lf__U_rel__le____U_sn____le__iso.Args := Checker.nat__iso.Checker <+ Checker.U_s__iso.Checker <+ Checker.le__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf__U_rel__le____U_sn____le__iso.Interface args
  with Definition imported_Original_LF_Rel_le__Sn__le := Imported.Original_LF_Rel_le__Sn__le.

Definition imported_Original_LF_Rel_le__Sn__le := Isomorphisms.U_original__U2_lf__U_rel__le____U_sn____le__iso.imported_Original_LF_Rel_le__Sn__le.
Definition Original_LF_Rel_le__Sn__le_iso := Isomorphisms.U_original__U2_lf__U_rel__le____U_sn____le__iso.Original_LF_Rel_le__Sn__le_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF_Rel_le__Sn__le_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.