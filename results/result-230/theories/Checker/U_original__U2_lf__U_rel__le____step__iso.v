From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf__U_rel__le____step__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf__U_rel__le____step__iso.
From IsomorphismChecker Require Checker.nat__iso Checker.U_s__iso Checker.le__iso Checker.lt__iso.

Module Type Args <: Interface.U_original__U2_lf__U_rel__le____step__iso.Args := Checker.nat__iso.Checker <+ Checker.U_s__iso.Checker <+ Checker.le__iso.Checker <+ Checker.lt__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf__U_rel__le____step__iso.Interface args
  with Definition imported_Original_LF_Rel_le__step := Imported.Original_LF_Rel_le__step.

Definition imported_Original_LF_Rel_le__step := Isomorphisms.U_original__U2_lf__U_rel__le____step__iso.imported_Original_LF_Rel_le__step.
Definition Original_LF_Rel_le__step_iso := Isomorphisms.U_original__U2_lf__U_rel__le____step__iso.Original_LF_Rel_le__step_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF_Rel_le__step_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.