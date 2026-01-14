From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf__U_rel__next____nat____closure____is____le__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf__U_rel__next____nat____closure____is____le__iso.
From IsomorphismChecker Require Checker.U_original__U2_lf__U_rel__relation__iso Checker.U_original__U2_lf__U_rel__clos____refl____trans__iso Checker.iff__iso Checker.nat__iso Checker.U_original__U2_lf__U_rel__next____nat__iso Checker.le__iso.

Module Type Args <: Interface.U_original__U2_lf__U_rel__next____nat____closure____is____le__iso.Args := Checker.U_original__U2_lf__U_rel__relation__iso.Checker <+ Checker.U_original__U2_lf__U_rel__clos____refl____trans__iso.Checker <+ Checker.iff__iso.Checker <+ Checker.nat__iso.Checker <+ Checker.U_original__U2_lf__U_rel__next____nat__iso.Checker <+ Checker.le__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf__U_rel__next____nat____closure____is____le__iso.Interface args
  with Definition imported_Original_LF_Rel_next__nat__closure__is__le := Imported.Original_LF_Rel_next__nat__closure__is__le.

Definition imported_Original_LF_Rel_next__nat__closure__is__le := Isomorphisms.U_original__U2_lf__U_rel__next____nat____closure____is____le__iso.imported_Original_LF_Rel_next__nat__closure__is__le.
Definition Original_LF_Rel_next__nat__closure__is__le_iso := Isomorphisms.U_original__U2_lf__U_rel__next____nat____closure____is____le__iso.Original_LF_Rel_next__nat__closure__is__le_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF_Rel_next__nat__closure__is__le_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.