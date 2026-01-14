From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf__U_rel__rsc____U_r__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf__U_rel__rsc____U_r__iso.
From IsomorphismChecker Require Checker.U_original__U2_lf__U_rel__relation__iso Checker.U_original__U2_lf__U_rel__clos____refl____trans____1n__iso.

Module Type Args <: Interface.U_original__U2_lf__U_rel__rsc____U_r__iso.Args := Checker.U_original__U2_lf__U_rel__relation__iso.Checker <+ Checker.U_original__U2_lf__U_rel__clos____refl____trans____1n__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf__U_rel__rsc____U_r__iso.Interface args
  with Definition imported_Original_LF_Rel_rsc__R := Imported.Original_LF_Rel_rsc__R.

Definition imported_Original_LF_Rel_rsc__R := Isomorphisms.U_original__U2_lf__U_rel__rsc____U_r__iso.imported_Original_LF_Rel_rsc__R.
Definition Original_LF_Rel_rsc__R_iso := Isomorphisms.U_original__U2_lf__U_rel__rsc____U_r__iso.Original_LF_Rel_rsc__R_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF_Rel_rsc__R_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.