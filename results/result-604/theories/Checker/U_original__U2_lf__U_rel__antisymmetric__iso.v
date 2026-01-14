From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf__U_rel__antisymmetric__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf__U_rel__antisymmetric__iso.
From IsomorphismChecker Require Checker.U_original__U2_lf__U_rel__relation__iso Checker.U_true__iso Checker.U_corelib__U_init__U_logic__eq__iso.

Module Type Args <: Interface.U_original__U2_lf__U_rel__antisymmetric__iso.Args := Checker.U_original__U2_lf__U_rel__relation__iso.Checker <+ Checker.U_true__iso.Checker <+ Checker.U_corelib__U_init__U_logic__eq__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf__U_rel__antisymmetric__iso.Interface args
  with Definition imported_Original_LF_Rel_antisymmetric := (@Imported.Original_LF_Rel_antisymmetric).

Definition imported_Original_LF_Rel_antisymmetric := Isomorphisms.U_original__U2_lf__U_rel__antisymmetric__iso.imported_Original_LF_Rel_antisymmetric.
Definition Original_LF_Rel_antisymmetric_iso := Isomorphisms.U_original__U2_lf__U_rel__antisymmetric__iso.Original_LF_Rel_antisymmetric_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF_Rel_antisymmetric_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.