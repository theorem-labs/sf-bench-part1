From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf__U_rel__le____antisymmetric__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf__U_rel__le____antisymmetric__iso.
From IsomorphismChecker Require Checker.U_original__U2_lf__U_rel__relation__iso Checker.U_true__iso Checker.U_corelib__U_init__U_logic__eq__iso Checker.U_original__U2_lf__U_rel__antisymmetric__iso Checker.nat__iso Checker.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le__iso.

Module Type Args <: Interface.U_original__U2_lf__U_rel__le____antisymmetric__iso.Args := Checker.U_original__U2_lf__U_rel__relation__iso.Checker <+ Checker.U_true__iso.Checker <+ Checker.U_corelib__U_init__U_logic__eq__iso.Checker <+ Checker.U_original__U2_lf__U_rel__antisymmetric__iso.Checker <+ Checker.nat__iso.Checker <+ Checker.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_original__U2_lf__U_rel__le____antisymmetric__iso.imported_Original_LF_Rel_le__antisymmetric Isomorphisms.U_original__U2_lf__U_rel__le____antisymmetric__iso.Original_LF_Rel_le__antisymmetric_iso ].

Module Checker (Import args : Args) <: Interface.U_original__U2_lf__U_rel__le____antisymmetric__iso.Interface args
  with Definition imported_Original_LF_Rel_le__antisymmetric := Imported.Original_LF_Rel_le__antisymmetric.

Definition imported_Original_LF_Rel_le__antisymmetric := Isomorphisms.U_original__U2_lf__U_rel__le____antisymmetric__iso.imported_Original_LF_Rel_le__antisymmetric.
Definition Original_LF_Rel_le__antisymmetric_iso := Isomorphisms.U_original__U2_lf__U_rel__le____antisymmetric__iso.Original_LF_Rel_le__antisymmetric_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF_Rel_le__antisymmetric_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.