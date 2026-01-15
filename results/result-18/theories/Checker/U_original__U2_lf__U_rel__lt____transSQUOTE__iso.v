From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf__U_rel__lt____transSQUOTE__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf__U_rel__lt____transSQUOTE__iso.
From IsomorphismChecker Require Checker.U_original__U2_lf__U_rel__relation__iso Checker.U_original__U2_lf__U_rel__transitive__iso Checker.nat__iso Checker.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__lt__iso.

Module Type Args <: Interface.U_original__U2_lf__U_rel__lt____transSQUOTE__iso.Args := Checker.U_original__U2_lf__U_rel__relation__iso.Checker <+ Checker.U_original__U2_lf__U_rel__transitive__iso.Checker <+ Checker.nat__iso.Checker <+ Checker.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__lt__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_original__U2_lf__U_rel__lt____transSQUOTE__iso.imported_Original_LF_Rel_lt__trans' Isomorphisms.U_original__U2_lf__U_rel__lt____transSQUOTE__iso.Original_LF_Rel_lt__trans'_iso ].

Module Checker (Import args : Args) <: Interface.U_original__U2_lf__U_rel__lt____transSQUOTE__iso.Interface args
  with Definition imported_Original_LF_Rel_lt__trans' := Imported.Original_LF_Rel_lt__trans'.

Definition imported_Original_LF_Rel_lt__trans' := Isomorphisms.U_original__U2_lf__U_rel__lt____transSQUOTE__iso.imported_Original_LF_Rel_lt__trans'.
Definition Original_LF_Rel_lt__trans'_iso := Isomorphisms.U_original__U2_lf__U_rel__lt____transSQUOTE__iso.Original_LF_Rel_lt__trans'_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF_Rel_lt__trans'_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.